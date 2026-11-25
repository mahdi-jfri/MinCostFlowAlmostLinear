module

public import MinCostFlow.NarrowProg.Stage0ResLayout
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (helpers): cost-limb sum, residual emitter, and cost-limb copier

Provides three small low-heartbeat building blocks for Item 5:
1. `stage0ResCostSum`: sums canonical cost-limb lengths over all `m` edges in `O(m + 1)` steps.
2. `stage0ResEmit`: writes all 8 Stage 1 residual edge fields at slot `j` in `O(1)` steps.
3. `stage0ResCopyCost`: copies the canonical cost limbs of edge `e` out of `narrowEncode I` into
   `pCostBuf2 + cOff` via `padCopy`, preserving `narrowEncode I` intact.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### `stage0ResCostSum`: compute `totCostLimbs I` in `O(m + 1)` -/

wram_def stage0ResCostSum (pEdges, m) {
  tot := 0
  eOff := 0
  for i in 0 .. m {
    tot := tot + mem[pEdges + eOff + 9]
    eOff := eOff + 11
  }
  return tot
}

def stage0ResCostSumSpec (w : ℕ) : Spec Instance where
  pre := fun I args => ⨆ pEdges : ℕ,
    ⌜args = [pEdges, I.m] ∧
      pEdges + 11 * I.m ≤ 2 ^ w ∧ 11 * I.m < 2 ^ w ∧ totCostLimbs I < 2 ^ w⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else []))
  post := fun I args v => ⨆ pEdges : ℕ,
    ⌜args = [pEdges, I.m] ∧ v = totCostLimbs I⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else []))

private theorem prefixCostLimbs_le_tot (I : Instance) {i : ℕ} (hi : i ≤ I.m) :
    prefixCostLimbs I i ≤ totCostLimbs I := by
  rw [← prefixCostLimbs_full I]
  unfold prefixCostLimbs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hi)

theorem stage0ResCostSum_meets {w : ℕ} {p : Program} {f : ℕ}
    (hw : 1 < 2 ^ w)
    (hp : p.procs[f]? = some stage0ResCostSum) :
    Meets w p f ((stage0ResCostSumSpec w).withCost fun I _ => 45 * I.m + 30) := by
  sep_enter I with hpE h11m htotW
  sep_step; sep_step
  sep_for (fun i =>
      ⟨[pEdges, I.m, prefixCostLimbs I i, i * 11, i],
       i ≤ I.m,
       30 * (I.m - i) + 15,
       [∏ e ∈ Finset.range I.m,
          Assn.list (pEdges + e * 11) (if hlt : e < I.m then edgeRec I ⟨e, hlt⟩ else [])]⟩)
  · have hi : i < I.m := hhi
    have hsucc := prefixCostLimbs_succ I hi
    have hle_next : prefixCostLimbs I (i + 1) ≤ totCostLimbs I :=
      prefixCostLimbs_le_tot I (by omega)
    have hpull := (Finset.mul_prod_erase (Finset.range I.m)
      (fun e => Assn.list (pEdges + e * 11) (if hlt : e < I.m then edgeRec I ⟨e, hlt⟩ else []))
      (Finset.mem_range.mpr hi)).symm
    have hcur : Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec I ⟨i, hi⟩) := by simp [hi]
    sep_apply hpull
    sep_apply hcur
    have hlen_er : (edgeRec I ⟨i, hi⟩).length = 11 := rfl
    have her9 : (edgeRec I ⟨i, hi⟩)[9] =
        (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨i, hi⟩).cost.natAbs).length := rfl
    have hnext_off : i * 11 + 11 = (i + 1) * 11 := by ring
    sep_step
    sep_apply hcur.symm
    sep_apply hpull.symm
    sep_step
  · rw [prefixCostLimbs_full I]
    sep_step

/-! ### `stage0ResEmit`: write all 8 fields of one pruned residual arc -/

wram_def stage0ResEmit
    (pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
     j, u, v, capPtr, capLen, cSign, cPtr, cLen, origIdx) {
  mem[pTail2 + j] := u
  mem[pHead2 + j] := v
  mem[pCapPtr2 + j] := capPtr
  mem[pCapLen2 + j] := capLen
  mem[pCostSign2 + j] := cSign
  mem[pCostPtr2 + j] := cPtr
  mem[pCostLen2 + j] := cLen
  mem[pOrigIdx2 + j] := origIdx
  return 0
}

structure ResEmitData where
  cap : ℕ
  j : ℕ
  u : ℕ
  v : ℕ
  capPtr : ℕ
  capLen : ℕ
  cSign : ℕ
  cPtr : ℕ
  cLen : ℕ
  origIdx : ℕ
  xsT : List ℕ
  xsH : List ℕ
  xsCP : List ℕ
  xsCL : List ℕ
  xsCS : List ℕ
  xsCoP : List ℕ
  xsCoL : List ℕ
  xsOI : List ℕ

/-- Bundled bounds/lengths precondition for `stage0ResEmit`. -/
def ResEmitOk (w : ℕ) (d : ResEmitData)
    (pT pH pCP pCL pCS pCoP pCoL pOI : ℕ) : Prop :=
  d.j < d.cap ∧
  d.xsT.length = d.cap ∧ d.xsH.length = d.cap ∧ d.xsCP.length = d.cap ∧
  d.xsCL.length = d.cap ∧ d.xsCS.length = d.cap ∧ d.xsCoP.length = d.cap ∧
  d.xsCoL.length = d.cap ∧ d.xsOI.length = d.cap ∧
  pT + d.cap ≤ 2 ^ w ∧ pH + d.cap ≤ 2 ^ w ∧ pCP + d.cap ≤ 2 ^ w ∧
  pCL + d.cap ≤ 2 ^ w ∧ pCS + d.cap ≤ 2 ^ w ∧ pCoP + d.cap ≤ 2 ^ w ∧
  pCoL + d.cap ≤ 2 ^ w ∧ pOI + d.cap ≤ 2 ^ w ∧
  d.u < 2 ^ w ∧ d.v < 2 ^ w ∧ d.capPtr < 2 ^ w ∧ d.capLen < 2 ^ w ∧
  d.cSign < 2 ^ w ∧ d.cPtr < 2 ^ w ∧ d.cLen < 2 ^ w ∧ d.origIdx < 2 ^ w

def stage0ResEmitSpec (w : ℕ) : Spec ResEmitData where
  pre := fun d args => ⨆ (pT : ℕ) (pH : ℕ) (pCP : ℕ) (pCL : ℕ)
      (pCS : ℕ) (pCoP : ℕ) (pCoL : ℕ) (pOI : ℕ),
    ⌜args = [pT, pH, pCP, pCL, pCS, pCoP, pCoL, pOI,
        d.j, d.u, d.v, d.capPtr, d.capLen, d.cSign, d.cPtr, d.cLen, d.origIdx] ∧
      ResEmitOk w d pT pH pCP pCL pCS pCoP pCoL pOI⌝ *
    Assn.list pT d.xsT * Assn.list pH d.xsH * Assn.list pCP d.xsCP * Assn.list pCL d.xsCL *
    Assn.list pCS d.xsCS * Assn.list pCoP d.xsCoP * Assn.list pCoL d.xsCoL * Assn.list pOI d.xsOI
  post := fun d args r => ⨆ (pT : ℕ) (pH : ℕ) (pCP : ℕ) (pCL : ℕ)
      (pCS : ℕ) (pCoP : ℕ) (pCoL : ℕ) (pOI : ℕ),
    ⌜args = [pT, pH, pCP, pCL, pCS, pCoP, pCoL, pOI,
        d.j, d.u, d.v, d.capPtr, d.capLen, d.cSign, d.cPtr, d.cLen, d.origIdx] ∧ r = 0⌝ *
    Assn.list pT (d.xsT.set d.j d.u) * Assn.list pH (d.xsH.set d.j d.v) *
    Assn.list pCP (d.xsCP.set d.j d.capPtr) * Assn.list pCL (d.xsCL.set d.j d.capLen) *
    Assn.list pCS (d.xsCS.set d.j d.cSign) * Assn.list pCoP (d.xsCoP.set d.j d.cPtr) *
    Assn.list pCoL (d.xsCoL.set d.j d.cLen) * Assn.list pOI (d.xsOI.set d.j d.origIdx)

theorem stage0ResEmit_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage0ResEmit) :
    Meets w p f ((stage0ResEmitSpec w).withCost fun _ _ => 70) := by
  sep_enter d with hok
  obtain ⟨hj, h1, h2, h3, h4, h5, h6, h7, h8,
    hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8,
    hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩ := hok
  sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step
  sep_step

/-! ### `stage0ResCopyCost`: copy one edge's canonical cost limbs into `pCostBuf2 + cOff` -/

wram_def stage0ResCopyCost (pCopy : ℕ) (pEdges, eOff, pCostBuf2, cOff) {
  cLen := mem[pEdges + eOff + 9]
  d := pCopy(mem[pEdges + eOff + 10], cLen, pCostBuf2 + cOff, cLen)
  return cLen
}

structure ResCopyCostData where
  I : Instance
  hv : I.IsValid
  e : Fin I.m
  preCost : List ℕ
  bufCap : ℕ

def stage0ResCopyCostSpec (w : ℕ) : Spec ResCopyCostData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pCostBuf2 : ℕ),
    let k := narrowLimbWidth d.I
    let cLen := (Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs).length
    ⌜args = [pEdges, d.e.val * 11, pCostBuf2, d.preCost.length] ∧
      d.preCost.length + cLen ≤ d.bufCap ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pCostBuf2 (d.preCost ++ List.replicate (d.bufCap - d.preCost.length) 0)
  post := fun d args v => ⨆ (pEdges : ℕ) (pCostBuf2 : ℕ),
    let k := narrowLimbWidth d.I
    let dig := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
    ⌜args = [pEdges, d.e.val * 11, pCostBuf2, d.preCost.length] ∧ v = dig.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pCostBuf2 ((d.preCost ++ dig) ++ List.replicate (d.bufCap - (d.preCost.length + dig.length)) 0)

theorem stage0ResCopyCost_meets {w : ℕ} {p : Program} {f pCopy : ℕ} {Tpad : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResCopyCost pCopy))
    (hpad : Meets w p pCopy (padCopySpec.withCost fun x _ => Tpad x.2.length)) :
    Meets w p f ((stage0ResCopyCostSpec w).withCost fun d _ =>
      Tpad (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge d.e).cost.natAbs).length + 60) := by
  sep_enter d with hfitC hpE h11m hpCB hcapW
  set k := narrowLimbWidth d.I
  set dig := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
  have he_mem : d.e.val ∈ Finset.range d.I.m := Finset.mem_range.mpr d.e.isLt
  have hpullE := (Finset.mul_prod_erase (Finset.range d.I.m)
    (fun i => Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else []))
    he_mem).symm
  have hcurE : Assn.list (pEdges + d.e.val * 11)
      (if hlt : d.e.val < d.I.m then edgeRec d.I ⟨d.e.val, hlt⟩ else []) =
      Assn.list (pEdges + d.e.val * 11) (edgeRec d.I d.e) := by
    rw [dite_eq_left d.e.isLt, Fin.eta]
  sep_apply hpullE
  sep_apply hcurE
  have hlen_er : (edgeRec d.I d.e).length = 11 := rfl
  have he11_lt : d.e.val * 11 + 11 ≤ 11 * d.I.m := by have := d.e.isLt; omega
  sep_step
  -- Split narrowEncode I to expose edgeCostPtr d.I d.e
  sep_apply list_narrowEncode_split d.I d.hv
  have hpullEnc := (Finset.mul_prod_erase (Finset.range d.I.m)
    (fun i => Assn.list (edgeStartPos d.I i)
      (if hlt : i < d.I.m then narrowEdgeWords k (d.I.edge ⟨i, hlt⟩) else []))
    he_mem).symm
  have hcurEnc : Assn.list (edgeStartPos d.I d.e.val)
      (if hlt : d.e.val < d.I.m then narrowEdgeWords k (d.I.edge ⟨d.e.val, hlt⟩) else []) =
      Assn.list (edgeStartPos d.I d.e.val) (narrowEdgeWords k (d.I.edge d.e)) := by
    rw [dite_eq_left d.e.isLt, Fin.eta]
  have hcostBlock : Assn.list (edgeCostPos d.I d.e) (intWords k (d.I.edge d.e).cost) =
      (edgeCostPos d.I d.e ↦ if (d.I.edge d.e).cost < 0 then 1 else 0) *
      (edgeCostPos d.I d.e + 1 ↦ dig.length) *
      Assn.list (edgeCostPtr d.I d.e) dig := by
    unfold intWords edgeCostPtr
    simp only [Assn.list_cons, mul_assoc, show edgeCostPos d.I d.e + 1 + 1 = edgeCostPos d.I d.e + 2 by omega]
    rfl
  sep_apply hpullEnc
  sep_apply hcurEnc
  sep_apply list_narrowEdgeWords d.I d.e
  sep_apply hcostBlock
  -- Split pCostBuf2 around [d.preCost.length, d.preCost.length + dig.length)
  have hcb_split : Assn.list pCostBuf2 (d.preCost ++ List.replicate (d.bufCap - d.preCost.length) 0) =
      Assn.list pCostBuf2 d.preCost *
      Assn.list (pCostBuf2 + d.preCost.length) (List.replicate dig.length 0) *
      Assn.list (pCostBuf2 + d.preCost.length + dig.length)
        (List.replicate (d.bufCap - (d.preCost.length + dig.length)) 0) := by
    have hrep : d.bufCap - d.preCost.length = dig.length + (d.bufCap - (d.preCost.length + dig.length)) := by
      omega
    rw [hrep, List.replicate_add, Assn.list_append, Assn.list_append, List.length_replicate, mul_assoc]
  sep_apply hcb_split
  generalize hF_rest :
    ((0 ↦ k) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
     (∏ i ∈ (Finset.range d.I.m).erase d.e.val,
       Assn.list (edgeStartPos d.I i)
         (if hlt : i < d.I.m then narrowEdgeWords k (d.I.edge ⟨i, hlt⟩) else [])) *
     (∏ v ∈ Finset.range d.I.n,
       Assn.list (demStartPos d.I v)
         (if _ : v < d.I.n then intWords k (d.I.d v) else [])) *
     (edgeStartPos d.I d.e.val ↦ (d.I.edge d.e).tail) *
     (edgeStartPos d.I d.e.val + 1 ↦ (d.I.edge d.e).head) *
     Assn.list (edgeStartPos d.I d.e.val + 2) (intWords k (d.I.edge d.e).lower) *
     Assn.list (edgeHiPos d.I d.e) (intWords k (d.I.edge d.e).upper) *
     (edgeCostPos d.I d.e ↦ if (d.I.edge d.e).cost < 0 then 1 else 0) *
     (edgeCostPos d.I d.e + 1 ↦ dig.length) *
     (∏ i ∈ (Finset.range d.I.m).erase d.e.val,
       Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pCostBuf2 d.preCost *
     Assn.list (pCostBuf2 + d.preCost.length + dig.length)
       (List.replicate (d.bufCap - (d.preCost.length + dig.length)) 0)) = F_rest
  sep_apply hF_rest
  have hcLen_eq : cLen = dig.length := hcLen
  have hptr_atom : Assn.list (edgeCostPtr d.I d.e) dig = Assn.list (edgeRec d.I d.e)[10] dig := rfl
  sep_apply hptr_atom
  sep_step from (dig, List.replicate dig.length 0)
  subst F_rest; sep_norm
  have hfold_e : Assn.list (pEdges + d.e.val * 11)
      [(d.I.edge d.e).tail, (d.I.edge d.e).head,
       if (d.I.edge d.e).lower < 0 then 1 else 0,
       (Nat.digits (2 ^ k) (d.I.edge d.e).lower.natAbs).length,
       edgeLoPtr d.I d.e,
       if (d.I.edge d.e).upper < 0 then 1 else 0,
       (Nat.digits (2 ^ k) (d.I.edge d.e).upper.natAbs).length,
       edgeHiPtr d.I d.e,
       if (d.I.edge d.e).cost < 0 then 1 else 0,
       (Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs).length,
       edgeCostPtr d.I d.e] =
      Assn.list (pEdges + d.e.val * 11) (edgeRec d.I d.e) := rfl
  sep_apply hfold_e
  sep_apply hptr_atom.symm
  -- Rejoin narrowEncode I, pEdges, and pCostBuf2
  sep_apply hcostBlock.symm
  sep_apply (list_narrowEdgeWords d.I d.e).symm
  sep_apply hcurEnc.symm
  sep_apply hpullEnc.symm
  sep_apply (list_narrowEncode_split d.I d.hv).symm
  sep_apply hcurE.symm
  sep_apply hpullE.symm
  have hcb_join : Assn.list pCostBuf2 d.preCost *
      Assn.list (pCostBuf2 + d.preCost.length) (padLimbs dig (List.replicate dig.length 0).length) *
      Assn.list (pCostBuf2 + d.preCost.length + dig.length)
        (List.replicate (d.bufCap - (d.preCost.length + dig.length)) 0) =
      Assn.list pCostBuf2 ((d.preCost ++ dig) ++
        List.replicate (d.bufCap - (d.preCost.length + dig.length)) 0) := by
    simp only [List.length_replicate, padLimbs, Nat.sub_self, List.replicate_zero, List.append_nil]
    rw [Assn.list_append, Assn.list_append, List.length_append, ← Nat.add_assoc]
  sep_apply hcb_join
  sep_step

/-! ### `stage0ResFwdEmit`, `stage0ResRevSign`, `stage0ResRevEmit`: per-arc emission helpers -/

/-- The unused cells (indices 2..7 and 9..10) of `edgeRec I e` at `p`, bundled behind a named
constant so `sep_step` never unfolds `edgeRec` during heap lookup and `sep_apply` matches by head. -/
def edgeRecRest (I : Instance) (e : Fin I.m) (p : ℕ) : Assn :=
  Assn.list (p + 2) (((edgeRec I e).drop 2).take 6) *
  Assn.list (p + 9) ((edgeRec I e).drop 9)

/-- Exposes the `tail`, `head`, and `costSign` cells of `edgeRec I e` as direct points-to atoms
plus `edgeRecRest I e p`. -/
theorem list_edgeRec_expose (I : Instance) (e : Fin I.m) (p : ℕ) :
    Assn.list p (edgeRec I e) =
      (p ↦ (I.edge e).tail) * (p + 1 ↦ (I.edge e).head) *
      (p + 8 ↦ if (I.edge e).cost < 0 then 1 else 0) * edgeRecRest I e p := by
  unfold edgeRecRest edgeRec
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    Assn.list_cons, Assn.list_nil, mul_one,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega, show p + 4 + 1 = p + 5 by omega,
    show p + 5 + 1 = p + 6 by omega, show p + 6 + 1 = p + 7 by omega,
    show p + 7 + 1 = p + 8 by omega, show p + 8 + 1 = p + 9 by omega,
    show p + 9 + 1 = p + 10 by omega]
  ac_rfl

structure ResArcEmitData where
  I : Instance
  hv : I.IsValid
  e : Fin I.m
  capPtrVal : ℕ
  capLenVal : ℕ
  cOffList : List ℕ
  bufCap : ℕ
  cap : ℕ
  j : ℕ
  ts : List ℕ
  hs : List ℕ
  cps : List ℕ
  cls : List ℕ
  css : List ℕ
  cops : List ℕ
  cols : List ℕ
  ois : List ℕ

wram_def stage0ResFwdEmit (copyCost resEmit : ℕ)
    (pEdges, eOff, capPtr, pCostBuf2, cOff, capLen, i, j,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2) {
  cLenE := copyCost(pEdges, eOff, pCostBuf2, cOff)
  u := mem[pEdges + eOff]
  v := mem[pEdges + eOff + 1]
  cSign := mem[pEdges + eOff + 8]
  d := resEmit(pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
    j, u, v, capPtr, capLen, cSign, pCostBuf2 + cOff, cLenE, i)
  return cLenE
}

def ResArcEmitOk (w : ℕ) (d : ResArcEmitData)
    (pEdges pCostBuf2 pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2 : ℕ) : Prop :=
  let k := narrowLimbWidth d.I
  let cLimbs := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
  pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
  d.cOffList.length + cLimbs.length ≤ d.bufCap ∧
  pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w ∧
  d.j < d.cap ∧ d.cap < 2 ^ w ∧ d.I.n < 2 ^ w ∧
  d.capPtrVal < 2 ^ w ∧ d.capLenVal < 2 ^ w ∧
  d.ts.length = d.cap ∧ d.hs.length = d.cap ∧ d.cps.length = d.cap ∧ d.cls.length = d.cap ∧
  d.css.length = d.cap ∧ d.cops.length = d.cap ∧ d.cols.length = d.cap ∧ d.ois.length = d.cap ∧
  pTail2 + d.cap ≤ 2 ^ w ∧ pHead2 + d.cap ≤ 2 ^ w ∧
  pCapPtr2 + d.cap ≤ 2 ^ w ∧ pCapLen2 + d.cap ≤ 2 ^ w ∧
  pCostSign2 + d.cap ≤ 2 ^ w ∧ pCostPtr2 + d.cap ≤ 2 ^ w ∧
  pCostLen2 + d.cap ≤ 2 ^ w ∧ pOrigIdx2 + d.cap ≤ 2 ^ w

def stage0ResFwdEmitSpec (w : ℕ) : Spec ResArcEmitData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ)
      (pCapPtr2 : ℕ) (pCapLen2 : ℕ) (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ),
    ⌜args = [pEdges, d.e.val * 11, d.capPtrVal, pCostBuf2, d.cOffList.length, d.capLenVal,
        d.e.val, d.j, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2] ∧
      ResArcEmitOk w d pEdges pCostBuf2 pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pCostBuf2 (d.cOffList ++ List.replicate (d.bufCap - d.cOffList.length) 0) *
    Assn.list pTail2 d.ts * Assn.list pHead2 d.hs *
    Assn.list pCapPtr2 d.cps * Assn.list pCapLen2 d.cls *
    Assn.list pCostSign2 d.css * Assn.list pCostPtr2 d.cops *
    Assn.list pCostLen2 d.cols * Assn.list pOrigIdx2 d.ois
  post := fun d args res => ⨆ (pEdges : ℕ) (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ)
      (pCapPtr2 : ℕ) (pCapLen2 : ℕ) (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ),
    let k := narrowLimbWidth d.I
    let cLimbs := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
    ⌜args = [pEdges, d.e.val * 11, d.capPtrVal, pCostBuf2, d.cOffList.length, d.capLenVal,
        d.e.val, d.j, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2] ∧
      res = cLimbs.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pCostBuf2
      ((d.cOffList ++ cLimbs) ++ List.replicate (d.bufCap - (d.cOffList.length + cLimbs.length)) 0) *
    Assn.list pTail2 (d.ts.set d.j (d.I.edge d.e).tail) *
    Assn.list pHead2 (d.hs.set d.j (d.I.edge d.e).head) *
    Assn.list pCapPtr2 (d.cps.set d.j d.capPtrVal) *
    Assn.list pCapLen2 (d.cls.set d.j d.capLenVal) *
    Assn.list pCostSign2 (d.css.set d.j (if (d.I.edge d.e).cost < 0 then 1 else 0)) *
    Assn.list pCostPtr2 (d.cops.set d.j (pCostBuf2 + d.cOffList.length)) *
    Assn.list pCostLen2 (d.cols.set d.j cLimbs.length) *
    Assn.list pOrigIdx2 (d.ois.set d.j d.e.val)

theorem stage0ResFwdEmit_meets {w : ℕ} {p : Program} {f copyCost resEmit : ℕ}
    {Tcopy : ℕ → ℕ} {Temit : ℕ}
    (hp : p.procs[f]? = some (stage0ResFwdEmit copyCost resEmit))
    (hcopy : Meets w p copyCost ((stage0ResCopyCostSpec w).withCost fun x _ =>
      Tcopy (narrowMaxCostLimbs x.I)))
    (hemit : Meets w p resEmit ((stage0ResEmitSpec w).withCost fun _ _ => Temit)) :
    Meets w p f ((stage0ResFwdEmitSpec w).withCost fun d _ =>
      Tcopy (narrowMaxCostLimbs d.I) + Temit + 60) := by
  sep_enter d with hOk
  obtain ⟨hpE, h11m, hfitC, hpCoB, hbufW, hjcap, hcapW, hnW, hcpW, hclW,
    hts, hhs, hcps, hcls, hcss, hcops, hcols, hois,
    hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI⟩ := hOk
  set k := narrowLimbWidth d.I
  set cLimbs := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
  have hmem : d.e.val ∈ Finset.range d.I.m := Finset.mem_range.mpr d.e.isLt
  have hw11 : 11 < 2 ^ w := by have := d.e.isLt; omega
  have hpEi : pEdges + d.e.val * 11 + 11 ≤ 2 ^ w := by have := d.e.isLt; omega
  generalize hF_arr :
    (Assn.list pTail2 d.ts * Assn.list pHead2 d.hs *
     Assn.list pCapPtr2 d.cps * Assn.list pCapLen2 d.cls *
     Assn.list pCostSign2 d.css * Assn.list pCostPtr2 d.cops *
     Assn.list pCostLen2 d.cols * Assn.list pOrigIdx2 d.ois) = F_arr
  sep_apply hF_arr
  sep_step from (⟨d.I, d.hv, d.e, d.cOffList, d.bufCap⟩ : ResCopyCostData)
  have hpullE := (Finset.mul_prod_erase (Finset.range d.I.m)
    (fun i => Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else []))
    hmem).symm
  have hcurE : Assn.list (pEdges + d.e.val * 11) (if hlt : d.e.val < d.I.m then edgeRec d.I ⟨d.e.val, hlt⟩ else []) =
      Assn.list (pEdges + d.e.val * 11) (edgeRec d.I d.e) := by simp [d.e.isLt]
  sep_apply hpullE; sep_apply hcurE
  generalize hF_em0 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ (Finset.range d.I.m).erase d.e.val,
       Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pCostBuf2
       ((d.cOffList ++ cLimbs) ++ List.replicate (d.bufCap - (d.cOffList.length + cLimbs.length)) 0)) = F_em0
  sep_apply hF_em0
  sep_apply list_edgeRec_expose d.I d.e (pEdges + d.e.val * 11)
  sep_step; sep_step; sep_step
  have hu_eq : u = (d.I.edge d.e).tail := hu
  have hv_eq : v = (d.I.edge d.e).head := hv
  have hcSign_eq : cSign = (if (d.I.edge d.e).cost < 0 then 1 else 0) := hcSign
  have hcLenE_eq : cLenE = cLimbs.length := hcLenE
  sep_apply (list_edgeRec_expose d.I d.e (pEdges + d.e.val * 11)).symm
  subst F_arr; sep_norm
  let ed : ResEmitData :=
    ⟨d.cap, d.j, u, v, d.capPtrVal, d.capLenVal, cSign, pCostBuf2 + d.cOffList.length, cLenE, d.e.val,
      d.ts, d.hs, d.cps, d.cls, d.css, d.cops, d.cols, d.ois⟩
  have hEmitOk : ResEmitOk w ed
      pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2 := by
    dsimp only [ResEmitOk, ed]
    rw [hu_eq, hv_eq, hcSign_eq, hcLenE_eq]
    refine ⟨hjcap, hts, hhs, hcps, hcls, hcss, hcops, hcols, hois,
      hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI,
      by have := (d.hv.1 (d.I.edge d.e) (List.getElem_mem d.e.isLt)).1; omega,
      by have := (d.hv.1 (d.I.edge d.e) (List.getElem_mem d.e.isLt)).2; omega,
      hcpW, hclW, by split_ifs <;> omega, by omega, by omega, by have := d.e.isLt; omega⟩
  sep_step from ed
  dsimp only [ed]
  rw [hu_eq, hv_eq, hcSign_eq, hcLenE_eq]
  subst F_em0; sep_norm
  sep_apply hcurE.symm; sep_apply hpullE.symm
  sep_step

wram_def stage0ResRevSign (cLenE, cSign) {
  if 0 < cLenE {
    return 1 - cSign
  } else {
    return 0
  }
}

def stage0ResRevSignSpec : Spec (ℕ × ℤ) where
  pre := fun (k, c) args =>
    ⌜args = [(Nat.digits (2 ^ k) c.natAbs).length, if c < 0 then 1 else 0] ∧ 1 ≤ k⌝
  post := fun (k, c) args v =>
    ⌜args = [(Nat.digits (2 ^ k) c.natAbs).length, if c < 0 then 1 else 0] ∧
      v = (if -c < 0 then 1 else 0)⌝

theorem stage0ResRevSign_meets {w : ℕ} {p : Program} {f : ℕ}
    (hw : 1 < 2 ^ w) (hp : p.procs[f]? = some stage0ResRevSign) :
    Meets w p f (stage0ResRevSignSpec.withCost fun _ _ => 30) := by
  sep_enter x with hk1
  rcases x with ⟨k, c⟩
  dsimp only at hk1
  have hb : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  sep_step
  · sep_step
    · have hne0 : c.natAbs ≠ 0 := by
        intro h0; rw [h0] at hcond; simp at hcond
      split_ifs <;> omega
  · sep_step
    · have h0 : c.natAbs = 0 := by
        by_contra hne0
        have := Nat.length_digits (2 ^ k) c.natAbs hb hne0
        omega
      have hc0 : c = 0 := Int.natAbs_eq_zero.mp h0
      simp [hc0]

wram_def stage0ResRevEmit (copyCost revSignFn resEmit : ℕ)
    (pEdges, eOff, capPtr, pCostBuf2, cOff, capLen, i, j,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2) {
  cLenE := copyCost(pEdges, eOff, pCostBuf2, cOff)
  u := mem[pEdges + eOff + 1]
  v := mem[pEdges + eOff]
  cSign := mem[pEdges + eOff + 8]
  revSign := revSignFn(cLenE, cSign)
  d := resEmit(pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2,
    j, u, v, capPtr, capLen, revSign, pCostBuf2 + cOff, cLenE, i)
  return cLenE
}

def stage0ResRevEmitSpec (w : ℕ) : Spec ResArcEmitData where
  pre := (stage0ResFwdEmitSpec w).pre
  post := fun d args res => ⨆ (pEdges : ℕ) (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ)
      (pCapPtr2 : ℕ) (pCapLen2 : ℕ) (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ),
    let k := narrowLimbWidth d.I
    let cLimbs := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
    ⌜args = [pEdges, d.e.val * 11, d.capPtrVal, pCostBuf2, d.cOffList.length, d.capLenVal,
        d.e.val, d.j, pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2] ∧
      res = cLimbs.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pCostBuf2
      ((d.cOffList ++ cLimbs) ++ List.replicate (d.bufCap - (d.cOffList.length + cLimbs.length)) 0) *
    Assn.list pTail2 (d.ts.set d.j (d.I.edge d.e).head) *
    Assn.list pHead2 (d.hs.set d.j (d.I.edge d.e).tail) *
    Assn.list pCapPtr2 (d.cps.set d.j d.capPtrVal) *
    Assn.list pCapLen2 (d.cls.set d.j d.capLenVal) *
    Assn.list pCostSign2 (d.css.set d.j (if -(d.I.edge d.e).cost < 0 then 1 else 0)) *
    Assn.list pCostPtr2 (d.cops.set d.j (pCostBuf2 + d.cOffList.length)) *
    Assn.list pCostLen2 (d.cols.set d.j cLimbs.length) *
    Assn.list pOrigIdx2 (d.ois.set d.j d.e.val)

theorem stage0ResRevEmit_meets {w : ℕ} {p : Program} {f copyCost revSignFn resEmit : ℕ}
    {Tcopy : ℕ → ℕ} {Trev Temit : ℕ}
    (hp : p.procs[f]? = some (stage0ResRevEmit copyCost revSignFn resEmit))
    (hcopy : Meets w p copyCost ((stage0ResCopyCostSpec w).withCost fun x _ =>
      Tcopy (narrowMaxCostLimbs x.I)))
    (hrev : Meets w p revSignFn (stage0ResRevSignSpec.withCost fun _ _ => Trev))
    (hemit : Meets w p resEmit ((stage0ResEmitSpec w).withCost fun _ _ => Temit)) :
    Meets w p f ((stage0ResRevEmitSpec w).withCost fun d _ =>
      Tcopy (narrowMaxCostLimbs d.I) + Trev + Temit + 70) := by
  sep_enter d with hOk
  obtain ⟨hpE, h11m, hfitC, hpCoB, hbufW, hjcap, hcapW, hnW, hcpW, hclW,
    hts, hhs, hcps, hcls, hcss, hcops, hcols, hois,
    hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI⟩ := hOk
  set k := narrowLimbWidth d.I
  set cLimbs := Nat.digits (2 ^ k) (d.I.edge d.e).cost.natAbs
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hmem : d.e.val ∈ Finset.range d.I.m := Finset.mem_range.mpr d.e.isLt
  have hw11 : 11 < 2 ^ w := by have := d.e.isLt; omega
  have hpEi : pEdges + d.e.val * 11 + 11 ≤ 2 ^ w := by have := d.e.isLt; omega
  generalize hF_arr :
    (Assn.list pTail2 d.ts * Assn.list pHead2 d.hs *
     Assn.list pCapPtr2 d.cps * Assn.list pCapLen2 d.cls *
     Assn.list pCostSign2 d.css * Assn.list pCostPtr2 d.cops *
     Assn.list pCostLen2 d.cols * Assn.list pOrigIdx2 d.ois) = F_arr
  sep_apply hF_arr
  sep_step from (⟨d.I, d.hv, d.e, d.cOffList, d.bufCap⟩ : ResCopyCostData)
  have hpullE := (Finset.mul_prod_erase (Finset.range d.I.m)
    (fun i => Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else []))
    hmem).symm
  have hcurE : Assn.list (pEdges + d.e.val * 11) (if hlt : d.e.val < d.I.m then edgeRec d.I ⟨d.e.val, hlt⟩ else []) =
      Assn.list (pEdges + d.e.val * 11) (edgeRec d.I d.e) := by simp [d.e.isLt]
  sep_apply hpullE; sep_apply hcurE
  generalize hF_em0 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ (Finset.range d.I.m).erase d.e.val,
       Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pCostBuf2
       ((d.cOffList ++ cLimbs) ++ List.replicate (d.bufCap - (d.cOffList.length + cLimbs.length)) 0)) = F_em0
  sep_apply hF_em0
  sep_apply list_edgeRec_expose d.I d.e (pEdges + d.e.val * 11)
  sep_step; sep_step; sep_step
  have hu_eq : u = (d.I.edge d.e).head := hu
  have hv_eq : v = (d.I.edge d.e).tail := hv
  have hcSign_eq : cSign = (if (d.I.edge d.e).cost < 0 then 1 else 0) := hcSign
  have hcLenE_eq : cLenE = cLimbs.length := hcLenE
  sep_apply (list_edgeRec_expose d.I d.e (pEdges + d.e.val * 11)).symm
  sep_step from (k, (d.I.edge d.e).cost)
  have hrevSign_eq : revSign = (if -(d.I.edge d.e).cost < 0 then 1 else 0) := hrevSign
  subst F_arr; sep_norm
  let ed : ResEmitData :=
    ⟨d.cap, d.j, u, v, d.capPtrVal, d.capLenVal, revSign, pCostBuf2 + d.cOffList.length, cLenE, d.e.val,
      d.ts, d.hs, d.cps, d.cls, d.css, d.cops, d.cols, d.ois⟩
  have hEmitOk : ResEmitOk w ed
      pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2 := by
    dsimp only [ResEmitOk, ed]
    rw [hu_eq, hv_eq, hrevSign_eq, hcLenE_eq]
    refine ⟨hjcap, hts, hhs, hcps, hcls, hcss, hcops, hcols, hois,
      hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI,
      by have := (d.hv.1 (d.I.edge d.e) (List.getElem_mem d.e.isLt)).2; omega,
      by have := (d.hv.1 (d.I.edge d.e) (List.getElem_mem d.e.isLt)).1; omega,
      hcpW, hclW, by split_ifs <;> omega, by omega, by omega, by have := d.e.isLt; omega⟩
  sep_step from ed
  dsimp only [ed]
  rw [hu_eq, hv_eq, hrevSign_eq, hcLenE_eq]
  subst F_em0; sep_norm
  sep_apply hcurE.symm; sep_apply hpullE.symm
  sep_step

end MinCostFlow.NarrowProg
