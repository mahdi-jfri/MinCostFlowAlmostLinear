module

public import MinCostFlow.NarrowProg.Stage0ResHelpers
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (Pass Fwd): forward residual arcs (`stage0ResFwdStep`, `stage0ResPassFwd`)

Scans all `I.m` original edges, computes `(shiftedCap e - f e)` in `pCapBuf2 + e * L` via
`limbsSub` and `canonLen`, and whenever positive emits the forward residual arc via
`stage0ResFwdEmit`. Splitting the loop body into `stage0ResFwdStep` keeps each proof small.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Helper lemmas for forward residual pass -/

theorem resCostPtrs_snoc (base : ℕ) (xss : List (List ℕ)) (a : List ℕ) :
    List.ofFn (fun t : Fin (xss ++ [a]).length =>
        base + (((xss ++ [a]).take t.val).map List.length).sum) =
      List.ofFn (fun t : Fin xss.length =>
        base + ((xss.take t.val).map List.length).sum) ++
      [base + xss.flatten.length] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    by_cases hlt : i < xss.length
    · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn,
          List.take_append_of_le_length (le_of_lt hlt)]
    · have hi_eq : i = xss.length := by simp at h1; omega
      subst hi_eq
      rw [List.getElem_append_right (by simp), List.take_append_of_le_length (le_refl _),
          List.take_length]
      simp [List.length_flatten]

private theorem resFwd_capBuf_next (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCapBuf2 L i : ℕ) (hi : i < I.m) :
    let k := narrowLimbWidth I
    Assn.list (pCapBuf2 + i * L)
      (padLimbs (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity ⟨i, hi⟩ : ℤ) - f ⟨i, hi⟩).toNat) L) *
    (∏ e ∈ (Finset.range I.m).erase i,
      Assn.list (pCapBuf2 + e * L)
        (if e < i then
          (if hm : e < I.m then
            padLimbs (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity ⟨e, hm⟩ : ℤ) - f ⟨e, hm⟩).toNat) L
           else [])
         else List.replicate L 0)) =
    (∏ e ∈ Finset.range I.m,
      Assn.list (pCapBuf2 + e * L)
        (if e < i + 1 then
          (if hm : e < I.m then
            padLimbs (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity ⟨e, hm⟩ : ℤ) - f ⟨e, hm⟩).toNat) L
           else [])
         else List.replicate L 0)) := by
  dsimp only
  set k := narrowLimbWidth I
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)]
  congr 1
  · rw [ite_eq_left (by omega : i < i + 1), dite_eq_left hi]
  · refine Finset.prod_congr rfl fun e he => ?_
    have hne : e ≠ i := (Finset.mem_erase.mp he).1
    have hiff : (e < i) ↔ (e < i + 1) := by omega
    rw [if_congr hiff rfl rfl]

private theorem resFwd_set_map {α : Type} (xs : List α) (g : α → ℕ) (a : α) (cap : ℕ)
    (hlt : xs.length < cap) :
    (xs.map g ++ List.replicate (cap - xs.length) 0).set xs.length (g a) =
      (xs ++ [a]).map g ++ List.replicate (cap - (xs ++ [a]).length) 0 := by
  have h1 := list_set_append_replicate (xs := xs.map g) (cap := cap) (v := g a) (by simp; exact hlt)
  simp only [List.length_map] at h1
  rw [h1, List.map_append]; simp

private theorem resFwd_set_costPtrs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCostBuf2 cap i : ℕ) (hi : i < I.m)
    (hpos : 0 < (((FlowReduction.shiftedGraph I hv).capacity ⟨i, hi⟩ : ℤ) - f ⟨i, hi⟩).toNat)
    (hlt : (resFwdPos I hv f i).length < cap) :
    let xs := resFwdPos I hv f i
    let cl := edgeCostLimbList I xs
    (List.ofFn (fun t : Fin xs.length =>
        pCostBuf2 + ((cl.take t.val).map List.length).sum) ++ List.replicate (cap - xs.length) 0).set
        xs.length (pCostBuf2 + cl.flatten.length) =
      List.ofFn (fun t : Fin (resFwdPos I hv f (i + 1)).length =>
        pCostBuf2 + (((edgeCostLimbList I (resFwdPos I hv f (i + 1))).take t.val).map List.length).sum) ++
        List.replicate (cap - (resFwdPos I hv f (i + 1)).length) 0 := by
  dsimp only
  set e0 : Fin I.m := ⟨i, hi⟩
  set k := narrowLimbWidth I
  set xs := resFwdPos I hv f i
  set cl := edgeCostLimbList I xs
  have hsucc' : resFwdPos I hv f (i + 1) = xs ++ [e0] := by
    rw [resFwdPos_succ I hv f hi, ite_eq_left hpos]
  have hcl_next : edgeCostLimbList I (resFwdPos I hv f (i + 1)) =
      cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs] := by
    rw [hsucc']; simp [edgeCostLimbList, cl, k]
  have hcl_len : cl.length = xs.length := by simp [cl, edgeCostLimbList]
  have h1 := list_set_append_replicate
    (xs := List.ofFn (fun t : Fin xs.length => pCostBuf2 + ((cl.take t.val).map List.length).sum))
    (cap := cap) (v := pCostBuf2 + cl.flatten.length) (by simp; exact hlt)
  simp only [List.length_ofFn] at h1
  rw [h1, hcl_next, hsucc']
  have hsnoc := resCostPtrs_snoc pCostBuf2 cl (Nat.digits (2 ^ k) (I.edge e0).cost.natAbs)
  have hlen_cl1 : (cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).length = (xs ++ [e0]).length := by
    simp [hcl_len]
  have hof1 : List.ofFn (fun t : Fin (xs ++ [e0]).length =>
      pCostBuf2 + (((cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).take t.val).map List.length).sum) =
      List.ofFn (fun t : Fin (cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).length =>
      pCostBuf2 + (((cl ++ [Nat.digits (2 ^ k) (I.edge e0).cost.natAbs]).take t.val).map List.length).sum) := by
    apply List.ext_getElem (by simp [hlen_cl1])
    intro r _ _; simp only [List.getElem_ofFn]
  have hof0 : List.ofFn (fun t : Fin cl.length =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) =
      List.ofFn (fun t : Fin xs.length =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) := by
    apply List.ext_getElem (by simp [hcl_len])
    intro r _ _; simp only [List.getElem_ofFn]
  rw [hof1, hsnoc, hof0]; simp

private theorem resFwd_sub_val {k L c fVal : ℕ} (hk1 : 1 ≤ k) (hle : fVal ≤ c)
    (hc : (Nat.digits (2 ^ k) c).length ≤ L) (hf : (Nat.digits (2 ^ k) fVal).length ≤ L) :
    let aL := padLimbs (Nat.digits (2 ^ k) c) L
    let bL := padLimbs (Nat.digits (2 ^ k) fVal) L
    let zs := subLimbs k aL bL
    aL.length = L ∧ bL.length = L ∧ Limbs k aL ∧ Limbs k bL ∧
    zs.length = L ∧ Limbs k zs ∧ Nat.ofDigits (2 ^ k) zs = c - fVal := by
  dsimp only
  set aL := padLimbs (Nat.digits (2 ^ k) c) L
  set bL := padLimbs (Nat.digits (2 ^ k) fVal) L
  set zs := subLimbs k aL bL
  have hlen_a : aL.length = L := by simp only [aL, padLimbs, List.length_append, List.length_replicate]; omega
  have hlen_b : bL.length = L := by simp only [bL, padLimbs, List.length_append, List.length_replicate]; omega
  have hlim_a : Limbs k aL := limbs_padLimbs (digits_limbs hk1 _) L
  have hlim_b : Limbs k bL := limbs_padLimbs (digits_limbs hk1 _) L
  have hsub_len : zs.length = L := by
    rw [show zs = (carryRun (subStep k aL bL) aL.length).1 from rfl, length_carryRun, hlen_a]
  have hrun := subRun_spec hk1 hlim_a hlim_b (by omega : bL.length = aL.length) aL.length (le_refl _)
  have hsub_lim : Limbs k zs := hrun.2.2
  have hsub_eq : Nat.ofDigits (2 ^ k) zs + fVal = c + subBorrow k aL bL * (2 ^ k) ^ L := by
    have h1 := hrun.1
    rw [List.take_length, List.take_of_length_le (by omega)] at h1
    change Nat.ofDigits (2 ^ k) zs + Nat.ofDigits (2 ^ k) bL =
      Nat.ofDigits (2 ^ k) aL + subBorrow k aL bL * (2 ^ k) ^ aL.length at h1
    rw [hlen_a, show Nat.ofDigits (2 ^ k) aL = c by rw [ofDigits_padLimbs, Nat.ofDigits_digits],
        show Nat.ofDigits (2 ^ k) bL = fVal by rw [ofDigits_padLimbs, Nat.ofDigits_digits]] at h1
    exact h1
  have hzs_lt : Nat.ofDigits (2 ^ k) zs < (2 ^ k) ^ L := by
    have h1 := ofDigits_lt_pow_length hk1 hsub_lim
    rwa [hsub_len] at h1
  have hbor0 : subBorrow k aL bL = 0 := by
    by_contra hbne
    have h1 : (2 ^ k) ^ L ≤ subBorrow k aL bL * (2 ^ k) ^ L := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [hbor0, zero_mul, add_zero] at hsub_eq
  exact ⟨hlen_a, hlen_b, hlim_a, hlim_b, hsub_len, hsub_lim, by omega⟩

/-! ### `stage0ResFwdSub`: compute `(cap - f)` limbs and its canonical length -/

wram_def stage0ResFwdSub (lSub cLen : ℕ) (pA, pB, pOut, L, k) {
  d := lSub(pA, pB, pOut, L, k)
  capLen := cLen(pOut, L)
  return capLen
}

structure ResFwdSubData where
  k : ℕ
  L : ℕ
  c : ℕ
  fVal : ℕ

def stage0ResFwdSubSpec (w : ℕ) : Spec ResFwdSubData where
  pre := fun d args => ⨆ (pA : ℕ) (pB : ℕ) (pOut : ℕ),
    ⌜args = [pA, pB, pOut, d.L, d.k] ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ 1 ≤ d.L ∧ d.fVal ≤ d.c ∧
      (Nat.digits (2 ^ d.k) d.c).length ≤ d.L ∧
      (Nat.digits (2 ^ d.k) d.fVal).length ≤ d.L⌝ *
    Assn.list pA (padLimbs (Nat.digits (2 ^ d.k) d.c) d.L) *
    Assn.list pB (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) *
    Assn.list pOut (List.replicate d.L 0)
  post := fun d args res => ⨆ (pA : ℕ) (pB : ℕ) (pOut : ℕ),
    ⌜args = [pA, pB, pOut, d.L, d.k] ∧
      res = (Nat.digits (2 ^ d.k) (d.c - d.fVal)).length⌝ *
    Assn.list pA (padLimbs (Nat.digits (2 ^ d.k) d.c) d.L) *
    Assn.list pB (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) *
    Assn.list pOut (padLimbs (Nat.digits (2 ^ d.k) (d.c - d.fVal)) d.L)

theorem stage0ResFwdSub_meets {w : ℕ} {p : Program} {f lSub cLen : ℕ}
    {Tsub Tcan : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResFwdSub lSub cLen))
    (hsub : Meets w p lSub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length)) :
    Meets w p f ((stage0ResFwdSubSpec w).withCost fun d _ => Tsub d.L + Tcan d.L + 30) := by
  sep_enter d with hk1 h2k hL1 hle hc hf
  set aL := padLimbs (Nat.digits (2 ^ d.k) d.c) d.L
  set bL := padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L
  set zs := subLimbs d.k aL bL
  obtain ⟨hlen_a, hlen_b, hlim_a, hlim_b, hsub_len, hsub_lim, hsub_val⟩ :=
    resFwd_sub_val hk1 hle hc hf
  have hlen_a' : aL.length = d.L := hlen_a
  have hlen_b' : bL.length = d.L := hlen_b
  have hsub_len' : d.L = zs.length := hsub_len.symm
  have hrep_len : (List.replicate d.L 0).length = aL.length := by rw [List.length_replicate, hlen_a']
  sep_step from (d.k, aL, bL, List.replicate d.L 0)
  sep_step from (d.k, zs) with _ hpad_zs
  rw [hsub_val, hsub_len] at hpad_zs
  have hpad_atom : Assn.list pOut zs = Assn.list pOut (padLimbs (Nat.digits (2 ^ d.k) (d.c - d.fVal)) d.L) := by
    rw [hpad_zs]
  sep_apply hpad_atom
  sep_step
  · rw [hlen_a', ← hsub_len']; omega
  · rw [hcapLen, hsub_val]

/-! ### `stage0ResFwdStep`: single iteration of the forward residual pass -/

wram_def stage0ResFwdStep (fwdSub fwdEmit : ℕ)
    (pEdges, eOff, pShCapBuf, pFeasFlow, pCapBuf2, fOff, pCostBuf2, cOff, L, k, i, j,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut) {
  capLen := fwdSub(pShCapBuf + fOff, pFeasFlow + fOff, pCapBuf2 + fOff, L, k)
  if 0 < capLen {
    cLenE := fwdEmit(pEdges, eOff, pCapBuf2 + fOff, pCostBuf2, cOff, capLen, i, j,
      pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2)
    mem[pCOffOut] := cOff + cLenE
    return j + 1
  } else {
    mem[pCOffOut] := cOff
    return j
  }
}

structure ResFwdStepData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  cap : ℕ
  bufCap : ℕ
  cOffCell : ℕ
  i : ℕ
  hi : i < I.m

def stage0ResFwdStepSpec (w : ℕ) : Spec ResFwdStepData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let xs := resFwdPos d.I d.hv d.f d.i
    let cl := edgeCostLimbList d.I xs
    ⌜args = [pEdges, d.i * 11, pShCapBuf, pFeasFlow, pCapBuf2, d.i * d.L, pCostBuf2,
        cl.flatten.length, d.L, k, d.i, xs.length,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧ d.I.m ≤ d.cap ∧ totCostLimbs d.I ≤ d.bufCap ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧
      pCapBuf2 + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w ∧
      pTail2 + d.cap ≤ 2 ^ w ∧ pHead2 + d.cap ≤ 2 ^ w ∧
      pCapPtr2 + d.cap ≤ 2 ^ w ∧ pCapLen2 + d.cap ≤ 2 ^ w ∧
      pCostSign2 + d.cap ≤ 2 ^ w ∧ pCostPtr2 + d.cap ≤ 2 ^ w ∧
      pCostLen2 + d.cap ≤ 2 ^ w ∧ pOrigIdx2 + d.cap ≤ 2 ^ w ∧ d.cap < 2 ^ w ∧ d.L < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + e * d.L)
        (if hlt : e < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
        else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pCapBuf2 + e * d.L)
        (if e < d.i then
          (if hm : e < d.I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
           else [])
         else List.replicate d.L 0)) *
    Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0) *
    Assn.list pTail2 (xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0) *
    Assn.list pHead2 (xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0) *
    Assn.list pCapPtr2 (xs.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0) *
    Assn.list pCapLen2 (xs.map (fun e =>
      (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      List.replicate (d.cap - xs.length) 0) *
    Assn.list pCostSign2 (xs.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      List.replicate (d.cap - xs.length) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin xs.length =>
      pCostBuf2 + ((cl.take t.val).map List.length).sum) ++ List.replicate (d.cap - xs.length) 0) *
    Assn.list pCostLen2 (xs.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      List.replicate (d.cap - xs.length) 0) *
    Assn.list pOrigIdx2 (xs.map Fin.val ++ List.replicate (d.cap - xs.length) 0) *
    (pCOffOut ↦ d.cOffCell)
  post := fun d args res => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let xs0 := resFwdPos d.I d.hv d.f d.i
    let cl0 := edgeCostLimbList d.I xs0
    let xs1 := resFwdPos d.I d.hv d.f (d.i + 1)
    let cl1 := edgeCostLimbList d.I xs1
    ⌜args = [pEdges, d.i * 11, pShCapBuf, pFeasFlow, pCapBuf2, d.i * d.L, pCostBuf2,
        cl0.flatten.length, d.L, k, d.i, xs0.length,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      res = xs1.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + e * d.L)
        (if hlt : e < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
        else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pCapBuf2 + e * d.L)
        (if e < d.i + 1 then
          (if hm : e < d.I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
           else [])
         else List.replicate d.L 0)) *
    Assn.list pCostBuf2 (cl1.flatten ++ List.replicate (d.bufCap - cl1.flatten.length) 0) *
    Assn.list pTail2 (xs1.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs1.length) 0) *
    Assn.list pHead2 (xs1.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs1.length) 0) *
    Assn.list pCapPtr2 (xs1.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs1.length) 0) *
    Assn.list pCapLen2 (xs1.map (fun e =>
      (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      List.replicate (d.cap - xs1.length) 0) *
    Assn.list pCostSign2 (xs1.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      List.replicate (d.cap - xs1.length) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin xs1.length =>
      pCostBuf2 + ((cl1.take t.val).map List.length).sum) ++ List.replicate (d.cap - xs1.length) 0) *
    Assn.list pCostLen2 (xs1.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      List.replicate (d.cap - xs1.length) 0) *
    Assn.list pOrigIdx2 (xs1.map Fin.val ++ List.replicate (d.cap - xs1.length) 0) *
    (pCOffOut ↦ cl1.flatten.length)

theorem stage0ResFwdStep_meets {w : ℕ} {p : Program} {f fwdSub fwdEmit : ℕ}
    {Tfsub Tfe : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResFwdStep fwdSub fwdEmit))
    (hfsub : Meets w p fwdSub ((stage0ResFwdSubSpec w).withCost fun x _ => Tfsub x.L))
    (hfe : Meets w p fwdEmit ((stage0ResFwdEmitSpec w).withCost fun x _ =>
      Tfe (narrowMaxCostLimbs x.I))) :
    Meets w p f ((stage0ResFwdStepSpec w).withCost fun d _ =>
      Tfsub d.L + Tfe (narrowMaxCostLimbs d.I) + 70) := by
  sep_enter d with hL1 h2k1 hmcap htotBuf hcapDig hpE h11m hpSC hpFF hpCB2 hmL
    hpCoB hbufW hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hLW hnW
  set k := narrowLimbWidth d.I
  set e0 : Fin d.I.m := ⟨d.i, d.hi⟩
  set xs := resFwdPos d.I d.hv d.f d.i
  set cl := edgeCostLimbList d.I xs
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth d.I
  have hw16 : 16 < 2 ^ w := by
    have hpow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hb2k : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  have hxs_le : xs.length ≤ d.i := resFwdPos_length_le d.I d.hv d.f d.i
  have hxs_cap : xs.length < d.cap := by have := d.hi; omega
  have hmem : d.i ∈ Finset.range d.I.m := Finset.mem_range.mpr d.hi
  have hiL_lt : d.i * d.L < d.I.m * d.L := Nat.mul_lt_mul_of_pos_right d.hi (by omega)
  have hcpW : pCapBuf2 + d.i * d.L < 2 ^ w := by omega
  have hcap_i := (d.hf e0).2
  have hnn_i := (d.hf e0).1
  have hf_dig : (Nat.digits (2 ^ k) (d.f e0).toNat).length ≤ d.L :=
    le_trans (digits_length_mono hb2k (by omega : (d.f e0).toNat ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e0))
      (hcapDig e0)
  have hspSC : (∏ e ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + e * d.L)
        (if hlt : e < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
        else [])) =
      Assn.list (pShCapBuf + d.i * d.L)
        (padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e0)) d.L) *
      (∏ e ∈ (Finset.range d.I.m).erase d.i,
        Assn.list (pShCapBuf + e * d.L)
          (if hlt : e < d.I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
          else [])) := by
    rw [← Finset.mul_prod_erase _ _ hmem, dite_eq_left d.hi]
  have hspFF : (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) =
      Assn.list (pFeasFlow + d.i * d.L) (padLimbs (Nat.digits (2 ^ k) (d.f e0).toNat) d.L) *
      (∏ e ∈ (Finset.range d.I.m).erase d.i,
        Assn.list (pFeasFlow + e * d.L)
          (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) := by
    rw [← Finset.mul_prod_erase _ _ hmem, dite_eq_left d.hi]
  have hspCB : (∏ e ∈ Finset.range d.I.m,
      Assn.list (pCapBuf2 + e * d.L)
        (if e < d.i then
          (if hm : e < d.I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
           else [])
         else List.replicate d.L 0)) =
      Assn.list (pCapBuf2 + d.i * d.L) (List.replicate d.L 0) *
      (∏ e ∈ (Finset.range d.I.m).erase d.i,
        Assn.list (pCapBuf2 + e * d.L)
          (if e < d.i then
            (if hm : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k)
                (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
             else [])
           else List.replicate d.L 0)) := by
    rw [← Finset.mul_prod_erase _ _ hmem, ite_eq_right (by omega : ¬ d.i < d.i)]
  generalize hF_arr :
    (Assn.list pTail2 (xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0) *
     Assn.list pHead2 (xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0) *
     Assn.list pCapPtr2 (xs.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0) *
     Assn.list pCapLen2 (xs.map (fun e =>
       (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
       List.replicate (d.cap - xs.length) 0) *
     Assn.list pCostSign2 (xs.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
       List.replicate (d.cap - xs.length) 0) *
     Assn.list pCostPtr2 (List.ofFn (fun t : Fin xs.length =>
       pCostBuf2 + ((cl.take t.val).map List.length).sum) ++ List.replicate (d.cap - xs.length) 0) *
     Assn.list pCostLen2 (xs.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
       List.replicate (d.cap - xs.length) 0) *
     Assn.list pOrigIdx2 (xs.map Fin.val ++ List.replicate (d.cap - xs.length) 0)) = F_arr
  generalize hF_aux :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ e ∈ Finset.range d.I.m,
       Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])) *
     Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0) *
     (pCOffOut ↦ d.cOffCell)) = F_aux
  sep_apply hF_arr; sep_apply hF_aux
  sep_apply hspSC; sep_apply hspFF; sep_apply hspCB
  have hdiff_eq : (FlowReduction.shiftedGraph d.I d.hv).capacity e0 - (d.f e0).toNat =
      (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat := by omega
  have hcap_dig_e0 : (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e0)).length ≤ d.L :=
    hcapDig e0
  sep_step from (⟨k, d.L, (FlowReduction.shiftedGraph d.I d.hv).capacity e0, (d.f e0).toNat⟩ : ResFwdSubData)
  rw [hdiff_eq] at hcapLen ⊢
  sep_apply hspSC.symm; sep_apply hspFF.symm
  sep_apply resFwd_capBuf_next d.I d.hv d.f pCapBuf2 d.L d.i d.hi
  clear hspSC hspFF hspCB hdiff_eq hf_dig hcap_dig_e0
  have hsucc := resFwdPos_succ d.I d.hv d.f d.hi
  sep_step
  · have hpos : 0 < (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat := by
      rw [hcapLen] at hcond
      by_contra h0
      have heq0 : (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat = 0 := by omega
      rw [heq0] at hcond; simp at hcond
    have hsucc' : resFwdPos d.I d.hv d.f (d.i + 1) = xs ++ [e0] := by
      rw [hsucc, ite_eq_left hpos]
    have hcl_next : edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1)) =
        cl ++ [Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs] := by
      rw [hsucc']; simp [edgeCostLimbList, cl, k]
    have hflat_next : (edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1))).flatten =
        cl.flatten ++ Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs := by
      simp only [hcl_next, List.flatten_append, List.flatten_singleton]
    have hflat_le : (edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1))).flatten.length ≤ d.bufCap :=
      le_trans (edgeCostLimbList_flatten_len_le d.I _ (resFwdPos_nodup d.I d.hv d.f (d.i + 1))) htotBuf
    have hfitC_cur : cl.flatten.length + (Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs).length ≤ d.bufCap := by
      rw [hflat_next, List.length_append] at hflat_le; exact hflat_le
    subst F_aux F_arr; sep_norm
    generalize hF_cc :
      ((∏ e ∈ Finset.range d.I.m,
          Assn.list (pShCapBuf + e * d.L)
            (if hlt : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
            else [])) *
       (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])) *
       (∏ e ∈ Finset.range d.I.m,
          Assn.list (pCapBuf2 + e * d.L)
            (if e < d.i + 1 then
              (if hm : e < d.I.m then
                padLimbs (Nat.digits (2 ^ k)
                  (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
               else [])
             else List.replicate d.L 0)) *
       (pCOffOut ↦ d.cOffCell)) = F_cc
    sep_apply hF_cc
    have hcapLen_eq : capLen = (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat).length :=
      hcapLen
    have hcapLen_lt : capLen < 2 ^ w := by
      rw [hcapLen_eq]
      have hle_c : (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat ≤
          (FlowReduction.shiftedGraph d.I d.hv).capacity e0 :=
        Int.toNat_le.mpr (by have := (d.hf e0).1; omega)
      exact lt_of_le_of_lt (le_trans (digits_length_mono hb2k hle_c) (hcapDig e0)) hLW
    have hlen_m : ∀ (f : Fin d.I.m → ℕ),
        (xs.map f ++ List.replicate (d.cap - xs.length) 0).length = d.cap := by
      intro f; simp only [List.length_append, List.length_map, List.length_replicate]; omega
    have hlen_cp : (List.ofFn (fun t : Fin xs.length =>
        pCostBuf2 + ((cl.take t.val).map List.length).sum) ++ List.replicate (d.cap - xs.length) 0).length = d.cap := by
      simp only [List.length_append, List.length_ofFn, List.length_replicate]; omega
    have hArcOk : ResArcEmitOk w
        ⟨d.I, d.hv, e0, pCapBuf2 + d.i * d.L, capLen, cl.flatten, d.bufCap, d.cap, xs.length,
          xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0,
          xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0,
          xs.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0,
          xs.map (fun e => (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
            List.replicate (d.cap - xs.length) 0,
          xs.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++ List.replicate (d.cap - xs.length) 0,
          List.ofFn (fun t : Fin xs.length => pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
            List.replicate (d.cap - xs.length) 0,
          xs.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
            List.replicate (d.cap - xs.length) 0,
          xs.map Fin.val ++ List.replicate (d.cap - xs.length) 0⟩
        pEdges pCostBuf2 pTail2 pHead2 pCapPtr2 pCapLen2 pCostSign2 pCostPtr2 pCostLen2 pOrigIdx2 :=
      ⟨hpE, h11m, hfitC_cur, hpCoB, hbufW, hxs_cap, hcapW, hnW, hcpW, hcapLen_lt,
        hlen_m _, hlen_m _, hlen_m _, hlen_m _, hlen_m _, hlen_cp, hlen_m _, hlen_m _,
        hpT, hpH, hpCP, hpCL, hpCS, hpCoP, hpCoL, hpOI⟩
    clear hlen_m hlen_cp
    sep_step from (⟨d.I, d.hv, e0, pCapBuf2 + d.i * d.L, capLen, cl.flatten, d.bufCap, d.cap, xs.length,
        xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0,
        xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0,
        xs.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0,
        xs.map (fun e => (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
          List.replicate (d.cap - xs.length) 0,
        xs.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++ List.replicate (d.cap - xs.length) 0,
        List.ofFn (fun t : Fin xs.length => pCostBuf2 + ((cl.take t.val).map List.length).sum) ++
          List.replicate (d.cap - xs.length) 0,
        xs.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
          List.replicate (d.cap - xs.length) 0,
        xs.map Fin.val ++ List.replicate (d.cap - xs.length) 0⟩ : ResArcEmitData)
    clear hArcOk
    rw [hcapLen_eq]
    subst F_cc; sep_norm
    rw [resFwd_set_map xs _ e0 d.cap hxs_cap, resFwd_set_map xs _ e0 d.cap hxs_cap,
        resFwd_set_map xs _ e0 d.cap hxs_cap, resFwd_set_map xs _ e0 d.cap hxs_cap,
        resFwd_set_map xs _ e0 d.cap hxs_cap, resFwd_set_map xs _ e0 d.cap hxs_cap,
        resFwd_set_map xs _ e0 d.cap hxs_cap,
        resFwd_set_costPtrs d.I d.hv d.f pCostBuf2 d.cap d.i d.hi hpos hxs_cap,
        ← hsucc', ← hflat_next]
    have hc_lt : cl.flatten.length + cLenE < 2 ^ w := by
      rw [hcLenE]; dsimp only [k] at hfitC_cur; omega
    sep_step
    have hcoff_eq : cl.flatten.length + cLenE =
        (edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1))).flatten.length := by
      rw [hcLenE, hflat_next, List.length_append]
    have hcoff_eq2 : cl.flatten.length + (Nat.digits (2 ^ k) (d.I.edge e0).cost.natAbs).length =
        (edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1))).flatten.length := by
      rw [hflat_next, List.length_append]
    rw [hcoff_eq, hcoff_eq2]
    sep_step
    · rw [hsucc']; simp
  · have hzero : ¬ (0 < (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat) := by
      rw [hcapLen] at hcond
      intro hpos
      have hne0 : (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat ≠ 0 := by omega
      have hlen_pos : 0 < (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e0 : ℤ) - d.f e0).toNat).length := by
        rw [Nat.length_digits _ _ hb2k hne0]; omega
      omega
    have hsucc' : resFwdPos d.I d.hv d.f (d.i + 1) = xs := by
      rw [hsucc, ite_eq_right hzero, List.append_nil]
    subst F_aux F_arr; sep_norm
    sep_step
    have hcl_next : cl = edgeCostLimbList d.I (resFwdPos d.I d.hv d.f (d.i + 1)) := by
      rw [hsucc']
    rw [hcl_next, ← hsucc']
    sep_step
    · rw [hsucc']
    · rw [hsucc']

/-! ### `stage0ResPassFwd`: build forward residual arcs -/

wram_def stage0ResPassFwd (fwdStep : ℕ)
    (pEdges, m, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, L, k,
     pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut) {
  j := 0
  cOff := 0
  eOff := 0
  fOff := 0
  for i in 0 .. m {
    j := fwdStep(pEdges, eOff, pShCapBuf, pFeasFlow, pCapBuf2, fOff, pCostBuf2, cOff, L, k, i, j,
      pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut)
    cOff := mem[pCOffOut]
    eOff := eOff + 11
    fOff := fOff + L
  }
  mem[pCOffOut] := cOff
  return j
}

structure ResPassFwdData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  cap : ℕ
  bufCap : ℕ
  cOff0 : ℕ

def stage0ResPassFwdSpec (w : ℕ) : Spec ResPassFwdData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, d.I.m, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, d.L, k,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧ d.I.m ≤ d.cap ∧ totCostLimbs d.I ≤ d.bufCap ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧
      pCapBuf2 + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pCostBuf2 + d.bufCap < 2 ^ w ∧ d.bufCap < 2 ^ w ∧
      pTail2 + d.cap ≤ 2 ^ w ∧ pHead2 + d.cap ≤ 2 ^ w ∧
      pCapPtr2 + d.cap ≤ 2 ^ w ∧ pCapLen2 + d.cap ≤ 2 ^ w ∧
      pCostSign2 + d.cap ≤ 2 ^ w ∧ pCostPtr2 + d.cap ≤ 2 ^ w ∧
      pCostLen2 + d.cap ≤ 2 ^ w ∧ pOrigIdx2 + d.cap ≤ 2 ^ w ∧ d.cap < 2 ^ w ∧ d.L < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m, Assn.list (pCapBuf2 + i * d.L) (List.replicate d.L 0)) *
    Assn.list pCostBuf2 (List.replicate d.bufCap 0) *
    Assn.list pTail2 (List.replicate d.cap 0) *
    Assn.list pHead2 (List.replicate d.cap 0) *
    Assn.list pCapPtr2 (List.replicate d.cap 0) *
    Assn.list pCapLen2 (List.replicate d.cap 0) *
    Assn.list pCostSign2 (List.replicate d.cap 0) *
    Assn.list pCostPtr2 (List.replicate d.cap 0) *
    Assn.list pCostLen2 (List.replicate d.cap 0) *
    Assn.list pOrigIdx2 (List.replicate d.cap 0) *
    (pCOffOut ↦ d.cOff0)
  post := fun d args res => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pCapBuf2 : ℕ)
      (pCostBuf2 : ℕ) (pTail2 : ℕ) (pHead2 : ℕ) (pCapPtr2 : ℕ) (pCapLen2 : ℕ)
      (pCostSign2 : ℕ) (pCostPtr2 : ℕ) (pCostLen2 : ℕ) (pOrigIdx2 : ℕ) (pCOffOut : ℕ),
    let k := narrowLimbWidth d.I
    let fwd := resFwdPos d.I d.hv d.f d.I.m
    let fwdCL := edgeCostLimbList d.I fwd
    ⌜args = [pEdges, d.I.m, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, d.L, k,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut] ∧
      res = fwd.length⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pCapBuf2 + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k)
            (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩ : ℤ) - d.f ⟨i, hlt⟩).toNat) d.L
        else [])) *
    Assn.list pCostBuf2 (fwdCL.flatten ++ List.replicate (d.bufCap - fwdCL.flatten.length) 0) *
    Assn.list pTail2 (fwd.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pHead2 (fwd.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCapPtr2 (fwd.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCapLen2 (fwd.map (fun e =>
      (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostSign2 (fwd.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostPtr2 (List.ofFn (fun t : Fin fwd.length =>
      pCostBuf2 + ((fwdCL.take t.val).map List.length).sum) ++ List.replicate (d.cap - fwd.length) 0) *
    Assn.list pCostLen2 (fwd.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
      List.replicate (d.cap - fwd.length) 0) *
    Assn.list pOrigIdx2 (fwd.map Fin.val ++ List.replicate (d.cap - fwd.length) 0) *
    (pCOffOut ↦ fwdCL.flatten.length)

theorem stage0ResPassFwd_meets {w : ℕ} {p : Program} {f fwdStep : ℕ}
    {Tstep : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ResPassFwd fwdStep))
    (hstep : Meets w p fwdStep ((stage0ResFwdStepSpec w).withCost fun x _ =>
      Tstep (narrowMaxCostLimbs x.I) x.L)) :
    Meets w p f ((stage0ResPassFwdSpec w).withCost fun d _ =>
      (Tstep (narrowMaxCostLimbs d.I) d.L + 65) * d.I.m + 50) := by
  sep_enter d with hL1 h2k1 hmcap htotBuf hcapDig hpE h11m hpSC hpFF hpCB2 hmL
    hpCoB hbufW hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hcapW hLW hnW
  set k := narrowLimbWidth d.I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth d.I
  have hw16 : 16 < 2 ^ w := by
    have hpow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hinit_cb : (∏ i ∈ Finset.range d.I.m, Assn.list (pCapBuf2 + i * d.L) (List.replicate d.L 0)) =
      (∏ i ∈ Finset.range d.I.m,
        Assn.list (pCapBuf2 + i * d.L)
          (if i < 0 then
            (if hm : i < d.I.m then
              padLimbs (Nat.digits (2 ^ k)
                (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hm⟩ : ℤ) - d.f ⟨i, hm⟩).toNat) d.L
             else [])
           else List.replicate d.L 0)) := by
    refine Finset.prod_congr rfl fun _ _ => by simp
  sep_apply hinit_cb
  sep_step; sep_step; sep_step; sep_step
  sep_for (fun i (cCell : ℕ) =>
      let xs := resFwdPos d.I d.hv d.f i
      let cl := edgeCostLimbList d.I xs
      ⟨[pEdges, d.I.m, pShCapBuf, pFeasFlow, pCapBuf2, pCostBuf2, d.L, k,
        pTail2, pHead2, pCapPtr2, pCapLen2, pCostSign2, pCostPtr2, pCostLen2, pOrigIdx2, pCOffOut,
        xs.length, cl.flatten.length, i * 11, i * d.L, i],
       i ≤ d.I.m,
       (Tstep (narrowMaxCostLimbs d.I) d.L + 50) * (d.I.m - i) + 20,
       [Assn.list 0 (narrowEncode d.I),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pShCapBuf + e * d.L)
            (if hlt : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hlt⟩)) d.L
            else [])),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if hlt : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨e, hlt⟩).toNat) d.L else [])),
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pCapBuf2 + e * d.L)
            (if e < i then
              (if hm : e < d.I.m then
                padLimbs (Nat.digits (2 ^ k)
                  (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
               else [])
             else List.replicate d.L 0)),
        Assn.list pCostBuf2 (cl.flatten ++ List.replicate (d.bufCap - cl.flatten.length) 0),
        Assn.list pTail2 (xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pHead2 (xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pCapPtr2 (xs.map (fun e => pCapBuf2 + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pCapLen2 (xs.map (fun e =>
          (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) - d.f e).toNat).length) ++
          List.replicate (d.cap - xs.length) 0),
        Assn.list pCostSign2 (xs.map (fun e => if (d.I.edge e).cost < 0 then 1 else 0) ++
          List.replicate (d.cap - xs.length) 0),
        Assn.list pCostPtr2 (List.ofFn (fun t : Fin xs.length =>
          pCostBuf2 + ((cl.take t.val).map List.length).sum) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pCostLen2 (xs.map (fun e => (Nat.digits (2 ^ k) (d.I.edge e).cost.natAbs).length) ++
          List.replicate (d.cap - xs.length) 0),
        Assn.list pOrigIdx2 (xs.map Fin.val ++ List.replicate (d.cap - xs.length) 0),
        (pCOffOut ↦ cCell)]⟩)
    with cCell
  · have hi : i < d.I.m := hhi
    have hnext11 : i * 11 + 11 = (i + 1) * 11 := by ring
    have hnextL : i * d.L + d.L = (i + 1) * d.L := by ring
    have hnextL_lt : (i + 1) * d.L ≤ d.I.m * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step from (⟨d.I, d.hv, d.f, d.hf, d.L, d.cap, d.bufCap, cCell, i, hi⟩ : ResFwdStepData)
    sep_step; sep_step; sep_step
  · have hcb_final : (∏ e ∈ Finset.range d.I.m,
        Assn.list (pCapBuf2 + e * d.L)
          (if e < d.I.m then
            (if hm : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k)
                (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
             else [])
           else List.replicate d.L 0)) =
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pCapBuf2 + e * d.L)
            (if hm : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k)
                (((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨e, hm⟩ : ℤ) - d.f ⟨e, hm⟩).toNat) d.L
            else [])) := by
      refine Finset.prod_congr rfl fun e he => by rw [ite_eq_left (Finset.mem_range.mp he)]
    sep_apply hcb_final
    sep_step; sep_step

end MinCostFlow.NarrowProg
