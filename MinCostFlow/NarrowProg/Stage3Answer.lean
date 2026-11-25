module

public import MinCostFlow.NarrowProg.Stage3OneEdge
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 3, item 6: answer assembly (`stage3Fill`) and disjoint copy to address `0` (`stage3Answer`)

Assembles `out = 1 :: (List.finRange I.m).flatMap (fun e => intWords k (ans e))` in freshly
allocated heap `pAns`, splits `Assn.list 0 (narrowEncode I)` at `out.length` using
`narrowAnswer_length_le_encode`, and copies `pAns` to address `0` via disjoint `WordRAM.Std.copy`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### `stage3Fill`: assemble the full answer list into `pAns` -/

wram_def stage3Fill (oneEdge : ℕ)
    (pEdges, pFeasFlow, pHFwd, pHRev, pAns, pTmpA, pTmpB, pRes, m, L, k) {
  mem[pAns] := 1
  outPos := 1
  eOff := 0
  fOff := 0
  for i in 0 .. m {
    loSign := mem[pEdges + eOff + 2]
    loLen := mem[pEdges + eOff + 3]
    loPtr := mem[pEdges + eOff + 4]
    wLen := oneEdge(loPtr, loSign, loLen, pFeasFlow + fOff, pHFwd + fOff, pHRev + fOff,
      pTmpA, pTmpB, pRes, pAns + outPos, L, k)
    outPos := outPos + wLen
    eOff := eOff + 11
    fOff := fOff + L
  }
  return outPos
}

structure Stage3Data where
  I : Instance
  hv : I.IsValid
  L : ℕ
  fVal : Fin I.m → ℕ
  hFwdVal : Fin I.m → ℕ
  hRevVal : Fin I.m → ℕ

/-- The restored integral flow vector `lower + f + hFwd - hRev`. -/
def stage3Flow (d : Stage3Data) (e : Fin d.I.m) : ℤ :=
  (d.I.edge e).lower + (d.fVal e : ℤ) + (d.hFwdVal e : ℤ) - (d.hRevVal e : ℤ)

/-- Prefix of the encoded answer after emitting the first `i` edges. -/
def stage3AnsPrefix (d : Stage3Data) (i : ℕ) : List ℕ :=
  1 :: ((List.finRange d.I.m).take i).flatMap fun e =>
    intWords (narrowLimbWidth d.I) (stage3Flow d e)

/-- Full encoded answer list `1 :: flatMap (intWords k) (stage3Flow d)`. -/
def stage3AnsList (d : Stage3Data) : List ℕ :=
  1 :: (List.finRange d.I.m).flatMap fun e =>
    intWords (narrowLimbWidth d.I) (stage3Flow d e)

theorem stage3AnsPrefix_zero (d : Stage3Data) : stage3AnsPrefix d 0 = [1] := by
  simp [stage3AnsPrefix]

theorem stage3AnsPrefix_succ (d : Stage3Data) {i : ℕ} (hi : i < d.I.m) :
    stage3AnsPrefix d (i + 1) =
      stage3AnsPrefix d i ++ intWords (narrowLimbWidth d.I) (stage3Flow d ⟨i, hi⟩) := by
  unfold stage3AnsPrefix
  have htake : (List.finRange d.I.m).take (i + 1) =
      (List.finRange d.I.m).take i ++ [⟨i, hi⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hi]), Option.toList_some]
    simp
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.cons_append]

theorem stage3AnsPrefix_full (d : Stage3Data) : stage3AnsPrefix d d.I.m = stage3AnsList d := by
  unfold stage3AnsPrefix stage3AnsList
  rw [List.take_of_length_le (by simp)]

theorem stage3Flow_bounds (d : Stage3Data)
    (hcaps : ∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper)
    (hrev : ∀ e, d.hRevVal e ≤ d.fVal e)
    (hsum : ∀ e, d.fVal e + d.hFwdVal e ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e) :
    ∀ e : Fin d.I.m, (d.I.edge e).lower ≤ stage3Flow d e ∧ stage3Flow d e ≤ (d.I.edge e).upper := by
  intro e
  have h1 := hcaps e
  have h2 := hrev e
  have h3 := hsum e
  change d.fVal e + d.hFwdVal e ≤ ((d.I.edge e).upper - (d.I.edge e).lower).toNat at h3
  unfold stage3Flow
  omega

theorem stage3AnsPrefix_length_le (d : Stage3Data)
    (hcaps : ∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper)
    (hltL : ∀ e : Fin d.I.m,
      (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length < d.L ∧
      (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).upper.natAbs).length < d.L)
    (hrev : ∀ e, d.hRevVal e ≤ d.fVal e)
    (hsum : ∀ e, d.fVal e + d.hFwdVal e ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e) :
    ∀ i ≤ d.I.m, (stage3AnsPrefix d i).length ≤ 1 + i * (2 + d.L) := by
  have hk1 : 1 ≤ narrowLimbWidth d.I := one_le_narrowLimbWidth d.I
  have hb : 1 < 2 ^ narrowLimbWidth d.I := by have := two_le_pow hk1; omega
  have hfb := stage3Flow_bounds d hcaps hrev hsum
  intro i
  induction i with
  | zero => intro _; simp [stage3AnsPrefix]
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    rw [stage3AnsPrefix_succ d (by omega), List.length_append, intWords_length]
    set e : Fin d.I.m := ⟨i, by omega⟩
    have hbd := hfb e
    have habs : (stage3Flow d e).natAbs ≤ max (d.I.edge e).lower.natAbs (d.I.edge e).upper.natAbs := by
      omega
    have hdig : (Nat.digits (2 ^ narrowLimbWidth d.I) (stage3Flow d e).natAbs).length ≤ d.L := by
      rcases le_total (d.I.edge e).lower.natAbs (d.I.edge e).upper.natAbs with hlu | hul
      · have h1 : (stage3Flow d e).natAbs ≤ (d.I.edge e).upper.natAbs := by omega
        exact le_trans (digits_length_mono hb h1) (le_of_lt (hltL e).2)
      · have h1 : (stage3Flow d e).natAbs ≤ (d.I.edge e).lower.natAbs := by omega
        exact le_trans (digits_length_mono hb h1) (le_of_lt (hltL e).1)
    have hmul : 1 + (i + 1) * (2 + d.L) = 1 + i * (2 + d.L) + (2 + d.L) := by ring
    omega

def stage3FillSpec (w : ℕ) : Spec Stage3Data where
  pre := fun d args => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pHFwd : ℕ) (pHRev : ℕ)
      (pAns : ℕ) (pTmpA : ℕ) (pTmpB : ℕ) (pRes : ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pFeasFlow, pHFwd, pHRev, pAns, pTmpA, pTmpB, pRes, d.I.m, d.L, k] ∧
      2 * k ≤ w ∧ 1 ≤ d.L ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < d.L) ∧
      (∀ e, d.hRevVal e ≤ d.fVal e) ∧
      (∀ e, d.fVal e + d.hFwdVal e ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e) ∧
      (∀ e, (Nat.digits (2 ^ k) (d.fVal e)).length ≤ d.L ∧
            (Nat.digits (2 ^ k) (d.hFwdVal e)).length ≤ d.L ∧
            (Nat.digits (2 ^ k) (d.hRevVal e)).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ pHFwd + d.I.m * d.L ≤ 2 ^ w ∧
      pHRev + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pAns + (1 + d.I.m * (2 + d.L)) ≤ 2 ^ w ∧ 1 + d.I.m * (2 + d.L) < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if h : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.fVal ⟨i, h⟩)) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHFwd + i * d.L)
        (if h : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hFwdVal ⟨i, h⟩)) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHRev + i * d.L)
        (if h : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hRevVal ⟨i, h⟩)) d.L else [])) *
    Assn.list pAns (List.replicate (1 + d.I.m * (2 + d.L)) 0) *
    Assn.list pTmpA (List.replicate d.L 0) *
    Assn.list pTmpB (List.replicate d.L 0) *
    Assn.list pRes (List.replicate d.L 0)
  post := fun d args v => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pHFwd : ℕ) (pHRev : ℕ)
      (pAns : ℕ) (pTmpA : ℕ) (pTmpB : ℕ) (pRes : ℕ),
    let k := narrowLimbWidth d.I
    let out := stage3AnsList d
    ⌜args = [pEdges, pFeasFlow, pHFwd, pHRev, pAns, pTmpA, pTmpB, pRes, d.I.m, d.L, k] ∧
      v = out.length ∧ out.length ≤ 1 + d.I.m * (2 + d.L)⌝ *
    Assn.list 0 (narrowEncode d.I) *
    Assn.list pAns out * Assn.gc

private theorem stage3_pull_flows (d : Stage3Data) (pFeasFlow pHFwd pHRev i : ℕ)
    (hhi : i < d.I.m) :
    let e : Fin d.I.m := ⟨i, hhi⟩
    let k := narrowLimbWidth d.I
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + j * d.L)
        (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.fVal ⟨j, h⟩)) d.L else [])) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (pHFwd + j * d.L)
        (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hFwdVal ⟨j, h⟩)) d.L else [])) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (pHRev + j * d.L)
        (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hRevVal ⟨j, h⟩)) d.L else [])) =
    Assn.list (pFeasFlow + i * d.L) (padLimbs (Nat.digits (2 ^ k) (d.fVal e)) d.L) *
    Assn.list (pHFwd + i * d.L) (padLimbs (Nat.digits (2 ^ k) (d.hFwdVal e)) d.L) *
    Assn.list (pHRev + i * d.L) (padLimbs (Nat.digits (2 ^ k) (d.hRevVal e)) d.L) *
    ((∏ j ∈ (Finset.range d.I.m).erase i,
       Assn.list (pFeasFlow + j * d.L)
         (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.fVal ⟨j, h⟩)) d.L else [])) *
     (∏ j ∈ (Finset.range d.I.m).erase i,
       Assn.list (pHFwd + j * d.L)
         (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hFwdVal ⟨j, h⟩)) d.L else [])) *
     (∏ j ∈ (Finset.range d.I.m).erase i,
       Assn.list (pHRev + j * d.L)
         (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hRevVal ⟨j, h⟩)) d.L else []))) := by
  have hmem : i ∈ Finset.range d.I.m := Finset.mem_range.mpr hhi
  dsimp only
  rw [Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pFeasFlow + j * d.L)
          (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.fVal ⟨j, h⟩)) d.L else [])),
      Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pHFwd + j * d.L)
          (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hFwdVal ⟨j, h⟩)) d.L else [])),
      Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (pHRev + j * d.L)
          (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hRevVal ⟨j, h⟩)) d.L else []))]
  simp only [hhi, ↓reduceDIte]; ac_rfl

private theorem stage3_pull_enc (I : Instance) (hv : I.IsValid) (i : ℕ) (hhi : i < I.m) :
    let e : Fin I.m := ⟨i, hhi⟩
    let k := narrowLimbWidth I
    Assn.list 0 (narrowEncode I) =
    Assn.list (edgeLoPtr I e) (Nat.digits (2 ^ k) (I.edge e).lower.natAbs) *
    ((0 ↦ k) * (1 ↦ I.n) * (2 ↦ I.m) *
     (edgeStartPos I e.val ↦ (I.edge e).tail) *
     (edgeStartPos I e.val + 1 ↦ (I.edge e).head) *
     (edgeStartPos I e.val + 2 ↦ if (I.edge e).lower < 0 then 1 else 0) *
     (edgeStartPos I e.val + 2 + 1 ↦
       (Nat.digits (2 ^ k) (I.edge e).lower.natAbs).length) *
     Assn.list (edgeHiPos I e) (intWords k (I.edge e).upper) *
     Assn.list (edgeCostPos I e) (intWords k (I.edge e).cost) *
     (∏ j ∈ (Finset.range I.m).erase i,
       Assn.list (edgeStartPos I j)
         (if h : j < I.m then narrowEdgeWords k (I.edge ⟨j, h⟩) else [])) *
     (∏ v ∈ Finset.range I.n,
       Assn.list (demStartPos I v)
         (if _ : v < I.n then intWords k (I.d v) else []))) := by
  have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
  dsimp only
  rw [list_narrowEncode_split I hv,
      Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (edgeStartPos I j)
          (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []))]
  simp only [hhi, ↓reduceDIte]
  rw [list_narrowEdgeWords I ⟨i, hhi⟩,
      list_intWords (edgeStartPos I i + 2) (narrowLimbWidth I) (I.edge ⟨i, hhi⟩).lower]
  have hloA : Assn.list (edgeStartPos I i + 2 + 2)
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨i, hhi⟩).lower.natAbs) =
      Assn.list (edgeLoPtr I ⟨i, hhi⟩)
        (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨i, hhi⟩).lower.natAbs) := rfl
  rw [hloA]; dsimp only; ac_rfl

theorem stage3Fill_meets {w : ℕ} {p : Program} {f oneEdge : ℕ} {T1 : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage3Fill oneEdge))
    (h1 : Meets w p oneEdge ((stage3OneEdgeSpec w).withCost fun d _ => T1 d.L)) :
    Meets w p f ((stage3FillSpec w).withCost fun d _ => (T1 d.L + 110) * d.I.m + 50) := by
  sep_enter d with h2k hL1 hcaps hltL hrev hsum hdigs hpE h11m hpF hpFwd hpRev hmL hpAns hAnsB
  have hk3 : 3 ≤ narrowLimbWidth d.I := three_le_narrowLimbWidth d.I
  have hplen := stage3AnsPrefix_length_le d hcaps hltL hrev hsum
  have hinit_ans :
      Assn.list pAns (List.replicate (1 + d.I.m * (2 + d.L)) 0) =
      (pAns ↦ 0) * Assn.list (pAns + 1) (List.replicate (d.I.m * (2 + d.L)) 0) := by
    rw [show 1 + d.I.m * (2 + d.L) = d.I.m * (2 + d.L) + 1 by omega, List.replicate_succ,
      Assn.list_cons]
  sep_apply hinit_ans
  sep_step; sep_step; sep_step; sep_step
  have hstart_ans :
      (pAns ↦ 1) * Assn.list (pAns + 1) (List.replicate (d.I.m * (2 + d.L)) 0) =
      Assn.list pAns (stage3AnsPrefix d 0) *
      Assn.list (pAns + (stage3AnsPrefix d 0).length)
        (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d 0).length) 0) := by
    simp [stage3AnsPrefix, Assn.list_cons, Assn.list_nil]
  sep_apply hstart_ans
  sep_for (fun i (t : List ℕ × List ℕ × List ℕ × ℕ × ℕ × ℕ × ℕ) =>
      ⟨[pEdges, pFeasFlow, pHFwd, pHRev, pAns, pTmpA, pTmpB, pRes, d.I.m, d.L, narrowLimbWidth d.I,
        (stage3AnsPrefix d i).length, i * 11, i * d.L, i, t.2.2.2.1, t.2.2.2.2.1,
        t.2.2.2.2.2.1, t.2.2.2.2.2.2],
      i ≤ d.I.m ∧ t.1.length = d.L ∧ t.2.1.length = d.L ∧ t.2.2.1.length = d.L,
      (T1 d.L + 95) * (d.I.m - i) + 15,
      [Assn.list 0 (narrowEncode d.I),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pFeasFlow + j * d.L)
           (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.fVal ⟨j, h⟩)) d.L else []),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pHFwd + j * d.L)
           (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hFwdVal ⟨j, h⟩)) d.L else []),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pHRev + j * d.L)
           (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hRevVal ⟨j, h⟩)) d.L else []),
       Assn.list pAns (stage3AnsPrefix d i),
       Assn.list (pAns + (stage3AnsPrefix d i).length)
         (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length) 0),
       Assn.list pTmpA t.1, Assn.list pTmpB t.2.1, Assn.list pRes t.2.2.1]⟩)
    with ⟨tmpA, tmpB, res, loS, loL, loP, wL⟩
  · let e : Fin d.I.m := ⟨i, hhi⟩
    have hmem : i ∈ Finset.range d.I.m := Finset.mem_range.mpr hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))
    have hcurE : Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec d.I e) := by simp [e, hhi]
    sep_apply hcurE
    have hedgeRec_len : (edgeRec d.I e).length = 11 := rfl
    sep_step; sep_step; sep_step
    simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at hloSign hloLen hloPtr
    subst loSign loLen loPtr
    sep_apply hcurE.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))).symm
    -- Pull flow blocks and edge lower limbs in two single rewrites
    sep_apply stage3_pull_flows d pFeasFlow pHFwd pHRev i hhi
    sep_apply stage3_pull_enc d.I d.hv i hhi
    have hpref_le := hplen i (by omega)
    have hrem_ge : d.L + 2 ≤ 1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length := by
      have : (i + 1) * (2 + d.L) ≤ d.I.m * (2 + d.L) := Nat.mul_le_mul_right _ (by omega)
      have : (i + 1) * (2 + d.L) = i * (2 + d.L) + (2 + d.L) := by ring
      omega
    have hiL_lt : i * d.L < d.I.m * d.L := Nat.mul_lt_mul_of_pos_right hhi (by omega)
    have hout_lt : (stage3AnsPrefix d i).length < 1 + d.I.m * (2 + d.L) := by
      have : i * (2 + d.L) < d.I.m * (2 + d.L) := Nat.mul_lt_mul_of_pos_right hhi (by omega)
      omega
    generalize hF :
      (((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
        (edgeStartPos d.I e.val ↦ (d.I.edge e).tail) *
        (edgeStartPos d.I e.val + 1 ↦ (d.I.edge e).head) *
        (edgeStartPos d.I e.val + 2 ↦ if (d.I.edge e).lower < 0 then 1 else 0) *
        (edgeStartPos d.I e.val + 2 + 1 ↦
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length) *
        Assn.list (edgeHiPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).upper) *
        Assn.list (edgeCostPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).cost) *
        (∏ j ∈ (Finset.range d.I.m).erase i,
          Assn.list (edgeStartPos d.I j)
            (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
        (∏ v ∈ Finset.range d.I.n,
          Assn.list (demStartPos d.I v)
            (if h : v < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d v) else []))) *
       ((∏ j ∈ (Finset.range d.I.m).erase i,
          Assn.list (pFeasFlow + j * d.L)
            (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.fVal ⟨j, h⟩)) d.L else [])) *
        (∏ j ∈ (Finset.range d.I.m).erase i,
          Assn.list (pHFwd + j * d.L)
            (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hFwdVal ⟨j, h⟩)) d.L else [])) *
        (∏ j ∈ (Finset.range d.I.m).erase i,
          Assn.list (pHRev + j * d.L)
            (if h : j < d.I.m then padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (d.hRevVal ⟨j, h⟩)) d.L else []))) *
       (∏ j ∈ Finset.range d.I.m,
         Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else [])) *
       Assn.list pAns (stage3AnsPrefix d i)) = F
    have hcap_e := hcaps e
    have hlo_e := (hltL e).1
    have hhi_e := (hltL e).2
    have hrev_e := hrev e
    have hsum_e : d.fVal e + d.hFwdVal e ≤ ((d.I.edge e).upper - (d.I.edge e).lower).toNat := hsum e
    have hf_e := (hdigs e).1
    have hfwd_e := (hdigs e).2.1
    have hrevd_e := (hdigs e).2.2
    have hdst_len : (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length) 0).length =
        1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length := List.length_replicate
    have hdst_fit : pAns + (stage3AnsPrefix d i).length +
        (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length) 0).length ≤ 2 ^ w := by
      rw [hdst_len]; omega
    have hL2_lt : d.L + 2 < 2 ^ w := by
      have : 1 * (2 + d.L) ≤ d.I.m * (2 + d.L) := Nat.mul_le_mul_right _ (by omega)
      omega
    sep_apply hF
    generalize hkEq : narrowLimbWidth d.I = kv at hk3 h2k hlo_e hhi_e hf_e hfwd_e hrevd_e ⊢
    generalize houtPos : (stage3AnsPrefix d i).length = outPos at hdst_len hdst_fit hrem_ge hpref_le hout_lt ⊢
    generalize hdstEq : List.replicate (1 + d.I.m * (2 + d.L) - outPos) 0 = dstBuf
      at hdst_len hdst_fit ⊢
    have hrem_ge' : d.L + 2 ≤ dstBuf.length := by rw [hdst_len]; exact hrem_ge
    sep_step from (⟨kv, d.L, (d.I.edge e).lower, (d.I.edge e).upper,
      d.fVal e, d.hFwdVal e, d.hRevVal e, tmpA, tmpB, res, dstBuf⟩ : Stage3OneEdgeData)
      with hwLen_le htmpA1 htmpB1 hres1
    subst hdstEq
    subst houtPos
    subst hkEq
    subst F; sep_norm
    -- Reassemble narrowEncode I and flow arrays in two rewrites
    sep_apply (stage3_pull_enc d.I d.hv i hhi).symm
    sep_apply (stage3_pull_flows d pFeasFlow pHFwd pHRev i hhi).symm
    -- Advance pAns prefix
    have hans_join :
        Assn.list pAns (stage3AnsPrefix d i) *
        Assn.list (pAns + (stage3AnsPrefix d i).length)
          (intWords (narrowLimbWidth d.I) (stage3Flow d e) ++
            (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d i).length) 0).drop
              (intWords (narrowLimbWidth d.I) (stage3Flow d e)).length) =
        Assn.list pAns (stage3AnsPrefix d (i + 1)) *
        Assn.list (pAns + (stage3AnsPrefix d (i + 1)).length)
          (List.replicate (1 + d.I.m * (2 + d.L) - (stage3AnsPrefix d (i + 1)).length) 0) := by
      rw [Assn.list_append, ← mul_assoc, ← Assn.list_append, ← stage3AnsPrefix_succ d hhi,
        List.drop_replicate, stage3AnsPrefix_succ d hhi, List.length_append]
      simp only [Nat.sub_sub, add_assoc, e]
    sep_apply hans_join
    have hpos_next : (stage3AnsPrefix d i).length +
        (intWords (narrowLimbWidth d.I) (stage3Flow d e)).length =
        (stage3AnsPrefix d (i + 1)).length := by
      rw [stage3AnsPrefix_succ d hhi, List.length_append]
    have hpos_lt : (stage3AnsPrefix d (i + 1)).length ≤ 1 + d.I.m * (2 + d.L) := by
      have := hplen (i + 1) (by omega)
      have : (i + 1) * (2 + d.L) ≤ d.I.m * (2 + d.L) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hmul_next : i * d.L + d.L = (i + 1) * d.L := by ring
    have hmul_lt : (i + 1) * d.L ≤ d.I.m * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step; sep_step; sep_step
  · have hfull_len : (stage3AnsList d).length ≤ 1 + d.I.m * (2 + d.L) := by
      rw [← stage3AnsPrefix_full]; exact hplen d.I.m le_rfl
    rw [stage3AnsPrefix_full]
    sep_step
    · apply Assn.NoDebt.le_gc
      apply Assn.NoDebt.mul
      · exact Assn.noDebt_credits (by simp only [sub_self, mul_zero, zero_add]; decide)
      · repeat (first | apply Assn.NoDebt.mul | (apply Assn.noDebt_prod; intro _ _; apply Assn.noDebt_list) | apply Assn.noDebt_list)

/-! ### Top-level `stage3Answer`: allocate, assemble, and copy to address `0` -/

/-- Exact space allocated by `stage3Answer`: `1 + m * (2 + L) + 3 * L`. -/
def stage3AnswerSpace (m L : ℕ) : ℕ :=
  1 + m * (2 + L) + 3 * L

private theorem split_free_stage3 {h m L w : ℕ} (hfit : h + stage3AnswerSpace m L < 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate (1 + m * (2 + L)) 0) *
      Assn.list (h + (1 + m * (2 + L))) (List.replicate L 0) *
      Assn.list (h + (1 + m * (2 + L)) + L) (List.replicate L 0) *
      Assn.list (h + (1 + m * (2 + L)) + L + L) (List.replicate L 0) *
      Assn.free (h + stage3AnswerSpace m L) (2 ^ w - (h + stage3AnswerSpace m L)) := by
  unfold stage3AnswerSpace at hfit ⊢
  set ansSz := 1 + m * (2 + L)
  have hsp : h + (ansSz + 3 * L) = h + ansSz + L + L + L := by ring
  rw [hsp]
  have h1 : 2 ^ w - h = ansSz + (2 ^ w - (h + ansSz)) := by omega
  have h2 : 2 ^ w - (h + ansSz) = L + (2 ^ w - (h + ansSz + L)) := by omega
  have h3 : 2 ^ w - (h + ansSz + L) = L + (2 ^ w - (h + ansSz + L + L)) := by omega
  have h4 : 2 ^ w - (h + ansSz + L + L) = L + (2 ^ w - (h + ansSz + L + L + L)) := by omega
  rw [h1, Assn.free_add, h2, Assn.free_add, h3, Assn.free_add, h4, Assn.free_add]
  simp only [← mul_assoc]

wram_def stage3Answer (fill arrCopy : ℕ)
    (pEdges, pFeasFlow, pHFwd, pHRev, m, L, k, h) {
  ansSz := 1 + m * (2 + L)
  pAns := h
  pTmpA := pAns + ansSz
  pTmpB := pTmpA + L
  pRes := pTmpB + L
  outLen := fill(pEdges, pFeasFlow, pHFwd, pHRev, pAns, pTmpA, pTmpB, pRes, m, L, k)
  d := arrCopy(pAns, 0, outLen)
  return outLen
}

def stage3AnswerSpec (w : ℕ) : Spec Stage3Data where
  pre := fun d args => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pFeasFlow, pHFwd, pHRev, d.I.m, d.L, k, h] ∧
      2 * k ≤ w ∧ 1 ≤ d.L ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < d.L) ∧
      (∀ e, d.hRevVal e ≤ d.fVal e) ∧
      (∀ e, d.fVal e + d.hFwdVal e ≤ (FlowReduction.shiftedGraph d.I d.hv).capacity e) ∧
      (∀ e, (Nat.digits (2 ^ k) (d.fVal e)).length ≤ d.L ∧
            (Nat.digits (2 ^ k) (d.hFwdVal e)).length ≤ d.L ∧
            (Nat.digits (2 ^ k) (d.hRevVal e)).length ≤ d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ pHFwd + d.I.m * d.L ≤ 2 ^ w ∧
      pHRev + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      h + stage3AnswerSpace d.I.m d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.fVal ⟨i, hlt⟩)) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHFwd + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hFwdVal ⟨i, hlt⟩)) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHRev + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.hRevVal ⟨i, hlt⟩)) d.L else [])) *
    Assn.free h (2 ^ w - h)
  post := fun d args v => ⨆ (pEdges : ℕ) (pFeasFlow : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (h : ℕ),
    let k := narrowLimbWidth d.I
    let out := stage3AnsList d
    let h' := h + stage3AnswerSpace d.I.m d.L
    ⌜args = [pEdges, pFeasFlow, pHFwd, pHRev, d.I.m, d.L, k, h] ∧ v = out.length⌝ *
    Assn.list 0 out * Assn.gc * Assn.free h' (2 ^ w - h')

theorem stage3Answer_meets {w : ℕ} {p : Program} {f fill arrCopy : ℕ}
    {Tfill : ℕ → ℕ → ℕ} {Tcopy : ℕ → ℕ}
    (hmonoC : ∀ a b, a ≤ b → Tcopy a ≤ Tcopy b)
    (hp : p.procs[f]? = some (stage3Answer fill arrCopy))
    (hfill : Meets w p fill ((stage3FillSpec w).withCost fun d _ => Tfill d.I.m d.L))
    (hcopy : Meets w p arrCopy ((copySpec w).withCost fun x _ => Tcopy x.1.length)) :
    Meets w p f ((stage3AnswerSpec w).withCost fun d _ =>
      Tfill d.I.m d.L + Tcopy (1 + d.I.m * (2 + d.L)) + 80) := by
  sep_enter d with h2k hL1 hcaps hltL hrev hsum hdigs hpE h11m hpF hpFwd hpRev hmL hfit
  have hk3 : 3 ≤ narrowLimbWidth d.I := three_le_narrowLimbWidth d.I
  have hw2 : 1 < 2 ^ w := by
    have : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsp : stage3AnswerSpace d.I.m d.L = 1 + d.I.m * (2 + d.L) + 3 * d.L := rfl
  sep_apply split_free_stage3 (h := h) (m := d.I.m) (L := d.L) (w := w) hfit
  sep_step; sep_step; sep_step; sep_step; sep_step
  -- Call stage3Fill
  sep_step from d with hout_le
  -- Split Assn.list 0 (narrowEncode d.I) at out.length using narrowAnswer_length_le_encode
  have hout_le_enc : (stage3AnsList d).length ≤ (narrowEncode d.I).length :=
    narrowAnswer_length_le_encode d.I (stage3Flow d) (stage3Flow_bounds d hcaps hrev hsum)
  have henc_split :
      Assn.list 0 (narrowEncode d.I) =
      Assn.list 0 ((narrowEncode d.I).take (stage3AnsList d).length) *
      Assn.list (stage3AnsList d).length ((narrowEncode d.I).drop (stage3AnsList d).length) := by
    conv_lhs => rw [← List.take_append_drop (stage3AnsList d).length (narrowEncode d.I)]
    rw [Assn.list_append, List.length_take, Nat.min_eq_left hout_le_enc, zero_add]
  sep_apply henc_split
  generalize hF2 :
    (Assn.list (stage3AnsList d).length ((narrowEncode d.I).drop (stage3AnsList d).length) *
     Assn.free (h + stage3AnswerSpace d.I.m d.L) (2 ^ w - (h + stage3AnswerSpace d.I.m d.L))) = F2
  sep_apply hF2
  sep_step from (stage3AnsList d, (narrowEncode d.I).take (stage3AnsList d).length)
  subst F2; sep_norm
  have hcopy_le : Tcopy (stage3AnsList d).length ≤ Tcopy (1 + d.I.m * (2 + d.L)) :=
    hmonoC _ _ hout_le
  sep_step

theorem stage3Answer_meets_direct {w : ℕ} {p : Program}
    {f pCopy lAdd lSub lCmp cLen arrCopy netFlow addLower oneEdge fill : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage3Answer fill arrCopy))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlAdd : p.procs[lAdd]? = some limbsAdd)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (harrCopy : p.procs[arrCopy]? = some copy)
    (hnetFlow : p.procs[netFlow]? = some (stage3NetFlow lSub lAdd))
    (haddLower : p.procs[addLower]? = some (stage3AddLower pCopy lAdd lSub lCmp))
    (honeEdge : p.procs[oneEdge]? = some (stage3OneEdge netFlow addLower cLen arrCopy))
    (hfill : p.procs[fill]? = some (stage3Fill oneEdge)) :
    Meets w p f ((stage3AnswerSpec w).withCost fun d _ =>
      400 * d.I.m * d.L + 590 * d.I.m + 160) := by
  have h1 := padCopy_meets (w := w) (by omega) hpCopy
  have h2 := limbsAdd_meets (w := w) hlAdd
  have h3 := limbsSub_meets (w := w) hlSub
  have h4 := limbsCmp_meets (w := w) hw hlCmp
  have h5 := canonLen_meets (w := w) hcLen
  have h6 := copy_meets (w := w) harrCopy
  have h7n := stage3NetFlow_meets (w := w)
    (Tsub := fun L => 60 * L + 30) (Tadd := fun L => 50 * L + 30)
    hnetFlow h3 h2
  have h7a := stage3AddLower_meets (w := w)
    (Tpad := fun L => 55 * L + 35) (Tadd := fun L => 50 * L + 30)
    (Tsub := fun L => 60 * L + 30) (Tcmp := fun L => 40 * L + 20)
    haddLower h1 h2 h3 h4
  have h7 := stage3OneEdge_meets (w := w)
    (Tnet := fun L => (60 * L + 30) + (50 * L + 30) + 30)
    (TaddL := fun L => (55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (40 * L + 20) + 60)
    (Tcan := fun L => 45 * L + 25) (Tcopy := fun L => 17 * L + 10)
    (fun _ _ h => by omega) honeEdge h7n h7a h5 h6
  have h8 := stage3Fill_meets (w := w)
    (T1 := fun L => ((60 * L + 30) + (50 * L + 30) + 30) +
      ((55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (40 * L + 20) + 60) +
      (45 * L + 25) + (17 * L + 10) + 100)
    hfill h7
  exact (stage3Answer_meets
    (Tfill := fun m L => (((60 * L + 30) + (50 * L + 30) + 30) +
      ((55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (40 * L + 20) + 60) +
      (45 * L + 25) + (17 * L + 10) + 100 + 110) * m + 50)
    (Tcopy := fun L => 17 * L + 10)
    (fun _ _ h => by omega) hp h8 h6).withCost_mono fun d _ => by nlinarith

theorem stage3Answer_meetsO {w : ℕ} {p : Program}
    {f pCopy lAdd lSub lCmp cLen arrCopy netFlow addLower oneEdge fill : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage3Answer fill arrCopy))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlAdd : p.procs[lAdd]? = some limbsAdd)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (harrCopy : p.procs[arrCopy]? = some copy)
    (hnetFlow : p.procs[netFlow]? = some (stage3NetFlow lSub lAdd))
    (haddLower : p.procs[addLower]? = some (stage3AddLower pCopy lAdd lSub lCmp))
    (honeEdge : p.procs[oneEdge]? = some (stage3OneEdge netFlow addLower cLen arrCopy))
    (hfill : p.procs[fill]? = some (stage3Fill oneEdge)) :
    MeetsO w p f (stage3AnswerSpec w) fun d _ => d.I.m * (d.L + 1) + 1 :=
  MeetsO.of_meets
    (stage3Answer_meets_direct hw hp hpCopy hlAdd hlSub hlCmp hcLen harrCopy
      hnetFlow haddLower honeEdge hfill)
    ⟨590, fun ⟨d, _⟩ => by dsimp only; nlinarith⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage3AnswerMod`, polymorphic over any name type `ι`. -/
structure Stage3AnswerNames (ι : Type) where
  padCopy : ι
  limbsAdd : ι
  limbsSub : ι
  limbsCmp : ι
  canonLen : ι
  copy : ι
  netFlow : ι
  addLower : ι
  oneEdge : ι
  fill : ι
  stage3Answer : ι

/-- Self-contained polymorphic module for Stage 3 (`stage3Answer`). -/
def stage3AnswerMod {ι : Type} (names : Stage3AnswerNames ι) : Module ι :=
  ⟨[(names.padCopy, fun _ => padCopy),
    (names.limbsAdd, fun _ => limbsAdd),
    (names.limbsSub, fun _ => limbsSub),
    (names.limbsCmp, fun _ => limbsCmp),
    (names.canonLen, fun _ => canonLen),
    (names.copy, fun _ => copy),
    (names.netFlow, fun idx => stage3NetFlow (idx names.limbsSub) (idx names.limbsAdd)),
    (names.addLower, fun idx =>
      stage3AddLower (idx names.padCopy) (idx names.limbsAdd)
        (idx names.limbsSub) (idx names.limbsCmp)),
    (names.oneEdge, fun idx =>
      stage3OneEdge (idx names.netFlow) (idx names.addLower)
        (idx names.canonLen) (idx names.copy)),
    (names.fill, fun idx => stage3Fill (idx names.oneEdge)),
    (names.stage3Answer, fun idx => stage3Answer (idx names.fill) (idx names.copy))]⟩

theorem stage3AnswerMod_noRand {ι : Type} (names : Stage3AnswerNames ι) :
    (stage3AnswerMod names).NoRand := by
  wram_no_rand

theorem stage3AnswerMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : Stage3AnswerNames ι} (hw : 2 < 2 ^ w)
    (hp : (stage3AnswerMod names).Placed p idx) :
    MeetsO w p (idx names.stage3Answer) (stage3AnswerSpec w) fun d _ => d.I.m * (d.L + 1) + 1 :=
  stage3Answer_meetsO hw
    (hp.get (n := names.stage3Answer) (b := fun idx =>
      stage3Answer (idx names.fill) (idx names.copy)) (by simp [stage3AnswerMod]))
    (hp.get (n := names.padCopy) (b := fun _ => padCopy) (by simp [stage3AnswerMod]))
    (hp.get (n := names.limbsAdd) (b := fun _ => limbsAdd) (by simp [stage3AnswerMod]))
    (hp.get (n := names.limbsSub) (b := fun _ => limbsSub) (by simp [stage3AnswerMod]))
    (hp.get (n := names.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage3AnswerMod]))
    (hp.get (n := names.canonLen) (b := fun _ => canonLen) (by simp [stage3AnswerMod]))
    (hp.get (n := names.copy) (b := fun _ => copy) (by simp [stage3AnswerMod]))
    (hp.get (n := names.netFlow) (b := fun idx =>
      stage3NetFlow (idx names.limbsSub) (idx names.limbsAdd)) (by simp [stage3AnswerMod]))
    (hp.get (n := names.addLower) (b := fun idx =>
      stage3AddLower (idx names.padCopy) (idx names.limbsAdd)
        (idx names.limbsSub) (idx names.limbsCmp)) (by simp [stage3AnswerMod]))
    (hp.get (n := names.oneEdge) (b := fun idx =>
      stage3OneEdge (idx names.netFlow) (idx names.addLower)
        (idx names.canonLen) (idx names.copy)) (by simp [stage3AnswerMod]))
    (hp.get (n := names.fill) (b := fun idx => stage3Fill (idx names.oneEdge))
      (by simp [stage3AnswerMod]))

end MinCostFlow.NarrowProg
