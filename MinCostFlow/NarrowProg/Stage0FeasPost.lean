module

public import MinCostFlow.NarrowProg.Stage0FeasSat
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4 (post-Stage-1 scatter & wrapper): `Stage0FeasPost`

Verifies `stage0FeasScatter` (scattering original positive-edge flows into `pFeasFlow`) and
`stage0FeasPost` (combining `stage0FeasSatCheck` and conditional `stage0FeasScatter`, and proving
feasibility / infeasibility certificates).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### `stage0FeasScatter`: scatter original positive-edge flows into `pFeasFlow` -/

wram_def stage0FeasScatter (copyFlow : ℕ)
    (m1Orig, pOrigIdx1, pFlow1, K1, pFeasFlow, L) {
  off := 0
  for j in 0 .. m1Orig {
    d := copyFlow(pFlow1 + off, K1, pFeasFlow + mem[pOrigIdx1 + j] * L, L)
    off := off + K1
  }
  return 0
}

structure FeasScatterData where
  I : Instance
  hv : I.IsValid
  L : ℕ
  K1 : ℕ
  f' : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ
  flowLimbs : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → List ℕ

def stage0FeasScatterSpec (w : ℕ) : Spec FeasScatterData where
  pre := fun d args => ⨆ (pOrigIdx1 : ℕ) (pFlow1 : ℕ) (pFeasFlow : ℕ),
    let P := FlowReduction.buildFeasibilityInstance d.I d.hv
    let P' := P.withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    let k := narrowLimbWidth d.I
    ⌜args = [orig.length, pOrigIdx1, pFlow1, d.K1, pFeasFlow, d.L] ∧
      1 ≤ d.L ∧
      (∀ j : Fin P'.m, 0 ≤ d.f' j ∧ Limbs k (d.flowLimbs j) ∧ (d.flowLimbs j).length = d.K1 ∧
        ((Nat.ofDigits (2 ^ k) (d.flowLimbs j) : ℕ) : ℤ) = d.f' j) ∧
      (∀ j : Fin P'.m, (Nat.digits (2 ^ k) (d.f' j).toNat).length ≤ d.L) ∧
      pOrigIdx1 + d.I.m ≤ 2 ^ w ∧
      P'.m * d.K1 < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      3 * d.I.m < 2 ^ w ∧ d.K1 < 2 ^ w ∧ d.L < 2 ^ w⌝ *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    (∏ j ∈ Finset.range P'.m,
      Assn.list (pFlow1 + j * d.K1) (if h : j < P'.m then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0))
  post := fun d args v => ⨆ (pOrigIdx1 : ℕ) (pFlow1 : ℕ) (pFeasFlow : ℕ),
    let P := FlowReduction.buildFeasibilityInstance d.I d.hv
    let P' := P.withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    let k := narrowLimbWidth d.I
    ⌜args = [orig.length, pOrigIdx1, pFlow1, d.K1, pFeasFlow, d.L] ∧ v = 0⌝ *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    (∏ j ∈ Finset.range P'.m,
      Assn.list (pFlow1 + j * d.K1) (if h : j < P'.m then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if h : e < d.I.m then
          padLimbs (Nat.digits (2 ^ k)
            (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
        else []))

private theorem feasScatter_slot_next (d : FeasScatterData) (j : ℕ)
    (hj : j < (feasOrigPos d.I d.hv d.I.m).length)
    (hfl : ∀ r : Fin (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges.m,
      0 ≤ d.f' r ∧ ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (d.flowLimbs r) : ℕ) : ℤ) = d.f' r)
    (pFeasFlow : ℕ) :
    let P := FlowReduction.buildFeasibilityInstance d.I d.hv
    let orig := feasOrigPos d.I d.hv d.I.m
    let k := narrowLimbWidth d.I
    let hj' : j < P.withoutZeroEdges.m := by
      have hm := feas_m_eq d.I d.hv; change P.withoutZeroEdges.m = _ at hm; omega
    let e0 := orig[j]'hj
    Assn.list (pFeasFlow + e0.val * d.L)
      (padLimbs (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hj'⟩))) d.L) *
    (∏ e ∈ (Finset.range d.I.m).erase e0.val,
      Assn.list (pFeasFlow + e * d.L)
        (if h : e < d.I.m then
          if ∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = ⟨e, h⟩ then
            padLimbs (Nat.digits (2 ^ k)
              (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
          else List.replicate d.L 0
        else [])) =
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if h : e < d.I.m then
          if ∃ r : Fin orig.length, r.val < j + 1 ∧ orig[r.val] = ⟨e, h⟩ then
            padLimbs (Nat.digits (2 ^ k)
              (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
          else List.replicate d.L 0
        else [])) := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set orig := feasOrigPos d.I d.hv d.I.m
  set k := narrowLimbWidth d.I
  have hj' : j < P.withoutZeroEdges.m := by
    have hm := feas_m_eq d.I d.hv; change P.withoutZeroEdges.m = _ at hm; omega
  set e0 := orig[j]'hj
  have hmem : e0.val ∈ Finset.range d.I.m := Finset.mem_range.mpr e0.isLt
  have hnodup : orig.Nodup := feasOrigPos_nodup d.I d.hv d.I.m
  have hval_eq : Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hj'⟩) =
      (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e0)).toNat := by
    have hs := feas_scatterPositive_orig d.I d.hv d.f' j hj
    dsimp only at hs
    rw [hs]
    have ⟨hnn, hof⟩ := hfl ⟨j, hj'⟩
    omega
  rw [← Finset.mul_prod_erase _ _ hmem]
  congr 1
  · have hex : ∃ r : Fin orig.length, r.val < j + 1 ∧ orig[r.val] = ⟨e0.val, e0.isLt⟩ :=
      ⟨⟨j, hj⟩, by simp, by simp [e0]⟩
    rw [dite_eq_left e0.isLt, ite_eq_left hex, hval_eq]
  · refine Finset.prod_congr rfl fun e he => ?_
    have hne : e ≠ e0.val := (Finset.mem_erase.mp he).1
    have hlt : e < d.I.m := Finset.mem_range.mp (Finset.mem_erase.mp he).2
    rw [dite_eq_left hlt, dite_eq_left hlt]
    have hiff : (∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = ⟨e, hlt⟩) ↔
        (∃ r : Fin orig.length, r.val < j + 1 ∧ orig[r.val] = ⟨e, hlt⟩) := by
      constructor
      · rintro ⟨r, hr, heq⟩; exact ⟨r, by omega, heq⟩
      · rintro ⟨r, hr, heq⟩
        by_cases hri : r.val = j
        · exfalso; apply hne
          have : orig[r.val] = e0 := by simp [e0, hri]
          have := congrArg Fin.val (heq.symm.trans this)
          exact this
        · exact ⟨r, by omega, heq⟩
    rw [if_congr hiff rfl rfl]

theorem stage0FeasScatter_meets {w : ℕ} {p : Program} {f copyFlow : ℕ}
    {Tcf : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0FeasScatter copyFlow))
    (hcf : Meets w p copyFlow (copyFlowLimbsSpec.withCost fun x _ =>
      Tcf x.src.length x.dst0.length)) :
    Meets w p f ((stage0FeasScatterSpec w).withCost fun d _ =>
      (Tcf d.K1 d.L + 75) * (feasOrigPos d.I d.hv d.I.m).length + 40) := by
  sep_enter d with hL1 hfl hdigLe hpOI hmK hpFF hmL h3m hKW hLW
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set P' := P.withoutZeroEdges
  set orig := feasOrigPos d.I d.hv d.I.m
  set k := narrowLimbWidth d.I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hm_eq : P'.m = orig.length + (feasArtPos d.I d.I.n).length + (feasArtNeg d.I d.I.n).length :=
    feas_m_eq d.I d.hv
  have horig_le_m : orig.length ≤ d.I.m := by
    have h1 := List.length_filter_le (fun e => decide (0 < (FlowReduction.shiftedGraph d.I d.hv).capacity e))
      ((List.finRange d.I.m).take d.I.m)
    simp only [List.length_take, List.length_finRange, Nat.min_self] at h1
    exact h1
  have hnodup : orig.Nodup := feasOrigPos_nodup d.I d.hv d.I.m
  have hinit : (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) =
      (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if h : e < d.I.m then
            if ∃ r : Fin orig.length, r.val < 0 ∧ orig[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ k)
                (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
            else List.replicate d.L 0
          else [])) := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hlt := Finset.mem_range.mp he
    rw [dite_eq_left hlt]; simp
  sep_apply hinit
  sep_step
  sep_for (fun j (d0 : ℕ) => (⟨[orig.length, pOrigIdx1, pFlow1, d.K1, pFeasFlow, d.L,
      j * d.K1, j, d0],
      j ≤ orig.length,
      (Tcf d.K1 d.L + 60) * (orig.length - j) + 15,
      [Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0),
       ∏ r ∈ Finset.range P'.m,
         Assn.list (pFlow1 + r * d.K1) (if h : r < P'.m then d.flowLimbs ⟨r, h⟩ else []),
       ∏ e ∈ Finset.range d.I.m,
         Assn.list (pFeasFlow + e * d.L)
           (if h : e < d.I.m then
             if ∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = ⟨e, h⟩ then
               padLimbs (Nat.digits (2 ^ k)
                 (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
             else List.replicate d.L 0
           else [])]⟩ : SInv))
    with d0
  · have hi_P' : j < P'.m := by omega
    have hi_mem : j ∈ Finset.range P'.m := Finset.mem_range.mpr hi_P'
    set e0 := orig[j]'hhi
    have he0_mem : e0.val ∈ Finset.range d.I.m := Finset.mem_range.mpr e0.isLt
    have hget_oi : (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0)[j]'(by
        simp only [List.length_append, List.length_map, List.length_replicate]; omega) = e0.val := by
      rw [List.getElem_append_left (by simp [hhi]), List.getElem_map]
    have hnot_before : ¬ ∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = e0 := by
      rintro ⟨r, hr, heq⟩
      have hidx := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnodup) (a₁ := r) (a₂ := ⟨j, hhi⟩) heq)
      dsimp only at hidx; omega
    have hspFl : (∏ r ∈ Finset.range P'.m,
        Assn.list (pFlow1 + r * d.K1) (if h : r < P'.m then d.flowLimbs ⟨r, h⟩ else [])) =
        Assn.list (pFlow1 + j * d.K1) (d.flowLimbs ⟨j, hi_P'⟩) *
        (∏ r ∈ (Finset.range P'.m).erase j,
          Assn.list (pFlow1 + r * d.K1) (if h : r < P'.m then d.flowLimbs ⟨r, h⟩ else [])) := by
      rw [← Finset.mul_prod_erase _ _ hi_mem, dite_eq_left hi_P']
    have hspFF : (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if h : e < d.I.m then
            if ∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ k)
                (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
            else List.replicate d.L 0
          else [])) =
        Assn.list (pFeasFlow + e0.val * d.L) (List.replicate d.L 0) *
        (∏ e ∈ (Finset.range d.I.m).erase e0.val,
          Assn.list (pFeasFlow + e * d.L)
            (if h : e < d.I.m then
              if ∃ r : Fin orig.length, r.val < j ∧ orig[r.val] = ⟨e, h⟩ then
                padLimbs (Nat.digits (2 ^ k)
                  (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
              else List.replicate d.L 0
            else [])) := by
      rw [← Finset.mul_prod_erase _ _ he0_mem, dite_eq_left e0.isLt, ite_eq_right hnot_before]
    sep_apply hspFl
    sep_apply hspFF
    have he0L_lt : e0.val * d.L < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right d.L (le_of_lt e0.isLt)) hmL
    have hiK_lt : j * d.K1 < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right d.K1 (le_of_lt hi_P')) hmK
    have hfl_i := hfl ⟨j, hi_P'⟩
    have hof_toNat : Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hi_P'⟩) = (d.f' ⟨j, hi_P'⟩).toNat := by
      omega
    have hdig_i : (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hi_P'⟩))).length ≤
        (List.replicate d.L 0).length := by
      rw [hof_toNat, List.length_replicate]; exact hdigLe ⟨j, hi_P'⟩
    let cd : CopyFlowLimbsData := ⟨k, d.flowLimbs ⟨j, hi_P'⟩, List.replicate d.L 0⟩
    have hcd_src : cd.src.length = d.K1 := hfl_i.2.2.1
    have hcd_dst : cd.dst0.length = d.L := List.length_replicate
    have hcd_lim : Limbs cd.k cd.src := hfl_i.2.1
    have hdst_atom : Assn.list (pFeasFlow + e0.val * d.L) (List.replicate d.L 0) =
        Assn.list (pFeasFlow + (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0)[j]'(by
          simp only [List.length_append, List.length_map, List.length_replicate]; omega) * d.L)
          (List.replicate d.L 0) := by
      rw [hget_oi]
    sep_apply hdst_atom
    sep_step from cd
    · have hdst_back : Assn.list (pFeasFlow + (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0)[j]'(by
            simp only [List.length_append, List.length_map, List.length_replicate]; omega) * d.L)
          (padLimbs (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hi_P'⟩)))
            (List.replicate d.L 0).length) =
          Assn.list (pFeasFlow + e0.val * d.L)
          (padLimbs (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) (d.flowLimbs ⟨j, hi_P'⟩))) d.L) := by
        rw [hget_oi, List.length_replicate]
      sep_apply hdst_back
      sep_apply hspFl.symm
      have hnext := feasScatter_slot_next d j hhi (fun r => ⟨(hfl r).1, (hfl r).2.2.2⟩) pFeasFlow
      sep_apply hnext
      have hi1K_eq : j * d.K1 + d.K1 = (j + 1) * d.K1 := by ring
      have hi1K_lt : (j + 1) * d.K1 < 2 ^ w :=
        lt_of_le_of_lt (Nat.mul_le_mul_right d.K1 (show j + 1 ≤ P'.m by omega)) hmK
      sep_step
      · rw [hcd_src, hcd_dst]; push_cast; ring_nf; omega
    · by_cases hK0 : d.K1 = 0
      · rw [hK0, mul_zero, add_zero]; omega
      · dsimp only [cd] at hcd_src; omega
  · have hfinal : (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if h : e < d.I.m then
            if ∃ r : Fin orig.length, r.val < orig.length ∧ orig[r.val] = ⟨e, h⟩ then
              padLimbs (Nat.digits (2 ^ k)
                (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
            else List.replicate d.L 0
          else [])) =
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if h : e < d.I.m then
              padLimbs (Nat.digits (2 ^ k)
                (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
            else [])) := by
      refine Finset.prod_congr rfl fun e he => ?_
      have hlt := Finset.mem_range.mp he
      rw [dite_eq_left hlt, dite_eq_left hlt]
      by_cases hmem : (⟨e, hlt⟩ : Fin d.I.m) ∈ orig
      · obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
        rw [ite_eq_left (⟨⟨idx, hidx⟩, hidx, hget⟩)]
      · have hno : ¬ ∃ r : Fin orig.length, r.val < orig.length ∧ orig[r.val] = ⟨e, hlt⟩ := by
          rintro ⟨r, _, heq⟩; exact hmem (heq ▸ List.getElem_mem r.isLt)
        rw [ite_eq_right hno]
        have hz := feas_scatterPositive_not_orig d.I d.hv d.f' ⟨e, hlt⟩ hmem
        rw [hz]
        simp [padLimbs]
    sep_apply hfinal
    sep_step

/-! ### `stage0FeasPost`: combine saturation check, conditional scatter, and optimality certificates -/

wram_def stage0FeasPost (satCheck scatter : ℕ)
    (m1Orig, m1, pCapPtr1, pCapLen1, pOrigIdx1, pOut1, pFeasFlow, L) {
  pFlow1 := mem[pOut1]
  K1 := mem[pOut1 + 1]
  ok := satCheck(m1Orig, m1, pCapPtr1, pCapLen1, pFlow1, K1)
  if ok == 1 {
    d := scatter(m1Orig, pOrigIdx1, pFlow1, K1, pFeasFlow, L)
  }
  return ok
}

structure FeasPostData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  L : ℕ
  pShCapBuf : ℕ
  pShDemBuf : ℕ
  f' : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ
  flowLimbs : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → List ℕ

def stage0FeasPostSpec (w : ℕ) : Spec FeasPostData where
  pre := fun d args => ⨆ (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pOrigIdx1 : ℕ)
      (pOut1 : ℕ) (pFeasFlow : ℕ) (pFlow1 : ℕ),
    let P := FlowReduction.buildFeasibilityInstance d.I d.hv
    let P' := P.withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    let k := narrowLimbWidth d.I
    let K1 := bitScalingPhases P' / k + 2
    ⌜args = [orig.length, P'.m, pCapPtr1, pCapLen1, pOrigIdx1, pOut1, pFeasFlow, d.L] ∧
      1 ≤ d.L ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length ≤ d.L) ∧
      (∀ j (hj : j < P'.m), CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) ∧
        Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j []) = P'.capacity ⟨j, hj⟩) ∧
      P'.Optimal (fun j => (d.f' j : ℝ)) ∧
      (∀ j : Fin P'.m, 0 ≤ d.f' j ∧ Limbs k (d.flowLimbs j) ∧ (d.flowLimbs j).length = K1 ∧
        ((Nat.ofDigits (2 ^ k) (d.flowLimbs j) : ℕ) : ℤ) = d.f' j) ∧
      (∀ j : Fin P'.m, (Nat.digits (2 ^ k) (d.f' j).toNat).length ≤ d.L) ∧
      pCapPtr1 + P'.m ≤ 2 ^ w ∧ pCapLen1 + P'.m ≤ 2 ^ w ∧
      pOrigIdx1 + d.I.m ≤ 2 ^ w ∧ pOut1 + 2 ≤ 2 ^ w ∧
      P'.m * K1 < 2 ^ w ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      3 * d.I.m < 2 ^ w ∧ K1 < 2 ^ w ∧ d.L < 2 ^ w⌝ *
    Assn.list pCapPtr1 (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L) *
    Assn.list pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).getD j 0)
        ((feasCapLimbs d.I d.hv).getD j [])) *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    Assn.list pOut1 [pFlow1, K1] *
    (∏ j ∈ Finset.range P'.m,
      Assn.list (pFlow1 + j * K1) (if h : j < P'.m then d.flowLimbs ⟨j, h⟩ else [])) *
    (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0))
  post := fun d args ok => ⨆ (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pOrigIdx1 : ℕ)
      (pOut1 : ℕ) (pFeasFlow : ℕ),
    let P := FlowReduction.buildFeasibilityInstance d.I d.hv
    let P' := P.withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    let k := narrowLimbWidth d.I
    let f := fun e : Fin d.I.m => P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e)
    ⌜args = [orig.length, P'.m, pCapPtr1, pCapLen1, pOrigIdx1, pOut1, pFeasFlow, d.L] ∧
      ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).getD j 0)
        ((feasCapLimbs d.I d.hv).getD j [])) *
    (∏ e ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + e * d.L)
        (if ok = 1 then
          (if h : e < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, h⟩).toNat) d.L else [])
         else List.replicate d.L 0)) *
    Assn.gc

private theorem circ_optimal_congr {A B : Circulation} (hAB : A = B) (hm : A.m = B.m)
    {f : Fin A.m → ℝ} (h : A.Optimal f) :
    B.Optimal (fun a => f (a.cast hm.symm)) := by
  subst hAB; simpa using h

private theorem circ_objective_congr {A B : Circulation} (hAB : A = B) (hm : A.m = B.m)
    (f : Fin A.m → ℝ) :
    B.objective (fun a => f (a.cast hm.symm)) = A.objective f := by
  subst hAB; rfl

theorem stage0FeasPost_meets {w : ℕ} {p : Program} {f satCheck scatter : ℕ}
    {Tsat : ℕ → ℕ → ℕ} {Tsc : ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0FeasPost satCheck scatter))
    (hsat : Meets w p satCheck ((stage0FeasSatCheckSpec w).withCost fun x _ =>
      Tsat x.K1 (x.m1 - x.m1Orig)))
    (hsc : Meets w p scatter ((stage0FeasScatterSpec w).withCost fun x _ =>
      Tsc x.K1 x.L (feasOrigPos x.I x.hv x.I.m).length)) :
    Meets w p f ((stage0FeasPostSpec w).withCost fun d _ =>
      let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
      let orig := feasOrigPos d.I d.hv d.I.m
      let K1 := bitScalingPhases P' / narrowLimbWidth d.I + 2
      Tsat K1 (P'.m - orig.length) + Tsc K1 d.L orig.length + 70) := by
  sep_enter d with hL1 hcaps hcapDig hcanCap hopt hfl hdigLe
    hpCP hpCL hpOI hpOut hmK hpFF hmL h3m hKW hLW
  set P := FlowReduction.buildFeasibilityInstance d.I d.hv
  set P' := P.withoutZeroEdges
  set orig := feasOrigPos d.I d.hv d.I.m
  set k := narrowLimbWidth d.I
  set K1 := bitScalingPhases P' / k + 2
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have hm_eq : P'.m = orig.length + (feasArtPos d.I d.I.n).length + (feasArtNeg d.I d.I.n).length :=
    feas_m_eq d.I d.hv
  have hm_le : P'.m ≤ 3 * d.I.m := feas_m_le_three_m d.I d.hv d.hiso
  have hPeq : P = FlowReduction.feasibilityInstance d.I d.hv :=
    FlowReduction.buildFeasibilityInstance_eq d.I d.hv
  have hopt_P : (FlowReduction.feasibilityInstance d.I d.hv).Optimal
      (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) := by
    have h1 := P.scatterPositive_optimal (fun j => (d.f' j : ℝ)) hopt
    rw [← P.scatterPositive_cast d.f'] at h1
    exact circ_optimal_congr hPeq rfl h1
  have hsat_iff : (∀ j : Fin P'.m, orig.length ≤ j.val →
        Nat.ofDigits (2 ^ k) (d.flowLimbs j) =
          Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j.val [])) ↔
      P.integerObjective (P.scatterPositive d.f') =
        -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℤ) := by
    have hobj := feasibility_objective_eq_iff_art_sat d.I d.hv d.f' hopt.1
    dsimp only at hobj
    rw [hobj]
    constructor
    · intro h j hj
      have hj' : orig.length ≤ j.val := (feas_positiveIndex_ge_m_iff d.I d.hv j).mp hj
      have h1 := h j hj'
      have h2 : Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j.val []) = P'.capacity j := by
        simpa only [Fin.eta] using (hcanCap j.val j.isLt).2
      have h3 := (hfl j).2.2.2
      rw [h1, h2] at h3
      exact h3.symm
    · intro h j hj
      have hj' : d.I.m ≤ (P.positiveIndex j).val := (feas_positiveIndex_ge_m_iff d.I d.hv j).mpr hj
      have h1 := h j hj'
      have h2 : Nat.ofDigits (2 ^ k) ((feasCapLimbs d.I d.hv).getD j.val []) = P'.capacity j := by
        simpa only [Fin.eta] using (hcanCap j.val j.isLt).2
      have h3 := (hfl j).2.2.2
      have h4 : ((Nat.ofDigits (2 ^ k) (d.flowLimbs j) : ℕ) : ℤ) = (P'.capacity j : ℤ) := h3.trans h1
      rw [h2]
      exact_mod_cast h4
  sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpFlow1_1 hK1_1
  subst pFlow1_1 K1_1
  have hsd_cp : (feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L).length =
      (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length := by
    simp [feasCapPtrs]
  have hsd_cl : (feasCapLimbs d.I d.hv).length =
      (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length := by
    simp [feasCapLimbs]
  have hcan_sd : ∀ j (hj : j < (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length),
      CanonicalLimbs k ((feasCapLimbs d.I d.hv).getD j []) :=
    fun j hj => (hcanCap j hj).1
  have hfl_sd : ∀ j : Fin (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length,
      Limbs k (d.flowLimbs j) ∧ (d.flowLimbs j).length = K1 :=
    fun j => ⟨(hfl j).2.1, (hfl j).2.2.1⟩
  have horig_le_P' : orig.length ≤ (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length := by
    change orig.length ≤ P'.m; omega
  sep_step from (⟨k, orig.length, (FlowReduction.buildFeasibilityInstance d.I d.hv).positiveEdges.length, K1,
      feasCapPtrs d.I d.hv d.pShCapBuf d.pShDemBuf d.L,
      feasCapLimbs d.I d.hv, d.flowLimbs⟩ : FeasSatCheckData) with hok_le hok_iff
  sep_step
  · -- ok == 1 branch
    sep_step from (⟨d.I, d.hv, d.L, K1, d.f', d.flowLimbs⟩ : FeasScatterData)
    have hobj_eq : P.integerObjective (P.scatterPositive d.f') =
        -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℤ) :=
      hsat_iff.mp (hok_iff.mp hcond)
    have hobj_tr : (FlowReduction.feasibilityInstance d.I d.hv).objective
        (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) =
        P.objective (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) := by
      simpa using circ_objective_congr hPeq rfl (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ))
    have hobjR : (FlowReduction.feasibilityInstance d.I d.hv).objective
        (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) =
        -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℝ) := by
      rw [hobj_tr, ← Circulation.integerObjective_cast]
      exact_mod_cast hobj_eq
    have hfeas_phase := FlowReduction.phaseFlow_feasible d.I d.hv hcaps (P.scatterPositive d.f')
      hopt_P.1 hobjR
    have hrestore_eq : FlowReduction.restore d.I
        (fun e => ((P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e) : ℤ) : ℝ)) =
        (fun e => ((FlowReduction.phaseFlow d.I (P.scatterPositive d.f') e : ℤ) : ℝ)) := by
      funext e
      simp only [FlowReduction.restore, FlowReduction.phaseFlow, Int.cast_add]
    have hbounds : ∀ e : Fin d.I.m,
        0 ≤ P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e) ∧
        P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e) ≤
          ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ) := by
      intro e
      have hfe := hopt_P.1.2 (Fin.castAdd (d.I.n + d.I.n) e)
      have hcap_eq : (FlowReduction.feasibilityInstance d.I d.hv).capacity (Fin.castAdd (d.I.n + d.I.n) e) =
          (FlowReduction.shiftedGraph d.I d.hv).capacity e := by
        simp [Fin.addCases_left]
      rw [hcap_eq] at hfe
      have h1 : (0 : ℝ) ≤ ((P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e) : ℤ) : ℝ) := hfe.1
      have h2 : ((P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) e) : ℤ) : ℝ) ≤
          (((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℕ) : ℝ) := hfe.2
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    have hff1 : (∏ e ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + e * d.L)
          (if h : e < d.I.m then
            padLimbs (Nat.digits (2 ^ k) (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
          else [])) =
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if ok = 1 then
              (if h : e < d.I.m then
                padLimbs (Nat.digits (2 ^ k) (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
              else [])
            else List.replicate d.L 0)) := by
      refine Finset.prod_congr rfl fun e _ => by rw [ite_eq_left hcond]
    sep_apply hff1
    sep_apply (Assn.noDebt_prod (Finset.range P'.m) fun j _ =>
      Assn.noDebt_list (pFlow1 + j * K1) (if h : j < P'.m then d.flowLimbs ⟨j, h⟩ else [])).le_gc
    sep_step
    · dsimp only [orig]; omega
    · intro _; exact ⟨hbounds, hrestore_eq.symm ▸ hfeas_phase⟩
  · -- ok == 0 branch
    have hok0 : ok = 0 := by omega
    have hobj_ne : P.integerObjective (P.scatterPositive d.f') ≠
        -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℤ) := by
      intro heq
      have := hok_iff.mpr (hsat_iff.mpr heq)
      omega
    have hobj_tr : (FlowReduction.feasibilityInstance d.I d.hv).objective
        (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) =
        P.objective (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) := by
      simpa using circ_objective_congr hPeq rfl (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ))
    have hobjR_ne : (FlowReduction.feasibilityInstance d.I d.hv).objective
        (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) ≠
        -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℝ) := by
      intro heq
      apply hobj_ne
      have h1 : P.objective (fun a => ((P.scatterPositive d.f' a : ℤ) : ℝ)) =
          -((FlowReduction.shiftedGraph d.I d.hv).demandMass (FlowReduction.shiftedDemand d.I) : ℝ) := by
        rwa [hobj_tr] at heq
      rw [← Circulation.integerObjective_cast] at h1
      exact_mod_cast h1
    have hinfeas : ∀ x, ¬ d.I.IsFeasible x :=
      FlowReduction.infeasible_of_phase_value d.I d.hv hcaps _ hopt_P hobjR_ne
    have hff0 : (∏ e ∈ Finset.range d.I.m, Assn.list (pFeasFlow + e * d.L) (List.replicate d.L 0)) =
        (∏ e ∈ Finset.range d.I.m,
          Assn.list (pFeasFlow + e * d.L)
            (if ok = 1 then
              (if h : e < d.I.m then
                padLimbs (Nat.digits (2 ^ k) (P.scatterPositive d.f' (Fin.castAdd (d.I.n + d.I.n) ⟨e, h⟩)).toNat) d.L
              else [])
            else List.replicate d.L 0)) :=
      Finset.prod_congr rfl fun _ _ => by rw [ite_eq_right hcond]
    sep_apply hff0
    sep_apply (Assn.noDebt_prod (Finset.range P'.m) fun j _ =>
      Assn.noDebt_list (pFlow1 + j * K1) (if h : j < P'.m then d.flowLimbs ⟨j, h⟩ else [])).le_gc
    sep_step; sep_step

end MinCostFlow.NarrowProg
