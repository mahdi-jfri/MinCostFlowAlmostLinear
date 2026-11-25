module

public import MinCostFlow.NarrowProg.Stage0Shift
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.PositiveScatter
public import MinCostFlow.Scaling.IsolatedDemands
public import MinCostFlow.Scaling.ReductionAlgorithm
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 1 bridges, bit-width bounds, and pruning lemmas for Stage 0 items 4 and 5

Provides:
1. Monotonicity and bit-width bounds bridging `NarrowMainFits` and `Stage1.stage1CircSpec`:
   `upperClip_mono`, `narrowMaxCapLimbs_lt_pow_k`, `narrowMaxCostLimbs_lt_pow_k`,
   `limbLen_mul_k_lt_pow_w`, `stage1_Kcap_le_maxCapLimbs`, `scalingCapacityBudget_lt_pow`,
   `stage0Check_L_eq`.
2. Mathematical pruning lemmas for both Stage 0 circulation calls:
   - `feasibility_objective_eq_iff_art_sat` (objective saturation ↔ all pruned artificial arcs
     saturated);
   - capacity and cost bounds on the pruned feasibility and residual circulations.
3. `copyFlowLimbs` (`canonLen` + `padCopy`), which copies a `K_cap`-limb Stage 1 output flow entry
   representing a value `< (2 ^ k) ^ L` into an `L`-limb `padLimbs` buffer in `O(K_cap + L + 1)`
   steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow
open MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowProg

/-! ### Clipping and bit-width bounds -/

theorem upperClip_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : upperClip m₁ ≤ upperClip m₂ := by
  unfold upperClip costPrecisionExp costClipExp
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.add_le_add
  · exact Nat.clog_mono_right 2 (Nat.pow_le_pow_left (by omega) 8)
  · exact Nat.clog_mono_right 2 (by omega)

theorem nat_size_le_clog_succ (x : ℕ) : Nat.size x ≤ Nat.clog 2 (x + 1) := by
  by_cases hx : x = 0
  · subst hx; simp
  · rw [Nat.size_le]
    have hc := Nat.le_pow_clog (by decide : 1 < 2) (x + 1)
    omega

private theorem clog_pow_mul_le (a b : ℕ) :
    Nat.clog 2 (2 ^ a * b) ≤ a + Nat.clog 2 b := by
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2), pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide : 1 < 2) b)

private theorem clog_pow_le_mul (x d : ℕ) :
    Nat.clog 2 (x ^ d) ≤ d * Nat.clog 2 x := by
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2), mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) x) d

theorem narrowCostRounds_compress_le (I : Instance) (K : Circulation)
    (hm : K.m ≤ 3 * I.m) (hC : circMaxCost K ≤ max I.maxCost 1) :
    narrowCostRounds K.compress ≤
      28 * (Nat.clog 2 (I.maxCost + 2) + Nat.clog 2 (I.m + 1) + 1) := by
  set C := K.compress
  have hCn : C.n ≤ 6 * I.m := by
    have h1 : C.n ≤ 2 * K.m := Circulation.endpointLabels_count_le K
    omega
  have hCm : C.m = K.m := rfl
  have hCostEq : circMaxCost C = circMaxCost K := rfl
  have hL : costScaleBits C ≤ Nat.clog 2 (I.maxCost + 2) := by
    unfold costScaleBits
    rw [hCostEq]
    exact le_trans (Nat.size_le_size hC)
      (le_trans (nat_size_le_clog_succ _) (Nat.clog_mono_right 2 (by omega)))
  have hp : costPrecisionExp C.m ≤ 24 + 8 * Nat.clog 2 (I.m + 1) := by
    unfold costPrecisionExp
    have h1 : (2 * C.m) ^ 8 ≤ 2 ^ 24 * (I.m + 1) ^ 8 := by
      calc (2 * C.m) ^ 8 ≤ (8 * (I.m + 1)) ^ 8 := Nat.pow_le_pow_left (by omega) 8
        _ = 8 ^ 8 * (I.m + 1) ^ 8 := Nat.mul_pow _ _ _
        _ = 2 ^ 24 * (I.m + 1) ^ 8 := by norm_num
    have h2 := le_trans (Nat.clog_mono_right 2 h1) (clog_pow_mul_le 24 ((I.m + 1) ^ 8))
    have h3 := clog_pow_le_mul (I.m + 1) 8
    omega
  have hsn : Nat.size (C.n + 1) ≤ 3 + Nat.clog 2 (I.m + 1) := by
    have h1 : C.n + 2 ≤ 2 ^ 3 * (I.m + 1) := by omega
    have h2 := le_trans (nat_size_le_clog_succ (C.n + 1))
      (le_trans (Nat.clog_mono_right 2 h1) (clog_pow_mul_le 3 (I.m + 1)))
    exact h2
  unfold narrowCostRounds
  omega

/-- When `stage0Check` succeeds (`isolatedCheck = true`), the computed limb width `L_dem` equals
`narrowMaxCapLimbs I + 1`. -/
theorem stage0Check_L_eq (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) {act : List ℕ} {L : ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    (hL1 : 1 ≤ L) (hLle : L ≤ narrowMaxCapLimbs I + 1)
    (hedge : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length < L)
    (hdem : ∀ (c : ℕ) (hc : c < act.length),
      (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'hc)).natAbs).length < L) :
    L = narrowMaxCapLimbs I + 1 := by
  have hmem : I.maxCapacity = 0 ∨
      (∃ e : Fin I.m, I.maxCapacity = (I.edge e).lower.natAbs ∨ I.maxCapacity = (I.edge e).upper.natAbs) ∨
      (∃ v : Fin I.n, I.maxCapacity = (I.d v).natAbs) := by
    have hfold : ∀ (l : List ℕ), l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
      intro l; induction l with
      | nil => left; rfl
      | cons a l ih =>
        simp only [List.foldr_cons]
        rcases le_total a (l.foldr max 0) with h | h
        · rw [max_eq_right h]
          rcases ih with h0 | hm
          · left; exact h0
          · right; exact List.mem_cons_of_mem a hm
        · rw [max_eq_left h]; right; exact List.mem_cons_self
    unfold Instance.maxCapacity
    rcases hfold _ with h0 | hm
    · left; exact h0
    · rcases List.mem_append.mp hm with hm1 | hm2
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm1
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
        right; left; refine ⟨⟨i, hi⟩, ?_⟩
        rcases le_total (I.edges[i]'hi).lower.natAbs (I.edges[i]'hi).upper.natAbs with h | h
        · right; rw [← heq, max_eq_right h]; rfl
        · left; rw [← heq, max_eq_left h]; rfl
      · obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm2
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hin : i < I.n := by rw [← hv.2]; exact hi
        right; right; refine ⟨⟨i, hin⟩, ?_⟩
        rw [← heq]; unfold Instance.d; rw [List.getD_eq_getElem _ _ hi]
  unfold narrowMaxCapLimbs at hLle ⊢
  rcases hmem with h0 | ⟨e, hlo | hhi⟩ | ⟨v, hdv⟩
  · rw [h0] at hLle ⊢; simp at hLle ⊢; omega
  · rw [hlo] at hLle ⊢; have := (hedge e).1; omega
  · rw [hhi] at hLle ⊢; have := (hedge e).2; omega
  · set el := (FlowReduction.shiftedGraph I hv).endpointLabels
    by_cases hlab : el.table v = 0
    · have hdv0 : I.d v = 0 :=
        ((FlowReduction.isolatedCheck_iff I hv).mp hiso v).resolve_left (by change ¬ 0 < el.table v; omega)
      rw [hdv, hdv0] at hLle ⊢; simp at hLle ⊢; omega
    · have hval := Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)
      have hle : el.table v ≤ el.count := hval.1 v
      have hc_lt : el.table v - 1 < el.count := by omega
      have hc_act : el.table v - 1 < act.length := by rw [hact.1]; exact hc_lt
      have htab : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ = el.table v := by
        have := (hact.2 (el.table v - 1) hc_act).2; omega
      have hne : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ ≠ 0 := by omega
      have hv_eq : (⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ : Fin I.n) = v :=
        hval.2 _ _ hne htab
      have hact_eq : act[el.table v - 1]'hc_act = v.val := congrArg Fin.val hv_eq
      have hd := hdem (el.table v - 1) hc_act
      rw [hact_eq] at hd
      rw [hdv] at hLle ⊢
      omega

theorem narrowBitLength_ge_log_maxCapacity (I : Instance) (hv : I.IsValid) :
    Nat.log 2 I.maxCapacity + 2 ≤ narrowBitLength I := by
  have hmem : I.maxCapacity = 0 ∨
      (∃ e : Fin I.m, I.maxCapacity = (I.edge e).lower.natAbs ∨ I.maxCapacity = (I.edge e).upper.natAbs) ∨
      (∃ v : Fin I.n, I.maxCapacity = (I.d v).natAbs) := by
    have hfold : ∀ (l : List ℕ), l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
      intro l; induction l with
      | nil => left; rfl
      | cons a l ih =>
        simp only [List.foldr_cons]
        rcases le_total a (l.foldr max 0) with h | h
        · rw [max_eq_right h]
          rcases ih with h0 | hm
          · left; exact h0
          · right; exact List.mem_cons_of_mem a hm
        · rw [max_eq_left h]; right; exact List.mem_cons_self
    unfold Instance.maxCapacity
    rcases hfold _ with h0 | hm
    · left; exact h0
    · rcases List.mem_append.mp hm with hm1 | hm2
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm1
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
        right; left; refine ⟨⟨i, hi⟩, ?_⟩
        rcases le_total (I.edges[i]'hi).lower.natAbs (I.edges[i]'hi).upper.natAbs with h | h
        · right; rw [← heq, max_eq_right h]; rfl
        · left; rw [← heq, max_eq_left h]; rfl
      · obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm2
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hin : i < I.n := by rw [← hv.2]; exact hi
        right; right; refine ⟨⟨i, hin⟩, ?_⟩
        rw [← heq]; unfold Instance.d; rw [List.getD_eq_getElem _ _ hi]
  rcases hmem with h0 | ⟨e, hlo | hhi⟩ | ⟨v, hdv⟩
  · rw [h0]; have := four_le_narrowBitLength I; simp; omega
  · have hle : narrowEdgeBits (I.edge e) ≤ (I.edges.map narrowEdgeBits).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
    unfold narrowBitLength narrowEdgeBits narrowIntBits at hle ⊢
    rw [hlo]; omega
  · have hle : narrowEdgeBits (I.edge e) ≤ (I.edges.map narrowEdgeBits).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
    unfold narrowBitLength narrowEdgeBits narrowIntBits at hle ⊢
    rw [hhi]; omega
  · have hv' : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
    have hdv' : I.d v = I.demand[v.val]'hv' := List.getD_eq_getElem _ _ hv'
    have hle : narrowIntBits (I.d v) ≤ (I.demand.map narrowIntBits).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨I.d v, hdv' ▸ List.getElem_mem hv', rfl⟩)
    unfold narrowBitLength narrowIntBits at hle ⊢
    rw [hdv]; omega

theorem narrowBitLength_ge_log_maxCost (I : Instance) :
    Nat.log 2 I.maxCost + 2 ≤ narrowBitLength I := by
  have hfold : ∀ (l : List ℕ), l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
    intro l; induction l with
    | nil => left; rfl
    | cons a l ih =>
      simp only [List.foldr_cons]
      rcases le_total a (l.foldr max 0) with h | h
      · rw [max_eq_right h]
        rcases ih with h0 | hm
        · left; exact h0
        · right; exact List.mem_cons_of_mem a hm
      · rw [max_eq_left h]; right; exact List.mem_cons_self
  unfold Instance.maxCost
  rcases hfold (I.edges.map fun e => e.cost.natAbs) with h0 | hm
  · rw [h0]; have := four_le_narrowBitLength I; simp; omega
  · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    have hle : narrowEdgeBits e ≤ (I.edges.map narrowEdgeBits).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
    unfold narrowBitLength narrowEdgeBits narrowIntBits at hle ⊢
    rw [← heq]; omega

theorem narrowMaxCapLimbs_lt_pow_k (I : Instance) (hv : I.IsValid) :
    narrowMaxCapLimbs I + 1 < 2 ^ narrowLimbWidth I := by
  have hk1 := one_le_narrowLimbWidth I
  have hlog := narrowBitLength_ge_log_maxCapacity I hv
  have hlt := narrowBitLength_lt_pow_limbWidth I
  have hdig : narrowMaxCapLimbs I ≤ Nat.log 2 I.maxCapacity + 1 := by
    unfold narrowMaxCapLimbs
    by_cases h0 : I.maxCapacity = 0
    · rw [h0]; simp
    · have hb : 1 < 2 ^ narrowLimbWidth I := by have := two_le_pow hk1; omega
      rw [Nat.length_digits _ _ hb h0]
      have h1 : (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤ I.maxCapacity :=
        Nat.pow_log_le_self _ h0
      have h2 : 2 ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤
          (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity :=
        Nat.pow_le_pow_left (two_le_pow hk1) _
      have h3 : Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤ Nat.log 2 I.maxCapacity :=
        (Nat.le_log_iff_pow_le (by decide) h0).mpr (le_trans h2 h1)
      omega
  omega

theorem narrowMaxCostLimbs_lt_pow_k (I : Instance) :
    narrowMaxCostLimbs I + 1 < 2 ^ narrowLimbWidth I := by
  have hk1 := one_le_narrowLimbWidth I
  have hlog := narrowBitLength_ge_log_maxCost I
  have hlt := narrowBitLength_lt_pow_limbWidth I
  have hdig : narrowMaxCostLimbs I ≤ Nat.log 2 I.maxCost + 1 := by
    unfold narrowMaxCostLimbs
    by_cases h0 : I.maxCost = 0
    · rw [h0]; simp
    · have hb : 1 < 2 ^ narrowLimbWidth I := by have := two_le_pow hk1; omega
      rw [Nat.length_digits _ _ hb h0]
      have h1 : (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCost ≤ I.maxCost :=
        Nat.pow_log_le_self _ h0
      have h2 : 2 ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCost ≤
          (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCost :=
        Nat.pow_le_pow_left (two_le_pow hk1) _
      have h3 : Nat.log (2 ^ narrowLimbWidth I) I.maxCost ≤ Nat.log 2 I.maxCost :=
        (Nat.le_log_iff_pow_le (by decide) h0).mpr (le_trans h2 h1)
      omega
  omega

theorem limbLen_mul_k_lt_pow_w {k w len : ℕ} (hk3 : 3 ≤ k) (h2k1 : 2 * k + 1 ≤ w)
    (hlen : len < 2 ^ k) : len * k < 2 ^ w := by
  have hk_lt : k < 2 ^ k := by have := two_mul_lt_pow_of_three_le hk3; omega
  have h1 : len * k < 2 ^ k * 2 ^ k :=
    Nat.mul_lt_mul_of_lt_of_lt hlen hk_lt
  have h2 : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by rw [← pow_add, two_mul]
  have h3 : 2 ^ (2 * k) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem stage1_Kcap_le_maxCapLimbs (I : Instance) (hv : I.IsValid) (K : Circulation)
    (hcap : circMaxCapacity K ≤ FlowReduction.scalingCapacityBudget I I.maxCapacity) :
    bitScalingPhases K / narrowLimbWidth I + 2 ≤ narrowMaxCapLimbs I + 3 := by
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have h6m : 6 * I.m + 1 < 2 ^ k := six_mul_m_add_one_lt_pow_limbWidth I hv
  have h2k8 : 8 ≤ 2 ^ k := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk3
  have hU_lt : I.maxCapacity < (2 ^ k) ^ narrowMaxCapLimbs I := by
    have h1 := ofDigits_lt_pow_length hk1 (digits_limbs hk1 I.maxCapacity)
    rwa [Nat.ofDigits_digits] at h1
  have hbud_lt : FlowReduction.scalingCapacityBudget I I.maxCapacity <
      2 ^ (k * (narrowMaxCapLimbs I + 1)) := by
    rw [pow_mul, pow_succ']
    unfold FlowReduction.scalingCapacityBudget
    by_cases hU0 : I.maxCapacity = 0
    · rw [hU0]; simp only [mul_zero, zero_add]
      have hpow1 : 1 ≤ (2 ^ k) ^ narrowMaxCapLimbs I := Nat.pow_pos (by omega)
      have := Nat.mul_le_mul_left (2 ^ k) hpow1
      omega
    · have h2m3 : 2 * (I.m + 1) + 1 ≤ 2 ^ k := by omega
      have h1 : 2 * (I.m + 1) * I.maxCapacity + 1 ≤ (2 * (I.m + 1) + 1) * I.maxCapacity := by
        have : (2 * (I.m + 1) + 1) * I.maxCapacity = 2 * (I.m + 1) * I.maxCapacity + I.maxCapacity := by ring
        omega
      have h2 : (2 * (I.m + 1) + 1) * I.maxCapacity < 2 ^ k * (2 ^ k) ^ narrowMaxCapLimbs I :=
        Nat.mul_lt_mul_of_le_of_lt h2m3 hU_lt (by omega)
      omega
  have hsize : bitScalingPhases K ≤ k * (narrowMaxCapLimbs I + 1) := by
    unfold bitScalingPhases
    rw [Nat.size_le]
    exact lt_of_le_of_lt hcap hbud_lt
  have hdiv : bitScalingPhases K / k ≤ narrowMaxCapLimbs I + 1 := by
    calc bitScalingPhases K / k ≤ (k * (narrowMaxCapLimbs I + 1)) / k := Nat.div_le_div_right hsize
      _ = narrowMaxCapLimbs I + 1 := Nat.mul_div_cancel_left _ (by omega)
  omega

/-! ### Mathematical pruning lemmas for Item 4 (feasibility) and Item 5 (residual) -/

/-- For the pruned feasibility circulation `P' = P.withoutZeroEdges`, a feasible integral flow `g'`
achieves the saturation objective `-demandMass` in `P` iff every pruned artificial arc
(`I.m ≤ (P.positiveIndex j).val`) is saturated (`g' j = P'.capacity j`). -/
theorem feasibility_objective_eq_iff_art_sat (I : Instance) (hv : I.IsValid)
    (g' : Fin (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m → ℤ)
    (hg' : (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.Feasible
      (fun j => (g' j : ℝ))) :
    let P := FlowReduction.buildFeasibilityInstance I hv
    let g := P.scatterPositive g'
    P.integerObjective g =
      -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℤ) ↔
    ∀ j : Fin P.withoutZeroEdges.m, I.m ≤ (P.positiveIndex j).val →
      g' j = (P.withoutZeroEdges.capacity j : ℤ) := by
  intro P g
  have hPeq : P = (FlowReduction.shiftedGraph I hv).demandInstance (FlowReduction.shiftedDemand I) :=
    FlowReduction.buildFeasibilityInstance_eq I hv
  have hg_feas : P.Feasible (fun a => (g a : ℝ)) := by
    have h := P.scatterPositive_feasible (fun j => (g' j : ℝ)) hg'
    rwa [← P.scatterPositive_cast g'] at h
  have hg_ext : ∀ a : Fin P.m, (g a : ℝ) = P.extendPositive (fun j => (g' j : ℝ)) a := by
    intro a
    have h1 := congrFun (P.scatterPositive_cast g') a
    have h2 := congrFun (P.scatterPositive_eq_extendPositive (fun j => (g' j : ℝ))) a
    exact h1.trans h2
  have hg_le : ∀ a : Fin P.m, g a ≤ (P.capacity a : ℤ) := by
    intro a
    have h := (hg_feas.2 a).2
    exact (Int.cast_le (R := ℝ)).mp (by simpa only [Int.cast_natCast] using h)
  have hobj_eq : (P.integerObjective g : ℝ) =
      -(∑ a : Fin (I.n + I.n), (g (Fin.natAdd I.m a) : ℝ)) := by
    rw [Circulation.integerObjective_cast]
    exact (FlowReduction.shiftedGraph I hv).demand_objective (FlowReduction.buildShiftedDemands I hv)
      (fun a => (g a : ℝ))
  have hmass_eq : (((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℕ) : ℝ) =
      ∑ a : Fin (I.n + I.n), (P.capacity (Fin.natAdd I.m a) : ℝ) := by
    rw [Fin.sum_univ_add]
    simp only [P, Fin.addCases_right, Fin.addCases_left, FlowReduction.buildShiftedDemands_eq,
      Circulation.demandMass, Nat.cast_sum, Nat.cast_add, Finset.sum_add_distrib]
  constructor
  · intro heq j hj
    have heqR : (P.integerObjective g : ℝ) =
        -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℝ) := by
      exact_mod_cast heq
    rw [hobj_eq, hmass_eq] at heqR
    have hsum0 : (∑ a : Fin (I.n + I.n),
        ((P.capacity (Fin.natAdd I.m a) : ℝ) - (g (Fin.natAdd I.m a) : ℝ))) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith
    have hnn : ∀ a ∈ (Finset.univ : Finset (Fin (I.n + I.n))),
        0 ≤ (P.capacity (Fin.natAdd I.m a) : ℝ) - (g (Fin.natAdd I.m a) : ℝ) := by
      intro a _
      have := hg_le (Fin.natAdd I.m a)
      have : (g (Fin.natAdd I.m a) : ℝ) ≤ (P.capacity (Fin.natAdd I.m a) : ℝ) := by exact_mod_cast this
      linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
    let a : Fin (I.n + I.n) := ⟨(P.positiveIndex j).val - I.m, by
      have hlt := (P.positiveIndex j).isLt; change (P.positiveIndex j).val < I.m + (I.n + I.n) at hlt; omega⟩
    have ha_eq : Fin.natAdd I.m a = P.positiveIndex j := by
      apply Fin.ext; simp [a, Fin.natAdd]; omega
    have hz := hall a (Finset.mem_univ a)
    rw [ha_eq] at hz
    have hpos : 0 < P.capacity (P.positiveIndex j) :=
      (P.mem_positiveEdges_iff _).mp (List.getElem_mem j.isLt)
    have hgj : (g (P.positiveIndex j) : ℝ) = (g' j : ℝ) := by
      rw [hg_ext, Circulation.extendPositive, dite_eq_left hpos, P.positiveSlot_positiveIndex j hpos]
    rw [hgj] at hz
    have hR : (g' j : ℝ) = (P.capacity (P.positiveIndex j) : ℝ) := by linarith
    exact_mod_cast hR
  · intro hsat
    have hall : ∀ a : Fin (I.n + I.n), (g (Fin.natAdd I.m a) : ℝ) = (P.capacity (Fin.natAdd I.m a) : ℝ) := by
      intro a
      by_cases hpos : 0 < P.capacity (Fin.natAdd I.m a)
      · let j := P.positiveSlot (Fin.natAdd I.m a) hpos
        have hj_idx : P.positiveIndex j = Fin.natAdd I.m a := P.positiveIndex_positiveSlot _ hpos
        have hj_ge : I.m ≤ (P.positiveIndex j).val := by rw [hj_idx]; simp [Fin.natAdd]
        have hs := hsat j hj_ge
        rw [hg_ext, Circulation.extendPositive, dite_eq_left hpos]
        change (g' j : ℝ) = _
        rw [hs]
        change (((P.capacity (P.positiveIndex j) : ℕ) : ℤ) : ℝ) = _
        rw [hj_idx]; norm_cast
      · have hz : P.capacity (Fin.natAdd I.m a) = 0 := by omega
        rw [hg_ext, Circulation.extendPositive, dite_eq_right hpos, hz]; simp
    have hR : (P.integerObjective g : ℝ) =
        -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℝ) := by
      rw [hobj_eq, hmass_eq]
      congr 1
      exact Finset.sum_congr rfl fun a _ => hall a
    exact_mod_cast hR

/-- Capacity bound on the residual graph of a feasible shifted flow: `circMaxCapacity R' ≤ 2 * U`. -/
theorem residual_withoutZeroEdges_maxCapacity_le (I : Instance) (hv : I.IsValid)
    (f : Fin I.m → ℤ) (hf : ∀ e, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)) :
    circMaxCapacity ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges ≤
      2 * I.maxCapacity := by
  unfold circMaxCapacity
  apply Finset.sup_le
  intro j _
  have hle : ((FlowReduction.shiftedGraph I hv).residual f).capacity
      (((FlowReduction.shiftedGraph I hv).residual f).positiveIndex j) ≤ 2 * I.maxCapacity := by
    refine Fin.addCases (fun e => ?_) (fun e => ?_)
      (((FlowReduction.shiftedGraph I hv).residual f).positiveIndex j)
    · simp only [Fin.addCases_left]
      have hcap : ((I.edge e).upper - (I.edge e).lower).toNat ≤ 2 * I.maxCapacity :=
        FlowReduction.shiftedGraph_capacity_le I hv I.maxCapacity
          (lower_natAbs_le_maxCapacity' I) (upper_natAbs_le_maxCapacity' I) e
      have hfe := hf e; omega
    · simp only [Fin.addCases_right]
      have hcap := FlowReduction.shiftedGraph_capacity_le I hv I.maxCapacity
        (lower_natAbs_le_maxCapacity' I) (upper_natAbs_le_maxCapacity' I) e
      have hfe := hf e; omega
  exact hle

/-- Cost bound on the residual graph: `circMaxCost R' ≤ I.maxCost`. -/
theorem residual_withoutZeroEdges_maxCost_le (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    circMaxCost ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges ≤ I.maxCost := by
  unfold circMaxCost
  apply Finset.sup_le
  intro j _
  change (((FlowReduction.shiftedGraph I hv).residual f).cost
    (((FlowReduction.shiftedGraph I hv).residual f).positiveIndex j)).natAbs ≤ I.maxCost
  generalize (((FlowReduction.shiftedGraph I hv).residual f).positiveIndex j) = a
  refine Fin.addCases (fun e => ?_) (fun e => ?_) a
  · simp only [Fin.addCases_left]
    exact cost_natAbs_le_maxCost' I e
  · simp only [Fin.addCases_right, Int.natAbs_neg]
    exact cost_natAbs_le_maxCost' I e

/-- Capacity bound on the pruned feasibility graph: `≤ scalingCapacityBudget I I.maxCapacity`. -/
theorem feasibility_withoutZeroEdges_maxCapacity_le (I : Instance) (hv : I.IsValid) :
    circMaxCapacity (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges ≤
      FlowReduction.scalingCapacityBudget I I.maxCapacity := by
  unfold circMaxCapacity
  apply Finset.sup_le
  intro j _
  exact FlowReduction.buildFeasibilityInstance_capacity_le I hv I.maxCapacity
    (demand_natAbs_le_maxCapacity' I hv) (lower_natAbs_le_maxCapacity' I)
    (upper_natAbs_le_maxCapacity' I) _

/-- Cost bound on the pruned feasibility graph: `≤ 1`. -/
theorem feasibility_withoutZeroEdges_maxCost_le (I : Instance) (hv : I.IsValid) :
    circMaxCost (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges ≤ 1 := by
  unfold circMaxCost
  apply Finset.sup_le
  intro j _
  set e := (FlowReduction.buildFeasibilityInstance I hv).positiveEdges[j.val]
  change ((Fin.addCases (fun _ : Fin I.m => (0 : ℤ))
    (fun _ : Fin (I.n + I.n) => -1) : Fin (I.m + (I.n + I.n)) → ℤ) e).natAbs ≤ 1
  induction e using Fin.addCases with
  | left _ => simp only [Fin.addCases_left, Int.natAbs_zero]; omega
  | right _ => simp only [Fin.addCases_right]; decide

/-! ### `copyFlowLimbs`: trim a `K_cap`-limb flow entry and pad-copy into an `L`-limb buffer -/

wram_def copyFlowLimbs (cLen pCopy : ℕ) (pSrc, srcLen, pDst, dstLen) {
  tLen := cLen(pSrc, srcLen)
  d := pCopy(pSrc, tLen, pDst, dstLen)
  return 0
}

structure CopyFlowLimbsData where
  k : ℕ
  src : List ℕ
  dst0 : List ℕ

def copyFlowLimbsSpec : Spec CopyFlowLimbsData where
  pre := fun d args => ⨆ (pSrc : ℕ) (pDst : ℕ),
    ⌜args = [pSrc, d.src.length, pDst, d.dst0.length] ∧
      1 ≤ d.k ∧ Limbs d.k d.src ∧
      (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src)).length ≤ d.dst0.length⌝ *
    Assn.list pSrc d.src * Assn.list pDst d.dst0
  post := fun d args v => ⨆ (pSrc : ℕ) (pDst : ℕ),
    ⌜args = [pSrc, d.src.length, pDst, d.dst0.length] ∧ v = 0⌝ *
    Assn.list pSrc d.src *
    Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src)) d.dst0.length)

theorem copyFlowLimbs_meets {w : ℕ} {p : Program} {f cLen pCopy : ℕ} {Tcan Tpad : ℕ → ℕ}
    (hp : p.procs[f]? = some (copyFlowLimbs cLen pCopy))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length))
    (hpad : Meets w p pCopy (padCopySpec.withCost fun x _ => Tpad x.2.length)) :
    Meets w p f (copyFlowLimbsSpec.withCost fun d _ => Tcan d.src.length + Tpad d.dst0.length + 30) := by
  sep_enter d with hk1 hL hdigLe
  sep_step from (d.k, d.src) with hpad_eq
  have hsplit : Assn.list pSrc d.src =
      Assn.list pSrc (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src)) *
      Assn.list (pSrc + (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src)).length)
        (List.replicate (d.src.length - (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src)).length) 0) := by
    conv_lhs => rw [hpad_eq]
    rw [padLimbs, Assn.list_append]
  sep_apply hsplit
  sep_step from (Nat.digits (2 ^ d.k) (Nat.ofDigits (2 ^ d.k) d.src), d.dst0)
  sep_apply hsplit.symm
  sep_step

/-! ### Reusable capacity-budget, digit-length, and pair-list helpers -/

theorem scalingCapacityBudget_lt_pow (I : Instance) (hv : I.IsValid) :
    FlowReduction.scalingCapacityBudget I I.maxCapacity <
      (2 ^ narrowLimbWidth I) ^ (narrowMaxCapLimbs I + 1) := by
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have h6m : 6 * I.m + 1 < 2 ^ k := six_mul_m_add_one_lt_pow_limbWidth I hv
  have hU_lt : I.maxCapacity < (2 ^ k) ^ narrowMaxCapLimbs I := by
    have h1 := ofDigits_lt_pow_length hk1 (digits_limbs hk1 I.maxCapacity)
    rwa [Nat.ofDigits_digits] at h1
  have h2k8 : 8 ≤ 2 ^ k := calc 8 = 2 ^ 3 := by decide
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk3
  rw [pow_succ']
  unfold FlowReduction.scalingCapacityBudget
  by_cases hU0 : I.maxCapacity = 0
  · rw [hU0]; simp only [mul_zero, zero_add]
    have hpow1 : 1 ≤ (2 ^ k) ^ narrowMaxCapLimbs I := Nat.pow_pos (by omega)
    have := Nat.mul_le_mul_left (2 ^ k) hpow1
    omega
  · have h2m3 : 2 * (I.m + 1) + 1 ≤ 2 ^ k := by omega
    have h1 : 2 * (I.m + 1) * I.maxCapacity + 1 ≤ (2 * (I.m + 1) + 1) * I.maxCapacity := by
      have : (2 * (I.m + 1) + 1) * I.maxCapacity = 2 * (I.m + 1) * I.maxCapacity + I.maxCapacity := by ring
      omega
    have h2 : (2 * (I.m + 1) + 1) * I.maxCapacity < 2 ^ k * (2 ^ k) ^ narrowMaxCapLimbs I :=
      Nat.mul_lt_mul_of_le_of_lt h2m3 hU_lt (by omega)
    omega

theorem digits_len_le_of_lt_pow {b x L : ℕ} (hb : 1 < b) (hx : x < b ^ L) :
    (Nat.digits b x).length ≤ L := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  · rw [Nat.length_digits _ _ hb hx0]
    have hlt : Nat.log b x < L := (Nat.log_lt_iff_lt_pow hb hx0).mpr hx
    omega

theorem stage1_k_log_bound {k w : ℕ} (hk3 : 3 ≤ k) (h2k1 : 2 * k + 1 ≤ w) :
    k + Nat.log 2 (2 * k) + 2 ≤ w := by
  have h2k_lt : 2 * k < 2 ^ k := two_mul_lt_pow_of_three_le hk3
  have hlog : Nat.log 2 (2 * k) < k :=
    (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr h2k_lt
  omega

theorem upperClip_pos (m : ℕ) : 1 ≤ upperClip m := by
  unfold upperClip
  exact Nat.one_le_pow _ 2 (by decide)

theorem list_split_two {p : ℕ} {xs : List ℕ} (h : xs.length = 2) :
    Assn.list p xs = (p ↦ xs[0]'(by omega)) * (p + 1 ↦ xs[1]'(by omega)) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at h
  simp only [Assn.list_cons, Assn.list_nil, mul_one, List.getElem_cons_zero, List.getElem_cons_succ]

theorem list_join_two (p a b : ℕ) :
    (p ↦ a) * (p + 1 ↦ b) = Assn.list p [a, b] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one]

end MinCostFlow.NarrowProg
