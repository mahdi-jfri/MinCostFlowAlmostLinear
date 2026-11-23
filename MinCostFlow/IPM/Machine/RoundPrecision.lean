module

public import MinCostFlow.IPM.Machine.RoundAvailability
public import MinCostFlow.IPM.Machine.RoundCyclePath
import MinCostFlow.IPM.Machine.PrecisionProducts
import Mathlib.Tactic

/-!
# Working bounds for exact rounding arithmetic

The rounder keeps every forest coordinate within one unit of its
input and every availability in [0,1]. A signed path cost sums at
most one contribution per forest edge.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The allocated block itself witnesses membership in the dyadic grid. -/
theorem RatAt.fixed {mem : ℕ → ℕ} {a h L P : ℕ} {q : ℚ} (hq : RatAt mem a h L P q) :
    IsFixedPoint P q :=
  ⟨Num.intVal mem a h L,hq.2.symm⟩

/-- The common signed range allows one extra unit on a flow. -/
theorem round_capacity_range (m U : ℕ) (hm : 0<m) (hU : 1≤U) :
    (U:ℝ)+1≤(2:ℝ)^(ipmRangeExponent m U) := by
  have h := twice_capacity_le_dyadic m U hm hU
  have hh : (1:ℝ)≤U := by exact_mod_cast hU
  have hexp : slackRangeExponent m U ≤ ipmRangeExponent m U := by unfold ipmRangeExponent; omega
  have ht : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(ipmRangeExponent m U) :=
    pow_le_pow_right₀ (by norm_num) hexp
  linarith only [h,hh,ht]

/-- The edge invariants and dyadic payloads entail the hardware fit
for the forest and any intermediate state after PathAdd. -/
theorem roundForest_fits {D : DynForest} {I : Instance} {s : D.State} {f : Fin I.m → ℚ}
    (U : ℕ) (hm : 0<I.m) (hU : 1≤U) (hn : NumbersBounded I (U:ℝ))
    (hf : ∀ j,|(f j:ℝ)|≤U)
    (hEdges : ∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e ∧
      IsFixedPoint (ipmPrecision I.m U) e.flow ∧ IsFixedPoint (ipmPrecision I.m U) e.availFwd ∧
      IsFixedPoint (ipmPrecision I.m U) e.availBwd) :
    ForestFits D 4 (ipmLimbs I.m U) (ipmPrecision I.m U) s := by
  intro e he
  obtain ⟨hWeak,hP,hF,hB⟩ := hEdges e he
  obtain ⟨j',_,hFlow⟩ := hWeak.flow_bounds
  obtain ⟨hf₀,hf₁,hb₀,hb₁,_⟩ := hWeak.avail_bounds
  have hC : |(e.cost:ℝ)|≤U := by
    obtain ⟨j,_,_,_,hc,_⟩ := hWeak
    rw [hc]
    exact (hn.2 j).2.2
  have hFlow' : |(e.flow:ℝ)|≤|(f j':ℝ)|+1 := by exact_mod_cast hFlow
  have hAvailF : |(e.availFwd:ℝ)|≤1 := by exact_mod_cast ((abs_of_nonneg hf₀).symm ▸ hf₁)
  have hAvailB : |(e.availBwd:ℝ)|≤1 := by exact_mod_cast ((abs_of_nonneg hb₀).symm ▸ hb₁)
  have hOne : (1:ℝ)≤(2:ℝ)^(ipmRangeExponent I.m U) := one_le_pow₀ (by norm_num)
  have hRange := round_capacity_range I.m U hm hU
  exact ⟨(fits_integer_at_chosen_precision I.m U e.cost (by linarith only [hC,hRange])).1,
    ratFits_chosen_precision I.m U _ hP (by linarith only [hFlow',hf j',hRange]),
    ratFits_chosen_precision I.m U _ hF (hAvailF.trans hOne),
    ratFits_chosen_precision I.m U _ hB (hAvailB.trans hOne)⟩

private theorem round_maxCost_le (I : Instance) (U : ℕ) (hn : NumbersBounded I (U:ℝ)) :
    I.maxCost≤U := by
  have hb : ∀ x∈I.edges.map (fun e => e.cost.natAbs),x≤U := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp he
    have hc : |(I.edge j).cost|≤(U:ℤ) := by
      exact_mod_cast (hn.2 j).2.2
    have hj' : I.edge j=e := hj
    rw [hj',Int.abs_eq_natAbs] at hc
    exact_mod_cast hc
  unfold Instance.maxCost
  generalize I.edges.map (fun e => e.cost.natAbs)=xs at hb ⊢
  induction xs with
  | nil => simp
  | cons a l ih =>
    exact max_le (hb a List.mem_cons_self) (ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)))

/-- The stored signed path cost fits the same limb width. Counting
distinct path edges yields a bound of mU before conversion. -/
theorem roundPathSum_fits {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {s : D.State} {f : Fin I.m → ℚ} {a b : ℕ}
    (U : ℕ) (hm : 0<I.m) (hU : 1≤U) (hn : NumbersBounded I (U:ℝ))
    (hInv : D.Inv s) (hConn : (D.toForest s).SameComp a b)
    (hWeak : ∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e)
    (hLen : (D.toForest s).edges.length≤I.m) :
    Num.Fits 4 (ipmLimbs I.m U) (D.pathSum s a b) := by
  obtain ⟨steps,hPath,hw,hnd⟩ := MathForest.findSteps_some_of_sameComp (hD.2.1 s hInv) hConn
  have hSub : steps.map PathStep.toRaw ⊆ (D.toForest s).rawEdges := by
    intro r hr
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨t.edge,hw.mem_edges t ht,rfl⟩
  have hLength : steps.length≤(D.toForest s).edges.length := by
    simpa [MathForest.rawEdges] using hnd.length_le_of_subset hSub
  have hc := stepsCost_abs_le (fun t ht => hWeak t.edge (hw.mem_edges t ht))
  have hr : D.pathSum s a b=stepsCost steps := by
    rw [hD.2.2.2.2.2.2.2 s a b hInv hConn]
    simp [MathForest.pathSum,hPath]
  have hs : |(D.pathSum s a b:ℝ)|≤(I.m:ℝ)*U := by
    rw [hr]
    calc
      _ ≤ (steps.length:ℝ)*(I.maxCost:ℝ) := by exact_mod_cast hc
      _ ≤ (I.m:ℝ)*U := mul_le_mul (by exact_mod_cast hLength.trans hLen)
          (by exact_mod_cast round_maxCost_le I U hn) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hrad := twice_search_radius_le_dyadic I.m U hm hU
  have hExp : slackRangeExponent I.m U ≤ ipmRangeExponent I.m U := by unfold ipmRangeExponent; omega
  have hUpper : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmRangeExponent I.m U) :=
    pow_le_pow_right₀ (by norm_num) hExp
  have hu : (1:ℝ)≤U := by exact_mod_cast hU
  have hsq : (U:ℝ)≤(U:ℝ)^2 := by nlinarith only [mul_nonneg (show (0:ℝ)≤U by positivity) (sub_nonneg.mpr hu)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤I.m by positivity)
  have hh : (0:ℝ)≤(I.m:ℝ)*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact (fits_integer_at_chosen_precision I.m U (D.pathSum s a b)
    (by linarith only [hs,hmul,hrad,hUpper,hh])).1

/-- The common signed range allows one extra unit on a flow. -/
theorem round_capacity_range_widened (m U k : ℕ) (hm : 0<m) (hU : 1≤U) :
    (U:ℝ)+1≤(2:ℝ)^(ipmQualityRangeExponent m U k) := by
  have h := twice_capacity_le_dyadic m U hm hU
  have hh : (1:ℝ)≤U := by exact_mod_cast hU
  have hexp : slackRangeExponent m U ≤ ipmQualityRangeExponent m U k := by have hs := slackRangeExponent_le_qualitySlackExponent m U k; unfold ipmQualityRangeExponent; omega
  have ht : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(ipmQualityRangeExponent m U k) :=
    pow_le_pow_right₀ (by norm_num) hexp
  linarith only [h,hh,ht]

/-- The edge invariants and dyadic payloads entail the hardware fit
for the forest and any intermediate state after PathAdd. -/
theorem roundForest_fits_widened {D : DynForest} {I : Instance} {s : D.State} {f : Fin I.m → ℚ}
    (U k : ℕ) (hm : 0<I.m) (hU : 1≤U) (hn : NumbersBounded I (U:ℝ))
    (hf : ∀ j,|(f j:ℝ)|≤U)
    (hEdges : ∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e ∧
      IsFixedPoint (ipmQualityPrecision I.m U k) e.flow ∧ IsFixedPoint (ipmQualityPrecision I.m U k) e.availFwd ∧
      IsFixedPoint (ipmQualityPrecision I.m U k) e.availBwd) :
    ForestFits D 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) s := by
  intro e he
  obtain ⟨hWeak,hP,hF,hB⟩ := hEdges e he
  obtain ⟨j',_,hFlow⟩ := hWeak.flow_bounds
  obtain ⟨hf₀,hf₁,hb₀,hb₁,_⟩ := hWeak.avail_bounds
  have hC : |(e.cost:ℝ)|≤U := by
    obtain ⟨j,_,_,_,hc,_⟩ := hWeak
    rw [hc]
    exact (hn.2 j).2.2
  have hFlow' : |(e.flow:ℝ)|≤|(f j':ℝ)|+1 := by exact_mod_cast hFlow
  have hAvailF : |(e.availFwd:ℝ)|≤1 := by exact_mod_cast ((abs_of_nonneg hf₀).symm ▸ hf₁)
  have hAvailB : |(e.availBwd:ℝ)|≤1 := by exact_mod_cast ((abs_of_nonneg hb₀).symm ▸ hb₁)
  have hOne : (1:ℝ)≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) := one_le_pow₀ (by norm_num)
  have hRange := round_capacity_range_widened I.m U k hm hU
  exact ⟨(fits_integer_at_quality_precision I.m U k e.cost (by linarith only [hC,hRange])).1,
    ratFits_widened_precision I.m U k _ hP (by linarith only [hFlow',hf j',hRange]),
    ratFits_widened_precision I.m U k _ hF (hAvailF.trans hOne),
    ratFits_widened_precision I.m U k _ hB (hAvailB.trans hOne)⟩


/-- The stored signed path cost fits the same limb width. Counting
distinct path edges yields a bound of mU before conversion. -/
theorem roundPathSum_fits_widened {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {s : D.State} {f : Fin I.m → ℚ} {a b : ℕ}
    (U k : ℕ) (hm : 0<I.m) (hU : 1≤U) (hn : NumbersBounded I (U:ℝ))
    (hInv : D.Inv s) (hConn : (D.toForest s).SameComp a b)
    (hWeak : ∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e)
    (hLen : (D.toForest s).edges.length≤I.m) :
    Num.Fits 4 (ipmQualityLimbs I.m U k) (D.pathSum s a b) := by
  obtain ⟨steps,hPath,hw,hnd⟩ := MathForest.findSteps_some_of_sameComp (hD.2.1 s hInv) hConn
  have hSub : steps.map PathStep.toRaw ⊆ (D.toForest s).rawEdges := by
    intro r hr
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨t.edge,hw.mem_edges t ht,rfl⟩
  have hLength : steps.length≤(D.toForest s).edges.length := by
    simpa [MathForest.rawEdges] using hnd.length_le_of_subset hSub
  have hc := stepsCost_abs_le (fun t ht => hWeak t.edge (hw.mem_edges t ht))
  have hr : D.pathSum s a b=stepsCost steps := by
    rw [hD.2.2.2.2.2.2.2 s a b hInv hConn]
    simp [MathForest.pathSum,hPath]
  have hs : |(D.pathSum s a b:ℝ)|≤(I.m:ℝ)*U := by
    rw [hr]
    calc
      _ ≤ (steps.length:ℝ)*(I.maxCost:ℝ) := by exact_mod_cast hc
      _ ≤ (I.m:ℝ)*U := mul_le_mul (by exact_mod_cast hLength.trans hLen)
          (by exact_mod_cast round_maxCost_le I U hn) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hrad := twice_search_radius_le_dyadic I.m U hm hU
  have hExp : slackRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by have hs := slackRangeExponent_le_qualitySlackExponent I.m U k; unfold ipmQualityRangeExponent; omega
  have hUpper : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) :=
    pow_le_pow_right₀ (by norm_num) hExp
  have hu : (1:ℝ)≤U := by exact_mod_cast hU
  have hsq : (U:ℝ)≤(U:ℝ)^2 := by nlinarith only [mul_nonneg (show (0:ℝ)≤U by positivity) (sub_nonneg.mpr hu)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤I.m by positivity)
  have hh : (0:ℝ)≤(I.m:ℝ)*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact (fits_integer_at_quality_precision I.m U k (D.pathSum s a b)
    (by linarith only [hs,hmul,hrad,hUpper,hh])).1

end MinCostFlow.IPM.Machine
