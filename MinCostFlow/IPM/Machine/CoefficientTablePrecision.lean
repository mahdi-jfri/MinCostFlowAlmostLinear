module

public import MinCostFlow.IPM.Machine.CoefficientTables
public import MinCostFlow.IPM.Machine.PrecisionProducts
import Mathlib.Tactic.Linarith

/-!
# Deriving the coefficient loader's numeric preconditions

The target-test table program does not need a range oracle for its
integer loads. The input common bound and selected precision prove
that all signed costs, upper capacities and scaled numerators fit.
Only the graph representation and caller-provided workspace remain as
ordinary machine preconditions.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem input_bound_in_chosen_range (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    (U:ℝ) ≤ (2:ℝ)^(ipmRangeExponent m U) := by
  have hh := twice_capacity_le_dyadic m U hm hU
  have hu : (0:ℝ) ≤ U := Nat.cast_nonneg _
  have he : slackRangeExponent m U ≤ ipmRangeExponent m U := by
    unfold ipmRangeExponent
    omega
  have hlo : (U:ℝ) ≤ (2:ℝ)^(slackRangeExponent m U) := by linarith only [hh,hu]
  exact hlo.trans (pow_le_pow_right₀ (by norm_num) he)

/-- The input numerical bound implies every integer and shifted-numerator
fit required by the actual coefficient-preparation procedure. -/
theorem coefficientTables_pre_of_chosen_precision (I : Instance) (U : ℕ)
    {w a heap : ℕ} {mem : ℕ → ℕ} (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hat : ZeroLowerAt mem a I)
    (hend : a+(zeroLowerWords I).length ≤ heap)
    (hinput : ∀ x ∈ zeroLowerWords I,x < 2^w) (hzero : ZeroFrom mem heap)
    (hspace : heap+(9*I.m+1)*ipmLimbs I.m U < 2^w) :
    (coefficientTablesContract w 4 I).pre
      [a,ipmLimbs I.m U,ipmPrecision I.m U,heap] mem := by
  have hbound := input_bound_in_chosen_range I.m U hm hU
  have hmargin := (ipm_precision_margins I.m U).2.2.2.2.1
  refine ⟨⟨a,ipmLimbs I.m U,ipmPrecision I.m U,heap,rfl,hI,hm,hat,hend,hinput,
    by omega,?_,?_⟩,hzero,hspace⟩
  · intro e
    exact (fits_integer_at_chosen_precision I.m U (I.edge e).cost
      ((hnums.2 e).2.2.trans hbound)).1
  · intro e
    exact fits_integer_at_chosen_precision I.m U (I.edge e).upper
      ((hnums.2 e).2.1.trans hbound)

/-- The input numerical bound implies every integer and shifted-numerator
fit required by the actual coefficient-preparation procedure. -/
theorem coefficientTables_pre_of_widened_precision (I : Instance) (U k : ℕ)
    {w a heap : ℕ} {mem : ℕ → ℕ} (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hat : ZeroLowerAt mem a I)
    (hend : a+(zeroLowerWords I).length ≤ heap)
    (hinput : ∀ x ∈ zeroLowerWords I,x < 2^w) (hzero : ZeroFrom mem heap)
    (hspace : heap+(9*I.m+1)*ipmQualityLimbs I.m U k < 2^w) :
    (coefficientTablesContract w 4 I).pre
      [a,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,heap] mem := by
  have hExp : ipmRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  have hbound := (input_bound_in_chosen_range I.m U hm hU).trans (pow_le_pow_right₀ (by norm_num) hExp)
  have hmargin := (ipm_quality_precision_margins I.m U k).2.2.2.2.1
  refine ⟨⟨a,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,heap,rfl,hI,hm,hat,hend,hinput,
    by omega,?_,?_⟩,hzero,hspace⟩
  · intro e
    exact (fits_integer_at_quality_precision I.m U k (I.edge e).cost
      ((hnums.2 e).2.2.trans hbound)).1
  · intro e
    exact fits_integer_at_quality_precision I.m U k (I.edge e).upper
      ((hnums.2 e).2.1.trans hbound)

end MinCostFlow.IPM.Machine
