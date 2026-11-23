module

public import MinCostFlow.IPM.Machine.ComputedGradient
public import MinCostFlow.IPM.Machine.PrecisionEdgeRange
import Mathlib.Tactic.Ring

/-!
# Ranges of coefficients computed with an epoch residual

The numerical gradient's cost term uses the epoch residual rather than
the residual of the partially refreshed stored vector. Shifting the
formal target identifies that expression with the gradient already used
in the range proof. No routing condition on the mixed stored vector is
needed, only its capacity slacks and the stored residual's range.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Stored-residual coefficients fit the same common range as ordinary
IPM coefficients. The input residual need not be the stored flow's cost
minus the current search target. -/
theorem computed_epoch_coefficients_range (I : Instance) (U : ℕ)
    (a r z ell : ℝ) (stored : Fin I.m → ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hnums : NumbersBounded I U) (e : Fin I.m)
    (hu : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ (I.edge e).upper-stored e ∧
      (I.edge e).upper-stored e ≤ (2:ℝ)^(slackRangeExponent I.m U))
    (hd : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ stored e-(I.edge e).lower ∧
      stored e-(I.edge e).lower ≤ (2:ℝ)^(slackRangeExponent I.m U))
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ r)
    (hell : ScalarApprox 2 ell (lengths I a stored e))
    (hz : |z-gradientWithResidual I a r stored e| ≤ lengths I a stored e) :
    |z| ≤ (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ ell ∧
      ell ≤ (2:ℝ)^(ipmRangeExponent I.m U) := by
  apply stored_coefficients_in_chosen_range I U a (I.cost stored-r) z ell stored ha ha' hnums e hu hd
  · simpa only [residual,sub_sub_cancel] using hr
  · exact hell
  · rw [gradient_at_stored_residual]
    exact hz

/-- The numerical gradient tolerance supplies the absolute-error premise
of the common range proof whenever its relative error unit is at most one. -/
theorem computed_gradient_absolute_error (I : Instance) (a r delta : ℝ)
    (stored computed : Fin I.m → ℝ) (hstored : StrictlyInside I stored)
    (hdelta : delta ≤ 1)
    (hcomputed : GradientTolerance (lengths I a stored) computed
      (gradientWithResidual I a r stored) delta) (e : Fin I.m) :
    |computed e-gradientWithResidual I a r stored e| ≤ lengths I a stored e := by
  have hlen := lengths_pos I a stored hstored e
  have hh := hcomputed e
  rw [abs_div,abs_of_pos hlen] at hh
  exact ((div_le_iff₀ hlen).mp hh).trans (mul_le_of_le_one_left hlen.le hdelta)

end MinCostFlow.IPM.Machine
