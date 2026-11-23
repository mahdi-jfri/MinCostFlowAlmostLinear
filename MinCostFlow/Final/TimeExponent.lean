module

public import MinCostFlow.Statement.Main
public import MinCostFlow.Chain.Theorem5_1Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# A vanishing exponent for the subpolynomial factor

The factor from Theorem 5.1 (page 15) can be written as a power
of the padded edge count, as needed by Theorem 1.1 (page 2).
-/

public noncomputable section
namespace MinCostFlow.Final
open Filter Topology Chain

/-- Absorb a positive constant and the subpolynomial factor into the edge exponent. -/
def scalingTimeExponent (A B : ℝ) (m : ℕ) : ℝ :=
  Real.log A / Real.log ((m:ℝ)+2) +
    Real.log (alg2TimeFactor B (47/48) m) / Real.log ((m:ℝ)+2)

private theorem logFactor_nonneg (B : ℝ) (hB : 0 ≤ B) (m : ℕ) :
    0 ≤ Real.log (alg2TimeFactor B (47/48) m) := by
  have hl := Real.log_nonneg (show (1:ℝ) ≤ (m:ℝ)+2 by
    linarith [Nat.cast_nonneg (α:=ℝ) m])
  unfold alg2TimeFactor
  rw [Real.log_exp]
  exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hl _)) (Real.log_nonneg (by linarith))

/-- The exponent tends to zero as the edge count grows. -/
theorem scalingTimeExponent_tendsto (A B : ℝ) (hB : 0 ≤ B) :
    Tendsto (scalingTimeExponent A B) atTop (𝓝 0) := by
  have htop : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hc := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp htop)).const_mul (Real.log A)
  have hf : Tendsto (fun m : ℕ => Real.log (alg2TimeFactor B (47/48) m) /
      Real.log ((m:ℝ)+2)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_log_alg2TimeFactor_div_log B (a := 47/48) (by norm_num) (by norm_num))
    · exact Eventually.of_forall fun m =>
        div_nonneg (logFactor_nonneg B hB m)
          (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) m]))
    · filter_upwards [eventually_ge_atTop (2:ℕ)] with m hm
      have h₂ : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      exact div_le_div_of_nonneg_left (logFactor_nonneg B hB m)
        (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) (by linarith))
  change Tendsto (fun m : ℕ => Real.log A / Real.log ((m:ℝ)+2) +
    Real.log (alg2TimeFactor B (47/48) m) / Real.log ((m:ℝ)+2)) atTop (𝓝 0)
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, zero_add] using hc.add hf

/-- A cost with a linear vertex term and the subpolynomial edge factor
has the time bound of Theorem 1.1. -/
theorem cost_le_timeBound_of_timeFactor (K A B cost : ℝ) (hA : 0 < A) (I : Instance)
    (hcost : cost ≤ K*I.n + (((I.m:ℝ)+2)*A*alg2TimeFactor B (47/48) I.m) *
      Real.log ((I.maxCapacity:ℝ)+2) * Real.log ((I.maxCost:ℝ)+2)) :
    cost ≤ timeBound K (scalingTimeExponent A B) I := by
  let x := (I.m:ℝ)+2
  let f := alg2TimeFactor B (47/48) I.m
  have hx : 0 < x := by dsimp [x]; positivity
  have hl : Real.log x ≠ 0 := (Real.log_pos (by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) I.m])).ne'
  have hf : 0 < f := alg2TimeFactor_pos _ _ _
  have he : (1+scalingTimeExponent A B I.m)*Real.log x =
      Real.log x + Real.log A + Real.log f := by
    change (1 + (Real.log A / Real.log x + Real.log f / Real.log x))*Real.log x = _
    field_simp
    ring
  have hxpow : x^(1+scalingTimeExponent A B I.m) = x*A*f := by
    rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x), he, Real.exp_add, Real.exp_add,
      Real.exp_log hx, Real.exp_log hA, Real.exp_log hf]
  unfold timeBound
  rw [show (I.m:ℝ)+2 = x by rfl, hxpow]
  exact hcost

end MinCostFlow.Final
