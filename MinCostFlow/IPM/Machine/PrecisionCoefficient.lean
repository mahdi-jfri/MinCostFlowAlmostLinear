module

public import MinCostFlow.IPM.Machine.PrecisionDyadic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer coefficient bounds for the gradient

The numerical gradient procedure first forms the integer `20mc`.
The binary lengths of the edge count and the bound on integral costs
supply its range, without a numerical hypothesis on an output of the
IPM. The same bound covers the uncoupled coefficient `20m`.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Five guard bits cover the factor twenty in the gradient. -/
@[expose] def gradientCoefficientExponent (m U : ℕ) : ℕ :=
  m.size+U.size+5

/-- The gradient's integer coefficient fits its explicitly chosen range. -/
theorem gradient_integer_coefficient_bound (m U : ℕ) (c : ℤ)
    (hc : c.natAbs ≤ U) :
    |20*(m:ℤ)*c| ≤ (2:ℤ)^(gradientCoefficientExponent m U) := by
  have hm := (Nat.lt_size_self m).le
  have hu := hc.trans (Nat.lt_size_self U).le
  have hh := Nat.mul_le_mul hm hu
  have hbound : 20*m*c.natAbs ≤ 2^(gradientCoefficientExponent m U) := by
    calc
      20*m*c.natAbs = 20*(m*c.natAbs) := by ring
      _ ≤ 20*(2^m.size*2^U.size) := Nat.mul_le_mul_left 20 hh
      _ ≤ 32*(2^m.size*2^U.size) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by simp only [gradientCoefficientExponent,pow_add]; ring
  have hreal : (20:ℤ)*m*|c| ≤ (2:ℤ)^(gradientCoefficientExponent m U) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hbound
  simpa only [abs_mul,abs_of_nonneg (by norm_num : (0:ℤ) ≤ 20),
    abs_of_nonneg (Int.natCast_nonneg m)] using hreal

/-- The unweighted coefficient is covered when `U≥1`. -/
theorem gradient_count_coefficient_bound (m U : ℕ) (hU : 1 ≤ U) :
    20*m ≤ 2^(gradientCoefficientExponent m U) := by
  have hh := gradient_integer_coefficient_bound m U 1 (by simpa using hU)
  norm_num only [mul_one,abs_mul,abs_of_nonneg (by norm_num : (0:ℤ) ≤ 20),
    abs_of_nonneg (Int.natCast_nonneg m)] at hh
  exact_mod_cast hh

/-- The input bound on real costs entails the integer range premise of
`gradientContract` for each source edge. -/
theorem gradient_instance_coefficient_bound (I : Instance) (U : ℕ)
    (hnums : NumbersBounded I U) (e : Fin I.m) :
    |20*(I.m:ℤ)*(I.edge e).cost| ≤
      (2:ℤ)^(gradientCoefficientExponent I.m U) := by
  apply gradient_integer_coefficient_bound
  have hh := (hnums.2 e).2.2
  rw [← Int.cast_abs,← Int.natCast_natAbs] at hh
  exact_mod_cast hh

end MinCostFlow.IPM.Machine
