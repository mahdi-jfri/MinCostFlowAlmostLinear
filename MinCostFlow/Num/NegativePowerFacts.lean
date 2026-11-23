module

public import MinCostFlow.Num.ExponentialFacts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Error propagation for negative powers

For positive `x`, the negative power is `exp (-a*log x)`. An absolute
logarithm error is multiplied by at most two when `a` is in `[0,2]`.
The lemmas below combine that error, the error in the product, and the relative
error in the exponential. They do not assume a machine implementation of those
operations.
-/

public section
namespace MinCostFlow.Num

/-- Relative exponential error and absolute argument error compose with the
explicit bound `η*(1+2δ)+2δ`. -/
theorem exp_composed_error {x y z δ η : ℝ}
    (hδ : δ≤1) (hη : 0≤η) (harg : |y-x|≤δ)
    (hout : |z-Real.exp y|≤η*Real.exp y) :
    |z-Real.exp x|≤(η*(1+2*δ)+2*δ)*Real.exp x := by
  have he := exp_argument_error hδ harg
  have hy : Real.exp y≤(1+2*δ)*Real.exp x := by
    have hh := (abs_le.mp he).2
    linarith
  calc
    |z-Real.exp x| ≤ |z-Real.exp y|+|Real.exp y-Real.exp x| := abs_sub_le _ _ _
    _ ≤ η*Real.exp y+2*δ*Real.exp x := add_le_add hout he
    _ ≤ η*((1+2*δ)*Real.exp x)+2*δ*Real.exp x :=
      add_le_add (mul_le_mul_of_nonneg_left hy hη) (le_refl _)
    _ = (η*(1+2*δ)+2*δ)*Real.exp x := by ring

/-- The logarithm and multiplication errors add before exponentiation. -/
theorem negative_power_argument_error {x a l t εlog εmul : ℝ}
    (ha0 : 0≤a) (ha2 : a≤2) (hε : 0≤εlog)
    (hl : |l-Real.log x|≤εlog) (ht : |t-(-a*l)|≤εmul) :
    |t-(-a*Real.log x)|≤εmul+2*εlog := by
  have hp : |(-a*l)-(-a*Real.log x)|≤2*εlog := by
    rw [← mul_sub,abs_mul,abs_neg,abs_of_nonneg ha0]
    exact le_trans (mul_le_mul_of_nonneg_left hl ha0)
      (mul_le_mul_of_nonneg_right ha2 hε)
  exact le_trans (abs_sub_le _ _ _) (add_le_add ht hp)

/-- A real-valued negative-power error bound ready for instantiation with
fixed-point rounding bounds. Here `l` approximates the logarithm and `t`
approximates the negative product. -/
theorem negative_power_composed_error {x a l t z εlog εmul η : ℝ}
    (hx : 0<x) (ha0 : 0≤a) (ha2 : a≤2) (hε : 0≤εlog)
    (hsmall : εmul+2*εlog≤1) (hη : 0≤η)
    (hl : |l-Real.log x|≤εlog) (ht : |t-(-a*l)|≤εmul)
    (hz : |z-Real.exp t|≤η*Real.exp t) :
    |z-Real.rpow x (-a)|≤
      (η*(1+2*(εmul+2*εlog))+2*(εmul+2*εlog))*Real.rpow x (-a) := by
  have harg := negative_power_argument_error ha0 ha2 hε hl ht
  have he := exp_composed_error hsmall hη harg hz
  have hp : Real.rpow x (-a)=Real.exp (-a*Real.log x) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [hp]
  exact he

/-- Reserving five extra bits for the logarithm, four for multiplication,
and two for the exponential suffices for a negative power's relative error.
The error budget `ε` may in particular be `2⁻q`. -/
theorem negative_power_relative_error {x a l t z ε : ℝ}
    (hx : 0<x) (ha0 : 0≤a) (ha2 : a≤2) (hε0 : 0≤ε) (hε1 : ε≤1)
    (hl : |l-Real.log x|≤ε/32) (ht : |t-(-a*l)|≤ε/16)
    (hz : |z-Real.exp t|≤(ε/4)*Real.exp t) :
    |z-Real.rpow x (-a)|≤ε*Real.rpow x (-a) := by
  have hb := negative_power_composed_error hx ha0 ha2
    (show 0≤ε/32 by positivity) (show ε/16+2*(ε/32)≤1 by linarith)
    (show 0≤ε/4 by positivity) hl ht hz
  have hs : ε^2≤ε := by
    have hh := mul_nonneg hε0 (sub_nonneg.mpr hε1)
    nlinarith only [hh]
  have hc : (ε/4)*(1+2*(ε/16+2*(ε/32)))+2*(ε/16+2*(ε/32))≤ε := by
    nlinarith only [hs,hε0]
  exact le_trans hb (mul_le_mul_of_nonneg_right hc
    (by simp only [Real.rpow_eq_pow]; exact le_of_lt (Real.rpow_pos_of_pos hx _)))

end MinCostFlow.Num
