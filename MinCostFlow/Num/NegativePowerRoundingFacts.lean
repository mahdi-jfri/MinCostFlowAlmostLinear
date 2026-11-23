module

public import MinCostFlow.Num.NegativePowerFacts
public import MinCostFlow.Num.DyadicRoundingFacts
public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.LogarithmRangeFacts
import Mathlib.Tactic

/-!
# Rounding and range bounds for negative powers

The dyadic input range bounds the absolute logarithm by `E`. Multiplication
by an exponent in `[0,2]` therefore keeps the exponential argument small.
These bounds also prove that the rounded product and its signed negation fit.
-/

public section
namespace MinCostFlow.Num

/-- The logarithm of an input in `[2⁻ᴱ,2ᴱ]` has absolute value at most `E`. -/
theorem log_abs_le_exponent {x : ℝ} {E : ℕ}
    (hlo : 1/(2:ℝ)^E≤x) (hhi : x≤(2:ℝ)^E) : |Real.log x|≤E := by
  have hxp : 0<x := lt_of_lt_of_le (by positivity) hlo
  have hlog0 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hup := Real.log_le_log hxp hhi
  have hlow := Real.log_le_log (show (0:ℝ)<1/(2:ℝ)^E by positivity) hlo
  rw [Real.log_pow] at hup
  rw [Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow] at hlow
  have hmul := mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg E : (0:ℝ)≤E)
  rw [abs_le]
  constructor <;> linarith only [hup,hlow,hmul]

/-- The rounded exponent product has absolute value at most `2E+3` when
the logarithm has absolute error at most one. -/
theorem negative_power_product_bound {x a l : ℝ} {P E : ℕ}
    (hlo : 1/(2:ℝ)^E≤x) (hhi : x≤(2:ℝ)^E)
    (ha0 : 0≤a) (ha2 : a≤2) (hl : |l-Real.log x|≤1) :
    |dyadicFloor P (a*l)|≤2*(E:ℝ)+3 := by
  have hlog := log_abs_le_exponent hlo hhi
  have hlabs : |l|≤(E:ℝ)+1 := by
    have hh := abs_add_le (l-Real.log x) (Real.log x)
    rw [sub_add_cancel] at hh
    linarith only [hh,hl,hlog]
  have hprod : |a*l|≤2*((E:ℝ)+1) := by
    rw [abs_mul,abs_of_nonneg ha0]
    exact mul_le_mul ha2 hlabs (abs_nonneg _) (by norm_num)
  have hr := dyadicFloor_error P (a*l)
  have hu : 1/(2:ℝ)^P≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hh := abs_add_le (dyadicFloor P (a*l)-a*l) (a*l)
  rw [sub_add_cancel] at hh
  linarith only [hr,hu,hprod,hh]

/-- Negating the rounded positive product adds at most one last-place unit
of error to the desired negative product. -/
theorem negative_power_product_rounding (P : ℕ) (a l : ℝ) :
    |(-dyadicFloor P (a*l))-(-a*l)|≤1/(2:ℝ)^P := by
  have he : (-dyadicFloor P (a*l))-(-a*l)=-(dyadicFloor P (a*l)-a*l) := by ring
  rw [he,abs_neg]
  exact dyadicFloor_error P (a*l)

/-- The integer product and its negation fit with six spare bits beyond
precision and `E`. -/
theorem negative_power_product_fits {h L P E : ℕ} {A V : ℤ}
    (hwidth : P+E+6≤h*L)
    (hbound : |dyadicFloor P ((A:ℝ)/(2:ℝ)^P*((V:ℝ)/(2:ℝ)^P))|≤2*(E:ℝ)+3) :
    Fits h L (A*V/(2:ℤ)^P) ∧ Fits h L (-(A*V/(2:ℤ)^P)) := by
  rw [dyadicFloor_product,abs_div,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) P)] at hbound
  have hh := (div_le_iff₀ (show (0:ℝ)<(2:ℝ)^P by positivity)).mp hbound
  have hh' : |(A*V/(2:ℤ)^P:ℤ)|≤(2*(E:ℤ)+3)*(2:ℤ)^P := by exact_mod_cast hh
  have hp : (0:ℤ)≤(2:ℤ)^P := by positivity
  have hb : |(A*V/(2:ℤ)^P:ℤ)|≤2*(E+2+1:ℕ)*(2:ℤ)^P := by
    push_cast
    nlinarith only [hh',hp]
  constructor
  · exact fits_log_range (E:=E+2) (by omega) hb
  · apply fits_log_range (E:=E+2) (by omega)
    simpa only [abs_neg] using hb

end MinCostFlow.Num
