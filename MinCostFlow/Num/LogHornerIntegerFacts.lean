module

public import MinCostFlow.Num.RoundedLogarithmFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Integer numerators for logarithm Horner evaluation

The stored square has numerator `s`. Coefficients are integer quotients of the
scale by an odd integer. Products are divided by the scale. These formulas
match the rounded real recurrence and keep all intermediate numerators between
zero and twice the scale.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Integer recurrence implemented by the logarithm series procedure. -/
def logHornerInt (P : ℕ) (s : ℤ) (i : ℕ) : ℕ→ℤ
  | 0 => 0
  | n+1 => (2:ℤ)^P/(2*i+1:ℕ)+s*logHornerInt P s (i+1) n/(2:ℤ)^P

/-- Integer and real rounded Horner recurrences agree. -/
theorem logHornerInt_value (P : ℕ) (s : ℤ) (i n : ℕ) :
    (logHornerInt P s i n:ℝ)/(2:ℝ)^P=
      roundedLogHorner P ((s:ℝ)/(2:ℝ)^P) i n := by
  induction n generalizing i with
  | zero => simp [logHornerInt,roundedLogHorner]
  | succ n ih =>
    simp only [logHornerInt,roundedLogHorner,Int.cast_add,add_div]
    rw [← ih (i+1),dyadicFloor_coefficient,dyadicFloor_product]

/-- A positive integer denominator gives a nonnegative coefficient no larger
than the fixed-point scale. -/
theorem logHornerInt_coefficient_bounds (P i : ℕ) :
    0≤(2:ℤ)^P/(2*i+1:ℕ) ∧ (2:ℤ)^P/(2*i+1:ℕ)≤(2:ℤ)^P := by
  have hd : (0:ℤ)<(2*i+1:ℕ) := by exact_mod_cast (show 0<2*i+1 by omega)
  constructor
  · exact Int.ediv_nonneg (le_of_lt (pow_pos (by decide) _)) (le_of_lt hd)
  · exact Int.ediv_le_self (2*i+1:ℕ) (le_of_lt (pow_pos (by decide) P))

/-- All Horner tails have nonnegative numerators at most twice the scale. -/
theorem logHornerInt_bounds {P : ℕ} {s : ℤ}
    (hs0 : 0≤s) (hs : 2*s≤(2:ℤ)^P) (i n : ℕ) :
    0≤logHornerInt P s i n ∧ logHornerInt P s i n≤2*(2:ℤ)^P := by
  have hr0 : (0:ℝ)≤(s:ℝ)/(2:ℝ)^P := div_nonneg (by exact_mod_cast hs0) (by positivity)
  have hr : (s:ℝ)/(2:ℝ)^P≤1/2 := by
    apply (div_le_iff₀ (show (0:ℝ)<(2:ℝ)^P by positivity)).mpr
    have hh : 2*(s:ℝ)≤(2:ℝ)^P := by exact_mod_cast hs
    linarith
  have hb := roundedLogHorner_bounds hr0 hr P i n
  rw [← logHornerInt_value] at hb
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have hlo := (le_div_iff₀ hp).mp hb.1
  simp only [zero_mul] at hlo
  have hhi := (div_le_iff₀ hp).mp hb.2
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Four spare bits cover every nonnegative intermediate up to twice the scale. -/
theorem fits_twice_scale {h L P : ℕ} {v : ℤ}
    (hwidth : P+4≤h*L) (hv0 : 0≤v) (hv : v≤2*(2:ℤ)^P) : Fits h L v := by
  have hc : (2:ℤ)^(P+4)≤(capacity h L:ℤ) := by
    rw [capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by decide) hwidth
  rw [pow_add] at hc
  norm_num only [show (2:ℤ)^4=16 by decide] at hc
  have hp : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  constructor <;> omega

/-- The product quotient fits whenever the tail is bounded by twice the scale. -/
theorem logHornerInt_product_bounds {P : ℕ} {s t : ℤ}
    (hs0 : 0≤s) (hs : 2*s≤(2:ℤ)^P) (ht0 : 0≤t) (ht : t≤2*(2:ℤ)^P) :
    0≤s*t/(2:ℤ)^P ∧ s*t/(2:ℤ)^P≤(2:ℤ)^P := by
  have hp : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  have hmul : s*t≤(2:ℤ)^P*(2:ℤ)^P := by
    have hh := mul_le_mul_of_nonneg_left ht hs0
    have hh' := mul_le_mul_of_nonneg_right hs (le_of_lt hp)
    nlinarith only [hh,hh']
  constructor
  · exact Int.ediv_nonneg (mul_nonneg hs0 ht0) (le_of_lt hp)
  · exact Int.ediv_le_of_le_mul hp hmul

end MinCostFlow.Num
