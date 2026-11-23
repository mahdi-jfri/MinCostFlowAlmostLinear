module

public import MinCostFlow.Num.RoundedExponentialFacts
public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.LogHornerIntegerFacts
import Mathlib.Tactic

/-!
# Integer numerators for exponential Horner evaluation

The integer recurrence first divides a product by the fixed-point scale,
then by the next positive coefficient index, and adds the scale. Its decoded
value is the rounded real recurrence. All tails lie between one and two scale
units, so the multiplication and addition fit with four spare bits.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Integer formula evaluated by the reduced exponential procedure. -/
def expHornerInt (P : ℕ) (Y : ℤ) (i : ℕ) : ℕ→ℤ
  | 0 => (2:ℤ)^P
  | n+1 => (2:ℤ)^P+(Y*expHornerInt P Y (i+1) n/(2:ℤ)^P)/(i+1:ℕ)

/-- Decoding the integer recurrence gives the rounded real recurrence. -/
theorem expHornerInt_value (P : ℕ) (Y : ℤ) (i n : ℕ) :
    (expHornerInt P Y i n:ℝ)/(2:ℝ)^P=
      roundedExpHorner P ((Y:ℝ)/(2:ℝ)^P) i n := by
  have hp : (2:ℝ)^P≠0 := ne_of_gt (pow_pos (by norm_num) _)
  induction n generalizing i with
  | zero => simp [expHornerInt,roundedExpHorner,hp]
  | succ n ih =>
    simp only [expHornerInt,roundedExpHorner,Int.cast_add,add_div,Int.cast_pow,Int.cast_ofNat,div_self hp]
    rw [← ih (i+1),dyadicFloor_product,dyadicFloor_div_nat]

/-- Every rounded tail lies between one and two scale units. -/
theorem expHornerInt_bounds {P : ℕ} {Y : ℤ} (hY0 : 0≤Y) (hY1 : 2*Y≤(2:ℤ)^P)
    (i n : ℕ) : (2:ℤ)^P≤expHornerInt P Y i n ∧ expHornerInt P Y i n≤2*(2:ℤ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have hx0 : (0:ℝ)≤(Y:ℝ)/(2:ℝ)^P := div_nonneg (by exact_mod_cast hY0) (le_of_lt hp)
  have hx1 : (Y:ℝ)/(2:ℝ)^P≤1/2 := by
    apply (div_le_iff₀ hp).mpr
    have hh : 2*(Y:ℝ)≤(2:ℝ)^P := by exact_mod_cast hY1
    linarith only [hh]
  obtain ⟨hlo,hmid,hhi⟩ := expHorner_bounds hx0 hx1 P i n
  have hb : (expHornerInt P Y i n:ℝ)/(2:ℝ)^P≤2 := by
    rw [expHornerInt_value]
    exact le_trans hmid hhi
  rw [← expHornerInt_value] at hlo
  have hhlo := (le_div_iff₀ hp).mp hlo
  have hhhi := (div_le_iff₀ hp).mp hb
  simp only [one_mul] at hhlo
  constructor
  · exact_mod_cast hhlo
  · exact_mod_cast hhhi

/-- The scaled product and its coefficient quotient both lie in `[0,2^P]`. -/
theorem expHornerInt_step_bounds {P : ℕ} {Y : ℤ}
    (hY0 : 0≤Y) (hY1 : 2*Y≤(2:ℤ)^P) (i n : ℕ) :
    (0≤Y*expHornerInt P Y (i+1) n/(2:ℤ)^P ∧
      Y*expHornerInt P Y (i+1) n/(2:ℤ)^P≤(2:ℤ)^P) ∧
    (0≤(Y*expHornerInt P Y (i+1) n/(2:ℤ)^P)/(i+1:ℕ) ∧
      (Y*expHornerInt P Y (i+1) n/(2:ℤ)^P)/(i+1:ℕ)≤(2:ℤ)^P) := by
  obtain ⟨hlo,hhi⟩ := expHornerInt_bounds hY0 hY1 (i+1) n
  have hp0 : (0:ℤ)≤(2:ℤ)^P := by positivity
  obtain ⟨hp,hp'⟩ := logHornerInt_product_bounds hY0 hY1 (le_trans hp0 hlo) hhi
  have hd : (0:ℤ)≤(i+1:ℕ) := Int.natCast_nonneg _
  exact ⟨⟨hp,hp'⟩,Int.ediv_nonneg hp hd,
    le_trans (Int.ediv_le_self (i+1:ℕ) hp) hp'⟩

/-- At the main series length, the decoded integer result is an underestimate
of the real exponential with error at most five last-place units. -/
theorem expHornerInt_exp_error {P : ℕ} {Y : ℤ}
    (hY0 : 0≤Y) (hY1 : 2*Y≤(2:ℤ)^P) :
    1≤(expHornerInt P Y 0 (P+4):ℝ)/(2:ℝ)^P ∧
    (expHornerInt P Y 0 (P+4):ℝ)/(2:ℝ)^P≤Real.exp ((Y:ℝ)/(2:ℝ)^P) ∧
    |(expHornerInt P Y 0 (P+4):ℝ)/(2:ℝ)^P-Real.exp ((Y:ℝ)/(2:ℝ)^P)|≤5/(2:ℝ)^P := by
  rw [expHornerInt_value]
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  apply roundedExpHorner_exp_error (div_nonneg (by exact_mod_cast hY0) (le_of_lt hp))
  apply (div_le_iff₀ hp).mpr
  have hh : 2*(Y:ℝ)≤(2:ℝ)^P := by exact_mod_cast hY1
  linarith only [hh]

end MinCostFlow.Num
