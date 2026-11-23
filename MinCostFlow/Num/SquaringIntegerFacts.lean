module

public import MinCostFlow.Num.SquaringFacts
public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Integer numerators for rounded squaring

Each square is divided by the scale before it is stored. Decoding this integer
recurrence gives exactly the rounded real recurrence. An upper bound on the
exact final power bounds every earlier rounded result and ensures it fits.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- The integer numerator after `n` rounded squarings. -/
def squaresInt (P : ℕ) (A : ℤ) : ℕ→ℤ
  | 0 => A
  | n+1 => squaresInt P A n*squaresInt P A n/(2:ℤ)^P

/-- Integer squaring agrees with the real rounding calculation. -/
theorem squaresInt_value (P : ℕ) (A : ℤ) (n : ℕ) :
    (squaresInt P A n:ℝ)/(2:ℝ)^P=roundedSquares P ((A:ℝ)/(2:ℝ)^P) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [roundedSquares,← ih,pow_two,dyadicFloor_product]
    rfl

/-- An exact final-power bound covers the signed integer range of every
rounded output. -/
theorem squaresInt_bounds {P B n : ℕ} {A : ℤ}
    (hA : (2:ℤ)^P≤A)
    (hpow : ((A:ℝ)/(2:ℝ)^P)^(2^n)≤(2:ℝ)^(2*B)) :
    (2:ℤ)^P≤squaresInt P A n ∧ squaresInt P A n≤(2:ℤ)^(2*B)*(2:ℤ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have ha1 : 1≤(A:ℝ)/(2:ℝ)^P := by
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (2:ℝ)^P≤(A:ℝ) by exact_mod_cast hA)
  have hb := roundedSquares_bounds ha1 (le_refl ((A:ℝ)/(2:ℝ)^P)) P n
  rw [← squaresInt_value] at hb
  have hlo := (le_div_iff₀ hp).mp hb.1
  have hhi := (div_le_iff₀ hp).mp (le_trans hb.2 hpow)
  simp only [one_mul] at hlo
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Four spare bits beyond the largest exponential numerator suffice for
nonnegative stored values. -/
theorem fits_exp_range {h L P B : ℕ} {v : ℤ}
    (hwidth : P+2*B+4≤h*L) (hv0 : 0≤v) (hv : v≤(2:ℤ)^(2*B)*(2:ℤ)^P) :
    Fits h L v := by
  have hc : (2:ℤ)^(P+2*B+4)≤(capacity h L:ℤ) := by
    rw [capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by decide) hwidth
  simp only [pow_add,show (2:ℤ)^4=16 by decide] at hc
  have hp : (0:ℤ)<(2:ℤ)^P*(2:ℤ)^(2*B) := by positivity
  constructor <;> nlinarith only [hv0,hv,hc,hp]

end MinCostFlow.Num
