module

public import MinCostFlow.Num.LogHornerIntegerFacts
public import MinCostFlow.Num.NormalizedLogarithmFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Integer formulas for a normalized logarithm

These are the integer numerators stored by the logarithm procedure. The
formulas match its rounded real calculation. Positivity and range bounds keep
every intermediate value in the signed block range.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Numerator of the rounded change of variable. -/
def normalizedLogArgument (P : ℕ) (N : ℤ) : ℤ :=
  (N-(2:ℤ)^P)*(2:ℤ)^P/(N+(2:ℤ)^P)

/-- Numerator of the rounded square. -/
def normalizedLogSquare (P : ℕ) (N : ℤ) : ℤ :=
  normalizedLogArgument P N*normalizedLogArgument P N/(2:ℤ)^P

/-- Numerator returned by the full normalized logarithm calculation. -/
def normalizedLogInt (P : ℕ) (N : ℤ) (n : ℕ) : ℤ :=
  2*(normalizedLogArgument P N*logHornerInt P (normalizedLogSquare P N) 0 n/(2:ℤ)^P)

/-- The integer change of variable matches the rounded real quotient. -/
theorem normalizedLogArgument_value {P : ℕ} {N : ℤ} (hN : (2:ℤ)^P≤N) :
    (normalizedLogArgument P N:ℝ)/(2:ℝ)^P=
      dyadicFloor P (((N:ℝ)/(2:ℝ)^P-1)/((N:ℝ)/(2:ℝ)^P+1)) := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have he : ((N:ℝ)/(2:ℝ)^P-1)/((N:ℝ)/(2:ℝ)^P+1)=
      (((N-(2:ℤ)^P:ℤ):ℝ)/(2:ℝ)^P)/(((N+(2:ℤ)^P:ℤ):ℝ)/(2:ℝ)^P) := by
    push_cast
    field_simp
  have hden : (0:ℤ)≤N+2^P := by
    have hp0 : (0:ℤ)<2^P := by positivity
    omega
  rw [he,dyadicFloor_division _ _ _ hden]
  rfl

/-- All intermediate numerators used after the quotient stay in small ranges. -/
theorem normalizedLogInt_bounds {P : ℕ} {N : ℤ}
    (hN0 : (2:ℤ)^P≤N) (hN1 : N≤2*(2:ℤ)^P) (n : ℕ) :
    (0≤normalizedLogArgument P N ∧ 3*normalizedLogArgument P N≤(2:ℤ)^P) ∧
    (0≤normalizedLogSquare P N ∧ 2*normalizedLogSquare P N≤(2:ℤ)^P) ∧
    (0≤normalizedLogInt P N n ∧ normalizedLogInt P N n≤2*(2:ℤ)^P) := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have hx0 : 1≤(N:ℝ)/(2:ℝ)^P := by
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (2:ℝ)^P≤(N:ℝ) by exact_mod_cast hN0)
  have hx1 : (N:ℝ)/(2:ℝ)^P≤2 := by
    apply (div_le_iff₀ hp).mpr
    exact_mod_cast hN1
  obtain ⟨ht0,ht1,hs0,hs1⟩ := normalized_log_rounding_bounds hx0 hx1 P
  rw [← normalizedLogArgument_value hN0] at ht0 ht1 hs0 hs1
  have hT0r := (le_div_iff₀ hp).mp ht0
  have hT1r := (div_le_iff₀ hp).mp ht1
  have hT0 : 0≤normalizedLogArgument P N := by
    have he : (0:ℝ)≤(normalizedLogArgument P N:ℝ) := by simpa only [zero_mul] using hT0r
    exact_mod_cast he
  have hT1 : 3*normalizedLogArgument P N≤(2:ℤ)^P := by
    have he : 3*(normalizedLogArgument P N:ℝ)≤(2:ℝ)^P := by linarith only [hT1r]
    exact_mod_cast he
  rw [pow_two,dyadicFloor_product] at hs0 hs1
  change 0≤((normalizedLogSquare P N:ℤ):ℝ)/(2:ℝ)^P at hs0
  change ((normalizedLogSquare P N:ℤ):ℝ)/(2:ℝ)^P≤1/2 at hs1
  have hS0r := (le_div_iff₀ hp).mp hs0
  have hS1r := (div_le_iff₀ hp).mp hs1
  have hS0 : 0≤normalizedLogSquare P N := by
    have he : (0:ℝ)≤(normalizedLogSquare P N:ℝ) := by simpa only [zero_mul] using hS0r
    exact_mod_cast he
  have hS1 : 2*normalizedLogSquare P N≤(2:ℤ)^P := by
    have he : 2*(normalizedLogSquare P N:ℝ)≤(2:ℝ)^P := by linarith only [hS1r]
    exact_mod_cast he
  obtain ⟨hH0,hH1⟩ := logHornerInt_bounds hS0 hS1 0 n
  have hT2 : 2*normalizedLogArgument P N≤(2:ℤ)^P := by omega
  obtain ⟨hM0,hM1⟩ := logHornerInt_product_bounds hT0 hT2 hH0 hH1
  refine ⟨⟨hT0,hT1⟩,⟨hS0,hS1⟩,?_,?_⟩
  · unfold normalizedLogInt
    omega
  · unfold normalizedLogInt
    omega

/-- Decoding the integer algorithm gives exactly the real algorithm, with
all roundings in the same places. -/
theorem normalizedLogInt_value {P : ℕ} {N : ℤ} (hN : (2:ℤ)^P≤N) (n : ℕ) :
    (normalizedLogInt P N n:ℝ)/(2:ℝ)^P=
      normalizedLogRounded P ((N:ℝ)/(2:ℝ)^P) n := by
  unfold normalizedLogRounded
  rw [← normalizedLogArgument_value hN]
  dsimp only
  rw [pow_two,dyadicFloor_product]
  change (normalizedLogInt P N n:ℝ)/(2:ℝ)^P=
    2*dyadicFloor P (((normalizedLogArgument P N:ℤ):ℝ)/(2:ℝ)^P*
      roundedLogHorner P (((normalizedLogSquare P N:ℤ):ℝ)/(2:ℝ)^P) 0 n)
  rw [← logHornerInt_value,dyadicFloor_product]
  simp only [normalizedLogInt,Int.cast_mul,Int.cast_ofNat]
  ring

/-- Four spare bits also cover nonnegative intermediates up to four times
the fixed-point scale. -/
theorem fits_four_scale {h L P : ℕ} {v : ℤ}
    (hwidth : P+4≤h*L) (hv0 : 0≤v) (hv : v≤4*(2:ℤ)^P) : Fits h L v := by
  have hc : (2:ℤ)^(P+4)≤(capacity h L:ℤ) := by
    rw [capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by decide) hwidth
  rw [pow_add] at hc
  norm_num only [show (2:ℤ)^4=16 by decide] at hc
  have hp : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  constructor <;> omega

end MinCostFlow.Num
