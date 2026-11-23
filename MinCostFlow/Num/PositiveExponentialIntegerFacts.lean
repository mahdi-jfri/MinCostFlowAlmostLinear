module

public import MinCostFlow.Num.PositiveExponentialFacts
public import MinCostFlow.Num.ExpHornerIntegerFacts
public import MinCostFlow.Num.SquaringIntegerFacts
import Mathlib.Tactic

/-!
# Integer formula for the positive exponential

A right shift reduces the argument, the rounded Horner recurrence evaluates
its exponential, and rounded squaring restores the original scale of the
argument. The decoded integer formula agrees with the complete real rounding
calculation.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Integer numerator produced by positive exponential evaluation. -/
def positiveExpInt (P B : ℕ) (N : ℤ) : ℤ :=
  squaresInt P (expHornerInt P (N/(2:ℤ)^(B+2)) 0 (P+4)) (B+2)

/-- The right shift of the input agrees with rounding the halved argument. -/
theorem positiveExp_reduced_value (P B : ℕ) (N : ℤ) :
    ((N/(2:ℤ)^(B+2):ℤ):ℝ)/(2:ℝ)^P=
      dyadicFloor P (((N:ℝ)/(2:ℝ)^P)/(2:ℝ)^(B+2)) := by
  have hh := dyadicFloor_div_nat N (2^(B+2)) P
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  exact hh.symm

/-- Integer and real calculations put every rounding in the same place. -/
theorem positiveExpInt_value (P B : ℕ) (N : ℤ) :
    (positiveExpInt P B N:ℝ)/(2:ℝ)^P=positiveExpRounded P B ((N:ℝ)/(2:ℝ)^P) := by
  rw [positiveExpInt,squaresInt_value,expHornerInt_value,positiveExp_reduced_value]
  rfl

/-- The reduced stored argument lies between zero and one half. -/
theorem positiveExp_reduced_bounds {P B : ℕ} {N : ℤ}
    (hN0 : 0≤N) (hNB : (N:ℝ)/(2:ℝ)^P≤B) :
    0≤N/(2:ℤ)^(B+2) ∧ 2*(N/(2:ℤ)^(B+2))≤(2:ℤ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  have hx0 : (0:ℝ)≤(N:ℝ)/(2:ℝ)^P := div_nonneg (by exact_mod_cast hN0) (le_of_lt hp)
  obtain ⟨_,_,hr0,hr1⟩ := positive_exp_reduced_bounds hx0 hNB P
  rw [← positiveExp_reduced_value] at hr0 hr1
  have hh0 := (le_div_iff₀ hp).mp hr0
  have hh1 := (div_le_iff₀ hp).mp hr1
  simp only [zero_mul] at hh0
  have hh1' : 2*((N/(2:ℤ)^(B+2):ℤ):ℝ)≤(2:ℝ)^P := by linarith only [hh1]
  constructor
  · exact_mod_cast hh0
  · exact_mod_cast hh1'

/-- The exact power of the initial series value is bounded by the final
exponential range, so every subsequent rounded square fits. -/
theorem positiveExp_horner_power_bound {P B : ℕ} {N : ℤ}
    (hN0 : 0≤N) (hNB : (N:ℝ)/(2:ℝ)^P≤B) :
    ((expHornerInt P (N/(2:ℤ)^(B+2)) 0 (P+4):ℝ)/(2:ℝ)^P)^(2^(B+2))≤
      (2:ℝ)^(2*B) := by
  obtain ⟨hY0,hY1⟩ := positiveExp_reduced_bounds hN0 hNB
  obtain ⟨hlo,hhi,_⟩ := expHornerInt_exp_error hY0 hY1
  have hT : Real.exp (((N/(2:ℤ)^(B+2):ℤ):ℝ)/(2:ℝ)^P)≤
      Real.exp (((N:ℝ)/(2:ℝ)^P)/(2:ℝ)^(B+2)) := by
    rw [positiveExp_reduced_value]
    exact Real.exp_le_exp.mpr (dyadicFloor_le P _)
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤(expHornerInt P (N/(2:ℤ)^(B+2)) 0 (P+4):ℝ)/(2:ℝ)^P by linarith only [hlo])
    (le_trans hhi hT) (2^(B+2))
  rw [exp_halving_power] at hp
  exact le_trans hp (exp_le_two_pow_twice hNB)

end MinCostFlow.Num
