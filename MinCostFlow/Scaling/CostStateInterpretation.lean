module

public import MinCostFlow.Scaling.NearestQuotient
public import MinCostFlow.Scaling.EpsilonOptimal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Interpreting the integer cost-scaling state

In Definition C.6 and Lemma C.7 of Chen et al., arXiv:2203.00671v2,
Appendix C, the rounding unit is epsilon divided by a fixed polynomial in
the edge count. The integer model stores a denominator power and potential
numerators. The real quantities below are their mathematical interpretation,
not data computed by the algorithm. We prove the exact numerator identity
and the rounding error for the model's untruncated integer rounded costs.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- The epsilon represented by the current positive denominator power. -/
def epsilon (C : ℕ) (s : CostState I) : ℝ := (C + 1 : ℕ) / (s.power : ℝ)

/-- The physical rounding unit of Definition C.6, using both residual slots. -/
def roundingUnit (C : ℕ) (s : CostState I) : ℝ :=
  ((C + 1 : ℕ) : ℝ) / (((I.m + I.m) ^ 8 : ℕ) * (s.power : ℝ))

/-- The real potential encoded by the integer table. -/
def realPotential (C : ℕ) (s : CostState I) (v : Fin I.n) : ℝ :=
  s.roundingUnit C * (s.potential v : ℝ)

/-- The integer numerator is exactly the reduced cost times its denominator. -/
theorem costNumerator_cast (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hp : 0 < s.power) (e : Fin (I.m + I.m)) :
    (I.residual s.flow).reducedCost (realPotential (I := I) C s) e =
      (s.costNumerator C e : ℝ) / (((I.m + I.m) ^ 8 : ℕ) * (s.power : ℝ)) := by
  have hb : (((I.m + I.m) ^ 8 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 8 (show I.m + I.m ≠ 0 by omega))
  have hpower : (s.power : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  simp only [Circulation.reducedCost, Circulation.potentialDifference, realPotential,
    roundingUnit, costNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  simp only [Nat.cast_pow] at hb ⊢
  field_simp [hb, hpower]

/-- The scaled integer rounding error is strictly less than one physical unit. -/
theorem roundedCost_error (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hp : 0 < s.power) (e : Fin (I.m + I.m)) :
    -s.roundingUnit C < (I.residual s.flow).reducedCost (realPotential (I := I) C s) e -
        s.roundingUnit C * (s.roundedCost C e : ℝ) ∧
      (I.residual s.flow).reducedCost (realPotential (I := I) C s) e -
        s.roundingUnit C * (s.roundedCost C e : ℝ) < s.roundingUnit C := by
  have hd : (0 : ℝ) < (((I.m + I.m) ^ 8 : ℕ) : ℝ) * (s.power : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (pow_pos (by omega) 8)) (Nat.cast_pos.mpr hp)
  have h := nearestQuotient_error (s.costNumerator C e) (C + 1) (Nat.zero_lt_succ C)
  have hlo : -((C + 1 : ℕ) : ℝ) < (s.costNumerator C e : ℝ) -
      ((C + 1 : ℕ) : ℝ) * (s.roundedCost C e : ℝ) := by exact_mod_cast h.1
  have hup : (s.costNumerator C e : ℝ) -
      ((C + 1 : ℕ) : ℝ) * (s.roundedCost C e : ℝ) < ((C + 1 : ℕ) : ℝ) := by exact_mod_cast h.2
  have hl := (div_lt_div_iff_of_pos_right hd).mpr hlo
  have hu := (div_lt_div_iff_of_pos_right hd).mpr hup
  rw [s.costNumerator_cast C hm hp e]
  simp only [roundingUnit]
  constructor
  · simpa only [sub_div, neg_div, div_mul_eq_mul_div] using hl
  · simpa only [sub_div, div_mul_eq_mul_div] using hu

/-- The physical rounding unit is positive in every nonempty, positive-power state. -/
theorem roundingUnit_pos (C : ℕ) (s : CostState I) (hm : 0 < I.m) (hp : 0 < s.power) :
    0 < s.roundingUnit C := by
  unfold roundingUnit
  have hb : 0 < (I.m + I.m) ^ 8 := pow_pos (by omega) _
  exact div_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ _))
    (mul_pos (Nat.cast_pos.mpr hb) (Nat.cast_pos.mpr hp))

/-- Multiplying the rounding unit by the polynomial denominator gives epsilon. -/
theorem roundingUnit_mul (C : ℕ) (s : CostState I) (hm : 0 < I.m) :
    s.roundingUnit C * (((I.m + I.m) ^ 8 : ℕ) : ℝ) = s.epsilon C := by
  have hb : (((I.m + I.m) ^ 8 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 8 (show I.m + I.m ≠ 0 by omega))
  unfold roundingUnit epsilon
  rw [div_mul_eq_div_mul_one_div, mul_right_comm, div_mul_cancel₀ _ hb, mul_one_div]

/-- The error unit is strictly below half epsilon even for one original edge. -/
theorem roundingUnit_lt_half (C : ℕ) (s : CostState I) (hm : 0 < I.m) (hp : 0 < s.power) :
    s.roundingUnit C < s.epsilon C / 2 := by
  have hpos := s.roundingUnit_pos C hm hp
  have he := s.roundingUnit_mul C hm
  have hB : (2 : ℝ) < (((I.m + I.m) ^ 8 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 2 ^ 8)
      (Nat.pow_le_pow_left (show 2 ≤ I.m + I.m by omega) 8))
  have hh := mul_lt_mul_of_pos_left hB hpos
  rw [he] at hh
  linarith only [hh]

end MinCostFlow.Scaling.CostState
