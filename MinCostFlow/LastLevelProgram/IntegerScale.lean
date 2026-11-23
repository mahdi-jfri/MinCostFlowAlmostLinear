module

public import MinCostFlow.SparseCore.LastLevel
import Mathlib.Tactic

/-!
# An integer update scale for the last-level rebuild

A binary logarithm of the vertex count bounds the real logarithm
in the rounded potential. Using this integer bound lets the machine
form the update denominator with word arithmetic.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open SparseCore LSF

/-- A machine-computable update scale, given an integer bound on the
constant in the tree guarantee. -/
def integerScale (D : ℕ) (G : MGraph) : ℕ :=
  4 * D * G.m * (Nat.log 2 (G.n + 2) + 1)^2

private theorem bitCount_bounds (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) ∧
    ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) ≤ 4 * Real.log ((n : ℝ) + 2) := by
  have hpow : (n + 2 : ℕ) < 2^(Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  have hpow' : (n : ℝ) + 2 ≤ (2 : ℝ)^(Nat.log 2 (n + 2) + 1) := by
    exact_mod_cast hpow.le
  have hlog := Real.log_le_log (by positivity) hpow'
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hhalf := half_lt_log_add_two n
  -- The lower power of two is already below the vertex count plus two.
  have hlo : (2 : ℝ)^Nat.log 2 (n + 2) ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n + 2 ≠ 0 by omega)
  have hlowLog := Real.log_le_log (by positivity) hlo
  rw [Real.log_pow] at hlowLog
  have hlog2Half := half_lt_log_add_two 0
  have hhalf' : (1 / 2 : ℝ) ≤ Real.log 2 := by simpa using hlog2Half.le
  have hmul := mul_le_mul_of_nonneg_left hhalf' (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  constructor
  · exact hlog.trans ((mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)).trans_eq (mul_one _))
  · push_cast
    linarith only [hmul, hlowLog, hhalf]

/-- The integer scale is large enough for the rounded update. If the
integer constant is at most twice the real constant, the scale loses
only a factor of 32 in the stretch bound. -/
theorem integerScale_bounds (C : ℝ) (G : MGraph) (D : ℕ)
    (hlo : max 1 C ≤ (D : ℝ)) (hhi : (D : ℝ) ≤ 2 * max 1 C) :
    2 * lastRho C G ≤ (integerScale D G : ℝ) ∧
      (integerScale D G : ℝ) ≤ 32 * (2 * lastRho C G) := by
  obtain ⟨hb₁, hb₂⟩ := bitCount_bounds G.n
  have hlog : 0 ≤ Real.log ((G.n : ℝ) + 2) := by
    linarith [half_lt_log_add_two G.n]
  have hB := Nat.cast_nonneg (α := ℝ) (Nat.log 2 (G.n + 2) + 1)
  have hC : (0 : ℝ) ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  have hlo' := mul_le_mul hlo (pow_le_pow_left₀ hlog hb₁ 2) (sq_nonneg _)
    (Nat.cast_nonneg D)
  have hhi' := mul_le_mul hhi (pow_le_pow_left₀ hB hb₂ 2) (sq_nonneg _)
    (mul_nonneg zero_le_two hC)
  unfold integerScale lastRho lastW
  push_cast
  push_cast at hlo' hhi'
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_right hlo' (Nat.cast_nonneg (α := ℝ) G.m)]
  · nlinarith only [mul_le_mul_of_nonneg_right hhi' (Nat.cast_nonneg (α := ℝ) G.m)]

/-- The model's update scale, with the real LSST constant rounded up once. -/
noncomputable def roundedScale (C : ℝ) (G : MGraph) : ℝ :=
  integerScale ⌈max 1 C⌉₊ G

/-- The integer update scale lies within a fixed factor of the reference
scale used by the exact-real potential. -/
theorem roundedScale_bounds (C : ℝ) (G : MGraph) :
    2 * lastRho C G ≤ roundedScale C G ∧
      roundedScale C G ≤ 32 * (2 * lastRho C G) := by
  have h₁ : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have h₂ := Nat.ceil_lt_add_one (zero_le_one.trans h₁)
  exact integerScale_bounds C G _ (Nat.le_ceil _) (by linarith)

end MinCostFlow.LastLevelProgram
