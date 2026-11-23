module

public import MinCostFlow.Chain.Algorithm2
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Bounds on the game weight `alg2PsiGame`

`alg2PsiGame Ψ M₀ = 2 ⌈Ψ⌉₊ + ⌈log₂ (M₀ + 1)⌉ + 1` is an integer. The paper needs only that the
game weights `‖w^{(t)}‖₁` have `log₂` in `(-Ψ_game, Ψ_game)` (`jtree.tex`, Algorithm 3, globals)
and that `Ψ_game = O(Ψ + log M₀)`. This file proves both sides:
- `alg2PsiGame_real_le`: `(Ψ + log (M₀ + 1)) / log 2 + 1 ≤ alg2PsiGame Ψ M₀`, which gives the
  weight range (`Chain/HiddenTrace.lean`);
- `alg2PsiGame_le`: `alg2PsiGame Ψ M₀ ≤ 2 max 0 Ψ + log (M₀ + 1) / log 2 + 4`, which gives the
  asymptotic bounds.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Chain

/-- `log (M₀ + 1) ≤ ⌈log₂ (M₀ + 1)⌉ · log 2`, from `M₀ + 1 ≤ 2 ^ ⌈log₂ (M₀ + 1)⌉`. -/
lemma log_succ_le_clog_mul_log_two (M₀ : ℕ) :
    Real.log ((M₀ : ℝ) + 1) ≤ (Nat.clog 2 (M₀ + 1) : ℝ) * Real.log 2 := by
  have h : ((M₀ + 1 : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (M₀ + 1) : ℕ) : ℝ) :=
    by exact_mod_cast Nat.le_pow_clog (by norm_num) (M₀ + 1)
  push_cast at h
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h

/-- `⌈log₂ (M₀ + 1)⌉ · log 2 ≤ log (M₀ + 1) + log 2`, from `2 ^ (⌈log₂ (M₀ + 1)⌉ - 1) < M₀ + 1`
when `M₀ ≥ 1` (and `⌈log₂ 1⌉ = 0` when `M₀ = 0`). -/
lemma clog_mul_log_two_le (M₀ : ℕ) :
    (Nat.clog 2 (M₀ + 1) : ℝ) * Real.log 2 ≤ Real.log ((M₀ : ℝ) + 1) + Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos M₀ with h0 | hpos
  · subst h0; simp [hlog2.le]
  have hlt : ((2 ^ (Nat.clog 2 (M₀ + 1)).pred : ℕ) : ℝ) < ((M₀ + 1 : ℕ) : ℝ) :=
    by exact_mod_cast Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  push_cast at hlt
  have hlog := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow] at hlog
  have hc : (Nat.clog 2 (M₀ + 1) : ℝ) ≤ ((Nat.clog 2 (M₀ + 1)).pred : ℕ) + 1 := by
    exact_mod_cast Nat.le_succ_of_pred_le le_rfl
  nlinarith

/-- `Ψ_game` is at least the real bound `(Ψ + log (M₀ + 1)) / log 2 + 1`. The first part holds
because `Ψ / log 2 ≤ 2 ⌈Ψ⌉₊` (as `1 / 2 < log 2`, and `Ψ / log 2 < 0` when `Ψ < 0`); the second
is `log_succ_le_clog_mul_log_two`. -/
lemma alg2PsiGame_real_le (Ψ : ℝ) (M₀ : ℕ) :
    (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 + 1 ≤ alg2PsiGame Ψ M₀ := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2p : 0 < Real.log 2 := by linarith
  have hM := log_succ_le_clog_mul_log_two M₀
  have hΨ : Ψ ≤ 2 * (⌈Ψ⌉₊ : ℝ) * Real.log 2 := by
    rcases le_or_gt Ψ 0 with h | h
    · have : 0 ≤ 2 * (⌈Ψ⌉₊ : ℝ) * Real.log 2 := by positivity
      linarith
    · have hc : Ψ ≤ (⌈Ψ⌉₊ : ℝ) := Nat.le_ceil Ψ
      nlinarith
  unfold alg2PsiGame
  push_cast
  rw [div_add_one hlog2p.ne', div_le_iff₀ hlog2p]
  nlinarith

/-- `Ψ_game = O(Ψ + log M₀)`: `⌈Ψ⌉₊ ≤ max 0 Ψ + 1`, and `⌈log₂ (M₀ + 1)⌉ ≤ log₂ (M₀ + 1) + 1`
(`clog_mul_log_two_le`). -/
lemma alg2PsiGame_le (Ψ : ℝ) (M₀ : ℕ) :
    alg2PsiGame Ψ M₀ ≤ 2 * max 0 Ψ + Real.log ((M₀ : ℝ) + 1) / Real.log 2 + 4 := by
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (⌈Ψ⌉₊ : ℝ) ≤ max 0 Ψ + 1 := by
    rcases le_or_gt Ψ 0 with h | h
    · rw [Nat.ceil_eq_zero.mpr h]; push_cast
      linarith [le_max_left 0 Ψ]
    · exact (Nat.ceil_lt_add_one h.le).le.trans (by linarith [le_max_right 0 Ψ])
  have hM : (Nat.clog 2 (M₀ + 1) : ℝ) ≤ Real.log ((M₀ : ℝ) + 1) / Real.log 2 + 1 := by
    rw [div_add_one hlog2p.ne', le_div_iff₀ hlog2p]
    exact clog_mul_log_two_le M₀
  unfold alg2PsiGame
  push_cast
  linarith

end MinCostFlow.Chain
