module

public import MinCostFlow.DynSpanner.ComplexitySum

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The slack of `E_L` over the work of a step with `0 < j`

The budget of a step with `0 < j` in the sum of Lemma 5.9 is `sLen · E_L · Δ₁` times constants,
where `E_L = 3^{(L+1)(L+2)/2 + L + 2} γ_c^{L+1} γ_ℓ^{(L+1)(L+2)/2 + 2}` and `Δ₁ = Δ₀ + 1`. The work
of the program in such a step is at most a constant times `sLen · V (ℓ + 1)² γ_ℓ²`, where
`V = vcongBound(j - 1)` and `ℓ = lenBound(j - 1)`: one factor `ℓ + 1` more than the model's own
work, which comes from the log of the walk lengths in the translation of the sparsifier.

`vcong_len_sq_le` shows that `E_L Δ₁` covers this: `V_{j-1} (ℓ_{j-1} + 1) ≤ V_j` by the recursion
of the congestion bound (`vcongBound_step`), and `V_j γ_ℓ² (ℓ_{j-1} + 1) ≤ V_L γ_ℓ² (ℓ_L + 1) ≤ E_L Δ₁`
by monotonicity and `expFactor_bounds`. We also record `j ≤ ℓ_{j-1}` and
`ℓ_j = 3 γ_ℓ ℓ_{j-1}`, which turn the factors `j` and `ℓ_j` of the program into powers of `ℓ`.
-/

namespace MinCostFlow.DynSpanner

public section

/-- **The slack of `E_L`**: `V_{j-1} (ℓ_{j-1} + 1)² γ_ℓ² ≤ E_L Δ₁` for `1 ≤ j ≤ L`. -/
theorem vcong_len_sq_le {γ_c γ_ℓ : ℝ} (hc : 1 ≤ γ_c) (hl : 1 ≤ γ_ℓ) (L Δ j : ℕ)
    (hj : 1 ≤ j) (hjL : j ≤ L) :
    vcongBound γ_c γ_ℓ Δ (j - 1) * (lenBound γ_ℓ (j - 1) + 1) ^ 2 * γ_ℓ ^ 2 ≤
      3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) * γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) *
        ((Δ : ℝ) + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hEL, -, -⟩ := expFactor_bounds hc hl L Δ
  have hstep := vcongBound_step hc hl Δ (j - 1)
  rw [Nat.sub_add_cancel hj] at hstep
  set V := vcongBound γ_c γ_ℓ Δ (j - 1)
  set ℓ := lenBound γ_ℓ (j - 1)
  have hV0 : 0 ≤ V := vcongBound_nonneg (by linarith) (by linarith) Δ (j - 1)
  have hℓ1 : 1 ≤ ℓ := one_le_lenBound hl (j - 1)
  have h1 : V * (ℓ + 1) ≤ vcongBound γ_c γ_ℓ Δ j := by
    have : (ℓ + 1) * V ≤ γ_c * (ℓ + 1) * (V + 2 * V) := by
      have h0 : 0 ≤ (ℓ + 1) * V := by positivity
      nlinarith
    linarith
  have hVj : vcongBound γ_c γ_ℓ Δ j ≤ vcongBound γ_c γ_ℓ Δ L := vcongBound_mono hc hl Δ hjL
  have hℓL : ℓ ≤ lenBound γ_ℓ L := lenBound_mono hl (le_trans (Nat.sub_le j 1) hjL)
  have hγ2 : 0 ≤ γ_ℓ ^ 2 := by positivity
  have hVj0 : 0 ≤ vcongBound γ_c γ_ℓ Δ j := le_trans (by positivity) h1
  calc V * (ℓ + 1) ^ 2 * γ_ℓ ^ 2 = (V * (ℓ + 1)) * (γ_ℓ ^ 2 * (ℓ + 1)) := by ring
    _ ≤ vcongBound γ_c γ_ℓ Δ L * (γ_ℓ ^ 2 * (lenBound γ_ℓ L + 1)) := by
      apply mul_le_mul (le_trans h1 hVj) _ (by positivity) (le_trans hVj0 hVj)
      exact mul_le_mul_of_nonneg_left (by linarith) hγ2
    _ = vcongBound γ_c γ_ℓ Δ L * γ_ℓ ^ 2 * (lenBound γ_ℓ L + 1) := by ring
    _ ≤ _ := hEL

/-- The level is at most the length bound of the level below: `j ≤ ℓ_{j-1}`. -/
theorem le_lenBound_pred {γ_ℓ : ℝ} (hl : 1 ≤ γ_ℓ) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ≤ lenBound γ_ℓ (j - 1) := by
  unfold lenBound
  have h1 : j ≤ 3 ^ (j - 1) := by
    have : j - 1 < 3 ^ (j - 1) := Nat.lt_pow_self (by norm_num)
    omega
  have h2 : ((3 : ℕ) ^ (j - 1) : ℝ) = (3 : ℝ) ^ (j - 1) := by push_cast; ring
  have h3 : (j : ℝ) ≤ (3 : ℝ) ^ (j - 1) := by rw [← h2]; exact_mod_cast h1
  have h4 : (1 : ℝ) ≤ γ_ℓ ^ (j - 1 + 1) := one_le_pow₀ hl
  have h5 : (0 : ℝ) ≤ (3 : ℝ) ^ (j - 1) := by positivity
  nlinarith

/-- `ℓ_j = 3 γ_ℓ ℓ_{j-1}` for `1 ≤ j`. -/
theorem lenBound_succ_pred (γ_ℓ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    lenBound γ_ℓ j = 3 * γ_ℓ * lenBound γ_ℓ (j - 1) := by
  unfold lenBound
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end

end MinCostFlow.DynSpanner
