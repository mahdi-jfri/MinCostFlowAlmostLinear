module

public import MinCostFlow.LastLevelProgram.Rounding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The rounded potential for Lemma 5.5 (page 18)

As in Appendix A.2, the sum of the weights grows by at most a fixed
factor per round. Each edge's own weight grows at least exponentially
in its accumulated stretch, with a smaller exponent to allow for rounding.
-/

public section

namespace MinCostFlow.LastLevelProgram

open scoped BigOperators

private lemma exp_quarter_le {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Real.exp (x / 4) ≤ 1 + x / 2 := by
  have hp : 0 < 1 - x / 4 := by linarith
  have he : 1 - x / 4 ≤ Real.exp (-(x / 4)) := by
    linarith [Real.add_one_le_exp (-(x / 4))]
  have hi := inv_anti₀ hp he
  rw [Real.exp_neg, inv_inv] at hi
  apply hi.trans
  rw [inv_eq_one_div, div_le_iff₀ hp]
  nlinarith [mul_nonneg hx (show 0 ≤ 1 - x by linarith)]

/-- A weighted stretch bound controls the total weight after one round. -/
theorem sum_update_le (E : Finset ℕ) (P : ℕ) {ρ W : ℝ} {v s : ℕ → ℝ}
    (hρ : 0 < ρ) (hP : 2 * ρ ≤ (2 : ℝ)^P)
    (hv : ∀ e ∈ E, 1 ≤ v e) (hs : ∀ e ∈ E, 1 ≤ s e)
    (hmean : ∑ e ∈ E, v e * s e ≤ W * ∑ e ∈ E, v e) :
    ∑ e ∈ E, updateWeight P ρ (v e) (s e) ≤
      Real.exp (W / ρ) * ∑ e ∈ E, v e := by
  have hsum : 0 ≤ ∑ e ∈ E, v e :=
    Finset.sum_nonneg fun e he => zero_le_one.trans (hv e he)
  calc
    _ ≤ ∑ e ∈ E, (v e + (v e * s e) / ρ) := by
      apply Finset.sum_le_sum
      intro e he
      convert (updateWeight_bounds P hρ (hv e he) (hs e he) hP).2 using 1; ring
    _ = (∑ e ∈ E, v e) + (∑ e ∈ E, v e * s e) / ρ := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (∑ e ∈ E, v e) + (W * ∑ e ∈ E, v e) / ρ :=
      add_le_add_right (div_le_div_of_nonneg_right hmean hρ.le) _
    _ = (W / ρ + 1) * ∑ e ∈ E, v e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) hsum

/-- Each edge contributes an exponential lower bound to the final potential. -/
theorem exp_sum_le_weight (P K : ℕ) {ρ : ℝ} {v s : ℕ → ℝ}
    (hρ : 0 < ρ) (hP : 2 * ρ ≤ (2 : ℝ)^P)
    (hinit : v 0 = 1) (hv : ∀ j < K, 1 ≤ v j)
    (hs : ∀ j < K, 1 ≤ s j ∧ s j ≤ ρ)
    (hstep : ∀ j < K, v (j + 1) = updateWeight P ρ (v j) (s j)) :
    Real.exp ((∑ j ∈ Finset.range K, s j) / (4 * ρ)) ≤ v K := by
  suffices bound : ∀ k ≤ K, Real.exp ((∑ j ∈ Finset.range k, s j) / (4 * ρ)) ≤ v k by
    exact bound K le_rfl
  intro k
  induction k with
  | zero => simp [hinit]
  | succ k ih =>
    intro hk
    have hk' : k < K := hk
    obtain ⟨hs₁, hs₂⟩ := hs k hk'
    have hx : 0 ≤ s k / ρ := div_nonneg (zero_le_one.trans hs₁) hρ.le
    have hx' : s k / ρ ≤ 1 := (div_le_one hρ).2 hs₂
    have hv₀ : 0 ≤ v k := zero_le_one.trans (hv k hk')
    rw [Finset.sum_range_succ, add_div, Real.exp_add, hstep k hk',
      show s k / (4 * ρ) = (s k / ρ) / 4 by ring]
    calc
      _ ≤ v k * (1 + (s k / ρ) / 2) :=
        mul_le_mul (ih hk'.le) (exp_quarter_le hx hx') (Real.exp_pos _).le hv₀
      _ ≤ _ := (updateWeight_bounds P hρ (hv k hk') hs₁ hP).1

end MinCostFlow.LastLevelProgram
