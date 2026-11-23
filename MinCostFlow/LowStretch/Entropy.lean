module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

/-!
# The entropy potential

The stretch bound adds up, over all petals, terms `v · log₂(V / v)`, where `v` is the volume of a
petal and `V` that of its cluster. We bound the sum with the potential `F(x) = x · log₂(x / κ)`:
when parts `x_i ≥ κ` add up to at most `S`, then `∑ x_i log₂(S / x_i) ≤ F(S) - ∑ F(x_i)`. The
potential telescopes from a cluster to its children. When a child is larger than its part, we pay
`F(b) - F(a) ≤ (b - a)(log₂(b / κ) + 2)`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Real

/-- The entropy potential. -/
noncomputable def Fe (κ x : ℝ) : ℝ := x * logb 2 (x / κ)

variable {κ : ℝ}

theorem logb_nonneg_of_le (hκ : 0 < κ) {x : ℝ} (hx : κ ≤ x) : 0 ≤ logb 2 (x / κ) := by
  apply logb_nonneg (by norm_num)
  rw [le_div_iff₀ hκ]; linarith

theorem Fe_nonneg (hκ : 0 < κ) {x : ℝ} (hx : κ ≤ x) : 0 ≤ Fe κ x :=
  mul_nonneg (by linarith) (logb_nonneg_of_le hκ hx)

theorem Fe_mono (hκ : 0 < κ) {a b : ℝ} (ha : κ ≤ a) (hab : a ≤ b) : Fe κ a ≤ Fe κ b := by
  unfold Fe
  have h1 := logb_nonneg_of_le hκ ha
  have hapos : 0 < a := by linarith
  have h2 : logb 2 (a / κ) ≤ logb 2 (b / κ) := by
    apply logb_le_logb_of_le (by norm_num) (div_pos hapos hκ)
    exact div_le_div_of_nonneg_right hab hκ.le
  calc a * logb 2 (a / κ) ≤ b * logb 2 (a / κ) := mul_le_mul_of_nonneg_right hab h1
    _ ≤ b * logb 2 (b / κ) := mul_le_mul_of_nonneg_left h2 (by linarith)

theorem one_div_log_two_lt_two : 1 / log 2 < 2 := by
  have := Real.log_two_gt_d9
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- `F(b) - F(a) ≤ (b - a)(log₂(b / κ) + 2)`. -/
theorem Fe_sub_le (hκ : 0 < κ) {a b : ℝ} (ha : κ ≤ a) (hab : a ≤ b) :
    Fe κ b - Fe κ a ≤ (b - a) * (logb 2 (b / κ) + 2) := by
  unfold Fe
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have e : logb 2 (a / κ) = logb 2 (b / κ) - logb 2 (b / a) := by
    rw [← logb_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [e]
  have h1 : logb 2 (b / a) ≤ (b / a - 1) / log 2 := by
    unfold logb
    have := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
    exact div_le_div_of_nonneg_right this (by positivity)
  have h2 : a * ((b / a - 1) / log 2) = (b - a) * (1 / log 2) := by
    field_simp
  have h3 := one_div_log_two_lt_two
  have h4 : 0 ≤ b - a := by linarith
  have h5 : a * logb 2 (b / a) ≤ (b - a) * 2 := by
    calc a * logb 2 (b / a) ≤ a * ((b / a - 1) / log 2) := mul_le_mul_of_nonneg_left h1 hapos.le
      _ = (b - a) * (1 / log 2) := h2
      _ ≤ (b - a) * 2 := mul_le_mul_of_nonneg_left h3.le h4
  nlinarith

/-- The entropy inequality: parts `x_i ≥ κ` with sum at most `S` have
`∑ x_i log₂(S / x_i) ≤ F(S) - ∑ F(x_i)`. -/
theorem entropy_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hκ : 0 < κ) (hx : ∀ i ∈ s, κ ≤ x i)
    {S : ℝ} (hS : ∑ i ∈ s, x i ≤ S) (hSκ : κ ≤ S) :
    ∑ i ∈ s, x i * logb 2 (S / x i) ≤ Fe κ S - ∑ i ∈ s, Fe κ (x i) := by
  have e : ∀ i ∈ s, x i * logb 2 (S / x i) = x i * logb 2 (S / κ) - Fe κ (x i) := by
    intro i hi
    unfold Fe
    have hxi : 0 < x i := by linarith [hx i hi]
    have hS : 0 < S := by linarith
    rw [← mul_sub, ← logb_div (div_pos hS hκ).ne' (div_pos hxi hκ).ne']
    congr 2
    field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have := logb_nonneg_of_le hκ hSκ
  unfold Fe
  nlinarith

end MinCostFlow.LowStretch
