module

public import MinCostFlow.Num.DyadicRoundingFacts
import Mathlib.Tactic

/-!
# Fixed-point updates for Lemma 5.5 (page 18)

Round the stretch up and the weight increment down. With a grid at least
twice as fine as the inverse update scale, the increment retains at least
half of its unrounded value.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

/-- Round a stretch up to the grid of spacing `2⁻ᴾ`. -/
noncomputable def roundStretch (P : ℕ) (s : ℝ) : ℝ :=
  -Num.dyadicFloor P (-s)

/-- The stored stretch overestimates the input by at most one grid unit. -/
theorem roundStretch_bounds (P : ℕ) (s : ℝ) :
    s ≤ roundStretch P s ∧ roundStretch P s ≤ s + 1 / (2 : ℝ)^P := by
  have hlo := Num.dyadicFloor_le P (-s)
  have herr := (abs_le.mp (Num.dyadicFloor_error P (-s))).1
  unfold roundStretch
  constructor <;> linarith

/-- Update by adding the rounded product of the weight and scaled stretch. -/
noncomputable def updateWeight (P : ℕ) (ρ v s : ℝ) : ℝ :=
  v + Num.dyadicFloor P (v * (s / ρ))

/-- A rounded update keeps at least half the desired increase. -/
theorem updateWeight_bounds (P : ℕ) {ρ v s : ℝ}
    (hρ : 0 < ρ) (hv : 1 ≤ v) (hs : 1 ≤ s)
    (hP : 2 * ρ ≤ (2 : ℝ)^P) :
    v * (1 + (s / ρ) / 2) ≤ updateWeight P ρ v s ∧
      updateWeight P ρ v s ≤ v * (1 + s / ρ) := by
  have hscale : (0 : ℝ) < (2 : ℝ)^P := by positivity
  have hgrid : 1 / (2 : ℝ)^P ≤ 1 / (2 * ρ) :=
    one_div_le_one_div_of_le (by positivity) hP
  have hvs : 1 ≤ v * s := one_le_mul_of_one_le_of_one_le hv hs
  have hhalf : 1 / (2 * ρ) ≤ v * (s / ρ) / 2 := by
    calc
      _ ≤ (v * s) / (2 * ρ) := div_le_div_of_nonneg_right hvs (by positivity)
      _ = _ := by ring
  have herr := (abs_le.mp (Num.dyadicFloor_error P (v * (s / ρ)))).1
  have hfloor := Num.dyadicFloor_le P (v * (s / ρ))
  unfold updateWeight
  constructor
  · linarith only [herr, hgrid.trans hhalf,
      show v * (1 + (s / ρ) / 2) = v + v * (s / ρ) / 2 by ring]
  · linarith only [hfloor, show v * (1 + s / ρ) = v + v * (s / ρ) by ring]

/-- When the update starts on the grid, it stays on the grid. -/
theorem updateWeight_onGrid (P : ℕ) (ρ s : ℝ) (a : ℤ) :
    ∃ b : ℤ, updateWeight P ρ ((a : ℝ) / (2 : ℝ)^P) s = (b : ℝ) / (2 : ℝ)^P := by
  refine ⟨a + ⌊((a : ℝ) / (2 : ℝ)^P * (s / ρ)) * (2 : ℝ)^P⌋, ?_⟩
  simp only [updateWeight, Num.dyadicFloor, Int.cast_add, add_div]

end MinCostFlow.LastLevelProgram
