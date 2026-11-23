module

public import MinCostFlow.LastLevelProgram.CanonicalOracle
public import MinCostFlow.LastLevelProgram.FixedPoint
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Fit bounds for the last-level weight queries

At any round the sum invariant bounds each live weight by twice the
edge count. The weights already lie on a grid, which the common
precision of the length and weight arrays can refine exactly.
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num LSF
open scoped BigOperators

/-- Increasing fractional precision preserves values on the coarser grid. -/
theorem queryGrid_mono {P Q : ℕ} (hPQ : P ≤ Q) {x : ℝ}
    (hx : ∃ a : ℤ, x = (a : ℝ) / (2 : ℝ)^P) :
    ∃ b : ℤ, x = (b : ℝ) / (2 : ℝ)^Q := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a * (2 : ℤ)^(Q - P), ?_⟩
  have he : (2 : ℝ)^Q = (2 : ℝ)^P * (2 : ℝ)^(Q-P) := by
    rw [← pow_add, Nat.add_sub_of_le hPQ]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, he]
  field_simp

/-- A positive grid value below the stated bound fits in the chosen limbs. -/
theorem queryNumerator_fits {h L P : ℕ} {x B : ℝ} (hx : 0 < x) (hB : x ≤ B)
    (hwidth : 2 * (2 : ℝ)^P * B < capacity h L)
    (hgrid : ∃ a : ℤ, x = (a : ℝ) / (2 : ℝ)^P) :
    0 < queryNumerator P x ∧ Fits h L (queryNumerator P x) := by
  obtain ⟨a, ha⟩ := hgrid
  rw [ha, queryNumerator_grid]
  rw [ha] at hx hB
  have hscale : (0 : ℝ) < (2 : ℝ)^P := by positivity
  have hpos := (div_pos_iff_of_pos_right hscale).mp hx
  have haB := (div_le_iff₀ hscale).mp hB
  have hhi : 2 * (a : ℝ) < capacity h L := by nlinarith only [haB, hwidth]
  have hzero : (0 : ℝ) ≤ capacity h L := Nat.cast_nonneg _
  refine ⟨by exact_mod_cast hpos, ⟨?_, by exact_mod_cast hhi⟩⟩
  exact_mod_cast (show -(capacity h L : ℝ) ≤ 2 * (a : ℝ) by linarith)

/-- The prefix invariants and a width chosen once for the graph give both
weight premises of the canonical tree oracle at every round. -/
theorem roundWeights_fit (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L P j : ℕ)
    (hprecision : weightPrecision C G ≤ P)
    (hwidth : 2 * (2 : ℝ)^P * (2 * (G.m : ℝ)) < capacity 1 L) :
    let v := weights (weightPrecision C G) (roundedScale C G)
      (stretchQuery oracle G ℓ (weightPrecision C G)) j
    (∀ e ∈ G.E, 1 ≤ v e) →
    (∑ e ∈ G.E, v e) ≤ 2 * G.m →
    (∀ e ∈ G.E, 0 < queryNumerator P (v e) ∧ Fits 1 L (queryNumerator P (v e))) ∧
    (∀ e, ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P) := by
  intro v hv hsum
  have hgrid (e : ℕ) : ∃ a : ℤ, v e = (a : ℝ) / (2 : ℝ)^P :=
    queryGrid_mono hprecision (weights_onGrid _ _ _ _ e)
  refine ⟨fun e he => queryNumerator_fits (zero_lt_one.trans_le (hv e he)) ?_ hwidth (hgrid e), hgrid⟩
  exact (Finset.single_le_sum (fun f hf => zero_le_one.trans (hv f hf)) he).trans hsum

/-- There is a positive limb count meeting a common bound on all positive
numerators at the chosen precision. -/
theorem exists_queryWidth (P : ℕ) (B : ℝ) :
    ∃ L : ℕ, 1 ≤ L ∧ 2 * (2 : ℝ)^P * B < capacity 1 L := by
  let N := ⌈2 * (2 : ℝ)^P * B⌉₊
  let L := max 1 N.size
  refine ⟨L, le_max_left _ _, ?_⟩
  have hN : N < 2^L :=
    (Nat.lt_size_self N).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hreal : 2 * (2 : ℝ)^P * B < ((2^L : ℕ) : ℝ) :=
    (show 2 * (2 : ℝ)^P * B ≤ (N : ℝ) from Nat.le_ceil _).trans_lt
      (by exact_mod_cast hN)
  simpa only [capacity, base, pow_one] using hreal

end MinCostFlow.LastLevelProgram
