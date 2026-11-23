module

public import MinCostFlow.LastLevelProgram.QueryFit
public import MinCostFlow.LastLevelProgram.StretchEncoding
import Mathlib.Tactic

/-!
# A common format for the last-level rebuild

The input lengths and rounded weights can share the finer of their
grids. Choose a signed width that also holds the stretch ceiling for
the collection of Definition 5.8 (pages 19–20).
-/

public section

namespace MinCostFlow.LastLevelProgram

open Num SparseCore

/-- Given input lengths at precision `P₀`, a common precision and width
can hold all input lengths, every queried weight, and the stretch bound. -/
theorem exists_lastLevelFormat (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (P₀ : ℕ)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hgrid : ∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P₀) :
    ∃ P L : ℕ, 1 ≤ L ∧ P₀ ≤ P ∧ weightPrecision C (representativeGraph G ℓ) ≤ P ∧
      (∀ e ∈ G.E, ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P) ∧
      (∀ e ∈ G.E, Fits 1 L (queryNumerator P (ℓ e))) ∧
      2 * (2 : ℝ)^P * (2 * ((representativeGraph G ℓ).m : ℝ)) < capacity 1 L ∧
      2 * (2 : ℝ)^P * (lastLevelParams (128 * max 1 C)).σ_last G.n < capacity 1 L := by
  let H := representativeGraph G ℓ
  let P := max P₀ (weightPrecision C H)
  let A := G.E.sup (fun e => ⌈ℓ e⌉₊)
  let S := (lastLevelParams (128 * max 1 C)).σ_last G.n
  let B := max (A : ℝ) (max (2 * (H.m : ℝ)) S)
  obtain ⟨L, hL, hwide⟩ := exists_queryWidth P B
  have hprec : P₀ ≤ P := le_max_left _ _
  have hgrid' (e : ℕ) (he : e ∈ G.E) :
      ∃ a : ℤ, ℓ e = (a : ℝ) / (2 : ℝ)^P := queryGrid_mono hprec (hgrid e he)
  have hfactor : 0 ≤ 2 * (2 : ℝ)^P := by positivity
  have hbound {x : ℝ} (hx : x ≤ B) : 2 * (2 : ℝ)^P * x < capacity 1 L :=
    (mul_le_mul_of_nonneg_left hx hfactor).trans_lt hwide
  refine ⟨P, L, hL, hprec, le_max_right _ _, hgrid', ?_,
    hbound ((le_max_left _ _).trans (le_max_right _ _)),
    hbound ((le_max_right _ _).trans (le_max_right _ _))⟩
  intro e he
  have hA : (⌈ℓ e⌉₊ : ℕ) ≤ A :=
    Finset.le_sup (f := fun e => ⌈ℓ e⌉₊) he
  have hℓA : ℓ e ≤ (A : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hA)
  exact (queryNumerator_fits (hpos e he) hℓA (hbound (le_max_left _ _)) (hgrid' e he)).2

/-- The selected width also suffices for stretch estimates on the
coarser grid used by the model. The layout precision may differ. -/
theorem selectedWidth_stretchEncoding {L P P₀ F : ℕ} {s B : ℝ}
    (hprec : P₀ ≤ P) (hs : 1 ≤ s) (hB : roundStretch P₀ s ≤ B)
    (hwide : 2 * (2 : ℝ)^P * B < capacity 1 L) :
    ∃ a d : ℤ, Fits 1 L a ∧ Fits 1 L d ∧ 0 < d ∧
      ((a : ℝ) / (2 : ℝ)^F) / ((d : ℝ) / (2 : ℝ)^F) = roundStretch P₀ s := by
  have hB0 : 0 ≤ B := zero_le_one.trans (hs.trans ((roundStretch_bounds P₀ s).1.trans hB))
  have hpow : (2 : ℝ)^P₀ ≤ (2 : ℝ)^P := pow_le_pow_right₀ (by norm_num) hprec
  have hwidth : 2 * (2 : ℝ)^P₀ * B < capacity 1 L :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow zero_le_two) hB0).trans_lt hwide
  exact roundStretch_encoding 1 L P₀ F hs hB hwidth

end MinCostFlow.LastLevelProgram
