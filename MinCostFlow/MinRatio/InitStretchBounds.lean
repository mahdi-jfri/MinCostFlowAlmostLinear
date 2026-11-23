module

public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.Spanner.Runtime
import Mathlib.Tactic

/-!
# Scaled bounds for the sparse-core stretch

Convert bounds on the sparsifier parameters and logarithmic factor to
integer endpoints with one scale for both terms of the stretch maximum.
-/

public section
namespace MinCostFlow.MinRatio

/-- Two scaled bounds for the terms of the stretch maximum use the
maximum of their integer endpoints at the same scale. -/
theorem initSparseCoreStretch_maxScaledBounds
    {lower₁ upper₁ lower₂ upper₂ scale : ℕ} {value₁ value₂ : ℝ}
    (hs : 0 < scale)
    (hl₁ : (lower₁ : ℝ) / scale ≤ value₁) (hu₁ : value₁ ≤ (upper₁ : ℝ) / scale)
    (hl₂ : (lower₂ : ℝ) / scale ≤ value₂) (hu₂ : value₂ ≤ (upper₂ : ℝ) / scale) :
    (↑(max lower₁ lower₂) : ℝ) / scale ≤ max value₁ value₂ ∧
      max value₁ value₂ ≤ (↑(max upper₁ upper₂) : ℝ) / scale := by
  have hscale : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  constructor
  · rcases le_total lower₁ lower₂ with h | h
    · rw [max_eq_right h]
      exact hl₂.trans (le_max_right _ _)
    · rw [max_eq_left h]
      exact hl₁.trans (le_max_left _ _)
  · apply max_le
    · exact hu₁.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left upper₁ upper₂) hscale.le)
    · exact hu₂.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right upper₁ upper₂) hscale.le)

/-- Scaled bounds on the sparsifier stretch give integer numerators
for the first term of the sparse-core stretch maximum. -/
theorem initSparseCoreStretch_firstScaledBounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (lower upper scale : ℕ)
    (hl : (lower : ℝ) / scale ≤ (E.P_fn m).γ_ℓ)
    (hu : (E.P_fn m).γ_ℓ ≤ (upper : ℝ) / scale) :
    let factor := 3 ^ E.L
    let den := scale ^ (E.L + 1)
    ((factor * lower ^ (E.L + 1) : ℕ) : ℝ) / (den : ℝ) ≤
        SparseCore.coreE82Len E.L (E.P_fn m) ∧
      SparseCore.coreE82Len E.L (E.P_fn m) ≤
        ((factor * upper ^ (E.L + 1) : ℕ) : ℝ) / (den : ℝ) := by
  dsimp only
  push_cast
  unfold SparseCore.coreE82Len
  simp only [mul_div_assoc, ← div_pow]
  have hnonneg : 0 ≤ (E.P_fn m).γ_ℓ := (by norm_num : (0 : ℝ) ≤ 1).trans (E.P_fn m).hγ_ℓ
  exact ⟨mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hl _) (by positivity),
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hu _) (by positivity)⟩

/-- Scaled bounds on the three nonnegative factors give integer
numerators for the second term of the sparse-core stretch maximum. -/
theorem initSparseCoreStretch_secondScaledBounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (kl ku sl su ll lu scale : ℕ) (hs : 0 < scale)
    (hkl : (kl : ℝ) / scale ≤ (E.P_fn m).K_s)
    (hku : (E.P_fn m).K_s ≤ (ku : ℝ) / scale)
    (hsl : (sl : ℝ) / scale ≤ (E.P_fn m).γ_ℓ)
    (hsu : (E.P_fn m).γ_ℓ ≤ (su : ℝ) / scale)
    (hll : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m)
    (hlu : SparseCore.coreLambdaS (E.P_fn m) m ≤ (lu : ℝ) / scale) :
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let den := scale ^ 3
    let num := fun k s l : ℕ => 11 * (cap * k * s * l + 115 * den)
    let term := 11 * (((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
      SparseCore.coreLambdaS (E.P_fn m) m * (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) + 115)
    (num kl sl ll : ℝ) / (den : ℝ) ≤ term ∧ term ≤ (num ku su lu : ℝ) / (den : ℝ) := by
  dsimp only
  have hs' : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  have hmono {a b c d f g : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hf : 0 ≤ f)
      (hab : a ≤ b) (hcd : c ≤ d) (hfg : f ≤ g) : a * c * f ≤ b * d * g :=
    mul_le_mul (mul_le_mul hab hcd hc (ha.trans hab)) hfg hf
      (mul_nonneg (ha.trans hab) (hc.trans hcd))
  have he (k s l : ℕ) :
      (↑(11 * ((E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190) * k * s * l +
        115 * scale ^ 3) : ℕ) : ℝ) / (↑(scale ^ 3) : ℝ) =
      11 * (((E.L : ℝ) + 1) * ((k : ℝ) / scale) * ((s : ℝ) / scale) *
        ((l : ℝ) / scale) * (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) + 115) := by
    push_cast
    field_simp
  rw [he, he]
  have hlow := hmono (by positivity) (by positivity) (by positivity) hkl hsl hll
  have hhigh := hmono ((by positivity : 0 ≤ (kl : ℝ) / scale).trans hkl)
    ((by positivity : 0 ≤ (sl : ℝ) / scale).trans hsl)
    ((by positivity : 0 ≤ (ll : ℝ) / scale).trans hll) hku hsu hlu
  have hfactor : 0 ≤ (11 : ℝ) * ((E.L : ℝ) + 1) * (E.B_fn m : ℝ) *
      (2 * (E.d_fn m : ℝ) + 190) := by positivity
  constructor
  · convert add_le_add_right (mul_le_mul_of_nonneg_left hlow hfactor) (11 * 115 : ℝ) using 1 <;> ring
  · convert add_le_add_right (mul_le_mul_of_nonneg_left hhigh hfactor) (11 * 115 : ℝ) using 1 <;> ring

/-- Raise each denominator only to the larger power required by the two
stretch terms to obtain individual bounds at one common scale. -/
theorem initSparseCoreStretch_scaledTermBounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (kl ku sl su ll lu scale : ℕ) (hs : 0 < scale)
    (hkl : (kl : ℝ) / scale ≤ (E.P_fn m).K_s)
    (hku : (E.P_fn m).K_s ≤ (ku : ℝ) / scale)
    (hsl : (sl : ℝ) / scale ≤ (E.P_fn m).γ_ℓ)
    (hsu : (E.P_fn m).γ_ℓ ≤ (su : ℝ) / scale)
    (hll : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m)
    (hlu : SparseCore.coreLambdaS (E.P_fn m) m ≤ (lu : ℝ) / scale) :
    let power := max (E.L + 1) 3
    let den := scale ^ power
    let first := fun s : ℕ => 3 ^ E.L * s ^ (E.L + 1) * scale ^ (power - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (power - 3)
    let firstTerm := SparseCore.coreE82Len E.L (E.P_fn m)
    let secondTerm := 11 * (((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
      SparseCore.coreLambdaS (E.P_fn m) m * (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) + 115)
    (first sl : ℝ) / (den : ℝ) ≤ firstTerm ∧ firstTerm ≤ (first su : ℝ) / (den : ℝ) ∧
      (second kl sl ll : ℝ) / (den : ℝ) ≤ secondTerm ∧
      secondTerm ≤ (second ku su lu : ℝ) / (den : ℝ) := by
  dsimp only
  let power := max (E.L + 1) 3
  have hs' : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  have hscale (num j : ℕ) (hj : j ≤ power) :
      (↑(num * scale ^ (power - j)) : ℝ) / (↑(scale ^ power) : ℝ) =
        (num : ℝ) / (↑(scale ^ j) : ℝ) := by
    have hpow : (scale : ℝ) ^ power = (scale : ℝ) ^ j * (scale : ℝ) ^ (power - j) := by
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hj]
    push_cast
    rw [hpow]
    field_simp
  obtain ⟨hfl, hfu⟩ := initSparseCoreStretch_firstScaledBounds E m sl su scale hsl hsu
  obtain ⟨hsl', hsu'⟩ :=
    initSparseCoreStretch_secondScaledBounds E m kl ku sl su ll lu scale hs hkl hku hsl hsu hll hlu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hscale _ _ (le_max_left _ _)).le.trans hfl
  · exact hfu.trans (hscale _ _ (le_max_left _ _)).ge
  · exact (hscale _ _ (le_max_right _ _)).le.trans hsl'
  · exact hsu'.trans (hscale _ _ (le_max_right _ _)).ge

/-- Raise each denominator only to the larger power required by the two
stretch terms, then take the maximum of their scaled endpoints. -/
theorem initSparseCoreStretch_scaledBounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (kl ku sl su ll lu scale : ℕ) (hs : 0 < scale)
    (hkl : (kl : ℝ) / scale ≤ (E.P_fn m).K_s)
    (hku : (E.P_fn m).K_s ≤ (ku : ℝ) / scale)
    (hsl : (sl : ℝ) / scale ≤ (E.P_fn m).γ_ℓ)
    (hsu : (E.P_fn m).γ_ℓ ≤ (su : ℝ) / scale)
    (hll : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m)
    (hlu : SparseCore.coreLambdaS (E.P_fn m) m ≤ (lu : ℝ) / scale) :
    let power := max (E.L + 1) 3
    let den := scale ^ power
    let first := fun s : ℕ => 3 ^ E.L * s ^ (E.L + 1) * scale ^ (power - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (power - 3)
    (↑(max (first sl) (second kl sl ll)) : ℝ) / (den : ℝ) ≤ SparseCore.gammaLEnv E m ∧
      SparseCore.gammaLEnv E m ≤ (↑(max (first su) (second ku su lu)) : ℝ) / (den : ℝ) := by
  dsimp only
  obtain ⟨ha, hb, hc, hd⟩ :=
    initSparseCoreStretch_scaledTermBounds E m kl ku sl su ll lu scale hs hkl hku hsl hsu hll hlu
  unfold SparseCore.gammaLEnv
  exact initSparseCoreStretch_maxScaledBounds (pow_pos hs _) ha hb hc hd

/-- The Section 8 sparsifier coefficient is enclosed by dividing by
opposite endpoints of the positive logarithm of two. -/
theorem initSparsifierCoefficient_bounds {scale logLo logHi : ℕ} (coefficient : ℕ)
    (hs : 0 < (scale : ℝ)) (hp : 0 < logLo)
    (hlo : (logLo : ℝ) / scale ≤ Real.log 2)
    (hhi : Real.log 2 ≤ (logHi : ℝ) / scale) :
    let numerator := coefficient * scale
    1 + (numerator : ℝ) / logHi ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ 1 + (numerator : ℝ) / logLo := by
  dsimp only
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < (logLo : ℝ) / scale := div_pos (by exact_mod_cast hp) hs
  have he (n : ℕ) : ((coefficient * scale : ℕ) : ℝ) / n = coefficient / ((n : ℝ) / scale) := by
    push_cast
    rw [div_div_eq_mul_div]
  rw [he, he]
  exact ⟨add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg coefficient) hlog hhi) 1,
    add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg coefficient) hpos hlo) 1⟩

/-- The length factor used by the Section 8 sparsifier is the square of
the larger path bound. Squaring the scaled maximum endpoints preserves
the enclosure. -/
theorem initSparsifierLengthFactor_bounds
    (cDeg phiConst phiMin : ℝ) (paths : Spanner.PathDSTool) (M : ℕ)
    {scale lo₁ hi₁ lo₂ hi₂ : ℕ} (hs : 0 < (scale : ℝ))
    (hlo₁ : (lo₁ : ℝ) / scale ≤ paths.γ_ExpPath phiMin M)
    (hhi₁ : paths.γ_ExpPath phiMin M ≤ (hi₁ : ℝ) / scale)
    (hlo₂ : (lo₂ : ℝ) / scale ≤
      paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M))
    (hhi₂ : paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ≤ (hi₂ : ℝ) / scale) :
    (((max lo₁ lo₂) ^ 2 : ℕ) : ℝ) / (scale : ℝ) ^ 2 ≤
      Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤
        (((max hi₁ hi₂) ^ 2 : ℕ) : ℝ) / (scale : ℝ) ^ 2 := by
  have hl := max_le_max hlo₁ hlo₂
  have hu := max_le_max hhi₁ hhi₂
  rw [max_div_div_right hs.le, ← Nat.cast_max] at hl
  rw [max_div_div_right hs.le, ← Nat.cast_max] at hu
  have hn : 0 ≤ max (paths.γ_ExpPath phiMin M)
      (paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M)) :=
    (by positivity : 0 ≤ ((max lo₁ lo₂ : ℕ) : ℝ) / scale).trans hl
  unfold Spanner.capGammaL Spanner.capGammaExpPath
  have hpow :=
    And.intro (pow_le_pow_left₀ (by positivity) hl 2) (pow_le_pow_left₀ hn hu 2)
  simpa only [div_pow, Nat.cast_pow] using hpow

end MinCostFlow.MinRatio
