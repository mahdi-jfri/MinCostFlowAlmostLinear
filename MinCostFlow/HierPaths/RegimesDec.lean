module

public import MinCostFlow.HierPaths.Params
public import MinCostFlow.Expander.SpannerToolImplProg

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `Γ` dominates the decomposition overhead when `a` is large

The chain also asks `decFactor mMax ≤ C_dec · capGammaL^2`, where the overhead of the expander
decomposition is `decFactor = subpolyB1 C₀ = exp(C₀ L^{2/3} log(L + 2))` with `L = log(M + 2)`
and a constant `C₀` that the cited decomposition provides (`decomposeImplUsed_decFactor_eq`).
Since `Γ` itself is `exp(Θ(a L^{2/3} log L))`, this needs the constant `a` of the construction
to be large compared to `C₀`. A larger `a` only weakens the bounds `U = 2^{a h v_x}`, so the
construction allows it.

`subpolyB1_le_gammaHP` proves `subpolyB1 C₀ M ≤ Γ` for `C₀ ≤ a`: we have
`Γ ≥ U_X^{2j+2} = 2^{a j v (2j + 2)}` with `v = ⌈log₂(X + 2)⌉`, and `L ≤ X ≤ j^3` gives
`L^{2/3} ≤ j^2`, `L + 2 ≤ 2^v` gives `log(L + 2) ≤ v`, and `j ≤ (2j + 2) log 2`.
`decFactor_le_capGammaL_sq_of_gExp_eq` is the bound of the chain, with `C_dec = 1`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Expander

private lemma bigUX_pow_le_gammaHP (a d M : ℕ) :
    2 ^ (a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2)) ≤ gammaHP a d M := by
  have hU : bigUX a M ^ (2 * bigJ M + 2) =
      2 ^ (a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2)) := by
    unfold bigUX; rw [← pow_mul]
  rw [← hU]
  unfold gammaHP
  have hA : 1 ≤ (bigJ M + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ 4 ^ (bigJ M + 1) := Nat.one_le_pow _ _ (by omega)
  have hC : 1 ≤ (bigKB M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hD : 1 ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc bigUX a M ^ (2 * bigJ M + 2) = 1 * 1 * 1 * 1 * 1 * bigUX a M ^ (2 * bigJ M + 2) := by ring
    _ ≤ _ := by gcongr; norm_num

/-- `subpolyB1 C₀ M ≤ Γ` when `C₀ ≤ a`. -/
theorem subpolyB1_le_gammaHP {C₀ : ℝ} {a : ℕ} (ha : C₀ ≤ a) (d M : ℕ) :
    subpolyB1 C₀ M ≤ gammaHP a d M := by
  set L := Real.log ((M : ℝ) + 2)
  have hL := half_le_log_add_two_nat M
  have hLpos : 0 < L := by linarith
  have hΓ : ((2 : ℝ) ^ (a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2))) ≤
      (gammaHP a d M : ℝ) := by
    exact_mod_cast bigUX_pow_le_gammaHP a d M
  have hX8 : 8 * M + 8 ≤ 2 ^ bigX M := Nat.le_pow_clog (by decide) _
  have hXj : bigX M ≤ bigJ M ^ 3 := le_ceilRoot_pow 2 (bigX M)
  have hXv : bigX M + 2 ≤ 2 ^ Nat.clog 2 (bigX M + 2) := Nat.le_pow_clog (by decide) _
  generalize gammaHP a d M = G at hΓ ⊢
  generalize Nat.clog 2 (bigX M + 2) = v at hΓ hXv
  generalize bigJ M = j at hΓ hXj
  generalize bigX M = X at hX8 hXj hXv
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  -- `L ≤ X`
  have hLX : L ≤ (X : ℝ) := by
    have h1 := hX8
    have h2 : ((M : ℝ) + 2) ≤ (2 : ℝ) ^ X := by
      have : ((8 * M + 8 : ℕ) : ℝ) ≤ ((2 ^ X : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hl2'.le hX0
    linarith
  -- `L^{2/3} ≤ j^2`
  have hj : L ^ (2 / 3 : ℝ) ≤ (j : ℝ) ^ 2 := by
    have h1 := hXj
    have h2 : L ≤ (j : ℝ) ^ 3 := le_trans hLX (by exact_mod_cast h1)
    have hjnn : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    calc L ^ (2 / 3 : ℝ) ≤ ((j : ℝ) ^ 3) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hLpos.le h2 (by norm_num)
      _ = (j : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hjnn, ← Real.rpow_natCast]; norm_num
  -- `log(L + 2) ≤ v`
  have hv : Real.log (L + 2) ≤ (v : ℝ) := by
    have h1 := hXv
    have h2 : L + 2 ≤ (2 : ℝ) ^ v := by
      have : ((X + 2 : ℕ) : ℝ) ≤ ((2 ^ v : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := Real.log_le_log (by linarith) h2
    rw [Real.log_pow] at h3
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hl2'.le hv0
    linarith
  have hjnn : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hvnn : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hann : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hlognn : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
  have hL23nn : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hexp : C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤
      Real.log 2 * ((a : ℝ) * j * v * (2 * j + 2)) := by
    have h1 : C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤ (a : ℝ) * (j : ℝ) ^ 2 * v := by
      have := mul_le_mul hj hv hlognn (by positivity)
      calc C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) = C₀ * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
            ring
        _ ≤ (a : ℝ) * ((j : ℝ) ^ 2 * v) := mul_le_mul ha this (by positivity) hann
        _ = (a : ℝ) * (j : ℝ) ^ 2 * v := by ring
    have h2 : (j : ℝ) ≤ Real.log 2 * (2 * j + 2) := by nlinarith
    have h3 : (a : ℝ) * (j : ℝ) ^ 2 * v ≤ (a : ℝ) * j * v * (Real.log 2 * (2 * j + 2)) := by
      have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (a : ℝ) * j * v by positivity)
      nlinarith
    nlinarith
  calc subpolyB1 C₀ M = Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := rfl
    _ ≤ Real.exp (Real.log 2 * ((a : ℝ) * j * v * (2 * j + 2))) := Real.exp_le_exp.mpr hexp
    _ = (2 : ℝ) ^ (a * j * v * (2 * j + 2)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]; push_cast; ring_nf
    _ ≤ (G : ℝ) := hΓ

/-- For `a` at least a constant that depends on the decomposition, the decomposition overhead is
at most `capGammaL^2` for any `PathDSImpl` whose `gExp` is `Γ`. -/
theorem decFactor_le_capGammaL_sq_of_gExp_eq (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∀ pathDS : Spanner.PathDSImpl,
      pathDS.params.gExp = gammaHP a → ∀ mMax : ℕ,
        (decomposeImplUsed hDec).decFactor mMax ≤
          1 * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
            (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2 := by
  obtain ⟨C₀, hC₀, hdec⟩ := decomposeImplUsed_decFactor_eq hDec
  refine ⟨Nat.ceil C₀, fun a ha pathDS hg mMax => ?_⟩
  have haR : C₀ ≤ (a : ℝ) := le_trans (Nat.le_ceil C₀) (by exact_mod_cast ha)
  rw [hdec, one_mul]
  set φ_min := (decomposeImplUsed hDec).φ_lb mMax
  set E := Spanner.capGammaExpPath 36 constructExpanderImpl.φ_Const
    (Spanner.pathDSTool_of_impl pathDS) φ_min mMax
  have hγ : subpolyB1 C₀ mMax ≤ E := by
    have h1 : subpolyB1 C₀ mMax ≤
        (gammaHP a (Nat.ceil (1 / Spanner.roundPhi φ_min)) mMax : ℝ) :=
      subpolyB1_le_gammaHP haR _ _
    refine le_trans h1 (le_of_eq_of_le ?_ (le_max_left _ _))
    dsimp only [Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_ExpPath]
    rw [hg]
  have hE1 : 1 ≤ E := le_trans (Real.one_le_exp (by
    have := half_le_log_add_two_nat mMax
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ Real.log (↑mMax + 2) + 2 by linarith)
    have h2 := Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log (↑mMax + 2) by linarith) (2 / 3 : ℝ)
    exact mul_nonneg (mul_nonneg hC₀ h2) h1)) hγ
  have hL : Spanner.capGammaL 36 constructExpanderImpl.φ_Const
      (Spanner.pathDSTool_of_impl pathDS) φ_min mMax ^ 2 = E ^ 4 := by
    dsimp only [Spanner.capGammaL, E]; ring
  rw [hL]
  calc subpolyB1 C₀ mMax ≤ E := hγ
    _ = E ^ 1 := (pow_one E).symm
    _ ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)

end MinCostFlow.HierPaths
