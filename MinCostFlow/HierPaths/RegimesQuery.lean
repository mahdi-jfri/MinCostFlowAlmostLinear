module

public import MinCostFlow.HierPaths.HierParams
public import MinCostFlow.HierPaths.Regimes
public import MinCostFlow.Expander.SpannerToolImplProg

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The query time bound of the chain for `Γ`

The chain bounds the time of one query by `capGammaQuery`, the larger of `γ_query` at the
decomposition conductance `φ_lb mMax` (with `M = mMax`) and at the constant conductance
`φ_Const` (with `M = capM_W 36 φ_lb mMax`, which is at most a constant times `(mMax + 2)^2`).
This file proves the bound
`capGammaQuery ≤ exp(C_q log(mMax + 2)^{8/9} log(log(mMax + 2) + 2)^{4/3})` for any `PathDSImpl`
whose `gQuery` is `Γ` (`capGammaQuery_bound_of_gQuery_eq`), in particular for `hierParams`
(`hierParams_capGammaQuery_bound`).

The proof has two steps. First, a function `f` with `ConsumerSubpolyAtRegimes f` is at most
`exp(C log(mMax + 2)^{7/8})` at both arguments (`regimes_eval_at_cap`): at the second one
because `log(capM_W + 2) ≤ L_K · log(mMax + 2)`. Second, `L^{7/8} ≤ 8 L^{8/9} log(L + 2)^{4/3}`
for `L ≥ 1/2` (`rpow78_le_rpow89_loglog`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Expander

/-- A function with `ConsumerSubpolyAtRegimes` is `exp(O(log(mMax + 2)^{7/8}))` at the two
arguments where the chain evaluates the path data structure parameters. -/
theorem regimes_eval_at_cap
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    {f : ℕ → ℕ → ℕ} (hf : ConsumerSubpolyAtRegimes f) :
    ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ mMax : ℕ,
      (f (Nat.ceil (1 / Spanner.roundPhi ((decomposeImplUsed hDec).φ_lb mMax))) mMax : ℝ) ≤
        Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      (f (Nat.ceil (1 / Spanner.roundPhi constructExpanderImpl.φ_Const))
          (Spanner.capM_W 36 ((decomposeImplUsed hDec).φ_lb mMax) mMax) : ℝ) ≤
        Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C₀_p, C₁_p, hC₀p, hC₁p, hphi_lb⟩ := decomposeImpl_phi_lb_subpoly hDec
  obtain ⟨C_d, hCd, hdec⟩ := hf.1 C₀_p C₁_p hC₀p (by linarith)
  obtain ⟨C_c, hCc, hcon⟩ := hf.2
  let C_phi := (decomposeImplUsed hDec).C_phi
  have hCphi1 : (1 : ℝ) ≤ C_phi := by exact_mod_cast (decomposeImplUsed hDec).hC_phi
  let K : ℝ := 36 * (C_phi : ℝ) + 4
  have hK1 : 1 ≤ K := by dsimp only [K]; linarith
  let L_K : ℝ := 2 * Real.log K + 2
  have hLK_nn : 0 ≤ L_K := by
    have : 0 ≤ Real.log K := Real.log_nonneg hK1
    dsimp only [L_K]; linarith
  let C_p : ℝ := max C_d (C_c * L_K ^ (7 / 8 : ℝ))
  have hCp : 0 ≤ C_p := le_trans hCd.le (le_max_left _ _)
  refine ⟨C_p, hCp, fun mMax => ?_⟩
  set φ_min := (decomposeImplUsed hDec).φ_lb mMax
  set φ_c := constructExpanderImpl.φ_Const
  have hφmin_pos : 0 < φ_min := (decomposeImplUsed hDec).hφ_lb_pos mMax
  have hφc_pos : 0 < φ_c := constructExpanderImpl.hφ_Const_pos
  have hd1_pos : 1 ≤ Nat.ceil (1 / Spanner.roundPhi φ_min) :=
    Nat.ceil_pos.mpr (one_div_pos.mpr (Spanner.roundPhi_pos hφmin_pos))
  have hd2_pos : 1 ≤ Nat.ceil (1 / Spanner.roundPhi φ_c) :=
    Nat.ceil_pos.mpr (one_div_pos.mpr (Spanner.roundPhi_pos hφc_pos))
  have hlogM : (1 / 2 : ℝ) ≤ Real.log (↑mMax + 2) := half_le_log_add_two_nat mMax
  have hlog_nn : 0 ≤ Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  refine ⟨?_, ?_⟩
  · have hd1_le : (Nat.ceil (1 / Spanner.roundPhi φ_min) : ℝ) ≤ C₁_p * subpolyB1 C₀_p mMax + 1 := by
      have hceil_eq : Nat.ceil (1 / Spanner.roundPhi φ_min) = Nat.ceil (1 / φ_min) := by
        dsimp only [Spanner.roundPhi]
        rw [one_div_one_div, Nat.ceil_natCast]
      rw [hceil_eq]
      have h1 : 1 / φ_min = ((decomposeImplUsed hDec).maxPhiDen mMax : ℝ) := by
        dsimp only [φ_min]
        rw [decomposeImpl_phi_lb_eq, one_div_one_div]
      rw [h1, Nat.ceil_natCast]
      linarith [hphi_lb mMax]
    refine le_trans (hdec mMax _ hd1_pos hd1_le) (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog_nn
  · have hd2_eq : Nat.ceil (1 / Spanner.roundPhi φ_c) = Nat.ceil (1 / φ_c) := by
      dsimp only [Spanner.roundPhi]
      rw [one_div_one_div, Nat.ceil_natCast]
    have hd2_le : Nat.ceil (1 / Spanner.roundPhi φ_c) ≤ Nat.ceil (1 / constructExpanderImpl.φ_Const) :=
      hd2_eq.le
    set M₂ := Spanner.capM_W 36 φ_min mMax
    have hphi_le : 1 / φ_min ≤ (C_phi : ℝ) * (↑mMax + 2) := by
      dsimp only [φ_min]
      rw [decomposeImpl_phi_lb_eq, one_div_one_div]
      exact_mod_cast (by simpa [decomposeImpl_c_phi] using (decomposeImplUsed hDec).hmaxPhiDen_le mMax :
        (decomposeImplUsed hDec).maxPhiDen mMax ≤ C_phi * (mMax + 2))
    have hMW_le : (M₂ : ℝ) + 2 ≤ K * (↑mMax + 2) ^ 2 := by
      dsimp only [M₂, Spanner.capM_W]
      have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 36 * (mMax : ℝ) / φ_min by positivity)
      have hmul : 36 * (mMax : ℝ) / φ_min ≤ 36 * (C_phi : ℝ) * (↑mMax + 2) ^ 2 := by
        rw [div_eq_mul_one_div]
        have hm_le : (mMax : ℝ) ≤ ↑mMax + 2 := by linarith
        have := mul_le_mul (by linarith : 36 * (mMax : ℝ) ≤ 36 * (↑mMax + 2)) hphi_le (by positivity) (by positivity)
        linarith
      have hM2_sq : (1 : ℝ) ≤ (↑mMax + 2) ^ 2 := by
        have : (2 : ℝ) ≤ ↑mMax + 2 := by linarith [show (0 : ℝ) ≤ mMax from Nat.cast_nonneg mMax]
        nlinarith
      push_cast
      dsimp only [K]
      nlinarith
    have hM2_pos : (0 : ℝ) < ↑M₂ + 2 := by positivity
    have hlog2_le : Real.log (↑M₂ + 2) ≤ L_K * Real.log (↑mMax + 2) := by
      have h1 := Real.log_le_log hM2_pos hMW_le
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
      norm_num at h1
      have hlogK_le : Real.log K ≤ 2 * Real.log K * Real.log (↑mMax + 2) := by
        have : 0 ≤ Real.log K := Real.log_nonneg hK1
        nlinarith
      dsimp only [L_K]
      linarith
    have hrpow : Real.log (↑M₂ + 2) ^ (7 / 8 : ℝ) ≤
        L_K ^ (7 / 8 : ℝ) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) := by
      have hnn2 : 0 ≤ Real.log (↑M₂ + 2) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ M₂ from Nat.cast_nonneg M₂])
      have h1 : Real.log (↑M₂ + 2) ^ (7 / 8 : ℝ) ≤ (L_K * Real.log (↑mMax + 2)) ^ (7 / 8 : ℝ) :=
        Real.rpow_le_rpow hnn2 hlog2_le (by norm_num)
      rw [Real.mul_rpow hLK_nn (by linarith)] at h1
      exact h1
    have hsub : C_c * Real.log (↑M₂ + 2) ^ (7 / 8 : ℝ) ≤ C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) := by
      have h1 : C_c * Real.log (↑M₂ + 2) ^ (7 / 8 : ℝ) ≤
          (C_c * L_K ^ (7 / 8 : ℝ)) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) := by
        calc C_c * Real.log (↑M₂ + 2) ^ (7 / 8 : ℝ)
            ≤ C_c * (L_K ^ (7 / 8 : ℝ) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
              mul_le_mul_of_nonneg_left hrpow hCc.le
          _ = (C_c * L_K ^ (7 / 8 : ℝ)) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) := by ring
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog_nn)
    exact le_trans (hcon _ M₂ hd2_pos hd2_le) (Real.exp_le_exp.mpr hsub)

private lemma rpow_one_third_ge_half' {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    (1 / 2 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hpow : ((1 / 2 : ℝ) ^ (3 : ℕ)) ≤ (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
    have h1 : (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [show ((1 / 2 : ℝ) ^ (3 : ℕ)) = 1 / 8 by norm_num]
  exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (Real.rpow_nonneg hxpos.le _) hpow

/-- `L^{7/8} ≤ 8 L^{8/9} log(L + 2)^{4/3}` for `L ≥ 1/2`: `L^{7/8} ≤ 2 L^{8/9}` since
`L^{1/72} ≥ 1/2`, and `log(L + 2)^{4/3} ≥ 1/4` since `log(L + 2) ≥ 1/2`. -/
lemma rpow78_le_rpow89_loglog (L : ℝ) (hL : (1 / 2 : ℝ) ≤ L) :
    L ^ (7 / 8 : ℝ) ≤ 8 * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have h172 : (1 / 2 : ℝ) ≤ L ^ (1 / 72 : ℝ) := by
    have hpow : ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ (L ^ (1 / 72 : ℝ)) ^ (72 : ℕ) := by
      have h1 : (L ^ (1 / 72 : ℝ)) ^ (72 : ℕ) = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
      have h2 : ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ (1 / 2 : ℝ) := by
        calc ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ ((1 / 2 : ℝ) ^ (1 : ℕ)) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by decide)
          _ = 1 / 2 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by decide : 72 ≠ 0) (Real.rpow_nonneg hLpos.le _) hpow
  have h78_89 : L ^ (7 / 8 : ℝ) ≤ 2 * L ^ (8 / 9 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left h172 (Real.rpow_nonneg hLpos.le (7 / 8 : ℝ))
    have hadd : L ^ (7 / 8 : ℝ) * L ^ (1 / 72 : ℝ) = L ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    linarith
  have hll_ge : (1 / 2 : ℝ) ≤ Real.log (L + 2) := by
    have h2 : (2 : ℝ) ≤ L + 2 := by linarith
    exact le_trans (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  have hllpos : 0 < Real.log (L + 2) := by linarith
  have hll43 : (1 / 4 : ℝ) ≤ Real.log (L + 2) ^ (4 / 3 : ℝ) := by
    have h1 := rpow_one_third_ge_half' hll_ge
    have hmul : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) :=
      mul_le_mul hll_ge h1 (by positivity) hllpos.le
    have hadd : Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) =
        Real.log (L + 2) ^ (4 / 3 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (Real.log (L + 2))]
      rw [← Real.rpow_add hllpos]; norm_num
    linarith
  have hmul := mul_le_mul h78_89 hll43 (by norm_num) (by positivity)
  linarith

/-- The query time bound of the chain for any `PathDSImpl` whose `gQuery` is `Γ`. -/
theorem capGammaQuery_bound_of_gQuery_eq
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (pathDS : Spanner.PathDSImpl) (a : ℕ)
    (hq : pathDS.params.gQuery = gammaHP a) :
    ∃ C_q : ℝ, 0 < C_q ∧ ∀ mMax : ℕ,
      Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
        Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ)) := by
  obtain ⟨C_p, hCp, hcap⟩ := regimes_eval_at_cap hDec (gammaHP_at_regimes a)
  refine ⟨8 * C_p + 1, by positivity, fun mMax => ?_⟩
  set L := Real.log (↑mMax + 2)
  have hL := half_le_log_add_two_nat mMax
  have hLpos : 0 < L := by linarith
  have hQ : 0 ≤ L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) := by
    have h1 := Real.rpow_nonneg hLpos.le (8 / 9 : ℝ)
    have h2 := Real.rpow_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ L + 2 by linarith)) (4 / 3 : ℝ)
    exact mul_nonneg h1 h2
  have hstep : C_p * L ^ (7 / 8 : ℝ) ≤
      (8 * C_p + 1) * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) := by
    have h := rpow78_le_rpow89_loglog L hL
    have h1 : C_p * L ^ (7 / 8 : ℝ) ≤ C_p * (8 * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h hCp
    have h2 : C_p * (8 * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) =
        (8 * C_p) * (L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) := by ring
    have h3 : (8 * C_p + 1) * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) =
        (8 * C_p + 1) * (L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) := by ring
    rw [h3]
    nlinarith
  dsimp only [Spanner.capGammaQuery, Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_query]
  rw [hq]
  exact max_le (le_trans (hcap mMax).1 (Real.exp_le_exp.mpr hstep))
    (le_trans (hcap mMax).2 (Real.exp_le_exp.mpr hstep))

/-- The query time bound of the chain for `hierParams`. -/
theorem hierParams_capGammaQuery_bound
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (pathDS : Spanner.PathDSImpl) (a : ℕ)
    {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq'}
    (hparams : pathDS.params = hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds
      cw hcw_pos boundsSpace initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq') :
    ∃ C_q : ℝ, 0 < C_q ∧ ∀ mMax : ℕ,
      Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
        Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ)) :=
  capGammaQuery_bound_of_gQuery_eq hDec pathDS a (by rw [hparams]; rfl)

/-- The three parameters of `hierParams` meet the regime bounds of the chain. -/
theorem hierParams_at_regimes (a : ℕ)
    {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq} :
    let p := hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds
      cw hcw_pos boundsSpace initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq
    ConsumerSubpolyAtRegimes p.phiOutDen ∧ ConsumerSubpolyAtRegimes p.gExp ∧
      ConsumerSubpolyAtRegimes p.gDel :=
  ⟨gammaHP_at_regimes a, gammaHP_at_regimes a, one_at_regimes⟩

end MinCostFlow.HierPaths
