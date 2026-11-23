/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.SpannerToolImplBase

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subpolynomial Bounds and `Section8Static` Bridges for `SpannerToolImplProg`

Derives subpolynomial `exp(O(log^{7/8}))` parameter bounds and connects `spannerToolImpl_of_pathDS`
to `Section8Static.theorem_8_1_concrete` and `Section8Static.theorem_8_1_concrete_with_time`.
-/

namespace MinCostFlow.Expander

open WordRAM

public section

/-- `subpolyB1 C m` is dominated by `Real.exp (C' * Real.log (m + 2) ^ (7 / 8))`. -/
lemma subpolyB1_le_exp_rpow {C : ℝ} (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ m : ℕ, subpolyB1 C m ≤ Real.exp (C' * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) := by
  refine ⟨C * 24, mul_nonneg hC (by norm_num), fun m => ?_⟩
  dsimp only [subpolyB1]
  apply Real.exp_le_exp.mpr
  set y : ℝ := Real.log (↑m + 2)
  have hy : (1 / 2 : ℝ) ≤ y := half_le_log_add_two_nat m
  have hy_pos : 0 < y := by linarith
  have hy2_pos : 0 < y + 2 := by linarith
  have ha : (0 : ℝ) < 5 / 24 := by norm_num
  have hlog_rpow : (5 / 24 : ℝ) * Real.log (y + 2) ≤ (y + 2) ^ (5 / 24 : ℝ) := by
    rw [← Real.log_rpow hy2_pos]
    exact le_trans (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy2_pos _)) (sub_le_self _ zero_le_one)
  have hy2_le : y + 2 ≤ 5 * y := by linarith
  have hrpow_le : (y + 2) ^ (5 / 24 : ℝ) ≤ (5 * y) ^ (5 / 24 : ℝ) :=
    Real.rpow_le_rpow hy2_pos.le hy2_le ha.le
  have h5_rpow : (5 : ℝ) ^ (5 / 24 : ℝ) ≤ 5 := by
    calc (5 : ℝ) ^ (5 / 24 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 5 := Real.rpow_one 5
  have hlog_le : Real.log (y + 2) ≤ 24 * y ^ (5 / 24 : ℝ) := by
    have hmul : (5 * y) ^ (5 / 24 : ℝ) = (5 : ℝ) ^ (5 / 24 : ℝ) * y ^ (5 / 24 : ℝ) :=
      Real.mul_rpow (by norm_num) hy_pos.le
    nlinarith [Real.rpow_nonneg hy_pos.le (5 / 24 : ℝ)]
  have hcomb : y ^ (2 / 3 : ℝ) * Real.log (y + 2) ≤ 24 * y ^ (7 / 8 : ℝ) := by
    calc y ^ (2 / 3 : ℝ) * Real.log (y + 2)
        ≤ y ^ (2 / 3 : ℝ) * (24 * y ^ (5 / 24 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hy_pos.le _)
      _ = 24 * (y ^ (2 / 3 : ℝ) * y ^ (5 / 24 : ℝ)) := by ring
      _ = 24 * y ^ ((2 / 3 : ℝ) + 5 / 24) := by rw [← Real.rpow_add hy_pos]
      _ = 24 * y ^ (7 / 8 : ℝ) := by norm_num
  calc C * y ^ (2 / 3 : ℝ) * Real.log (y + 2)
      = C * (y ^ (2 / 3 : ℝ) * Real.log (y + 2)) := by ring
    _ ≤ C * (24 * y ^ (7 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hcomb hC
    _ = C * 24 * y ^ (7 / 8 : ℝ) := by ring

lemma decomposeCost_decFactor_le_exp_rpow
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ m : ℕ, (Spanner.spannerToolCosts_of_impl
        (spannerToolImpl_of_pathDS hDec pathDS)).decompose.decFactor m ≤
          Real.exp (C' * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C₀, hC₀, hEq⟩ := spannerToolCosts_decompose_decFactor_subpoly hDec pathDS
  obtain ⟨C', hC', hbd⟩ := subpolyB1_le_exp_rpow hC₀
  exact ⟨C', hC', fun m => by rw [hEq]; exact hbd m⟩

private lemma nat_log_two_le_two_mul_real_log {k M : ℕ} (hk : 1 ≤ k) (hk_le : (k : ℝ) ≤ (↑M + 2) ^ 2) :
    (Nat.log 2 k : ℝ) ≤ 4 * Real.log (↑M + 2) := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hpow : (2 : ℝ) ^ Nat.log 2 k ≤ (k : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_pow : Real.log ((2 : ℝ) ^ Nat.log 2 k) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog_pow
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by simpa using half_le_log_add_two_nat 0
  have hM2 : (0 : ℝ) < ↑M + 2 := by positivity
  have hlog_k : Real.log (k : ℝ) ≤ 2 * Real.log (↑M + 2) := by
    calc Real.log (k : ℝ) ≤ Real.log ((↑M + 2) ^ 2) := Real.log_le_log hk_pos hk_le
      _ = 2 * Real.log (↑M + 2) := by rw [Real.log_pow]; ring
  nlinarith

private lemma nat_log_two_poly_le {k M : ℕ} {K : ℝ} (hk : 1 ≤ k) (hK : 1 ≤ K)
    (hk_le : (k : ℝ) ≤ K * (↑M + 2) ^ 2) :
    (Nat.log 2 k : ℝ) ≤ (4 * Real.log K + 4) * Real.log (↑M + 2) := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hM2 : (0 : ℝ) < ↑M + 2 := by positivity
  have hpow : (2 : ℝ) ^ Nat.log 2 k ≤ (k : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_pow : Real.log ((2 : ℝ) ^ Nat.log 2 k) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog_pow
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by simpa using half_le_log_add_two_nat 0
  have hhalf : ↑(Nat.log 2 k) * (1 / 2 : ℝ) ≤ ↑(Nat.log 2 k) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
  have hlogM : (1 / 2 : ℝ) ≤ Real.log (↑M + 2) := half_le_log_add_two_nat M
  have hlogK_nn : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlog_k : Real.log (k : ℝ) ≤ Real.log (K * (↑M + 2) ^ 2) :=
    Real.log_le_log hk_pos hk_le
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog_k
  norm_num at hlog_k
  have h1 : Real.log K ≤ 2 * Real.log K * Real.log (↑M + 2) := by nlinarith
  linarith

private lemma capEta1_dec_le_mul_log (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    ∃ K_e1 : ℝ, 1 ≤ K_e1 ∧
      ∀ m : ℕ, (Spanner.capEta1 36 ((decomposeImplUsed hDec).φ_lb m) m : ℝ) + 1 / 2 ≤
        K_e1 * Real.log (↑m + 2) := by
  let C_phi := (decomposeImplUsed hDec).C_phi
  have hCphi1 : (1 : ℝ) ≤ C_phi := by exact_mod_cast (decomposeImplUsed hDec).hC_phi
  let K_poly : ℝ := 18 * C_phi + 2
  have hKpoly : 1 ≤ K_poly := by dsimp only [K_poly]; linarith
  let L_coef : ℝ := 4 * Real.log K_poly + 4
  have hL_nn : 0 ≤ L_coef := by
    have : 0 ≤ Real.log K_poly := Real.log_nonneg hKpoly
    dsimp only [L_coef]; linarith
  refine ⟨75 * L_coef + 150, by nlinarith, fun m => ?_⟩
  have hlogM : (1 / 2 : ℝ) ≤ Real.log (↑m + 2) := half_le_log_add_two_nat m
  have hphi_pos : 0 < (decomposeImplUsed hDec).φ_lb m := (decomposeImplUsed hDec).hφ_lb_pos m
  set arg : ℕ := Nat.ceil (36 * (m : ℝ) / (2 * (decomposeImplUsed hDec).φ_lb m)) + 1
  have harg1 : 1 ≤ arg := Nat.succ_le_succ (Nat.zero_le _)
  have hphi_le : 1 / (decomposeImplUsed hDec).φ_lb m ≤ (C_phi : ℝ) * (↑m + 2) := by
    rw [decomposeImpl_phi_lb_eq, one_div_one_div]
    exact_mod_cast (by simpa [decomposeImpl_c_phi] using (decomposeImplUsed hDec).hmaxPhiDen_le m :
      (decomposeImplUsed hDec).maxPhiDen m ≤ C_phi * (m + 2))
  have hdiv_le : 36 * (m : ℝ) / (2 * (decomposeImplUsed hDec).φ_lb m) ≤ 18 * (C_phi : ℝ) * (↑m + 2) ^ 2 := by
    have h1 : 36 * (m : ℝ) / (2 * (decomposeImplUsed hDec).φ_lb m) =
        18 * (m : ℝ) * (1 / (decomposeImplUsed hDec).φ_lb m) := by ring
    rw [h1]
    have hm_le : (m : ℝ) ≤ ↑m + 2 := by linarith
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h2 : 18 * (m : ℝ) * (1 / (decomposeImplUsed hDec).φ_lb m) ≤
        18 * (↑m + 2) * ((C_phi : ℝ) * (↑m + 2)) :=
      mul_le_mul (by linarith) hphi_le (by positivity) (by positivity)
    linarith [h2]
  have hceil_le : (arg : ℝ) ≤ K_poly * (↑m + 2) ^ 2 := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 36 * (m : ℝ) / (2 * (decomposeImplUsed hDec).φ_lb m) by
      positivity)
    have hM2_sq : (1 : ℝ) ≤ (↑m + 2) ^ 2 := by
      have : (2 : ℝ) ≤ ↑m + 2 := by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
      nlinarith
    have harg_eq : (arg : ℝ) = ↑(Nat.ceil (36 * (m : ℝ) / (2 * (decomposeImplUsed hDec).φ_lb m))) + 1 := by
      dsimp only [arg]; push_cast; rfl
    dsimp only [K_poly]
    nlinarith
  have hnat_log := nat_log_two_poly_le harg1 hKpoly hceil_le
  have hceil72 : Nat.ceil (2 * (36 : ℝ)) ≤ 72 := by
    apply Nat.ceil_le.mpr; norm_num
  have heta_eq : (Spanner.capEta1 36 ((decomposeImplUsed hDec).φ_lb m) m : ℝ) + 1 / 2 =
      3 / 2 + ↑(Nat.ceil (2 * (36 : ℝ))) * (↑(Nat.log 2 arg) + 1) := by
    dsimp only [Spanner.capEta1, arg]
    push_cast; ring
  rw [heta_eq]
  have hceil72_r : (Nat.ceil (2 * (36 : ℝ)) : ℝ) ≤ 72 := by exact_mod_cast hceil72
  have hnat_log_nn : (0 : ℝ) ≤ Nat.log 2 arg := Nat.cast_nonneg _
  have hmul_le : (Nat.ceil (2 * (36 : ℝ)) : ℝ) * (↑(Nat.log 2 arg) + 1) ≤
      72 * (L_coef * Real.log (↑m + 2) + 1) :=
    mul_le_mul hceil72_r (by linarith) (by positivity) (by norm_num)
  have hL_mul_nn : 0 ≤ L_coef * Real.log (↑m + 2) := mul_nonneg hL_nn (by linarith)
  calc 3 / 2 + ↑(Nat.ceil (2 * (36 : ℝ))) * (↑(Nat.log 2 arg) + 1)
      ≤ 3 / 2 + 72 * (L_coef * Real.log (↑m + 2) + 1) := add_le_add (le_refl _) hmul_le
    _ = 72 * (L_coef * Real.log (↑m + 2)) + 147 / 2 := by ring
    _ ≤ 75 * (L_coef * Real.log (↑m + 2)) + 150 * Real.log (↑m + 2) := by linarith [hL_mul_nn, hlogM]
    _ = (75 * L_coef + 150) * Real.log (↑m + 2) := by ring

private lemma capEta2_le_mul_log (m : ℕ) :
    (Spanner.capEta2 m : ℝ) + 1 / 2 ≤ 16 * Real.log (↑m + 2) := by
  have hlogM : (1 / 2 : ℝ) ≤ Real.log (↑m + 2) := half_le_log_add_two_nat m
  have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hm1_sq : ((m + 1 : ℕ) : ℝ) ≤ (↑m + 2) ^ 2 := by
    have : (1 : ℝ) ≤ ↑m + 2 := by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    push_cast; nlinarith
  have hlog2 := nat_log_two_le_two_mul_real_log hm1 hm1_sq
  have heta2 : (Spanner.capEta2 m : ℝ) + 1 / 2 = 3 / 2 + 2 * (↑(Nat.log 2 (m + 1)) + 1) := by
    dsimp only [Spanner.capEta2]; push_cast; ring
  rw [heta2]
  nlinarith

private lemma mul_log_le_exp_rpow {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    K * Real.log (↑m + 2) ≤ Real.exp ((2 * K + 3) * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) := by
  have hK_exp : K ≤ Real.exp (2 * K * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) :=
    nonneg_const_le_exp_rpow hK (by norm_num) (by norm_num) m
  have hL_exp : Real.log (↑m + 2) ≤ Real.exp (3 * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) :=
    log_add_two_le_exp_rpow (by norm_num) (by norm_num) m
  have hL_nn : 0 ≤ Real.log (↑m + 2) := by linarith [half_le_log_add_two_nat m]
  calc K * Real.log (↑m + 2)
      ≤ Real.exp (2 * K * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (3 * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) :=
        mul_le_mul hK_exp hL_exp hL_nn (Real.exp_pos _).le
    _ = Real.exp ((2 * K + 3) * Real.log (↑m + 2) ^ (7 / 8 : ℝ)) := by
        rw [← Real.exp_add]; ring_nf

/-- Bridges subpolynomial `PathDS` recourse/stretch bounds (`exp(C_p * log^(7/8))`) directly to
the `γ_ℓ` and `γ_c` bounds in `Section8Static.theorem_8_1_concrete`. -/
theorem spannerToolImpl_capGamma_exp_bound
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl)
    {C_p : ℝ} (hCp : 0 ≤ C_p)
    (hPath : ∀ mMax : ℕ,
      Spanner.capGammaExpPath 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      Spanner.capGammaDel 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      1 / Spanner.capPhiDS 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ))) :
    ∃ C_γ : ℝ, 0 < C_γ ∧ ∀ mMax : ℕ,
      let tools := Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)
      let φ_min := (decomposeImplUsed hDec).φ_lb mMax
      Spanner.capGammaL 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      Spanner.capGammaC 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax + 1 ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨K_e1, hKe1, heta1⟩ := capEta1_dec_le_mul_log hDec
  let C_e1 : ℝ := 2 * K_e1 + 3
  let C_e2 : ℝ := 2 * 16 + 3
  let C_raw : ℝ := 4 + C_e1 + C_e2 + 6 * C_p
  let C_γ : ℝ := C_raw + 4
  refine ⟨C_γ, by dsimp only [C_γ, C_raw, C_e1, C_e2]; linarith, fun mMax => ?_⟩
  obtain ⟨hExp_ub, hDel_ub, hPhi_ub⟩ := hPath mMax
  set tools := Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)
  set φ_min := (decomposeImplUsed hDec).φ_lb mMax
  have hlog_nn : 0 ≤ Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) :=
    Real.rpow_nonneg (by linarith [half_le_log_add_two_nat mMax]) _
  have hExp_nn : 0 ≤ Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax := by
    dsimp only [Spanner.capGammaExpPath, tools, spannerTools_of_impl_pathDS, Spanner.pathDSTool_of_impl,
      Spanner.PathDSParams.γ_ExpPath]
    exact le_max_of_le_left (Nat.cast_nonneg _)
  have hExp_sq :
      Spanner.capGammaL 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ≤
        Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    dsimp only [Spanner.capGammaL]
    have h1 : Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 ≤
        Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := by
      refine pow_le_pow_left₀ hExp_nn ?_ 2
      dsimp only [tools, φ_min, spannerTools_of_impl_constructExpander, spannerTools_of_impl_pathDS]
      exact hExp_ub
    calc Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2
        ≤ Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := h1
      _ = Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
          rw [sq, ← Real.exp_add]; ring_nf
  have hL_ub :
      Spanner.capGammaL 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    refine le_trans hExp_sq (Real.exp_le_exp.mpr ?_)
    have : 2 * C_p ≤ C_γ := by dsimp only [C_γ, C_raw, C_e1, C_e2]; linarith
    exact mul_le_mul_of_nonneg_right this hlog_nn
  refine ⟨hL_ub, ?_⟩
  have h2_ub : (2 : ℝ) ≤ Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    simpa [show (2 : ℝ) * 2 = 4 by norm_num] using
      nonneg_const_le_exp_rpow (K := 2) (by norm_num) (a := 7 / 8) (by norm_num) (by norm_num) mMax
  have heta1_exp : (Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2 ≤
      Real.exp (C_e1 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
    le_trans (heta1 mMax) (mul_log_le_exp_rpow (by linarith) mMax)
  have heta2_exp : (Spanner.capEta2 mMax : ℝ) + 1 / 2 ≤
      Real.exp (C_e2 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
    le_trans (capEta2_le_mul_log mMax) (mul_log_le_exp_rpow (by norm_num) mMax)
  have hDel_nn : 0 ≤ Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax := by
    dsimp only [Spanner.capGammaDel, tools, spannerTools_of_impl_pathDS, Spanner.pathDSTool_of_impl,
      Spanner.PathDSParams.γ_del]
    exact le_max_of_le_left (Nat.cast_nonneg _)
  have hDel_sq :
      Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 ≤
        Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    have h1 : Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 ≤
        Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := by
      refine pow_le_pow_left₀ hDel_nn ?_ 2
      dsimp only [tools, φ_min, spannerTools_of_impl_constructExpander, spannerTools_of_impl_pathDS]
      exact hDel_ub
    calc _ ≤ Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := h1
      _ = Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
          rw [sq, ← Real.exp_add]; ring_nf
  have hPhi_sq :
      (1 / Spanner.capPhiDS 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax) ^ 2 ≤
        Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    have hphi_pos : 0 < Spanner.capPhiDS 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax := by
      dsimp only [Spanner.capPhiDS]
      exact lt_min (tools.pathDS.hφ_pos φ_min mMax ((decomposeImplUsed hDec).hφ_lb_pos mMax))
        (tools.pathDS.hφ_pos tools.constructExpander.φ_Const _ tools.constructExpander.hφ_pos)
    have h1 : (1 / Spanner.capPhiDS 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax) ^ 2 ≤
        Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      dsimp only [tools, φ_min, spannerTools_of_impl_constructExpander, spannerTools_of_impl_pathDS]
      exact hPhi_ub
    calc _ ≤ Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ^ 2 := h1
      _ = Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
          rw [sq, ← Real.exp_add]; ring_nf
  have hcapC_rw :
      Spanner.capGammaC 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax =
        2 * ((Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2) *
          ((Spanner.capEta2 mMax : ℝ) + 1 / 2) *
          Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 *
          Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 *
          (1 / Spanner.capPhiDS 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax) ^ 2 := by
    dsimp only [Spanner.capGammaC]; ring
  have hcapC_raw :
      Spanner.capGammaC 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ≤
        Real.exp (C_raw * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    rw [hcapC_rw]
    have hDel_nn : 0 ≤ Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 := by positivity
    have hExp_nn : 0 ≤ Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 := by positivity
    have h12 : 2 * ((Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2) ≤
        Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e1 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
      mul_le_mul h2_ub heta1_exp (by positivity) (by positivity)
    have h123 : 2 * ((Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2) * ((Spanner.capEta2 mMax : ℝ) + 1 / 2) ≤
        Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e1 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e2 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
      mul_le_mul h12 heta2_exp (by positivity) (by positivity)
    have h1234 :
        2 * ((Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2) * ((Spanner.capEta2 mMax : ℝ) + 1 / 2) *
          Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 ≤
        Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e1 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e2 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
      mul_le_mul h123 hExp_sq hExp_nn (by positivity)
    have h12345 :
        2 * ((Spanner.capEta1 36 φ_min mMax : ℝ) + 1 / 2) * ((Spanner.capEta2 mMax : ℝ) + 1 / 2) *
          Spanner.capGammaExpPath 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 *
          Spanner.capGammaDel 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax ^ 2 ≤
        Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e1 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_e2 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp ((2 * C_p) * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
      mul_le_mul h1234 hDel_sq hDel_nn (by positivity)
    have h123456 := mul_le_mul h12345 hPhi_sq (by positivity) (by positivity)
    refine le_trans h123456 (le_of_eq ?_)
    simp only [← Real.exp_add]
    congr 1
    dsimp only [C_raw]
    ring
  have h1_le_exp : (1 : ℝ) ≤ Real.exp (C_raw * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
    apply Real.one_le_exp
    have : 0 ≤ C_raw := by dsimp only [C_raw, C_e1, C_e2]; linarith
    exact mul_nonneg this hlog_nn
  calc Spanner.capGammaC 36 tools.constructExpander.φ_Const tools.pathDS φ_min mMax + 1
      ≤ 2 * Real.exp (C_raw * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by linarith
    _ ≤ Real.exp (4 * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) *
          Real.exp (C_raw * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_right h2_ub (Real.exp_pos _).le
    _ = Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
        rw [← Real.exp_add]; congr 1; dsimp only [C_γ]; ring

/-- Consumer regime predicate for a `PathDSParams` parameter `f : ℕ → ℕ → ℕ`:
`f d M ≤ exp(C · log(M + 2)^{7/8})` holds (1) at `Decompose` scales
`1 ≤ d ≤ C₁ * subpolyB1 C₀ M + 1` and (2) at `ConstructExpander`'s constant scale
`1 ≤ d ≤ ⌈1 / constructExpanderImpl.φ_Const⌉₊`.

Using global bounds over all `d ≥ 1` would be unsatisfiable because
`d ≤ phiOutDen d M ≤ gExp d M`. -/
@[expose] def ConsumerSubpolyAtRegimes (f : ℕ → ℕ → ℕ) : Prop :=
  (∀ C₀ C₁ : ℝ, 0 < C₀ → 0 < C₁ →
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ C₁ * subpolyB1 C₀ M + 1 →
      (f d M : ℝ) ≤ Real.exp (C_p * Real.log (↑M + 2) ^ (7 / 8 : ℝ))) ∧
  (∃ C_p : ℝ, 0 < C_p ∧ ∀ d M : ℕ, 1 ≤ d →
    d ≤ Nat.ceil (1 / constructExpanderImpl.φ_Const) →
    (f d M : ℝ) ≤ Real.exp (C_p * Real.log (↑M + 2) ^ (7 / 8 : ℝ)))

private lemma eval_at_cap_of_regimes
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

private lemma pathDS_subpoly_of_params_bound
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl)
    (hphi : ConsumerSubpolyAtRegimes pathDS.params.phiOutDen)
    (hgExp : ConsumerSubpolyAtRegimes pathDS.params.gExp)
    (hgDel : ConsumerSubpolyAtRegimes pathDS.params.gDel) :
    ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ mMax : ℕ,
      Spanner.capGammaExpPath 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      Spanner.capGammaDel 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
      1 / Spanner.capPhiDS 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C_phi, hCphi, hphi_cap⟩ := eval_at_cap_of_regimes hDec hphi
  obtain ⟨C_exp, hCexp, hexp_cap⟩ := eval_at_cap_of_regimes hDec hgExp
  obtain ⟨C_del, hCdel, hdel_cap⟩ := eval_at_cap_of_regimes hDec hgDel
  set C_p : ℝ := max C_phi (max C_exp C_del)
  have hCp : 0 ≤ C_p := le_trans hCphi (le_max_left _ _)
  refine ⟨C_p, hCp, fun mMax => ?_⟩
  set φ_min := (decomposeImplUsed hDec).φ_lb mMax
  set φ_c := constructExpanderImpl.φ_Const
  have hφmin_pos : 0 < φ_min := (decomposeImplUsed hDec).hφ_lb_pos mMax
  have hφc_pos : 0 < φ_c := constructExpanderImpl.hφ_Const_pos
  have hd1 : 1 ≤ Nat.ceil (1 / Spanner.roundPhi φ_min) :=
    Nat.ceil_pos.mpr (one_div_pos.mpr (Spanner.roundPhi_pos hφmin_pos))
  have hd2 : 1 ≤ Nat.ceil (1 / Spanner.roundPhi φ_c) :=
    Nat.ceil_pos.mpr (one_div_pos.mpr (Spanner.roundPhi_pos hφc_pos))
  have hlog_nn : 0 ≤ Real.log (↑mMax + 2) ^ (7 / 8 : ℝ) :=
    Real.rpow_nonneg (by linarith [half_le_log_add_two_nat mMax]) _
  have up : ∀ {C x : ℝ}, C ≤ C_p → x ≤ Real.exp (C * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) →
      x ≤ Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := fun hC hx =>
    le_trans hx (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC hlog_nn))
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Spanner.capGammaExpPath, Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_ExpPath]
    exact max_le
      (up (le_trans (le_max_left _ _) (le_max_right _ _)) (hexp_cap mMax).1)
      (up (le_trans (le_max_left _ _) (le_max_right _ _)) (hexp_cap mMax).2)
  · dsimp only [Spanner.capGammaDel, Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_del]
    exact max_le
      (up (le_trans (le_max_right _ _) (le_max_right _ _)) (hdel_cap mMax).1)
      (up (le_trans (le_max_right _ _) (le_max_right _ _)) (hdel_cap mMax).2)
  · dsimp only [Spanner.capPhiDS, Spanner.pathDSTool_of_impl, Spanner.PathDSParams.φ_out]
    rw [one_div_le (lt_min
      (one_div_pos.mpr (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega)
        (le_trans (le_max_right _ _) (pathDS.params.hphiOutDen_ge _ mMax hd1)))))
      (one_div_pos.mpr (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega)
        (le_trans (le_max_right _ _) (pathDS.params.hphiOutDen_ge _ _ hd2))))))
      (Real.exp_pos _)]
    have h1 := up (le_max_left _ _) (hphi_cap mMax).1
    have h2 := up (le_max_left _ _) (hphi_cap mMax).2
    have hle1 : (1 : ℝ) / Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ≤
        1 / ↑(pathDS.params.phiOutDen ⌈1 / Spanner.roundPhi φ_min⌉₊ mMax) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega)
        (le_trans (le_max_right _ _) (pathDS.params.hphiOutDen_ge _ mMax hd1)))) h1
    have hle2 : (1 : ℝ) / Real.exp (C_p * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ≤
        1 / ↑(pathDS.params.phiOutDen ⌈1 / Spanner.roundPhi φ_c⌉₊ (Spanner.capM_W 36 φ_min mMax)) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega)
        (le_trans (le_max_right _ _) (pathDS.params.hphiOutDen_ge _ _ hd2)))) h2
    exact le_min hle1 hle2

/-- Full `Section8Static.theorem_8_1_concrete`-matching `DynSpanner.SparsifySpec` theorem
for `Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)` in the
`γ_query = γ_ExpPath` specialization under `ConsumerSubpolyAtRegimes` bounds and
`decFactor ≤ C_dec * capGammaL^2`. -/
theorem spannerToolImpl_theorem_8_1_of_dec_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl)
    {C_dec : ℝ} (hC_dec : 0 ≤ C_dec)
    (hphi : ConsumerSubpolyAtRegimes pathDS.params.phiOutDen)
    (hgExp : ConsumerSubpolyAtRegimes pathDS.params.gExp)
    (hgDel : ConsumerSubpolyAtRegimes pathDS.params.gDel)
    (hdec_le : ∀ mMax : ℕ, (decomposeImplUsed hDec).decFactor mMax ≤
      C_dec * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2)
    (hγq : ∀ φ M, 0 < φ →
      (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
        (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let sparsify := Spanner.sparsifyMG tools costs
    let params : ℕ → DynSpanner.SparsifyParams := fun mMax =>
      Spanner.sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_dec
    ∃ C_γ K_s K_t : ℝ,
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧
      0 ≤ K_t ∧
      ∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify := by
  obtain ⟨C_p, hCp, hPath⟩ :=
    pathDS_subpoly_of_params_bound hDec pathDS hphi hgExp hgDel
  obtain ⟨C_γ, hC_γ, hgam⟩ :=
    spannerToolImpl_capGamma_exp_bound hDec pathDS hCp hPath
  let impl := spannerToolImpl_of_pathDS hDec pathDS
  let costs := Spanner.spannerToolCosts_of_impl impl
  refine ⟨C_γ, 1 + 36 / Real.log 2,
    C_dec * (2 * impl.decompose.K_dec + 1) + Spanner.sparsifyBaseConst 36 costs + 4,
    hC_γ, rfl, ?_, ?_, fun mMax => ?_⟩
  · have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · have h1 := (Spanner.sparsifyMGParamsOfDec (Spanner.spannerTools_of_impl impl) costs
      ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb 0)
      ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos 0) 0 C_dec hC_dec).hK_t
    have hagr := (spannerToolImpl_sparsifyMGParamsOfDec_agree hDec pathDS 0 hC_dec).2.2.2
    linarith
  · obtain ⟨hKs, hps, hpt, hKt⟩ := spannerToolImpl_sparsifyMGParamsOfDec_agree hDec pathDS mMax hC_dec
    obtain ⟨hL, hC⟩ := hgam mMax
    have hL' : (Spanner.sparsifyMGParamsOfDec (Spanner.spannerTools_of_impl impl) costs
        ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb mMax)
        ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos mMax) mMax C_dec hC_dec).γ_ℓ ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
      dsimp only [Spanner.sparsifyMGParamsOfDec]
      rw [spannerTools_constructExpander_c_deg]
      exact hL
    have hC' : (Spanner.sparsifyMGParamsOfDec (Spanner.spannerTools_of_impl impl) costs
        ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb mMax)
        ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos mMax) mMax C_dec hC_dec).γ_c ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
      dsimp only [Spanner.sparsifyMGParamsOfDec]
      rw [spannerTools_constructExpander_c_deg]
      exact hC
    exact ⟨hKs, hps, hKt, hpt, hL', hC',
      spannerToolImpl_sparsifyMG_spec_of_dec_le hDec pathDS mMax hC_dec (hdec_le mMax) hγq⟩

/-- Full `Section8Static.theorem_8_1_concrete_with_time`-matching `DynSpanner.SparsifySpecWithTime`
theorem for `Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)` under
`ConsumerSubpolyAtRegimes` bounds, fallback `γ_t` query bound, and `decFactor ≤ C_dec * capGammaL^2`. -/
theorem spannerToolImpl_theorem_8_1_with_time_of_dec_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl)
    {C_dec C_q : ℝ} (hC_dec : 0 ≤ C_dec)
    (hphi : ConsumerSubpolyAtRegimes pathDS.params.phiOutDen)
    (hgExp : ConsumerSubpolyAtRegimes pathDS.params.gExp)
    (hgDel : ConsumerSubpolyAtRegimes pathDS.params.gDel)
    (hgQuery_bd : ∀ mMax : ℕ,
      Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
        Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ)))
    (hdec_le : ∀ mMax : ℕ, (decomposeImplUsed hDec).decFactor mMax ≤
      C_dec * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let sparsify := Spanner.sparsifyMG tools costs
    let params : ℕ → DynSpanner.SparsifyParams := fun mMax =>
      Spanner.sparsifyMGParamsOfDecWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_dec
    ∃ C_γ K_s K_t : ℝ,
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧
      0 ≤ K_t ∧
      ∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify := by
  obtain ⟨C_p, hCp, hPath⟩ :=
    pathDS_subpoly_of_params_bound hDec pathDS hphi hgExp hgDel
  obtain ⟨C_γ, hC_γ, hgam⟩ :=
    spannerToolImpl_capGamma_exp_bound hDec pathDS hCp hPath
  let impl := spannerToolImpl_of_pathDS hDec pathDS
  let costs := Spanner.spannerToolCosts_of_impl impl
  refine ⟨C_γ, 1 + 36 / Real.log 2,
    C_dec * (2 * impl.decompose.K_dec + 1) + Spanner.sparsifyBaseConst 36 costs + 4,
    hC_γ, rfl, ?_, ?_, fun mMax => ?_⟩
  · have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · have h1 := (Spanner.sparsifyMGParamsOfDecWithTime (Spanner.spannerTools_of_impl impl) costs
      ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb 0)
      ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos 0) 0 C_dec hC_dec).hK_t
    have hagr := (spannerToolImpl_sparsifyMGParamsOfDecWithTime_agree hDec pathDS 0 hC_dec).2.2.2.1
    linarith
  · obtain ⟨hKs, hps, hpt, hKt, hγt⟩ :=
      spannerToolImpl_sparsifyMGParamsOfDecWithTime_agree hDec pathDS mMax hC_dec
    obtain ⟨hL, hC⟩ := hgam mMax
    have hL' : (Spanner.sparsifyMGParamsOfDecWithTime (Spanner.spannerTools_of_impl impl) costs
        ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb mMax)
        ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos mMax) mMax C_dec hC_dec).γ_ℓ ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
      dsimp only [Spanner.sparsifyMGParamsOfDecWithTime, Spanner.sparsifyMGParamsOfDec]
      rw [spannerTools_constructExpander_c_deg]
      exact hL
    have hC' : (Spanner.sparsifyMGParamsOfDecWithTime (Spanner.spannerTools_of_impl impl) costs
        ((Spanner.decomposeMonotone_of_impl impl.decompose).φ_lb mMax)
        ((Spanner.decomposeMonotone_of_impl impl.decompose).hφ_lb_pos mMax) mMax C_dec hC_dec).γ_c ≤
        Real.exp (C_γ * Real.log (↑mMax + 2) ^ (7 / 8 : ℝ)) := by
      dsimp only [Spanner.sparsifyMGParamsOfDecWithTime, Spanner.sparsifyMGParamsOfDec]
      rw [spannerTools_constructExpander_c_deg]
      exact hC
    exact ⟨hKs, hps, hKt, hpt, hL', hC', hγt ▸ hgQuery_bd mMax,
      spannerToolImpl_sparsifyMG_spec_of_dec_le_with_time hDec pathDS mMax hC_dec (hdec_le mMax)⟩

end

end MinCostFlow.Expander
