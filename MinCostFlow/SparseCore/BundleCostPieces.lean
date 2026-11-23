module

public import MinCostFlow.SparseCore.BundleCoreParams
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Piecewise Algebraic Bounds for the Bundle Runtime Envelope

This file proves the piece-by-piece algebraic comparisons used by `BundleCostEnv.lean` to relate
the per-branch cost bound of `bundleRunSeq` (and of a single restart) to `bundleCoreParams E`:
* `bundleEnv_core_bounds`: basic comparisons between `bundleUCRatio`, `bundleRecoursePerQ`,
  `bundleRecEnv`, and `bundleCostMult`.
* `bundleCost_piece2a`, `bundleCost_piece2b`, `bundleCost_piece34`, `bundleCost_piece5_split`,
  and `bundleCost_piece5`: bounds on initialization, input/bundle/output batches, and
  dynamic-spanner work, with the bundle degree factor `((k : ℝ) + 1)` kept outside `γ_r`.
* `bundleLambda_le_logMN`: bounds `bundleLambda` by `7^p · log(m₀ + n₀ + 2)^p`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

lemma bundleEnv_core_bounds (E : SparseCoreEnv) (m₀ n₀ actCard : ℕ)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (hcn : (n₀ : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1)) :
    let P_b := E.P_fn m₀
    (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤ bundleRecEnv E m₀ ∧
    (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
      P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ ≤ bundleRecEnv E m₀ ∧
    bundleUCRatio n₀ ≤ bundleUCRatioHi E m₀ ∧
    bundleRecoursePerQ E.L P_b m₀ n₀ actCard ≤ bundleRecEnv E m₀ ∧
    3 + P_b.γ_ℓ ≤ bundleRecEnv E m₀ ∧
    ((E.L : ℝ) + 1) ≤ bundleCostMult E m₀ := by
  intro P_b
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ bundleUCRatioHi E m₀ := bundleUCRatioHi_ge_one E m₀
  have hLen3 : 3 ≤ coreE82Len E.L P_b := coreE82Len_ge_three E.L E.hL P_b
  have hnr1 : 1 ≤ bundleNRoot E.L m₀ := bundleParams_nRoot_ge_one E.L m₀
  have hUH2 : 2 ≤ bundleBucketRecUH E.L P_b m₀ := by
    unfold bundleBucketRecUH
    have := P_b.hK_s; have := P_b.hγ_ℓ; have := bundleParams_lambdaS_pos P_b m₀
    have : 0 ≤ 12 * (E.L : ℝ) * bundleNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ *
        bundleLambdaS P_b m₀ := by positivity
    linarith
  have hD0 : 0 ≤ bundleBucketRecD E.L P_b m₀ := (bundleParams_bucketRec_pos E.L P_b m₀).2.1
  have hKs_nn := P_b.hK_s
  have hγ_nn := P_b.hγ_ℓ
  have hls_nn := bundleParams_lambdaS_pos P_b m₀
  have hrem_nn :
      0 ≤ 22 * (E.B_fn m₀ : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ +
        7 + 224 * (Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2)) ^ 2 := by
    have hlog_arg : (1 : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1) + 2 := by
      have : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀; nlinarith [E.hc_n]
    have hlog_nn := Real.log_nonneg hlog_arg
    positivity
  have hsplit : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤ bundleRecEnv E m₀ := by
    have ht1 : (10 : ℝ) ≤ (3 + 2 * coreE82Len E.L P_b) *
        bundleBucketRecUH E.L P_b m₀ + 2 * bundleBucketRecD E.L P_b m₀ := by
      have hUH_nn : 0 ≤ bundleBucketRecUH E.L P_b m₀ := by linarith
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht1 (by positivity))
      (show 0 ≤ 2 * bundleUCRatioHi E m₀ by linarith)
    unfold bundleRecEnv
    have ht2 : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤
        (E.B_fn m₀ : ℝ) * 10 * (2 * bundleUCRatioHi E m₀) := by
      have : 0 ≤ (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ := by positivity
      linarith
    linarith
  have hKs : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
      P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ ≤ bundleRecEnv E m₀ := by
    have hcore_nn : 0 ≤ (E.L : ℝ) * bundleNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ *
        bundleLambdaS P_b m₀ := by positivity
    have hUH_ge : (E.L : ℝ) * bundleNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ ≤
        bundleBucketRecUH E.L P_b m₀ := by unfold bundleBucketRecUH; linarith
    have hm1 : (E.L : ℝ) * bundleNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ ≤
        (3 + 2 * coreE82Len E.L P_b) * bundleBucketRecUH E.L P_b m₀ +
          2 * bundleBucketRecD E.L P_b m₀ := by
      have hUH_nn : 0 ≤ bundleBucketRecUH E.L P_b m₀ := by linarith
      nlinarith
    have hm3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 (by positivity))
      (show 0 ≤ 2 * bundleUCRatioHi E m₀ by linarith)
    have hm4 : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
          P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ ≤
        (E.B_fn m₀ : ℝ) * ((E.L : ℝ) * bundleNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ *
          bundleLambdaS P_b m₀) * (2 * bundleUCRatioHi E m₀) := by
      have : 0 ≤ (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
          P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ := by positivity
      linarith
    unfold bundleRecEnv; linarith
  have hlog1 : 0 ≤ Real.log ((n₀ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n₀])
  have hlog_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₀]) (by linarith)
  have hsq := pow_le_pow_left₀ hlog1 hlog_le 2
  have huc : bundleUCRatio n₀ ≤ bundleUCRatioHi E m₀ := by
    unfold bundleUCRatio bundleUCRatioHi; linarith
  have hrec : bundleRecoursePerQ E.L P_b m₀ n₀ actCard ≤ bundleRecEnv E m₀ := by
    have hcp := bundleParams_bucketRec_pos E.L P_b m₀
    have huc_nn := bundleParams_ucRatio_pos n₀
    have h3_nn : 0 ≤ (3 + 2 * coreE82Len E.L P_b) * bundleBucketRecUH E.L P_b m₀ +
        2 * bundleBucketRecD E.L P_b m₀ := by
      have h1 := hcp.1; have h2 := hcp.2.1; have h3 := hcp.2.2; positivity
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_right hB_le h3_nn)
      (show 2 * bundleUCRatio n₀ ≤ 2 * bundleUCRatioHi E m₀ by linarith)
      (by linarith) (by positivity)
    have hmul2 : 22 * (actCard : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ *
          bundleLambdaS P_b m₀ ≤
        22 * (E.B_fn m₀ : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b m₀ := by
      gcongr
    unfold bundleRecoursePerQ bundleRecEnv; linarith
  have hγ3 : 3 + P_b.γ_ℓ ≤ bundleRecEnv E m₀ := by
    have hγ_le_len : P_b.γ_ℓ ≤ coreE82Len E.L P_b := by
      unfold coreE82Len
      have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ E.L :=
        le_trans (by norm_num : (3 : ℝ) ≤ 3 ^ 1) (pow_le_pow_right₀ (by norm_num) E.hL)
      have hp : P_b.γ_ℓ ≤ P_b.γ_ℓ ^ (E.L + 1) :=
        le_trans (by simp) (pow_le_pow_right₀ P_b.hγ_ℓ (by omega : 1 ≤ E.L + 1))
      nlinarith [P_b.hγ_ℓ]
    have h4len : 2 * coreE82Len E.L P_b * 2 ≤ bundleRecEnv E m₀ := by
      unfold bundleRecEnv
      have h1 : 2 * coreE82Len E.L P_b * 2 ≤
          (3 + 2 * coreE82Len E.L P_b) * bundleBucketRecUH E.L P_b m₀ +
            2 * bundleBucketRecD E.L P_b m₀ := by
        have hUH_nn : 0 ≤ bundleBucketRecUH E.L P_b m₀ := by linarith
        nlinarith
      have h2 := mul_le_mul hB1 h1 (by positivity) (by positivity)
      have h3 := mul_le_mul h2 (by linarith : (1 : ℝ) ≤ 2 * bundleUCRatioHi E m₀) zero_le_one
        (by positivity)
      linarith
    linarith [hLen3]
  have hLp1 : ((E.L : ℝ) + 1) ≤ bundleCostMult E m₀ := by
    unfold bundleCostMult
    have h1 := coreE_L_ge_one E.L P_b
    have h3 : (1 : ℝ) ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1 := by
      nlinarith [P_b.hK_t, sq_nonneg P_b.γ_ℓ]
    have h4 : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) := le_max_left _ _
    have h134 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h3) h4
    exact le_trans (le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ (E.L : ℝ) + 1) h134)
      (le_max_right _ _)
  exact ⟨hsplit, hKs, huc, hrec, hγ3, hLp1⟩

lemma bundleCost_piece2a (E : SparseCoreEnv) (m₀ : ℕ)
    (hLp1_cm : ((E.L : ℝ) + 1) ≤ bundleCostMult E m₀)
    {logMN : ℝ} (hlogMN_ge1 : 1 ≤ logMN) :
    ((E.L : ℝ) + 1) * (m₀ : ℝ) ≤
      ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
        logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hrb1 : 1 ≤ bundleRecBase E m₀ :=
    le_trans (by linarith [bundleRecEnv_ge_four E m₀]) (le_max_left _ _)
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith [bundleCostMult_ge_one E m₀]
  have hlog_pow : 1 ≤ logMN ^ (max E.p_s_hi E.p_t_hi + 1) := one_le_pow₀ hlogMN_ge1
  have h1 : (E.L : ℝ) + 1 ≤
      (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
    calc (E.L : ℝ) + 1 ≤ bundleCostMult E m₀ := hLp1_cm
      _ = 1 * bundleCostMult E m₀ * 1 := by ring
      _ ≤ (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
          gcongr
  linarith [mul_le_mul h1 (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)]

lemma bundleCost_piece2b (E : SparseCoreEnv) (m₀ : ℕ)
    (hKs_piece : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀ ≤ bundleRecEnv E m₀)
    (hγ_le_rec : 3 + (E.P_fn m₀).γ_ℓ ≤ bundleRecEnv E m₀)
    (hLp1_cm : ((E.L : ℝ) + 1) ≤ bundleCostMult E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN) (hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi)
    (hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi *
      bundleLambdaS (E.P_fn m₀) m₀) :
    ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
      2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) ≤
      (3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 1) *
        (((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  set p_max := max E.p_s_hi E.p_t_hi
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hpow_le_succ : logMN ^ p_max ≤ logMN ^ (p_max + 1) :=
    pow_le_pow_right₀ hlogMN_ge1 (Nat.le_succ p_max)
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  have hrec_ge4 : 4 ≤ bundleRecEnv E m₀ := bundleRecEnv_ge_four E m₀
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb1 : 1 ≤ bundleRecBase E m₀ := by linarith
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ bundleCostMult E m₀ := bundleCostMult_ge_one E m₀
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith
  have hγr_nn : 0 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ := mul_nonneg hrb_nn hcm_nn
  have hKt_cm : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) ≤ bundleCostMult E m₀ := by
    unfold bundleCostMult
    have h1 := coreE_L_ge_one E.L (E.P_fn m₀)
    have h45 := one_le_mul_of_one_le_of_one_le
      (le_max_left (1 : ℝ) ((E.L : ℝ) * bundleNRoot E.L m₀))
      (by linarith [Nat.cast_nonneg (α := ℝ) E.L] : (1 : ℝ) ≤ (E.L : ℝ) + 1)
    have hkt_nn : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) := by
      have := (E.P_fn m₀).hK_t; positivity
    have hkt1_nn : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by linarith
    have hA : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) ≤
        coreE_L E.L (E.P_fn m₀) * ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) :=
      le_trans (by linarith) (mul_le_mul_of_nonneg_right h1 hkt1_nn)
    have hB1 := le_mul_of_one_le_right (mul_nonneg (le_trans zero_le_one h1) hkt1_nn) h45
    have hB2 : coreE_L E.L (E.P_fn m₀) * ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          (max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1)) =
        coreE_L E.L (E.P_fn m₀) * ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1) := by ring
    exact le_trans (le_trans hA (le_trans hB1 (le_of_eq hB2))) (le_max_right _ _)
  have ht1 : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ * (m₀ : ℝ) ≤
      (7 : ℝ) ^ p_max * (((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
        logMN ^ (p_max + 1)) := by
    have hΛp : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ (p_max + 1) :=
      le_trans hΛ_bound (mul_le_mul_of_nonneg_left hpow_le_succ (by positivity))
    have hcm_γr : bundleCostMult E m₀ ≤ bundleRecBase E m₀ * bundleCostMult E m₀ :=
      le_trans (by rw [one_mul]) (mul_le_mul_of_nonneg_right hrb1 hcm_nn)
    have hprod := mul_le_mul (le_trans hKt_cm hcm_γr) hΛp hΛ_nn hγr_nn
    linarith [mul_le_mul hprod (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)]
  have ht2 : (3 + (E.P_fn m₀).γ_ℓ) * (m₀ : ℝ) ≤
      ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1) := by
    have h1 : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ * bundleCostMult E m₀ :=
      le_trans hrb_ge (le_trans (by rw [mul_one]) (mul_le_mul_of_nonneg_left hcm_ge1 hrb_nn))
    have hprod := mul_le_mul (le_trans hγ_le_rec h1) hlog_pow_ge1 zero_le_one hγr_nn
    linarith [mul_le_mul hprod (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)]
  have ht3 : 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ * (m₀ : ℝ) ≤
      2 * (7 : ℝ) ^ p_max *
        (((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)) := by
    have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
    have hucHi1 : 1 ≤ bundleUCRatioHi E m₀ := bundleUCRatioHi_ge_one E m₀
    have hL1 : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
    have hnr1 : 1 ≤ bundleNRoot E.L m₀ := bundleParams_nRoot_ge_one E.L m₀
    have hK_nn : 0 ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ :=
      mul_nonneg (E.P_fn m₀).hK_s (by linarith [(E.P_fn m₀).hγ_ℓ])
    have hls_nn := bundleParams_lambdaS_pos (E.P_fn m₀) m₀
    have hKs1 : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀ ≤
        bundleRecEnv E m₀ := by
      have hBu := one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hB1 hucHi1) (one_le_mul_of_one_le_of_one_le hL1 hnr1)
      have hmul := mul_le_mul_of_nonneg_right hBu (mul_nonneg hK_nn hls_nn)
      have hEq2 : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * ((E.L : ℝ) * bundleNRoot E.L m₀) *
            ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀) =
          (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
            (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀ := by ring
      exact le_trans (by rw [one_mul]) (le_trans hmul (le_trans (le_of_eq hEq2) hKs_piece))
    have hKΛ : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ ≤
        (7 : ℝ) ^ p_max * bundleRecBase E m₀ * logMN ^ (p_max + 1) := by
      calc (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ
          ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
              ((7 : ℝ) ^ p_max * logMN ^ p_max * bundleLambdaS (E.P_fn m₀) m₀) :=
              mul_le_mul_of_nonneg_left hΛ_mul_Λs hK_nn
        _ = (7 : ℝ) ^ p_max * ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
              bundleLambdaS (E.P_fn m₀) m₀) * logMN ^ p_max := by ring
        _ ≤ (7 : ℝ) ^ p_max * bundleRecBase E m₀ * logMN ^ (p_max + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hKs1 hrb_ge) (by positivity))
              hpow_le_succ (pow_nonneg hlogMN_nn _) (mul_nonneg (by positivity) hrb_nn)
    have hprod : ((E.L : ℝ) + 1) * ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) ≤
        (7 : ℝ) ^ p_max * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1) := by
      linarith [mul_le_mul hLp1_cm hKΛ (mul_nonneg hK_nn hΛ_nn) hcm_nn]
    have hprod' := le_trans (le_mul_of_one_le_left (mul_nonneg hK_nn hΛ_nn)
      (by linarith [Nat.cast_nonneg (α := ℝ) E.L] : (1 : ℝ) ≤ (E.L : ℝ) + 1)) hprod
    linarith [mul_le_mul hprod' (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn
      (mul_nonneg (mul_nonneg (by positivity) hγr_nn) (pow_nonneg hlogMN_nn _))]
  have hrew3 : ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
        2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
      (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ * (m₀ : ℝ) +
        (3 + (E.P_fn m₀).γ_ℓ) * (m₀ : ℝ) +
        2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ * (m₀ : ℝ) := by ring
  linarith [hrew3, ht1, ht2, ht3]

lemma bundleCost_piece34 (E : SparseCoreEnv) (m₀ n₀ actCard q_τ : ℕ)
    (hq_m0 : q_τ ≤ m₀)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (huc_le : bundleUCRatio n₀ ≤ bundleUCRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤ bundleRecEnv E m₀)
    (hRec_le : bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ actCard ≤ bundleRecEnv E m₀)
    {logMN : ℝ} (hlogMN_ge1 : 1 ≤ logMN) :
    let T := ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
      logMN ^ (max E.p_s_hi E.p_t_hi + 1)
    (q_τ : ℝ) ≤ T ∧
    (actCard : ℝ) * (2 * bundleUCRatio n₀ * (q_τ : ℝ)) ≤ 2 * T ∧
    bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ actCard * (q_τ : ℝ) ≤ T := by
  intro T
  set p_max := max E.p_s_hi E.p_t_hi
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ bundleUCRatioHi E m₀ := bundleUCRatioHi_ge_one E m₀
  have hrec_ge4 : 4 ≤ bundleRecEnv E m₀ := bundleRecEnv_ge_four E m₀
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ bundleCostMult E m₀ := bundleCostMult_ge_one E m₀
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith
  have hγr_nn : 0 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ := mul_nonneg hrb_nn hcm_nn
  have hγr_ge1 : 1 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith) hcm_ge1
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  have hm_1_nn : (0 : ℝ) ≤ (m₀ : ℝ) + 1 := by linarith
  have hT_pre_nn := mul_nonneg hm_1_nn hγr_nn
  have hr_γr : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ * bundleCostMult E m₀ :=
    le_trans hrb_ge (le_trans (by rw [mul_one]) (mul_le_mul_of_nonneg_left hcm_ge1 hrb_nn))
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq_m0
  have hq_nn : 0 ≤ (q_τ : ℝ) := Nat.cast_nonneg _
  have hm_le_T : (m₀ : ℝ) ≤ T := by
    have h1_le := one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
    calc (m₀ : ℝ) ≤ ((m₀ : ℝ) + 1) := by linarith
      _ = ((m₀ : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀ * logMN ^ (p_max + 1)) :=
          mul_le_mul_of_nonneg_left h1_le hm_1_nn
      _ = T := by dsimp only [T]; ring
  have hBuc_le : (actCard : ℝ) * bundleUCRatio n₀ ≤ (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ :=
    mul_le_mul hB_le huc_le (bundleParams_ucRatio_pos n₀) (by linarith)
  have hBuc_b : (actCard : ℝ) * bundleUCRatio n₀ * (q_τ : ℝ) ≤
      (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (m₀ : ℝ) :=
    mul_le_mul hBuc_le hqR hq_nn (by positivity)
  have hBuc_rec : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ ≤
      bundleRecBase E m₀ * bundleCostMult E m₀ := by
    have hBu : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ ≤
        (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 := by
      have : 0 ≤ (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ := by positivity
      linarith
    exact le_trans (le_trans hBu hrec_split) hr_γr
  have hm2' : ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) ≤ T := by
    calc ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀)
        = ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * 1 := (mul_one _).symm
      _ ≤ T := mul_le_mul_of_nonneg_left hlog_pow_ge1 hT_pre_nn
  have huc_term : (actCard : ℝ) * (2 * bundleUCRatio n₀ * (q_τ : ℝ)) ≤ 2 * T := by
    have hm1 := mul_le_mul hBuc_rec (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn hγr_nn
    have hEq : (actCard : ℝ) * (2 * bundleUCRatio n₀ * (q_τ : ℝ)) =
        2 * ((actCard : ℝ) * bundleUCRatio n₀ * (q_τ : ℝ)) := by ring
    linarith [hEq, hBuc_b, hm1, hm2']
  have h4_le := mul_le_mul hRec_le hqR hq_nn (by linarith)
  have hr_term : bundleRecEnv E m₀ * (m₀ : ℝ) ≤ T := by
    have hrm : bundleRecEnv E m₀ * (m₀ : ℝ) ≤
        ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) := by
      linarith [mul_le_mul hr_γr (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn hγr_nn]
    exact le_trans hrm hm2'
  exact ⟨le_trans hqR hm_le_T, huc_term, le_trans h4_le hr_term⟩

lemma bundleCost_piece5_split (E : SparseCoreEnv) (k m₀ n₀ actCard q_ep q_τ : ℕ)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (huc_le : bundleUCRatio n₀ ≤ bundleUCRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤ bundleRecEnv E m₀)
    (hKs_piece : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀ ≤ bundleRecEnv E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN)
    (hlog_uc : Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2) ≤ 7 * logMN)
    (_hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi) :
    90 * (E.L : ℝ) * bundleNRoot E.L m₀ *
      ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) * coreE_L E.L (E.P_fn m₀) *
      ((k : ℝ) + 1) * Λ *
      (20 * ((m₀ : ℝ) + (actCard : ℝ) * (2 * bundleUCRatio n₀ * (q_ep : ℝ))) *
        Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2)) ≤
      12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        (((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (max E.p_s_hi E.p_t_hi + 1)) +
      25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        ((q_ep : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  set p_max := max E.p_s_hi E.p_t_hi
  set uc_ep := 2 * bundleUCRatio n₀ * (q_ep : ℝ)
  set ucBound := 2 * bundleUCRatio n₀ * (q_τ : ℝ)
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ bundleUCRatioHi E m₀ := bundleUCRatioHi_ge_one E m₀
  have hrec_ge4 : 4 ≤ bundleRecEnv E m₀ := bundleRecEnv_ge_four E m₀
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ bundleCostMult E m₀ := bundleCostMult_ge_one E m₀
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith
  have hEL_nn : 0 ≤ coreE_L E.L (E.P_fn m₀) := by linarith [coreE_L_ge_one E.L (E.P_fn m₀)]
  have hNR_nn : 0 ≤ bundleNRoot E.L m₀ := by linarith [bundleParams_nRoot_ge_one E.L m₀]
  have hKt_nn := (E.P_fn m₀).hK_t; have hKs_nn := (E.P_fn m₀).hK_s
  have huc_pos := bundleParams_ucRatio_pos n₀
  have huc_ep_nn : 0 ≤ uc_ep := mul_nonneg (mul_nonneg zero_le_two huc_pos) (Nat.cast_nonneg _)
  have huc_b : uc_ep ≤ 2 * (bundleUCRatioHi E m₀ * (q_ep : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right huc_le (Nat.cast_nonneg (α := ℝ) q_ep)
    dsimp only [uc_ep]; linarith
  have h1m : (m₀ : ℝ) ≤ (m₀ : ℝ) * (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ := by
    have hBu1 := one_le_mul_of_one_le_of_one_le hB1 hucHi1
    calc (m₀ : ℝ) = (m₀ : ℝ) * 1 := (mul_one _).symm
      _ ≤ (m₀ : ℝ) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) :=
          mul_le_mul_of_nonneg_left hBu1 (Nat.cast_nonneg _)
      _ = _ := by ring
  have h2m : (actCard : ℝ) * uc_ep ≤ 2 * (E.B_fn m₀ : ℝ) * (bundleUCRatioHi E m₀ * (q_ep : ℝ)) := by
    linarith [mul_le_mul hB_le huc_b huc_ep_nn (by linarith)]
  have hm_uc : (m₀ : ℝ) + (actCard : ℝ) * uc_ep ≤
      (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) := by
    have hBu_ge1 := one_le_mul_of_one_le_of_one_le hB1 hucHi1
    linarith [h1m, h2m, hBu_ge1]
  have hcore_factor :
      (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) ≤
        bundleRecBase E m₀ * bundleCostMult E m₀ := by
    have hEL_le_cm : coreE_L E.L (E.P_fn m₀) * max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) *
        ((E.P_fn m₀).K_t + 1) ≤ bundleCostMult E m₀ := by
      unfold bundleCostMult
      have hL1 : (1 : ℝ) ≤ (E.L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E.L]
      have hK1 : (E.P_fn m₀).K_t + 1 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
        nlinarith [(E.P_fn m₀).hK_t, sq_nonneg (E.P_fn m₀).γ_ℓ]
      have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 hEL_nn)
        (by positivity : 0 ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L m₀))
      have h3_nn : 0 ≤ coreE_L E.L (E.P_fn m₀) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) := by
        have : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
          have := sq_nonneg (E.P_fn m₀).γ_ℓ; positivity
        positivity
      have hpre1 : coreE_L E.L (E.P_fn m₀) * max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) *
            ((E.P_fn m₀).K_t + 1) =
          coreE_L E.L (E.P_fn m₀) * ((E.P_fn m₀).K_t + 1) *
            max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) := by ring
      exact le_trans (le_of_eq hpre1) (le_trans h3 (le_trans (le_mul_of_one_le_right h3_nn hL1)
        (le_max_right _ _)))
    have hKs_le_rb : (E.L : ℝ) * bundleNRoot E.L m₀ * (E.P_fn m₀).K_s *
        ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) ≤ bundleRecBase E m₀ := by
      have hγls := one_le_mul_of_one_le_of_one_le (E.P_fn m₀).hγ_ℓ
        (bundleParams_lambdaS_ge_one (E.P_fn m₀) m₀)
      have h1 := le_mul_of_one_le_right
        (by positivity : 0 ≤ (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) *
          bundleNRoot E.L m₀ * (E.P_fn m₀).K_s) hγls
      have hEq : (E.L : ℝ) * bundleNRoot E.L m₀ * (E.P_fn m₀).K_s *
            ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) =
          (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
            (E.P_fn m₀).K_s := by ring
      have hKs' : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
            (E.P_fn m₀).K_s * ((E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀) ≤
          bundleRecEnv E m₀ := by simpa only [mul_assoc] using hKs_piece
      exact le_trans (le_of_eq hEq) (le_trans h1 (le_trans hKs' hrb_ge))
    have hsplit_Kt :
        (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) ≤
        ((E.P_fn m₀).K_t + 1) * max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) *
          coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) +
        coreE_L E.L (E.P_fn m₀) *
          ((E.L : ℝ) * bundleNRoot E.L m₀ * (E.P_fn m₀).K_s *
            ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀)) := by
      have hfirst := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((E.L : ℝ) * bundleNRoot E.L m₀))
          (by linarith : 0 ≤ (E.P_fn m₀).K_t + 1))
        (by positivity : 0 ≤ coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀))
      linarith
    have hT1 : ((E.P_fn m₀).K_t + 1) * max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) *
          coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) ≤
        bundleCostMult E m₀ * (bundleRecBase E m₀ / 2) := by
      have hBu_rb : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ ≤ bundleRecBase E m₀ / 2 := by linarith
      linarith [mul_le_mul hEL_le_cm hBu_rb (by positivity) hcm_nn]
    have hT2 : coreE_L E.L (E.P_fn m₀) *
          ((E.L : ℝ) * bundleNRoot E.L m₀ * (E.P_fn m₀).K_s *
            ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀)) ≤
        bundleCostMult E m₀ * (bundleRecBase E m₀ / 2) := by
      have hcm2 : coreE_L E.L (E.P_fn m₀) ≤ bundleCostMult E m₀ / 2 := by
        have hL1 : (2 : ℝ) ≤ (E.L : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
          linarith
        have hKt1 : (1 : ℝ) ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
          nlinarith [(E.P_fn m₀).hK_t, sq_nonneg (E.P_fn m₀).γ_ℓ]
        have h2mul : (2 : ℝ) ≤ ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
            max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1) := by
          calc (2 : ℝ) = 1 * 2 := by norm_num
            _ ≤ _ := mul_le_mul
                (one_le_mul_of_one_le_of_one_le hKt1 (le_max_left _ _)) hL1
                (by norm_num) (by positivity)
        have hm2 := mul_le_mul_of_nonneg_left h2mul hEL_nn
        unfold bundleCostMult
        have hrr : coreE_L E.L (E.P_fn m₀) *
              (((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
                max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1)) =
            coreE_L E.L (E.P_fn m₀) * ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
              max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1) := by ring
        rw [hrr] at hm2
        linarith [le_max_right (1 : ℝ) (coreE_L E.L (E.P_fn m₀) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L m₀) * ((E.L : ℝ) + 1))]
      linarith [mul_le_mul hcm2 hKs_le_rb (by positivity) (by linarith)]
    linarith
  have hcore_nn : 0 ≤ (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
      coreE_L E.L (E.P_fn m₀) := by positivity
  have hlog_uc_nn : 0 ≤ Real.log ((m₀ : ℝ) + ucBound + 2) :=
    Real.log_nonneg (by
      have : 0 ≤ ucBound := mul_nonneg (mul_nonneg zero_le_two huc_pos) (Nat.cast_nonneg _)
      linarith [Nat.cast_nonneg (α := ℝ) m₀])
  have hm_uc_nn : 0 ≤ (m₀ : ℝ) + (actCard : ℝ) * uc_ep := by positivity
  have hcoeff_sum_nn : 0 ≤ (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN) := by positivity
  have hinner_prod :
      ((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀)) *
        (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2)) ≤
      (bundleRecBase E m₀ * bundleCostMult E m₀) *
        ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN)) := by
    have h1 := mul_le_mul hm_uc hlog_uc hlog_uc_nn (by positivity)
    have h2_eq : ((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀)) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) *
            (7 * logMN)) =
        (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN) *
          ((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
            coreE_L E.L (E.P_fn m₀) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀)) := by ring
    have h2 : ((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀)) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀) *
            (7 * logMN)) ≤
        (bundleRecBase E m₀ * bundleCostMult E m₀) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN)) := by
      rw [h2_eq]; linarith [mul_le_mul_of_nonneg_left hcore_factor hcoeff_sum_nn]
    exact le_trans (mul_le_mul_of_nonneg_left h1 hcore_nn) h2
  have hfull :
      90 * 20 * ((k : ℝ) + 1) * Λ *
        (((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀)) *
          (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2))) ≤
      90 * 20 * ((k : ℝ) + 1) * ((7 : ℝ) ^ p_max * logMN ^ p_max) *
        ((bundleRecBase E m₀ * bundleCostMult E m₀) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hΛ_bound (by positivity)) hinner_prod
      (mul_nonneg hcore_nn (mul_nonneg hm_uc_nn hlog_uc_nn)) (by positivity)
  have hre1 :
      90 * (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((k : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2)) =
      90 * 20 * ((k : ℝ) + 1) * Λ *
        (((E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀)) *
          (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2))) := by ring
  have hre2 :
      90 * 20 * ((k : ℝ) + 1) * ((7 : ℝ) ^ p_max * logMN ^ p_max) *
        ((bundleRecBase E m₀ * bundleCostMult E m₀) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN))) =
      12600 * (7 : ℝ) ^ p_max *
        (((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (p_max + 1)) +
      25200 * (7 : ℝ) ^ p_max *
        ((q_ep : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (p_max + 1)) := by
    rw [show p_max + 1 = Nat.succ p_max from rfl, pow_succ]; ring
  linarith [hre1, hre2, hfull]

lemma bundleCost_piece5 (E : SparseCoreEnv) (k m₀ n₀ actCard q_τ : ℕ)
    (hq_m0 : q_τ ≤ m₀)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (huc_le : bundleUCRatio n₀ ≤ bundleUCRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * 10 ≤ bundleRecEnv E m₀)
    (hKs_piece : (E.B_fn m₀ : ℝ) * bundleUCRatioHi E m₀ * (E.L : ℝ) * bundleNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * bundleLambdaS (E.P_fn m₀) m₀ ≤ bundleRecEnv E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN)
    (hlog_uc : Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2) ≤ 7 * logMN)
    (hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi) :
    90 * (E.L : ℝ) * bundleNRoot E.L m₀ *
      ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) * coreE_L E.L (E.P_fn m₀) *
      ((k : ℝ) + 1) * Λ *
      (20 * ((m₀ : ℝ) + (actCard : ℝ) * (2 * bundleUCRatio n₀ * (q_τ : ℝ))) *
        Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2)) ≤
      37800 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        (((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  have hs := bundleCost_piece5_split E k m₀ n₀ actCard q_τ q_τ hB_le huc_le
    hrec_split hKs_piece hlogMN_ge1 hlog_uc hΛ_nn hΛ_bound
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq_m0
    linarith
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith [bundleRecEnv_ge_four E m₀]
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith [bundleCostMult_ge_one E m₀]
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hfactor_nn : 0 ≤ 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      (((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
        logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by positivity
  nlinarith [hs, hqR, hfactor_nn]

lemma bundleLambda_le_logMN (E : SparseCoreEnv) (m₀ n₀ : ℕ) (hn₀_pos : 1 ≤ n₀) :
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    bundleLambda (E.P_fn m₀) m₀ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max ∧
    bundleLambda (E.P_fn m₀) m₀ ≤
      (7 : ℝ) ^ p_max * logMN ^ p_max * bundleLambdaS (E.P_fn m₀) m₀ := by
  intro p_max logMN
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) m₀]))]
  have hΛ_bound : bundleLambda (E.P_fn m₀) m₀ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max := by
    unfold bundleLambda
    have hlogC := log_bundleNMax_le m₀ n₀ hn₀_pos
    have hp_le : max (E.P_fn m₀).p_s (E.P_fn m₀).p_t ≤ p_max :=
      max_le (le_trans (E.hp_s m₀) (le_max_left _ _)) (le_trans (E.hp_t m₀) (le_max_right _ _))
    have hbase : 0 ≤ 1 + Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^
            max (E.P_fn m₀).p_s (E.P_fn m₀).p_t
        ≤ (7 * logMN) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t := pow_le_pow_left₀ hbase hlogC _
      _ ≤ (7 * logMN) ^ p_max := pow_le_pow_right₀ (by linarith) hp_le
      _ = (7 : ℝ) ^ p_max * logMN ^ p_max := by rw [mul_pow]
  have hΛs_ge1 : 1 ≤ bundleLambdaS (E.P_fn m₀) m₀ := bundleParams_lambdaS_ge_one _ m₀
  exact ⟨hΛ_bound, by
    linarith [mul_le_mul_of_nonneg_left hΛs_ge1
      (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ p_max * logMN ^ p_max)]⟩

end

end MinCostFlow.SparseCore
