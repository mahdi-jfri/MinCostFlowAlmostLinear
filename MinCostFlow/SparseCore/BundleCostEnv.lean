module

public import MinCostFlow.SparseCore.BundleCostPieces
public import MinCostFlow.SparseCore.BundleParamBridges
import MinCostFlow.SparseCore.BundleCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime Envelope Bridge for `sparseCoreBundleTool`

This file translates the per-branch cost bound of `bundleRunSeq` (and of a single branch restart)
into the parameter form of `bundleCoreParams E` (`IsSpecOrdUpTo`, `IsSpecOrdRestart`; paper Lemma
5.17, pages 23–24).

The bundle degree is at most `k`, so the dynamic-spanner update work carries `((k : ℝ) + 1)`
outside `γ_r(M)` instead of a degree function `d_fn`. None of the proofs reads `SparseCoreEnv.d_fn`
or `SparseCoreEnv.hd_mono`.

The main results are:
* `bundleRestartCost_le_params`: parameter-form bound on one restart, without `hComp_bound`.
* `bundleCost_env_baseline_parts` and `bundleCost_env_baseline_parts_noComp`: baseline plus
  dynamic-spanner cost envelope for an epoch or a full run.
* `bundleRunSeq_cost_le_params_at` / `bundleRunSeq_cost_le_params`: per-branch cost bound from
  `bundleRunSeq_cost_le` (with `hComp_bound`).
* `bundleRunSeq_cost_le_params_noComp_at` / `bundleRunSeq_cost_le_params_noComp` and
  `sparseCoreBundleTool_cost_le_of_branch`: per-branch and total tool cost bounds without
  `hComp_bound`, using the active-vertex / `min N (M + 1)` cost bound.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Restart cost and baseline-plus-dynamic cost envelope -/

/-- Parameter-form bound on the cost of one branch restart (no degree bound and no `hComp_bound`).
Gives both the raw restart cost and its combination with one epoch's `12600 · 7^p` allowance,
with or without the `((k : ℝ) + 1)` factor. -/
lemma bundleRestartCost_le_params (E : SparseCoreEnv) (m₀ n₀ m_cur bucketCost : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hm_cur : m_cur ≤ 2 * m₀)
    (hbuck : (bucketCost : ℝ) ≤
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * bundleLambda (E.P_fn m₀) m₀ +
        3 + (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
        bundleLambda (E.P_fn m₀) m₀) * (m₀ : ℝ)) :
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let T := ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T ∧
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T ≤ P.c_T * T ∧
    (∀ k : ℕ, ((m_cur + 1 + bucketCost : ℕ) : ℝ) +
      12600 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * T) ≤ P.c_T * (((k : ℝ) + 1) * T)) := by
  intro P p_max logMN T
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))]
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨_, hKs_piece, _, _, hγ_le_rec, hLp1_cm⟩ :=
    bundleEnv_core_bounds E m₀ (min n₀ (m₀ + 1)) (E.B_fn m₀) le_rfl
      (min_le_cn_mul_m_add_one E m₀ n₀)
  set Λ := bundleLambda (E.P_fn m₀) m₀
  have hΛ_nn : 0 ≤ Λ := by linarith [bundleParams_lambda_ge_one (E.P_fn m₀) m₀]
  obtain ⟨hΛ_bound, hΛ_mul_Λs⟩ := bundleLambda_le_logMN E m₀ n₀ hn₀_pos
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith [bundleRecEnv_ge_four E m₀]
  have hcm_ge1 : 1 ≤ bundleCostMult E m₀ := bundleCostMult_ge_one E m₀
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith
  have hγr_ge1 : 1 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith [bundleRecEnv_ge_four E m₀]) hcm_ge1
  have h1_le : (1 : ℝ) ≤ (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1) :=
    one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
  have hm_cur_T : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have hmc : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * ((m₀ : ℝ) + 1) := by
      have : (m_cur : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hm_cur
      push_cast; linarith
    have hstep := mul_le_mul_of_nonneg_left h1_le (show 0 ≤ 2 * ((m₀ : ℝ) + 1) by linarith)
    have hEq : 2 * ((m₀ : ℝ) + 1) *
        ((bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)) = 2 * T := by
      dsimp only [T]; ring
    linarith
  have hp2a := bundleCost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := bundleCost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn
    hΛ_bound hΛ_mul_Λs
  have hinit_split :
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
        ((E.L : ℝ) + 1) * (m₀ : ℝ) +
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
            2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) := by ring
  have htot : ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T := by
    dsimp only [T, p_max] at hm_cur_T ⊢
    push_cast at hm_cur_T ⊢
    linarith [hm_cur_T, hbuck, hinit_split, hp2a, hp2b]
  have hT_nn : 0 ≤ T := by
    dsimp only [T]
    have : 0 ≤ logMN := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg this _)
  have hcT : (4 + 3 * (7 : ℝ) ^ p_max) + 12600 * (7 : ℝ) ^ p_max ≤ P.c_T := by
    dsimp only [P, bundleCoreParams, p_max]
    linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := max E.p_s_hi E.p_t_hi), E.hc_n]
  refine ⟨htot, ?_, fun k => ?_⟩
  · calc ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T
        ≤ (4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * T := by linarith [htot]
      _ ≤ P.c_T * T := mul_le_mul_of_nonneg_right hcT hT_nn
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hT_le_Tk : T ≤ ((k : ℝ) + 1) * T := by nlinarith
    have htot_k : ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤
        (4 + 3 * (7 : ℝ) ^ p_max) * (((k : ℝ) + 1) * T) :=
      le_trans htot (mul_le_mul_of_nonneg_left hT_le_Tk (by positivity))
    have hTk_nn : 0 ≤ ((k : ℝ) + 1) * T := mul_nonneg (by linarith) hT_nn
    calc ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * T)
        ≤ (4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * (((k : ℝ) + 1) * T) := by
          linarith [htot_k]
      _ ≤ P.c_T * (((k : ℝ) + 1) * T) := mul_le_mul_of_nonneg_right hcT hTk_nn

private lemma bundleCost_env_baseline_parts_gen (E : SparseCoreEnv)
    (k m₀ n₀ n_init n_uc q_τ : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hqτ_le_m0 : q_τ ≤ m₀)
    (hn_uc_cn : (n_uc : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1))
    (hlog_uc : Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n_uc * (q_τ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2))
    (hn_init : n_init ≤ 2 * m₀ ∨ (n_init : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1)) :
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let Λ := bundleLambda (E.P_fn m₀) m₀
    let T := ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)
    let Tk := ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
      logMN ^ (p_max + 1)
    ((m₀ : ℝ) + (n_init : ℝ) + 1) +
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
        (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
      (q_τ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n_uc * (q_τ : ℝ)) +
      bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n_uc (E.B_fn m₀) * (q_τ : ℝ) ≤
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T ∧
    (∀ q_ep : ℕ,
      90 * (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((k : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n_uc * (q_ep : ℝ))) *
          Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n_uc * (q_τ : ℝ) + 2)) ≤
        12600 * (7 : ℝ) ^ p_max * Tk +
        25200 * (7 : ℝ) ^ p_max *
          ((q_ep : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
            logMN ^ (p_max + 1))) ∧
    (((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * Tk ≤
      P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T ∧
      (0 ≤ T ∧ 0 ≤ Tk ∧ 0 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ ∧ 1 ≤ logMN)) := by
  intro P p_max logMN Λ T Tk
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))]
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨hrec_split, hKs_piece, huc_le, hRec_le, hγ_le_rec, hLp1_cm⟩ :=
    bundleEnv_core_bounds E m₀ n_uc (E.B_fn m₀) le_rfl hn_uc_cn
  have hΛ_nn : 0 ≤ Λ := by linarith [bundleParams_lambda_ge_one (E.P_fn m₀) m₀]
  obtain ⟨hΛ_bound, hΛ_mul_Λs⟩ := bundleLambda_le_logMN E m₀ n₀ hn₀_pos
  have hrec_ge4 : 4 ≤ bundleRecEnv E m₀ := bundleRecEnv_ge_four E m₀
  have hrb_ge : bundleRecEnv E m₀ ≤ bundleRecBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ bundleRecBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ bundleCostMult E m₀ := bundleCostMult_ge_one E m₀
  have hcm_nn : 0 ≤ bundleCostMult E m₀ := by linarith
  have hγr_ge4 : 4 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ := by nlinarith
  have hT_nn : 0 ≤ T := by
    dsimp only [T]
    have : 0 ≤ logMN := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg this _)
  have hTk_nn : 0 ≤ Tk := by
    have hEq : Tk = ((k : ℝ) + 1) * T := by dsimp only [Tk, T]; ring
    rw [hEq]; exact mul_nonneg (by positivity) hT_nn
  have hp1 : (m₀ : ℝ) + (n_init : ℝ) + 1 ≤ (1 + E.c_n) * T := by
    rcases hn_init with hact | hcomp
    · have hactR : (n_init : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hact
      have hmn : (m₀ : ℝ) + (n_init : ℝ) + 1 ≤ 3 * ((m₀ : ℝ) + 1) := by linarith
      have h4_le : (4 : ℝ) ≤ (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (p_max + 1) := by nlinarith
      have h3T : 3 * ((m₀ : ℝ) + 1) ≤ T := by
        have hstep := mul_le_mul_of_nonneg_left
          (show (3 : ℝ) ≤ (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1) by
            linarith) (show (0 : ℝ) ≤ (m₀ : ℝ) + 1 by linarith)
        have hEq : ((m₀ : ℝ) + 1) * ((bundleRecBase E m₀ * bundleCostMult E m₀) *
            logMN ^ (p_max + 1)) = T := by dsimp only [T]; ring
        linarith
      have hcn_ge1 : (1 : ℝ) ≤ 1 + E.c_n := by linarith [E.hc_n]
      exact le_trans hmn (le_trans h3T (by nlinarith))
    · have hmn : (m₀ : ℝ) + (n_init : ℝ) + 1 ≤ (1 + E.c_n) * ((m₀ : ℝ) + 1) := by linarith
      have h1_le : (1 : ℝ) ≤ (bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (p_max + 1) := by nlinarith
      have hstep := mul_le_mul_of_nonneg_left h1_le
        (show 0 ≤ (1 + E.c_n) * ((m₀ : ℝ) + 1) by linarith [E.hc_n])
      have hEq : (1 + E.c_n) * ((m₀ : ℝ) + 1) * ((bundleRecBase E m₀ * bundleCostMult E m₀) *
          logMN ^ (p_max + 1)) = (1 + E.c_n) * T := by dsimp only [T]; ring
      exact le_trans hmn (by linarith [hstep, hEq])
  have hp2a := bundleCost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := bundleCost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn
    hΛ_bound hΛ_mul_Λs
  obtain ⟨hp3, hp3b, hp4⟩ := bundleCost_piece34 E m₀ n_uc (E.B_fn m₀) q_τ
    hqτ_le_m0 le_rfl huc_le hrec_split hRec_le hlogMN_ge1
  have hinit_split :
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
        ((E.L : ℝ) + 1) * (m₀ : ℝ) +
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
            2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) := by ring
  have hbase_le :
      ((m₀ : ℝ) + (n_init : ℝ) + 1) +
        ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
        (q_τ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n_uc * (q_τ : ℝ)) +
        bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n_uc (E.B_fn m₀) * (q_τ : ℝ) ≤
          ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by
    have hsum_eq : (1 + E.c_n) * T + (T + (3 * (7 : ℝ) ^ p_max + 1) * T) + T + 2 * T + T =
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by ring
    linarith [hinit_split, hp1, hp2a, hp2b, hp3, hp3b, hp4, hsum_eq]
  refine ⟨hbase_le, fun q_ep => ?_, ?_⟩
  · exact bundleCost_piece5_split E k m₀ n_uc (E.B_fn m₀) q_ep q_τ
      le_rfl huc_le hrec_split hKs_piece hlogMN_ge1 hlog_uc hΛ_nn hΛ_bound
  · have hcT_le : (7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max ≤ P.c_T := by
      dsimp only [P, bundleCoreParams]
      linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := p_max), E.hc_n]
    have hFinal_eq : P.c_T * Tk =
        P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T := by
      dsimp only [Tk, P, bundleCoreParams, p_max]; ring
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hcT_le hTk_nn) (le_of_eq hFinal_eq),
      hT_nn, hTk_nn, mul_nonneg hrb_nn hcm_nn, hlogMN_ge1⟩

/-- Baseline plus dynamic-spanner cost envelope with `hComp : n₀ ≤ E.c_n * (m₀ + 1)`. -/
lemma bundleCost_env_baseline_parts (E : SparseCoreEnv) (k m₀ n₀ q_τ : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hqτ_le_m0 : q_τ ≤ m₀)
    (hComp : (n₀ : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1)) :
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let Λ := bundleLambda (E.P_fn m₀) m₀
    let T := ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)
    let Tk := ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
      logMN ^ (p_max + 1)
    ((m₀ : ℝ) + (n₀ : ℝ) + 1) +
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
        (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
      (q_τ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n₀ * (q_τ : ℝ)) +
      bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ (E.B_fn m₀) * (q_τ : ℝ) ≤
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T ∧
    (∀ q_ep : ℕ,
      90 * (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((k : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n₀ * (q_ep : ℝ))) *
          Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2)) ≤
        12600 * (7 : ℝ) ^ p_max * Tk +
        25200 * (7 : ℝ) ^ p_max *
          ((q_ep : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
            logMN ^ (p_max + 1))) ∧
    (((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * Tk ≤
      P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T ∧
      (0 ≤ T ∧ 0 ≤ Tk ∧ 0 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ ∧ 1 ≤ logMN)) :=
  bundleCost_env_baseline_parts_gen E k m₀ n₀ n₀ n₀ q_τ hn₀_pos hqτ_le_m0 hComp
    (log_bundleUCBound_le m₀ n₀ hn₀_pos q_τ hqτ_le_m0) (Or.inr hComp)

/-- Baseline plus dynamic-spanner cost envelope without `hComp_bound`, using `n_act ≤ 2 * m₀` and
`n_eff = min n₀ (m₀ + 1)`. -/
lemma bundleCost_env_baseline_parts_noComp (E : SparseCoreEnv) (k m₀ n₀ n_act q_τ : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hn_act : n_act ≤ 2 * m₀) (hqτ_le_m0 : q_τ ≤ m₀) :
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let Λ := bundleLambda (E.P_fn m₀) m₀
    let n_eff := min n₀ (m₀ + 1)
    let T := ((m₀ : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) * logMN ^ (p_max + 1)
    let Tk := ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
      logMN ^ (p_max + 1)
    ((m₀ : ℝ) + (n_act : ℝ) + 1) +
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
        (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
      (q_τ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n_eff * (q_τ : ℝ)) +
      bundleRecoursePerQ E.L (E.P_fn m₀) m₀ n_eff (E.B_fn m₀) * (q_τ : ℝ) ≤
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T ∧
    (∀ q_ep : ℕ,
      90 * (E.L : ℝ) * bundleNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((k : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * bundleUCRatio n_eff * (q_ep : ℝ))) *
          Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n_eff * (q_τ : ℝ) + 2)) ≤
        12600 * (7 : ℝ) ^ p_max * Tk +
        25200 * (7 : ℝ) ^ p_max *
          ((q_ep : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E m₀ * bundleCostMult E m₀) *
            logMN ^ (p_max + 1))) ∧
    (((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * Tk ≤
      P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T ∧
      (0 ≤ T ∧ 0 ≤ Tk ∧ 0 ≤ bundleRecBase E m₀ * bundleCostMult E m₀ ∧ 1 ≤ logMN)) :=
  bundleCost_env_baseline_parts_gen E k m₀ n₀ n_act (min n₀ (m₀ + 1)) q_τ hn₀_pos hqτ_le_m0
    (min_le_cn_mul_m_add_one E m₀ n₀) (log_bundleUCBound_le_min m₀ n₀ hn₀_pos q_τ hqτ_le_m0)
    (Or.inl hn_act)

/-! ## 2. Per-branch and total cost bounds in parameter form -/

private lemma combine_branch_cost_parts (E : SparseCoreEnv) (k M N q_τ : ℕ)
    (hqτ_le_M : q_τ ≤ M)
    {baseCost dynCost : ℝ}
    (hbase : baseCost ≤
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
        (((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)))
    (hdyn : dynCost ≤
      12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        (((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) +
      25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        ((q_τ : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)))
    (hfin : ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi +
        37800 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
        (((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) ≤
      (bundleCoreParams E).c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleCoreParams E).γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (bundleCoreParams E).p_T)
    (hT_nn : 0 ≤ ((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1))
    (hγr_nn : 0 ≤ bundleRecBase E M * bundleCostMult E M)
    (hlog_ge1 : 1 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2)) :
    baseCost + dynCost ≤
      (bundleCoreParams E).c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleCoreParams E).γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (bundleCoreParams E).p_T := by
  set p_max := max E.p_s_hi E.p_t_hi
  set logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
  set T := ((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1)
  set Tk := ((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
    logMN ^ (p_max + 1)
  have hTk_eq : Tk = ((k : ℝ) + 1) * T := by dsimp only [Tk, T]; ring
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hT_le_Tk : T ≤ Tk := by rw [hTk_eq]; nlinarith
  have hcoef_nn : 0 ≤ (7 + E.c_n) + 3 * (7 : ℝ) ^ p_max := by
    have : 0 ≤ E.c_n := by linarith [E.hc_n]
    positivity
  have hbase_k : baseCost ≤ ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * Tk :=
    le_trans hbase (mul_le_mul_of_nonneg_left hT_le_Tk hcoef_nn)
  have hq_m1 : (q_τ : ℝ) ≤ (M : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqτ_le_M
    linarith
  have hfac_nn : 0 ≤ 25200 * (7 : ℝ) ^ p_max *
      (((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1)) := by
    have : 0 ≤ logMN := by linarith
    positivity
  have hq_Tk : 25200 * (7 : ℝ) ^ p_max *
      ((q_τ : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1)) ≤
      25200 * (7 : ℝ) ^ p_max * Tk := by
    have h1 := mul_le_mul_of_nonneg_right hq_m1 hfac_nn
    have hL : (q_τ : ℝ) * (25200 * (7 : ℝ) ^ p_max *
          (((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1))) =
        25200 * (7 : ℝ) ^ p_max *
          ((q_τ : ℝ) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
            logMN ^ (p_max + 1)) := by ring
    have hR : ((M : ℝ) + 1) * (25200 * (7 : ℝ) ^ p_max *
          (((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1))) =
        25200 * (7 : ℝ) ^ p_max * Tk := by dsimp only [Tk]; ring
    linarith [h1, hL, hR]
  have hring : ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * Tk +
      (12600 * (7 : ℝ) ^ p_max * Tk + 25200 * (7 : ℝ) ^ p_max * Tk) =
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * Tk := by ring
  linarith [hbase_k, hdyn, hq_Tk, hring, hfin]

/-- Per-branch cost bound in parameter form at `(M, N)` under `hComp`. -/
theorem bundleRunSeq_cost_le_params_at
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hComp : (N : ℝ) ≤ E.c_n * ((M : ℝ) + 1))
    (j : ℕ) (hj : j < k) :
    let P := bundleCoreParams E
    ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j τ).1.cost : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro P
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  have hCL := bundleRunSeq_cost_le oracle E.C_lsst E.L E.hL (E.P_fn M)
    sparsify hHyps.hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps.hSp ord hOrd j hj
    (E.B_fn M) (hHyps.activeBuckets_card_le hj)
  dsimp only at hCL
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length
  obtain ⟨hbase, hd5, hfin, hT_nn, _, hγr_nn, hlog_ge1⟩ :=
    bundleCost_env_baseline_parts E k M N q_τ hN_pos hqτ_le_M hComp
  exact le_trans hCL
    (combine_branch_cost_parts E k M N q_τ hqτ_le_M hbase (hd5 q_τ) hfin hT_nn hγr_nn hlog_ge1)

/-- Per-branch cost bound in parameter form at `M = (D.G 0).m`, `N = (D.G 0).n` under
`BundleInstanceHyps`. -/
theorem bundleRunSeq_cost_le_params
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleInstanceHyps E oracle sparsify k τ D)
    (j : ℕ) (hj : j < k) :
    let P := bundleCoreParams E
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    ((bundleRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D ord j τ).1.cost : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T :=
  bundleRunSeq_cost_le_params_at E oracle sparsify k (D.G 0).m (D.G 0).n τ D
    ord hk hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hOrd hHyps.toCoreHyps hHyps.hComp_bound j hj

/-- Per-branch cost bound in parameter form at `(M, N)` without `hComp_bound`, using the
active-vertex / `min N (M + 1)` cost bound (`bundleRunSeq_cost_le_active`). -/
theorem bundleRunSeq_cost_le_params_noComp_at
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (j : ℕ) (hj : j < k) :
    let P := bundleCoreParams E
    ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j τ).1.cost : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro P
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  have hCL := bundleRunSeq_cost_le_active oracle E.C_lsst E.L E.hL (E.P_fn M)
    sparsify hHyps.hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps.hSp ord hOrd j hj
    (E.B_fn M) (hHyps.activeBuckets_card_le hj)
  dsimp only at hCL
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length
  obtain ⟨hbase, hd5, hfin, hT_nn, _, hγr_nn, hlog_ge1⟩ :=
    bundleCost_env_baseline_parts_noComp E k M N (activeSubgraph (D.G 0)).n q_τ hN_pos
      (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
  exact le_trans hCL
    (combine_branch_cost_parts E k M N q_τ hqτ_le_M hbase (hd5 q_τ) hfin hT_nn hγr_nn hlog_ge1)

/-- Per-branch cost bound without `hComp_bound` at `M = (D.G 0).m`, `N = (D.G 0).n`. -/
theorem bundleRunSeq_cost_le_params_noComp
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHyps E oracle sparsify k τ D)
    (j : ℕ) (hj : j < k) :
    let P := bundleCoreParams E
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    ((bundleRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D ord j τ).1.cost : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T :=
  bundleRunSeq_cost_le_params_noComp_at E oracle sparsify k
    (D.G 0).m (D.G 0).n τ D ord hk hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hOrd hHyps j hj

/-- Total cost clause of `IsSpecOrdUpTo` for `sparseCoreBundleTool` across all `k` branches,
including the empty-graph case, from any per-branch cost bound. -/
theorem sparseCoreBundleTool_cost_le_of_branch (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hBranch : (D.G 0).V.Nonempty → ∀ j < k,
      let P := bundleCoreParams E
      ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j τ).1.cost : ℝ) ≤
        P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :
    let T := sparseCoreBundleTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    (T.cost (T.runOrdAt k M N D ord τ).1 : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro T P
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreBundleTool_runOrdAt oracle E.C_lsst E.L sparsify k M N D ord hV₀ τ
    set r := (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).runOrdAt k M N D ord τ
    have hne : r.1.isNonempty = true := hrun.1
    have hk_eq : r.1.k = k := hrun.2.1
    have hcost_eq : (T.cost r.1 : ℝ) =
        (Finset.range k).sum fun j =>
          ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j τ).1.cost : ℝ) := by
      change ((if r.1.isNonempty = true then
          (Finset.range r.1.k).sum (fun j => (r.1.trees j).cost) else 0 : ℕ) : ℝ) = _
      simp only [hne, hk_eq, ↓reduceIte, Nat.cast_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hrun.2.2.2.1 j]
    rw [show (T.cost (T.runOrdAt k M N D ord τ).1 : ℝ) = (T.cost r.1 : ℝ) from rfl, hcost_eq]
    calc (Finset.range k).sum
            (fun j => ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j τ).1.cost : ℝ))
        ≤ (Finset.range k).sum (fun _ =>
            P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
              (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :=
          Finset.sum_le_sum fun j hj => hBranch hV₀ j (Finset.mem_range.mp hj)
      _ = (k : ℝ) * (P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by ring
  · have hrunE := bundleTool_runOrdAt_empty oracle E.C_lsst E.L sparsify k M N D ord hV₀ τ
    set r := (sparseCoreBundleTool oracle E.C_lsst E.L sparsify).runOrdAt k M N D ord τ
    have hne : r.1.isNonempty = false := hrunE.1
    have hcost0 : T.cost r.1 = 0 := by
      change (if r.1.isNonempty = true then _ else 0) = 0
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [show (T.cost (T.runOrdAt k M N D ord τ).1 : ℝ) = (T.cost r.1 : ℝ) from rfl, hcost0,
      Nat.cast_zero]
    have hVal := bundleCoreParams_valid E
    have hcT : 0 ≤ P.c_T := hVal.2.2.2.2.2.2.2.2.2
    have hγr : 0 ≤ P.γ_r M := by linarith [hVal.2.2.2.2.2.2.1 M]
    have hlog : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
    positivity

end

end MinCostFlow.SparseCore
