module

public import MinCostFlow.SparseCore.SparseCoreParams
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime Envelope Bridge for `sparseCoreTool`

This file factors out the algebraic comparison between `treeRunSeq_cost_le` and
`(sparseCoreParams E).c_T * (m₀ + 1) * γ_r(m₀) * log^{p_T}(m₀ + n₀ + 2)` per branch `j < k`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma env_core_bounds (E : SparseCoreEnv) (m₀ n₀ Δ₀ dC actCard : ℕ)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (hΔ₀ : (Δ₀ : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (_hdC : (dC : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (hcn : (n₀ : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1)) :
    let P_b := E.P_fn m₀
    (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤ recEnv E m₀ ∧
    (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
      P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤ recEnv E m₀ ∧
    coreUCRatio n₀ Δ₀ ≤ ucRatioHi E m₀ ∧
    coreRecoursePerQ E.L P_b m₀ n₀ Δ₀ actCard ≤ recEnv E m₀ ∧
    3 + P_b.γ_ℓ ≤ recEnv E m₀ ∧
    ((E.L : ℝ) + 1) ≤ costMult E m₀ := by
  intro P_b
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ ucRatioHi E m₀ := ucRatioHi_ge_one E m₀
  have hLen3 : 3 ≤ coreE82Len E.L P_b := coreE82Len_ge_three E.L E.hL P_b
  have hnr1 : 1 ≤ coreNRoot E.L m₀ := coreNRoot_ge_one E.L m₀
  have hUH2 : 2 ≤ coreBucketRecUH E.L P_b m₀ := by
    unfold coreBucketRecUH
    have := P_b.hK_s; have := P_b.hγ_ℓ; have := coreLambdaS_pos P_b m₀
    have : 0 ≤ 12 * (E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ := by
      positivity
    linarith
  have hD0 : 0 ≤ coreBucketRecD E.L P_b m₀ := (coreBucketRec_pos E.L P_b m₀).2.1
  have hKs_nn := P_b.hK_s
  have hγ_nn := P_b.hγ_ℓ
  have hls_nn := coreLambdaS_pos P_b m₀
  have hrem_nn :
      0 ≤ 22 * (E.B_fn m₀ : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ +
        7 + 224 * (Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2)) ^ 2 := by
    have hlog_arg : (1 : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1) + 2 := by
      have : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
      nlinarith [E.hc_n]
    have hlog_nn := Real.log_nonneg hlog_arg
    positivity
  have hsplit : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤ recEnv E m₀ := by
    have ht1 : (10 : ℝ) ≤ (3 + 2 * coreE82Len E.L P_b) *
        coreBucketRecUH E.L P_b m₀ + 2 * coreBucketRecD E.L P_b m₀ := by
      have hUH_nn : 0 ≤ coreBucketRecUH E.L P_b m₀ := by linarith
      nlinarith
    have hmul : (E.B_fn m₀ : ℝ) * 10 * (2 * ucRatioHi E m₀) ≤
        (E.B_fn m₀ : ℝ) * ((3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
          2 * coreBucketRecD E.L P_b m₀) * (2 * ucRatioHi E m₀) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht1 (by positivity)) (by linarith)
    unfold recEnv
    have ht2 : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤
        (E.B_fn m₀ : ℝ) * 10 * (2 * ucRatioHi E m₀) := by
      have : 0 ≤ (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ := by positivity
      linarith
    linarith
  have hKs : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
      P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤ recEnv E m₀ := by
    have hcore_nn : 0 ≤ (E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ := by
      positivity
    have hUH_ge : (E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤
        coreBucketRecUH E.L P_b m₀ := by
      unfold coreBucketRecUH
      linarith
    have hm1 : (E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤
        (3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
          2 * coreBucketRecD E.L P_b m₀ := by
      have hUH_nn : 0 ≤ coreBucketRecUH E.L P_b m₀ := by linarith
      nlinarith
    have hm3 : (E.B_fn m₀ : ℝ) * ((E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ *
          coreLambdaS P_b m₀) * (2 * ucRatioHi E m₀) ≤
        (E.B_fn m₀ : ℝ) * ((3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
          2 * coreBucketRecD E.L P_b m₀) * (2 * ucRatioHi E m₀) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 (by positivity)) (by linarith)
    have hm4 : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
          P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤
        (E.B_fn m₀ : ℝ) * ((E.L : ℝ) * coreNRoot E.L m₀ * P_b.K_s * P_b.γ_ℓ *
          coreLambdaS P_b m₀) * (2 * ucRatioHi E m₀) := by
      have : 0 ≤ (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
          P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ := by positivity
      linarith
    unfold recEnv
    linarith
  have hlog1 : 0 ≤ Real.log ((n₀ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n₀])
  have hlog_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₀]) (by linarith)
  have huc : coreUCRatio n₀ Δ₀ ≤ ucRatioHi E m₀ := by
    unfold coreUCRatio ucRatioHi
    have hsq : (Real.log ((n₀ : ℝ) + 2)) ^ 2 ≤ (Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2)) ^ 2 :=
      pow_le_pow_left₀ hlog1 hlog_le 2
    linarith
  have hrec : coreRecoursePerQ E.L P_b m₀ n₀ Δ₀ actCard ≤ recEnv E m₀ := by
    have hcp := coreBucketRec_pos E.L P_b m₀
    have huc_nn := coreUCRatio_pos n₀ Δ₀
    have h3_nn : 0 ≤ (3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
        2 * coreBucketRecD E.L P_b m₀ := by positivity
    have hmul : (actCard : ℝ) * ((3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
          2 * coreBucketRecD E.L P_b m₀) * (2 * coreUCRatio n₀ Δ₀) ≤
        (E.B_fn m₀ : ℝ) * ((3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
          2 * coreBucketRecD E.L P_b m₀) * (2 * ucRatioHi E m₀) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hB_le h3_nn) (by linarith) (by linarith) (by positivity)
    have hmul2 : 22 * (actCard : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ ≤
        22 * (E.B_fn m₀ : ℝ) * ((E.L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ := by
      gcongr
    have hsq : (Real.log ((n₀ : ℝ) + 2)) ^ 2 ≤ (Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2)) ^ 2 :=
      pow_le_pow_left₀ hlog1 hlog_le 2
    unfold coreRecoursePerQ recEnv
    linarith
  have hγ3 : 3 + P_b.γ_ℓ ≤ recEnv E m₀ := by
    have hγ_le_len : P_b.γ_ℓ ≤ coreE82Len E.L P_b := by
      unfold coreE82Len
      have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ E.L := by
        calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (3 : ℝ) ^ E.L := pow_le_pow_right₀ (by norm_num) E.hL
      have hp : P_b.γ_ℓ ≤ P_b.γ_ℓ ^ (E.L + 1) := by
        calc P_b.γ_ℓ = P_b.γ_ℓ ^ 1 := (pow_one _).symm
          _ ≤ P_b.γ_ℓ ^ (E.L + 1) := pow_le_pow_right₀ P_b.hγ_ℓ (by omega)
      nlinarith [P_b.hγ_ℓ]
    have h4len : 2 * coreE82Len E.L P_b * 2 ≤ recEnv E m₀ := by
      unfold recEnv
      have h1 : 2 * coreE82Len E.L P_b * 2 ≤
          (3 + 2 * coreE82Len E.L P_b) * coreBucketRecUH E.L P_b m₀ +
            2 * coreBucketRecD E.L P_b m₀ := by
        have hUH_nn : 0 ≤ coreBucketRecUH E.L P_b m₀ := by linarith
        nlinarith
      have h2 := mul_le_mul hB1 h1 (by positivity) (by positivity)
      have h3 := mul_le_mul h2 (by linarith : (1 : ℝ) ≤ 2 * ucRatioHi E m₀) zero_le_one (by positivity)
      linarith
    linarith [hLen3]
  have hLp1 : ((E.L : ℝ) + 1) ≤ costMult E m₀ := by
    unfold costMult
    have h1 := coreE_L_ge_one E.L P_b
    have h2 : (1 : ℝ) ≤ (E.d_fn m₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (E.d_fn m₀)]
    have h3 : (1 : ℝ) ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1 := by
      nlinarith [P_b.hK_t, sq_nonneg P_b.γ_ℓ]
    have h4 : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₀) := le_max_left _ _
    have h12 : 1 ≤ coreE_L E.L P_b * ((E.d_fn m₀ : ℝ) + 1) := one_le_mul_of_one_le_of_one_le h1 h2
    have h123 : 1 ≤ coreE_L E.L P_b * ((E.d_fn m₀ : ℝ) + 1) * (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) :=
      one_le_mul_of_one_le_of_one_le h12 h3
    have h1234 : 1 ≤ coreE_L E.L P_b * ((E.d_fn m₀ : ℝ) + 1) *
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L m₀) :=
      one_le_mul_of_one_le_of_one_le h123 h4
    have hL_nn : (0 : ℝ) ≤ (E.L : ℝ) + 1 := by positivity
    exact le_trans (le_mul_of_one_le_left hL_nn h1234) (le_max_right _ _)
  exact ⟨hsplit, hKs, huc, hrec, hγ3, hLp1⟩

lemma cost_piece2a (E : SparseCoreEnv) (m₀ : ℕ)
    (hLp1_cm : ((E.L : ℝ) + 1) ≤ costMult E m₀)
    {logMN : ℝ} (hlogMN_ge1 : 1 ≤ logMN) :
    ((E.L : ℝ) + 1) * (m₀ : ℝ) ≤
      ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hrb1 : 1 ≤ recBase E m₀ := le_trans (by linarith [recEnv_ge_four E m₀]) (le_max_left _ _)
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith [costMult_ge_one E m₀]
  have hlog_pow : 1 ≤ logMN ^ (max E.p_s_hi E.p_t_hi + 1) := one_le_pow₀ hlogMN_ge1
  have h1 : (E.L : ℝ) + 1 ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
    calc (E.L : ℝ) + 1 ≤ costMult E m₀ := hLp1_cm
      _ = 1 * costMult E m₀ * 1 := by ring
      _ ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1) := by
          gcongr
  have h2 := mul_le_mul h1 (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)
  linarith [h2]

lemma cost_piece2b (E : SparseCoreEnv) (m₀ : ℕ)
    (hKs_piece : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ ≤ recEnv E m₀)
    (hγ_le_rec : 3 + (E.P_fn m₀).γ_ℓ ≤ recEnv E m₀)
    (hLp1_cm : ((E.L : ℝ) + 1) ≤ costMult E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN) (hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi)
    (hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi *
      coreLambdaS (E.P_fn m₀) m₀) :
    ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
      2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) ≤
      (3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 1) *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  set p_max := max E.p_s_hi E.p_t_hi
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hpow_le_succ : logMN ^ p_max ≤ logMN ^ (p_max + 1) :=
    pow_le_pow_right₀ hlogMN_ge1 (Nat.le_succ p_max)
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  have hrec_ge4 : 4 ≤ recEnv E m₀ := recEnv_ge_four E m₀
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb1 : 1 ≤ recBase E m₀ := by linarith
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_nn : 0 ≤ recBase E m₀ * costMult E m₀ := mul_nonneg hrb_nn hcm_nn
  have hKt_cm : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) ≤ costMult E m₀ := by
    unfold costMult
    have h1 := coreE_L_ge_one E.L (E.P_fn m₀)
    have h2 : (1 : ℝ) ≤ (E.d_fn m₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (E.d_fn m₀)]
    have h4 : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₀) := le_max_left _ _
    have h5 : (1 : ℝ) ≤ (E.L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E.L]
    have h12 := one_le_mul_of_one_le_of_one_le h1 h2
    have h45 := one_le_mul_of_one_le_of_one_le h4 h5
    have hkt_nn : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) := by
      have := (E.P_fn m₀).hK_t; positivity
    have hkt1_nn : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by linarith
    have hA : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) ≤
        coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) := by
      calc (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2)
          ≤ 1 * ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right h12 hkt1_nn
    have hA_nn : 0 ≤ coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
        ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) :=
      mul_nonneg (by linarith) hkt1_nn
    have hB1 := le_mul_of_one_le_right hA_nn h45
    have hB2 : coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          (max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1)) =
        coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1) := by ring
    exact le_trans (le_trans hA (le_trans hB1 (le_of_eq hB2))) (le_max_right _ _)
  have ht1 : (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ * (m₀ : ℝ) ≤
      (7 : ℝ) ^ p_max * (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) := by
    have hΛp : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ (p_max + 1) :=
      le_trans hΛ_bound (mul_le_mul_of_nonneg_left hpow_le_succ (by positivity))
    have hcm_γr : costMult E m₀ ≤ recBase E m₀ * costMult E m₀ := by
      calc costMult E m₀ = 1 * costMult E m₀ := (one_mul _).symm
        _ ≤ recBase E m₀ * costMult E m₀ := mul_le_mul_of_nonneg_right hrb1 hcm_nn
    have hprod := mul_le_mul (le_trans hKt_cm hcm_γr) hΛp hΛ_nn hγr_nn
    have hmul_m := mul_le_mul hprod (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)
    linarith [hmul_m]
  have ht2 : (3 + (E.P_fn m₀).γ_ℓ) * (m₀ : ℝ) ≤
      ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) := by
    have h1 : recEnv E m₀ ≤ recBase E m₀ * costMult E m₀ := by
      calc recEnv E m₀ ≤ recBase E m₀ := hrb_ge
        _ = recBase E m₀ * 1 := (mul_one _).symm
        _ ≤ recBase E m₀ * costMult E m₀ := mul_le_mul_of_nonneg_left hcm_ge1 hrb_nn
    have hprod := mul_le_mul (le_trans hγ_le_rec h1) hlog_pow_ge1 zero_le_one hγr_nn
    have hmul_m := mul_le_mul hprod (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn (by positivity)
    linarith [hmul_m]
  have ht3 : 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ * (m₀ : ℝ) ≤
      2 * (7 : ℝ) ^ p_max *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) := by
    have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
    have hucHi1 : 1 ≤ ucRatioHi E m₀ := ucRatioHi_ge_one E m₀
    have hL1 : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
    have hnr1 : 1 ≤ coreNRoot E.L m₀ := coreNRoot_ge_one E.L m₀
    have hK_nn : 0 ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ :=
      mul_nonneg (E.P_fn m₀).hK_s (by linarith [(E.P_fn m₀).hγ_ℓ])
    have hls_nn := coreLambdaS_pos (E.P_fn m₀) m₀
    have hKs1 : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ ≤ recEnv E m₀ := by
      have hBu := one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hB1 hucHi1) (one_le_mul_of_one_le_of_one_le hL1 hnr1)
      have hks_nn : 0 ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ :=
        mul_nonneg hK_nn hls_nn
      have hmul := mul_le_mul_of_nonneg_right hBu hks_nn
      have hEq1 : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ =
          1 * ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀) := (one_mul _).symm
      have hEq2 : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * ((E.L : ℝ) * coreNRoot E.L m₀) *
            ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀) =
          (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
            (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ := by ring
      exact le_trans (le_of_eq hEq1) (le_trans hmul (le_trans (le_of_eq hEq2) hKs_piece))
    have hKΛ : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ ≤
        (7 : ℝ) ^ p_max * recBase E m₀ * logMN ^ (p_max + 1) := by
      calc (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ
          ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
              ((7 : ℝ) ^ p_max * logMN ^ p_max * coreLambdaS (E.P_fn m₀) m₀) :=
              mul_le_mul_of_nonneg_left hΛ_mul_Λs hK_nn
        _ = (7 : ℝ) ^ p_max * ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
              coreLambdaS (E.P_fn m₀) m₀) * logMN ^ p_max := by ring
        _ ≤ (7 : ℝ) ^ p_max * recBase E m₀ * logMN ^ (p_max + 1) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hKs1 hrb_ge) (by positivity))
              hpow_le_succ (pow_nonneg hlogMN_nn _) (mul_nonneg (by positivity) hrb_nn)
    have hprod : ((E.L : ℝ) + 1) * ((E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) ≤
        (7 : ℝ) ^ p_max * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) := by
      have h1 := mul_le_mul hLp1_cm hKΛ (mul_nonneg hK_nn hΛ_nn) hcm_nn
      linarith
    have hL1p : (1 : ℝ) ≤ (E.L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E.L]
    have hKΛ_nn : 0 ≤ (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ := mul_nonneg hK_nn hΛ_nn
    have hprod' : (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ ≤
        (7 : ℝ) ^ p_max * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) :=
      le_trans (le_mul_of_one_le_left hKΛ_nn hL1p) hprod
    have hmul_m := mul_le_mul hprod' (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn
      (mul_nonneg (mul_nonneg (by positivity) hγr_nn) (pow_nonneg hlogMN_nn _))
    linarith [hmul_m]
  have hrew3 : ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
        2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
      (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ * (m₀ : ℝ) +
        (3 + (E.P_fn m₀).γ_ℓ) * (m₀ : ℝ) +
        2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ * (m₀ : ℝ) := by ring
  linarith [hrew3, ht1, ht2, ht3]

lemma cost_piece34 (E : SparseCoreEnv) (m₀ n₀ Δ₀ actCard q_τ : ℕ)
    (hq_m0 : q_τ ≤ m₀)
    (_hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (huc_le : coreUCRatio n₀ Δ₀ ≤ ucRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤ recEnv E m₀)
    (hRec_le : coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ Δ₀ actCard ≤ recEnv E m₀)
    {logMN : ℝ} (hlogMN_ge1 : 1 ≤ logMN) :
    let T := ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)
    (q_τ : ℝ) ≤ T ∧
    2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) ≤ 2 * T ∧
    coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ Δ₀ actCard * (q_τ : ℝ) ≤ T := by
  intro T
  set p_max := max E.p_s_hi E.p_t_hi
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ ucRatioHi E m₀ := ucRatioHi_ge_one E m₀
  have hrec_ge4 : 4 ≤ recEnv E m₀ := recEnv_ge_four E m₀
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_nn : 0 ≤ recBase E m₀ * costMult E m₀ := mul_nonneg hrb_nn hcm_nn
  have hγr_ge1 : 1 ≤ recBase E m₀ * costMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith) hcm_ge1
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  have hm_1_nn : (0 : ℝ) ≤ (m₀ : ℝ) + 1 := by linarith
  have hT_pre_nn : 0 ≤ ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) :=
    mul_nonneg hm_1_nn hγr_nn
  have hr_γr : recEnv E m₀ ≤ recBase E m₀ * costMult E m₀ := by
    calc recEnv E m₀ ≤ recBase E m₀ := hrb_ge
      _ = recBase E m₀ * 1 := (mul_one _).symm
      _ ≤ recBase E m₀ * costMult E m₀ := mul_le_mul_of_nonneg_left hcm_ge1 hrb_nn
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq_m0
  have hq_nn : 0 ≤ (q_τ : ℝ) := Nat.cast_nonneg _
  have hm_le_T : (m₀ : ℝ) ≤ T := by
    have h1_le := one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
    calc (m₀ : ℝ) ≤ ((m₀ : ℝ) + 1) := by linarith
      _ = ((m₀ : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀ * logMN ^ (p_max + 1)) :=
          mul_le_mul_of_nonneg_left h1_le hm_1_nn
      _ = T := by dsimp only [T]; ring
  have huc_b : coreUCRatio n₀ Δ₀ * (q_τ : ℝ) ≤ ucRatioHi E m₀ * (m₀ : ℝ) :=
    mul_le_mul huc_le hqR hq_nn (by linarith)
  have huc_rec : ucRatioHi E m₀ ≤ recBase E m₀ * costMult E m₀ := by
    have hBu : ucRatioHi E m₀ ≤ (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 := by
      have h10 : 1 ≤ (E.B_fn m₀ : ℝ) * 10 := by nlinarith
      calc ucRatioHi E m₀ = 1 * ucRatioHi E m₀ := (one_mul _).symm
        _ ≤ ((E.B_fn m₀ : ℝ) * 10) * ucRatioHi E m₀ :=
            mul_le_mul_of_nonneg_right h10 (by linarith)
        _ = (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 := by ring
    exact le_trans (le_trans hBu hrec_split) hr_γr
  have huc_term : 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) ≤ 2 * T := by
    have hm1 : ucRatioHi E m₀ * (m₀ : ℝ) ≤ (recBase E m₀ * costMult E m₀) * ((m₀ : ℝ) + 1) :=
      mul_le_mul huc_rec (by linarith) hm_nn hγr_nn
    have hm2 := mul_le_mul_of_nonneg_left hlog_pow_ge1 hT_pre_nn
    have hm2' : ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) ≤ T := by
      calc ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀)
          = ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * 1 := (mul_one _).symm
        _ ≤ T := hm2
    linarith [huc_b, hm1, hm2']
  have h4_le : coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ Δ₀ actCard * (q_τ : ℝ) ≤
      recEnv E m₀ * (m₀ : ℝ) :=
    mul_le_mul hRec_le hqR hq_nn (by linarith)
  have hr_term : recEnv E m₀ * (m₀ : ℝ) ≤ T := by
    have hrm : recEnv E m₀ * (m₀ : ℝ) ≤ ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) := by
      have h1 := mul_le_mul hr_γr (show (m₀ : ℝ) ≤ (m₀ : ℝ) + 1 by linarith) hm_nn hγr_nn
      linarith [h1]
    have hm2 := mul_le_mul_of_nonneg_left hlog_pow_ge1 hT_pre_nn
    have hm2' : ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) ≤ T := by
      calc ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀)
          = ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * 1 := (mul_one _).symm
        _ ≤ T := hm2
    exact le_trans hrm hm2'
  exact ⟨le_trans hqR hm_le_T, huc_term, le_trans h4_le hr_term⟩

lemma cost_piece5_split (E : SparseCoreEnv) (m₀ n₀ Δ₀ dC actCard q_ep q_τ : ℕ)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (hdC_le : (dC : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (huc_le : coreUCRatio n₀ Δ₀ ≤ ucRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤ recEnv E m₀)
    (hKs_piece : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ ≤ recEnv E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN)
    (hlog_uc : Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2) ≤ 7 * logMN)
    (_hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi) :
    90 * (E.L : ℝ) * coreNRoot E.L m₀ *
      ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) * coreE_L E.L (E.P_fn m₀) *
      ((dC : ℝ) + 1) * Λ *
      (20 * ((m₀ : ℝ) + (actCard : ℝ) * (2 * coreUCRatio n₀ Δ₀ * (q_ep : ℝ))) *
        Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2)) ≤
      12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)) +
      25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        ((q_ep : ℝ) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  set p_max := max E.p_s_hi E.p_t_hi
  set uc_ep := 2 * coreUCRatio n₀ Δ₀ * (q_ep : ℝ)
  set ucBound := 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ)
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hB1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) := by exact_mod_cast E.hB_pos m₀
  have hucHi1 : 1 ≤ ucRatioHi E m₀ := ucRatioHi_ge_one E m₀
  have hrec_ge4 : 4 ≤ recEnv E m₀ := recEnv_ge_four E m₀
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hEL_nn : 0 ≤ coreE_L E.L (E.P_fn m₀) := by linarith [coreE_L_ge_one E.L (E.P_fn m₀)]
  have hNR_nn : 0 ≤ coreNRoot E.L m₀ := by linarith [coreNRoot_ge_one E.L m₀]
  have hKt_nn := (E.P_fn m₀).hK_t
  have hKs_nn := (E.P_fn m₀).hK_s
  have huc_pos := coreUCRatio_pos n₀ Δ₀
  have huc_ep_nn : 0 ≤ uc_ep := mul_nonneg (mul_nonneg zero_le_two huc_pos) (Nat.cast_nonneg _)
  have huc_b : uc_ep ≤ 2 * (ucRatioHi E m₀ * (q_ep : ℝ)) := by
    have h1 : coreUCRatio n₀ Δ₀ * (q_ep : ℝ) ≤ ucRatioHi E m₀ * (q_ep : ℝ) :=
      mul_le_mul_of_nonneg_right huc_le (Nat.cast_nonneg _)
    dsimp only [uc_ep]
    linarith
  have h1m : (m₀ : ℝ) ≤ (m₀ : ℝ) * (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ := by
    have hBu1 := one_le_mul_of_one_le_of_one_le hB1 hucHi1
    calc (m₀ : ℝ) = (m₀ : ℝ) * 1 := (mul_one _).symm
      _ ≤ (m₀ : ℝ) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) :=
          mul_le_mul_of_nonneg_left hBu1 (Nat.cast_nonneg _)
      _ = _ := by ring
  have h2m : (actCard : ℝ) * uc_ep ≤ 2 * (E.B_fn m₀ : ℝ) * (ucRatioHi E m₀ * (q_ep : ℝ)) := by
    have h1 := mul_le_mul hB_le huc_b huc_ep_nn (by linarith)
    linarith
  have hm_uc : (m₀ : ℝ) + (actCard : ℝ) * uc_ep ≤
      (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) := by
    have hBu_ge1 : (1 : ℝ) ≤ (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ :=
      one_le_mul_of_one_le_of_one_le hB1 hucHi1
    linarith [h1m, h2m, hBu_ge1]
  have hcore_factor :
      (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
          ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) ≤ recBase E m₀ * costMult E m₀ := by
    have hEL_le_cm : coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
        max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.P_fn m₀).K_t + 1) ≤ costMult E m₀ := by
      unfold costMult
      have hd_le1 : (dC : ℝ) + 1 ≤ (E.d_fn m₀ : ℝ) + 1 := by linarith
      have hL1 : (1 : ℝ) ≤ (E.L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E.L]
      have hK1 : (E.P_fn m₀).K_t + 1 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
        nlinarith [(E.P_fn m₀).hK_t, sq_nonneg (E.P_fn m₀).γ_ℓ]
      have h1 : coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) ≤
          coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hd_le1 hEL_nn
      have h2 := mul_le_mul h1 hK1 (by linarith) (by positivity)
      have h3 := mul_le_mul_of_nonneg_right h2
        (by positivity : 0 ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₀))
      have h3_nn : 0 ≤ coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * coreNRoot E.L m₀) := by
        have : 0 ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
          have := sq_nonneg (E.P_fn m₀).γ_ℓ; positivity
        have : 0 ≤ (E.d_fn m₀ : ℝ) + 1 := by positivity
        positivity
      have hpre1 : coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
            max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.P_fn m₀).K_t + 1) =
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * ((E.P_fn m₀).K_t + 1) *
            max 1 ((E.L : ℝ) * coreNRoot E.L m₀) := by ring
      exact le_trans (le_of_eq hpre1) (le_trans h3 (le_trans (le_mul_of_one_le_right h3_nn hL1)
        (le_max_right _ _)))
    have hKs_le_rb : (E.L : ℝ) * coreNRoot E.L m₀ * (E.P_fn m₀).K_s *
        ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) ≤ recBase E m₀ := by
      have hγls := one_le_mul_of_one_le_of_one_le (E.P_fn m₀).hγ_ℓ (coreLambdaS_ge_one (E.P_fn m₀) m₀)
      have hfac : 0 ≤ (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
          (E.P_fn m₀).K_s := by positivity
      have h1 := le_mul_of_one_le_right hfac hγls
      have hEq : (E.L : ℝ) * coreNRoot E.L m₀ * (E.P_fn m₀).K_s *
            ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) =
          (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
            (E.P_fn m₀).K_s := by ring
      have hKs' : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
            (E.P_fn m₀).K_s * ((E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀) ≤ recEnv E m₀ := by
        simpa only [mul_assoc] using hKs_piece
      exact le_trans (le_of_eq hEq) (le_trans h1 (le_trans hKs' hrb_ge))
    have hsplit_Kt :
        (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) ≤
        ((E.P_fn m₀).K_t + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L m₀) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) +
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
          ((E.L : ℝ) * coreNRoot E.L m₀ * (E.P_fn m₀).K_s * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀)) := by
      have hle_max : (E.L : ℝ) * coreNRoot E.L m₀ ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₀) :=
        le_max_right _ _
      have hkt_nn : 0 ≤ (E.P_fn m₀).K_t + 1 := by linarith
      have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_max hkt_nn)
        (by positivity : 0 ≤ coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
          ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀))
      linarith
    have hT1 :
        ((E.P_fn m₀).K_t + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L m₀) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
          ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) ≤ costMult E m₀ * (recBase E m₀ / 2) := by
      have hBu_rb : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ ≤ recBase E m₀ / 2 := by linarith
      have hmul := mul_le_mul hEL_le_cm hBu_rb (by positivity) hcm_nn
      linarith
    have hT2 :
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) *
          ((E.L : ℝ) * coreNRoot E.L m₀ * (E.P_fn m₀).K_s *
            ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀)) ≤ costMult E m₀ * (recBase E m₀ / 2) := by
      have hcm2 : coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) ≤ costMult E m₀ / 2 := by
        have hL1 : (2 : ℝ) ≤ (E.L : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
          linarith
        have hKt1 : (1 : ℝ) ≤ (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1 := by
          nlinarith [(E.P_fn m₀).hK_t, sq_nonneg (E.P_fn m₀).γ_ℓ]
        have hnr1' : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₀) := le_max_left _ _
        have hd_le1 : (dC : ℝ) + 1 ≤ (E.d_fn m₀ : ℝ) + 1 := by linarith
        have hE_le : coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) ≤
            coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hd_le1 hEL_nn
        have h2mul : (2 : ℝ) ≤ ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
            max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1) := by
          calc (2 : ℝ) = 1 * 2 := by norm_num
            _ ≤ ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
                  max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1) :=
                mul_le_mul (one_le_mul_of_one_le_of_one_le hKt1 hnr1') hL1 (by norm_num) (by positivity)
        have hm2 := mul_le_mul hE_le h2mul zero_le_two (by positivity)
        unfold costMult
        have hrr : coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
              (((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
                max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1)) =
            coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
              ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
              max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1) := by ring
        rw [hrr] at hm2
        linarith [le_max_right (1 : ℝ) (coreE_L E.L (E.P_fn m₀) * ((E.d_fn m₀ : ℝ) + 1) *
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * coreNRoot E.L m₀) * ((E.L : ℝ) + 1))]
      have hmul := mul_le_mul hcm2 hKs_le_rb (by positivity) (by linarith)
      linarith
    linarith
  have hcore_nn : 0 ≤ (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
      coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) := by positivity
  have hlog_uc_nn : 0 ≤ Real.log ((m₀ : ℝ) + ucBound + 2) :=
    Real.log_nonneg (by
      have : 0 ≤ ucBound := mul_nonneg (mul_nonneg zero_le_two huc_pos) (Nat.cast_nonneg _)
      linarith [Nat.cast_nonneg (α := ℝ) m₀])
  have hm_uc_nn : 0 ≤ (m₀ : ℝ) + (actCard : ℝ) * uc_ep := by positivity
  have hcoeff_sum_nn : 0 ≤ (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN) := by positivity
  have hinner_prod :
      ((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1)) *
        (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2)) ≤
      (recBase E m₀ * costMult E m₀) * ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN)) := by
    have h1 := mul_le_mul hm_uc hlog_uc hlog_uc_nn (by positivity)
    have h2_eq : ((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1)) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) * (7 * logMN)) =
        (((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN) *
          ((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
            coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀)) := by
      ring
    have h2 : ((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1)) *
          ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * ((E.B_fn m₀ : ℝ) * ucRatioHi E m₀) * (7 * logMN)) ≤
        (recBase E m₀ * costMult E m₀) * ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN)) := by
      rw [h2_eq]
      have hmul := mul_le_mul_of_nonneg_left hcore_factor hcoeff_sum_nn
      linarith [hmul]
    exact le_trans (mul_le_mul_of_nonneg_left h1 hcore_nn) h2
  have hfull :
      90 * 20 * Λ *
        (((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1)) *
          (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2))) ≤
      90 * 20 * ((7 : ℝ) ^ p_max * logMN ^ p_max) *
        ((recBase E m₀ * costMult E m₀) * ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN))) := by
    have hA : 90 * 20 * Λ ≤ 90 * 20 * ((7 : ℝ) ^ p_max * logMN ^ p_max) := by linarith
    exact mul_le_mul hA hinner_prod
      (mul_nonneg hcore_nn (mul_nonneg hm_uc_nn hlog_uc_nn)) (by positivity)
  have hre1 :
      90 * (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2)) =
      90 * 20 * Λ *
        (((E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
          coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1)) *
          (((m₀ : ℝ) + (actCard : ℝ) * uc_ep) * Real.log ((m₀ : ℝ) + ucBound + 2))) := by
    ring
  have hre2 :
      90 * 20 * ((7 : ℝ) ^ p_max * logMN ^ p_max) *
        ((recBase E m₀ * costMult E m₀) * ((((m₀ : ℝ) + 1) + 2 * (q_ep : ℝ)) * (7 * logMN))) =
      12600 * (7 : ℝ) ^ p_max *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) +
      25200 * (7 : ℝ) ^ p_max *
        ((q_ep : ℝ) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) := by
    rw [show p_max + 1 = Nat.succ p_max from rfl, pow_succ]
    ring
  linarith [hre1, hre2, hfull]

lemma cost_piece5 (E : SparseCoreEnv) (m₀ n₀ Δ₀ dC actCard q_τ : ℕ)
    (hq_m0 : q_τ ≤ m₀)
    (hB_le : (actCard : ℝ) ≤ (E.B_fn m₀ : ℝ))
    (hdC_le : (dC : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (huc_le : coreUCRatio n₀ Δ₀ ≤ ucRatioHi E m₀)
    (hrec_split : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * 10 ≤ recEnv E m₀)
    (hKs_piece : (E.B_fn m₀ : ℝ) * ucRatioHi E m₀ * (E.L : ℝ) * coreNRoot E.L m₀ *
      (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * coreLambdaS (E.P_fn m₀) m₀ ≤ recEnv E m₀)
    {logMN Λ : ℝ} (hlogMN_ge1 : 1 ≤ logMN)
    (hlog_uc : Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2) ≤ 7 * logMN)
    (hΛ_nn : 0 ≤ Λ)
    (hΛ_bound : Λ ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi * logMN ^ max E.p_s_hi E.p_t_hi) :
    90 * (E.L : ℝ) * coreNRoot E.L m₀ *
      ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) * coreE_L E.L (E.P_fn m₀) *
      ((dC : ℝ) + 1) * Λ *
      (20 * ((m₀ : ℝ) + (actCard : ℝ) * (2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ))) *
        Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2)) ≤
      37800 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by
  have hs := cost_piece5_split E m₀ n₀ Δ₀ dC actCard q_τ q_τ hB_le hdC_le huc_le
    hrec_split hKs_piece hlogMN_ge1 hlog_uc hΛ_nn hΛ_bound
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq_m0
    linarith
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith [recEnv_ge_four E m₀]
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith [costMult_ge_one E m₀]
  have hlogMN_nn : 0 ≤ logMN := by linarith
  have hfactor_nn : 0 ≤ 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      ((recBase E m₀ * costMult E m₀) * logMN ^ (max E.p_s_hi E.p_t_hi + 1)) := by positivity
  nlinarith [hs, hqR, hfactor_nn]

lemma restartCost_le_params (E : SparseCoreEnv) (m₀ n₀ Δ₀ m_cur bucketCost : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hm_cur : m_cur ≤ 2 * m₀)
    (hΔ₀ : (Δ₀ : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (hcn : (n₀ : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1))
    (hbuck : (bucketCost : ℝ) ≤
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * coreLambda (E.P_fn m₀) m₀ +
        3 + (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
        coreLambda (E.P_fn m₀) m₀) * (m₀ : ℝ)) :
    let P := sparseCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let T := ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T ∧
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T ≤ P.c_T * T := by
  intro P p_max logMN T
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    have := lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))
    linarith
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨_, hKs_piece, _, _, hγ_le_rec, hLp1_cm⟩ :=
    env_core_bounds E m₀ n₀ Δ₀ 0 (E.B_fn m₀) le_rfl hΔ₀
      (by exact_mod_cast Nat.zero_le (E.d_fn m₀)) hcn
  set Λ := coreLambda (E.P_fn m₀) m₀
  have hΛ_nn : 0 ≤ Λ := by linarith [coreLambda_ge_one (E.P_fn m₀) m₀]
  have hΛ_bound : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max := by
    unfold Λ coreLambda
    have hlogC := log_coreNMax_le m₀ n₀ hn₀_pos
    have hp_le : max (E.P_fn m₀).p_s (E.P_fn m₀).p_t ≤ p_max :=
      max_le (le_trans (E.hp_s m₀) (le_max_left _ _)) (le_trans (E.hp_t m₀) (le_max_right _ _))
    have h1 : 1 ≤ 7 * logMN := by linarith
    have hbase : 0 ≤ 1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t
        ≤ (7 * logMN) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t := pow_le_pow_left₀ hbase hlogC _
      _ ≤ (7 * logMN) ^ p_max := pow_le_pow_right₀ h1 hp_le
      _ = (7 : ℝ) ^ p_max * logMN ^ p_max := by rw [mul_pow]
  have hΛs_ge1 : 1 ≤ coreLambdaS (E.P_fn m₀) m₀ := coreLambdaS_ge_one _ m₀
  have hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max * coreLambdaS (E.P_fn m₀) m₀ := by
    have := mul_le_mul_of_nonneg_left hΛs_ge1 (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ p_max * logMN ^ p_max)
    linarith
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith [recEnv_ge_four E m₀]
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_ge1 : 1 ≤ recBase E m₀ * costMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith [recEnv_ge_four E m₀]) hcm_ge1
  have h1_le : (1 : ℝ) ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) :=
    one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
  have hm_cur_T : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have hmc : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * ((m₀ : ℝ) + 1) := by
      have : (m_cur : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hm_cur
      push_cast; linarith
    have hstep := mul_le_mul_of_nonneg_left h1_le (show 0 ≤ 2 * ((m₀ : ℝ) + 1) by linarith)
    have hEq : 2 * ((m₀ : ℝ) + 1) * ((recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) = 2 * T := by
      dsimp only [T]; ring
    linarith
  have hp2a := cost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := cost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn hΛ_bound hΛ_mul_Λs
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
  refine ⟨htot, ?_⟩
  have hT_nn : 0 ≤ T := by
    dsimp only [T]
    have : 0 ≤ logMN := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg this _)
  have hcT : (4 + 3 * (7 : ℝ) ^ p_max) + 12600 * (7 : ℝ) ^ p_max ≤ P.c_T := by
    dsimp only [P, sparseCoreParams, p_max]
    linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := max E.p_s_hi E.p_t_hi), E.hc_n]
  calc ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T
      ≤ (4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * T := by linarith [htot]
    _ ≤ P.c_T * T := mul_le_mul_of_nonneg_right hcT hT_nn

lemma cost_env_baseline_parts (E : SparseCoreEnv) (m₀ n₀ Δ₀ dC q_τ : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hqτ_le_m0 : q_τ ≤ m₀) (hΔ₀_raw : Δ₀ ≤ 2 * m₀)
    (hΔ₀_le : (Δ₀ : ℝ) ≤ (E.d_fn m₀ : ℝ)) (hdC_le : (dC : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (hComp : (n₀ : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1)) :
    let P := sparseCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let Λ := coreLambda (E.P_fn m₀) m₀
    let T := ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)
    ((m₀ : ℝ) + (n₀ : ℝ) + 1) +
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
        (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
      (q_τ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) +
      coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ Δ₀ (E.B_fn m₀) * (q_τ : ℝ) ≤
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T ∧
    (∀ q_ep : ℕ,
      90 * (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * coreUCRatio n₀ Δ₀ * (q_ep : ℝ))) *
          Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2)) ≤
        12600 * (7 : ℝ) ^ p_max * T +
        25200 * (7 : ℝ) ^ p_max *
          ((q_ep : ℝ) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1))) ∧
    (((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * T ≤
      P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T ∧
      (0 ≤ T ∧ 0 ≤ recBase E m₀ * costMult E m₀ ∧ 1 ≤ logMN)) := by
  intro P p_max logMN Λ T
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    have := lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))
    linarith
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨hrec_split, hKs_piece, huc_le, hRec_le, hγ_le_rec, hLp1_cm⟩ :=
    env_core_bounds E m₀ n₀ Δ₀ dC (E.B_fn m₀) le_rfl hΔ₀_le hdC_le hComp
  have hΛ_nn : 0 ≤ Λ := by linarith [coreLambda_ge_one (E.P_fn m₀) m₀]
  have hΛ_bound : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max := by
    unfold Λ coreLambda
    have hlogC := log_coreNMax_le m₀ n₀ hn₀_pos
    have hp_le : max (E.P_fn m₀).p_s (E.P_fn m₀).p_t ≤ p_max :=
      max_le (le_trans (E.hp_s m₀) (le_max_left _ _)) (le_trans (E.hp_t m₀) (le_max_right _ _))
    have h1 : 1 ≤ 7 * logMN := by linarith
    have hbase : 0 ≤ 1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t
        ≤ (7 * logMN) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t := pow_le_pow_left₀ hbase hlogC _
      _ ≤ (7 * logMN) ^ p_max := pow_le_pow_right₀ h1 hp_le
      _ = (7 : ℝ) ^ p_max * logMN ^ p_max := by rw [mul_pow]
  have hΛs_ge1 : 1 ≤ coreLambdaS (E.P_fn m₀) m₀ := coreLambdaS_ge_one _ m₀
  have hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max * coreLambdaS (E.P_fn m₀) m₀ := by
    have := mul_le_mul_of_nonneg_left hΛs_ge1 (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ p_max * logMN ^ p_max)
    linarith
  have hrec_ge4 : 4 ≤ recEnv E m₀ := recEnv_ge_four E m₀
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_ge1 : 1 ≤ recBase E m₀ * costMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith) hcm_ge1
  have hp1 : (m₀ : ℝ) + (n₀ : ℝ) + 1 ≤ (1 + E.c_n) * T := by
    have hmn : (m₀ : ℝ) + (n₀ : ℝ) + 1 ≤ (1 + E.c_n) * ((m₀ : ℝ) + 1) := by linarith [hComp]
    have h1_le : (1 : ℝ) ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) :=
      one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
    have hcn_nn : 0 ≤ (1 + E.c_n) * ((m₀ : ℝ) + 1) := by linarith [E.hc_n]
    have hstep := mul_le_mul_of_nonneg_left h1_le hcn_nn
    have hEq : (1 + E.c_n) * ((m₀ : ℝ) + 1) * ((recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) =
        (1 + E.c_n) * T := by dsimp only [T]; ring
    exact le_trans hmn (by linarith [hstep, hEq])
  have hp2a := cost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := cost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn hΛ_bound hΛ_mul_Λs
  obtain ⟨hp3, hp3b, hp4⟩ := cost_piece34 E m₀ n₀ Δ₀ (E.B_fn m₀) q_τ
    hqτ_le_m0 le_rfl huc_le hrec_split hRec_le hlogMN_ge1
  have hlog_uc := log_ucBound_le m₀ n₀ hn₀_pos Δ₀ hΔ₀_raw q_τ hqτ_le_m0
  have hinit_split :
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
        ((E.L : ℝ) + 1) * (m₀ : ℝ) +
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
            2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) := by ring
  have hbase_le :
      ((m₀ : ℝ) + (n₀ : ℝ) + 1) +
        ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
        (q_τ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) +
        coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ Δ₀ (E.B_fn m₀) * (q_τ : ℝ) ≤
          ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by
    have hsum_eq : (1 + E.c_n) * T + (T + (3 * (7 : ℝ) ^ p_max + 1) * T) + T + 2 * T + T =
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by ring
    linarith [hinit_split, hp1, hp2a, hp2b, hp3, hp3b, hp4, hsum_eq]
  refine ⟨hbase_le, fun q_ep => ?_, ?_⟩
  · exact cost_piece5_split E m₀ n₀ Δ₀ dC (E.B_fn m₀) q_ep q_τ
      le_rfl hdC_le huc_le hrec_split hKs_piece hlogMN_ge1 hlog_uc hΛ_nn hΛ_bound
  · have hcT_le : (7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max ≤ P.c_T := by
      dsimp only [P, sparseCoreParams]
      linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := p_max), E.hc_n]
    have hT_nn : 0 ≤ T := by
      dsimp only [T]
      have hlogMN_nn : 0 ≤ logMN := by linarith
      exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg hlogMN_nn _)
    have hFinal_eq : P.c_T * T =
        P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T := by
      dsimp only [T, P, sparseCoreParams, p_max]
      ring
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hcT_le hT_nn) (le_of_eq hFinal_eq),
      hT_nn, mul_nonneg hrb_nn hcm_nn, hlogMN_ge1⟩

lemma treeRunSeq_cost_le_params (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : SparseCoreInstanceHyps E oracle sparsify k τ D)
    (j : ℕ) (hj : j < k) :
    let P := sparseCoreParams E
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j τ).1.cost : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T := by
  intro P m₀ n₀
  have hn₀_pos : 1 ≤ n₀ := Finset.card_pos.mpr hV₀
  have hqτ_le_m0 : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ m₀ :=
    (updateThreshold_le_div_k hk hG₀ hThresh τ le_rfl).2
  have hCL := treeRunSeq_cost_le oracle E.C_lsst E.L E.hL (E.P_fn m₀)
    sparsify hHyps.hLSST k m₀ n₀ τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hHyps.hSp j hj
    (E.B_fn m₀) (hHyps.hB_bound j hj)
  dsimp only at hCL
  set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
  set ts₀ := fun C => initTildeState (cs₀.compSt C)
  set dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length
  obtain ⟨hbase, hd5, hfin, _, hγr_nn, hlogMN_ge1⟩ := cost_env_baseline_parts E m₀ n₀ (D.G 0).maxDeg
    dC q_τ hn₀_pos hqτ_le_m0 (maxDeg_le_two_m (D.G 0))
    (by exact_mod_cast hHyps.hDeg_bound.1) (by exact_mod_cast hHyps.hDeg_bound.2 j hj)
    hHyps.hComp_bound
  have hd5_tau := hd5 q_τ
  have hq_m1 : (q_τ : ℝ) ≤ (m₀ : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hqτ_le_m0
    linarith
  have hfac_nn : 0 ≤ 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      ((recBase E m₀ * costMult E m₀) * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
    have : 0 ≤ Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by linarith
    positivity
  have hq_T : 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      ((q_τ : ℝ) * (recBase E m₀ * costMult E m₀) * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) ≤
      25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
    nlinarith [hq_m1, hfac_nn]
  have hring :
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
          (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) *
            (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) +
        (12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) *
            (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) +
        25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) *
            (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1))) =
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi +
          37800 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
        (((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) *
          (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by ring
  linarith [hCL, hbase, hd5_tau, hq_T, hfin, hring]

end

end MinCostFlow.SparseCore
