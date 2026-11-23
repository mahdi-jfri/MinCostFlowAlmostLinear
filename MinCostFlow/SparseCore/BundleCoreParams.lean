module

public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.BundleConstants
public import MinCostFlow.SparseCore.BundleTool
import MinCostFlow.DynSpanner.Examples
import MinCostFlow.LSF.Theorem22
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter Envelope and Omitted Hypotheses for Lemma 5.17 on Bundle Graphs

This file builds the degree-free parameter envelope `bundleCoreParams E` for
`sparseCoreBundleTool` (paper Lemma 5.17, pages 23–24). It reuses
`SparseCoreEnv` without reading `d_fn` or `hd_mono`, so those fields can be removed once the old
quotient pipeline is retired.

The main definitions and results are:
* `bundleUCRatioHi`, `bundleRecEnv`, `bundleGammaLEnv`, `bundleEncEnv`, `bundleRecBase`,
  `bundleCostMult`, and `bundleCoreParams E : SparseCoreParams` with `bundleCoreParams_valid`.
* Parameter comparisons for the restart specification: `bundleGammaLEnv_le_bundleRecEnv`,
  `bundleCostMult_ge_four`, and `four_mul_bundleEncEnv_le_gamma_r`.
* `BundleCoreHypsAt`, `BundleCoreHyps`, and `BundleInstanceHyps`: per-instance hypotheses with
  bucket count on `(initBundleTree ..).activeBuckets` and no degree bound, plus non-vacuity
  witnesses `bundleCoreHypsAt_of_B_ge_m` and `exists_bundleCoreHypsAt`.
* Empty-graph run helper (`bundleTool_runOrdAt_empty`) and logarithmic bounds
  (`log_bundleNMax_le`, `log_bundleUCBound_le`, `log_bundleUCBound_le_min`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Degree-free parameter envelope `bundleCoreParams` -/

/-- Upper envelope on `bundleUCRatio` at edge scale `m` with vertex factor `E.c_n`. -/
noncomputable def bundleUCRatioHi (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  1 + 112 * (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2

/-- Upper envelope on `bundleRecoursePerQ` at edge scale `m`. -/
noncomputable def bundleRecEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  (E.B_fn m : ℝ) *
    ((3 + 2 * coreE82Len E.L (E.P_fn m)) * bundleBucketRecUH E.L (E.P_fn m) m +
      2 * bundleBucketRecD E.L (E.P_fn m) m) * (2 * bundleUCRatioHi E m) +
    22 * (E.B_fn m : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
      bundleLambdaS (E.P_fn m) m +
    7 + 224 * (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2

/-- Length and size factor `γ_ℓ(m)` of `bundleCoreParams E`. -/
noncomputable def bundleGammaLEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max (coreE82Len E.L (E.P_fn m)) (11 * bundleSizeFactor E.L (E.P_fn m) m (E.B_fn m))

/-- Encoded-recourse factor at edge scale `m`. -/
noncomputable def bundleEncEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  20 * max (bundleGammaLEnv E m) (bundleRecEnv E m) *
    Real.log ((m : ℝ) + bundleRecEnv E m * (m : ℝ) + 2)

/-- Combined recourse and encoding base factor at edge scale `m`. -/
noncomputable def bundleRecBase (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max (bundleRecEnv E m) (bundleEncEnv E m)

/-- Degree-free runtime multiplier absorbed into `γ_r(m)`. The extra `(k + 1)` from bundle degree
`Δ₀ ≤ k` stays outside `γ_r` in the ordered specification. -/
noncomputable def bundleCostMult (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max 1 (coreE_L E.L (E.P_fn m) *
    ((E.P_fn m).K_t * (2 + (E.P_fn m).γ_ℓ ^ 2) + 1) *
    max 1 ((E.L : ℝ) * bundleNRoot E.L m) * ((E.L : ℝ) + 1))

/-- Concrete degree-free `SparseCoreParams` associated with a `SparseCoreEnv` on bundle graphs
(paper Lemma 5.17, page 23). -/
noncomputable def bundleCoreParams (E : SparseCoreEnv) : SparseCoreParams where
  σ := fun k n => max 1 (mwuK0 E.C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6)
  γ_ℓ := bundleGammaLEnv E
  γ_c := fun m => 1 + coreE82Cong E.L (E.P_fn m)
  γ_r := fun m => bundleRecBase E m * bundleCostMult E m
  c_R := 112
  c_T := 37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n
  p_T := max E.p_s_hi E.p_t_hi + 1

/-! ## 2. Basic bounds on `BundleConstants` -/

lemma bundleParams_nMax_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : bundleNMax m₁ ≤ bundleNMax m₂ := by
  unfold bundleNMax; omega

lemma bundleParams_nRoot_ge_one (L m : ℕ) : 1 ≤ bundleNRoot L m := by
  unfold bundleNRoot
  by_cases hL0 : L = 0
  · subst hL0; simp
  · have hge1 : (1 : ℝ) ≤ (max (bundleNMax m) 1 : ℕ) := by
      exact_mod_cast le_max_right (bundleNMax m) 1
    exact Real.one_le_rpow hge1 (by positivity)

lemma bundleParams_nRoot_mono {L m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleNRoot L m₁ ≤ bundleNRoot L m₂ := by
  unfold bundleNRoot
  have h1 : (max (bundleNMax m₁) 1 : ℝ) ≤ (max (bundleNMax m₂) 1 : ℕ) := by
    exact_mod_cast max_le_max_right 1 (bundleParams_nMax_mono h)
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1) (by positivity)

lemma bundleParams_lambdaS_ge_one (P_b : SparsifyParams) (m : ℕ) : 1 ≤ bundleLambdaS P_b m := by
  unfold bundleLambdaS
  refine one_le_pow₀ ?_
  have : (1 : ℝ) ≤ (bundleNMax m : ℝ) + (m : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg this]

lemma bundleParams_lambdaS_pos (P_b : SparsifyParams) (m : ℕ) : 0 ≤ bundleLambdaS P_b m :=
  le_trans zero_le_one (bundleParams_lambdaS_ge_one P_b m)

lemma bundleParams_lambda_ge_one (P_b : SparsifyParams) (m : ℕ) : 1 ≤ bundleLambda P_b m := by
  unfold bundleLambda
  refine one_le_pow₀ ?_
  have : (1 : ℝ) ≤ (bundleNMax m : ℝ) + (m : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg this]

lemma bundleParams_lambdaS_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleLambdaS (E.P_fn m₁) m₁ ≤ bundleLambdaS (E.P_fn m₂) m₂ := by
  unfold bundleLambdaS
  have harg1 : (1 : ℝ) ≤ (bundleNMax m₁ : ℝ) + (m₁ : ℝ) + 2 := by linarith
  have harg2 : (bundleNMax m₁ : ℝ) + (m₁ : ℝ) + 2 ≤ (bundleNMax m₂ : ℝ) + (m₂ : ℝ) + 2 := by
    have hm : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    have hn : (bundleNMax m₁ : ℝ) ≤ (bundleNMax m₂ : ℝ) := by
      exact_mod_cast bundleParams_nMax_mono h
    linarith
  have hbase1 : 1 ≤ 1 + Real.log ((bundleNMax m₁ : ℝ) + (m₁ : ℝ) + 2) := by
    linarith [Real.log_nonneg harg1]
  have hbase_le :
      1 + Real.log ((bundleNMax m₁ : ℝ) + (m₁ : ℝ) + 2) ≤
        1 + Real.log ((bundleNMax m₂ : ℝ) + (m₂ : ℝ) + 2) :=
    add_le_add le_rfl (Real.log_le_log (by linarith) harg2)
  exact le_trans (pow_le_pow_left₀ (by linarith) hbase_le _)
    (pow_le_pow_right₀ (by linarith) (E.hMono h).2.2.2.1)

lemma bundleParams_ucRatio_pos (n₀ : ℕ) : 0 ≤ bundleUCRatio n₀ := by
  unfold bundleUCRatio
  have : 0 ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
  positivity

lemma bundleParams_ucRatio_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    bundleUCRatio n₁ ≤ bundleUCRatio n₂ := by
  unfold bundleUCRatio
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith [pow_le_pow_left₀ h1 hlog 2]

lemma bundleParams_bucketRec_pos (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) :
    0 ≤ bundleBucketRecUH L P_b m₀ ∧ 0 ≤ bundleBucketRecD L P_b m₀ ∧
      0 ≤ coreE82Len L P_b := by
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hnr : 0 ≤ bundleNRoot L m₀ := le_trans zero_le_one (bundleParams_nRoot_ge_one L m₀)
  have hlam : 0 ≤ bundleLambdaS P_b m₀ := bundleParams_lambdaS_pos P_b m₀
  exact ⟨by unfold bundleBucketRecUH; positivity, by unfold bundleBucketRecD; positivity,
    by unfold coreE82Len; positivity⟩

lemma bundleParams_bucketRec_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleBucketRecUH E.L (E.P_fn m₁) m₁ ≤ bundleBucketRecUH E.L (E.P_fn m₂) m₂ ∧
    bundleBucketRecD E.L (E.P_fn m₁) m₁ ≤ bundleBucketRecD E.L (E.P_fn m₂) m₂ := by
  have hm := E.hMono h
  have hnr := bundleParams_nRoot_mono (L := E.L) h
  have hls := bundleParams_lambdaS_mono E h
  have hnr1 : 0 ≤ bundleNRoot E.L m₁ := by linarith [bundleParams_nRoot_ge_one E.L m₁]
  have hnr2 : 0 ≤ bundleNRoot E.L m₂ := by linarith [bundleParams_nRoot_ge_one E.L m₂]
  have hls1 : 0 ≤ bundleLambdaS (E.P_fn m₁) m₁ := bundleParams_lambdaS_pos _ _
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hγℓ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hp1 : 12 * (E.L : ℝ) * bundleNRoot E.L m₁ * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ ≤
      12 * (E.L : ℝ) * bundleNRoot E.L m₂ * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ := by
    have ha := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ 12 * (E.L : ℝ))
    have hb := mul_le_mul ha hm.2.2.1 hKs1 (by positivity)
    exact mul_le_mul hb hm.2.1 hγℓ1 (by positivity)
  constructor
  · unfold bundleBucketRecUH
    linarith [mul_le_mul hp1 hls hls1 (by positivity)]
  · unfold bundleBucketRecD
    have hpow : (3 : ℝ) ^ E.L * (E.P_fn m₁).γ_ℓ ^ (E.L + 1) + 1 ≤
        (3 : ℝ) ^ E.L * (E.P_fn m₂).γ_ℓ ^ (E.L + 1) + 1 := by
      have hp := pow_le_pow_left₀ hγℓ1 hm.2.1 (E.L + 1)
      linarith [mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ E.L)]
    have h6 : 6 * (E.L : ℝ) * bundleNRoot E.L m₁ * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ ≤
        6 * (E.L : ℝ) * bundleNRoot E.L m₂ * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ := by
      have ha := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ 6 * (E.L : ℝ))
      have hb := mul_le_mul ha hm.2.2.1 hKs1 (by positivity)
      exact mul_le_mul hb hm.2.1 hγℓ1 (by positivity)
    exact mul_le_mul (mul_le_mul h6 hpow (by positivity) (by positivity)) hls hls1 (by positivity)

lemma bundleParams_sizeFactor_nonneg (L : ℕ) (P_b : SparsifyParams) (M B : ℕ) :
    0 ≤ bundleSizeFactor L P_b M B := by
  unfold bundleSizeFactor
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlam := bundleParams_lambdaS_pos P_b M
  positivity

lemma bundleParams_recoursePerQ_mono_n (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (B : ℕ) :
    bundleRecoursePerQ L P_b m₀ n₁ B ≤ bundleRecoursePerQ L P_b m₀ n₂ B := by
  unfold bundleRecoursePerQ
  have huc := bundleParams_ucRatio_mono h
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  have hcp := bundleParams_bucketRec_pos L P_b m₀
  have hc : 0 ≤ (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b m₀ +
      2 * bundleBucketRecD L P_b m₀) := by
    have h1' := hcp.1; have h2' := hcp.2.1; have h3' := hcp.2.2; positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show 2 * bundleUCRatio n₁ ≤ 2 * bundleUCRatio n₂ by linarith) hc
  linarith

/-! ## 3. Positivity, monotonicity, `bundleCoreParams_valid`, and parameter comparisons -/

lemma bundleUCRatioHi_ge_one (E : SparseCoreEnv) (m : ℕ) : 1 ≤ bundleUCRatioHi E m := by
  unfold bundleUCRatioHi
  nlinarith [sq_nonneg (Real.log (E.c_n * ((m : ℝ) + 1) + 2))]

lemma bundleUCRatioHi_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleUCRatioHi E m₁ ≤ bundleUCRatioHi E m₂ := by
  unfold bundleUCRatioHi
  have h1 : (1 : ℝ) ≤ E.c_n * ((m₁ : ℝ) + 1) + 2 := by
    have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁; nlinarith [E.hc_n]
  have hlog1 : 0 ≤ Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) := Real.log_nonneg h1
  have harg : E.c_n * ((m₁ : ℝ) + 1) + 2 ≤ E.c_n * ((m₂ : ℝ) + 1) + 2 := by
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    nlinarith [E.hc_n]
  have hlog_le : Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) ≤ Real.log (E.c_n * ((m₂ : ℝ) + 1) + 2) :=
    Real.log_le_log (by linarith) harg
  gcongr

lemma bundleRecEnv_ge_four (E : SparseCoreEnv) (m : ℕ) : (4 : ℝ) ≤ bundleRecEnv E m := by
  unfold bundleRecEnv
  have h1 : 0 ≤ (E.B_fn m : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ bundleBucketRecUH E.L (E.P_fn m) m := (bundleParams_bucketRec_pos E.L _ m).1
  have h3 : 0 ≤ bundleBucketRecD E.L (E.P_fn m) m := (bundleParams_bucketRec_pos E.L _ m).2.1
  have h4 : 0 ≤ coreE82Len E.L (E.P_fn m) := (bundleParams_bucketRec_pos E.L _ m).2.2
  have h5 : 0 ≤ bundleUCRatioHi E m := by linarith [bundleUCRatioHi_ge_one E m]
  have hKs := (E.P_fn m).hK_s
  have hγℓ : 0 ≤ (E.P_fn m).γ_ℓ := by linarith [(E.P_fn m).hγ_ℓ]
  have hls := bundleParams_lambdaS_pos (E.P_fn m) m
  have ht1 : 0 ≤ (E.B_fn m : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m)) *
      bundleBucketRecUH E.L (E.P_fn m) m + 2 * bundleBucketRecD E.L (E.P_fn m) m) *
      (2 * bundleUCRatioHi E m) := by positivity
  have ht2 : 0 ≤ 22 * (E.B_fn m : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m).K_s *
      (E.P_fn m).γ_ℓ * bundleLambdaS (E.P_fn m) m := by positivity
  nlinarith [sq_nonneg (Real.log (E.c_n * ((m : ℝ) + 1) + 2))]

lemma bundleRecEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleRecEnv E m₁ ≤ bundleRecEnv E m₂ := by
  unfold bundleRecEnv
  have hm := E.hMono h
  have hB : (E.B_fn m₁ : ℝ) ≤ (E.B_fn m₂ : ℝ) := by exact_mod_cast E.hB_mono h
  have hL1 := coreE82Len_mono (L := E.L) hm.2.1
  have hrec := bundleParams_bucketRec_mono E h
  have huc := bundleUCRatioHi_mono E h
  have hls_le := bundleParams_lambdaS_mono E h
  have h1 : (1 : ℝ) ≤ E.c_n * ((m₁ : ℝ) + 1) + 2 := by
    have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁; nlinarith [E.hc_n]
  have hlog1 : 0 ≤ Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) := Real.log_nonneg h1
  have hlog_le : Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) ≤ Real.log (E.c_n * ((m₂ : ℝ) + 1) + 2) := by
    refine Real.log_le_log (by linarith) ?_
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    nlinarith [E.hc_n]
  have hUH_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₁) m₁).1
  have hD_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₁) m₁).2.1
  have hLen_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₁) m₁).2.2
  have hLen2_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₂) m₂).2.2
  have hUH2_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₂) m₂).1
  have hD2_nn := (bundleParams_bucketRec_pos E.L (E.P_fn m₂) m₂).2.1
  have huc_nn : 0 ≤ 2 * bundleUCRatioHi E m₁ := by linarith [bundleUCRatioHi_ge_one E m₁]
  have hbr_nn : 0 ≤ (3 + 2 * coreE82Len E.L (E.P_fn m₁)) * bundleBucketRecUH E.L (E.P_fn m₁) m₁ +
      2 * bundleBucketRecD E.L (E.P_fn m₁) m₁ := by positivity
  have hbr_le : (3 + 2 * coreE82Len E.L (E.P_fn m₁)) * bundleBucketRecUH E.L (E.P_fn m₁) m₁ +
        2 * bundleBucketRecD E.L (E.P_fn m₁) m₁ ≤
      (3 + 2 * coreE82Len E.L (E.P_fn m₂)) * bundleBucketRecUH E.L (E.P_fn m₂) m₂ +
        2 * bundleBucketRecD E.L (E.P_fn m₂) m₂ :=
    add_le_add (mul_le_mul (by linarith) hrec.1 hUH_nn (by linarith)) (by linarith [hrec.2])
  have hmul1 : (E.B_fn m₁ : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m₁)) *
        bundleBucketRecUH E.L (E.P_fn m₁) m₁ + 2 * bundleBucketRecD E.L (E.P_fn m₁) m₁) *
        (2 * bundleUCRatioHi E m₁) ≤
      (E.B_fn m₂ : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m₂)) *
        bundleBucketRecUH E.L (E.P_fn m₂) m₂ + 2 * bundleBucketRecD E.L (E.P_fn m₂) m₂) *
        (2 * bundleUCRatioHi E m₂) :=
    mul_le_mul (mul_le_mul hB hbr_le hbr_nn (Nat.cast_nonneg _)) (by linarith) huc_nn (by positivity)
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hls1 : 0 ≤ bundleLambdaS (E.P_fn m₁) m₁ := bundleParams_lambdaS_pos _ _
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγℓ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hKs_le := hm.2.2.1; have hγ_le := hm.2.1
  have hmul2 : 22 * (E.B_fn m₁ : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ *
        bundleLambdaS (E.P_fn m₁) m₁ ≤
      22 * (E.B_fn m₂ : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ *
        bundleLambdaS (E.P_fn m₂) m₂ := by gcongr
  have hsq_le := pow_le_pow_left₀ hlog1 hlog_le 2
  linarith

lemma bundleGammaLEnv_ge_three (E : SparseCoreEnv) (m : ℕ) : (3 : ℝ) ≤ bundleGammaLEnv E m :=
  le_trans (coreE82Len_ge_three E.L E.hL (E.P_fn m)) (le_max_left _ _)

lemma bundleGammaLEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleGammaLEnv E m₁ ≤ bundleGammaLEnv E m₂ := by
  unfold bundleGammaLEnv bundleSizeFactor
  have hm := E.hMono h
  have hLen := coreE82Len_mono (L := E.L) hm.2.1
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hγ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hls1 : 0 ≤ bundleLambdaS (E.P_fn m₁) m₁ := bundleParams_lambdaS_pos _ _
  have hls2 : 0 ≤ bundleLambdaS (E.P_fn m₂) m₂ := bundleParams_lambdaS_pos _ _
  have hls_le := bundleParams_lambdaS_mono E h
  have hB_le : (E.B_fn m₁ : ℝ) ≤ (E.B_fn m₂ : ℝ) := by exact_mod_cast E.hB_mono h
  have hB1 : (0 : ℝ) ≤ (E.B_fn m₁ : ℝ) := Nat.cast_nonneg _
  have hKs_le := hm.2.2.1; have hγ_le := hm.2.1
  refine max_le_max hLen ?_
  gcongr

lemma bundleEncEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleEncEnv E m₁ ≤ bundleEncEnv E m₂ := by
  unfold bundleEncEnv
  have hL1 := bundleGammaLEnv_mono E h
  have hR := bundleRecEnv_mono E h
  have hR_nn : 0 ≤ bundleRecEnv E m₁ := by linarith [bundleRecEnv_ge_four E m₁]
  have hm_le : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
  have hlog1 : 0 ≤ Real.log ((m₁ : ℝ) + bundleRecEnv E m₁ * (m₁ : ℝ) + 2) :=
    Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m₁])
  have hlog_le : Real.log ((m₁ : ℝ) + bundleRecEnv E m₁ * (m₁ : ℝ) + 2) ≤
      Real.log ((m₂ : ℝ) + bundleRecEnv E m₂ * (m₂ : ℝ) + 2) :=
    Real.log_le_log (by nlinarith [Nat.cast_nonneg (α := ℝ) m₁])
      (by nlinarith [Nat.cast_nonneg (α := ℝ) m₁])
  have hmax_le : max (bundleGammaLEnv E m₁) (bundleRecEnv E m₁) ≤
      max (bundleGammaLEnv E m₂) (bundleRecEnv E m₂) := max_le_max hL1 hR
  have hmax_nn : 0 ≤ max (bundleGammaLEnv E m₁) (bundleRecEnv E m₁) :=
    le_trans hR_nn (le_max_right _ _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmax_le (by norm_num)) hlog_le hlog1 (by linarith)

lemma bundleCostMult_ge_one (E : SparseCoreEnv) (m : ℕ) : 1 ≤ bundleCostMult E m :=
  le_max_left _ _

lemma bundleCostMult_ge_four (E : SparseCoreEnv) (m : ℕ) : 4 ≤ bundleCostMult E m := by
  set P_b := E.P_fn m
  have h1 : (3 : ℝ) ≤ (3 : ℝ) ^ ((E.L + 1) * (E.L + 2) / 2 + E.L + 2) := by
    have hexp : 1 ≤ (E.L + 1) * (E.L + 2) / 2 + E.L + 2 := by omega
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (3 : ℝ) ^ ((E.L + 1) * (E.L + 2) / 2 + E.L + 2) := pow_le_pow_right₀ (by norm_num) hexp
  have h2 : 1 ≤ P_b.γ_c ^ (E.L + 1) := one_le_pow₀ P_b.hγ_c
  have h3 : 1 ≤ P_b.γ_ℓ ^ ((E.L + 1) * (E.L + 2) / 2 + 2) := one_le_pow₀ P_b.hγ_ℓ
  have hE : 3 ≤ coreE_L E.L P_b := by
    dsimp only [coreE_L]; nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  have hkt : 1 ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1 := by
    have := P_b.hK_t; nlinarith [sq_nonneg P_b.γ_ℓ]
  have hmx : (1 : ℝ) ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L m) := le_max_left _ _
  have hL1 : (2 : ℝ) ≤ (E.L : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (E.L : ℝ) := by exact_mod_cast E.hL
    linarith
  have hprod : 4 ≤ coreE_L E.L P_b * (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) *
      max 1 ((E.L : ℝ) * bundleNRoot E.L m) * ((E.L : ℝ) + 1) := by
    have ha : 3 ≤ coreE_L E.L P_b * (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) := by nlinarith
    have hb : 3 ≤ coreE_L E.L P_b * (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) + 1) *
        max 1 ((E.L : ℝ) * bundleNRoot E.L m) := by nlinarith
    nlinarith
  exact le_trans hprod (le_max_right _ _)

lemma bundleCostMult_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    bundleCostMult E m₁ ≤ bundleCostMult E m₂ := by
  unfold bundleCostMult
  have hm := E.hMono h
  have hγ_le := hm.2.1; have hKt_le := hm.2.2.2.2.1
  have hKt2 := (E.P_fn m₂).hK_t
  have hE := coreE_L_mono (L := E.L) hm.1 hm.2.1
  have hE2 := coreE_L_ge_one E.L (E.P_fn m₂)
  have hnr := bundleParams_nRoot_mono (L := E.L) h
  have hK1 : 0 ≤ (E.P_fn m₁).K_t := (E.P_fn m₁).hK_t
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hE1 : 0 ≤ coreE_L E.L (E.P_fn m₁) := by linarith [coreE_L_ge_one E.L (E.P_fn m₁)]
  have hL_nn : (0 : ℝ) ≤ (E.L : ℝ) := Nat.cast_nonneg _
  have hkt_nn : 0 ≤ (E.P_fn m₁).K_t * (2 + (E.P_fn m₁).γ_ℓ ^ 2) + 1 := by positivity
  have hnr_nn : 0 ≤ bundleNRoot E.L m₁ := by linarith [bundleParams_nRoot_ge_one E.L m₁]
  have hmx_nn : 0 ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L m₁) := by positivity
  have hL1_nn : (0 : ℝ) ≤ (E.L : ℝ) + 1 := by positivity
  refine max_le_max le_rfl ?_
  gcongr

/-- The real inequality behind `bundleGammaLEnv_le_bundleRecEnv`, with plain real parameters. -/
lemma bundleGammaLEnv_le_bundleRecEnv_aux {B Lr Ks γ Λs nr len RD lg : ℝ}
    (hB : 1 ≤ B) (hLr : 1 ≤ Lr) (hKs : 0 ≤ Ks) (hγ : 1 ≤ γ) (hΛs : 1 ≤ Λs)
    (hnr : 1 ≤ nr) (hlen : 3 ≤ len) (hRD : 0 ≤ RD) (hlg : 1 ≤ lg) :
    max len (11 * ((Lr + 1) * Ks * γ * Λs * B * 1000 + 115)) ≤
      B * ((3 + 2 * len) * (2 + 12 * Lr * nr * Ks * γ * Λs) + 2 * RD) *
          (2 * (1 + 112 * lg)) +
        22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg := by
  have hP : 0 ≤ Ks * γ * Λs := by positivity
  have hT1 : 9 * 2 * 226 ≤ B * (3 + 2 * len) * 2 * (2 * (1 + 112 * lg)) := by
    have h9 : (9 : ℝ) ≤ B * (3 + 2 * len) := by nlinarith
    have hu : (226 : ℝ) ≤ 2 * (1 + 112 * lg) := by linarith
    linarith [mul_le_mul (mul_le_mul_of_nonneg_right h9 (by norm_num : (0 : ℝ) ≤ 2)) hu
      (by positivity) (by positivity)]
  have hT1' : len ≤ B * (3 + 2 * len) * 2 * (2 * (1 + 112 * lg)) := by
    have h1 : len ≤ B * (3 + 2 * len) := by nlinarith
    have h2 : (1 : ℝ) ≤ 2 * (2 * (1 + 112 * lg)) := by linarith
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
  have hX : 6 * ((Lr + 1) * (Ks * γ * Λs)) ≤ 12 * Lr * nr * Ks * γ * Λs := by
    have h1 : 6 * (Lr + 1) ≤ 12 * Lr * nr := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hP]
  have hT2 : 9 * (6 * ((Lr + 1) * (Ks * γ * Λs) * B)) * 226 ≤
      B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (1 + 112 * lg)) := by
    have h9 : (9 : ℝ) ≤ 3 + 2 * len := by linarith
    have hBX : 6 * ((Lr + 1) * (Ks * γ * Λs) * B) ≤ B * (12 * Lr * nr * Ks * γ * Λs) := by
      linarith [mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ B)]
    have hu : (226 : ℝ) ≤ 2 * (1 + 112 * lg) := by linarith
    linarith [mul_le_mul (mul_le_mul h9 hBX (by positivity) (by linarith)) hu
      (by positivity) (by positivity)]
  have hRest : 0 ≤ B * (2 * RD) * (2 * (1 + 112 * lg)) +
      22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg := by positivity
  have hsplit : B * ((3 + 2 * len) * (2 + 12 * Lr * nr * Ks * γ * Λs) + 2 * RD) *
        (2 * (1 + 112 * lg)) +
      22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg =
      B * (3 + 2 * len) * 2 * (2 * (1 + 112 * lg)) +
      B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (1 + 112 * lg)) +
      (B * (2 * RD) * (2 * (1 + 112 * lg)) +
        22 * B * (Lr + 1) * Ks * γ * Λs + 7 + 224 * lg) := by ring
  have hT2nn : 0 ≤ B * (3 + 2 * len) * (12 * Lr * nr * Ks * γ * Λs) * (2 * (1 + 112 * lg)) := by
    have : 0 ≤ len := by linarith
    have : 0 ≤ Lr := by linarith
    have : 0 ≤ nr := by linarith
    positivity
  rw [hsplit]
  refine max_le (by linarith) ?_
  have hE : 11 * ((Lr + 1) * Ks * γ * Λs * B * 1000 + 115) =
      11000 * ((Lr + 1) * (Ks * γ * Λs) * B) + 1265 := by ring
  have hE2 : 9 * (6 * ((Lr + 1) * (Ks * γ * Λs) * B)) * 226 =
      12204 * ((Lr + 1) * (Ks * γ * Λs) * B) := by ring
  rw [hE]; linarith

/-- The length factor `bundleGammaLEnv` of `bundleCoreParams` is at most `bundleRecEnv`. -/
lemma bundleGammaLEnv_le_bundleRecEnv (E : SparseCoreEnv) (m : ℕ) :
    bundleGammaLEnv E m ≤ bundleRecEnv E m := by
  have hlog : 1 ≤ Real.log (E.c_n * ((m : ℝ) + 1) + 2) := by
    have harg : (3 : ℝ) ≤ E.c_n * ((m : ℝ) + 1) + 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m, E.hc_n]
    exact le_trans (by linarith [real_log_three_gt]) (Real.log_le_log (by norm_num) harg)
  have hlg : 1 ≤ (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2 := one_le_pow₀ hlog
  have h := bundleGammaLEnv_le_bundleRecEnv_aux (B := (E.B_fn m : ℝ)) (Lr := (E.L : ℝ))
    (Ks := (E.P_fn m).K_s) (γ := (E.P_fn m).γ_ℓ) (Λs := bundleLambdaS (E.P_fn m) m)
    (nr := bundleNRoot E.L m) (len := coreE82Len E.L (E.P_fn m))
    (RD := bundleBucketRecD E.L (E.P_fn m) m) (lg := (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2)
    (by exact_mod_cast E.hB_pos m) (by exact_mod_cast E.hL)
    (E.P_fn m).hK_s (E.P_fn m).hγ_ℓ (bundleParams_lambdaS_ge_one _ _)
    (bundleParams_nRoot_ge_one _ _) (coreE82Len_ge_three E.L E.hL _)
    (bundleParams_bucketRec_pos E.L (E.P_fn m) m).2.1 hlg
  unfold bundleGammaLEnv bundleSizeFactor bundleRecEnv bundleUCRatioHi bundleBucketRecUH
  exact h

lemma four_mul_bundleEncEnv_le_gamma_r (E : SparseCoreEnv) (m : ℕ) :
    4 * bundleEncEnv E m ≤ (bundleCoreParams E).γ_r m := by
  dsimp only [bundleCoreParams]
  have h1 : bundleEncEnv E m ≤ bundleRecBase E m := le_max_right _ _
  have hcm4 : 4 ≤ bundleCostMult E m := bundleCostMult_ge_four E m
  have hrb_nn : 0 ≤ bundleRecBase E m :=
    le_trans (by linarith [bundleRecEnv_ge_four E m]) (le_max_left _ _)
  linarith [mul_le_mul_of_nonneg_left hcm4 hrb_nn]

lemma bundleEncEnv_le_gamma_r (E : SparseCoreEnv) (m : ℕ) :
    bundleEncEnv E m ≤ (bundleCoreParams E).γ_r m := by
  have hR_nn : 0 ≤ bundleRecEnv E m := by linarith [bundleRecEnv_ge_four E m]
  have hmax_nn : 0 ≤ max (bundleGammaLEnv E m) (bundleRecEnv E m) :=
    le_trans hR_nn (le_max_right _ _)
  have hlog_nn : 0 ≤ Real.log ((m : ℝ) + bundleRecEnv E m * (m : ℝ) + 2) :=
    Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have henc_nn : 0 ≤ bundleEncEnv E m := by unfold bundleEncEnv; positivity
  linarith [four_mul_bundleEncEnv_le_gamma_r E m]

/-- `bundleCoreParams E` satisfies all validity conditions of `SparseCoreParams.Valid`. -/
theorem bundleCoreParams_valid (E : SparseCoreEnv) : (bundleCoreParams E).Valid := by
  dsimp only [SparseCoreParams.Valid, bundleCoreParams]
  have hK₀ : 0 < mwuK0 E.C_lsst := mwuK0_pos E.C_lsst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_⟩
  · intro _ _ _; exact le_max_left _ _
  · intro k₁ k₂ n₁ n₂ hk hn
    refine max_le_max le_rfl ?_
    have hk' : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hk
    have hlog1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := by linarith [half_lt_log_add_two n₁]
    have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
      Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₁])
        (by linarith [show (n₁ : ℝ) ≤ (n₂ : ℝ) from by exact_mod_cast hn])
    gcongr
  · intro m; linarith [bundleGammaLEnv_ge_three E m]
  · intro m₁ m₂ h; exact bundleGammaLEnv_mono E h
  · intro m; linarith [coreE82Cong_nonneg E.L (E.P_fn m)]
  · intro m₁ m₂ h
    have hm := E.hMono h
    linarith [coreE82Cong_mono (L := E.L) hm.1 hm.2.1]
  · intro m
    have h1 : 4 ≤ bundleRecBase E m := le_trans (bundleRecEnv_ge_four E m) (le_max_left _ _)
    have h2 : 1 ≤ bundleCostMult E m := bundleCostMult_ge_one E m
    nlinarith
  · intro m₁ m₂ h
    have hrb : bundleRecBase E m₁ ≤ bundleRecBase E m₂ :=
      max_le_max (bundleRecEnv_mono E h) (bundleEncEnv_mono E h)
    have hcm := bundleCostMult_mono E h
    have h1 : 0 ≤ bundleRecBase E m₁ :=
      le_trans (by linarith [bundleRecEnv_ge_four E m₁]) (le_max_left _ _)
    have h2 : 0 ≤ bundleCostMult E m₁ := by linarith [bundleCostMult_ge_one E m₁]
    have hcm2 : 0 ≤ bundleCostMult E m₂ := by linarith [bundleCostMult_ge_one E m₂]
    exact mul_le_mul hrb hcm h2 (by linarith)
  · have : (0 : ℝ) ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := by positivity
    linarith [E.hc_n]

/-! ## 4. Degree-free instance hypotheses `BundleCoreHypsAt` and `BundleInstanceHyps` -/

/-- The initial bucket partition of `initBundleTree` depends only on the LSF oracle, `C_lsst`,
`k`, `G₀`, `ℓ₀`, and branch `j`, not on `L`, `sparsify`, `M`, `N`, or `ord`. -/
lemma initBundleTree_activeBuckets_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L₁ L₂ : ℕ)
    (sparsify₁ sparsify₂ : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M₁ M₂ N₁ N₂ : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord₁ ord₂ : ℕ → List End) (j : ℕ) :
    (initBundleTree oracle C_lsst L₁ sparsify₁ k M₁ N₁ G₀ ℓ₀ ord₁ j).activeBuckets =
      (initBundleTree oracle C_lsst L₂ sparsify₂ k M₂ N₂ G₀ ℓ₀ ord₂ j).activeBuckets :=
  rfl

/-- Explicit image formula for the initial active buckets of `initBundleTree`. -/
lemma initBundleTree_activeBuckets_apply
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let C₀ := coreGraph G₀ cs₀.lsf
    (initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C =
      (C₀.E.filter fun e => C₀.tail e ∈ C).image
        (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) :=
  rfl

/-- Every component has at most `G₀.m` active length buckets in `initBundleTree`. -/
lemma initBundleTree_activeBuckets_card_le_m
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) :
    ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤ G₀.m := by
  classical
  rw [initBundleTree_activeBuckets_apply]
  exact le_trans Finset.card_image_le
    (le_trans (Finset.card_filter_le _ _) (Finset.card_le_card Finset.sdiff_subset))

/-- The per-instance hypotheses of `sparseCoreBundleTool` at edge scale `M` (with no degree bound
and no `hComp_bound`). -/
structure BundleCoreHypsAt (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M : ℕ) (D : DynamicInstance) : Prop where
  hLSST : HasLSSTSpec oracle E.C_lsst
  hSp : SparsifySpec M (E.P_fn M) (sparsify M)
  hB_bound : ∀ j < k, ∀ C ∈ components (D.G 0),
    ((initBundleTree oracle E.C_lsst E.L sparsify k M 0 (D.G 0) (D.ℓ 0) (fun _ => []) j).activeBuckets
      C).card ≤ E.B_fn M

lemma BundleCoreHypsAt.activeBuckets_card_le {E : SparseCoreEnv}
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M : ℕ} {D : DynamicInstance}
    (h : BundleCoreHypsAt E oracle sparsify k M D)
    {N : ℕ} {ord : ℕ → ℕ → List End} {j : ℕ} (hj : j < k) :
    ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j 0).1.activeBuckets C).card ≤
        E.B_fn M :=
  h.hB_bound j hj

/-- Special case of `BundleCoreHypsAt` at `M = (D.G 0).m`. -/
abbrev BundleCoreHyps (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k _τ : ℕ) (D : DynamicInstance) : Prop :=
  BundleCoreHypsAt E oracle sparsify k (D.G 0).m D

/-- Per-instance hypotheses with `hComp_bound` at `M = (D.G 0).m` (no degree bound). -/
structure BundleInstanceHyps (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) : Prop where
  hLSST : HasLSSTSpec oracle E.C_lsst
  hSp : SparsifySpec (D.G 0).m (E.P_fn (D.G 0).m) (sparsify (D.G 0).m)
  hB_bound : ∀ j < k, ∀ C ∈ components (D.G 0),
    ((initBundleTree oracle E.C_lsst E.L sparsify k (D.G 0).m 0 (D.G 0) (D.ℓ 0) (fun _ => [])
      j).activeBuckets C).card ≤ E.B_fn (D.G 0).m
  hComp_bound : ((D.G 0).n : ℝ) ≤ E.c_n * (((D.G 0).m : ℝ) + 1)

theorem BundleInstanceHyps.toCoreHyps {E : SparseCoreEnv}
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k τ : ℕ} {D : DynamicInstance}
    (h : BundleInstanceHyps E oracle sparsify k τ D) :
    BundleCoreHyps E oracle sparsify k τ D where
  hLSST := h.hLSST
  hSp := h.hSp
  hB_bound := h.hB_bound

/-- Whenever `E.B_fn M ≥ (D.G 0).m`, `BundleCoreHypsAt` follows directly from the LSST and
sparsifier specifications. -/
theorem bundleCoreHypsAt_of_B_ge_m {E : SparseCoreEnv}
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M : ℕ} {D : DynamicInstance}
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : SparsifySpec M (E.P_fn M) (sparsify M))
    (hBm : (D.G 0).m ≤ E.B_fn M) :
    BundleCoreHypsAt E oracle sparsify k M D where
  hLSST := hLSST
  hSp := hSp
  hB_bound := fun j _ C _ =>
    le_trans (initBundleTree_activeBuckets_card_le_m oracle E.C_lsst E.L sparsify k M 0
      (D.G 0) (D.ℓ 0) (fun _ => []) j C) hBm

/-- Non-vacuity witness: all hypotheses of `BundleCoreHypsAt` and `BundleInstanceHyps` can hold
simultaneously on a nonempty graph. -/
theorem exists_bundleCoreHypsAt :
    ∃ (E : SparseCoreEnv) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
      (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
      (k M : ℕ) (D : DynamicInstance),
      0 < k ∧ (D.G 0).IsValid ∧ (D.G 0).V.Nonempty ∧ (D.G 0).m ≤ M ∧
      BundleCoreHypsAt E oracle sparsify k M D ∧
      BundleInstanceHyps E oracle sparsify k 0 D := by
  obtain ⟨oracle, C_lsst, hLSST⟩ := MinCostFlow.LSF.theorem_2_2
  let E : SparseCoreEnv :=
    { C_lsst := C_lsst, L := 1, hL := le_rfl, P_fn := idSparsifyParams
      hMono := fun _ _ h => ⟨le_rfl, le_rfl, by dsimp only [idSparsifyParams]; exact_mod_cast h,
        le_rfl, le_rfl, le_rfl⟩
      p_s_hi := 0, p_t_hi := 0, hp_s := fun _ => le_rfl, hp_t := fun _ => le_rfl
      B_fn := fun m => max 1 m, hB_pos := fun m => le_max_left 1 m
      hB_mono := fun _ _ h => max_le_max_left 1 h
      d_fn := fun _ => 0, hd_mono := fun _ _ _ => le_rfl
      c_n := 1, hc_n := le_rfl }
  let G₀ : MGraph := { V := {0}, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  let D : DynamicInstance :=
    { G := fun _ => G₀, U := fun _ => [], g := fun _ _ => 0, ℓ := fun _ _ => 1 }
  have hCore : BundleCoreHypsAt E oracle (fun _ => idSparsify) 1 0 D :=
    bundleCoreHypsAt_of_B_ge_m hLSST (idSparsify_spec 0) (by simp [E, D, G₀, MGraph.m])
  refine ⟨E, oracle, fun _ => idSparsify, 1, 0, D, Nat.one_pos,
    fun e he => by simp [D, G₀] at he, ⟨0, by simp [D, G₀]⟩, by simp [D, G₀, MGraph.m], hCore, ?_⟩
  exact ⟨hCore.hLSST, hCore.hSp, hCore.hB_bound, by simp [E, D, G₀, MGraph.n, MGraph.m]⟩

/-! ## 5. Empty-graph run and logarithmic bounds -/

lemma bundleTool_runOrdAt_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] := by
  intro t
  induction t with
  | zero =>
    dsimp only [SparseCoreTool.runOrdAt, sparseCoreBundleTool, sparseCoreBundleToolWith,
      initBundleCore, initBundleCoreWith, initBundleCoreWithParams]
    simp only [decide_eq_false hV₀]
    exact ⟨trivial, trivial⟩
  | succ s ih =>
    dsimp only [SparseCoreTool.runOrdAt]
    rcases ih with ⟨hne, _⟩
    dsimp only [sparseCoreBundleTool, sparseCoreBundleToolWith, updateBundleCore] at hne ⊢
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, trivial⟩

lemma log_bundleNMax_le (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) :
    1 + Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  set X := (m₀ : ℝ) + (n₀ : ℝ) + 2
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hlog3 : (1 : ℝ) ≤ Real.log X := by
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := X) (by norm_num) hX3)]
  have harg : (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2 ≤ X ^ 6 := by
    have hbN : (bundleNMax m₀ : ℝ) = 114 * (m₀ : ℝ) + 2 := by
      unfold bundleNMax; push_cast; ring
    have hlin : (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2 ≤ 115 * X := by linarith [hbN]
    have h115 : (115 : ℝ) ≤ X ^ 5 :=
      le_trans (by norm_num : (115 : ℝ) ≤ 3 ^ 5) (pow_le_pow_left₀ (by norm_num) hX3 5)
    calc (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2
        ≤ 115 * X := hlin
      _ ≤ X ^ 5 * X := mul_le_mul_of_nonneg_right h115 (by linarith)
      _ = X ^ 6 := by ring
  have hlog_le : Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2) ≤ 6 * Real.log X := by
    calc Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2)
        ≤ Real.log (X ^ 6) := Real.log_le_log (by positivity) harg
      _ = 6 * Real.log X := by rw [Real.log_pow]; norm_num
  linarith

lemma log_bundleUCBound_le (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) (q_τ : ℕ) (hq : q_τ ≤ m₀) :
    Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq
  set X := (m₀ : ℝ) + (n₀ : ℝ) + 2
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hmX : (m₀ : ℝ) ≤ X := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  have hlog_X : Real.log ((n₀ : ℝ) + 2) ≤ X / 2 := by
    have h1 : Real.log ((n₀ : ℝ) + 2) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by linarith)
    have hX2 : Real.log X = Real.log 2 + Real.log (X / 2) := by
      have : X = 2 * (X / 2) := by ring
      conv_lhs => rw [this, Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < X / 2)]
  have hsq_le : (Real.log ((n₀ : ℝ) + 2)) ^ 2 ≤ (X / 2) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_X 2
  have huc : 2 * bundleUCRatio n₀ ≤ 57 * X ^ 2 := by
    unfold bundleUCRatio
    have h2X : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    linarith [hsq_le, h2X]
  have harg : (m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2 ≤ X ^ 7 := by
    have hp1 : (m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2 ≤ X + 57 * X ^ 3 := by
      have h1 : 2 * bundleUCRatio n₀ * (q_τ : ℝ) ≤ 57 * X ^ 2 * X :=
        mul_le_mul huc (le_trans hqR hmX) (Nat.cast_nonneg _) (by positivity)
      linarith
    have hX58 : X + 57 * X ^ 3 ≤ 58 * X ^ 3 := by nlinarith
    have hX4 : (58 : ℝ) ≤ X ^ 4 :=
      le_trans (by norm_num : (58 : ℝ) ≤ 3 ^ 4) (pow_le_pow_left₀ (by norm_num) hX3 4)
    have hmul : 58 * X ^ 3 ≤ X ^ 7 := by
      calc 58 * X ^ 3 ≤ X ^ 4 * X ^ 3 := mul_le_mul_of_nonneg_right hX4 (by positivity)
        _ = X ^ 7 := by ring
    linarith
  calc Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2)
      ≤ Real.log (X ^ 7) := by
        refine Real.log_le_log ?_ harg
        have : 0 ≤ bundleUCRatio n₀ := bundleParams_ucRatio_pos n₀
        have : 0 ≤ (q_τ : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ = 7 * Real.log X := by rw [Real.log_pow]; norm_num

lemma log_bundleUCBound_le_min (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) (q_τ : ℕ) (hq : q_τ ≤ m₀) :
    Real.log ((m₀ : ℝ) + 2 * bundleUCRatio (min n₀ (m₀ + 1)) * (q_τ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have huc := bundleParams_ucRatio_mono (min_le_left n₀ (m₀ + 1))
  have huc_nn := bundleParams_ucRatio_pos (min n₀ (m₀ + 1))
  have h1 : Real.log ((m₀ : ℝ) + 2 * bundleUCRatio (min n₀ (m₀ + 1)) * (q_τ : ℝ) + 2) ≤
      Real.log ((m₀ : ℝ) + 2 * bundleUCRatio n₀ * (q_τ : ℝ) + 2) := by
    refine Real.log_le_log (by
      have : 0 ≤ 2 * bundleUCRatio (min n₀ (m₀ + 1)) * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) m₀]) ?_
    have := mul_le_mul_of_nonneg_right
      (show 2 * bundleUCRatio (min n₀ (m₀ + 1)) ≤ 2 * bundleUCRatio n₀ by linarith)
      (Nat.cast_nonneg (α := ℝ) q_τ)
    linarith
  exact le_trans h1 (log_bundleUCBound_le m₀ n₀ hn₀ q_τ hq)

end

end MinCostFlow.SparseCore
