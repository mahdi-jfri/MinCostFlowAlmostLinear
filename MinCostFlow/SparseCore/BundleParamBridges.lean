module

public import MinCostFlow.SparseCore.BundleCoreParams
import MinCostFlow.SparseCore.BundleSpannerMetrics
import MinCostFlow.SparseCore.BundleRecourse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter-Form Bridges for Sparsified Core Metrics and Recourse

This file translates the raw size/congestion/length and recourse/encoding theorems for
`bundleRunSeq` into the parameter form of `bundleCoreParams E` (paper Lemma 5.17, pages 23–24).

The main results are:
* `bundleRunSeq_isSparsifiedCoreGraphAt_params`: lifts `bundleRunSeq_isSparsifiedCoreGraph` to
  `IsSparsifiedCoreGraphAt` at `bundleCoreParams E` without `hComp_bound` or a degree bound.
* `bundleRunSeq_recourse_and_enc_params_gen`: algebraic bridge from a raw recourse/encoding bound
  at vertex scale `n_uc` to `P.γ_r M`.
* `bundleRunSeq_recourse_and_enc_params` and `bundleRunSeq_recourse_and_enc_params_noComp`:
  specializations for `bundleRunSeq` (with `hComp` using `bundleRunSeq_recourse_and_enc`, and
  without `hComp` using `bundleRunSeq_recourse_and_enc_min`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-- Translates `bundleRunSeq_isSparsifiedCoreGraph` into `IsSparsifiedCoreGraphAt` at
`bundleCoreParams E`, with no degree bound and no `hComp_bound`. -/
theorem bundleRunSeq_isSparsifiedCoreGraphAt_params
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (j : ℕ) (hj : j < k) (t : ℕ) (ht : t ≤ τ) :
    let P := bundleCoreParams E
    let st := (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j t).1
    IsSparsifiedCoreGraphAt (D.G t) st.cs.lsf (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
      st.S_cur st.emb := by
  intro P st
  have hsp := bundleRunSeq_isSparsifiedCoreGraph oracle E.C_lsst E.L E.hL (E.P_fn M)
    sparsify hHyps.hLSST k M N τ hk D hG₀ hV₀ hD hℓ hLen hM hN hThresh hHyps.hSp ord hOrd j hj t ht
  dsimp only at hsp
  have hlen : (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ P.γ_ℓ M :=
    le_trans hsp.2.2.2.1 (le_max_left _ _)
  have hcong : st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      (k : ℝ) * P.γ_c M := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : 1 + coreE82Cong E.L (E.P_fn M) * (k : ℝ) ≤
        (k : ℝ) * (1 + coreE82Cong E.L (E.P_fn M)) := by nlinarith
    exact le_trans hsp.2.2.2.2.1 h1
  have hcard : (st.S_cur.E.card : ℝ) ≤ (M : ℝ) * P.γ_ℓ M / (k : ℝ) := by
    have hC := hsp.2.2.2.2.2 (E.B_fn M) (hHyps.activeBuckets_card_le hj)
    have hsf_nn := bundleParams_sizeFactor_nonneg E.L (E.P_fn M) M (E.B_fn M)
    have hsf_le : bundleSizeFactor E.L (E.P_fn M) M (E.B_fn M) ≤ P.γ_ℓ M :=
      le_trans (by linarith) (le_max_right (coreE82Len E.L (E.P_fn M)) _)
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hm_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    exact le_trans hC (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsf_le hm_nn) (le_of_lt hk_pos) |>.trans_eq (by ring))
  exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hlen, hcong, hcard⟩

/-- General algebraic bridge turning a raw recourse-and-encoding bound at vertex scale `n_uc` into
the `bundleCoreParams E` recourse and encoding inequalities. -/
lemma bundleRunSeq_recourse_and_enc_params_gen (E : SparseCoreEnv) (k M n_uc q_t sumLen sumEnc S0m : ℕ)
    (hk : 0 < k) (hq_le_M : q_t ≤ M) (hcn : (n_uc : ℝ) ≤ E.c_n * ((M : ℝ) + 1))
    (hS0_γ : (S0m : ℝ) ≤ (M : ℝ) * bundleGammaLEnv E M / (k : ℝ))
    (hS0_M : (S0m : ℝ) ≤ (M : ℝ))
    (hLen : (sumLen : ℝ) ≤ bundleRecoursePerQ E.L (E.P_fn M) M n_uc (E.B_fn M) * (q_t : ℝ))
    (hEnc : (sumEnc : ℝ) ≤
      20 * ((S0m : ℝ) + (sumLen : ℝ)) * Real.log ((S0m : ℝ) + (sumLen : ℝ) + 2))
    (hZero : q_t = 0 → sumLen = 0 ∧ sumEnc = 0) :
    let P := bundleCoreParams E
    (sumLen : ℝ) ≤ P.γ_r M * (q_t : ℝ) ∧
    (sumEnc : ℝ) ≤ P.γ_r M * ((M : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
  intro P
  have hlog1 : 0 ≤ Real.log ((n_uc : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n_uc])
  have hlog_le : Real.log ((n_uc : ℝ) + 2) ≤ Real.log (E.c_n * ((M : ℝ) + 1) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n_uc]) (by linarith)
  have hsq : (Real.log ((n_uc : ℝ) + 2)) ^ 2 ≤ (Real.log (E.c_n * ((M : ℝ) + 1) + 2)) ^ 2 :=
    pow_le_pow_left₀ hlog1 hlog_le 2
  have huc_le : bundleUCRatio n_uc ≤ bundleUCRatioHi E M := by
    unfold bundleUCRatio bundleUCRatioHi; linarith
  have hRec_le : bundleRecoursePerQ E.L (E.P_fn M) M n_uc (E.B_fn M) ≤ bundleRecEnv E M := by
    have hcp := bundleParams_bucketRec_pos E.L (E.P_fn M) M
    have h3_nn : 0 ≤ (3 + 2 * coreE82Len E.L (E.P_fn M)) * bundleBucketRecUH E.L (E.P_fn M) M +
        2 * bundleBucketRecD E.L (E.P_fn M) M := by
      have h1 := hcp.1; have h2 := hcp.2.1; have h3 := hcp.2.2; positivity
    have hmul := mul_le_mul_of_nonneg_left
      (show 2 * bundleUCRatio n_uc ≤ 2 * bundleUCRatioHi E M by linarith)
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (E.B_fn M)) h3_nn)
    unfold bundleRecoursePerQ bundleRecEnv
    linarith
  have hlen_rec : (sumLen : ℝ) ≤ bundleRecEnv E M * (q_t : ℝ) :=
    le_trans hLen (mul_le_mul_of_nonneg_right hRec_le (Nat.cast_nonneg _))
  have hrec_nn : 0 ≤ bundleRecEnv E M := by linarith [bundleRecEnv_ge_four E M]
  have hrec_le_γr : bundleRecEnv E M ≤ P.γ_r M := by
    dsimp only [P, bundleCoreParams]
    have hcm := bundleCostMult_ge_one E M
    have hrb : bundleRecEnv E M ≤ bundleRecBase E M := le_max_left _ _
    nlinarith
  have hlen_γr : (sumLen : ℝ) ≤ P.γ_r M * (q_t : ℝ) :=
    le_trans hlen_rec (mul_le_mul_of_nonneg_right hrec_le_γr (Nat.cast_nonneg _))
  refine ⟨hlen_γr, ?_⟩
  by_cases hq0 : q_t = 0
  · rw [(hZero hq0).2, Nat.cast_zero]
    have hγr_nn : 0 ≤ P.γ_r M := by linarith [(bundleCoreParams_valid E).2.2.2.2.2.2.1 M]
    exact mul_nonneg hγr_nn (by positivity)
  · have hqR : (q_t : ℝ) ≤ (M : ℝ) := by exact_mod_cast hq_le_M
    have hsum_in : (S0m : ℝ) + (sumLen : ℝ) ≤
        max (bundleGammaLEnv E M) (bundleRecEnv E M) * ((M : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
      have hm_nn : 0 ≤ (M : ℝ) / (k : ℝ) := by positivity
      have hq_nn : 0 ≤ (q_t : ℝ) := Nat.cast_nonneg _
      have hM1 := mul_le_mul_of_nonneg_right
        (le_max_left (bundleGammaLEnv E M) (bundleRecEnv E M)) hm_nn
      have hM2 := mul_le_mul_of_nonneg_right
        (le_max_right (bundleGammaLEnv E M) (bundleRecEnv E M)) hq_nn
      have hS0' : (S0m : ℝ) ≤ bundleGammaLEnv E M * ((M : ℝ) / (k : ℝ)) := by
        linarith [hS0_γ, show (M : ℝ) * bundleGammaLEnv E M / (k : ℝ) =
          bundleGammaLEnv E M * ((M : ℝ) / (k : ℝ)) from by ring]
      linarith [hS0', hlen_rec, hM1, hM2]
    have hlog_arg : (S0m : ℝ) + (sumLen : ℝ) + 2 ≤ (M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2 := by
      nlinarith [hS0_M, hlen_rec, hqR]
    have hlog1 : 0 ≤ Real.log ((S0m : ℝ) + (sumLen : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) S0m, Nat.cast_nonneg (α := ℝ) sumLen])
    have hlog_le' : Real.log ((S0m : ℝ) + (sumLen : ℝ) + 2) ≤
        Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) :=
      Real.log_le_log (by positivity) hlog_arg
    have hmax_nn : 0 ≤ max (bundleGammaLEnv E M) (bundleRecEnv E M) :=
      le_trans hrec_nn (le_max_right _ _)
    have hm1 : 20 * ((S0m : ℝ) + (sumLen : ℝ)) ≤
        20 * max (bundleGammaLEnv E M) (bundleRecEnv E M) * ((M : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
      linarith
    have hm2 := mul_le_mul hm1 hlog_le' hlog1 (by positivity)
    have heq : 20 * max (bundleGammaLEnv E M) (bundleRecEnv E M) * ((M : ℝ) / (k : ℝ) + (q_t : ℝ)) *
          Real.log ((M : ℝ) + bundleRecEnv E M * (M : ℝ) + 2) =
        bundleEncEnv E M * ((M : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
      unfold bundleEncEnv; ring
    exact le_trans (le_trans hEnc (heq ▸ hm2))
      (mul_le_mul_of_nonneg_right (bundleEncEnv_le_gamma_r E M) (by positivity))

/-- Parameter-form recourse and encoding bounds for `bundleRunSeq` at `(M, N)` under `hComp`. -/
theorem bundleRunSeq_recourse_and_enc_params
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hComp : (N : ℝ) ≤ E.c_n * ((M : ℝ) + 1))
    (j : ℕ) (hj : j < k) (t : ℕ) (ht : t ≤ τ) :
    let P := bundleCoreParams E
    let st := fun s => (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).1
    let U_S := fun s => (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).2
    (((Finset.Icc 1 t).sum fun s => (U_S s).length : ℕ) : ℝ) ≤
      P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
    (((Finset.Icc 1 t).sum fun s => (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
      P.γ_r M * ((M : ℝ) / (k : ℝ) +
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
  intro P st U_S
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hq_le_M := (updateThreshold_le_div_k_at hk hN_pos hThresh t ht).2
  have hSp0 := bundleRunSeq_isSparsifiedCoreGraphAt_params
    E oracle sparsify k M N τ D ord hk hG₀ hV₀ hD hℓ hLen hM hN hThresh hOrd hHyps j hj 0
    (Nat.zero_le τ)
  have hRec := bundleRunSeq_recourse_and_enc oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
    hHyps.hLSST k M N τ hk D hG₀ hV₀ (hℓ 0 (Nat.zero_le τ)) hD hM hN hThresh hHyps.hSp ord hOrd
    j hj (E.B_fn M) (hHyps.activeBuckets_card_le hj) t ht
  have hS0_M : ((st 0).S_cur.m : ℝ) ≤ (M : ℝ) := by
    have hsub : (st 0).S_cur.E ⊆ (D.G 0).E := Finset.Subset.trans hSp0.1.2.1 Finset.sdiff_subset
    exact_mod_cast le_trans (Finset.card_le_card hsub) hM
  exact bundleRunSeq_recourse_and_enc_params_gen E k M N _ _ _ (st 0).S_cur.m hk hq_le_M hComp
    hSp0.2.2.2.2.2 hS0_M hRec.1 hRec.2.1 hRec.2.2

/-- Parameter-form recourse and encoding bounds for `bundleRunSeq` at `(M, N)` without
`hComp_bound`, using `bundleRunSeq_recourse_and_enc_min` (with `min N (M + 1)`). -/
theorem bundleRunSeq_recourse_and_enc_params_noComp
    (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (j : ℕ) (hj : j < k) (t : ℕ) (ht : t ≤ τ) :
    let P := bundleCoreParams E
    let st := fun s => (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).1
    let U_S := fun s => (bundleRunSeq oracle E.C_lsst E.L sparsify k M N D ord j s).2
    (((Finset.Icc 1 t).sum fun s => (U_S s).length : ℕ) : ℝ) ≤
      P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
    (((Finset.Icc 1 t).sum fun s => (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
      P.γ_r M * ((M : ℝ) / (k : ℝ) +
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
  intro P st U_S
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hq_le_M := (updateThreshold_le_div_k_at hk hN_pos hThresh t ht).2
  have hSp0 := bundleRunSeq_isSparsifiedCoreGraphAt_params
    E oracle sparsify k M N τ D ord hk hG₀ hV₀ hD hℓ hLen hM hN hThresh hOrd hHyps j hj 0
    (Nat.zero_le τ)
  have hRec := bundleRunSeq_recourse_and_enc_min oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
    hHyps.hLSST k M N τ hk D hG₀ hV₀ (hℓ 0 (Nat.zero_le τ)) hD hM hN hThresh hHyps.hSp ord hOrd
    j hj (E.B_fn M) (hHyps.activeBuckets_card_le hj) t ht
  have hS0_M : ((st 0).S_cur.m : ℝ) ≤ (M : ℝ) := by
    have hsub : (st 0).S_cur.E ⊆ (D.G 0).E := Finset.Subset.trans hSp0.1.2.1 Finset.sdiff_subset
    exact_mod_cast le_trans (Finset.card_le_card hsub) hM
  exact bundleRunSeq_recourse_and_enc_params_gen E k M (min N (M + 1)) _ _ _ (st 0).S_cur.m hk
    hq_le_M (min_le_cn_mul_m_add_one E M N) hSp0.2.2.2.2.2 hS0_M hRec.1 hRec.2.1 hRec.2.2

end

end MinCostFlow.SparseCore
