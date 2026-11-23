module

public import MinCostFlow.Chain.BundleRestartMachCost
public import MinCostFlow.Chain.BundleRestartSpec
public import MinCostFlow.Chain.BundleRestartCostBranch
public import MinCostFlow.SparseCore.BundleMachParams
import MinCostFlow.SparseCore.BundleCostEnv
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-restart and per-epoch machine-cost bounds

Bounds used to assemble the per-branch machine cost in `BundleRestartMachBound.lean`:
* `spanInitBound_buckets_to_env`: envelope bound for `∑ c_sp * spanInitBound` over buckets;
* `singleBundleRestartMachInner_pre_le`: pre-log bound on the inner term of one branch restart
  (item 3 of `IsSpecOrdRestart`);
* `bundleEpoch_spanBatchCharge_restart_le_Tk`: cumulative dynamic-spanner update charge
  `∑ spanBatchChargeWith` over one non-restarted epoch `[s₀, t]`, using
  `spanBatchChargeWith_le_two_mul`, `spanBatchRate_le`, and Lemma 2.1 (`lemma_2_1`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

/-! ## 1. Envelope bound for `spanInitBound` summed over buckets -/

/-- Bounds `∑_{C ∈ actComps} ∑_{b ∈ actB C} c_sp * spanInitBound P_b E.L splitB (Hb C b)` in
terms of `(bundleCoreParams E).γ_r M * log^{p_T + 1}(M + N + 2)`. -/
lemma spanInitBound_buckets_to_env (E : SparseCoreEnv)
    (c_sp k M N : ℕ) {P_b : SparsifyParams} (hP : SparsifyParamsLe P_b (E.P_fn M))
    (hk : 1 ≤ k) (hN_pos : 1 ≤ N) {G₀ : MGraph}
    (actComps : Finset (Finset ℕ)) (hact_sub : actComps ⊆ components G₀)
    (actB : Finset ℕ → Finset ℤ) (Hb : Finset ℕ → ℤ → MGraph)
    (hcard : (components G₀).sum (fun C => (actB C).card) ≤ M)
    (hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M)
    (hn_2m : ∀ C ∈ components G₀, ∀ b ∈ actB C, (Hb C b).n ≤ 2 * (Hb C b).m) :
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let Lg := Real.log ((M : ℝ) + (N : ℝ) + 2)
    ((actComps.sum fun C => (actB C).sum fun b =>
        c_sp * spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b) : ℕ) : ℝ) ≤
      (c_sp : ℝ) * (21 * (7 : ℝ) ^ p_max + 16) *
        ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) := by
  intro P p_max Lg
  have hm_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
  have hLg1 : 1 ≤ Lg := by
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (M : ℝ) + (N : ℝ) + 2) (by norm_num) (by linarith))]
  have hLg_nn : 0 ≤ Lg := by linarith
  have hsub : ((actComps.sum fun C => (actB C).sum fun b =>
        c_sp * spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b) : ℕ) : ℝ) ≤
      (c_sp : ℝ) * ((components G₀).sum fun C => (actB C).sum fun b =>
        (spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b) : ℝ)) := by
    have hnat : (actComps.sum fun C => (actB C).sum fun b =>
          c_sp * spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b)) ≤
        c_sp * ((components G₀).sum fun C => (actB C).sum fun b =>
          spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b)) := by
      have h1 : (actComps.sum fun C => (actB C).sum fun b =>
            c_sp * spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b)) ≤
          (components G₀).sum fun C => (actB C).sum fun b =>
            c_sp * spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b) :=
        Finset.sum_le_sum_of_subset hact_sub
      refine le_trans h1 (le_of_eq ?_)
      simp only [Finset.mul_sum]
    exact_mod_cast hnat
  have hraw := spanInitBound_buckets_sum_le hP (bundleSplitBudget_le_add_one hk)
    (comps := components G₀) (actB := actB) (Hb := Hb) (L := E.L) hcard hm_sum hn_2m
  push_cast at hraw
  set logN := 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)
  set Λ := bundleLambda (E.P_fn M) M
  have hlogN_le : logN ≤ 7 * Lg := log_bundleNMax_le M N hN_pos
  have hlogN_ge1 : 1 ≤ logN := by
    dsimp only [logN]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)]
  have h7Lg_ge1 : 1 ≤ 7 * Lg := by linarith
  have hΛ_nn : 0 ≤ Λ := by linarith [bundleParams_lambda_ge_one (E.P_fn M) M]
  have hKs_nn : 0 ≤ (E.P_fn M).K_s := (E.P_fn M).hK_s
  have hKt_nn : 0 ≤ (E.P_fn M).K_t := (E.P_fn M).hK_t
  have hγℓ_nn : 0 ≤ (E.P_fn M).γ_ℓ := by linarith [(E.P_fn M).hγ_ℓ]
  have hbracket :
      (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * (Λ * logN) +
        2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ * Λ + 5 + (E.P_fn M).γ_ℓ + ((E.L : ℝ) + 1) * logN ≤
      7 * Lg * (((E.L : ℝ) + 1) +
        ((E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn M).γ_ℓ +
          2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ * Λ)) := by
    have h1 : (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * (Λ * logN) ≤
        7 * Lg * ((E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * Λ) := by
      have := mul_le_mul_of_nonneg_left hlogN_le
        (show 0 ≤ (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * Λ by positivity)
      linarith
    have h2 : ((E.L : ℝ) + 1) * logN ≤ 7 * Lg * ((E.L : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left hlogN_le (show 0 ≤ (E.L : ℝ) + 1 by positivity)
      linarith
    have h3 : 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ * Λ ≤
        7 * Lg * (2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ * Λ) :=
      le_mul_of_one_le_left (by positivity) h7Lg_ge1
    have h4 : (E.P_fn M).γ_ℓ ≤ 7 * Lg * (E.P_fn M).γ_ℓ :=
      le_mul_of_one_le_left hγℓ_nn h7Lg_ge1
    have h5 : (5 : ℝ) ≤ 7 * Lg * 3 := by linarith
    linarith
  obtain ⟨_, hKs_piece, _, _, hγ_le_rec, hLp1_cm⟩ :=
    bundleEnv_core_bounds E M (min N (M + 1)) (E.B_fn M) le_rfl (min_le_cn_mul_m_add_one E M N)
  obtain ⟨hΛ_bound, hΛ_mul_Λs⟩ := bundleLambda_le_logMN E M N hN_pos
  have hp2a := bundleCost_piece2a E M hLp1_cm hLg1
  have hp2b := bundleCost_piece2b E M hKs_piece hγ_le_rec hLp1_cm hLg1 hΛ_nn hΛ_bound hΛ_mul_Λs
  set T := ((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * Lg ^ (p_max + 1)
  have hγr_ge1 : 1 ≤ bundleRecBase E M * bundleCostMult E M :=
    one_le_mul_of_one_le_of_one_le
      (le_trans (by norm_num : (1 : ℝ) ≤ 4)
        (le_trans (bundleRecEnv_ge_four E M) (le_max_left _ _)))
      (bundleCostMult_ge_one E M)
  have hlog_pow_ge1 : 1 ≤ Lg ^ (p_max + 1) := one_le_pow₀ hLg1
  have hM_le_T : (M : ℝ) ≤ T := by
    have h1 : (1 : ℝ) ≤ (bundleRecBase E M * bundleCostMult E M) * Lg ^ (p_max + 1) :=
      one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
    have h2 : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
    calc (M : ℝ) = (M : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((M : ℝ) + 1) * ((bundleRecBase E M * bundleCostMult E M) * Lg ^ (p_max + 1)) :=
          mul_le_mul h2 h1 zero_le_one (by linarith)
      _ = T := by dsimp only [T]; ring
  have hM_le_TLg : (M : ℝ) ≤ T * Lg := le_trans hM_le_T (le_mul_of_one_le_right (by linarith) hLg1)
  have hsum_le : ((components G₀).sum fun C => (actB C).sum fun b =>
        (spanInitBound P_b E.L (bundleSplitBudget k M) (Hb C b) : ℝ)) ≤
      (21 * (7 : ℝ) ^ p_max + 16) * (T * Lg) := by
    have hmulM := mul_le_mul_of_nonneg_right hbracket hm_nn
    have hmid : (((E.L : ℝ) + 1) +
        ((E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn M).γ_ℓ +
          2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ * Λ)) * (M : ℝ) ≤
        (3 * (7 : ℝ) ^ p_max + 2) * T := by
      dsimp only [T, p_max]
      linarith [hp2a, hp2b]
    have h7mid := mul_le_mul_of_nonneg_left hmid (show 0 ≤ 7 * Lg by linarith)
    have hT_nn : 0 ≤ T * Lg := by linarith
    have hEq1 : 7 * Lg * ((3 * (7 : ℝ) ^ p_max + 2) * T) = (21 * (7 : ℝ) ^ p_max + 14) * (T * Lg) := by ring
    linarith [hraw, hmulM, h7mid, hEq1, hM_le_TLg, hT_nn]
  have hEq : (c_sp : ℝ) * (21 * (7 : ℝ) ^ p_max + 16) *
      ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) =
      (c_sp : ℝ) * ((21 * (7 : ℝ) ^ p_max + 16) * (T * Lg)) := by
    dsimp only [P, bundleCoreParams, T, p_max]
    rw [pow_succ]
    ring
  rw [hEq]
  exact le_trans hsub (mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg _))

/-! ## 2. Restart machine-cost bounds -/

/-- Pre-log bound on the inner term of a single branch restart at stage `r ≤ τ`. -/
lemma singleBundleRestartMachInner_pre_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M))
    (r j : ℕ) (hj : j < k) (hr : r ≤ τ) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let tr := (Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j
    let st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let Lg := Real.log ((M : ℝ) + (N : ℝ) + 2)
    ((tr.cs.G.m + 1 + tr.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
        spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
          (normGraph (restartBucketBundle tr (ord r) C b).graph) : ℕ) : ℝ) ≤
      (2 + (spanConst : ℝ) * (21 * (7 : ℝ) ^ p_max + 16)) *
        ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) := by
  classical
  intro Tb tr st₀ P p_max Lg
  have hk1 : 1 ≤ k := hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j (hHyps.hInit j hj) r hr
  have hk_tr : tr.k = k := hBun.1
  have hI_r : CompLSFInv E.C_lsst (D.ℓ 0) tr.cs := hBun.2.2.2.2.2.2.2.1
  have hcsG : tr.cs.G = D.G r := hBun.2.2.2.2.2.2.2.2.1
  have hact : tr.activeComps ⊆ components (D.G 0) := hBun.2.2.2.2.2.2.2.2.2.1.2
  have hm_cur : tr.cs.G.m ≤ 2 * M := by
    rw [hcsG]
    have h1 := dyn_G_m_le hD r hr
    have h2 := (updateThreshold_le_div_k_at hk hN_pos hThresh r hr).2
    omega
  obtain ⟨hcard0, hm0_sum, _, _⟩ := initBundleTreeWith_buckets_sum_le lsfInit E.L sparsify
    (M := M) (N := N) hk1 (G₀ := D.G 0) (D.ℓ 0) (ord 0) j
  have hE_sub0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (restartBucketBundle tr (ord r) C b).edges ⊆ (st₀.bun (C, b)).edges := by
    intro C hC b
    have hsub1 : (restartBucketBundle tr (ord r) C b).edges ⊆ (tr.bun (C, b)).edges :=
      initBundleFor_edges_subset tr.cs (ord r) (tr.bun (C, b)).edges tr.k
    have hsub2 : (tr.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := by
      rw [((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]
      exact Finset.sdiff_subset
    exact hsub1.trans hsub2
  have hm_sum : (components (D.G 0)).sum
      (fun C => (st₀.activeBuckets C).sum fun b =>
        (normGraph (restartBucketBundle tr (ord r) C b).graph).m) ≤ M := by
    refine le_trans (le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) hm0_sum) hM
    exact Finset.card_le_card (hE_sub0 C hC b)
  obtain ⟨ρ_r, hρ_r⟩ := orderedUpTo_rot_at hOrd hr hcsG
  have hn_2m : ∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
      (normGraph (restartBucketBundle tr (ord r) C b).graph).n ≤
        2 * (normGraph (restartBucketBundle tr (ord r) C b).graph).m := by
    intro C hC b _
    have hR := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
    have hEcore : (tr.bun (C, b)).edges ⊆ (coreGraph tr.cs.G tr.cs.lsf).E :=
      (hR.1 ρ_r hI_r.hG_val (compLSF_RF_isRSF hI_r) hρ_r).1
    dsimp only [restartBucketBundle]
    rw [hk_tr]
    exact initBundleFor_n_le_two_m tr.cs (ord r) hEcore hk
  have hbuck := spanInitBound_buckets_to_env E spanConst k M N hParams hk1 hN_pos
    tr.activeComps hact st₀.activeBuckets
    (fun C b => normGraph (restartBucketBundle tr (ord r) C b).graph)
    (le_trans hcard0 hM) hm_sum hn_2m
  have hLg1 : 1 ≤ Lg := by
    have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (M : ℝ) + (N : ℝ) + 2) (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) M]))]
  have hγr1 : 1 ≤ P.γ_r M := (bundleCoreParams_valid E).2.2.2.2.2.2.1 M
  have hpow1 : 1 ≤ Lg ^ (P.p_T + 1) := one_le_pow₀ hLg1
  have hm_curR : ((tr.cs.G.m + 1 : ℕ) : ℝ) ≤ 2 * (((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1)) := by
    have hmc : ((tr.cs.G.m + 1 : ℕ) : ℝ) ≤ 2 * ((M : ℝ) + 1) := by
      have : (tr.cs.G.m : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hm_cur
      push_cast; linarith
    have h1 : (1 : ℝ) ≤ P.γ_r M * Lg ^ (P.p_T + 1) := one_le_mul_of_one_le_of_one_le hγr1 hpow1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * ((M : ℝ) + 1) by positivity)
    linarith
  dsimp only at hbuck
  push_cast at hm_curR hbuck ⊢
  linarith [hbuck, hm_curR]

/-! ## 3. Per-epoch dynamic-spanner update charge bound (`spanBatchChargeWith`) -/

/-- Bounds the sum of `spanBatchChargeWith` over one non-restarted epoch `[s₀, t]` of branch `j`,
in the `Tk` envelope of `bundleCost_env_baseline_parts_noComp`. -/
lemma bundleEpoch_spanBatchCharge_restart_le_Tk (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M))
    (s₀ t j : ℕ) (hj : j < k) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let post := fun s => Tb.runOrdAfterRestarts k M N D ord restarts s
    let infoB := fun s => stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
    let Tk := ((M : ℝ) + 1) * ((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
      logMN ^ (p_max + 1)
    ∑ s ∈ Finset.Icc (s₀ + 1) t,
        ((((infoB (s - 1)).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b =>
            spanBatchChargeWith spanConst (params M) E.L
              ((((post (s - 1)).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
              (((post (s - 1)).trees j).initBunG (C, b))
              (((post (s - 1)).trees j).dyn (C, b)).G ((infoB (s - 1)).U_B (C, b)) : ℕ) : ℝ)) ≤
      (2 * (spanConst : ℝ)) * (12600 * (7 : ℝ) ^ p_max * Tk) +
        (2 * (spanConst : ℝ)) * (25200 * (7 : ℝ) ^ p_max *
          (((k : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1))) *
          ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
  classical
  intro Tb st₀ post infoB p_max logMN Tk
  have hk1 : 1 ≤ k := hk
  have hInit_j := hHyps.hInit j hj
  set ep := epochBundleSeq lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j
  set Δ := t - s₀
  set actB := st₀.activeBuckets
  set splitB := bundleSplitBudget k M
  set Hb := fun C b => normGraph ((ep 0).bun (C, b)).graph
  have hInv := epochBundleSeq_inv lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit_j hst htτ hs₀ hNoRest
  have hDyn := epochBundleSeq_dyn_spec lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
    k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest
  obtain ⟨hSt_base, hSt_step⟩ := epochBundleSeq_steps lsfInit E.C_lsst E.L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  have hInitG := epochBundleSeq_initBunG_eq lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
  set n_eff := min N (M + 1)
  set q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
  set q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
  set uc_ep := 2 * bundleUCRatio n_eff * (q_ep : ℝ)
  set ucBound := 2 * bundleUCRatio n_eff * (q_τ : ℝ)
  set Λ := bundleLambda (E.P_fn M) M
  set coeff := 90 * (E.L : ℝ) * bundleNRoot E.L M * ((E.P_fn M).K_t + (E.P_fn M).K_s + 1) *
    coreE_L E.L (E.P_fn M) * ((k : ℝ) + 1) * Λ
  have hcoeff_nn : 0 ≤ coeff := by
    dsimp only [coeff, bundleNRoot, coreE_L, Λ]
    have := (E.P_fn M).hK_t; have := (E.P_fn M).hK_s
    have : 0 ≤ (E.P_fn M).γ_c := by linarith [(E.P_fn M).hγ_c]
    have : 0 ≤ (E.P_fn M).γ_ℓ := by linarith [(E.P_fn M).hγ_ℓ]
    have : 0 ≤ bundleLambda (E.P_fn M) M := by linarith [bundleParams_lambda_ge_one (E.P_fn M) M]
    positivity
  -- Rewrite the LHS sum over `Finset.range Δ` in terms of `ep` and `Hb`.
  let U_B_ep : ℕ → Finset ℕ × ℤ → List Update := fun r p =>
    (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B p
  have hterm : ∀ r < Δ,
      (((infoB (s₀ + r)).state.activeComps.sum fun C =>
          (actB C).sum fun b =>
            spanBatchChargeWith spanConst (params M) E.L
              ((((post (s₀ + r)).trees j).initBunG (C, b)).n + splitB)
              (((post (s₀ + r)).trees j).initBunG (C, b))
              (((post (s₀ + r)).trees j).dyn (C, b)).G ((infoB (s₀ + r)).U_B (C, b)) : ℕ) : ℝ) =
        (ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ) := by
    intro r hr
    have hep : ep r = (post (s₀ + r)).trees j :=
      (epochBundleSeq_eq_post lsfInit E.C_lsst E.L sparsify k M N D ord restarts s₀ t j hst).1 r hr
    have hstep : ep (r + 1) = (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1))).state := (hSt_step r hr).1
    have hinfo : infoB (s₀ + r) = stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1))
        (ord (s₀ + r)) (ord (s₀ + r + 1)) := by dsimp only [infoB]; rw [hep]
    rw [hinfo, ← hstep]
    push_cast
    refine Finset.sum_congr rfl fun C hCA => Finset.sum_congr rfl fun b _ => ?_
    have hC : C ∈ components (D.G 0) := (hInv.2.2.1 (r + 1) hr).2.1 hCA
    have hIG : (ep r).initBunG (C, b) = Hb C b := hInitG r hr.le C hC b
    rw [← hep, hIG]
  rw [bundle_sum_Icc_succ_eq_sum_range]
  have hsum_eq : ∑ r ∈ Finset.range Δ,
      ((((infoB (s₀ + r + 1 - 1)).state.activeComps.sum fun C =>
          (actB C).sum fun b =>
            spanBatchChargeWith spanConst (params M) E.L
              ((((post (s₀ + r + 1 - 1)).trees j).initBunG (C, b)).n + splitB)
              (((post (s₀ + r + 1 - 1)).trees j).initBunG (C, b))
              (((post (s₀ + r + 1 - 1)).trees j).dyn (C, b)).G
              ((infoB (s₀ + r + 1 - 1)).U_B (C, b)) : ℕ) : ℝ)) =
      ∑ r ∈ Finset.range Δ, (ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
          ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ) :=
    Finset.sum_congr rfl fun r hr => by
      rw [show s₀ + r + 1 - 1 = s₀ + r by omega]
      exact hterm r (Finset.mem_range.mp hr)
  rw [hsum_eq]
  -- Root-growth and bundle-batch bounds over `[s₀, t]` (identical to `BundleRestartCostEpoch`).
  have hI_at : ∀ s ≤ τ, CompLSFInv E.C_lsst (D.ℓ 0)
      (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j s).1.cs ∧
      (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j s).1.cs.G = D.G s ∧
      (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j s).1.cs.G₀ = D.G 0 := fun s hs => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
      hV₀ j s).1
    have hb := hBun s hs
    exact ⟨hbp.cs ▸ hb.2.2.2.2.2.2.2.1, by rw [← hbp.cs]; exact hb.2.2.2.2.2.2.2.2.1,
      by rw [← hbp.cs, hb.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl⟩
  have hR_comp_sum : ∀ r < Δ,
      ((components (D.G 0)).sum fun C =>
        (((ep (r + 1)).cs.compSt C).R \ ((ep r).cs.compSt C).R).card) =
        ((ep (r + 1)).cs.RF.R \ (ep r).cs.RF.R).card := by
    intro r hr
    rw [(hSt_base (r + 1) hr).cs, (hSt_base r hr.le).cs]
    obtain ⟨hI_r, hG_r, hG0_r⟩ := hI_at (s₀ + r) (by omega)
    obtain ⟨hI_r1, _, _⟩ := hI_at (s₀ + (r + 1)) (by omega)
    have hDt := hD (s₀ + r + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.G.BatchIsValid
        (D.U (s₀ + r + 1)) := hG_r.symm ▸ hDt.1
    have hcs1 : (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs =
        compLSFBatch (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs
          (D.U (s₀ + r + 1)) := by
      rw [show s₀ + (r + 1) = (s₀ + r) + 1 by omega]
      exact bundleRunSeqWith_cs lsfInit E.L sparsify k M N D ord j (s₀ + r)
    have hsp := compLSFBatch_step_props (D.U (s₀ + r + 1)) hI_r hBU
    have heq := compLSF_sum_R_sdiff_eq hI_r hI_r1 (by rw [hcs1, compLSFBatch_G₀])
      (fun C hC => by rw [hcs1]; exact (hsp.2.2.1 C hC).2.2.2.1)
    rwa [hG0_r] at heq
  have hR_sum : ((∑ r ∈ Finset.range Δ, ((ep (r + 1)).cs.RF.R \ (ep r).cs.RF.R).card : ℕ) : ℝ) ≤
      112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
    have hstep_R : ∀ r < Δ,
        (((ep (r + 1)).cs.RF.R \ (ep r).cs.RF.R).card : ℝ) ≤
          112 * ((D.U (s₀ + r + 1)).length : ℝ) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
      intro r hr
      rw [(hSt_base (r + 1) hr).cs, (hSt_base r hr.le).cs]
      obtain ⟨hI_r, hG_r, hG0_r⟩ := hI_at (s₀ + r) (by omega)
      have hDt := hD (s₀ + r + 1) (Nat.succ_pos _) (by omega)
      simp only [Nat.add_sub_cancel] at hDt
      have hBU : (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.G.BatchIsValid
          (D.U (s₀ + r + 1)) := hG_r.symm ▸ hDt.1
      have hcs1 : (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs =
          compLSFBatch (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs
            (D.U (s₀ + r + 1)) := by
        rw [show s₀ + (r + 1) = (s₀ + r) + 1 by omega]
        exact bundleRunSeqWith_cs lsfInit E.L sparsify k M N D ord j (s₀ + r)
      have hsub : (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.RF.R ⊆
          (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs.RF.R := by
        rw [hcs1]; exact (compLSFBatch_decremental hI_r hBU).2
      have hR := compLSF_R_sum_le_min hI_r hBU
      rw [← hcs1, hG0_r] at hR
      have hc : (((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs.RF.R \
          (bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.RF.R).card : ℝ) =
          ((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + (r + 1))).1.cs.RF.R.card : ℝ) -
          ((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j (s₀ + r)).1.cs.RF.R.card : ℝ) := by
        rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
      have h2 : 56 * ((2 * (D.U (s₀ + r + 1)).length : ℕ) : ℝ) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 =
          112 * ((D.U (s₀ + r + 1)).length : ℝ) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by push_cast; ring
      linarith
    have hlog_le : (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
        (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
      have hnn : 0 ≤ Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2) :=
        (half_lt_log_add_two _).le.trans' (by norm_num)
      refine pow_le_pow_left₀ hnn (Real.log_le_log (by positivity) ?_) 2
      have hmin : min (D.G 0).n ((D.G 0).m + 1) ≤ n_eff := min_le_min hN (Nat.add_le_add_right hM 1)
      have hR : ((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) ≤ (n_eff : ℝ) := by exact_mod_cast hmin
      linarith
    have hq_eq : (q_ep : ℝ) = ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) := by
      dsimp only [q_ep]
      rw [Nat.cast_sum, bundle_sum_Icc_succ_eq_sum_range, Nat.add_sub_cancel_left]
    rw [Nat.cast_sum]
    calc (∑ r ∈ Finset.range Δ, (((ep (r + 1)).cs.RF.R \ (ep r).cs.RF.R).card : ℝ))
        ≤ ∑ r ∈ Finset.range Δ, (112 * ((D.U (s₀ + r + 1)).length : ℝ) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2) :=
          Finset.sum_le_sum fun r hr => hstep_R r (Finset.mem_range.mp hr)
      _ = 112 * (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) *
            (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = 112 * (q_ep : ℝ) * (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
          rw [hq_eq]
      _ ≤ 112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
  obtain ⟨hUB_single_ep, hUB_sum⟩ := bundle_epoch_U_B_sum_le
    (G₀ := D.G 0) (N := n_eff) (B_bound := E.B_fn M) (s₀ := s₀) (Δ := Δ) (D := D)
    actB (hHyps.activeBuckets_card_le (N := N) hj)
    (fun r => (ep r).cs) U_B_ep
    (fun r hr C hC b _ => ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr).2.2.1)
    (fun r hr => epochBundleSeq_deletes_sum_le lsfInit E.C_lsst E.L E.hL (E.P_fn M) sparsify
      k M N τ hk1 D ord restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit_j hst htτ hs₀ hNoRest hr)
    (fun r hr C hC b _ => ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 r hr).2.2.2.1)
    hR_comp_sum hR_sum
  have hq_le : q_ep ≤ q_τ := Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (by omega))
  have huc_le : uc_ep ≤ ucBound :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hq_le)
      (mul_nonneg zero_le_two (bundleUCRatio_pos n_eff).le)
  have huc_nn : 0 ≤ ucBound :=
    mul_nonneg (mul_nonneg zero_le_two (bundleUCRatio_pos n_eff).le) (Nat.cast_nonneg _)
  have hm_sum_M : (components (D.G 0)).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M :=
    le_trans hInv.2.1 hM
  -- Per-bucket bound: `∑ spanBatchChargeWith ≤ 2 * c_sp * coeff * (20 * (Hb.m + ∑ |U_B|) * log)`.
  have hb_bound : ∀ C ∈ components (D.G 0), ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB)
          (Hb C b) ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ)) ≤
        (2 * (spanConst : ℝ)) * coeff *
          (20 * (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)) *
            Real.log ((M : ℝ) + ucBound + 2)) := by
    intro C hC b hb
    have hm_b : (Hb C b).m ≤ M := le_trans
      (Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb)
      (le_trans (Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
        (fun _ _ => Nat.zero_le _) hC) hm_sum_M)
    have hn_2m : (Hb C b).n ≤ 2 * (Hb C b).m := (hInv.1 C hC b).2.2.1
    have hdeg_b : (Hb C b).maxDeg ≤ k := by
      dsimp only [Hb]; rw [normGraph_maxDeg]; exact (hInv.1 C hC b).2.2.2.1
    have hnMax_le : (Hb C b).n + splitB ≤ bundleNMax M := by
      have hspB := bundleSplitBudget_le_add_one (M := M) hk1
      unfold bundleNMax; omega
    have hrate : spanBatchRate (params M) E.L ((Hb C b).n + splitB) (Hb C b) ≤ coeff :=
      spanBatchRate_le hParams hnMax_le hm_b hdeg_b
    have hstep_le : ∀ r ∈ Finset.range Δ,
        (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ) ≤
          (2 * (spanConst : ℝ)) * coeff *
            (((ep r).dyn (C, b)).G.batchEnc (U_B_ep r (C, b)) : ℝ) := by
      intro r _
      have h1 := spanBatchChargeWith_le_two_mul hConst (params M) E.hL ((Hb C b).n + splitB)
        (Hb C b) ((ep r).dyn (C, b)).G (U_B_ep r (C, b))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrate (show 0 ≤ 2 * (spanConst : ℝ) by positivity))
        (Nat.cast_nonneg (((ep r).dyn (C, b)).G.batchEnc (U_B_ep r (C, b))))
      linarith
    -- Lemma 2.1 on `Gb r := ((ep r).dyn (C, b)).G`
    set ub_tot := ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)
    have henc_b : (∑ r ∈ Finset.range Δ, (((ep r).dyn (C, b)).G.batchEnc (U_B_ep r (C, b)) : ℝ)) ≤
        20 * (((Hb C b).m : ℝ) + ub_tot) * Real.log ((M : ℝ) + ucBound + 2) := by
      let Gb : ℕ → MGraph := fun r => ((ep r).dyn (C, b)).G
      let Ub : ℕ → List Update := fun r => if r = 0 then [] else U_B_ep (r - 1) (C, b)
      have hval0 : (Gb 0).IsValid := ((hDyn C hC b).2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)).2.2.1
      have hm0 : (Gb 0).m = (Hb C b).m := by
        dsimp only [Gb, Hb]
        rw [normGraph_m]
        exact graphEq_m ((hDyn C hC b).2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)).2.1
      have hval_b : ∀ r, 1 ≤ r → r ≤ Δ →
          (Gb (r - 1)).BatchIsValid (Ub r) ∧ Gb r = (Gb (r - 1)).applyBatch (Ub r) := by
        intro r hr1 hrΔ
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
        simp only [Ub, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Nat.succ_eq_add_one]
        have hs := (hDyn C hC b).2.2.2.2.2.2.2.2.2.2 s hrΔ
        have hsp := (hInv.2.2.2.1 s hrΔ).2.2.2.1 C hC b
        exact ⟨hs.2.1, by dsimp only [Gb]; rw [← hsp.2.1, hsp.1, update_G_eq]⟩
      have hL21 := MinCostFlow.Chain.lemma_2_1 (G := Gb) (U := Ub) (τ := Δ) hval0 hval_b
      have hsum_enc : ∑ r ∈ Finset.Icc 1 Δ, (Gb (r - 1)).batchEnc (Ub r) =
          ∑ r ∈ Finset.range Δ, (Gb r).batchEnc (U_B_ep r (C, b)) := by
        refine Finset.sum_bij (fun r _ => r - 1)
          (fun r hr => by simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega)
          (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
          (fun r hr => ⟨r + 1, by simp only [Finset.mem_range, Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
          (fun r hr => by
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
            have hne : r ≠ 0 := by omega
            simp [Ub, hne])
      have hsum_len : ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) = ub_tot := by
        have hbij : ∑ r ∈ Finset.Icc 1 Δ, (Ub r).length =
            ∑ r ∈ Finset.range Δ, (U_B_ep r (C, b)).length := by
          refine Finset.sum_bij (fun r _ => r - 1)
            (fun r hr => by simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega)
            (fun a ha b hb h => by simp only [Finset.mem_Icc] at ha hb; omega)
            (fun r hr => ⟨r + 1, by simp only [Finset.mem_range, Finset.mem_Icc] at hr ⊢; omega, by omega⟩)
            (fun r hr => by
              have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
              have hne : r ≠ 0 := by omega
              simp [Ub, hne])
        rw [hbij, Nat.cast_sum]
      rw [hm0, hsum_enc, Nat.cast_sum, hsum_len] at hL21
      refine le_trans hL21 ?_
      have hub_le : ub_tot ≤ ucBound := le_trans (hUB_single_ep C hC b hb) huc_le
      have hub_nn : 0 ≤ ub_tot := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hmR : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_b
      have hlog_le : Real.log (((Hb C b).m : ℝ) + ub_tot + 2) ≤
          Real.log ((M : ℝ) + ucBound + 2) :=
        Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) (Hb C b).m]) (by linarith)
      exact mul_le_mul_of_nonneg_left hlog_le (by linarith [Nat.cast_nonneg (α := ℝ) (Hb C b).m])
    calc ∑ r ∈ Finset.range Δ, (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB)
            (Hb C b) ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ)
        ≤ ∑ r ∈ Finset.range Δ, ((2 * (spanConst : ℝ)) * coeff *
            (((ep r).dyn (C, b)).G.batchEnc (U_B_ep r (C, b)) : ℝ)) :=
          Finset.sum_le_sum hstep_le
      _ = (2 * (spanConst : ℝ)) * coeff *
            ∑ r ∈ Finset.range Δ, (((ep r).dyn (C, b)).G.batchEnc (U_B_ep r (C, b)) : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left henc_b (by positivity)
  -- Sum over active components and buckets, then apply `bundleCost_env_baseline_parts_noComp`.
  have hstep_sub :
      (∑ r ∈ Finset.range Δ, (ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ)) ≤
      ∑ r ∈ Finset.range Δ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ) :=
    Finset.sum_le_sum fun r hr =>
      Finset.sum_le_sum_of_subset_of_nonneg (hInv.2.2.1 (r + 1) (Finset.mem_range.mp hr)).2.1
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hcomm :
      (∑ r ∈ Finset.range Δ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ)) =
      (components (D.G 0)).sum fun C => (actB C).sum fun b =>
        ∑ r ∈ Finset.range Δ, (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB)
          (Hb C b) ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
  have hinner_sum :
      ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
        (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ))) ≤
        (M : ℝ) + (E.B_fn M : ℝ) * uc_ep := by
    have hm_r : ((components (D.G 0)).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) ≤
        (M : ℝ) := by
      simp only [← Nat.cast_sum]
      exact_mod_cast hm_sum_M
    simp only [Finset.sum_add_distrib]
    linarith [hm_r, hUB_sum]
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + ucBound + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have htotal :
      (∑ r ∈ Finset.range Δ, (ep (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          (spanBatchChargeWith spanConst (params M) E.L ((Hb C b).n + splitB) (Hb C b)
            ((ep r).dyn (C, b)).G (U_B_ep r (C, b)) : ℝ)) ≤
      (2 * (spanConst : ℝ)) * (coeff * (20 * ((M : ℝ) + (E.B_fn M : ℝ) * uc_ep) *
        Real.log ((M : ℝ) + ucBound + 2))) := by
    calc _ ≤ _ := hstep_sub
      _ = _ := hcomm
      _ ≤ (components (D.G 0)).sum fun C => (actB C).sum fun b =>
            (2 * (spanConst : ℝ)) * coeff *
              (20 * (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)) *
                Real.log ((M : ℝ) + ucBound + 2)) :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hb_bound C hC b hb
      _ = (2 * (spanConst : ℝ)) * (coeff * (20 *
            ((components (D.G 0)).sum fun C => (actB C).sum fun b =>
              (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ))) *
            Real.log ((M : ℝ) + ucBound + 2))) := by
          simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ _ := by gcongr
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  obtain ⟨_, hd5, _⟩ := bundleCost_env_baseline_parts_noComp E k M N (activeSubgraph (D.G 0)).n
    ((Finset.Icc 1 τ).sum fun s => (D.U s).length) hN_pos
    (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
  have h5 := hd5 q_ep
  have hq_eq : (q_ep : ℝ) = ∑ s ∈ Finset.Icc (s₀ + 1) t, ((D.U s).length : ℝ) := by
    dsimp only [q_ep, Δ]
    rw [show s₀ + (t - s₀) = t by omega, Nat.cast_sum]
  refine le_trans htotal ?_
  have hmul := mul_le_mul_of_nonneg_left h5 (show 0 ≤ 2 * (spanConst : ℝ) by positivity)
  refine le_trans hmul (le_of_eq ?_)
  rw [hq_eq]
  ring

end MinCostFlow.Chain

end
