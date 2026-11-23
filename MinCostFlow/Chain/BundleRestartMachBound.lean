module

public import MinCostFlow.Chain.BundleRestartMachEpoch
import MinCostFlow.SparseCore.BundleCostEnv
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Machine-cost bounds for one branch

Publicly re-exports `BundleRestartMachEpoch` (`spanInitBound_buckets_to_env`,
`singleBundleRestartMachInner_pre_le`, `bundleEpoch_spanBatchCharge_restart_le_Tk`) and proves:
* `bundleBranchWith_machCost_restart_le` and `bundleBranch_machCost_restart_le`: the total machine
  cost of branch `j` after stage `τ`, bounded by
  `(1 + R_j) · c_T' · (M + 1) · (k + 1) · γ_r(M) · log^{p_T'}(M + N + 2)` with the parameters of
  `bundleCoreParamsMachWith E spanConst`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

/-! ## 1. Output encodings and LSF batches (reused on `Tb`) -/

private lemma bundleBranch_US_enc_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    let infoR := fun s =>
      stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    ((∑ s ∈ Finset.range τ, ((post s).trees j).S_cur.batchEnc (infoR s).U_S : ℕ) : ℝ) ≤
      (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
          ((bundleCoreParams E).γ_r M * ((M : ℝ) / (k : ℝ))) +
        (bundleCoreParams E).γ_r M *
          (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := by
  intro T post infoR
  set P := bundleCoreParams E
  have hValP := bundleCoreParams_valid E
  have hγr_nn : 0 ≤ P.γ_r M := by linarith [hValP.2.2.2.2.2.2.1 M]
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord_post : ∀ s, (post s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.2.2.2
      hV₀).2
  have h4 := bundleRestart_spec_item4 E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD
    hLen hWeak hOrd hM hN hrest hThresh hHyps hV₀
  dsimp only at h4
  set f : ℕ → ℝ := fun s => ((T.S (post (s - 1)) j).batchEnc
    ((T.runOrdAfterUpdate k M N D ord restarts s).2 j) : ℝ) with hf
  have hA_nn : 0 ≤ P.γ_r M * ((M : ℝ) / (k : ℝ)) := by positivity
  have hpart := bundle_epoch_partition_sum_le restarts j τ f (fun s => ((D.U s).length : ℝ))
    (P.γ_r M * ((M : ℝ) / (k : ℝ))) (P.γ_r M) hA_nn
    (fun s₀ t hst htτ hs₀ hNoRest => by
      have h := (h4 s₀ t hst htτ j hj hs₀ hNoRest).2
      push_cast at h
      simp only [hf]
      linarith) τ le_rfl
  have hUS_eq : ∀ s, (infoR s).U_S = (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).2 j :=
    fun s => by
      dsimp only [infoR, post, T]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
        sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne s), hord_post s]
  have hS_eq : ∀ s, T.S (post s) j = ((post s).trees j).S_cur := fun s => by
    dsimp only [T]; rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left (hne s)]
  have hsum_eq : ((∑ s ∈ Finset.range τ, ((post s).trees j).S_cur.batchEnc (infoR s).U_S : ℕ) : ℝ)
      = ∑ s ∈ Finset.Icc 1 τ, f s := by
    rw [Nat.cast_sum, ← bundle_sum_range_eq_sum_Icc_succ f τ]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hf, Nat.add_sub_cancel, hS_eq, hUS_eq]
  have hCount : ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0) ≤
      ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun r _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => ((restarts r).count j : ℝ))
        (fun x hx => by simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega)
        (fun _ _ _ => Nat.cast_nonneg _))
    split_ifs with hmem
    · exact_mod_cast List.count_pos_iff.mpr hmem
    · exact Nat.cast_nonneg _
  have hq : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) =
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := by rw [Nat.cast_sum]
  rw [hsum_eq]
  rw [hq] at hpart
  have hmul := mul_le_mul_of_nonneg_right (add_le_add_left hCount 1) hA_nn
  linarith

private lemma bundleBranch_lsfBatch_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) (hV₀ : (D.G 0).V.Nonempty)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    ∑ s ∈ Finset.range τ, lsfBatchSize ((post s).trees j).cs (D.U (s + 1)) ≤
      6 * (Finset.Icc 1 τ).sum fun s => (D.U s).length := by
  intro T post
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j (hHyps.hInit j hj)
  have hstep : ∀ s ∈ Finset.range τ,
      lsfBatchSize ((post s).trees j).cs (D.U (s + 1)) ≤ 6 * (D.U (s + 1)).length := by
    intro s hs
    have hsτ : s < τ := Finset.mem_range.mp hs
    have hbp := runOrdAfterRestarts_base_proj lsfInit E.C_lsst E.L sparsify k M N D ord restarts
      hV₀ j s
    have hcs : ((post s).trees j).cs = ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).cs :=
      hbp.2.cs.trans hbp.1.cs.symm
    have hb := hBun s hsτ.le
    have hI : CompLSFInv E.C_lsst (D.ℓ 0) ((post s).trees j).cs := hcs ▸ hb.2.2.2.2.2.2.2.1
    have hG : ((post s).trees j).cs.G = D.G s := hcs ▸ hb.2.2.2.2.2.2.2.2.1
    have hDt := hD (s + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : ((post s).trees j).cs.G.BatchIsValid (D.U (s + 1)) := hG.symm ▸ hDt.1
    exact lsfBatchSize_le hI hBU
  calc ∑ s ∈ Finset.range τ, lsfBatchSize ((post s).trees j).cs (D.U (s + 1))
      ≤ ∑ s ∈ Finset.range τ, 6 * (D.U (s + 1)).length := Finset.sum_le_sum hstep
    _ = 6 * (Finset.Icc 1 τ).sum fun s => (D.U s).length := by
      rw [← Finset.mul_sum]
      congr 1
      have h := bundle_sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ
      exact_mod_cast h

/-! ## 2. Final per-branch machine-cost bound -/

/-- **Machine cost of one branch (generalized to any `lsfInit`, `params`, `spanConst`).**
After stage `τ` of a run with restarts on a nonempty initial graph, the machine cost of branch `j`
is at most `(1 + R_j) · c_T' · (M + 1) · (k + 1) · γ_r(M) · log^{p_T'}(M + N + 2)` with the
constants of `bundleCoreParamsMachWith E spanConst`. -/
theorem bundleBranchWith_machCost_restart_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M))
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) (hj : j < k) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    (((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℝ) ≤
      (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        (P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P'.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T) := by
  classical
  intro Tm P'
  set Tb := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
  set P := bundleCoreParams E
  set p_max := max E.p_s_hi E.p_t_hi
  set Lg := Real.log ((M : ℝ) + (N : ℝ) + 2)
  set lg := bundleLogFactor M N
  set Rc := ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)
  set q : ℝ := (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ)
  set c_sp : ℝ := (spanConst : ℝ)
  set K := ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M
  set Tk := K * Lg ^ P.p_T
  have hk1 : 1 ≤ k := hk
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
    ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
  have hValP := bundleCoreParams_valid E
  have hγr1 : 1 ≤ P.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hLg1 : 1 ≤ Lg := by
    have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
    linarith [lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (M : ℝ) + (N : ℝ) + 2) (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) M]))]
  have hLg_nn : 0 ≤ Lg := by linarith
  have hc_sp1 : 1 ≤ c_sp := by dsimp only [c_sp]; exact_mod_cast hConst
  have hK_nn : 0 ≤ K := by dsimp only [K]; positivity
  have hRc_nn : 0 ≤ Rc := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hR1 : 1 ≤ 1 + Rc := by linarith
  have hlg_le : (lg : ℝ) ≤ 16 * Lg ^ 2 := bundleLogFactor_le M N
  have hpow1 : 1 ≤ Lg ^ P.p_T := one_le_pow₀ hLg1
  have hpow_le_succ : Lg ^ P.p_T ≤ Lg ^ (P.p_T + 1) := pow_le_pow_right₀ hLg1 (Nat.le_succ _)
  have hTk_nn : 0 ≤ Tk := mul_nonneg hK_nn (by positivity)
  have hTk_le_Lg : Tk ≤ K * Lg ^ (P.p_T + 1) := mul_le_mul_of_nonneg_left hpow_le_succ hK_nn
  have hK_le_Tk : K ≤ Tk := le_mul_of_one_le_right hK_nn hpow1
  have hK_le_TLg : K ≤ K * Lg ^ (P.p_T + 1) := le_trans hK_le_Tk hTk_le_Lg
  have hM1_le_K : (M : ℝ) + 1 ≤ K := by
    dsimp only [K]
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) * P.γ_r M :=
      one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) hγr1
    calc (M : ℝ) + 1 = ((M : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ ((M : ℝ) + 1) * (((k : ℝ) + 1) * P.γ_r M) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M := by ring
  have hMγ_le_K : ((M : ℝ) + 1) * P.γ_r M ≤ K := by
    dsimp only [K]
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    calc ((M : ℝ) + 1) * P.γ_r M = ((M : ℝ) + 1) * 1 * P.γ_r M := by ring
      _ ≤ ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_ge1 (by positivity)) (by linarith)
  have hqk := (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).1
  have hqM : q ≤ (M : ℝ) := le_trans hqk (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hk))
  -- 1. Decomposition from `bundleWith_branch_machCost_le`
  have hDecomp := bundleWith_branch_machCost_le lsfInit E.C_lsst E.L E.hL sparsify params spanConst
    hConst k M N D ord restarts hV₀ j τ
  have hDecompR : (((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℝ) ≤
      (lg : ℝ) * (
        (3 * ((D.G 0).m : ℝ) + 3 * ((activeSubgraph (D.G 0)).n : ℝ) + 2) +
        (lsfInitSize (D.G 0) : ℝ) * (lg : ℝ) ^ 2 +
        ((((Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j).activeComps.sum
          fun C => ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum
            fun b => spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
              (normGraph ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).bun (C, b)).graph) : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).S_cur.batchEnc
          (stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).U_S : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, lsfBatchSize ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs
          (D.U (s + 1)) : ℕ) : ℝ) +
        2 * ((∑ s ∈ Finset.range τ,
          ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanBatchChargeWith spanConst (params M) E.L
                  ((((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b))
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).dyn (C, b)).G
                  ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
                    (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b))) : ℕ) : ℝ) +
        ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
          ((((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).cs.G.m + 1 +
            ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
                  (normGraph (restartBucketBundle ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j)
                    (ord r) C b).graph))) : ℕ) : ℝ)) := by
    have hR : ((((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℕ) : ℝ) ≤ _ :=
      Nat.cast_le.mpr hDecomp
    push_cast at hR ⊢
    exact hR
  -- 2. Term-by-term bounds
  have hBase_le : 3 * ((D.G 0).m : ℝ) + 3 * ((activeSubgraph (D.G 0)).n : ℝ) + 2 ≤
      9 * (K * Lg ^ (P.p_T + 1)) := by
    have hact : (activeSubgraph (D.G 0)).n ≤ 2 * (D.G 0).m := activeSubgraph_n_le_two_m hG₀
    have h1 : 3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2 ≤ 9 * (M + 1) := by omega
    have h1R : 3 * ((D.G 0).m : ℝ) + 3 * ((activeSubgraph (D.G 0)).n : ℝ) + 2 ≤ 9 * ((M : ℝ) + 1) := by
      exact_mod_cast h1
    linarith [hM1_le_K, hK_le_TLg]
  have hLsfInit_le : (lsfInitSize (D.G 0) : ℝ) * (lg : ℝ) ^ 2 ≤ 1024 * K * Lg ^ 4 := by
    have h1 : (lsfInitSize (D.G 0) : ℝ) ≤ 4 * (M : ℝ) := by
      have := lsfInitSize_le hG₀
      exact_mod_cast le_trans this (Nat.mul_le_mul_left 4 hM)
    have hlg2_le : (lg : ℝ) ^ 2 ≤ (16 * Lg ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlg_le 2
    have h2 := mul_le_mul h1 hlg2_le (by positivity) (by positivity)
    have h3 : 4 * (M : ℝ) * (16 * Lg ^ 2) ^ 2 = 1024 * (M : ℝ) * Lg ^ 4 := by ring
    have h4 : 1024 * (M : ℝ) * Lg ^ 4 ≤ 1024 * K * Lg ^ 4 := by
      have : (M : ℝ) ≤ K := by linarith
      gcongr
    linarith
  have hLazy_le :
      ((((Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j).activeComps.sum
        fun C => ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum
          fun b => spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
            (normGraph ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).bun (C, b)).graph) : ℕ) : ℝ) ≤
      c_sp * (21 * (7 : ℝ) ^ p_max + 16) * (K * Lg ^ (P.p_T + 1)) := by
    obtain ⟨hcard0, hm0_sum, hn0_2m, _⟩ := initBundleTreeWith_buckets_sum_le lsfInit E.L sparsify
      (M := M) (N := N) hk1 (G₀ := D.G 0) (D.ℓ 0) (ord 0) j
    have hact_sub : ((Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j).activeComps ⊆
        components (D.G 0) := by
      have hbf := (foldl_bundleRestart_props lsfInit E.C_lsst E.L sparsify
        (Tb.runOrdAfterUpdate k M N D ord restarts τ).1 (restarts τ)).2.2.2.2.1 j
      have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
        k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j (hHyps.hInit j hj) τ le_rfl
      change ((List.foldl (sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify).restart
        (Tb.runOrdAfterUpdate k M N D ord restarts τ).1 (restarts τ)).trees j).activeComps ⊆ _
      rw [hbf.activeComps]; exact hBun.2.2.2.2.2.2.2.2.2.1.2
    have h1 := spanInitBound_buckets_to_env E spanConst k M N hParams hk1 hN_pos
      ((Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j).activeComps hact_sub
      (initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets
      (fun C b => normGraph ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).bun (C, b)).graph)
      (le_trans hcard0 hM) (le_trans hm0_sum hM) (fun C _ b _ => hn0_2m C b)
    have h2 : c_sp * (21 * (7 : ℝ) ^ p_max + 16) * ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) ≤
        c_sp * (21 * (7 : ℝ) ^ p_max + 16) * (K * Lg ^ (P.p_T + 1)) := by
      have hEq1 : c_sp * (21 * (7 : ℝ) ^ p_max + 16) * ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) =
          c_sp * (21 * (7 : ℝ) ^ p_max + 16) * (((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1)) := by ring
      rw [hEq1]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMγ_le_K (by positivity)) (by positivity)
    exact le_trans h1 h2
  have hU_le : ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) ≤ K * Lg ^ (P.p_T + 1) := by
    have hq_eq : ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) = q := by
      rw [Nat.cast_sum, bundle_sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ]
      dsimp only [q]; rw [Nat.cast_sum]
    rw [hq_eq]; linarith [hqM, hM1_le_K, hK_le_TLg]
  have hUS_le :
      ((∑ s ∈ Finset.range τ, ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).S_cur.batchEnc
        (stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).U_S : ℕ) : ℝ) ≤
      (1 + Rc) * (2 * (K * Lg ^ (P.p_T + 1))) := by
    have hUS := bundleBranch_US_enc_le E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD
      hLen hWeak hOrd hM hN hrest hThresh hHyps hV₀ j hj
    dsimp only at hUS
    have hMk : (M : ℝ) / (k : ℝ) ≤ (M : ℝ) + 1 :=
      le_trans (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hk)) (by linarith)
    have h1 : P.γ_r M * ((M : ℝ) / (k : ℝ)) ≤ K * Lg ^ (P.p_T + 1) := by
      have ha : P.γ_r M * ((M : ℝ) / (k : ℝ)) ≤ P.γ_r M * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hMk (by linarith)
      have hb : P.γ_r M * ((M : ℝ) + 1) = ((M : ℝ) + 1) * P.γ_r M := mul_comm _ _
      exact le_trans ha (le_trans (hb ▸ hMγ_le_K) hK_le_TLg)
    have h2 : P.γ_r M * q ≤ K * Lg ^ (P.p_T + 1) := by
      have ha : P.γ_r M * q ≤ P.γ_r M * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hb : P.γ_r M * ((M : ℝ) + 1) = ((M : ℝ) + 1) * P.γ_r M := mul_comm _ _
      exact le_trans ha (le_trans (hb ▸ hMγ_le_K) hK_le_TLg)
    have h3 : P.γ_r M * q ≤ (1 + Rc) * (K * Lg ^ (P.p_T + 1)) :=
      le_trans h2 (le_mul_of_one_le_left (by positivity) hR1)
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 + Rc)
    linarith
  have hLSF_le :
      ((∑ s ∈ Finset.range τ, lsfBatchSize ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs
        (D.U (s + 1)) : ℕ) : ℝ) ≤ 6 * (K * Lg ^ (P.p_T + 1)) := by
    have h1 := bundleBranch_lsfBatch_le E lsfInit sparsify k τ M N D ord restarts hk hG₀ hD hOrd
      hℓ₀ hHyps hV₀ j hj
    have h1R : ((∑ s ∈ Finset.range τ, lsfBatchSize ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs
        (D.U (s + 1)) : ℕ) : ℝ) ≤ 6 * q := by
      have : _ ≤ ((6 * (Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := Nat.cast_le.mpr h1
      dsimp only [q]
      push_cast at this ⊢
      exact this
    linarith [hqM, hM1_le_K, hK_le_TLg]
  -- 3. Epoch-partitioned dynamic-spanner update charge
  have hDyn_le :
      ((∑ s ∈ Finset.range τ,
        ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
            ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) E.L
                ((((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b))
                (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).dyn (C, b)).G
                ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
                  (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b))) : ℕ) : ℝ) ≤
      (1 + Rc) * ((2 * c_sp * 37800 * (7 : ℝ) ^ p_max) * (K * Lg ^ (P.p_T + 1))) := by
    set f : ℕ → ℝ := fun s =>
      (((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
          (D.U s) (ord (s - 1)) (ord s)).state.activeComps.sum fun C =>
            ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) E.L
                ((((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                (((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).initBunG (C, b))
                (((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).dyn (C, b)).G
                ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
                  (D.U s) (ord (s - 1)) (ord s)).U_B (C, b)) : ℕ) : ℝ)
    have hpart := bundle_epoch_partition_sum_le restarts j τ f (fun s => ((D.U s).length : ℝ))
      ((2 * c_sp) * (12600 * (7 : ℝ) ^ p_max * Tk))
      ((2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T)))
      (by positivity)
      (fun s₀ t hst htτ hs₀ hNoRest => by
        have hEp := bundleEpoch_spanBatchCharge_restart_le_Tk E lsfInit sparsify params spanConst
          hConst k M N τ D ord restarts hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps hParams
          s₀ t j hj hst htτ hs₀ hNoRest
        dsimp only at hEp
        have hf_eq : ∑ s ∈ Finset.Icc (s₀ + 1) t, f s =
            ∑ s ∈ Finset.Icc (s₀ + 1) t,
              (((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
                (D.U (s - 1 + 1)) (ord (s - 1)) (ord (s - 1 + 1))).state.activeComps.sum fun C =>
                  ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                    spanBatchChargeWith spanConst (params M) E.L
                      ((((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                      (((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).initBunG (C, b))
                      (((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j).dyn (C, b)).G
                      ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
                        (D.U (s - 1 + 1)) (ord (s - 1)) (ord (s - 1 + 1))).U_B (C, b)) : ℕ) : ℝ) :=
          Finset.sum_congr rfl fun s hs => by
            have hs1 : 1 ≤ s := by have := (Finset.mem_Icc.mp hs).1; omega
            simp only [f, Nat.sub_add_cancel hs1]
        rw [hf_eq]
        exact hEp) τ le_rfl
    have hsum_eq :
        ((∑ s ∈ Finset.range τ,
          ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanBatchChargeWith spanConst (params M) E.L
                  ((((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b))
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).dyn (C, b)).G
                  ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
                    (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b))) : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc 1 τ, f s := by
      rw [Nat.cast_sum, ← bundle_sum_range_eq_sum_Icc_succ f τ]
      refine Finset.sum_congr rfl fun s _ => by simp only [f, Nat.add_sub_cancel]
    have hCount : ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0) ≤ Rc := by
      refine le_trans (Finset.sum_le_sum fun r _ => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => ((restarts r).count j : ℝ))
          (fun x hx => by simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega)
          (fun _ _ _ => Nat.cast_nonneg _))
      split_ifs with hmem
      · exact_mod_cast List.count_pos_iff.mpr hmem
      · exact Nat.cast_nonneg _
    have hq_cast : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) = q := by dsimp only [q]; rw [Nat.cast_sum]
    rw [hsum_eq]; rw [hq_cast] at hpart
    have hq_term : (2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T)) * q ≤
        (1 + Rc) * ((2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * Tk)) := by
      have h1 : (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T) * q ≤ Tk := by
        have hqM1 : q ≤ (M : ℝ) + 1 := by linarith
        have hfac_nn : 0 ≤ ((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T := by positivity
        have hmul := mul_le_mul_of_nonneg_left hqM1 hfac_nn
        have hEq : (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T) * ((M : ℝ) + 1) = Tk := by
          dsimp only [Tk, K]; ring
        linarith
      have h2 : (2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T)) * q ≤
          (2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * Tk) := by
        have hEq : (2 * c_sp) * (25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T)) * q =
            (2 * c_sp * 25200 * (7 : ℝ) ^ p_max) * ((((k : ℝ) + 1) * P.γ_r M * Lg ^ P.p_T) * q) := by ring
        rw [hEq]
        have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * c_sp * 25200 * (7 : ℝ) ^ p_max by positivity)
        linarith
      exact le_trans h2 (le_mul_of_one_le_left (by positivity) hR1)
    have h1 := mul_le_mul_of_nonneg_right (add_le_add_left hCount 1)
      (show 0 ≤ (2 * c_sp) * (12600 * (7 : ℝ) ^ p_max * Tk) by positivity)
    have h2 : (1 + Rc) * ((2 * c_sp * 37800 * (7 : ℝ) ^ p_max) * Tk) ≤
        (1 + Rc) * ((2 * c_sp * 37800 * (7 : ℝ) ^ p_max) * (K * Lg ^ (P.p_T + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTk_le_Lg (by positivity)) (by linarith)
    linarith
  -- 4. Restart sum
  have hRest_le :
      ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
        ((((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).cs.G.m + 1 +
          ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).activeComps.sum fun C =>
            ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
              spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
                (normGraph (restartBucketBundle ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j)
                  (ord r) C b).graph))) : ℕ) : ℝ) ≤
      (1 + Rc) * ((2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1))) := by
    rw [Nat.cast_sum]
    have hper : ∀ r ∈ Finset.range (τ + 1),
        (((restarts r).count j *
          (((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).cs.G.m + 1 +
            ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
                  (normGraph (restartBucketBundle ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j)
                    (ord r) C b).graph)) : ℕ) : ℝ) ≤
        ((restarts r).count j : ℝ) *
          ((2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1))) := by
      intro r hr
      rw [Nat.cast_mul]
      have h1 := singleBundleRestartMachInner_pre_le E lsfInit sparsify params spanConst
        k M N τ D ord restarts hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps hParams
        r j hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      have h2 : (2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) ≤
          (2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1)) := by
        have hEq : (2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) =
            (2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1)) := by ring
        rw [hEq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMγ_le_K (by positivity)) (by positivity)
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (Nat.cast_nonneg _)
    calc _ ≤ ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) *
            ((2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1))) :=
          Finset.sum_le_sum hper
      _ = Rc * ((2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1))) := by
          rw [← Finset.sum_mul]
      _ ≤ (1 + Rc) * ((2 + c_sp * (21 * (7 : ℝ) ^ p_max + 16)) * (K * Lg ^ (P.p_T + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  -- 5. Combine all terms and multiply by `lg ≤ 16 * Lg ^ 2`
  set p_br := max 4 (P.p_T + 1)
  have h1leR : ∀ x : ℝ, 0 ≤ x → x ≤ (1 + Rc) * x := fun x hx => le_mul_of_one_le_left hx hR1
  have hLg4_le : Lg ^ 4 ≤ Lg ^ p_br :=
    pow_le_pow_right₀ hLg1 (le_max_left _ _)
  have hLg_pT_le : Lg ^ (P.p_T + 1) ≤ Lg ^ p_br :=
    pow_le_pow_right₀ hLg1 (le_max_right _ _)
  have hKLg_le : K * Lg ^ (P.p_T + 1) ≤ K * Lg ^ p_br :=
    mul_le_mul_of_nonneg_left hLg_pT_le hK_nn
  have hLsfInit_le' : (lsfInitSize (D.G 0) : ℝ) * (lg : ℝ) ^ 2 ≤ 1024 * (K * Lg ^ p_br) := by
    have := mul_le_mul_of_nonneg_left hLg4_le (show 0 ≤ 1024 * K by positivity)
    linarith
  have hBracket_le :
      (3 * ((D.G 0).m : ℝ) + 3 * ((activeSubgraph (D.G 0)).n : ℝ) + 2) +
        (lsfInitSize (D.G 0) : ℝ) * (lg : ℝ) ^ 2 +
        ((((Tb.runOrdAfterRestarts k M N D ord restarts τ).trees j).activeComps.sum
          fun C => ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum
            fun b => spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
              (normGraph ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).bun (C, b)).graph) : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).S_cur.batchEnc
          (stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).U_S : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, lsfBatchSize ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).cs
          (D.U (s + 1)) : ℕ) : ℝ) +
        2 * ((∑ s ∈ Finset.range τ,
          ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanBatchChargeWith spanConst (params M) E.L
                  ((((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).initBunG (C, b))
                  (((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j).dyn (C, b)).G
                  ((stepBundleTree sparsify ((Tb.runOrdAfterRestarts k M N D ord restarts s).trees j)
                    (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b))) : ℕ) : ℝ) +
        ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
          ((((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).cs.G.m + 1 +
            ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j).activeComps.sum fun C =>
              ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
                  (normGraph (restartBucketBundle ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j)
                    (ord r) C b).graph))) : ℕ) : ℝ) ≤
      (1 + Rc) * ((1044 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) * (K * Lg ^ p_br)) := by
    have hBase' := le_trans hBase_le (h1leR _ (by positivity))
    have hLsfI' := le_trans hLsfInit_le' (h1leR _ (by positivity))
    have hLazy' := le_trans hLazy_le (h1leR _ (by positivity))
    have hU' := le_trans hU_le (h1leR _ (by positivity))
    have hLSF' := le_trans hLSF_le (h1leR _ (by positivity))
    have hLift : (1 + Rc) * ((20 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) * (K * Lg ^ (P.p_T + 1))) ≤
        (1 + Rc) * ((20 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) * (K * Lg ^ p_br)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKLg_le (by positivity)) (by linarith)
    linarith
  have hmul_lg := mul_le_mul hlg_le hBracket_le (by positivity) (by positivity)
  have hmax1 : ((max 1 spanConst : ℕ) : ℝ) = c_sp := by
    rw [max_eq_right hConst]
  have hcoeff_fin : 16 * (1044 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) ≤ P'.c_T := by
    dsimp only [P', bundleCoreParamsMachWith, bundleCoreParams, p_max]
    rw [hmax1]
    have h7_nn : (0 : ℝ) ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := by positivity
    have hc_nn : (0 : ℝ) ≤ c_sp := by linarith
    have hprod_nn : 0 ≤ c_sp * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := mul_nonneg hc_nn h7_nn
    have hL : 16 * (1044 + c_sp * (151242 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 32)) =
        16704 + 2419872 * (c_sp * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) + 512 * c_sp := by ring
    have hR : c_sp * (65 * (37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n) + 18000) =
        2457650 * (c_sp * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) + 65 * (c_sp * E.c_n) + 18000 * c_sp := by ring
    have hcn : c_sp ≤ c_sp * E.c_n := le_mul_of_one_le_right hc_nn E.hc_n
    rw [hL, hR]
    linarith [hc_sp1, hprod_nn, hcn]
  have hpow_add : Lg ^ 2 * Lg ^ p_br = Lg ^ P'.p_T := by
    rw [← pow_add]
    congr 1
    dsimp only [P', P, p_br, bundleCoreParamsMachWith]
    omega
  have hfinal : 16 * Lg ^ 2 *
      ((1 + Rc) * ((1044 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) * (K * Lg ^ p_br))) ≤
      (1 + Rc) * (P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P'.γ_r M * Lg ^ P'.p_T) := by
    have hL : 16 * Lg ^ 2 *
        ((1 + Rc) * ((1044 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32)) * (K * Lg ^ p_br))) =
        (1 + Rc) * ((16 * (1044 + c_sp * (151242 * (7 : ℝ) ^ p_max + 32))) * (K * (Lg ^ 2 * Lg ^ p_br))) := by
      ring
    have hR : (1 + Rc) * (P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P'.γ_r M * Lg ^ P'.p_T) =
        (1 + Rc) * (P'.c_T * (K * Lg ^ P'.p_T)) := by
      dsimp only [K, P', bundleCoreParamsMachWith]; ring
    rw [hL, hpow_add, hR]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcoeff_fin (by positivity)) (by linarith)
  exact le_trans hDecompR (le_trans hmul_lg hfinal)

/-- **Machine cost of one branch** (specialization at `initLSFOnline oracle E.C_lsst`). -/
theorem bundleBranch_machCost_restart_le (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M))
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) (hj : j < k) :
    let Tm := sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    (((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℝ) ≤
      (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        (P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P'.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T) :=
  bundleBranchWith_machCost_restart_le E (initLSFOnline oracle E.C_lsst) sparsify params spanConst
    hConst k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
    hHyps.toWith hParams hV₀ j hj

end MinCostFlow.Chain

end
