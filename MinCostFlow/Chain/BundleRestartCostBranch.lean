module

public import MinCostFlow.Chain.BundleRestartCostEpoch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Total Cost of One Branch of `sparseCoreBundleRestartTool`

Proves `bundleBranch_cost_restart_le`: after step `τ` of a run with restarts on a nonempty initial
graph, branch `j`'s cumulative cost is at most
`(1 + R_j) * c_T * (M + 1) * (k + 1) * γ_r(M) * log^{p_T}(M + N + 2)`,
where `R_j = ∑_{r ≤ τ} (restarts r).count j` is the number of restarts of branch `j`, with no input
degree bound and no `hComp_bound` (paper Lemma 5.17, pages 23–24).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

/-- Cumulative cost bound for one branch `j < k` after step `τ` of a run of
`sparseCoreBundleRestartTool` with restarts, at `(M, N)` without any input degree bound or
`hComp_bound`. -/
theorem bundleBranch_cost_restart_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) (j : ℕ) (hj : j < k) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    (((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost : ℝ) ≤
      (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        (P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  intro T P
  have hk1 : 1 ≤ k := hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  have hne : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  set p_max := max E.p_s_hi E.p_t_hi with hp_max
  set logMN := Real.log ((M : ℝ) + (N : ℝ) + 2) with hlogMN
  set γ' := bundleRecBase E M * bundleCostMult E M with hγ'
  set T_b := ((M : ℝ) + 1) * γ' * logMN ^ (p_max + 1) with hT_b
  set Tk := ((M : ℝ) + 1) * ((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1) with hTk
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length with hq_τ
  set n_eff := min N (M + 1) with hn_eff
  set n_act := (activeSubgraph (D.G 0)).n with hn_act
  set st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
  obtain ⟨hbase, _, hfin, hTb_nn, hTk_nn, hγ'_nn, hlogMN_ge1⟩ :=
    bundleCost_env_baseline_parts_noComp E k M N n_act q_τ hN_pos
      (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
  have hG_eq : P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M * logMN ^ P.p_T = P.c_T * Tk := by
    simp only [hTk, hγ', P, bundleCoreParams, hp_max]; ring
  rw [hG_eq]
  have hG_fin : ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * Tk ≤
      P.c_T * Tk := by
    have h := hfin; rw [hG_eq] at h; exact h
  have hTk_eq : Tk = ((k : ℝ) + 1) * T_b := by simp only [hTk, hT_b]; ring
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hTb_le_Tk : T_b ≤ Tk := by rw [hTk_eq]; nlinarith
  have h7_ge1 : (1 : ℝ) ≤ (7 : ℝ) ^ p_max := one_le_pow₀ (by norm_num)
  have hcT_rest : (4 + 3 * (7 : ℝ) ^ p_max) + 12600 * (7 : ℝ) ^ p_max ≤ P.c_T := by
    simp only [P, bundleCoreParams, hp_max]
    linarith only [h7_ge1, E.hc_n]
  have hlog_nn : 0 ≤ logMN := by linarith
  have hdec := bundle_branch_cost_decomp lsfInit E.C_lsst E.L sparsify k M N D ord restarts hV₀ j τ
  dsimp only at hdec
  obtain ⟨hInit, hBun⟩ := bundleRestart_init_bun_le_active lsfInit E.C_lsst E.L E.hL (E.P_fn M)
    sparsify k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd hM hN hHyps.hSp
    j (hHyps.hInit j hj) (E.B_fn M) (hHyps.activeBuckets_card_le (N := N) hj)
  have hDU : ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) = (q_τ : ℝ) := by
    rw [Nat.cast_sum, bundle_sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ, hq_τ,
      Nat.cast_sum]
  have hUS_eq : ∀ s, (stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
      (D.U (s + 1)) (ord s) (ord (s + 1))).U_S =
      (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).2 j := fun s => by
    dsimp only [T]
    rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
      sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne s), hord_post s]
  have hUS_part := bundle_epoch_partition_sum_le restarts j τ
    (fun s => (((T.runOrdAfterUpdate k M N D ord restarts s).2 j).length : ℝ))
    (fun s => ((D.U s).length : ℝ)) 0
    (bundleRecoursePerQ E.L (E.P_fn M) M n_eff (E.B_fn M)) le_rfl
    (fun s₀ t hst htτ hs₀ hNoRest => by
      rw [zero_add]
      exact bundleEpoch_US_restart_le E lsfInit sparsify k M N τ D ord restarts
        hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest) τ le_rfl
  have hUS_sum : ∑ s ∈ Finset.range τ, ((stepBundleTree sparsify
      ((T.runOrdAfterRestarts k M N D ord restarts s).trees j) (D.U (s + 1))
      (ord s) (ord (s + 1))).U_S.length : ℝ) ≤
      bundleRecoursePerQ E.L (E.P_fn M) M n_eff (E.B_fn M) * (q_τ : ℝ) := by
    have h1 : ∑ s ∈ Finset.range τ, ((stepBundleTree sparsify
        ((T.runOrdAfterRestarts k M N D ord restarts s).trees j) (D.U (s + 1))
        (ord s) (ord (s + 1))).U_S.length : ℝ) =
        ∑ s ∈ Finset.Icc 1 τ, (((T.runOrdAfterUpdate k M N D ord restarts s).2 j).length : ℝ) := by
      rw [← bundle_sum_range_eq_sum_Icc_succ
        (fun s => (((T.runOrdAfterUpdate k M N D ord restarts s).2 j).length : ℝ))]
      exact Finset.sum_congr rfl fun s _ => by rw [hUS_eq s]
    rw [h1]
    have hq : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) = (q_τ : ℝ) := by
      rw [hq_τ, Nat.cast_sum]
    rw [hq, mul_zero, zero_add] at hUS_part
    exact hUS_part
  set dynF : ℕ → ℝ := fun s =>
    ((((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
        (D.U (s - 1 + 1)) (ord (s - 1)) (ord (s - 1 + 1))).state.activeComps.sum fun C =>
      (st₀.activeBuckets C).sum fun b =>
        ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts (s - 1)).trees j)
          (D.U (s - 1 + 1)) (ord (s - 1)) (ord (s - 1 + 1))).stepOut (C, b)).cost : ℕ) : ℝ)) with hdynF
  have hB_nn : 0 ≤ 25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1)) := by
    positivity
  have hA_nn : 0 ≤ 12600 * (7 : ℝ) ^ p_max * Tk := by positivity
  have hDyn_part := bundle_epoch_partition_sum_le restarts j τ dynF (fun s => ((D.U s).length : ℝ))
    (12600 * (7 : ℝ) ^ p_max * Tk)
    (25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1)))
    hA_nn
    (fun s₀ t hst htτ hs₀ hNoRest =>
      bundleEpoch_dyn_cost_restart_le_Tk E lsfInit sparsify k M N τ D ord restarts
        hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest) τ le_rfl
  have hDyn_eq : ∑ s ∈ Finset.range τ, (((stepBundleTree sparsify
      ((T.runOrdAfterRestarts k M N D ord restarts s).trees j) (D.U (s + 1))
      (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).stepOut (C, b)).cost : ℕ) : ℝ) =
      ∑ s ∈ Finset.Icc 1 τ, dynF s := by
    rw [← bundle_sum_range_eq_sum_Icc_succ dynF]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hdynF, Nat.add_sub_cancel]
  have hRest : ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
      singleBundleRestartCost E.L sparsify
        ((T.runOrdAfterUpdate k M N D ord restarts r).1.trees j) (ord r) : ℕ) : ℝ) ≤
      (∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        ((4 + 3 * (7 : ℝ) ^ p_max) * Tk) := by
    rw [Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hrc := singleBundleRestartCost_pre_le E lsfInit sparsify k M N τ D ord restarts
      hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps r j hj hr_le
    dsimp only at hrc
    have hrc_k : (singleBundleRestartCost E.L sparsify
        ((T.runOrdAfterUpdate k M N D ord restarts r).1.trees j) (ord r) : ℝ) ≤
        (4 + 3 * (7 : ℝ) ^ p_max) * Tk :=
      le_trans hrc.1 (mul_le_mul_of_nonneg_left hTb_le_Tk (by positivity))
    push_cast
    exact mul_le_mul_of_nonneg_left hrc_k (Nat.cast_nonneg _)
  have hCount : ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0) ≤
      ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun r _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => ((restarts r).count j : ℝ))
        (fun x hx => by simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega)
        (fun _ _ _ => Nat.cast_nonneg _))
    split_ifs with hmem
    · exact_mod_cast List.count_pos_iff.mpr hmem
    · exact Nat.cast_nonneg _
  have hq_m1 : (q_τ : ℝ) ≤ (M : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqτ_le_M
    linarith
  have hBq : 25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1)) * (q_τ : ℝ) ≤
      25200 * (7 : ℝ) ^ p_max * Tk := by
    have h1 := mul_le_mul_of_nonneg_left hq_m1 hB_nn
    have h2 : 25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1)) * ((M : ℝ) + 1) =
        25200 * (7 : ℝ) ^ p_max * Tk := by rw [hTk]; ring
    linarith
  have hq_eq : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) = (q_τ : ℝ) := by
    rw [hq_τ, Nat.cast_sum]
  rw [hq_eq] at hDyn_part
  set Rc := ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) with hRc
  set Nc := ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0)
  have hRc_nn : 0 ≤ Rc := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hNA := mul_le_mul_of_nonneg_right hCount hA_nn
  have hRest_tot : Rc * ((4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * Tk) ≤
      Rc * (P.c_T * Tk) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcT_rest hTk_nn) hRc_nn
  have hcoef_nn : 0 ≤ (7 + E.c_n) + 3 * (7 : ℝ) ^ p_max := by linarith only [h7_ge1, E.hc_n]
  have hbase_k : (M : ℝ) + (n_act : ℝ) + 1 +
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * bundleLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        bundleLambda (E.P_fn M) M) * (M : ℝ) +
      (q_τ : ℝ) + (E.B_fn M : ℝ) * (2 * bundleUCRatio n_eff * (q_τ : ℝ)) +
      bundleRecoursePerQ E.L (E.P_fn M) M n_eff (E.B_fn M) * (q_τ : ℝ) ≤
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * Tk :=
    le_trans hbase (mul_le_mul_of_nonneg_left hTb_le_Tk hcoef_nn)
  have hInit' : ((D.G 0).m : ℝ) + (n_act : ℝ) + 1 +
      (((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j τ).1.activeComps.sum
        st₀.lazyInitCost : ℕ) : ℝ) ≤
      (M : ℝ) + (n_act : ℝ) + 1 +
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * bundleLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        bundleLambda (E.P_fn M) M) * (M : ℝ) := hInit
  have hBun' : ∑ s ∈ Finset.range τ,
      ((((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
        (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b =>
            ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
              (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b)).length : ℕ) : ℝ)) ≤
      (E.B_fn M : ℝ) * (2 * bundleUCRatio n_eff * (q_τ : ℝ)) := hBun
  have hDyn_part' : ∑ s ∈ Finset.Icc 1 τ, dynF s ≤
      (1 + Nc) * (12600 * (7 : ℝ) ^ p_max * Tk) +
        25200 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * γ' * logMN ^ (p_max + 1)) * (q_τ : ℝ) :=
    hDyn_part
  have hcostR : (((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost : ℝ) =
      ((D.G 0).m : ℝ) + (n_act : ℝ) + 1 +
        (((bundleRunSeqWith lsfInit E.L sparsify k M N D ord j τ).1.activeComps.sum
          st₀.lazyInitCost : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) +
        (∑ s ∈ Finset.range τ,
          ((((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
              (st₀.activeBuckets C).sum fun b =>
                ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
                  (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b)).length : ℕ) : ℝ))) +
        ∑ s ∈ Finset.range τ, ((stepBundleTree sparsify
          ((T.runOrdAfterRestarts k M N D ord restarts s).trees j) (D.U (s + 1))
          (ord s) (ord (s + 1))).U_S.length : ℝ) +
        ∑ s ∈ Finset.range τ,
          ((((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps.sum fun C =>
              (st₀.activeBuckets C).sum fun b =>
                ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
                  (D.U (s + 1)) (ord s) (ord (s + 1))).stepOut (C, b)).cost : ℕ) : ℝ)) +
        ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
          singleBundleRestartCost E.L sparsify
            ((T.runOrdAfterUpdate k M N D ord restarts r).1.trees j) (ord r) : ℕ) : ℝ) := by
    rw [hdec]
    push_cast
    ring
  rw [hcostR, hDU, hDyn_eq]
  linarith only [hInit', hBun', hUS_sum, hDyn_part', hRest, hbase_k, hG_fin, hNA, hRest_tot, hBq]

end MinCostFlow.Chain

end
