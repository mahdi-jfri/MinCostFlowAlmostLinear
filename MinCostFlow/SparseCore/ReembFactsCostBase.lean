module

public import MinCostFlow.SparseCore.Program.AssemblyInputRun
public import MinCostFlow.Chain.BundleRestartMachCost

import MinCostFlow.Chain.BundleRestartDyn
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cost comparison helpers for reached states of the sparse core (`ReembFactsCostBase`)

Provides the per-component and per-epoch lemmas used by `ReembFactsCost.lean` to prove
`tr.cost ≤ tr.machCost`:
* `dynSpanner_init_cost_le_spanInitBound`: clauses 1 and 2 of `DynSpanner.theorem_8_2` bound the
  model initialization cost of a bucket spanner by `spanInitBound`.
* `bundleWith_branch_machCost_eq`: exact decomposition of `((post_m t).trees j).machCost`.
* `inactive_step_U_B_nil`: an inactive component produces an empty bundle batch (`[]`), so its
  spanner update cost and charge both vanish.
* `epoch_dyn_cost_le_charge` and `run_dyn_cost_le_charge`: the last clause of
  `DynSpanner.theorem_8_2` bounds the cumulative dynamic-spanner update cost over every epoch
  and hence over every prefix `[0, t)` by the sum of `spanBatchChargeWith`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.LSF
open MinCostFlow.SparseCore.Program

/-! ## 1. Initialization cost against `spanInitBound` -/

/-- By clauses 1 and 2 of `DynSpanner.theorem_8_2`, the model initialization cost of a dynamic
spanner on a valid graph `Hb` with `Hb.m ≤ M` is at most `spanInitBound P_b L splitB Hb`. -/
theorem dynSpanner_init_cost_le_spanInitBound
    {L M splitB : ℕ} {P_b : SparsifyParams}
    {sp : MGraph → MGraph → Embedding → SparsifyOut}
    {Hb : MGraph} (hV : Hb.IsValid) (hL : 1 ≤ L) (hm : Hb.m ≤ M)
    (hSp : SparsifySpec M P_b sp) :
    (DynSpanner.init Hb L (phaseBase (Hb.n + splitB) L) sp).cost ≤
      spanInitBound P_b L splitB Hb := by
  have h82 := DynSpanner.theorem_8_2 (Us := []) (splitBound := splitB) hV hL hm hSp trivial
    (by simp) (by simp [batchSplitCount])
  have hHm : ((DynSpanner.init Hb L (phaseBase (Hb.n + splitB) L) sp).state.H.m : ℝ) ≤
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s := h82.1
  have hCost : ((DynSpanner.init Hb L (phaseBase (Hb.n + splitB) L) sp).cost : ℝ) ≤
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t +
        (Hb.n : ℝ) + (Hb.m : ℝ) +
        ((DynSpanner.init Hb L (phaseBase (Hb.n + splitB) L) sp).state.H.m : ℝ) +
        (Hb.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1 := h82.2.1
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph Hb).n, Nat.cast_nonneg (α := ℝ) Hb.m])]
  have hlog2 : (1 : ℝ) ≤ 1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((Hb.n + splitB : ℕ) : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) (Hb.n + splitB)])]
  have hpow : (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t ≤
      (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1 :=
    pow_le_pow_right₀ hlog1 (le_max_left P_b.p_t 1)
  have hKt_nn : 0 ≤ P_b.K_t := P_b.hK_t
  have hγ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hterm1 :
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t ≤
      P_b.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have htermL : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  unfold spanInitBound
  exact Nat.cast_le.mp (le_trans (by linarith) (Nat.le_ceil _))

/-! ## 2. Exact machine-cost decomposition of one branch -/

/-- Exact decomposition of `machCost` of branch `j` after stage `t` of
`sparseCoreBundleRestartToolMachWith`, expressed in terms of the non-machine run. -/
theorem bundleWith_branch_machCost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let post_m := fun t => Tm.runOrdAfterRestarts k M N D ord restarts t
    let pre_b := fun t => (Tb.runOrdAfterUpdate k M N D ord restarts t).1
    let post_b := fun t => Tb.runOrdAfterRestarts k M N D ord restarts t
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let infoB := fun s =>
      stepBundleTree sparsify ((post_b s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    ∀ t, ((post_m t).trees j).machCost = bundleLogFactor M N * (
      (3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2) +
      lsfInitSize (D.G 0) * bundleLogFactor M N ^ 2 +
      ((post_b t).trees j).activeComps.sum (fun C => (st₀.activeBuckets C).sum fun b =>
        spanConst * spanInitBound (params M) L (bundleSplitBudget k M)
          (normGraph (st₀.bun (C, b)).graph)) +
      (∑ s ∈ Finset.range t, (D.U (s + 1)).length) +
      (∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          (((post_b s).trees j).dyn (C, b)).G.batchEnc ((infoB s).U_B (C, b)))) +
      (∑ s ∈ Finset.range t, ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S) +
      (∑ s ∈ Finset.range t, lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1))) +
      (∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L
            ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b)))) +
      ∑ r ∈ Finset.range (t + 1), (restarts r).count j *
        (((pre_b r).trees j).cs.G.m + 1 +
          ((pre_b r).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            spanConst * spanInitBound (params M) L (bundleSplitBudget k M)
              (normGraph (restartBucketBundle ((pre_b r).trees j) (ord r) C b).graph))) := by
  classical
  intro Tm Tb post_m pre_b post_b st₀ infoB
  set lg := bundleLogFactor M N
  set splitB := bundleSplitBudget k M
  let pre_m := fun t => (Tm.runOrdAfterUpdate k M N D ord restarts t).1
  let lazyFn : Finset ℕ → ℕ := fun C => (st₀.activeBuckets C).sum fun b =>
    spanConst * spanInitBound (params M) L splitB (normGraph (st₀.bun (C, b)).graph)
  have hNM := fun s => sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D ord restarts s
  have hPar := runOrdAfterRestartsMachWith_params lsfInit C_lsst L sparsify params spanConst
    k M N D ord restarts
  have hne_pre_b : ∀ s, (pre_b s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).1.trans
      (decide_eq_true hV₀)
  have hne_post_b : ∀ s, (post_b s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hne_pre_m : ∀ s, (pre_m s).isNonempty = true := fun s => (hNM s).1.isNonempty.trans (hne_pre_b s)
  have hne_post_m : ∀ s, (post_m s).isNonempty = true := fun s => (hNM s).2.2.isNonempty.trans (hne_post_b s)
  have hord_pre_b : ∀ s, (pre_b s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).1
  have hord_post_b : ∀ s, (post_b s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  have hord_pre_m : ∀ s, (pre_m s).ord = ord s := fun s => (hNM s).1.ord.trans (hord_pre_b s)
  have hord_post_m : ∀ s, (post_m s).ord = ord s := fun s => (hNM s).2.2.ord.trans (hord_post_b s)
  have hAB_pre : ∀ s, ((pre_b s).trees j).activeBuckets = st₀.activeBuckets := fun s => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j s).1
    have hinv : ∀ n, (bundleRunSeqWith lsfInit L sparsify k M N D ord j n).1.activeBuckets =
        st₀.activeBuckets := fun n => by
      induction n with
      | zero => rfl
      | succ m ih => exact ih
    exact hbp.activeBuckets.trans (hinv s)
  have hAB_post : ∀ s, ((post_b s).trees j).activeBuckets = st₀.activeBuckets := fun s =>
    ((foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b s) (restarts s)).2.2.2.2.1 j).activeBuckets.trans
      (hAB_pre s)
  have hSB_pre : ∀ s, ((pre_b s).trees j).splitBound = splitB := fun s => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j s).1
    have hinv : ∀ n, (bundleRunSeqWith lsfInit L sparsify k M N D ord j n).1.splitBound = splitB :=
      fun n => by induction n with | zero => rfl | succ m ih => exact ih
    exact hbp.splitBound.trans (hinv s)
  have hSB_post : ∀ s, ((post_b s).trees j).splitBound = splitB := fun s =>
    ((foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b s) (restarts s)).2.2.2.2.1 j).splitBound.trans
      (hSB_pre s)
  have hRest_inner : ∀ r,
      singleBundleRestartMachCost L sparsify ((pre_m r).trees j) (ord r) =
        (((pre_b r).trees j).cs.G.m + 1 +
          ((pre_b r).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            spanConst * spanInitBound (params M) L splitB
              (normGraph (restartBucketBundle ((pre_b r).trees j) (ord r) C b).graph)) * lg := by
    intro r
    rw [singleBundleRestartMachCost_eq_inner]
    have hp := (hPar r j).1
    rw [hp.1, hp.2.1]
    have hin := singleBundleRestartMachInner_of_nonMachEq sparsify ((hNM r).1.trees j)
      hp.2.2.1 hp.2.2.2.1 (hSB_pre r) (ord r)
    rw [hin, hAB_pre r]
  have hpostM : ∀ s, ((post_m s).trees j).machCost = ((pre_m s).trees j).machCost +
      (restarts s).count j * singleBundleRestartMachCost L sparsify ((pre_m s).trees j) (ord s) := by
    intro s
    have h := foldl_bundleRestartWith_machCost lsfInit C_lsst L sparsify (restarts s) (pre_m s)
      (hne_pre_m s) j
    rw [hord_pre_m s] at h
    exact h
  have hact_post : ∀ s, ((post_b s).trees j).activeComps = ((pre_b s).trees j).activeComps := fun s =>
    ((foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b s) (restarts s)).2.2.2.2.1 j).activeComps
  intro t
  induction t with
  | zero =>
    rw [hpostM 0, hRest_inner 0, Finset.sum_range_zero, Finset.sum_range_one]
    have hpre0 : (pre_m 0).trees j =
        initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0) (ord 0) j := rfl
    have hact0 : ((post_b 0).trees j).activeComps = st₀.activeComps := hact_post 0
    have hpre0_cost : ((pre_m 0).trees j).machCost =
        (3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2 +
          lsfInitSize (D.G 0) * lg ^ 2 + st₀.activeComps.sum lazyFn) * lg := by
      rw [hpre0, initBundleTreeWithParams_machCost]; rfl
    rw [hpre0_cost, hact0]
    ring
  | succ s ih =>
    set infoM := stepBundleTree sparsify ((post_m s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    have hpre_m_eq : (pre_m (s + 1)).trees j = infoM.state := by
      dsimp only [pre_m, Tm]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ]
      change ((updateBundleCore sparsify (post_m s) (D.U (s + 1)) (ord (s + 1))).1.trees j) = _
      rw [updateBundleCore_of_nonempty (hne_post_m s), hord_post_m s]
    have hpre_b_eq : (pre_b (s + 1)).trees j = (infoB s).state := by
      dsimp only [pre_b, Tb]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
        sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne_post_b s), hord_post_b s]
    have hStepNM := BundleNonMachEq.step sparsify ((hNM s).2.2.trees j) (D.U (s + 1)) (ord s)
      (ord (s + 1))
    have hstepM : infoM.state.machCost = ((post_m s).trees j).machCost +
        ((D.U (s + 1)).length +
          ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            (((post_b s).trees j).dyn (C, b)).G.batchEnc ((infoB s).U_B (C, b))) +
          ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S +
          ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            spanBatchChargeWith spanConst (params M) L
              ((((post_b s).trees j).initBunG (C, b)).n + splitB)
              (((post_b s).trees j).initBunG (C, b))
              (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) +
          lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1)) +
          (infoB s).newlyActive.sum lazyFn) * lg := by
      have h0 := stepBundleTree_machCost sparsify ((post_m s).trees j) (D.U (s + 1)) (ord s)
        (ord (s + 1))
      dsimp only at h0
      have hp := (hPar s j).2
      have hnm := (hNM s).2.2.trees j
      rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, hnm.activeBuckets, hAB_post s,
        hnm.dyn, hnm.S_cur, hnm.cs, hnm.initBunG, hnm.splitBound, hSB_post s,
        hStepNM.1.activeComps, hStepNM.2.1, hStepNM.2.2.1, hStepNM.2.2.2.2] at h0
      exact h0
    have hact_union : ((post_b (s + 1)).trees j).activeComps.sum lazyFn =
        ((post_b s).trees j).activeComps.sum lazyFn + (infoB s).newlyActive.sum lazyFn := by
      rw [hact_post (s + 1), hpre_b_eq]
      change (((post_b s).trees j).activeComps ∪
        (touchedCompsBatch ((post_b s).trees j).cs (D.U (s + 1)) \
          ((post_b s).trees j).activeComps)).sum lazyFn = _
      exact Finset.sum_union Finset.disjoint_sdiff
    dsimp only [lazyFn] at hstepM hact_union
    rw [hpostM (s + 1), hRest_inner (s + 1), hpre_m_eq, hstepM,
      Finset.sum_range_succ (n := s + 1),
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s),
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s),
      Finset.sum_range_succ (n := s), hact_union, ih]
    ring

/-! ## 3. Inactive components produce empty bucket batches -/

private lemma inactive_step_U_B_nil
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {s : ℕ} (hs : s < τ) {C : Finset ℕ} (hC : C ∈ components (D.G 0)) (b : ℤ)
    (hna : C ∉ (stepBundleTree sparsify
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
        k M N D ord restarts s |>.trees j)
      (D.U (s + 1)) (ord s) (ord (s + 1))).state.activeComps) :
    (stepBundleTree sparsify
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
        k M N D ord restarts s |>.trees j)
      (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b) = [] := by
  classical
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  set post := (Tb.runOrdAfterRestarts k M N D ord restarts s).trees j
  set pre := (Tb.runOrdAfterUpdate k M N D ord restarts s).1.trees j
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit s (Nat.le_of_lt hs)
  have hbf : BundleBaseFieldsEq post pre :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (Tb.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j
  have hI : CompLSFInv C_lsst (D.ℓ 0) post.cs := hbf.cs.symm ▸ hBun.2.2.2.2.2.2.2.1
  have hG : post.cs.G = D.G s := hbf.cs ▸ hBun.2.2.2.2.2.2.2.2.1
  have hG₀_eq : post.cs.G₀ = D.G 0 := by rw [hbf.cs, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hk_eq : post.k = k := hbf.k.trans hBun.1
  have hDt := hD (s + 1) (Nat.succ_pos s) hs
  simp only [Nat.add_sub_cancel] at hDt
  have hBV : post.cs.G.BatchIsValid (D.U (s + 1)) := hG.symm ▸ hDt.1
  obtain ⟨ρ, σ, hρ, hσ, hrot⟩ := orderedUpTo_rot_step hOrd hs hG
  have hB : BundleCompReady post.cs C (post.bun (C, b)) k (ord s) :=
    ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1
  have hnt : C ∉ touchedCompsBatch post.cs (D.U (s + 1)) := by
    intro ht
    apply hna
    by_cases ha : C ∈ post.activeComps
    · exact Finset.mem_union_left _ ha
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ht, ha⟩)
  have hst := bundleCompStep_stage hI hBV hρ hσ hrot (hG₀_eq.symm ▸ hC) hB
  change (bundleCompStep post.cs (post.bun (C, b)) post.k (ord s) (ord (s + 1)) (D.U (s + 1))).1 = []
  rw [hk_eq, hst.2.2.2.2.2.2.2.2 hnt]

/-! ## 4. Per-epoch and full-run dynamic spanner update cost against `spanBatchChargeWith` -/

private lemma epoch_dyn_cost_le_charge
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (P_b : SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t' j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (hst : s₀ ≤ t') (htτ : t' ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t' → j ∉ restarts r)
    {C : Finset ℕ} (hC : C ∈ components (D.G 0)) (b : ℤ) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let post_b := fun s => Tb.runOrdAfterRestarts k M N D ord restarts s
    let infoB := fun s =>
      stepBundleTree sparsify ((post_b s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    ∑ r ∈ Finset.range (t' - s₀), ((infoB (s₀ + r)).stepOut (C, b)).cost ≤
      ∑ r ∈ Finset.range (t' - s₀),
        spanBatchChargeWith spanConst P_b L
          ((((post_b (s₀ + r)).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
          (((post_b (s₀ + r)).trees j).initBunG (C, b))
          (((post_b (s₀ + r)).trees j).dyn (C, b)).G ((infoB (s₀ + r)).U_B (C, b)) := by
  classical
  intro Tb post_b infoB
  set splitB := bundleSplitBudget k M
  set ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t' j
  set Hb := ((ep 0).bun (C, b)).graph
  set G_init := normGraph Hb
  set Us_ep : List (List Update) := (List.range (t' - s₀)).map fun r =>
    (stepBundleTree sparsify (ep r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t' j hInit hst htτ hs₀ hNoRest C hC b
  have hSplit : batchSplitCount Us_ep.flatten ≤ splitB :=
    epochBundleSeq_batchSplitCount_le_splitB lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh
      s₀ t' j hInit hst htτ hs₀ hNoRest hC b
  have hInitG := epochBundleSeq_initBunG_eq lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd s₀ t' j hInit hst htτ hs₀ hNoRest
  have hEp_lt := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t' j hst).1
  have hG_val : G_init.IsValid := normGraph_isValid hDyn.1
  have hG_m : G_init.m ≤ M := le_trans hDyn.2.1 hM
  have hBV_norm : G_init.BatchIsValid Us_ep.flatten :=
    batchIsValid_of_graphEq (graphEq_symm (normGraph_graphEq Hb)) hDyn.2.2.2.2.2.1
  have hds_norm : ∀ u ∈ Us_ep.flatten, isDelOrSplit u := hDyn.2.2.2.2.2.2.1
  have h82 := DynSpanner.theorem_8_2 (L := L) (mMax := M) (splitBound := splitB) (P := P_b)
    (sparsify := sparsify M) (Us := Us_ep) hG_val hL hG_m hSp hBV_norm hds_norm hSplit
  have hlen : Us_ep.length = t' - s₀ := by simp [Us_ep]
  have h82_cost := (h82.2.2.2.2 (t' - s₀) hlen.ge).2.2.2
  have hLhs : ((∑ r ∈ Finset.range (t' - s₀), ((infoB (s₀ + r)).stepOut (C, b)).cost : ℕ) : ℝ) =
      ∑ r ∈ Finset.range (t' - s₀),
        ((DynSpanner.runBatchStepOut (L := L) G_init (phaseBase (G_init.n + splitB) L)
          (sparsify M) Us_ep r).cost : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_lt : r < t' - s₀ := Finset.mem_range.mp hr
    have hstep_eq : (infoB (s₀ + r)).stepOut (C, b) =
        DynSpanner.runBatchStepOut (L := L) G_init (phaseBase (G_init.n + splitB) L)
          (sparsify M) Us_ep r := by
      have h1 := (hDyn.2.2.2.2.2.2.2.2.2.2 r hr_lt).1
      have hep_r : ep r = (post_b (s₀ + r)).trees j := hEp_lt r hr_lt
      dsimp only [infoB]
      rw [← hep_r]
      exact h1
    rw [hstep_eq]
  have hRhs_le :
      spanBatchRate P_b L (G_init.n + splitB) G_init *
        (∑ r ∈ Finset.range (t' - s₀), match Us_ep[r]? with
          | some U => ((DynSpanner.runBatchState (L := L) G_init
              (phaseBase (G_init.n + splitB) L) (sparsify M) Us_ep r).G.batchEnc U : ℝ)
          | none => 0) ≤
      ((∑ r ∈ Finset.range (t' - s₀),
        spanBatchChargeWith spanConst P_b L
          ((((post_b (s₀ + r)).trees j).initBunG (C, b)).n + splitB)
          (((post_b (s₀ + r)).trees j).initBunG (C, b))
          (((post_b (s₀ + r)).trees j).dyn (C, b)).G ((infoB (s₀ + r)).U_B (C, b)) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_le_sum fun r hr => ?_
    have hr_lt : r < t' - s₀ := Finset.mem_range.mp hr
    have hep_r : ep r = (post_b (s₀ + r)).trees j := hEp_lt r hr_lt
    have hUs_r : Us_ep[r]? = some ((infoB (s₀ + r)).U_B (C, b)) := by
      simp [Us_ep, hr_lt, infoB, hep_r]
    have hdyn_r : DynSpanner.runBatchState (L := L) G_init (phaseBase (G_init.n + splitB) L)
        (sparsify M) Us_ep r = ((post_b (s₀ + r)).trees j).dyn (C, b) := by
      have h1 := (hDyn.2.2.2.2.2.2.2.2.2.1 r hr_lt.le).1
      rw [← hep_r]
      exact h1.symm
    have hig_r : ((post_b (s₀ + r)).trees j).initBunG (C, b) = G_init := by
      rw [← hep_r]; exact hInitG r hr_lt.le C hC b
    rw [hUs_r, hdyn_r, hig_r]
    dsimp only [spanBatchChargeWith]
    have hc1 : (1 : ℝ) ≤ (spanConst : ℝ) := by exact_mod_cast hConst
    have hrate_nn : 0 ≤ spanBatchRate P_b L (G_init.n + splitB) G_init :=
      spanBatchRate_nonneg P_b L (G_init.n + splitB) G_init
    have hmul : spanBatchRate P_b L (G_init.n + splitB) G_init *
          ((((post_b (s₀ + r)).trees j).dyn (C, b)).G.batchEnc ((infoB (s₀ + r)).U_B (C, b)) : ℝ) ≤
        (spanConst : ℝ) * spanBatchRate P_b L (G_init.n + splitB) G_init *
          ((((post_b (s₀ + r)).trees j).dyn (C, b)).G.batchEnc ((infoB (s₀ + r)).U_B (C, b)) : ℝ) := by
      have h1 : spanBatchRate P_b L (G_init.n + splitB) G_init ≤
          (spanConst : ℝ) * spanBatchRate P_b L (G_init.n + splitB) G_init :=
        le_mul_of_one_le_left hrate_nn hc1
      exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
    exact le_trans hmul (Nat.le_ceil _)
  exact Nat.cast_le.mp (le_trans (le_of_eq hLhs) (le_trans h82_cost hRhs_le))

/-- Over every prefix `[0, t)` of a valid run with arbitrary restarts, the total dynamic-spanner
update cost across all active components and buckets is at most the sum of `spanBatchChargeWith`. -/
theorem run_dyn_cost_le_charge
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (P_b : SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let post_b := fun s => Tb.runOrdAfterRestarts k M N D ord restarts s
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let infoB := fun s =>
      stepBundleTree sparsify ((post_b s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    ∀ t ≤ τ,
      ∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost) ≤
      ∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst P_b L
            ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) := by
  classical
  intro Tb post_b st₀ infoB
  have hcomp_step : ∀ s < τ,
      ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost) =
      ((components (D.G 0)).sum fun C =>
        (st₀.activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost) ∧
      ((infoB s).state.activeComps.sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst P_b L
            ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) =
      ((components (D.G 0)).sum fun C =>
        (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst P_b L
            ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) := by
    intro s hs
    have hne_post : (post_b s).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
        (decide_eq_true hV₀)
    have hord_post : (post_b s).ord = ord s :=
      ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
    have hpre_eq : (Tb.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j = (infoB s).state := by
      dsimp only [Tb, infoB, post_b]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
        sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_post, hord_post]
    have hact_sub : (infoB s).state.activeComps ⊆ components (D.G 0) := by
      rw [← hpre_eq]
      exact (runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
        k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit (s + 1) hs).2.2.2.2.2.2.2.2.2.1.2
    constructor
    · refine Finset.sum_subset hact_sub fun C hC hna => ?_
      refine Finset.sum_eq_zero fun b _ => ?_
      have hnil := inactive_step_U_B_nil lsfInit C_lsst L sparsify k M N τ hk D ord restarts
        hG₀ hV₀ hℓ₀ hD hOrd j hInit hs hC b hna
      change (DynSpanner.update (((post_b s).trees j).dyn (C, b)) ((infoB s).U_B (C, b))
        (sparsify ((post_b s).trees j).m₀)).cost = 0
      rw [hnil]
      rfl
    · refine Finset.sum_subset hact_sub fun C hC hna => ?_
      refine Finset.sum_eq_zero fun b _ => ?_
      have hnil := inactive_step_U_B_nil lsfInit C_lsst L sparsify k M N τ hk D ord restarts
        hG₀ hV₀ hℓ₀ hD hOrd j hInit hs hC b hna
      rw [hnil, spanBatchChargeWith_nil]
  let f : ℕ → ℕ := fun s => (components (D.G 0)).sum fun C =>
    (st₀.activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost
  let g : ℕ → ℕ := fun s => (components (D.G 0)).sum fun C =>
    (st₀.activeBuckets C).sum fun b =>
      spanBatchChargeWith spanConst P_b L
        ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
        (((post_b s).trees j).initBunG (C, b))
        (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))
  have hfg : ∀ t ≤ τ, ∑ s ∈ Finset.range t, f s ≤ ∑ s ∈ Finset.range t, g s := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · simp
      · set s₀ := bundleLastRestart restarts j (t - 1)
        obtain ⟨hs₀_le, hs₀_cases, hs₀_none⟩ := bundleLastRestart_spec restarts j (t - 1)
        have hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 =>
          hs₀_none r h1 (by omega)
        have hsplit : ∀ h : ℕ → ℕ, ∑ s ∈ Finset.range t, h s =
            ∑ s ∈ Finset.range s₀, h s + ∑ r ∈ Finset.range (t - s₀), h (s₀ + r) := fun h => by
          have ht_eq : s₀ + (t - s₀) = t := by omega
          conv_lhs => rw [← ht_eq, Finset.sum_range_add]
        rw [hsplit f, hsplit g]
        have hIH : ∑ s ∈ Finset.range s₀, f s ≤ ∑ s ∈ Finset.range s₀, g s :=
          ih s₀ (by omega) (by omega)
        have hEp : ∑ r ∈ Finset.range (t - s₀), f (s₀ + r) ≤
            ∑ r ∈ Finset.range (t - s₀), g (s₀ + r) := by
          dsimp only [f, g]
          rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (t - s₀))]
          refine Finset.sum_le_sum fun C hC => ?_
          rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (t - s₀))]
          refine Finset.sum_le_sum fun b _ => ?_
          exact epoch_dyn_cost_le_charge lsfInit C_lsst L hL sparsify P_b spanConst hConst
            k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh
            s₀ t j hInit (by omega) ht hs₀_cases hNoRest hC b
        exact Nat.add_le_add hIH hEp
  intro t ht
  have h1 : (∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
      (st₀.activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost)) =
      ∑ s ∈ Finset.range t, f s :=
    Finset.sum_congr rfl fun s hs => (hcomp_step s (lt_of_lt_of_le (Finset.mem_range.mp hs) ht)).1
  have h2 : (∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
      (st₀.activeBuckets C).sum fun b =>
        spanBatchChargeWith spanConst P_b L
          ((((post_b s).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
          (((post_b s).trees j).initBunG (C, b))
          (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b)))) =
      ∑ s ∈ Finset.range t, g s :=
    Finset.sum_congr rfl fun s hs => (hcomp_step s (lt_of_lt_of_le (Finset.mem_range.mp hs) ht)).2
  rw [h1, h2]
  exact hfg t ht

end MinCostFlow.SparseCore
