module

public import MinCostFlow.Chain.BundleRestartMach
public import MinCostFlow.Chain.BundleRestartCostTotal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Machine-cost decomposition of one branch

The machine cost `machCost` of a branch charges every step and every restart the log factor
`lg = bundleLogFactor M N`, and charges:
* initial setup `3 m + 3 |V_act| + 2 + lsfInitSize G₀ · lg²`,
* lazy spanner initializations `spanConst · spanInitBound` for each newly active component,
* input updates, bundle and output batch encodings, LSF batches, and dynamic-spanner update charges
  `spanBatchChargeWith spanConst (params M) L`,
* restarts `m_cur + 1 + ∑ spanConst · spanInitBound`.

This file proves:
* `bundleWith_branch_machCost_le`: bounds `((post_m t).trees j).machCost` of
  `sparseCoreBundleRestartToolMachWith` directly in terms of the non-machine run of
  `sparseCoreBundleRestartToolWith` (using `BundleNonMachEq` and `batchEnc_le_spanBatchChargeWith`
  to absorb bundle encodings into `2 * ∑ spanBatchChargeWith`);
* `epochBundleSeq_initBunG_eq`: along any non-restarted epoch `[s₀, t]`, `initBunG (C, b)` stays
  equal to `normGraph ((ep 0).bun (C, b)).graph` for every component `C` and bucket `b`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

/-! ## Inner factor of `singleBundleRestartMachCost` -/

/-- The inner (pre-log-factor) term of `singleBundleRestartMachCost`. -/
noncomputable def singleBundleRestartMachInner (L : ℕ)
    (_sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) : ℕ :=
  tr.cs.G.m + 1 +
    tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      let Hb := normGraph (restartBucketBundle tr ord C b).graph
      tr.spanConst * spanInitBound tr.spanParams L tr.splitBound Hb

lemma singleBundleRestartMachCost_eq_inner (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    singleBundleRestartMachCost L sparsify tr ord =
      singleBundleRestartMachInner L sparsify tr ord * bundleLogFactor tr.m₀ tr.n₀ := rfl

lemma singleBundleRestartMachInner_of_nonMachEq {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {a b : BundleTreeState L} {P_sp : SparsifyParams} {c_sp sb : ℕ} (h : BundleNonMachEq a b)
    (hP : a.spanParams = P_sp) (hc : a.spanConst = c_sp) (hsb : b.splitBound = sb)
    (ord : ℕ → List End) :
    singleBundleRestartMachInner L sparsify a ord =
      b.cs.G.m + 1 +
        b.activeComps.sum fun C => (b.activeBuckets C).sum fun bk =>
          c_sp * spanInitBound P_sp L sb (normGraph (restartBucketBundle b ord C bk).graph) := by
  classical
  unfold singleBundleRestartMachInner
  rw [h.cs, h.activeComps, h.activeBuckets, hP, hc, h.splitBound, hsb]
  congr 1
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun bk _ => ?_
  have hrb : restartBucketBundle a ord C bk = restartBucketBundle b ord C bk := by
    unfold restartBucketBundle; rw [h.cs, h.bun, h.k]
  rw [hrb]

/-! ## Direct machine-cost upper bound for one branch -/

/-- Direct decomposition / upper bound for the machine cost of branch `j` after stage `t` of
`sparseCoreBundleRestartToolMachWith`, expressed in terms of the non-machine run of
`sparseCoreBundleRestartToolWith`. -/
lemma bundleWith_branch_machCost_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
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
    ∀ t, ((post_m t).trees j).machCost ≤ bundleLogFactor M N * (
      (3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2) +
      lsfInitSize (D.G 0) * bundleLogFactor M N ^ 2 +
      ((post_b t).trees j).activeComps.sum (fun C => (st₀.activeBuckets C).sum fun b =>
        spanConst * spanInitBound (params M) L (bundleSplitBudget k M)
          (normGraph (st₀.bun (C, b)).graph)) +
      (∑ s ∈ Finset.range t, (D.U (s + 1)).length) +
      (∑ s ∈ Finset.range t, ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S) +
      (∑ s ∈ Finset.range t, lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1))) +
      2 * (∑ s ∈ Finset.range t, ((infoB s).state.activeComps.sum fun C =>
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
  have hAB_post : ∀ s, ((post_b s).trees j).activeBuckets = st₀.activeBuckets := fun s => by
    have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b s) (restarts s)).2.2.2.2.1 j
    exact hbf.activeBuckets.trans (hAB_pre s)
  have hSB_pre : ∀ s, ((pre_b s).trees j).splitBound = splitB := fun s => by
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j s).1
    have hinv : ∀ n, (bundleRunSeqWith lsfInit L sparsify k M N D ord j n).1.splitBound = splitB :=
      fun n => by induction n with | zero => rfl | succ m ih => exact ih
    exact hbp.splitBound.trans (hinv s)
  have hSB_post : ∀ s, ((post_b s).trees j).splitBound = splitB := fun s => by
    have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b s) (restarts s)).2.2.2.2.1 j
    exact hbf.splitBound.trans (hSB_pre s)
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
    exact le_of_eq (by ring)
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
    have hbe_le : ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          (((post_b s).trees j).dyn (C, b)).G.batchEnc ((infoB s).U_B (C, b))) ≤
        ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L
            ((((post_b s).trees j).initBunG (C, b)).n + splitB)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) :=
      Finset.sum_le_sum fun C _ => Finset.sum_le_sum fun b _ =>
        batchEnc_le_spanBatchChargeWith hConst (params M) hL _ _ _ _
    have hact_union : ((post_b (s + 1)).trees j).activeComps.sum lazyFn =
        ((post_b s).trees j).activeComps.sum lazyFn + (infoB s).newlyActive.sum lazyFn := by
      rw [hact_post (s + 1), hpre_b_eq]
      change (((post_b s).trees j).activeComps ∪
        (touchedCompsBatch ((post_b s).trees j).cs (D.U (s + 1)) \
          ((post_b s).trees j).activeComps)).sum lazyFn = _
      exact Finset.sum_union Finset.disjoint_sdiff
    rw [hpostM (s + 1), hRest_inner (s + 1), hpre_m_eq, hstepM,
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s),
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s),
      Finset.sum_range_succ (n := s + 1), hact_union]
    have hmul := Nat.mul_le_mul_left lg (show
      (D.U (s + 1)).length +
        ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          (((post_b s).trees j).dyn (C, b)).G.batchEnc ((infoB s).U_B (C, b))) +
        ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S +
        ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L
            ((((post_b s).trees j).initBunG (C, b)).n + splitB)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) +
        lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1)) +
        (infoB s).newlyActive.sum lazyFn ≤
      (D.U (s + 1)).length +
        ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S +
        lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1)) +
        2 * ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          spanBatchChargeWith spanConst (params M) L
            ((((post_b s).trees j).initBunG (C, b)).n + splitB)
            (((post_b s).trees j).initBunG (C, b))
            (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) +
        (infoB s).newlyActive.sum lazyFn by omega)
    have hstep_le := Nat.add_le_add_right (Nat.add_le_add ih hmul)
      (lg * ((restarts (s + 1)).count j *
        (((pre_b (s + 1)).trees j).cs.G.m + 1 +
          ((pre_b (s + 1)).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            spanConst * spanInitBound (params M) L splitB
              (normGraph (restartBucketBundle ((pre_b (s + 1)).trees j) (ord (s + 1)) C b).graph))))
    have hLhs :
        ((post_m s).trees j).machCost +
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
            (infoB s).newlyActive.sum lazyFn) * lg +
          (restarts (s + 1)).count j *
            ((((pre_b (s + 1)).trees j).cs.G.m + 1 +
              ((pre_b (s + 1)).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) L splitB
                  (normGraph (restartBucketBundle ((pre_b (s + 1)).trees j) (ord (s + 1)) C b).graph)) *
              lg) =
        ((post_m s).trees j).machCost +
          lg * ((D.U (s + 1)).length +
            ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
              (((post_b s).trees j).dyn (C, b)).G.batchEnc ((infoB s).U_B (C, b))) +
            ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S +
            ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) L
                ((((post_b s).trees j).initBunG (C, b)).n + splitB)
                (((post_b s).trees j).initBunG (C, b))
                (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) +
            lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1)) +
            (infoB s).newlyActive.sum lazyFn) +
          lg * ((restarts (s + 1)).count j *
            (((pre_b (s + 1)).trees j).cs.G.m + 1 +
              ((pre_b (s + 1)).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) L splitB
                  (normGraph (restartBucketBundle ((pre_b (s + 1)).trees j) (ord (s + 1)) C b).graph))) := by
      ring
    have hRhs :
        lg * ((3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2) +
          lsfInitSize (D.G 0) * lg ^ 2 +
          ((post_b s).trees j).activeComps.sum lazyFn +
          (∑ x ∈ Finset.range s, (D.U (x + 1)).length) +
          (∑ x ∈ Finset.range s, ((post_b x).trees j).S_cur.batchEnc (infoB x).U_S) +
          (∑ x ∈ Finset.range s, lsfBatchSize ((post_b x).trees j).cs (D.U (x + 1))) +
          2 * (∑ x ∈ Finset.range s, ((infoB x).state.activeComps.sum fun C =>
            (st₀.activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) L
                ((((post_b x).trees j).initBunG (C, b)).n + splitB)
                (((post_b x).trees j).initBunG (C, b))
                (((post_b x).trees j).dyn (C, b)).G ((infoB x).U_B (C, b)))) +
          ∑ r ∈ Finset.range (s + 1), (restarts r).count j *
            (((pre_b r).trees j).cs.G.m + 1 +
              ((pre_b r).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) L splitB
                  (normGraph (restartBucketBundle ((pre_b r).trees j) (ord r) C b).graph))) +
        lg * ((D.U (s + 1)).length +
          ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S +
          lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1)) +
          2 * ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
            spanBatchChargeWith spanConst (params M) L
              ((((post_b s).trees j).initBunG (C, b)).n + splitB)
              (((post_b s).trees j).initBunG (C, b))
              (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b))) +
          (infoB s).newlyActive.sum lazyFn) +
        lg * ((restarts (s + 1)).count j *
          (((pre_b (s + 1)).trees j).cs.G.m + 1 +
            ((pre_b (s + 1)).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
              spanConst * spanInitBound (params M) L splitB
                (normGraph (restartBucketBundle ((pre_b (s + 1)).trees j) (ord (s + 1)) C b).graph))) =
        lg * ((3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2) +
          lsfInitSize (D.G 0) * lg ^ 2 +
          (((post_b s).trees j).activeComps.sum lazyFn + (infoB s).newlyActive.sum lazyFn) +
          ((∑ x ∈ Finset.range s, (D.U (x + 1)).length) + (D.U (s + 1)).length) +
          ((∑ x ∈ Finset.range s, ((post_b x).trees j).S_cur.batchEnc (infoB x).U_S) +
            ((post_b s).trees j).S_cur.batchEnc (infoB s).U_S) +
          ((∑ x ∈ Finset.range s, lsfBatchSize ((post_b x).trees j).cs (D.U (x + 1))) +
            lsfBatchSize ((post_b s).trees j).cs (D.U (s + 1))) +
          2 * ((∑ x ∈ Finset.range s, ((infoB x).state.activeComps.sum fun C =>
            (st₀.activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) L
                ((((post_b x).trees j).initBunG (C, b)).n + splitB)
                (((post_b x).trees j).initBunG (C, b))
                (((post_b x).trees j).dyn (C, b)).G ((infoB x).U_B (C, b)))) +
            ((infoB s).state.activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
              spanBatchChargeWith spanConst (params M) L
                ((((post_b s).trees j).initBunG (C, b)).n + splitB)
                (((post_b s).trees j).initBunG (C, b))
                (((post_b s).trees j).dyn (C, b)).G ((infoB s).U_B (C, b)))) +
          ((∑ r ∈ Finset.range (s + 1), (restarts r).count j *
            (((pre_b r).trees j).cs.G.m + 1 +
              ((pre_b r).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
                spanConst * spanInitBound (params M) L splitB
                  (normGraph (restartBucketBundle ((pre_b r).trees j) (ord r) C b).graph))) +
            (restarts (s + 1)).count j *
              (((pre_b (s + 1)).trees j).cs.G.m + 1 +
                ((pre_b (s + 1)).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
                  spanConst * spanInitBound (params M) L splitB
                    (normGraph (restartBucketBundle ((pre_b (s + 1)).trees j) (ord (s + 1)) C b).graph)))) := by
      ring
    exact le_trans (le_of_eq hLhs) (le_trans hstep_le (le_of_eq hRhs))

/-! ## Epoch `initBunG` invariant -/

private lemma foldl_bundleRestart_initBunG_inactive
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (j : ℕ) {C : Finset ℕ} {b : ℤ}
    (hna : C ∉ (st.trees j).activeComps) :
    ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees
        j).initBunG (C, b) = (st.trees j).initBunG (C, b) := by
  let r : SparseCoreBundleState L → ℕ → SparseCoreBundleState L :=
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart
  change ((xs.foldl r st).trees j).initBunG (C, b) = (st.trees j).initBunG (C, b)
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    have hact : ((r st x).trees j).activeComps = (st.trees j).activeComps := by
      change (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees
        j).activeComps = _
      rw [sparseCoreBundleRestartTool_restart_eq]
      split_ifs with hne
      · by_cases hjx : j = x
        · subst hjx; simp only [Function.update_self]; rfl
        · simp only [Function.update_of_ne hjx]
      · rfl
    have hinit : ((r st x).trees j).initBunG (C, b) = (st.trees j).initBunG (C, b) := by
      change (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees
        j).initBunG (C, b) = _
      rw [sparseCoreBundleRestartTool_restart_eq]
      split_ifs with hne
      · by_cases hjx : j = x
        · subst hjx; simp only [Function.update_self, restartBundleTree, hna, ↓reduceIte]
        · simp only [Function.update_of_ne hjx]
      · rfl
    rw [ih _ (hact.symm ▸ hna), hinit]

private lemma foldl_bundleRestart_initBunG_active
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (j : ℕ)
    (hne : st.isNonempty = true) (hmem : j ∈ xs) {C : Finset ℕ} {b : ℤ}
    (hact : C ∈ (st.trees j).activeComps) :
    let tr' := (xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j
    tr'.initBunG (C, b) = normGraph (tr'.bun (C, b)).graph := by
  classical
  induction xs generalizing st with
  | nil => simp at hmem
  | cons x xs ih =>
    dsimp only [List.foldl_cons]
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    have hR : T.restart st x =
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees x (restartBundleTree L sparsify (st.trees x) st.ord) } := by
      dsimp only [T]; rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
    have hne' : (T.restart st x).isNonempty = true := by rw [hR]; exact hne
    have hact' : C ∈ ((T.restart st x).trees j).activeComps := by
      rw [hR]; dsimp only
      by_cases hjx : j = x
      · subst hjx; simp only [Function.update_self]; exact hact
      · simp only [Function.update_of_ne hjx]; exact hact
    rcases List.mem_cons.mp hmem with rfl | htail
    · by_cases htail' : j ∈ xs
      · exact ih (T.restart st j) hne' htail' hact'
      · let r : SparseCoreBundleState L → ℕ → SparseCoreBundleState L :=
          (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart
        have hno : ∀ (ys : List ℕ) (s : SparseCoreBundleState L), j ∉ ys →
            (ys.foldl r s).trees j = s.trees j := by
          intro ys
          induction ys with
          | nil => intro _ _; rfl
          | cons y ys ihy =>
            intro s hny
            have hjy : j ≠ y := fun h => hny (by subst h; exact List.mem_cons_self)
            have hny' : j ∉ ys := fun h => hny (List.mem_cons_of_mem y h)
            rw [List.foldl_cons, ihy _ hny']
            change ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart s y).trees j = _
            rw [sparseCoreBundleRestartTool_restart_eq]
            split_ifs
            · simp only [Function.update_of_ne hjy]
            · rfl
        have htr : ((j :: xs).foldl r st).trees j = (r st j).trees j := by
          rw [List.foldl_cons]
          exact hno xs (r st j) htail'
        change (((j :: xs).foldl r st).trees j).initBunG (C, b) =
          normGraph ((((j :: xs).foldl r st).trees j).bun (C, b)).graph
        rw [htr]
        change ((T.restart st j).trees j).initBunG (C, b) =
          normGraph (((T.restart st j).trees j).bun (C, b)).graph
        rw [hR]
        simp only [Function.update_self, restartBundleTree, hact, ↓reduceIte]
    · exact ih (T.restart st x) hne' htail hact'

private lemma runOrdAfterRestarts_initBunG_inactive
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    ∀ t C b, C ∉ ((T.runOrdAfterUpdate k M N D ord restarts t).1.trees j).activeComps →
      ((T.runOrdAfterUpdate k M N D ord restarts t).1.trees j).initBunG (C, b) =
        normGraph (st₀.bun (C, b)).graph ∧
      ((T.runOrdAfterRestarts k M N D ord restarts t).trees j).initBunG (C, b) =
        normGraph (st₀.bun (C, b)).graph := by
  intro T st₀ t
  have hne_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  induction t with
  | zero =>
    intro C b hna
    have hpre0 : ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).initBunG (C, b) =
        normGraph (st₀.bun (C, b)).graph := rfl
    have hpost0 := foldl_bundleRestart_initBunG_inactive lsfInit C_lsst L sparsify (restarts 0)
      (T.runOrdAfterUpdate k M N D ord restarts 0).1 j (b := b) hna
    exact ⟨hpre0, hpost0.trans hpre0⟩
  | succ s ih =>
    intro C b hna
    have hpre_eq : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j =
        (stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).state := by
      dsimp only [T]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
        sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne_post s), hord_post s]
    have hna_post_s : C ∉ ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).activeComps := by
      intro h; apply hna; rw [hpre_eq]
      exact Finset.mem_union_left _ h
    have hact_s : ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).activeComps =
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).activeComps :=
      ((foldl_bundleRestart_props lsfInit C_lsst L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j).activeComps
    have hprev := (ih C b (hact_s ▸ hna_post_s)).2
    have hpre1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).initBunG (C, b) =
        normGraph (st₀.bun (C, b)).graph := by
      rw [hpre_eq]; exact hprev
    have hpost1 := foldl_bundleRestart_initBunG_inactive lsfInit C_lsst L sparsify (restarts (s + 1))
      (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 j (b := b) hna
    exact ⟨hpre1, hpost1.trans hpre1⟩

/-- Along any non-restarted epoch `[s₀, t]`, `initBunG (C, b)` stays equal to
`normGraph ((ep 0).bun (C, b)).graph` for every component `C ∈ components (D.G 0)` and bucket `b`. -/
lemma epochBundleSeq_initBunG_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    ∀ r ≤ t - s₀, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (ep r).initBunG (C, b) = normGraph ((ep 0).bun (C, b)).graph := by
  intro ep
  obtain ⟨_, hSt_step⟩ := epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  have hconst : ∀ r ≤ t - s₀, (ep r).initBunG = (ep 0).initBunG := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have h1 : (ep (m + 1)).initBunG = (ep m).initBunG := by
        dsimp only [ep]; rw [(hSt_step m hm).1]; rfl
      exact h1.trans (ih (Nat.le_of_succ_le hm))
  intro r hr C hC b
  rw [hconst r hr]
  set T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
  have hne_pre : (T.runOrdAfterUpdate k M N D ord restarts s₀).1.isNonempty = true :=
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s₀).1.trans
      (decide_eq_true hV₀)
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit s₀ (le_trans hst htτ)
  have hep0 : ep 0 = (T.runOrdAfterRestarts k M N D ord restarts s₀).trees j := by
    by_cases hlt : 0 < t - s₀
    · simpa using (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j hst).1 0 hlt
    · have hEq : s₀ = t := by omega
      subst hEq
      have := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ s₀ j le_rfl).2.1
        (Or.inr rfl)
      simpa using this
  rw [hep0]
  by_cases hmem : j ∈ restarts s₀
  · by_cases hact : C ∈ ((T.runOrdAfterUpdate k M N D ord restarts s₀).1.trees j).activeComps
    · exact foldl_bundleRestart_initBunG_active lsfInit C_lsst L sparsify (restarts s₀)
        (T.runOrdAfterUpdate k M N D ord restarts s₀).1 j hne_pre hmem hact
    · have h1 := (runOrdAfterRestarts_initBunG_inactive lsfInit C_lsst L sparsify
        k M N D ord restarts hV₀ j s₀ C b hact).2
      have h2 := ((hBun.2.2.2.2.2.2.2.2.2.2.1 C hC hact).2 b).2.2.1
      rw [h1, h2]
  · have hs0 : s₀ = 0 := hs₀.resolve_right hmem
    subst hs0
    let r : SparseCoreBundleState L → ℕ → SparseCoreBundleState L :=
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart
    have hno : ∀ (ys : List ℕ) (s : SparseCoreBundleState L), j ∉ ys →
        (ys.foldl r s).trees j = s.trees j := by
      intro ys
      induction ys with
      | nil => intro _ _; rfl
      | cons y ys ihy =>
        intro s hny
        have hjy : j ≠ y := fun h => hny (by subst h; exact List.mem_cons_self)
        have hny' : j ∉ ys := fun h => hny (List.mem_cons_of_mem y h)
        rw [List.foldl_cons, ihy _ hny']
        change ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart s y).trees j = _
        rw [sparseCoreBundleRestartTool_restart_eq]
        split_ifs
        · simp only [Function.update_of_ne hjy]
        · rfl
    have htree0 : (T.runOrdAfterRestarts k M N D ord restarts 0).trees j =
        (T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j :=
      hno (restarts 0) _ hmem
    rw [htree0]
    rfl

end MinCostFlow.Chain

end
