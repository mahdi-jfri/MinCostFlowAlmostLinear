module

public import MinCostFlow.Chain.BundleRestart
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.DynSpanner.StepTransition

/-!
# Global Bundle Invariant Along Restarts

Proves `runOrdAfterRestarts_bun_inv`, together with the restart-fold helpers
`foldl_bundleRestart_inactive`, `foldl_bundleRestart_active`, `bundleRunBatchState_take_eq`, and
`bundleRunBatchStepOut_take_eq`. At every stage `t ≤ τ` (both before and after `restarts t`),
without needing `hThresh`, `hM`, or `hSp`, every component-bucket bundle state satisfies
`BundleCompReady` for the current order `ord t`, keeps the exact surviving edge set
`(st₀.bun (C, b)).edges \ ⋃_{1 ≤ s ≤ t} batchDeletes (D.U s)` disjoint from `insertedGlobal`,
matches `(dyn (C, b)).G`, and stays unchanged on inactive components.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Restart-fold and `runBatchState` helpers -/

lemma foldl_bundleRestart_inactive
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (j : ℕ) {C : Finset ℕ} {b : ℤ}
    (hna : C ∉ (st.trees j).activeComps) :
    let st' := xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st
    (st'.trees j).bun (C, b) = (st.trees j).bun (C, b) ∧
    (st'.trees j).dyn (C, b) = (st.trees j).dyn (C, b) := by
  induction xs generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    have hx_act : C ∉ (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).activeComps := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      split_ifs with hne
      · dsimp only
        by_cases hjx : j = x
        · subst hjx
          rw [Function.update_self, (restartBundleTree_base_fields sparsify _ _).activeComps]
          exact hna
        · rw [Function.update_of_ne hjx]; exact hna
      · exact hna
    have hx_bd :
        (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).bun (C, b) =
          (st.trees j).bun (C, b) ∧
        (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).dyn (C, b) =
          (st.trees j).dyn (C, b) := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      split_ifs with hne
      · dsimp only
        by_cases hjx : j = x
        · subst hjx
          rw [Function.update_self]
          dsimp only [restartBundleTree]
          simp [hna]
        · rw [Function.update_of_ne hjx]; exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    have hrec := ih ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x) hx_act
    exact ⟨hrec.1.trans hx_bd.1, hrec.2.trans hx_bd.2⟩

lemma foldl_bundleRestart_active
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (j : ℕ) {C : Finset ℕ} {b : ℤ}
    (hne : st.isNonempty = true) (hact : C ∈ (st.trees j).activeComps) (hj : j ∈ xs) :
    let st' := xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st
    (st'.trees j).bun (C, b) = restartBucketBundle (st.trees j) st.ord C b ∧
    (st'.trees j).dyn (C, b) =
      (DynSpanner.init (normGraph (restartBucketBundle (st.trees j) st.ord C b).graph) L
        (phaseBase ((restartBucketBundle (st.trees j) st.ord C b).graph.n + (st.trees j).splitBound) L)
        (sparsify (st.trees j).m₀)).state := by
  induction xs generalizing st with
  | nil => cases hj
  | cons x xs ih =>
    have hx_ne : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).isNonempty = true := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      simp only [hne, ↓reduceIte]
    have hx_ord : ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).ord = st.ord :=
      sparseCoreBundleRestartTool_restart_ord lsfInit C_lsst L sparsify st x
    have hf1 := (foldl_bundleRestart_props lsfInit C_lsst L sparsify st [x]).2.2.2.2.1 j
    dsimp only [List.foldl] at hf1
    have hx_act : C ∈ (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).activeComps := by
      rw [hf1.activeComps]; exact hact
    have hx_rb : restartBucketBundle
        (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j) st.ord C b =
        restartBucketBundle (st.trees j) st.ord C b := by
      rw [sparseCoreBundleRestartTool_restart_eq]
      simp only [hne, ↓reduceIte]
      by_cases hjx : j = x
      · subst hjx
        simp only [Function.update_self]
        exact restartBucketBundle_restartBundleTree sparsify (st.trees j) st.ord C b
      · simp only [Function.update_of_ne hjx]
    have hx_spB : (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).splitBound =
        (st.trees j).splitBound := hf1.splitBound
    have hx_m0 : (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x).trees j).m₀ =
        (st.trees j).m₀ := hf1.m₀
    by_cases hmem : j ∈ xs
    · have h1 := ih ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x) hx_ne hx_act hmem
      dsimp only at h1 ⊢
      rw [hx_ord, hx_rb, hx_spB, hx_m0] at h1
      exact h1
    · have hjx : j = x := (List.mem_cons.mp hj).resolve_right hmem
      subst hjx
      have hni := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j) xs).2.2.2.2.2 j hmem
      dsimp only [List.foldl] at hni ⊢
      rw [hni]
      rw [sparseCoreBundleRestartTool_restart_eq]
      simp only [hne, ↓reduceIte, Function.update_self]
      dsimp only [restartBundleTree]
      simp [hact]

lemma bundleRunBatchState_take_eq {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) :
    ∀ k d, k ≤ d →
      DynSpanner.runBatchState (L := L) G₀ q sparsify Us k =
        DynSpanner.runBatchState (L := L) G₀ q sparsify (Us.take d) k := by
  intro k d hkd
  induction k with
  | zero => rfl
  | succ m ih =>
    have hm_lt : m < d := hkd
    have ih' := ih (Nat.le_of_lt hm_lt)
    dsimp only [DynSpanner.runBatchState]
    rw [List.getElem?_take_of_lt hm_lt, ← ih']

lemma bundleRunBatchStepOut_take_eq {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) {k d : ℕ} (hkd : k < d) :
    DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us k =
      DynSpanner.runBatchStepOut (L := L) G₀ q sparsify (Us.take d) k := by
  dsimp only [DynSpanner.runBatchStepOut]
  rw [List.getElem?_take_of_lt hkd,
    ← bundleRunBatchState_take_eq G₀ q sparsify Us k d (Nat.le_of_lt hkd)]

/-! ## 2. Global bundle invariant along `runOrdAfterUpdate` and `runOrdAfterRestarts` -/

private lemma mem_foldl_updateInserted_cases (U : List Update) (ins : Finset ℕ) {e : ℕ}
    (he : e ∈ U.foldl updateInserted ins) :
    e ∈ ins ∨ ∃ u ∈ U, u.Inserts e := by
  induction U generalizing ins with
  | nil => exact Or.inl he
  | cons u rest ih =>
    dsimp only [List.foldl_cons] at he
    rcases ih (updateInserted ins u) he with h1 | ⟨u', hu', hIu'⟩
    · cases u with
      | split _ _ _ _ => exact Or.inl h1
      | delete e₀ => exact Or.inl (Finset.mem_of_mem_erase h1)
      | insert e₀ a b =>
        rcases Finset.mem_insert.mp h1 with rfl | hmem
        · exact Or.inr ⟨.insert e a b, List.mem_cons_self, rfl⟩
        · exact Or.inl hmem
    · exact Or.inr ⟨u', List.mem_cons_of_mem u hu', hIu'⟩

private lemma disjoint_sdiff_batchDeletes_inserted {cs : CompLSFState} {U : List Update}
    {E : Finset ℕ} (hBU : cs.G.BatchIsValid U) (hE : E ⊆ cs.G.E)
    (hDisj : Disjoint E cs.insertedGlobal) :
    Disjoint (E \ batchDeletes U) (compLSFBatch cs U).insertedGlobal := by
  rw [compLSFBatch_insertedGlobal]
  refine Finset.disjoint_left.mpr fun e he hins => ?_
  obtain ⟨heE, hnd⟩ := Finset.mem_sdiff.mp he
  rcases mem_foldl_updateInserted_cases U cs.insertedGlobal hins with h0 | ⟨u, hu, hIu⟩
  · exact Finset.disjoint_left.mp hDisj heE h0
  · exact hnd (mem_batchDeletes_of_inserts hBU (hE heE) ⟨u, hu, hIu⟩)

private lemma foldl_bundleRestart_ready
    (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {ℓ₀ : ℕ → ℝ} {G₀ : MGraph} {k : ℕ} (hk : 1 ≤ k)
    (xs : List ℕ) (st : SparseCoreBundleState L) (j : ℕ)
    (hne : st.isNonempty = true) (hk_st : (st.trees j).k = k)
    (hG₀ : (st.trees j).cs.G₀ = G₀) (hI : CompLSFInv C_lsst ℓ₀ (st.trees j).cs)
    (ρ : Rotation (st.trees j).cs.G) (hρ : ρ.order = st.ord)
    {C : Finset ℕ} (hC : C ∈ components G₀) (b : ℤ)
    (hReady : BundleCompReady (st.trees j).cs C ((st.trees j).bun (C, b)) k st.ord)
    (hDisj : Disjoint ((st.trees j).bun (C, b)).edges (st.trees j).cs.insertedGlobal)
    (hDynG : GraphEq ((st.trees j).dyn (C, b)).G ((st.trees j).bun (C, b)).graph) :
    let tr' := (xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j
    BundleCompReady tr'.cs C (tr'.bun (C, b)) k st.ord ∧
    (tr'.bun (C, b)).edges = ((st.trees j).bun (C, b)).edges ∧
    GraphEq (tr'.dyn (C, b)).G (tr'.bun (C, b)).graph := by
  intro tr'
  have hbase := (foldl_bundleRestart_props lsfInit C_lsst L sparsify st xs).2.2.2.2.1 j
  by_cases hj : j ∈ xs
  · by_cases hact : C ∈ (st.trees j).activeComps
    · have ha := foldl_bundleRestart_active lsfInit C_lsst L sparsify xs st j (C := C) (b := b)
        hne hact hj
      have hbun_eq : tr'.bun (C, b) =
          initBundleState (coreRotation (L := (st.trees j).cs.lsf) ρ hI.hG_val
            (compLSF_RF_isRSF hI)) ((st.trees j).bun (C, b)).edges k := by
        rw [ha.1]
        dsimp only [restartBucketBundle]
        rw [hk_st]
        exact initBundleFor_eq hI hρ _ _
      have hE_core : ((st.trees j).bun (C, b)).edges ⊆
          (coreGraph (st.trees j).cs.G (st.trees j).cs.lsf).E :=
        (hReady.1 ρ hI.hG_val (compLSF_RF_isRSF hI) hρ).1
      have hCross : ∀ e ∈ ((st.trees j).bun (C, b)).edges, e ∉ (st.trees j).cs.crossEdges :=
        fun e he hc => Finset.disjoint_left.mp hDisj he (hI.hCross_sub hc)
      refine ⟨?_, ?_, ?_⟩
      · rw [hbase.cs, hbun_eq]
        refine ⟨fun ρ' hG hF hρ' => ?_,
          initBundleState_parent_mem hI (hG₀.symm ▸ hC) _ hE_core hReady.2.2 hCross k,
          hReady.2.2⟩
        rw [coreRotation_eq_of_order (hρ.trans hρ'.symm) hI.hG_val hG (compLSF_RF_isRSF hI) hF]
        exact initBundleState_inv _ (coreGraph_isValid hG hF) hE_core hk
      · rw [hbun_eq]; rfl
      · rw [ha.2, ha.1]; exact normGraph_graphEq _
    · have hi := foldl_bundleRestart_inactive lsfInit C_lsst L sparsify xs st j (C := C) (b := b) hact
      rw [hbase.cs, hi.1, hi.2]
      exact ⟨hReady, rfl, hDynG⟩
  · have hni := (foldl_bundleRestart_props lsfInit C_lsst L sparsify st xs).2.2.2.2.2 j hj
    dsimp only [tr']
    rw [hni]
    exact ⟨hReady, rfl, hDynG⟩

/-- Global bundle-stage invariant along a run of `sparseCoreBundleRestartToolWith` with arbitrary
restarts (requiring only `hInit`, `hD`, `hOrd`, and no `hThresh`, `hM`, or `hSp`). -/
theorem runOrdAfterRestarts_bun_inv
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let G₀ := D.G 0
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
    let cs₀ := st₀.cs
    let splitB := bundleSplitBudget k M
    ∀ t ≤ τ,
      let pre := (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
      let post := (T.runOrdAfterRestarts k M N D ord restarts t).trees j
      pre.k = k ∧ pre.m₀ = M ∧ pre.splitBound = splitB ∧
      pre.origBucket = st₀.origBucket ∧ pre.activeBuckets = st₀.activeBuckets ∧
      pre.lazyInitCost = st₀.lazyInitCost ∧
      pre.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst (D.ℓ 0) pre.cs ∧
      pre.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ pre.activeComps ∧ pre.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ pre.activeComps →
        pre.cs.compSt C = cs₀.compSt C ∧
        ∀ b : ℤ, pre.bun (C, b) = st₀.bun (C, b) ∧ pre.dyn (C, b) = st₀.dyn (C, b) ∧
          post.bun (C, b) = st₀.bun (C, b) ∧ post.dyn (C, b) = st₀.dyn (C, b)) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (pre.cs.compSt C) ∧
        ∀ b : ℤ,
          BundleCompReady pre.cs C (pre.bun (C, b)) k (ord t) ∧
          BundleCompReady post.cs C (post.bun (C, b)) k (ord t) ∧
          (pre.bun (C, b)).edges =
            (st₀.bun (C, b)).edges \ (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)) ∧
          (post.bun (C, b)).edges = (pre.bun (C, b)).edges ∧
          Disjoint (pre.bun (C, b)).edges pre.cs.insertedGlobal ∧
          GraphEq (pre.dyn (C, b)).G (pre.bun (C, b)).graph ∧
          GraphEq (post.dyn (C, b)).G (post.bun (C, b)).graph) := by
  classical
  intro T G₀ st₀ cs₀ splitB
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hS₀ : ∀ C ∈ components G₀, (cs₀.compSt C).G₀ = compGraph G₀ C ∧
      (cs₀.compSt C).G = compGraph G₀ C ∧ (cs₀.compSt C).isolatedVerts = ∅ := by
    intro C hC
    set ℓs := safeLen G₀ (D.ℓ 0)
    have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
      rw [show ℓs e = D.ℓ 0 e from safeLen_eq_of_mem (D.ℓ 0) heG]
      exact hℓ₀ e heG
    have hsp := hInit (compGraph G₀ C) ℓs (compGraph_isValid hG₀ hC) (compGraph_nonempty hC) hℓC hk
    exact ⟨hsp.2.1, hsp.2.2.1, hsp.2.2.2.2.1⟩
  have hne_pre : ∀ s, (T.runOrdAfterUpdate k M N D ord restarts s).1.isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).1.trans
      (decide_eq_true hV₀)
  have hne_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord_pre : ∀ s, (T.runOrdAfterUpdate k M N D ord restarts s).1.ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).1
  have hord_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := cs₀.G) rfl
    have hbun₀ : ∀ C b, st₀.bun (C, b) = initBundleState
        (coreRotation (L := cs₀.lsf) ρ₀ hI₀.hG_val (compLSF_RF_isRSF hI₀))
        (bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b) k :=
      fun C b => initBundleFor_eq hI₀ hρ₀ _ _
    have hE₀core : ∀ C b, bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b ⊆
        (coreGraph cs₀.G cs₀.lsf).E := fun C b => Finset.filter_subset _ _
    have hE₀C : ∀ C ∈ components G₀, ∀ b,
        bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b ⊆ (cs₀.compSt C).G.E := by
      intro C hC b e he
      obtain ⟨heC, htC, -⟩ := Finset.mem_filter.mp he
      have heG : e ∈ cs₀.G.E := (Finset.mem_sdiff.mp heC).1
      have hroot : cs₀.RF.root (cs₀.G.tail e) ∈ (cs₀.compSt C).G.V := by
        rw [(hS₀ C hC).2.1]; exact htC
      have ht := compLSF_mem_V_of_root hI₀ hC (hI₀.hG_val e heG).1 hroot
      rw [(hS₀ C hC).2.1] at ht ⊢
      exact Finset.mem_filter.mpr ⟨heG, ht⟩
    have hready₀ : ∀ C ∈ components G₀, ∀ b,
        BundleCompReady cs₀ C (st₀.bun (C, b)) k (ord 0) := by
      intro C hC b
      rw [hbun₀ C b]
      refine ⟨fun ρ hG hF hρ => ?_, initBundleState_parent_mem hI₀ hC _ (hE₀core C b)
        (hE₀C C hC b) (fun e _ => Finset.notMem_empty e) k, hE₀C C hC b⟩
      rw [coreRotation_eq_of_order (hρ₀.trans hρ.symm) hI₀.hG_val hG (compLSF_RF_isRSF hI₀) hF]
      exact initBundleState_inv _ (coreGraph_isValid hG hF) (hE₀core C b) hk
    have hpre0 : (T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j = st₀ := rfl
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI₀, rfl, ⟨Finset.Subset.rfl, largeComps_sub⟩,
      fun C _ hna => ⟨rfl, fun b => ?_⟩, fun C hC => ⟨?_, fun b => ?_⟩⟩
    · have hi := foldl_bundleRestart_inactive lsfInit C_lsst L sparsify (restarts 0)
        (T.runOrdAfterUpdate k M N D ord restarts 0).1 j (C := C) (b := b) hna
      exact ⟨rfl, rfl, hi.1, hi.2⟩
    · exact lsfDerivedFrom_refl ((hS₀ C hC).2.1.trans (hS₀ C hC).1.symm) (hS₀ C hC).2.2
    · have hDynG₀ : GraphEq (st₀.dyn (C, b)).G (st₀.bun (C, b)).graph :=
        normGraph_graphEq (st₀.bun (C, b)).graph
      have hpost0 := foldl_bundleRestart_ready lsfInit L sparsify hk (restarts 0)
        (T.runOrdAfterUpdate k M N D ord restarts 0).1 j (hne_pre 0) rfl rfl hI₀ ρ₀ hρ₀ hC b
        (hready₀ C hC b) (by change Disjoint _ ∅; exact Finset.disjoint_empty_right _) hDynG₀
      refine ⟨hready₀ C hC b, hpost0.1, ?_, hpost0.2.1,
        by change Disjoint _ ∅; exact Finset.disjoint_empty_right _, hDynG₀, hpost0.2.2⟩
      simp [hpre0]
  | succ s ih =>
    intro hs_le
    obtain ⟨hk_s, hm_s, hsb_s, hob_s, hab_s, hlc_s, hCS, hI_s, hGs, hAct_s, hUnt_s, hC_s⟩ :=
      ih (Nat.le_of_succ_le hs_le)
    set pre_s := (T.runOrdAfterUpdate k M N D ord restarts s).1.trees j
    set post_s := (T.runOrdAfterRestarts k M N D ord restarts s).trees j
    have hbf_s := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j
    have hk_post : post_s.k = k := hbf_s.k.trans hk_s
    have hm_post : post_s.m₀ = M := hbf_s.m₀.trans hm_s
    have hsb_post : post_s.splitBound = splitB := hbf_s.splitBound.trans hsb_s
    have hob_post : post_s.origBucket = st₀.origBucket := hbf_s.origBucket.trans hob_s
    have hab_post : post_s.activeBuckets = st₀.activeBuckets := hbf_s.activeBuckets.trans hab_s
    have hlc_post : post_s.lazyInitCost = st₀.lazyInitCost := hbf_s.lazyInitCost.trans hlc_s
    have hcs_post : post_s.cs = pre_s.cs := hbf_s.cs
    have hact_post : post_s.activeComps = pre_s.activeComps := hbf_s.activeComps
    have hI_post : CompLSFInv C_lsst (D.ℓ 0) post_s.cs := hcs_post.symm ▸ hI_s
    have hG_post : post_s.cs.G = D.G s := by rw [hcs_post, hGs]
    have hG₀_post : post_s.cs.G₀ = G₀ := by rw [hcs_post, hCS, compLSFBatch_G₀]; rfl
    set U := D.U (s + 1)
    have hDt := hD (s + 1) (Nat.succ_pos s) hs_le
    simp only [Nat.add_sub_cancel] at hDt
    have hBV : post_s.cs.G.BatchIsValid U := by rw [hG_post]; exact hDt.1
    have hsp := compLSFBatch_step_props U hI_post hBV
    obtain ⟨ρ, σ, hρ, hσ, hrot⟩ := orderedUpTo_rot_step hOrd hs_le hG_post
    have hpre_eq : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j =
        (stepBundleTree sparsify post_s U (ord s) (ord (s + 1))).state := by
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne_post s), hord_post s]
    have hcs1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs =
        compLSFBatch post_s.cs U := by rw [hpre_eq]; rfl
    have hG1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.G = D.G (s + 1) := by
      rw [hcs1, hsp.2.1, hG_post]; exact hDt.2.symm
    have hG₀_1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.G₀ = G₀ := by
      rw [hcs1, compLSFBatch_G₀, hG₀_post]
    have hI_1 : CompLSFInv C_lsst (D.ℓ 0)
        ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs := by
      rw [hcs1]; exact hsp.1
    have hk_1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).k = k := by
      rw [hpre_eq]; exact hk_post
    have hstep : ∀ C ∈ components G₀, ∀ b,
        let out := bundleCompStep post_s.cs (post_s.bun (C, b)) k (ord s) (ord (s + 1)) U
        BundleCompReady (compLSFBatch post_s.cs U) C out.2 k (ord (s + 1)) ∧
        out.2.edges = (post_s.bun (C, b)).edges \ batchDeletes U ∧
        out.2.graph = (post_s.bun (C, b)).graph.applyBatch out.1 ∧
        (C ∉ touchedCompsBatch post_s.cs U → out = ([], post_s.bun (C, b))) := by
      intro C hC b
      have h := bundleCompStep_stage hI_post hBV hρ hσ hrot (hG₀_post ▸ hC)
        ((hC_s C hC).2 b).2.1
      exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
    have hbun1 : ∀ p, ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun p =
        (bundleCompStep post_s.cs (post_s.bun p) k (ord s) (ord (s + 1)) U).2 := fun p => by
      rw [hpre_eq]; change (bundleCompStep post_s.cs (post_s.bun p) post_s.k _ _ _).2 = _
      rw [hk_post]
    have hdyn1 : ∀ p, ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).dyn p =
        (DynSpanner.update (post_s.dyn p)
          (bundleCompStep post_s.cs (post_s.bun p) k (ord s) (ord (s + 1)) U).1
          (sparsify M)).state := fun p => by
      rw [hpre_eq]
      change (DynSpanner.update (post_s.dyn p)
        (bundleCompStep post_s.cs (post_s.bun p) post_s.k _ _ _).1 (sparsify post_s.m₀)).state = _
      rw [hk_post, hm_post]
    have hact1 : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).activeComps =
        post_s.activeComps ∪ (touchedCompsBatch post_s.cs U \ post_s.activeComps) := by
      rw [hpre_eq]; rfl
    refine ⟨hk_1, by rw [hpre_eq]; exact hm_post, by rw [hpre_eq]; exact hsb_post,
      by rw [hpre_eq]; exact hob_post, by rw [hpre_eq]; exact hab_post,
      by rw [hpre_eq]; exact hlc_post, ?_, hI_1, hG1, ?_, ?_, ?_⟩
    · rw [hcs1, hcs_post, hCS, ← compLSFBatch_dynBatches_succ]
    · rw [hact1]
      refine ⟨(hact_post.symm ▸ hAct_s.1).trans Finset.subset_union_left,
        Finset.union_subset (hact_post.symm ▸ hAct_s.2) (Finset.sdiff_subset.trans ?_)⟩
      rw [← hG₀_post]
      exact Finset.filter_subset _ _
    · intro C hC hna
      have hna_post : C ∉ post_s.activeComps := fun h => hna (by rw [hact1]; exact Finset.mem_union_left _ h)
      have hna_pre : C ∉ pre_s.activeComps := hact_post ▸ hna_post
      have hnt : C ∉ touchedCompsBatch post_s.cs U := fun h =>
        hna (by rw [hact1]; exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hna_post⟩))
      have hunt := compLSFBatch_untouched hI_post hBV (hG₀_post ▸ hC) hnt
      obtain ⟨hprev, hprevb⟩ := hUnt_s C hC hna_pre
      refine ⟨by rw [hcs1, hunt.2, hcs_post, hprev], fun b => ?_⟩
      have hout := (hstep C hC b).2.2.2 hnt
      have hbun_eq : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun (C, b) =
          st₀.bun (C, b) := by
        rw [hbun1, hout, (hprevb b).2.2.1]
      have hdyn_eq : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).dyn (C, b) =
          st₀.dyn (C, b) := by
        rw [hdyn1, hout, update_nil, (hprevb b).2.2.2]
      have hi := foldl_bundleRestart_inactive lsfInit C_lsst L sparsify (restarts (s + 1))
        (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 j (C := C) (b := b) hna
      exact ⟨hbun_eq, hdyn_eq, hi.1.trans hbun_eq, hi.2.trans hdyn_eq⟩
    · intro C hC
      obtain ⟨hDer, hCb⟩ := hC_s C hC
      have hcomp := compLSFBatch_compSt hI_post hBV (hG₀_post ▸ hC)
      refine ⟨?_, fun b => ?_⟩
      · rw [hcs1, hcomp.1]
        exact lsfDerivedFrom_batch (hI_post.hCompLSF C (hG₀_post ▸ hC)).1 hcomp.2.2.1
          (hcs_post.symm ▸ hDer)
      obtain ⟨_, hReady_post, hE_pre, hE_post, hDisj_pre, _, hDynG_post⟩ := hCb b
      obtain ⟨hReady', hEq', hGr', -⟩ := hstep C hC b
      have hReady_1 : BundleCompReady
          ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs C
          (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun (C, b))
          k (ord (s + 1)) := by
        rw [hcs1, hbun1]; exact hReady'
      have hE_1 : (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun (C, b)).edges =
          (st₀.bun (C, b)).edges \
            (Finset.Icc 1 (s + 1)).biUnion (fun r => batchDeletes (D.U r)) := by
        rw [hbun1, hEq', hE_post, hE_pre]
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h0, h1⟩, h2⟩
          refine ⟨h0, ?_⟩
          rintro ⟨r, ⟨hr1, hr2⟩, hr3⟩
          rcases Nat.eq_or_lt_of_le hr2 with rfl | hlt
          · exact h2 hr3
          · exact h1 ⟨r, ⟨hr1, Nat.le_of_lt_succ hlt⟩, hr3⟩
        · rintro ⟨h0, h1⟩
          refine ⟨⟨h0, ?_⟩, ?_⟩
          · rintro ⟨r, ⟨hr1, hr2⟩, hr3⟩
            exact h1 ⟨r, ⟨hr1, Nat.le_succ_of_le hr2⟩, hr3⟩
          · intro h2; exact h1 ⟨s + 1, ⟨Nat.succ_pos s, le_rfl⟩, h2⟩
      have hDisj_post : Disjoint (post_s.bun (C, b)).edges post_s.cs.insertedGlobal := by
        rw [hE_post, hcs_post]; exact hDisj_pre
      have hE_subG : (post_s.bun (C, b)).edges ⊆ post_s.cs.G.E := fun e he =>
        (Finset.mem_sdiff.mp ((hReady_post.1 ρ hI_post.hG_val (compLSF_RF_isRSF hI_post) hρ).1 he)).1
      have hDisj_1 : Disjoint
          (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun (C, b)).edges
          ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.insertedGlobal := by
        rw [hbun1, hEq', hcs1]
        exact disjoint_sdiff_batchDeletes_inserted hBV hE_subG hDisj_post
      have hDynG_1 :
          GraphEq (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).dyn (C, b)).G
            (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).bun (C, b)).graph := by
        rw [hdyn1, update_G_eq, hbun1, hGr']
        exact graphEq_applyBatch hDynG_post _
      obtain ⟨ρ₁, hρ₁⟩ := orderedUpTo_rot_at hOrd hs_le hG1
      have hρ₁' : ρ₁.order = (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.ord :=
        hρ₁.trans (hord_pre (s + 1)).symm
      have hpost1 := foldl_bundleRestart_ready lsfInit L sparsify hk (restarts (s + 1))
        (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 j (hne_pre (s + 1)) hk_1 hG₀_1 hI_1
        ρ₁ hρ₁' hC b (hord_pre (s + 1) ▸ hReady_1) hDisj_1 hDynG_1
      rw [hord_pre (s + 1)] at hpost1
      exact ⟨hReady_1, hpost1.1, hE_1, hpost1.2.1, hDisj_1, hDynG_1, hpost1.2.2⟩

end MinCostFlow.Chain

end
