module

public import MinCostFlow.Chain.BundleRestartDyn
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.BundleStepBounds
import MinCostFlow.SparseCore.BundleInitCount
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Global `S_cur` Invariant and Per-Step Epoch Bounds

Proves `runOrdAfterRestarts_S_cur_inv` (global `S_cur` invariant along `runOrdAfterUpdate` and
`runOrdAfterRestarts`) and `epochBundleSeq_step_spec` (per-step `applyBatch`, empty-batch
invariance, no-reinsert propagation, `newlyActive` properties, and `stepBundleTree_US_len` along
any non-restarted epoch `[s₀, t]`), requiring no `hThresh`. Publicly re-exported by
`BundleRestartInv.lean`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Helper: bundle core membership -/

private lemma bundleCompReady_core_and_root {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {G₀ : MGraph} {C : Finset ℕ} {B : BundleState} {k : ℕ} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hG₀ : cs.G₀ = G₀) (hC : C ∈ components G₀)
    (hR : BundleCompReady cs C B k ord) (hDisj : Disjoint B.edges cs.insertedGlobal)
    (hrot : ∃ ρ : Rotation cs.G, ρ.order = ord) :
    ∀ e ∈ B.edges,
      e ∈ cs.G.E \ cs.RF.F.E ∧ cs.RF.root (cs.G.tail e) ∈ (cs.compSt C).R := by
  obtain ⟨ρ, hρ⟩ := hrot
  have hPart := hR.1 ρ hI.hG_val (compLSF_RF_isRSF hI) hρ
  intro e he
  refine ⟨hPart.1 he, ?_⟩
  have heC := hR.2.2 he
  have hX : e ∉ cs.crossEdges := fun hc => Finset.disjoint_left.mp hDisj he (hI.hCross_sub hc)
  have ht := (hI.hNonCross_ends C (hG₀.symm ▸ hC) e heC hX).1
  have hv : cs.G.tail e ∈ (cs.compSt C).G.V := ht ▸ ((hI.hCompLSF C (hG₀.symm ▸ hC)).1.hG_val e heC).1
  exact compLSF_root_mem_R hI (hG₀.symm ▸ hC) hv

private lemma bundleCompStep_nil {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {G₀ : MGraph} {C : Finset ℕ} {B : BundleState} {k : ℕ} {ord ord' : ℕ → List End}
    {U : List Update} (hUnil : U = [])
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hG₀ : cs.G₀ = G₀) (hC : C ∈ components G₀)
    (hBU : cs.G.BatchIsValid U)
    (ρ : Rotation cs.G) (σ : Rotation (cs.G.applyBatch U))
    (hρ : ρ.order = ord) (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    (hR : BundleCompReady cs C B k ord) :
    (bundleCompStep cs B k ord ord' U).1 = [] ∧
      (bundleCompStep cs B k ord ord' U).2.edges = B.edges := by
  have hstg := bundleCompStep_stage hI hBU hρ hσ hrot (hG₀.symm ▸ hC) hR
  have hsc0 : batchSplitCount (bundleCompStep cs B k ord ord' U).1 = 0 := by
    have hsc := hstg.2.2.2.2.2.1
    subst hUnil
    have hR0 : (((compLSFBatch cs []).compSt C).R \ (cs.compSt C).R).card = 0 := by
      change ((cs.compSt C).R \ (cs.compSt C).R).card = 0; simp
    omega
  have hdl0 : (bundleCompStep cs B k ord ord' U).1.countP deleteTag = 0 := by
    have hdl := hstg.2.2.2.2.2.2.1
    subst hUnil
    have h0 : (B.edges ∩ batchDeletes []).card = 0 := by simp [batchDeletes]
    omega
  refine ⟨eq_nil_of_delOrSplit hstg.2.2.2.2.1 hsc0 hdl0, ?_⟩
  rw [hstg.2.1, hUnil]; simp [batchDeletes]

/-! ## 2. Global `S_cur` invariant along `runOrdAfterRestarts` -/

/-- Global `S_cur` invariant along `runOrdAfterUpdate` and `runOrdAfterRestarts` (requiring only
`hLSST`, `1 ≤ L`, and `hSp`, with no `hThresh`). -/
theorem runOrdAfterRestarts_S_cur_inv
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let G₀ := D.G 0
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
    let actB := st₀.activeBuckets
    ∀ t ≤ τ,
      let pre := (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
      let post := (T.runOrdAfterRestarts k M N D ord restarts t).trees j
      (pre.S_cur.IsValid ∧ pre.S_cur.V = pre.cs.RF.R ∧
        pre.S_cur.E =
          (pre.activeComps.biUnion fun C => (actB C).biUnion fun b => (pre.dyn (C, b)).H.E) ∪
            (pre.activeComps.biUnion fun C => pre.extraEdges C) ∪
            pre.cs.crossEdges ∧
        (coreGraph pre.cs.G pre.cs.lsf).IsSubgraph pre.S_cur) ∧
      (post.S_cur.IsValid ∧ post.S_cur.V = post.cs.RF.R ∧
        post.S_cur.E =
          (post.activeComps.biUnion fun C => (actB C).biUnion fun b => (post.dyn (C, b)).H.E) ∪
            (post.activeComps.biUnion fun C => post.extraEdges C) ∪
            post.cs.crossEdges ∧
        (coreGraph post.cs.G post.cs.lsf).IsSubgraph post.S_cur) := by
  intro T G₀ st₀ actB
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCov₀ : ∀ C ∈ components G₀,
      (st₀.cs.compSt C).W_init.biUnion (inducedEdges (st₀.cs.compSt C).RF.F) =
        (st₀.cs.compSt C).RF.F.E :=
    fun C hC => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC).2.2
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
  have hRestart_pres : ∀ s ≤ τ,
      let pre := (T.runOrdAfterUpdate k M N D ord restarts s).1.trees j
      (pre.S_cur.IsValid ∧ pre.S_cur.V = pre.cs.RF.R ∧
        pre.S_cur.E =
          (pre.activeComps.biUnion fun C => (actB C).biUnion fun b => (pre.dyn (C, b)).H.E) ∪
            (pre.activeComps.biUnion fun C => pre.extraEdges C) ∪
            pre.cs.crossEdges ∧
        (coreGraph pre.cs.G pre.cs.lsf).IsSubgraph pre.S_cur) →
      let post := (T.runOrdAfterRestarts k M N D ord restarts s).trees j
      post.S_cur.IsValid ∧ post.S_cur.V = post.cs.RF.R ∧
        post.S_cur.E =
          (post.activeComps.biUnion fun C => (actB C).biUnion fun b => (post.dyn (C, b)).H.E) ∪
            (post.activeComps.biUnion fun C => post.extraEdges C) ∪
            post.cs.crossEdges ∧
        (coreGraph post.cs.G post.cs.lsf).IsSubgraph post.S_cur := by
    intro s hs pre hpre post
    have hBs := hBun s hs
    have hstep_fold : ∀ (xs : List ℕ) (st : SparseCoreBundleState L),
        st.isNonempty = true → st.ord = ord s →
        ((st.trees j).S_cur.IsValid ∧ (st.trees j).S_cur.V = (st.trees j).cs.RF.R ∧
          (st.trees j).S_cur.E =
            ((st.trees j).activeComps.biUnion fun C => (actB C).biUnion fun b =>
              ((st.trees j).dyn (C, b)).H.E) ∪
              ((st.trees j).activeComps.biUnion fun C => (st.trees j).extraEdges C) ∪
              (st.trees j).cs.crossEdges ∧
          (coreGraph (st.trees j).cs.G (st.trees j).cs.lsf).IsSubgraph (st.trees j).S_cur) →
        BundleBaseFieldsEq (st.trees j) pre →
        (∀ C ∈ components G₀, ∀ b : ℤ, ((st.trees j).bun (C, b)).edges = (pre.bun (C, b)).edges) →
        let tr := (xs.foldl T.restart st).trees j
        tr.S_cur.IsValid ∧ tr.S_cur.V = tr.cs.RF.R ∧
        tr.S_cur.E =
          (tr.activeComps.biUnion fun C => (actB C).biUnion fun b => (tr.dyn (C, b)).H.E) ∪
            (tr.activeComps.biUnion fun C => tr.extraEdges C) ∪
            tr.cs.crossEdges ∧
        (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
      intro xs st hst_ne hst_ord hst_inv hbf_st hE_st
      induction xs generalizing st with
      | nil => exact hst_inv
      | cons x xs ih =>
        dsimp only [List.foldl_cons]
        have hx_ne : (T.restart st x).isNonempty = true := by
          dsimp only [T]; rw [sparseCoreBundleRestartTool_restart_eq]; simp only [hst_ne, ↓reduceIte]
        have hx_ord : (T.restart st x).ord = ord s := by
          dsimp only [T]; rw [sparseCoreBundleRestartTool_restart_ord]; exact hst_ord
        have hxf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify st [x]).2.2.2.2.1 j
        dsimp only [List.foldl] at hxf
        have hI_pre := hBs.2.2.2.2.2.2.2.1
        have hG_pre := hBs.2.2.2.2.2.2.2.2.1
        obtain ⟨ρ_s, hρ_s⟩ := orderedUpTo_rot_at hOrd hs hG_pre
        have hE_next : ∀ C ∈ components G₀, ∀ b : ℤ,
            (((T.restart st x).trees j).bun (C, b)).edges = (pre.bun (C, b)).edges := by
          intro C hC b
          dsimp only [T]; rw [sparseCoreBundleRestartTool_restart_eq]; simp only [hst_ne, ↓reduceIte]
          by_cases hjx : j = x
          · subst hjx; simp only [Function.update_self]
            dsimp only [restartBundleTree]
            split_ifs with hCA
            · dsimp only [restartBucketBundle]
              rw [hst_ord, hbf_st.cs, hbf_st.k, hE_st C hC b, initBundleFor_edges hI_pre hρ_s]
            · exact hE_st C hC b
          · simp only [Function.update_of_ne hjx]; exact hE_st C hC b
        refine ih (T.restart st x) hx_ne hx_ord ?_ (hxf.trans hbf_st) hE_next
        dsimp only [T]; rw [sparseCoreBundleRestartTool_restart_eq]; simp only [hst_ne, ↓reduceIte]
        by_cases hjx : j = x
        · subst hjx; simp only [Function.update_self]
          have hG₀_st : (st.trees j).cs.G₀ = G₀ := by
            rw [hbf_st.cs, hBs.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
          have hI_st : CompLSFInv C_lsst (D.ℓ 0) (st.trees j).cs := hbf_st.cs.symm ▸ hI_pre
          have hAct_st : (st.trees j).activeComps ⊆ components G₀ := by
            rw [hbf_st.activeComps]; exact hBs.2.2.2.2.2.2.2.2.2.1.2
          have hab_st : (st.trees j).activeBuckets = actB := hbf_st.activeBuckets.trans hBs.2.2.2.2.1
          have hBun_core : ∀ C ∈ components G₀, ∀ b ∈ actB C,
              ((st.trees j).bun (C, b)).edges ⊆ (coreGraph (st.trees j).cs.G (st.trees j).cs.lsf).E := by
            intro C hC b _
            rw [hE_st C hC b, hbf_st.cs]
            exact (((hBs.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1.1 ρ_s hI_pre.hG_val
              (compLSF_RF_isRSF hI_pre) hρ_s).1
          exact restartBundleTree_S_cur_spec (L := L) (sparsify := sparsify) (ord := st.ord)
            hG₀_st hI_st hAct_st hab_st hBun_core fun C hC b hb => by
              have hrb_eq : restartBucketBundle (st.trees j) st.ord C b =
                  initBundleState (coreRotation (L := pre.cs.lsf) ρ_s hI_pre.hG_val
                    (compLSF_RF_isRSF hI_pre)) (pre.bun (C, b)).edges k := by
                dsimp only [restartBucketBundle]
                rw [hst_ord, hbf_st.cs, hbf_st.k, hE_st C hC b, hBs.1, initBundleFor_eq hI_pre hρ_s]
              have hEc : (pre.bun (C, b)).edges ⊆ (coreGraph pre.cs.G pre.cs.lsf).E := by
                have := hBun_core C hC b hb; rwa [hE_st C hC b, hbf_st.cs] at this
              have hPart_r : (restartBucketBundle (st.trees j) st.ord C b).IsPartition
                  (coreRotation (L := pre.cs.lsf) ρ_s hI_pre.hG_val (compLSF_RF_isRSF hI_pre)) k := by
                rw [hrb_eq]
                exact initBundleState_inv _ (coreGraph_isValid hI_pre.hG_val (compLSF_RF_isRSF hI_pre)) hEc hk
              have hVal_r : (normGraph (restartBucketBundle (st.trees j) st.ord C b).graph).IsValid :=
                normGraph_isValid (BundleState.graph_isValid hPart_r)
              have hm_r : (normGraph (restartBucketBundle (st.trees j) st.ord C b).graph).m ≤ (st.trees j).m₀ := by
                rw [normGraph_m, hbf_st.m₀.trans hBs.2.1, hrb_eq]
                change (pre.bun (C, b)).edges.card ≤ M
                have hsub0 : (pre.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := by
                  rw [((hBs.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]; exact Finset.sdiff_subset
                have hsubG : (st₀.bun (C, b)).edges ⊆ G₀.E :=
                  (initBundleFor_edges_subset _ _ _ _).trans
                    ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
                exact le_trans (Finset.card_le_card (hsub0.trans hsubG)) hM
              have hq1 : 1 ≤ phaseBase ((normGraph (restartBucketBundle (st.trees j) st.ord C b).graph).n +
                  (st.trees j).splitBound) L := le_trans (by omega) (two_le_phaseBase _ L)
              have hm₀_eq : (st.trees j).m₀ = M := hbf_st.m₀.trans hBs.2.1
              have hinv0 := (DynSpanner.runInv_all hVal_r hL hq1 hm_r (hm₀_eq.symm ▸ hSp) (us := [])
                (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
              exact hinv0.H_sub.2.1
        · simp only [Function.update_of_ne hjx]; exact hst_inv
    exact hstep_fold (restarts s) (T.runOrdAfterUpdate k M N D ord restarts s).1 (hne_pre s)
      (hord_pre s) hpre (BundleBaseFieldsEq.refl _) (fun _ _ _ => rfl)
  intro t
  induction t with
  | zero =>
    intro ht
    have hpre0 : (T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j = st₀ := by
      dsimp only [T, SparseCoreRestartTool.runOrdAfterUpdate]
      exact sparseCoreBundleRestartTool_initOrd_trees lsfInit C_lsst L sparsify
        k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0) j
    have hpre_inv : ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).S_cur.IsValid ∧
        ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).S_cur.V =
          ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).cs.RF.R ∧
        ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).S_cur.E =
          (((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).activeComps.biUnion fun C =>
            (actB C).biUnion fun b =>
              (((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).dyn (C, b)).H.E) ∪
            (((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).activeComps.biUnion fun C =>
              ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).extraEdges C) ∪
            ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).cs.crossEdges ∧
        (coreGraph ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).cs.G
          ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).cs.lsf).IsSubgraph
          ((T.runOrdAfterUpdate k M N D ord restarts 0).1.trees j).S_cur := by
      rw [hpre0]
      obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (rfl : G₀ = D.G 0)
      have hRF₀ := compLSF_RF_isRSF hI₀
      set E₀ := st₀.activeComps.biUnion fun C => (actB C).biUnion fun b => (st₀.dyn (C, b)).H.E
      have hS₀ : st₀.S_cur = MGraph.mk st₀.cs.RF.R E₀ (coreGraph G₀ st₀.cs.lsf).tail
          (coreGraph G₀ st₀.cs.lsf).head := rfl
      have hSub_E : E₀ ⊆ st₀.cs.G.E \ st₀.cs.RF.F.E := by
        intro e he
        simp only [E₀, Finset.mem_biUnion] at he
        obtain ⟨C, hCA, b, _, heb⟩ := he
        have hEc : bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b ⊆
            (coreGraph G₀ st₀.cs.lsf).E := Finset.filter_subset _ _
        have hbun_eq : st₀.bun (C, b) = initBundleState
            (coreRotation (L := st₀.cs.lsf) ρ₀ hI₀.hG_val hRF₀)
            (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b) k :=
          initBundleFor_eq hI₀ hρ₀ _ k
        have hPart : (st₀.bun (C, b)).IsPartition
            (coreRotation (L := st₀.cs.lsf) ρ₀ hI₀.hG_val hRF₀) k := by
          rw [hbun_eq]
          exact initBundleState_inv _ (coreGraph_isValid hI₀.hG_val hRF₀) hEc hk
        have hVal := normGraph_isValid (BundleState.graph_isValid hPart)
        have hm_b : (normGraph (st₀.bun (C, b)).graph).m ≤ M :=
          le_trans (Finset.card_le_card ((initBundleFor_edges_subset _ _ _ _).trans
            (hEc.trans Finset.sdiff_subset))) hM
        have hq1 : 1 ≤ phaseBase ((normGraph (st₀.bun (C, b)).graph).n + bundleSplitBudget k M) L :=
          le_trans (by omega) (two_le_phaseBase _ L)
        have hinv0 := (DynSpanner.runInv_all hVal hL hq1 hm_b hSp (us := [])
          (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
        exact hPart.1 (hinv0.H_sub.2.1 heb)
      have hEx : (st₀.activeComps.biUnion fun C => st₀.extraEdges C) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he; rw [Finset.mem_biUnion] at he; obtain ⟨C, hCA, heC⟩ := he
        have h0 := initBundleTreeWith_extraEdges lsfInit L sparsify M N hk hG₀ hV₀ hℓ₀ j hInit hρ₀
          (largeComps_sub hCA)
        rw [h0] at heC; exact Finset.notMem_empty e heC
      have hX : st₀.cs.crossEdges = ∅ := rfl
      refine ⟨?_, rfl, ?_, ?_⟩
      · rw [hS₀]; intro e he
        have hth := hI₀.hG_val e (Finset.mem_sdiff.mp (hSub_E he)).1
        exact ⟨(LSF.rootedForest_root_spec hRF₀ hth.1).1, (LSF.rootedForest_root_spec hRF₀ hth.2).1⟩
      · rw [hEx, hX, Finset.union_empty, Finset.union_empty]; rfl
      · rw [hS₀]; exact ⟨Finset.Subset.rfl, hSub_E, fun _ _ => ⟨rfl, rfl⟩⟩
    exact ⟨hpre_inv, hRestart_pres 0 ht hpre_inv⟩
  | succ s ih =>
    intro hs1
    obtain ⟨_, hpost_s⟩ := ih (Nat.le_of_succ_le hs1)
    set s₀ := bundleLastRestart restarts j s
    have hs₀ := bundleLastRestart_spec restarts j s
    have hNoR : ∀ r, s₀ < r → r < s + 1 → j ∉ restarts r := fun r hr1 hr2 =>
      hs₀.2.2 r hr1 (Nat.le_of_lt_succ hr2)
    have hDyn_ep := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ (s + 1) j hInit
      (Nat.le_succ_of_le hs₀.1) hs1 hs₀.2.1 hNoR
    set st_ep := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ (s + 1) j
    have hpre_eq : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j =
        (stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).state := by
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne_post s), hord_post s]
    have hpre_st : (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j =
        st_ep (s + 1 - s₀) := by
      have := (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ (s + 1) j
        (Nat.le_succ_of_le hs₀.1)).2.2 (by omega)
      exact this.symm
    have hBs := hBun s (Nat.le_of_lt hs1)
    have hBs1 := hBun (s + 1) hs1
    have hbf_s : BundleBaseFieldsEq ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j) :=
      (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j
    have hI_s : CompLSFInv C_lsst (D.ℓ 0) ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).cs :=
      hbf_s.cs.symm ▸ hBs.2.2.2.2.2.2.2.1
    have hG_s : ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).cs.G = D.G s := by
      rw [hbf_s.cs, hBs.2.2.2.2.2.2.2.2.1]
    have hG₀_s : ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).cs.G₀ = G₀ := by
      rw [hbf_s.cs, hBs.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hDt := hD (s + 1) (Nat.succ_pos s) hs1
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).cs.G.BatchIsValid
        (D.U (s + 1)) := by rw [hG_s]; exact hDt.1
    obtain ⟨ρs, σs, hρs, hσs, hrots⟩ := orderedUpTo_rot_step hOrd hs1 hG_s
    have hBun_nil : D.U (s + 1) = [] → ∀ C ∈ components G₀, ∀ b : ℤ,
        (stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b) = [] ∧
        ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
          (D.U (s + 1)) (ord s) (ord (s + 1))).state.bun (C, b)).edges =
          (((T.runOrdAfterRestarts k M N D ord restarts s).trees j).bun (C, b)).edges := by
      intro hUnil C hC b
      have hk_s : ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).k = k :=
        hbf_s.k.trans hBs.1
      change (bundleCompStep _ _ _ _ _ _).1 = [] ∧ (bundleCompStep _ _ _ _ _ _).2.edges = _
      rw [hk_s]
      exact bundleCompStep_nil hUnil hI_s hG₀_s hC hBU ρs σs hρs hσs hrots
        ((hBs.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1
    have hsp := stepBundleTree_stage_step sparsify hI₀ rfl hCov₀
      ((T.runOrdAfterRestarts k M N D ord restarts s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
      actB (hbf_s.activeBuckets.trans hBs.2.2.2.2.1) hG₀_s hI_s
      (hbf_s.activeComps.symm ▸ hBs.2.2.2.2.2.2.2.2.2.1.2)
      (fun C hC => hbf_s.cs.symm ▸ (hBs.2.2.2.2.2.2.2.2.2.2.2 C hC).1)
      hBU ρs σs hρs hσs hrots hpost_s.1 hpost_s.2.1 hpost_s.2.2.1 hpost_s.2.2.2
      (fun C hC b _ => by
        have hd := (hDyn_ep C hC b).2.2.2.2.2.2.2.2.2.1 (s + 1 - s₀) le_rfl
        rw [← hpre_st, hpre_eq] at hd; exact hd.2.2.2.1.2.1)
      (fun C hC b _ => by
        have hd := (hDyn_ep C hC b).2.2.2.2.2.2.2.2.2.1 (s + 1 - s₀) le_rfl
        rw [← hpre_st, hpre_eq] at hd; rw [hd.2.1.2.1]; exact Finset.Subset.rfl)
      (fun C hC b _ => by
        rw [← hpre_eq]
        exact bundleCompReady_core_and_root hBs1.2.2.2.2.2.2.2.1
          (by rw [hBs1.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl) hC
          ((hBs1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
          ((hBs1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.1
          (orderedUpTo_rot_at hOrd hs1 hBs1.2.2.2.2.2.2.2.2.1))
      (fun hUnil C hC b _ => hBun_nil hUnil C hC b)
      (fun hUnil C hC b => by
        change DynSpanner.update _
          ((stepBundleTree sparsify ((T.runOrdAfterRestarts k M N D ord restarts s).trees j)
            (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b)) _ = _
        rw [(hBun_nil hUnil C hC b).1, update_nil])
    have hpre_inv : ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).S_cur.IsValid ∧
        ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).S_cur.V =
          ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.RF.R ∧
        ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).S_cur.E =
          (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).activeComps.biUnion fun C =>
            (actB C).biUnion fun b =>
              (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).dyn (C, b)).H.E) ∪
            (((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).activeComps.biUnion fun C =>
              ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).extraEdges C) ∪
            ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.crossEdges ∧
        (coreGraph ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.G
          ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).cs.lsf).IsSubgraph
          ((T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j).S_cur := by
      rw [hpre_eq]; exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1⟩
    exact ⟨hpre_inv, hRestart_pres (s + 1) hs1 hpre_inv⟩

/-! ## 3. Per-step specification and output batch length bound along an epoch -/

/-- Per-step `S_cur` update validity, `applyBatch`, empty-batch invariance, no-reinsert
propagation, `newlyActive` properties (including `n ≤ 11` for small components), and the
`stepBundleTree_US_len` recourse bound at every step `δ < t - s₀` of an epoch `[s₀, t]`. -/
theorem epochBundleSeq_step_spec
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀_rest : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    ∀ δ < t - s₀,
      let info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))
      (st δ).S_cur.BatchIsValid info.U_S ∧
      (st (δ + 1)).S_cur = (st δ).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + δ + 1) = [] → info.U_S = [] ∧ (st (δ + 1)).cost = (st δ).cost) ∧
      (∀ e ∈ (st δ).S_cur.E, e ∈ (st (δ + 1)).S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
        e ∉ info.D_total ∧ ∀ u ∈ D.U (s₀ + δ + 1), ¬ u.Inserts e) ∧
      (info.newlyActive = touchedCompsBatch (st δ).cs (D.U (s₀ + δ + 1)) \ (st δ).activeComps ∧
        Disjoint (st δ).activeComps info.newlyActive ∧
        (st (δ + 1)).activeComps = (st δ).activeComps ∪ info.newlyActive ∧
        info.newlyActive ⊆ components (D.G 0) \ largeComps k (D.G 0) ∧
        info.newlyActive.card ≤ 2 * (D.U (s₀ + δ + 1)).length ∧
        (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st δ).dyn (C, b)).G.n ≤ 11)) ∧
      info.U_S.length ≤
        ((st (δ + 1)).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        (info.newlyActive.sum fun C => (st₀.activeBuckets C).sum fun b =>
          ((st δ).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + δ + 1)).length +
        2 * ((st (δ + 1)).cs.RF.R \ (st δ).cs.RF.R).card +
        2 * info.D_total.card := by
  intro st₀ st δ hδ info
  set T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  set G₀ := D.G 0
  set actB := st₀.activeBuckets
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀_rest hNoRest
  have hSt_step := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).2 δ hδ
  have hEp := epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j hst
  have hδ_eq : st δ = (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j := hEp.1 δ hδ
  have hδ1_eq : st (δ + 1) = info.state := hSt_step.1
  have hbf_δ : BundleBaseFieldsEq ((T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j)
      ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1.trees j) :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1 (restarts (s₀ + δ))).2.2.2.2.1 j
  have hBδ := hBun (s₀ + δ) (by omega)
  have hBδ1 := hBun (s₀ + δ + 1) (by omega)
  have hSc_δ := (hSc (s₀ + δ) (by omega)).2
  have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCov₀ : ∀ C ∈ components G₀,
      (st₀.cs.compSt C).W_init.biUnion (inducedEdges (st₀.cs.compSt C).RF.F) =
        (st₀.cs.compSt C).RF.F.E :=
    fun C hC => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC).2.2
  have hI_δ : CompLSFInv C_lsst (D.ℓ 0) (st δ).cs := by
    rw [hδ_eq, hbf_δ.cs]; exact hBδ.2.2.2.2.2.2.2.1
  have hG_δ : (st δ).cs.G = D.G (s₀ + δ) := by
    rw [hδ_eq, hbf_δ.cs, hBδ.2.2.2.2.2.2.2.2.1]
  have hG₀_δ : (st δ).cs.G₀ = G₀ := by
    rw [hδ_eq, hbf_δ.cs, hBδ.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hAct_δ : (st δ).activeComps ⊆ components G₀ := by
    rw [hδ_eq, hbf_δ.activeComps]; exact hBδ.2.2.2.2.2.2.2.2.2.1.2
  have hLarge_δ : largeComps k G₀ ⊆ (st δ).activeComps := by
    rw [hδ_eq, hbf_δ.activeComps]; exact hBδ.2.2.2.2.2.2.2.2.2.1.1
  have hAB_δ : (st δ).activeBuckets = actB := by
    rw [hδ_eq, hbf_δ.activeBuckets, hBδ.2.2.2.2.1]
  have hDt := hD (s₀ + δ + 1) (Nat.succ_pos _) (by omega)
  simp only [Nat.add_sub_cancel] at hDt
  have hBU : (st δ).cs.G.BatchIsValid (D.U (s₀ + δ + 1)) := by rw [hG_δ]; exact hDt.1
  obtain ⟨ρδ, σδ, hρδ, hσδ, hrotδ⟩ := orderedUpTo_rot_step hOrd (by omega : s₀ + δ < τ) hG_δ
  have hPre_eq : st (δ + 1) = (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ + 1)).1.trees j := by
    have hne_δ : (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts (s₀ + δ)).2.1.trans
        (decide_eq_true hV₀)
    have hord_δ : (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).ord = ord (s₀ + δ) :=
      ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts
        (s₀ + δ)).2.2.2.2 hV₀).2
    rw [hδ1_eq, T.runOrdAfterUpdate_succ]
    dsimp only [T, info]
    rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_δ, hord_δ, hδ_eq]
  have hBun_nil : D.U (s₀ + δ + 1) = [] → ∀ C ∈ components G₀, ∀ b : ℤ,
      info.U_B (C, b) = [] ∧ (info.state.bun (C, b)).edges = ((st δ).bun (C, b)).edges := by
    intro hUnil C hC b
    have hk_δ : (st δ).k = k := by rw [hδ_eq, hbf_δ.k, hBδ.1]
    change (bundleCompStep _ _ _ _ _ _).1 = [] ∧ (bundleCompStep _ _ _ _ _ _).2.edges = _
    rw [hk_δ]
    exact bundleCompStep_nil hUnil hI_δ hG₀_δ hC hBU ρδ σδ hρδ hσδ hrotδ
      (hδ_eq.symm ▸ ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1)
  have hsp := stepBundleTree_stage_step sparsify hI₀ rfl hCov₀
    (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1)) actB hAB_δ hG₀_δ hI_δ hAct_δ
    (fun C hC => by rw [hδ_eq, hbf_δ.cs]; exact (hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).1)
    hBU ρδ σδ hρδ hσδ hrotδ (hδ_eq.symm ▸ hSc_δ.1) (hδ_eq.symm ▸ hSc_δ.2.1)
    (hδ_eq.symm ▸ hSc_δ.2.2.1) (hδ_eq.symm ▸ hSc_δ.2.2.2)
    (fun C hC b _ => by
      have hd := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 (δ + 1) hδ
      have hsub : ((st (δ + 1)).dyn (C, b)).H.E ⊆ ((st (δ + 1)).dyn (C, b)).G.E := hd.2.2.2.1.2.1
      rwa [hδ1_eq] at hsub)
    (fun C hC b _ => by
      have hd := (hDyn C hC b).2.2.2.2.2.2.2.2.2.1 (δ + 1) hδ
      have hGeq : GraphEq ((st (δ + 1)).dyn (C, b)).G ((st (δ + 1)).bun (C, b)).graph := hd.2.1
      rw [hδ1_eq] at hGeq; rw [hGeq.2.1]; exact Finset.Subset.rfl)
    (fun C hC b _ => by
      change ∀ e ∈ (info.state.bun (C, b)).edges, _
      rw [← hδ1_eq, hPre_eq]
      exact bundleCompReady_core_and_root hBδ1.2.2.2.2.2.2.2.1
        (by rw [hBδ1.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl) hC
        ((hBδ1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
        ((hBδ1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.1
        (orderedUpTo_rot_at hOrd (by omega) hBδ1.2.2.2.2.2.2.2.2.1))
    (fun hUnil C hC b _ => hBun_nil hUnil C hC b)
    (fun hUnil C hC b => by
      change DynSpanner.update _ (info.U_B (C, b)) _ = _
      rw [(hBun_nil hUnil C hC b).1, update_nil])
  have hUnt : ∀ C ∈ components G₀, C ∉ (st δ).activeComps → (st δ).extraEdges C = ∅ := by
    intro C hC hna
    have hna' : C ∉ ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1.trees j).activeComps := by
      rw [hδ_eq, hbf_δ.activeComps] at hna; exact hna
    have hunt := hBδ.2.2.2.2.2.2.2.2.2.2.1 C hC hna'
    obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (rfl : G₀ = D.G 0)
    have hEx0 := initBundleTreeWith_extraEdges lsfInit L sparsify M N hk hG₀ hV₀ hℓ₀ j hInit hρ₀ hC
    unfold BundleTreeState.extraEdges at hEx0 ⊢
    rw [hAB_δ, show ((st δ).cs.compSt C) = st₀.cs.compSt C by rw [hδ_eq, hbf_δ.cs]; exact hunt.1]
    have hbi : (actB C).biUnion (fun b => ((st δ).bun (C, b)).edges) =
        (actB C).biUnion (fun b => (st₀.bun (C, b)).edges) :=
      Finset.biUnion_congr rfl fun b _ => by rw [hδ_eq, (hunt.2 b).2.2.1]
    rw [hbi]; exact hEx0
  have hDyn_UH : ∀ C ∈ info.state.activeComps, ∀ b ∈ actB C,
      ((st δ).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (info.state.dyn (C, b)).H := by
    intro C hCA b _
    have hC : C ∈ components G₀ := by
      rcases Finset.mem_union.mp hCA with h1 | h2
      · exact hAct_δ h1
      · exact hG₀_δ ▸ (Finset.mem_filter.mp (Finset.mem_sdiff.mp h2).1).1
    have hDc := hDyn C hC b
    have hHb_val : (normGraph ((st 0).bun (C, b)).graph).IsValid := normGraph_isValid hDc.1
    have hHb_mM : (normGraph ((st 0).bun (C, b)).graph).m ≤ M := le_trans hDc.2.1 hM
    have hq1 : 1 ≤ phaseBase (((st 0).bun (C, b)).graph.n + bundleSplitBudget k M) L :=
      le_trans (by omega) (two_le_phaseBase _ L)
    set Us_ep : List (List Update) := (List.range (t - s₀)).map fun r =>
      (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
    have hBV_n : (normGraph ((st 0).bun (C, b)).graph).BatchIsValid Us_ep.flatten :=
      (graphEq_batchIsValid (graphEq_symm (normGraph_graphEq _)) _).mp hDc.2.2.2.2.2.1
    have hTr := (DynSpanner.batchTrace_spec hHb_val hL hq1 hHb_mM hSp hBV_n
      hDc.2.2.2.2.2.2.1).2 δ (by simp [Us_ep]; exact hδ) (info.U_B (C, b))
      (by dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hδ]; rfl)
    dsimp only at hTr
    have hst_δ := (hDc.2.2.2.2.2.2.2.2.2.1 δ hδ.le).1
    have hso_δ := (hDc.2.2.2.2.2.2.2.2.2.2 δ hδ).1
    rw [← hst_δ, ← hso_δ] at hTr
    exact hTr.2.2.2.1
  have hLen := stepBundleTree_US_len sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ))
    (ord (s₀ + δ + 1)) actB hAB_δ hG₀_δ hI_δ hAct_δ hUnt hBU
    (hδ_eq.symm ▸ hSc_δ.2.2.1) hsp.2.2.1 hsp.2.2.2.2.2.2.2.2 hDyn_UH
    (fun C hC b _ => by
      have hst_b : ((st δ).bun (C, b)).edges \ ((st (δ + 1)).bun (C, b)).edges ⊆
          batchDeletes (D.U (s₀ + δ + 1)) :=
        ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 δ hδ).2.2.2.2.2.1
      rw [hδ1_eq] at hst_b
      refine ⟨fun e he => by
        by_contra hnot
        have hsub0 : ((st (δ + 1)).bun (C, b)).edges ⊆ ((st δ).bun (C, b)).edges := by
          rw [hPre_eq, ((hBδ1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1,
            hδ_eq, ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1,
            ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]
          exact Finset.sdiff_subset_sdiff Finset.Subset.rfl
            (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.Icc_subset_Icc le_rfl (by omega)))
        rw [hδ1_eq] at hsub0; exact hnot (hsub0 he), hst_b⟩)
  have hNew_sub : info.newlyActive ⊆ components G₀ \ largeComps k G₀ := by
    intro C hC
    obtain ⟨ht, hna⟩ := Finset.mem_sdiff.mp hC
    exact Finset.mem_sdiff.mpr ⟨hG₀_δ ▸ (Finset.mem_filter.mp ht).1, fun hL => hna (hLarge_δ hL)⟩
  have hNew_card : info.newlyActive.card ≤ 2 * (D.U (s₀ + δ + 1)).length :=
    (Finset.card_le_card Finset.sdiff_subset).trans (touchedCompsBatch_card_le hI_δ hBU)
  have hNew_small : ∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st δ).dyn (C, b)).G.n ≤ 11 := by
    intro C hCA b
    have hCm := Finset.mem_sdiff.mp (hNew_sub hCA)
    have hna : C ∉ (st δ).activeComps := (Finset.mem_sdiff.mp hCA).2
    have hna' : C ∉ ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1.trees j).activeComps := by
      rw [hδ_eq, hbf_δ.activeComps] at hna; exact hna
    have hbun0 : (st δ).bun (C, b) = st₀.bun (C, b) :=
      hδ_eq ▸ ((hBδ.2.2.2.2.2.2.2.2.2.2.1 C hCm.1 hna').2 b).2.2.1
    have hdynG : GraphEq ((st δ).dyn (C, b)).G ((st δ).bun (C, b)).graph :=
      hδ_eq ▸ ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hCm.1).2 b).2.2.2.2.2.2
    rw [graphEq_n hdynG, hbun0]
    exact (initBundleTreeWith_vertex_sum_le lsfInit C_lsst L sparsify k M N hk G₀ hG₀ hV₀
      (D.ℓ 0) hℓ₀ (ord 0) j hInit (G₀.m) (fun _ _ =>
        le_trans (Finset.card_image_le)
          (le_trans (Finset.card_le_card (Finset.filter_subset _ _))
            (Finset.card_le_card Finset.sdiff_subset)))).2.1 C hCm.1 hCm.2 b
  rw [hδ1_eq]
  exact ⟨hsp.2.2.2.2.1, hsp.2.2.2.2.2.1, hsp.2.2.2.2.2.2.1, hsp.2.2.2.2.2.2.2.1,
    ⟨rfl, Finset.disjoint_sdiff, rfl, hNew_sub, hNew_card, hNew_small⟩, hLen⟩

end MinCostFlow.Chain

end
