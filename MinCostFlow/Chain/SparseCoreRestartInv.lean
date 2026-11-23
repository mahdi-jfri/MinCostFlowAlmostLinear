module

public import MinCostFlow.Chain.SparseCoreRestart
import MinCostFlow.Chain.SparseCoreRestartDyn
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `S_cur` invariant and three restart obligations

`runAfterRestarts_S_cur_inv`, and the obligations `ToolEmbedsSurvivingRestart`,
`ToolMWURestart` and `ToolNoReinsertRestart` for `sparseCoreRestartTool`. Split out of
`SparseCoreRestart.lean` to keep files short.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF

/-- Global `S_cur` invariant along `runAfterRestarts` (requiring only `hLSST`, `1 ≤ L`, and
`hSp`, with no `hThresh` or `hDeg_bound`). -/
lemma runAfterRestarts_S_cur_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (j : ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let G₀ := D.G 0
    let cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let actB := fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    ∀ t ≤ τ,
      let pre := (T.runAfterUpdate k M N D restarts t).1.trees j
      let post := (T.runAfterRestarts k M N D restarts t).trees j
      (pre.S_cur.IsValid ∧ pre.S_cur.V = pre.cs.RF.R ∧
        pre.S_cur.E =
          (pre.activeComps.biUnion fun C => (actB C).biUnion fun b => (pre.dyn (C, b)).H.E) ∪
            (pre.activeComps.biUnion fun C => extraSet (pre.cs.compSt C) (pre.ts C)) ∪
            pre.cs.crossEdges ∧
        (coreGraph pre.cs.G pre.cs.lsf).IsSubgraph pre.S_cur) ∧
      (post.S_cur.IsValid ∧ post.S_cur.V = post.cs.RF.R ∧
        post.S_cur.E =
          (post.activeComps.biUnion fun C => (actB C).biUnion fun b => (post.dyn (C, b)).H.E) ∪
            (post.activeComps.biUnion fun C => extraSet (post.cs.compSt C) (post.ts C)) ∪
            post.cs.crossEdges ∧
        (coreGraph post.cs.G post.cs.lsf).IsSubgraph post.S_cur) := by
  intro T G₀ cs₀ ts₀ actB
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => initLSF_cov0 oracle C_lsst hk hG₀ hℓ₀ hC hLSST
  have hne : ∀ s, (T.runAfterRestarts k M N D restarts s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hRestart_pres : ∀ s ≤ τ,
      let pre := (T.runAfterUpdate k M N D restarts s).1.trees j
      (pre.S_cur.IsValid ∧ pre.S_cur.V = pre.cs.RF.R ∧
        pre.S_cur.E =
          (pre.activeComps.biUnion fun C => (actB C).biUnion fun b => (pre.dyn (C, b)).H.E) ∪
            (pre.activeComps.biUnion fun C => extraSet (pre.cs.compSt C) (pre.ts C)) ∪
            pre.cs.crossEdges ∧
        (coreGraph pre.cs.G pre.cs.lsf).IsSubgraph pre.S_cur) →
      let post := (T.runAfterRestarts k M N D restarts s).trees j
      post.S_cur.IsValid ∧ post.S_cur.V = post.cs.RF.R ∧
        post.S_cur.E =
          (post.activeComps.biUnion fun C => (actB C).biUnion fun b => (post.dyn (C, b)).H.E) ∪
            (post.activeComps.biUnion fun C => extraSet (post.cs.compSt C) (post.ts C)) ∪
            post.cs.crossEdges ∧
        (coreGraph post.cs.G post.cs.lsf).IsSubgraph post.S_cur := by
    intro s hs pre hpre post
    by_cases hj_s : j ∈ restarts s
    · have hp_s := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j s
      have hb_s := hBase s hs
      have hne_pre : (T.runAfterUpdate k M N D restarts s).1.isNonempty = true :=
        (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).1.trans
          (decide_eq_true hV₀)
      have hAct_sub : pre.activeComps ⊆ components G₀ := by
        rw [hp_s.1.activeComps]; exact hb_s.2.2.2.2.2.2.2.2.2.2.1.2
      have hT_pre : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (pre.cs.compSt C) (pre.ts C) := by
        intro C hC
        rw [hp_s.1.cs, hp_s.1.ts]
        exact (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
      have hstep_fold : ∀ (xs : List ℕ) (st : SparseCoreState L),
          st.isNonempty = true →
          (st.trees j).S_cur.IsValid ∧ (st.trees j).S_cur.V = (st.trees j).cs.RF.R ∧
          (st.trees j).S_cur.E =
            ((st.trees j).activeComps.biUnion fun C => (actB C).biUnion fun b =>
              ((st.trees j).dyn (C, b)).H.E) ∪
              ((st.trees j).activeComps.biUnion fun C =>
                extraSet ((st.trees j).cs.compSt C) ((st.trees j).ts C)) ∪
              (st.trees j).cs.crossEdges ∧
          (coreGraph (st.trees j).cs.G (st.trees j).cs.lsf).IsSubgraph (st.trees j).S_cur →
          (st.trees j).cs = pre.cs → (st.trees j).ts = pre.ts →
          (st.trees j).activeComps = pre.activeComps → (st.trees j).m₀ = M →
          (st.trees j).origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e)) →
          (st.trees j).activeBuckets = actB →
          let tr := (xs.foldl T.restart st).trees j
          tr.S_cur.IsValid ∧ tr.S_cur.V = tr.cs.RF.R ∧
          tr.S_cur.E =
            (tr.activeComps.biUnion fun C => (actB C).biUnion fun b => (tr.dyn (C, b)).H.E) ∪
              (tr.activeComps.biUnion fun C => extraSet (tr.cs.compSt C) (tr.ts C)) ∪
              tr.cs.crossEdges ∧
          (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
        intro xs st hst_ne hst_inv hcs_st hts_st hact_st hm₀_st hob_st hab_st
        induction xs generalizing st with
        | nil => exact hst_inv
        | cons x xs ih =>
          dsimp only [List.foldl_cons]
          have hx_ne : (T.restart st x).isNonempty = true := by
            dsimp only [T]
            rw [sparseCoreRestartTool_restart_eq]
            simp only [hst_ne, ↓reduceIte]
          have hxf := (foldl_restart_props oracle C_lsst L sparsify st [x]).2.2.2.1 j
          dsimp only [List.foldl] at hxf
          refine ih (T.restart st x) hx_ne ?_ (hxf.cs.trans hcs_st)
            (hxf.ts.trans hts_st) (hxf.activeComps.trans hact_st)
            (hxf.m₀.trans hm₀_st) (hxf.origBucket.trans hob_st)
            (hxf.activeBuckets.trans hab_st)
          dsimp only [T]
          rw [sparseCoreRestartTool_restart_eq]
          simp only [hst_ne, ↓reduceIte]
          by_cases hjx : j = x
          · subst hjx
            simp only [Function.update_self]
            have hG₀_st : (st.trees j).cs.G₀ = G₀ := by
              rw [hcs_st, hp_s.1.cs, hb_s.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
            have hI_st : CompLSFInv C_lsst (D.ℓ 0) (st.trees j).cs := by
              rw [hcs_st, hp_s.1.cs]; exact hb_s.2.2.2.2.2.2.2.2.1
            have hT_st : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C)
                ((st.trees j).cs.compSt C) ((st.trees j).ts C) := by
              rw [hcs_st, hts_st]; exact hT_pre
            exact restartTreeCore_S_cur_spec hG₀_st hI_st (hact_st ▸ hAct_sub) hT_st hab_st
              fun C hC b _ => by
                have hRsp := activeSubgraph_rawBucket_spec (hT_st C hC).hC_val
                  (st.trees j).origBucket b
                have hm_hb : (restartBucketGraph (st.trees j) C b).m ≤ (st.trees j).m₀ := by
                  rw [hm₀_st]
                  have hTs_sub : ((st.trees j).ts C).C.E ⊆ (ts₀ C).C.E := by
                    rw [hts_st, hp_s.1.ts]
                    exact (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1
                  have hE_sub : (restartBucketGraph (st.trees j) C b).E ⊆
                      (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).E := by
                    intro e he
                    dsimp only [restartBucketGraph] at he
                    rw [hRsp.2.2.1, Finset.mem_filter] at he
                    rw [initBucketGraph, rawBucket]
                    dsimp only [activeSubgraph]
                    rw [Finset.mem_filter]
                    refine ⟨hTs_sub he.1, ?_⟩
                    dsimp only [cs₀] at hob_st ⊢
                    rw [← initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e
                      (hTs_sub he.1),
                      ← initCompLSF_safeLen_origBucket_eq oracle C_lsst hk hG₀ hV₀ hℓ₀ hC hLSST
                        (hTs_sub he.1)]
                    exact (congrFun hob_st e).symm ▸ he.2
                  have hm1 : (restartBucketGraph (st.trees j) C b).m ≤
                      (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m :=
                    Finset.card_le_card hE_sub
                  have hm2 : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m ≤ (cs₀.compSt C).G.m :=
                    (initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b).2.2.2.2.2.2.2.1
                  have hmc : (cs₀.compSt C).G.m ≤ G₀.m := by
                    rw [(initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.1]
                    exact compGraph_m_le
                  exact le_trans (le_trans (le_trans hm1 hm2) hmc) hM
                have hq1 : 1 ≤ phaseBase
                    ((restartBucketGraph (st.trees j) C b).n + (st.trees j).splitBound) L :=
                  le_trans (by omega) (two_le_phaseBase _ L)
                have hinv0 := (DynSpanner.runInv_all hRsp.1 hL hq1 hm_hb (hm₀_st.symm ▸ hSp) (us := [])
                  (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
                have hsub0 : (restartBucketGraph (st.trees j) C b).IsSubgraph
                    (DynSpanner.init (restartBucketGraph (st.trees j) C b) L
                      (phaseBase ((restartBucketGraph (st.trees j) C b).n + (st.trees j).splitBound) L)
                      (sparsify (st.trees j).m₀)).state.H := hinv0.H_sub
                exact hsub0.2.1
          · simp only [Function.update_of_ne hjx]; exact hst_inv
      exact hstep_fold (restarts s) (T.runAfterUpdate k M N D restarts s).1 hne_pre hpre
        rfl rfl rfl (hp_s.1.m₀.trans hb_s.1) (hp_s.1.origBucket.trans hb_s.2.2.2.2.1)
        (hp_s.1.activeBuckets.trans hb_s.2.2.2.2.2.1)
    · have hni := (foldl_restart_props oracle C_lsst L sparsify
        (T.runAfterUpdate k M N D restarts s).1 (restarts s)).2.2.2.2 j hj_s
      change ((restarts s).foldl T.restart (T.runAfterUpdate k M N D restarts s).1 |>.trees j) = pre at hni
      rw [show post = (T.runAfterRestarts k M N D restarts s).trees j from rfl]
      simpa only [SparseCoreRestartTool.runAfterRestarts, hni] using hpre
  intro t
  induction t with
  | zero =>
    intro ht
    have hpre0 : (T.runAfterUpdate k M N D restarts 0).1.trees j =
        (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1 := by
      dsimp only [T, SparseCoreRestartTool.runAfterUpdate, treeRunSeq, treeRunSeqWith]
      exact sparseCoreRestartTool_init_trees oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) (D.g 0) j
    have hpre_inv : ((T.runAfterUpdate k M N D restarts 0).1.trees j).S_cur.IsValid ∧
        ((T.runAfterUpdate k M N D restarts 0).1.trees j).S_cur.V =
          ((T.runAfterUpdate k M N D restarts 0).1.trees j).cs.RF.R ∧
        ((T.runAfterUpdate k M N D restarts 0).1.trees j).S_cur.E =
          (((T.runAfterUpdate k M N D restarts 0).1.trees j).activeComps.biUnion fun C =>
            (actB C).biUnion fun b =>
              (((T.runAfterUpdate k M N D restarts 0).1.trees j).dyn (C, b)).H.E) ∪
            (((T.runAfterUpdate k M N D restarts 0).1.trees j).activeComps.biUnion fun C =>
              extraSet (((T.runAfterUpdate k M N D restarts 0).1.trees j).cs.compSt C)
                (((T.runAfterUpdate k M N D restarts 0).1.trees j).ts C)) ∪
            ((T.runAfterUpdate k M N D restarts 0).1.trees j).cs.crossEdges ∧
        (coreGraph ((T.runAfterUpdate k M N D restarts 0).1.trees j).cs.G
          ((T.runAfterUpdate k M N D restarts 0).1.trees j).cs.lsf).IsSubgraph
          ((T.runAfterUpdate k M N D restarts 0).1.trees j).S_cur := by
      rw [hpre0]
      dsimp only [treeRunSeq, treeRunSeqWith, initTreeCore]
      have hRF₀ := compLSF_RF_isRSF hI₀
      have hT₀ : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (cs₀.compSt C) (ts₀ C) :=
        fun C hC => initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
      set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
        Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      have hSub_E : (largeComps k G₀).biUnion (fun C => (actB C).biUnion fun b =>
          (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
            (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n + splitB) L)
            (sparsify M)).state.H.E) ⊆
          cs₀.G.E \ cs₀.RF.F.E := by
        intro e he
        rw [Finset.mem_biUnion] at he
        rcases he with ⟨C, hCL, heB⟩
        rw [Finset.mem_biUnion] at heB
        rcases heB with ⟨b, _, heb⟩
        have hC := largeComps_sub hCL
        have hHb := initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
        have hmc : (cs₀.compSt C).G.m ≤ G₀.m := by
          rw [(initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.1]
          exact compGraph_m_le
        have hGm_b : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m ≤ M :=
          le_trans (le_trans hHb.2.2.2.2.2.2.2.1 hmc) hM
        have hq1 : 1 ≤ phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n + splitB) L :=
          le_trans (by omega) (two_le_phaseBase _ L)
        have hinv0 := (DynSpanner.runInv_all hHb.1 hL hq1 hGm_b hSp (us := [])
          (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
        have hsub0 : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).IsSubgraph
            (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
              (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n + splitB) L)
              (sparsify M)).state.H := hinv0.H_sub
        have heHb := hsub0.2.1 heb
        exact compLSF_comp_sdiff_sub hI₀ hC ((hT₀ C hC).hCE_sub (hHb.2.1.2.1 heHb))
      set E₀ := (largeComps k G₀).biUnion fun C => (actB C).biUnion fun b =>
        (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
          (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n + splitB) L)
          (sparsify M)).state.H.E
      have hVal : (MGraph.mk cs₀.RF.R E₀
          (coreGraph G₀ cs₀.lsf).tail (coreGraph G₀ cs₀.lsf).head).IsValid := by
        intro e he
        have heG := (Finset.mem_sdiff.mp (hSub_E he)).1
        have hth := hI₀.hG_val e heG
        dsimp only [coreGraph]
        exact ⟨(root_mem_R hRF₀ hth.1).1, (root_mem_R hRF₀ hth.2).1⟩
      have hSubC : (coreGraph cs₀.G cs₀.lsf).IsSubgraph
          (MGraph.mk cs₀.RF.R E₀ (coreGraph G₀ cs₀.lsf).tail (coreGraph G₀ cs₀.lsf).head) := by
        refine ⟨Finset.Subset.rfl, hSub_E, fun _ _ => ?_⟩
        dsimp only [coreGraph]; exact ⟨rfl, rfl⟩
      have hEx_empty : (largeComps k G₀).biUnion (fun C =>
          extraSet (cs₀.compSt C) (ts₀ C)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he; rw [Finset.mem_biUnion] at he; rcases he with ⟨C, _, heC⟩
        rw [extraSet_init] at heC; exact Finset.notMem_empty e heC
      have hX_empty : cs₀.crossEdges = ∅ := rfl
      have hAB₀ : (fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e))) =
          actB := (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.1
      have hS₀_E :
          ((largeComps k G₀).biUnion fun C =>
            ((ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e))).biUnion fun b =>
              (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
                (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n + splitB) L)
                (sparsify M)).state.H.E) = E₀ :=
        Finset.biUnion_congr rfl fun C _ => by rw [congrFun hAB₀ C]
      refine ⟨hS₀_E.symm ▸ hVal, rfl, ?_, hS₀_E.symm ▸ hSubC⟩
      change _ = E₀ ∪ (largeComps k G₀).biUnion (fun C => extraSet (cs₀.compSt C) (ts₀ C)) ∪
        cs₀.crossEdges
      rw [hS₀_E, hEx_empty, hX_empty, Finset.union_empty, Finset.union_empty]
    exact ⟨hpre_inv, hRestart_pres 0 ht hpre_inv⟩
  | succ s ih =>
    intro hs1
    obtain ⟨_, hpost_s⟩ := ih (Nat.le_of_succ_le hs1)
    set s₀ := lastRestart restarts j s
    have hs₀ := lastRestart_spec restarts j s
    have hNoR : ∀ r, s₀ < r → r < s + 1 → j ∉ restarts r := fun r hr1 hr2 =>
      hs₀.2.2 r hr1 (Nat.le_of_lt_succ hr2)
    have hDyn_ep := epochTreeSeq_dyn_spec oracle C_lsst L hL P_b sparsify hLSST
      k M N τ hk D restarts hM hN hSp hG₀ hV₀ hℓ₀ hD s₀ (s + 1) j (Nat.le_succ_of_le hs₀.1) hs1
      hs₀.2.1 hNoR
    set st_ep := epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ (s + 1) j
    have hpre_eq : (T.runAfterUpdate k M N D restarts (s + 1)).1.trees j =
        (stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
          (D.U (s + 1))).state := by
      rw [T.runAfterUpdate_succ]
      dsimp only [T]
      rw [sparseCoreRestartTool_update_of_nonempty (hne s)]
    have hpost_st : (T.runAfterRestarts k M N D restarts s).trees j = st_ep (s - s₀) := by
      dsimp only [st_ep, epochTreeSeq]
      split_ifs with hc
      · omega
      · rw [show s₀ + (s - s₀) = s by omega]
    have hpre_st : (T.runAfterUpdate k M N D restarts (s + 1)).1.trees j = st_ep (s + 1 - s₀) := by
      dsimp only [st_ep, epochTreeSeq]
      rw [show s₀ + (s + 1 - s₀) = s + 1 by omega]
      split_ifs with hc
      · rfl
      · omega
    have hb_s := hBase s (Nat.le_of_lt hs1)
    have hb_s1 := hBase (s + 1) hs1
    have hp_s := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j s
    have hp_s1 := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j (s + 1)
    have hsp := stepTreeCoreAux_stage_stepWith true sparsify hI₀ rfl hCov₀
      ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1)) actB
      (hp_s.2.activeBuckets.trans hb_s.2.2.2.2.2.1)
      (by rw [hp_s.2.cs, hb_s.2.2.2.2.2.2.2.1, compLSFBatch_G₀])
      (by rw [hp_s.2.cs]; exact hb_s.2.2.2.2.2.2.2.2.1)
      (by rw [hp_s.2.activeComps]; exact hb_s.2.2.2.2.2.2.2.2.2.2.1.2)
      (fun C hC hna => by
        rw [hp_s.2.cs, hp_s.2.ts]
        exact hb_s.2.2.2.2.2.2.2.2.2.2.2.1 C hC (hp_s.2.activeComps ▸ hna))
      (fun C hC => by rw [hp_s.2.cs]; exact (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1)
      (fun C hC => by rw [hp_s.2.cs, hp_s.2.ts]; exact (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1)
      (by rw [hp_s.2.cs]; exact (hStep s hs1).1)
      hpost_s.1 hpost_s.2.1 hpost_s.2.2.1 hpost_s.2.2.2
      (fun C hC b _ => by
        have hd := (hDyn_ep C hC b).2.2.2.2.2.2.2.1 (s + 1 - s₀) (by omega)
        rw [← hpre_st, hpre_eq] at hd
        exact hd.2.2.1.2.1)
      (fun C hC b _ => by
        have hd := (hDyn_ep C hC b).2.2.2.2.2.2.2.1 (s + 1 - s₀) (by omega)
        rw [← hpre_st, hpre_eq] at hd
        have he1 := hd.2.2.2.1
        have hob1 : ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).origBucket =
            fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e) :=
          hp_s1.1.origBucket.trans hb_s1.2.2.2.2.1
        rw [hpre_eq] at hob1
        rw [hob1] at he1
        exact fun e he => (Finset.mem_filter.mp (he1 ▸ he)).1)
      (fun hUnil C _ b => by
        have hUb : (stepTreeCoreAuxWith true sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
            (D.U (s + 1))).U_b (C, b) = [] := by
          dsimp only [stepTreeCoreAuxWith]; rw [hUnil]; rfl
        dsimp only [stepTreeCoreAuxWith] at hUb ⊢
        simp [hUb, update_nil])
    have hpre_inv : ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).S_cur.IsValid ∧
        ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).S_cur.V =
          ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).cs.RF.R ∧
        ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).S_cur.E =
          (((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).activeComps.biUnion fun C =>
            (actB C).biUnion fun b =>
              (((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).dyn (C, b)).H.E) ∪
            (((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).activeComps.biUnion fun C =>
              extraSet (((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).cs.compSt C)
                (((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).ts C)) ∪
            ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).cs.crossEdges ∧
        (coreGraph ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).cs.G
          ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).cs.lsf).IsSubgraph
          ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j).S_cur := by
      rw [hpre_eq]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1⟩
    exact ⟨hpre_inv, hRestart_pres (s + 1) hs1 hpre_inv⟩

/-! ## 2. Restart Tool Side Properties (`ToolEmbedsSurvivingRestart`, `ToolMWURestart`, `ToolNoReinsertRestart`) -/

/-- **Unconditional** `ToolEmbedsSurvivingRestart` for `sparseCoreRestartTool`:
every surviving edge in `T.S (post t) j` embeds as `[(e, true)]`. -/
theorem sparseCoreRestartTool_embedsSurvivingRestart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).ToolEmbedsSurvivingRestart := by
  intro k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh t ht j hj e he
  rw [sparseCoreRestartTool_S_eq] at he
  split_ifs at he with hne
  · rw [sparseCoreRestartTool_emb_eq]
    simp only [hne, ↓reduceIte]
    dsimp only [TreeCoreState.emb]
    simp only [he, ↓reduceIte]
  · simp [emptyGraph] at he

/-- `ToolMWURestart` for `sparseCoreRestartTool` under `hLSST` and polynomial edge density
`(D.G 0).m + 2 ≤ ((D.G 0).n + 2)^μ`. -/
theorem sparseCoreRestartTool_toolMWURestart (C_lsst : ℝ) (L μ : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} {D : DynamicInstance} (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let σ_mwu := fun n => (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runAfterRestarts k M N D restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n := by
  intro T σ_mwu t ht e he
  have hbase := lemma_5_17_mwu C_lsst L μ oracle sparsify hLSST hk hG₀ hD hℓ hLen hM_poly t ht e he
  have hlsf_eq : ∀ j,
      T.lsfs (T.runAfterRestarts k M N D restarts t) j =
        (sparseCoreTool oracle C_lsst L sparsify).lsfs
          ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1 j := by
    intro j
    by_cases hV₀ : (D.G 0).V.Nonempty
    · have hℓ₀ : ∀ x ∈ (D.G 0).E, 0 < D.ℓ 0 x := hℓ 0 (Nat.zero_le τ)
      have hne1 : (T.runAfterRestarts k M N D restarts t).isNonempty = true :=
        (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts t).2.1.trans
          (decide_eq_true hV₀)
      have hne2 : ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = true := by
        have := (runAfterRestarts_isNonempty oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D
          (fun _ => []) t).2.1.trans (decide_eq_true hV₀)
        rw [T.runAfterRestarts_empty_eq_runAt k (D.G 0).m (D.G 0).n D t] at this
        exact this
      have hp := (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j t).2.cs
      have hp0 : (((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.trees j).cs =
          (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j t).1.cs := by
        have := (runAfterRestarts_base_proj oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D
          (fun _ => []) hV₀ j t).2.cs
        rw [T.runAfterRestarts_empty_eq_runAt k (D.G 0).m (D.G 0).n D t] at this
        exact this
      have hcs1 := ((treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
        k M N τ hk D hG₀ hV₀ hℓ₀ hD j).1 t ht).2.2.2.2.2.2.2.1
      have hcs2 := ((treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
        k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hℓ₀ hD j).1 t ht).2.2.2.2.2.2.2.1
      dsimp only [T] at hne1 ⊢
      rw [sparseCoreRestartTool_lsfs_of_nonempty hne1, sparseCoreTool_lsfs_of_nonempty hne2,
        hp, hp0, hcs1, hcs2]
    · have h1 := (runAfterRestarts_empty_case oracle C_lsst L sparsify k M N D restarts hV₀ t).2.1
      have h2 : ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = false := by
        have := (runAfterRestarts_empty_case oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D
          (fun _ => []) hV₀ t).2.1
        rw [T.runAfterRestarts_empty_eq_runAt k (D.G 0).m (D.G 0).n D t] at this
        exact this
      dsimp only [T] at h1 ⊢
      rw [sparseCoreRestartTool_lsfs_of_empty h1, sparseCoreTool_lsfs_of_empty h2]
  simp_rw [hlsf_eq]
  exact hbase

private lemma mem_applyBatch_E_of_no_inserts {G : MGraph} {U : List Update} {e : ℕ}
    (he : e ∈ (G.applyBatch U).E) (hni : ∀ u ∈ U, ¬ u.Inserts e) : e ∈ G.E := by
  induction U generalizing G with
  | nil => exact he
  | cons u rest ih =>
    have h1 := ih he (fun u' hu' => hni u' (List.mem_cons_of_mem u hu'))
    have hu_ni := hni u List.mem_cons_self
    cases u with
    | delete e₀ =>
      exact Finset.mem_of_mem_erase h1
    | split _ _ _ _ => exact h1
    | insert e₀ _ _ =>
      rcases Finset.mem_insert.mp h1 with rfl | heG
      · exact False.elim (hu_ni rfl)
      · exact heG

private lemma mem_foldl_updateInserted_iff {ins : Finset ℕ} {G : MGraph}
    {U : List Update} {e : ℕ} (he_end : e ∈ (G.applyBatch U).E) :
    ((e ∈ G.E ∧ e ∈ ins) ∨ (∃ u ∈ U, u.Inserts e)) →
    e ∈ U.foldl updateInserted ins := by
  intro h
  induction U generalizing G ins with
  | nil =>
    rcases h with ⟨_, hins⟩ | ⟨_, hmem, _⟩
    · exact hins
    · simp at hmem
  | cons u rest ih =>
    dsimp only [MGraph.applyBatch] at he_end
    dsimp only [List.foldl_cons]
    by_cases hr : ∃ u' ∈ rest, u'.Inserts e
    · exact ih he_end (Or.inr hr)
    · have he1 : e ∈ (G.applyUpdate u).E :=
        mem_applyBatch_E_of_no_inserts he_end (fun u' hu' => fun hI => hr ⟨u', hu', hI⟩)
      have h_prev : e ∈ G.E ∧ e ∈ ins ∨ u.Inserts e := by
        rcases h with h0 | ⟨u', hu', hIu'⟩
        · exact Or.inl h0
        · rcases List.mem_cons.mp hu' with rfl | hmem
          · exact Or.inr hIu'
          · exact False.elim (hr ⟨u', hmem, hIu'⟩)
      refine ih he_end (Or.inl ⟨he1, ?_⟩)
      cases u with
      | split _ _ _ _ =>
        rcases h_prev with ⟨_, hins⟩ | hI
        · exact hins
        · simp only [Update.Inserts] at hI
      | delete e₀ =>
        rcases h_prev with ⟨_, hins⟩ | hI
        · rw [MGraph.applyUpdate] at he1
          have hne : e ≠ e₀ := (Finset.mem_erase.mp he1).1
          exact Finset.mem_erase.mpr ⟨hne, hins⟩
        · simp only [Update.Inserts] at hI
      | insert e₀ a b =>
        rcases h_prev with ⟨_, hins⟩ | hI
        · exact Finset.mem_insert_of_mem hins
        · simp only [Update.Inserts] at hI; subst hI; exact Finset.mem_insert_self _ _

/-- **Unconditional** `ToolNoReinsertRestart` for `sparseCoreRestartTool` under `hLSST`, `1 ≤ L`,
and `∀ m, SparsifySpec m (P_fn m) (sparsify m)` (no `hDeg_bound`, `hB_bound`, or `hThresh₀`). -/
theorem sparseCoreRestartTool_toolNoReinsertRestart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).ToolNoReinsertRestart := by
  intro k τ M N D restarts Ψ c w hk hG₀ hD _ hWeak hM hN hrest hThresh t ht1 htτ j hj
    e hePrev heCur hNoIns u hu hIu
  by_cases hV₀ : (D.G 0).V.Nonempty
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hePrev
    have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e :=
      fun x hx => ((hWeak 0 (Nat.zero_le τ)).2.2.2 x hx).2.2.1
    set T := sparseCoreRestartTool oracle C_lsst L sparsify
    have hne_s : (T.runAfterRestarts k M N D restarts s).isNonempty = true :=
      (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
        (decide_eq_true hV₀)
    have hne_s1 : (T.runAfterRestarts k M N D restarts (s + 1)).isNonempty = true :=
      (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts (s + 1)).2.1.trans
        (decide_eq_true hV₀)
    set stPrev := (T.runAfterRestarts k M N D restarts s).trees j
    set stPre := (T.runAfterUpdate k M N D restarts (s + 1)).1.trees j
    set stPost := (T.runAfterRestarts k M N D restarts (s + 1)).trees j
    have hePrev' : e ∈ stPrev.S_cur.E := by
      dsimp only [T] at hePrev hne_s
      rw [sparseCoreRestartTool_S_eq] at hePrev
      simp only [hne_s, ↓reduceIte] at hePrev
      exact hePrev
    have heCur' : e ∈ stPost.S_cur.E := by
      dsimp only [T] at heCur hne_s1
      rw [sparseCoreRestartTool_S_eq] at heCur
      simp only [hne_s1, ↓reduceIte] at heCur
      exact heCur
    have hNoIns' : ∀ u' ∈ (stepTreeCoreAux sparsify stPrev (D.U (s + 1))).U_S, ¬ u'.Inserts e := by
      intro u' hu'
      apply hNoIns u'
      rw [T.runAfterUpdate_succ]
      dsimp only [T] at hne_s ⊢
      rw [sparseCoreRestartTool_update_of_nonempty hne_s]
      exact hu'
    have hSc := runAfterRestarts_S_cur_inv oracle C_lsst L hL (P_fn M) sparsify hLSST
      k M N τ hk D restarts hM hN (hSp M) hG₀ hV₀ hℓ₀ hD j
    have hSc_s := (hSc s (Nat.le_of_lt htτ)).2
    have hSc_s1_pre := (hSc (s + 1) htτ).1
    have hSc_s1 := (hSc (s + 1) htτ).2
    obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
      k M N τ hk D hG₀ hV₀ hℓ₀ hD j
    have hp_s := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j s
    have hp_s1 := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j (s + 1)
    have hb_s := hBase s (Nat.le_of_lt htτ)
    have hb_s1 := hBase (s + 1) htτ
    have hBU : stPrev.cs.G.BatchIsValid (D.U (s + 1)) := by
      rw [hp_s.2.cs]; exact (hStep s htτ).1
    have hstPre_eq : stPre = (stepTreeCoreAux sparsify stPrev (D.U (s + 1))).state := by
      dsimp only [stPre]
      rw [T.runAfterUpdate_succ]
      dsimp only [T] at hne_s ⊢
      rw [sparseCoreRestartTool_update_of_nonempty hne_s]
    have hProp := stepTreeCoreAux_noReinsertPropagates sparsify stPrev (D.U (s + 1)) hBU
      hSc_s.2.2.2 (hp_s.2.activeBuckets.trans hb_s.2.2.2.2.2.1)
      (by
        dsimp only
        rw [← hstPre_eq]
        exact hSc_s1_pre.2.2.1)
      e hePrev'
    have heG_s1 : e ∈ stPost.cs.G.E := (Finset.mem_sdiff.mp (hSc_s1.2.2.2.2.1 heCur')).1
    by_cases hePre : e ∈ stPre.S_cur.E
    · exact (hProp (hstPre_eq ▸ hePre) hNoIns').2 u hu hIu
    · rw [hSc_s1.2.2.1] at heCur'
      rcases Finset.mem_union.mp heCur' with he12 | heX
      · rcases Finset.mem_union.mp he12 with heD | heEx
        · rw [Finset.mem_biUnion] at heD
          rcases heD with ⟨C, hCA, heB⟩
          rw [Finset.mem_biUnion] at heB
          rcases heB with ⟨b, _, heb⟩
          have hC : C ∈ components (D.G 0) := by
            rw [hp_s1.2.activeComps] at hCA
            exact hb_s1.2.2.2.2.2.2.2.2.2.2.1.2 hCA
          set s₀ := lastRestart restarts j (s + 1)
          have hs₀ := lastRestart_spec restarts j (s + 1)
          have hDyn := epochTreeSeq_dyn_spec oracle C_lsst L hL (P_fn M) sparsify hLSST
            k M N τ hk D restarts hM hN (hSp M) hG₀ hV₀ hℓ₀ hD s₀ (s + 1) j hs₀.1 htτ hs₀.2.1
            (fun r hr1 hr2 => hs₀.2.2 r hr1 (Nat.le_of_lt hr2)) C hC b
          have hd_post := hDyn.2.2.2.2.2.2.2.1 (s + 1 - s₀) le_rfl
          have hst_ep : epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ (s + 1) j (s + 1 - s₀) =
              stPost := by
            dsimp only [epochTreeSeq]
            rw [show s₀ + (s + 1 - s₀) = s + 1 by omega]
            by_cases hs₀_lt : s₀ < s + 1
            · have hcond : s + 1 = s + 1 ∧ s₀ < s + 1 := ⟨rfl, hs₀_lt⟩
              simp only [hcond]
              have hni : j ∉ restarts (s + 1) := hs₀.2.2 (s + 1) hs₀_lt le_rfl
              have hf := (foldl_restart_props oracle C_lsst L sparsify
                (T.runAfterUpdate k M N D restarts (s + 1)).1 (restarts (s + 1))).2.2.2.2 j hni
              dsimp only [stPost, T] at hf ⊢
              exact hf.symm
            · simp only [hs₀_lt, and_false, ↓reduceIte]
              dsimp only [stPost, T]
          rw [hst_ep] at hd_post
          have heG_cb : e ∈ (stPost.dyn (C, b)).G.E := hd_post.2.2.1.2.1 heb
          have heTs : e ∈ (stPost.ts C).C.E := (Finset.mem_filter.mp (hd_post.2.2.2.1 ▸ heG_cb)).1
          have hcs_step : stPost.cs = compLSFBatch stPrev.cs (D.U (s + 1)) := by
            rw [hp_s1.2.cs, hp_s.2.cs, hb_s1.2.2.2.2.2.2.2.1, hb_s.2.2.2.2.2.2.2.1,
              dynBatches_succ, List.flatten_append, compLSFBatch_append]
            simp
          have he_insG : e ∈ stPost.cs.insertedGlobal := by
            rw [hcs_step, compLSFBatch_insertedGlobal]
            refine mem_foldl_updateInserted_iff (G := stPrev.cs.G) ?_ (Or.inr ⟨u, hu, hIu⟩)
            rw [← compLSFBatch_G, ← hcs_step]
            exact heG_s1
          have hI_s1 : CompLSFInv C_lsst (D.ℓ 0) stPost.cs := by
            rw [hp_s1.2.cs]; exact hb_s1.2.2.2.2.2.2.2.2.1
          have hG₀_s1 : stPost.cs.G₀ = D.G 0 := by
            rw [hp_s1.2.cs, hb_s1.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
          have he_ts_sub : e ∈ (stPost.cs.compSt C).G.E := by
            have hT_s1 : TildeInv (initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j |>.compSt C)
                (stPost.cs.compSt C) (stPost.ts C) := by
              rw [hp_s1.2.cs, hp_s1.2.ts]
              exact (hb_s1.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
            exact (Finset.mem_sdiff.mp (hT_s1.hCE_sub heTs)).1
          have he_insC : e ∈ (stPost.cs.compSt C).insertedEdges :=
            hI_s1.hCE_ins C (hG₀_s1 ▸ hC) e he_ts_sub he_insG
          have hDisj : Disjoint (stPost.ts C).C.E (stPost.cs.compSt C).insertedEdges := by
            rw [hp_s1.2.cs, hp_s1.2.ts]
            exact (hb_s1.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.1
          exact Finset.disjoint_left.mp hDisj heTs he_insC
        · refine False.elim (hePre ?_)
          rw [hSc_s1_pre.2.2.1, Finset.mem_union, Finset.mem_union]
          left; right
          have h1 : stPre.activeComps = stPost.activeComps := by
            rw [hp_s1.1.activeComps, hp_s1.2.activeComps]
          have h2 : stPre.cs = stPost.cs := by rw [hp_s1.1.cs, hp_s1.2.cs]
          have h3 : stPre.ts = stPost.ts := by rw [hp_s1.1.ts, hp_s1.2.ts]
          rwa [h1, h2, h3]
      · refine False.elim (hePre ?_)
        rw [hSc_s1_pre.2.2.1, Finset.mem_union, Finset.mem_union]
        right
        have h2 : stPre.cs = stPost.cs := by rw [hp_s1.1.cs, hp_s1.2.cs]
        rwa [h2]
  · have hrunE := runAfterRestarts_empty_case oracle C_lsst L sparsify k M N D restarts hV₀ (t - 1)
    rw [sparseCoreRestartTool_S_eq] at hePrev
    simp only [hrunE.2.1, Bool.false_eq_true, ↓reduceIte] at hePrev
    simp [emptyGraph] at hePrev



end MinCostFlow.Chain

end
