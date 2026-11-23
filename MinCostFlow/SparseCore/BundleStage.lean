module

public import MinCostFlow.SparseCore.BundleStageBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bundle stage of the run

`bundleRunSeq_stage_inv` is the analogue of `treeRunSeq_tilde_inv` for `bundleRunSeq`. Along an
ordered run (`OrderedUpTo D τ 2 ord`), at every stage the component-wise LSF is the LSF run on the
input, the bundles of every component and bucket form a partition for the core rotation of the
current order, their parents are roots of their component, and the spanner of the bucket runs on
the bundle graph. At every step the bundle batch has only deletions and splits, at most two splits
per new root of its component, and the bundles lose exactly the edges that the input deletes. Over
the whole run each bundle graph receives at most `bundleSplitBudget k M` splits, because a
component gets at most `⌈56 M / k⌉` new roots (paper Lemma 5.4, page 18). Each bundle has degree at
most `k`. No degree of the input enters.

The proof runs `bundleCompStep_stage` (`BundleStageBase.lean`) on every bucket at every step.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The bundle stage of the run. -/
theorem bundleRunSeq_stage_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let st₀ := (run 0).1
    let cs₀ := st₀.cs
    let splitB := bundleSplitBudget k M
    (∀ t ≤ τ,
      let st := (run t).1
      st.k = k ∧ st.m₀ = M ∧ st.splitBound = splitB ∧
      st.origBucket = st₀.origBucket ∧ st.activeBuckets = st₀.activeBuckets ∧
      st.lazyInitCost = st₀.lazyInitCost ∧
      st.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst ℓ₀ st.cs ∧
      st.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ st.activeComps ∧ st.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ st.activeComps →
        st.cs.compSt C = cs₀.compSt C ∧ ∀ b : ℤ, st.bun (C, b) = st₀.bun (C, b) ∧
          st.dyn (C, b) = st₀.dyn (C, b)) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
        ∀ b : ℤ,
          (∀ (ρ : Rotation st.cs.G) (hG : st.cs.G.IsValid)
              (hF : st.cs.RF.IsRootedSpanningForestOf st.cs.G), ρ.order = ord t →
            (st.bun (C, b)).IsPartition (coreRotation (L := st.cs.lsf) ρ hG hF) k) ∧
          (st.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
          (∀ x ∈ (st.bun (C, b)).vertices, (st.bun (C, b)).parent x ∈ (st.cs.compSt C).R) ∧
          GraphEq (st.dyn (C, b)).G (st.bun (C, b)).graph ∧
          (st.dyn (C, b)).G.IsValid ∧
          st.dyn (C, b) = DynSpanner.runBatchState (normGraph (st₀.bun (C, b)).graph)
            (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)
            (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) t)) ∧
    (∀ t < τ,
      let st := (run t).1
      let st' := (run (t + 1)).1
      let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j t
      st.cs.G.BatchIsValid (D.U (t + 1)) ∧
      (info.newlyActive = touchedCompsBatch st.cs (D.U (t + 1)) \ st.activeComps ∧
        Disjoint st.activeComps info.newlyActive ∧
        st'.activeComps = st.activeComps ∪ info.newlyActive ∧
        info.newlyActive.card ≤ 2 * (D.U (t + 1)).length) ∧
      (∀ b : ℤ, ((components G₀).sum fun C => (info.U_B (C, b)).countP deleteTag) ≤
        (D.U (t + 1)).length) ∧
      (∀ C ∈ components G₀, C ∉ touchedCompsBatch st.cs (D.U (t + 1)) → ∀ b : ℤ,
        info.U_B (C, b) = []) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        (st.dyn (C, b)).G.BatchIsValid (info.U_B (C, b)) ∧
        (st'.dyn (C, b)).G = (st.dyn (C, b)).G.applyBatch (info.U_B (C, b)) ∧
        (∀ op ∈ info.U_B (C, b), isDelOrSplit op) ∧
        batchSplitCount (info.U_B (C, b)) ≤
          2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card ∧
        (st.bun (C, b)).edges \ (st'.bun (C, b)).edges ⊆ batchDeletes (D.U (t + 1)) ∧
        Disjoint (st'.bun (C, b)).edges (batchDeletes (D.U (t + 1))))) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := (st₀.bun (C, b)).graph
      let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
      Hb₀.BatchIsValid Us_b.flatten ∧
      (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
      batchSplitCount Us_b.flatten ≤ splitB ∧
      Hb₀.maxDeg ≤ k) := by
  classical
  intro G₀ ℓ₀ run st₀ cs₀ splitB
  have hk0 : 0 < k := hk
  have hI₀ : CompLSFInv C_lsst ℓ₀ cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hcs₀ : cs₀ = initCompLSF oracle C_lsst G₀ ℓ₀ k j := rfl
  -- The component states at the start.
  have hS₀ : ∀ C ∈ components G₀, (cs₀.compSt C).G₀ = compGraph G₀ C ∧
      (cs₀.compSt C).G = compGraph G₀ C ∧ (cs₀.compSt C).isolatedVerts = ∅ := by
    intro C hC
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    set ℓs := safeLen G₀ ℓ₀
    have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
      rw [show ℓs e = ℓ₀ e from safeLen_eq_of_mem ℓ₀ heG]
      exact hℓ₀ e heG
    have hsp := initLSF_spec hLSST (compGraph_isValid hG₀ hC) (compGraph_nonempty hC) hℓC
      (fun e _ => mwuWeights_pos oracle C_lsst (compGraph G₀ C) ℓs k j e) hk_real
    exact ⟨hsp.1, hsp.2.1, hsp.2.2.2.2.1⟩
  -- The initial bundles.
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
      rw [(hS₀ C hC).2.1]
      exact htC
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
    exact initBundleState_inv _ (coreGraph_isValid hG hF) (hE₀core C b) hk0
  have hedges₀ : ∀ C b, (st₀.bun (C, b)).edges =
      bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b := by
    intro C b
    rw [hbun₀ C b]
    rfl
  -- The invariant at every stage, with the edges of the bundles in their component graph.
  have hBase : ∀ t ≤ τ,
      let st := (run t).1
      st.k = k ∧ st.m₀ = M ∧ st.splitBound = splitB ∧
      st.origBucket = st₀.origBucket ∧ st.activeBuckets = st₀.activeBuckets ∧
      st.lazyInitCost = st₀.lazyInitCost ∧
      st.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst ℓ₀ st.cs ∧
      st.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ st.activeComps ∧ st.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ st.activeComps →
        st.cs.compSt C = cs₀.compSt C ∧ ∀ b : ℤ, st.bun (C, b) = st₀.bun (C, b) ∧
          st.dyn (C, b) = st₀.dyn (C, b)) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
        ∀ b : ℤ,
          BundleCompReady st.cs C (st.bun (C, b)) k (ord t) ∧
          (st.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
          GraphEq (st.dyn (C, b)).G (st.bun (C, b)).graph ∧
          st.dyn (C, b) = DynSpanner.runBatchState (normGraph (st₀.bun (C, b)).graph)
            (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)
            (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) t) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI₀, rfl, ⟨Finset.Subset.rfl, largeComps_sub⟩,
        fun C _ _ => ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun C hC => ⟨?_, fun b =>
          ⟨hready₀ C hC b, Finset.Subset.rfl, normGraph_graphEq _, rfl⟩⟩⟩
      exact lsfDerivedFrom_refl ((hS₀ C hC).2.1.trans (hS₀ C hC).1.symm) (hS₀ C hC).2.2
    | succ s ih =>
      intro hs_le
      obtain ⟨hk_s, hm_s, hsb_s, hob_s, hab_s, hlc_s, hCS, hI_s, hGs, hAct_s, hUnt_s, hC_s⟩ :=
        ih (Nat.le_of_succ_le hs_le)
      set st := (run s).1 with hst
      set U := D.U (s + 1) with hU_def
      have hDt := hD (s + 1) (Nat.succ_pos s) hs_le
      simp only [Nat.add_sub_cancel] at hDt
      have hBV : st.cs.G.BatchIsValid U := by rw [hGs]; exact hDt.1
      have hsp := compLSFBatch_step_props U hI_s hBV
      have hG₀_eq : st.cs.G₀ = G₀ := by rw [hCS, compLSFBatch_G₀]; rfl
      obtain ⟨ρ, σ, hρ, hσ, hrot⟩ := orderedUpTo_rot_step hOrd hs_le hGs
      have hstep : ∀ C ∈ components G₀, ∀ b,
          let out := bundleCompStep st.cs (st.bun (C, b)) k (ord s) (ord (s + 1)) U
          BundleCompReady (compLSFBatch st.cs U) C out.2 k (ord (s + 1)) ∧
          out.2.edges = (st.bun (C, b)).edges \ batchDeletes U ∧
          (C ∉ touchedCompsBatch st.cs U → out = ([], st.bun (C, b))) := by
        intro C hC b
        have h := bundleCompStep_stage hI_s hBV hρ hσ hrot (hG₀_eq ▸ hC) ((hC_s C hC).2 b).1
        exact ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.2⟩
      have hbun' : ∀ p, (run (s + 1)).1.bun p =
          (bundleCompStep st.cs (st.bun p) k (ord s) (ord (s + 1)) U).2 := by
        intro p
        rw [← hk_s]
        rfl
      have hdyn' : ∀ p, (run (s + 1)).1.dyn p = (DynSpanner.update (st.dyn p)
          (bundleCompStep st.cs (st.bun p) k (ord s) (ord (s + 1)) U).1 (sparsify M)).state := by
        intro p
        rw [← hk_s, ← hm_s]
        rfl
      have hcs' : (run (s + 1)).1.cs = compLSFBatch st.cs U := rfl
      refine ⟨hk_s, hm_s, hsb_s, hob_s, hab_s, hlc_s, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcs', hCS, ← compLSFBatch_dynBatches_succ]
      · exact hsp.1
      · rw [hcs', hsp.2.1, hGs]
        exact hDt.2.symm
      · refine ⟨hAct_s.1.trans Finset.subset_union_left, ?_⟩
        refine Finset.union_subset hAct_s.2 (Finset.sdiff_subset.trans ?_)
        rw [← hG₀_eq]
        exact Finset.filter_subset _ _
      · intro C hC hna
        have hna_s : C ∉ st.activeComps := fun h => hna (Finset.mem_union_left _ h)
        have hnt : C ∉ touchedCompsBatch st.cs U := fun h =>
          hna (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hna_s⟩))
        have hunt := compLSFBatch_untouched hI_s hBV (hG₀_eq ▸ hC) hnt
        obtain ⟨hprev, hprevb⟩ := hUnt_s C hC hna_s
        refine ⟨by rw [hcs', hunt.2, hprev], fun b => ?_⟩
        have hout := (hstep C hC b).2.2 hnt
        refine ⟨by rw [hbun', hout, (hprevb b).1], ?_⟩
        rw [hdyn', hout, update_nil, (hprevb b).2]
      · intro C hC
        obtain ⟨hDer, hCb⟩ := hC_s C hC
        have hcomp := compLSFBatch_compSt hI_s hBV (hG₀_eq ▸ hC)
        refine ⟨?_, fun b => ?_⟩
        · rw [hcs', hcomp.1]
          exact lsfDerivedFrom_batch (hI_s.hCompLSF C (hG₀_eq ▸ hC)).1 hcomp.2.2.1 hDer
        obtain ⟨_, hsub, hGb, hrun⟩ := hCb b
        obtain ⟨hready', hEq', -⟩ := hstep C hC b
        have hspec := bundleCompStep_stage hI_s hBV hρ hσ hrot (hG₀_eq ▸ hC) (hCb b).1
        refine ⟨by rw [hbun']; exact hready', ?_, ?_, ?_⟩
        · rw [hbun', hEq']
          exact Finset.sdiff_subset.trans hsub
        · rw [hdyn', update_G_eq, hbun', hspec.2.2.2.1]
          exact graphEq_applyBatch hGb _
        · have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs_le
          rw [hdyn']
          dsimp only [DynSpanner.runBatchState]
          have hUB : (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b) =
              (bundleCompStep st.cs (st.bun (C, b)) k (ord s) (ord (s + 1)) U).1 := by
            change (bundleCompStep st.cs (st.bun (C, b)) st.k (ord s) (ord (s + 1)) U).1 = _
            rw [hk_s]
          rw [hget, ← hrun]
          dsimp only
          rw [hUB]
  -- The facts of one step of one bucket.
  have hstepAt : ∀ t < τ, ∀ C ∈ components G₀, ∀ b : ℤ,
      let st := (run t).1
      let out := bundleCompStep st.cs (st.bun (C, b)) k (ord t) (ord (t + 1)) (D.U (t + 1))
      BundleCompReady (compLSFBatch st.cs (D.U (t + 1))) C out.2 k (ord (t + 1)) ∧
      out.2.edges = (st.bun (C, b)).edges \ batchDeletes (D.U (t + 1)) ∧
      (st.bun (C, b)).graph.BatchIsValid out.1 ∧
      out.2.graph = (st.bun (C, b)).graph.applyBatch out.1 ∧
      (∀ op ∈ out.1, isDelOrSplit op) ∧
      batchSplitCount out.1 ≤
        2 * (((compLSFBatch st.cs (D.U (t + 1))).compSt C).R \ (st.cs.compSt C).R).card ∧
      out.1.countP deleteTag ≤ ((st.bun (C, b)).edges ∩ batchDeletes (D.U (t + 1))).card ∧
      out.2.vertices.card = (st.bun (C, b)).vertices.card + batchSplitCount out.1 ∧
      (C ∉ touchedCompsBatch st.cs (D.U (t + 1)) → out = ([], st.bun (C, b))) := by
    intro t ht C hC b
    obtain ⟨_, _, _, _, _, _, hCS, hI_t, hGt, _, _, hC_t⟩ := hBase t ht.le
    have hDt := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hDt
    have hBV : (run t).1.cs.G.BatchIsValid (D.U (t + 1)) := by rw [hGt]; exact hDt.1
    have hG₀_eq : (run t).1.cs.G₀ = G₀ := by rw [hCS, compLSFBatch_G₀]; rfl
    obtain ⟨ρ, σ, hρ, hσ, hrot⟩ := orderedUpTo_rot_step hOrd ht hGt
    exact bundleCompStep_stage hI_t hBV hρ hσ hrot (hG₀_eq ▸ hC) ((hC_t C hC).2 b).1
  -- The bundle batch, bundles and spanner graph after a step.
  have hUB : ∀ t ≤ τ, ∀ C b, (bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).U_B (C, b) =
      (bundleCompStep (run t).1.cs ((run t).1.bun (C, b)) k (ord t) (ord (t + 1))
        (D.U (t + 1))).1 := by
    intro t ht C b
    change (bundleCompStep (run t).1.cs ((run t).1.bun (C, b)) (run t).1.k (ord t) (ord (t + 1))
      (D.U (t + 1))).1 = _
    rw [(hBase t ht).1]
  have hbunS : ∀ t ≤ τ, ∀ C b, (run (t + 1)).1.bun (C, b) =
      (bundleCompStep (run t).1.cs ((run t).1.bun (C, b)) k (ord t) (ord (t + 1))
        (D.U (t + 1))).2 := by
    intro t ht C b
    change (bundleCompStep (run t).1.cs ((run t).1.bun (C, b)) (run t).1.k (ord t) (ord (t + 1))
      (D.U (t + 1))).2 = _
    rw [(hBase t ht).1]
  have hdynG : ∀ t C b, ((run (t + 1)).1.dyn (C, b)).G = ((run t).1.dyn (C, b)).G.applyBatch
      ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).U_B (C, b)) := by
    intro t C b
    exact update_G_eq _ _ _
  -- The roots of a component only grow.
  have hRgrow : ∀ t < τ, ∀ C ∈ components G₀,
      (cs₀.compSt C).R ⊆ ((run t).1.cs.compSt C).R ∧
      ((run t).1.cs.compSt C).R ⊆ ((run (t + 1)).1.cs.compSt C).R ∧
      ((((run (t + 1)).1.cs.compSt C).R.card : ℕ) : ℝ) ≤ (((run t).1.cs.compSt C).R.card : ℝ) +
        56 * ((D.U (t + 1)).length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    intro t ht C hC
    obtain ⟨_, _, _, _, _, _, hCS, hI_t, hGt, _, _, hC_t⟩ := hBase t ht.le
    have hDt := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hDt
    have hBV : (run t).1.cs.G.BatchIsValid (D.U (t + 1)) := by rw [hGt]; exact hDt.1
    have hG₀_eq : (run t).1.cs.G₀ = G₀ := by rw [hCS, compLSFBatch_G₀]; rfl
    have hgrow := compLSFBatch_compSt_R_card_le hI_t hBV (hG₀_eq ▸ hC)
    rw [hG₀_eq] at hgrow
    exact ⟨(hC_t C hC).1.hR_sub, (compLSFBatch_compSt hI_t hBV (hG₀_eq ▸ hC)).2.2.2.1, hgrow⟩
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun C hC b => ?_⟩
  · -- The stage part.
    obtain ⟨h1, h2, h3, h4, h5, h6, hCS, hI_t, hGt, hAct, hUnt, hC_t⟩ := hBase t ht
    refine ⟨h1, h2, h3, h4, h5, h6, hCS, hI_t, hGt, hAct, hUnt, fun C hC =>
      ⟨(hC_t C hC).1, fun b => ?_⟩⟩
    obtain ⟨⟨hP, hpar, -⟩, hsub, hGb, hrun⟩ := (hC_t C hC).2 b
    obtain ⟨ρ, hρ⟩ := orderedUpTo_rot_at hOrd ht hGt
    refine ⟨hP, hsub, hpar, hGb, ?_, hrun⟩
    exact graphEq_isValid (graphEq_symm hGb)
      (BundleState.graph_isValid (hP ρ hI_t.hG_val (compLSF_RF_isRSF hI_t) hρ))
  · -- The step part.
    obtain ⟨_, _, _, _, _, _, _, hI_t, hGt, _, _, hC_t⟩ := hBase t ht.le
    have hDt := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hDt
    have hBV : (run t).1.cs.G.BatchIsValid (D.U (t + 1)) := by rw [hGt]; exact hDt.1
    refine ⟨hBV, ⟨rfl, disjoint_sdiff_self_right, rfl,
      (Finset.card_le_card Finset.sdiff_subset).trans (touchedCompsBatch_card_le hI_t hBV)⟩,
      fun b => ?_, fun C hC hnt b => ?_, fun C hC b => ?_⟩
    · have hdisj : ∀ C ∈ components G₀, ∀ C' ∈ components G₀, C ≠ C' →
          Disjoint (((run t).1.bun (C, b)).edges ∩ batchDeletes (D.U (t + 1)))
            (((run t).1.bun (C', b)).edges ∩ batchDeletes (D.U (t + 1))) := by
        intro C hC C' hC' hne
        refine Finset.disjoint_left.mpr fun e he he' => ?_
        have h1 := ((hC_t C hC).2 b).2.1 (Finset.mem_inter.mp he).1
        have h2 := ((hC_t C' hC').2 b).2.1 (Finset.mem_inter.mp he').1
        rw [hedges₀] at h1 h2
        have hd := hI₀.hV_disj C hC C' hC' hne
        rw [(hS₀ C hC).2.1, (hS₀ C' hC').2.1] at hd
        exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
      calc ((components G₀).sum fun C =>
            ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j t).U_B (C, b)).countP deleteTag)
          ≤ (components G₀).sum fun C =>
            (((run t).1.bun (C, b)).edges ∩ batchDeletes (D.U (t + 1))).card :=
            Finset.sum_le_sum fun C hC => by
              rw [hUB t ht.le]
              exact (hstepAt t ht C hC b).2.2.2.2.2.2.1
        _ = ((components G₀).biUnion fun C =>
            ((run t).1.bun (C, b)).edges ∩ batchDeletes (D.U (t + 1))).card :=
            (Finset.card_biUnion hdisj).symm
        _ ≤ (batchDeletes (D.U (t + 1))).card :=
            Finset.card_le_card (Finset.biUnion_subset.mpr fun C _ => Finset.inter_subset_right)
        _ ≤ (D.U (t + 1)).length := batchDeletes_card_le _
    · rw [hUB t ht.le, (hstepAt t ht C hC b).2.2.2.2.2.2.2.2 hnt]
    · have hs := hstepAt t ht C hC b
      obtain ⟨-, -, hGb, -⟩ := (hC_t C hC).2 b
      refine ⟨?_, hdynG t C b, ?_, ?_, ?_, ?_⟩
      · rw [hUB t ht.le]
        exact (graphEq_batchIsValid hGb _).mpr hs.2.2.1
      · rw [hUB t ht.le]
        exact hs.2.2.2.2.1
      · rw [hUB t ht.le]
        exact hs.2.2.2.2.2.1
      · rw [hbunS t ht.le, hs.2.1]
        intro e he
        obtain ⟨heB, hn⟩ := Finset.mem_sdiff.mp he
        by_contra hd
        exact hn (Finset.mem_sdiff.mpr ⟨heB, hd⟩)
      · rw [hbunS t ht.le, hs.2.1]
        exact Finset.sdiff_disjoint
  · -- The whole run of one bucket.
    intro Hb₀ Us_b
    have hPref : ∀ t ≤ τ,
        Hb₀.BatchIsValid (Us_b.take t).flatten ∧
        GraphEq (Hb₀.applyBatch (Us_b.take t).flatten) ((run t).1.dyn (C, b)).G ∧
        (∀ op ∈ (Us_b.take t).flatten, isDelOrSplit op) ∧
        batchSplitCount (Us_b.take t).flatten ≤
          2 * (((run t).1.cs.compSt C).R \ (cs₀.compSt C).R).card := by
      intro t
      induction t with
      | zero =>
        intro _
        exact ⟨trivial, graphEq_symm (normGraph_graphEq _), fun _ h => by simp at h, by simp [batchSplitCount]⟩
      | succ s ih =>
        intro hs_le
        obtain ⟨hBV_p, hApp_p, hds_p, hsc_p⟩ := ih (Nat.le_of_succ_le hs_le)
        have hs_lt : s < τ := hs_le
        have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs_lt
        have htake : (Us_b.take (s + 1)).flatten = (Us_b.take s).flatten ++
            (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b) := by
          rw [take_succ_of_getElem? hget, List.flatten_append]
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
          rfl
        obtain ⟨-, -, hGb, -⟩ := ((hBase s hs_lt.le).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
        have hs := hstepAt s hs_lt C hC b
        obtain ⟨hS0, hss, -⟩ := hRgrow s hs_lt C hC
        rw [htake, hUB s hs_lt.le]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [MinCostFlow.SparseCore.batchIsValid_append]
          refine ⟨hBV_p, ?_⟩
          exact (graphEq_batchIsValid (graphEq_trans hApp_p hGb) _).mpr hs.2.2.1
        · rw [MinCostFlow.SparseCore.applyBatch_append, hdynG, hUB s hs_lt.le]
          exact graphEq_applyBatch hApp_p _
        · intro op hop
          rcases List.mem_append.mp hop with h | h
          · exact hds_p op h
          · exact hs.2.2.2.2.1 op h
        · rw [MinCostFlow.SparseCore.batchSplitCount_append]
          have hc := hs.2.2.2.2.2.1
          change _ ≤ 2 * ((((run (s + 1)).1.cs.compSt C).R \ (cs₀.compSt C).R).card)
          change _ ≤ 2 * ((((run (s + 1)).1.cs.compSt C).R \ ((run s).1.cs.compSt C).R).card) at hc
          have htel := Finset.card_sdiff_of_subset hS0
          have htel' := Finset.card_sdiff_of_subset hss
          have htel'' := Finset.card_sdiff_of_subset (hS0.trans hss)
          have c1 := Finset.card_le_card hS0
          have c2 := Finset.card_le_card hss
          omega
    have hRb : ∀ t ≤ τ, ((((run t).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤
        56 * ((∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      intro t
      induction t with
      | zero =>
        intro _
        show (((cs₀.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤ _
        simp
      | succ s ih =>
        intro hs_le
        have hs_lt : s < τ := hs_le
        have ih' := ih hs_lt.le
        obtain ⟨hS0, hss, hgrow⟩ := hRgrow s hs_lt C hC
        have hdiff : ((((run (s + 1)).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤
            ((((run s).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) +
              ((((run (s + 1)).1.cs.compSt C).R.card : ℝ) -
                (((run s).1.cs.compSt C).R.card : ℝ)) := by
          have c1 := Finset.card_le_card hS0
          have c2 := Finset.card_le_card hss
          rw [Finset.card_sdiff_of_subset hS0, Finset.card_sdiff_of_subset (hS0.trans hss),
            Nat.cast_sub c1, Nat.cast_sub (c1.trans c2)]
          linarith
        have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
          ext x
          simp [Finset.mem_Icc]
          omega
        rw [hIcc, Finset.sum_insert (by simp), Nat.cast_add]
        have hring : 56 * (((D.U (s + 1)).length : ℝ) +
            ((∑ x ∈ Finset.Icc 1 s, (D.U x).length : ℕ) : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 =
            56 * ((D.U (s + 1)).length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 +
            56 * ((∑ x ∈ Finset.Icc 1 s, (D.U x).length : ℕ) : ℝ) *
              (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
        linarith [hgrow, ih', hdiff, hring]
    have hlogN_pos : (0 : ℝ) < Real.log ((N : ℝ) + 2) := by
      linarith [half_lt_log_add_two N]
    have hlog_sq_le : (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := by
      refine pow_le_pow_left₀ (by linarith [half_lt_log_add_two G₀.n])
        (Real.log_le_log (by positivity) ?_) 2
      have : (G₀.n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlog2_pos : (0 : ℝ) < (Real.log ((N : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlogN_pos
    have hR_le : ((((run τ).1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤
        56 * (M : ℝ) / (k : ℝ) := by
      have hr' := le_trans (hRb τ le_rfl) (mul_le_mul_of_nonneg_left hlog_sq_le (by positivity))
      have h1 : 56 * ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) ≤
          56 * SparseCoreTool.updateThreshold k M N := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hlog2_pos.le
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have heq : 56 * SparseCoreTool.updateThreshold k M N *
          (Real.log ((N : ℝ) + 2)) ^ 2 = 56 * (M : ℝ) / (k : ℝ) := by
        rw [SparseCoreTool.updateThreshold]
        field_simp [hlog2_pos.ne', hk_pos.ne']
      exact le_trans hr' (heq ▸ h2)
    have hceil : (((run τ).1.cs.compSt C).R \ (cs₀.compSt C).R).card ≤
        Nat.ceil (56 * (M : ℝ) / (k : ℝ)) := by
      exact_mod_cast le_trans hR_le (Nat.le_ceil _)
    obtain ⟨hBV_all, -, hds_all, hsc_all⟩ := hPref τ le_rfl
    have hlen : Us_b.length = τ := by simp [Us_b, bundleBatchList, bundleBatchListWith]
    rw [List.take_of_length_le hlen.le] at hBV_all hds_all hsc_all
    refine ⟨hBV_all, hds_all, hsc_all.trans ?_, ?_⟩
    · change _ ≤ 2 * _
      omega
    · exact BundleState.maxDeg_le
        ((hready₀ C hC b).1 ρ₀ hI₀.hG_val (compLSF_RF_isRSF hI₀) hρ₀)

/-- `bundleRunSeq_stage_inv` in the form that `BundleRunInvBase.lean` takes as a
hypothesis: the same statement without the last conjunct of the step part. -/
theorem bundleRunSeq_stage_inv_stmt : BundleRunSeqStageInvStmt := by
  intro oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨h1, h2, h3⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST k M N τ hk D hG₀
    hV₀ hℓ₀ hD hN hThresh ord hOrd j
  refine ⟨h1, fun t ht => ?_, h3⟩
  obtain ⟨a, b, c, d, e⟩ := h2 t ht
  exact ⟨a, b, c, d, fun C hC b' =>
    let h := e C hC b'
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩

end MinCostFlow.SparseCore
