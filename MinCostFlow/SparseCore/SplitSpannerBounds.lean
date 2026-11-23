module

public import MinCostFlow.SparseCore.SplitSpannerBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stage-1 trajectory invariants for `treeRunSeq`

Proves the Stage-1 component-wise quotient and per-bucket graph invariants across steps `0..τ`:
* `treeRunSeq_tilde_core_inv` (without update-budget threshold), and
* `treeRunSeq_tilde_inv` (with `batchSplitCount ≤ splitB` under `hThresh`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-- Stage-1 component-wise quotient and per-bucket graph invariants across steps `0..τ`. -/
lemma treeRunSeq_tilde_core_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (j : ℕ) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    (∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      st.m₀ = M ∧
      st.n₀ = N ∧
      st.Δ₀ = G₀.maxDeg ∧
      st.splitBound = splitB ∧
      st.origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) ∧
      st.activeBuckets = (fun C => (ts₀ C).C.E.image origB) ∧
      st.lazyInitCost = (fun C => ((ts₀ C).C.E.image origB).sum fun b =>
        (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
          (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)).cost) ∧
      st.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst ℓ₀ st.cs ∧
      st.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ st.activeComps ∧ st.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ st.activeComps →
        st.cs.compSt C = cs₀.compSt C ∧ st.ts C = ts₀ C) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
        TildeInv (cs₀.compSt C) (st.cs.compSt C) (st.ts C) ∧
        (st.ts C).C.E ⊆ (ts₀ C).C.E ∧
        Disjoint (st.ts C).C.E (st.cs.compSt C).insertedEdges ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.IsValid ∧
          (st.ts C).C.IsSubgraph (st.dyn (C, b)).G ∧
          (st.dyn (C, b)).G.E = (st.ts C).C.E.filter (fun e => origB e = b) ∧
          st.dyn (C, b) = DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
            (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
            (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) t)) ∧
    (∀ t < τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      let st' := (treeRunSeq oracle C_lsst L sparsify k M N D j (t + 1)).1
      let info := stepTreeCoreAux sparsify st (D.U (t + 1))
      st.cs.G.BatchIsValid (D.U (t + 1)) ∧
      (info.newlyActive = touchedCompsBatch st.cs (D.U (t + 1)) \ st.activeComps ∧
        Disjoint st.activeComps info.newlyActive ∧
        st'.activeComps = st.activeComps ∪ info.newlyActive ∧
        info.newlyActive.card ≤ 2 * (D.U (t + 1)).length) ∧
      ((components G₀).sum fun C =>
        projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))) ≤
          2 * (D.U (t + 1)).length ∧
      (∀ C ∈ components G₀,
        let U_proj := projCompBatchG st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        let w_proj := projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        info.U_C C = (tildeStepBatch (st.cs.compSt C) (st.ts C) U_proj).1 ∧
        (∀ op ∈ info.U_C C, isDelOrSplit op) ∧
        batchSplitCount (info.U_C C) ≤
          w_proj * (G₀.maxDeg + 1) + ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card ∧
        ((info.U_C C).length : ℝ) ≤ (w_proj : ℝ) *
          ((G₀.maxDeg : ℝ) + 1 + 56 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.BatchIsValid (info.U_b (C, b)) ∧
          (st'.dyn (C, b)).G = (st.dyn (C, b)).G.applyBatch (info.U_b (C, b)) ∧
          (∀ op ∈ info.U_b (C, b), isDelOrSplit op) ∧
          (info.U_b (C, b)).length ≤ (info.U_C C).length ∧
          batchSplitCount (info.U_b (C, b)) ≤ batchSplitCount (info.U_C C))) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      Hb₀.BatchIsValid Us_b.flatten ∧
      (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
      batchSplitCount Us_b.flatten ≤
        (∑ s ∈ Finset.Icc 1 τ, (D.U s).length) * (G₀.maxDeg + 1) +
          (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cs.compSt C).R \
            (cs₀.compSt C).R).card) := by
  classical
  intro G₀ ℓ₀ cs₀ ts₀ origB splitB
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ : CompLSFInv C_lsst ℓ₀ cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G₀ = compGraph G₀ C ∧
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).isolatedVerts = ∅ ∧
      (cs₀.compSt C).insertedEdges = ∅ ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E := by
    intro C hC
    have hGC_val := compGraph_isValid hG₀ hC
    have hGC_ne := compGraph_nonempty hC
    set ℓs := safeLen G₀ ℓ₀
    have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
      rw [show ℓs e = ℓ₀ e from safeLen_eq_of_mem ℓ₀ heG]
      exact hℓ₀ e heG
    have hw : ∀ e ∈ (compGraph G₀ C).E, 0 < mwuWeights oracle C_lsst (compGraph G₀ C) ℓs k j e :=
      fun e _ => mwuWeights_pos oracle C_lsst (compGraph G₀ C) ℓs k j e
    have hsp := initLSF_spec hLSST hGC_val hGC_ne hℓC hw hk_real
    exact ⟨hsp.1, hsp.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2.1,
      hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2.2.2.2
  have hT₀ : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (cs₀.compSt C) (ts₀ C) :=
    fun C hC => initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
  have hActB_eq : (fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e))) =
      (fun C => (ts₀ C).C.E.image origB) := by
    funext C
    refine Finset.image_congr fun e he => ?_
    have heG : e ∈ G₀.E := Finset.filter_subset _ _ (Finset.mem_sdiff.mp he).1
    simp only [origB, coreLen, safeLen_eq_of_mem ℓ₀ heG]
  have hBase : ∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      st.m₀ = M ∧
      st.n₀ = N ∧
      st.Δ₀ = G₀.maxDeg ∧
      st.splitBound = splitB ∧
      st.origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) ∧
      st.activeBuckets = (fun C => (ts₀ C).C.E.image origB) ∧
      st.lazyInitCost = (fun C => ((ts₀ C).C.E.image origB).sum fun b =>
        (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
          (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)).cost) ∧
      st.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst ℓ₀ st.cs ∧
      st.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ st.activeComps ∧ st.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ st.activeComps →
        st.cs.compSt C = cs₀.compSt C ∧ st.ts C = ts₀ C) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
        TildeInv (cs₀.compSt C) (st.cs.compSt C) (st.ts C) ∧
        (st.ts C).C.E ⊆ (ts₀ C).C.E ∧
        Disjoint (st.ts C).C.E (st.cs.compSt C).insertedEdges ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.IsValid ∧
          (st.ts C).C.IsSubgraph (st.dyn (C, b)).G ∧
          (st.dyn (C, b)).G.E = (st.ts C).C.E.filter (fun e => origB e = b) ∧
          st.dyn (C, b) = DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
            (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
            (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) t) := by
    intro t
    induction t with
    | zero =>
      intro _
      dsimp only [treeRunSeq, treeRunSeqWith, initTreeCore]
      refine ⟨rfl, rfl, rfl, rfl, rfl, hActB_eq, ?_, rfl, hI₀, rfl,
        ⟨Finset.Subset.rfl, largeComps_sub⟩, fun C _ _ => ⟨rfl, rfl⟩, fun C hC => ?_⟩
      · funext C
        rw [congrFun hActB_eq C]
      have hspC := hS₀C_spec C hC
      refine ⟨lsfDerivedFrom_refl (hspC.2.1.trans hspC.1.symm) hspC.2.2.1, hT₀ C hC,
        Finset.Subset.rfl, ?_, fun b => ?_⟩
      · rw [hspC.2.2.2.1]; exact Finset.disjoint_empty_right _
      · have hHb := initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
        dsimp only [DynSpanner.runBatchState, DynSpanner.init, DynSpanner.initAt]
        refine ⟨hHb.1, hHb.2.1, ?_, rfl⟩
        rw [hHb.2.2.1]; refine Finset.filter_congr fun e he => ?_
        exact eq_iff_iff.mp (congrArg (· = b)
          (initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e he).symm)
    | succ s ih =>
      intro hs_le
      obtain ⟨hm₀, hn₀, hΔ₀, hspB, hOB, hAB, hLC, hCS, hI_s, hGs, hAct_s, hUnt_s, hC_s⟩ :=
        ih (Nat.le_of_succ_le hs_le)
      set st := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
      set U := D.U (s + 1)
      have hDt := hD (s + 1) (Nat.succ_pos s) hs_le
      simp only [Nat.add_sub_cancel] at hDt
      have hBV_U : st.cs.G.BatchIsValid U := by rw [hGs]; exact hDt.1
      have hsp_cs := compLSFBatch_step_props U hI_s hBV_U
      have hG₀_eq : st.cs.G₀ = G₀ := by rw [hCS, compLSFBatch_G₀]; rfl
      have hcs'_eq : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs =
          compLSFBatch cs₀ (dynBatches D (s + 1)).flatten := by
        change compLSFBatch st.cs U = _
        rw [hCS, ← compLSFBatch_dynBatches_succ]
      have hG'_D : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.G = D.G (s + 1) := by
        change (compLSFBatch st.cs U).G = D.G (s + 1)
        rw [hsp_cs.2.1, hGs]
        exact hDt.2.symm
      have hAct' : largeComps k G₀ ⊆ (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps ∧
          (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps ⊆ components G₀ := by
        refine ⟨Finset.Subset.trans hAct_s.1 Finset.subset_union_left, ?_⟩
        refine Finset.union_subset hAct_s.2 (Finset.Subset.trans Finset.sdiff_subset ?_)
        rw [← hG₀_eq]
        exact Finset.filter_subset _ _
      have hUnt' : ∀ C ∈ components G₀,
          C ∉ (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps →
          (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.compSt C = cs₀.compSt C ∧
          (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.ts C = ts₀ C := by
        intro C hC hna
        have hna_s : C ∉ st.activeComps := fun h => hna (Finset.mem_union_left _ h)
        have hnt : C ∉ touchedCompsBatch st.cs U := fun h =>
          hna (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hna_s⟩))
        have hunt := compLSFBatch_untouched hI_s hBV_U (hG₀_eq ▸ hC) hnt
        have hprev := hUnt_s C hC hna_s
        refine ⟨?_, ?_⟩
        · change (compLSFBatch st.cs U).compSt C = cs₀.compSt C
          rw [hunt.2, hprev.1]
        · change (tildeStepBatch (st.cs.compSt C) (st.ts C)
            (projCompBatchG st.cs.G (st.cs.compSt C).G U)).2.1 = ts₀ C
          rw [hunt.1, tildeStepBatch]
          exact hprev.2
      refine ⟨hm₀, hn₀, hΔ₀, hspB, hOB, hAB, hLC, hcs'_eq, hsp_cs.1, hG'_D, hAct', hUnt', ?_⟩
      intro C hC
      obtain ⟨hD_C, hT_C, hCE_sub_C, hDisj_C, hDyn_C⟩ := hC_s C hC
      have hCI₀ := (hI₀.hCompLSF C hC).1
      have hCI_s := (hI_s.hCompLSF C (hG₀_eq ▸ hC)).1
      have hcomp_sp := hsp_cs.2.2.1 C (hG₀_eq ▸ hC)
      set U_C := projCompBatchG st.cs.G (st.cs.compSt C).G U
      have htd := tildeStepBatch_spec hCI₀ (hCov₀ C hC) hCI_s hD_C hT_C hcomp_sp.2.2.1
      rcases htd with ⟨htd_S, htd_I, htd_D, htd_T, _, htd_BV, htd_C, htd_ds, _, _, _, _⟩
      have hCE_sub2 := tildeStepBatch_CE_sub hCI₀ (hCov₀ C hC) U_C hCI_s hD_C hcomp_sp.2.2.1 hT_C
      have hDisj2 := tildeStepBatch_disjoint_inserted hCI₀ (hCov₀ C hC) U_C hCI_s hD_C
        hcomp_sp.2.2.1 hT_C hDisj_C
      have hcompSt_eq : (compLSFBatch st.cs U).compSt C = (tildeStepBatch (st.cs.compSt C) (st.ts C) U_C).2.2 := by
        rw [htd_S, hcomp_sp.1]
      refine ⟨hcompSt_eq ▸ htd_D, hcompSt_eq ▸ htd_T, Finset.Subset.trans hCE_sub2 hCE_sub_C,
        hcompSt_eq ▸ hDisj2, fun b => ?_⟩
      obtain ⟨hdb_val, hdb_sub, hdb_E, hdb_run⟩ := hDyn_C b
      have hfb := filterBucketBatch_spec (origBucket := origB) (b := b)
        hT_C.hC_val hdb_val hdb_sub hdb_E htd_BV htd_ds
      rcases hfb with ⟨_, hfb_app, hfb_val, hfb_sub, hfb_E, _, _, _⟩
      have hnext_dyn : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.dyn (C, b) =
          DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
            (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
            (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) (s + 1) := by
        have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_le
        dsimp only [DynSpanner.runBatchState]
        rw [hget, ← hdb_run]
        change (DynSpanner.update (st.dyn (C, b)) _ (sparsify st.m₀)).state =
          (DynSpanner.update (st.dyn (C, b)) _ (sparsify M)).state
        rw [hm₀]; rfl
      have hG_eq : ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.dyn (C, b)).G =
          (filterBucketBatch (st.dyn (C, b)).G
            (tildeStepBatch (st.cs.compSt C) (st.ts C) U_C).1).1 := by
        change (DynSpanner.update (st.dyn (C, b))
          (filterBucketBatch (st.dyn (C, b)).G
            (tildeStepBatch (st.cs.compSt C) (st.ts C) U_C).1).2
          (sparsify st.m₀)).state.G = _
        rw [update_G_eq, ← hfb_app]
      refine ⟨?_, ?_, ?_, hnext_dyn⟩
      · rw [hG_eq]; exact hfb_val
      · rw [hG_eq]
        change (tildeStepBatch (st.cs.compSt C) (st.ts C) U_C).2.1.C.IsSubgraph _
        rw [htd_C]
        exact hfb_sub
      · rw [hG_eq]
        change (filterBucketBatch _ _).1.E =
          (tildeStepBatch (st.cs.compSt C) (st.ts C) U_C).2.1.C.E.filter _
        rw [htd_C]
        exact hfb_E
  have hStep : ∀ t < τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      let st' := (treeRunSeq oracle C_lsst L sparsify k M N D j (t + 1)).1
      let info := stepTreeCoreAux sparsify st (D.U (t + 1))
      st.cs.G.BatchIsValid (D.U (t + 1)) ∧
      (info.newlyActive = touchedCompsBatch st.cs (D.U (t + 1)) \ st.activeComps ∧
        Disjoint st.activeComps info.newlyActive ∧
        st'.activeComps = st.activeComps ∪ info.newlyActive ∧
        info.newlyActive.card ≤ 2 * (D.U (t + 1)).length) ∧
      ((components G₀).sum fun C =>
        projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))) ≤
          2 * (D.U (t + 1)).length ∧
      (∀ C ∈ components G₀,
        let U_proj := projCompBatchG st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        let w_proj := projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        info.U_C C = (tildeStepBatch (st.cs.compSt C) (st.ts C) U_proj).1 ∧
        (∀ op ∈ info.U_C C, isDelOrSplit op) ∧
        batchSplitCount (info.U_C C) ≤
          w_proj * (G₀.maxDeg + 1) + ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card ∧
        ((info.U_C C).length : ℝ) ≤ (w_proj : ℝ) *
          ((G₀.maxDeg : ℝ) + 1 + 56 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.BatchIsValid (info.U_b (C, b)) ∧
          (st'.dyn (C, b)).G = (st.dyn (C, b)).G.applyBatch (info.U_b (C, b)) ∧
          (∀ op ∈ info.U_b (C, b), isDelOrSplit op) ∧
          (info.U_b (C, b)).length ≤ (info.U_C C).length ∧
          batchSplitCount (info.U_b (C, b)) ≤ batchSplitCount (info.U_C C)) := by
    intro t ht
    obtain ⟨_, _, _, _, _, _, _, hCS_t, hI_t, hGt, _, _, hC_t⟩ := hBase t (Nat.le_of_lt ht)
    have hDt := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hDt
    have hBV_U : (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G.BatchIsValid (D.U (t + 1)) := by
      rw [hGt]; exact hDt.1
    have hG₀_t : (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G₀ = G₀ := by
      rw [hCS_t, compLSFBatch_G₀]; rfl
    have htc := touchedCompsBatch_card_le hI_t hBV_U
    have hsum_p := sum_projCompBatchWeight_le (D.U (t + 1)) hI_t hBV_U
    rw [hG₀_t] at hsum_p
    refine ⟨hBV_U, ⟨rfl, disjoint_sdiff_self_right, rfl,
      le_trans (Finset.card_le_card Finset.sdiff_subset) htc⟩, hsum_p, fun C hC => ?_⟩
    obtain ⟨hD_C, hT_C, _, _, hDyn_C⟩ := hC_t C hC
    have hCI₀ := (hI₀.hCompLSF C hC).1
    have hCI_t := (hI_t.hCompLSF C (hG₀_t ▸ hC)).1
    have hcomp_sp := compLSFBatch_compSt hI_t hBV_U (hG₀_t ▸ hC)
    set U_proj := projCompBatchG (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
      ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G (D.U (t + 1))
    have htd := tildeStepBatch_spec hCI₀ (hCov₀ C hC) hCI_t hD_C hT_C hcomp_sp.2.2.1
    rcases htd with ⟨htd_S, _, _, _, _, htd_BV, _, htd_ds, _, _, _, _⟩
    have htw := tildeStepBatch_projCompBatchG_spec hCI₀ (hCov₀ C hC) (D.U (t + 1))
      hI_t (hG₀_t ▸ hC) hD_C hT_C hBV_U
    have hGC_0 : (cs₀.compSt C).G₀ = compGraph G₀ C := (hS₀C_spec C hC).1
    have hGC_G : (cs₀.compSt C).G = compGraph G₀ C := (hS₀C_spec C hC).2.1
    have hn_le : (compGraph G₀ C).n ≤ G₀.n := compGraph_n_le hC
    have hd_le : (compGraph G₀ C).maxDeg ≤ G₀.maxDeg := compGraph_maxDeg_le hC
    have hR_eq_C : ((treeRunSeq oracle C_lsst L sparsify k M N D j (t + 1)).1.cs.compSt C).R =
        (tildeStepBatch ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C)
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.ts C) U_proj).2.2.R := by
      change ((compLSFBatch _ (D.U (t + 1))).compSt C).R = _
      rw [hcomp_sp.1, htd_S]
    have hsc' : batchSplitCount (tildeStepBatch ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C)
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.ts C) U_proj).1 ≤
        projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G (D.U (t + 1)) * (G₀.maxDeg + 1) +
          (((treeRunSeq oracle C_lsst L sparsify k M N D j (t + 1)).1.cs.compSt C).R \
            ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).R).card := by
      have hsc_w := htw.1
      rw [hGC_G] at hsc_w
      rw [hR_eq_C]
      exact le_trans hsc_w (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
    have hlen' : ((tildeStepBatch ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C)
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.ts C) U_proj).1.length : ℝ) ≤
        (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G (D.U (t + 1)) : ℝ) *
          ((G₀.maxDeg : ℝ) + 1 + 56 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
      have hlen_w := htw.2.1
      rw [hGC_0, hGC_G] at hlen_w
      have hlogC : Real.log (((compGraph G₀ C).n : ℝ) + 2) ≤ Real.log ((G₀.n : ℝ) + 2) := by
        refine Real.log_le_log (by positivity) ?_
        have : ((compGraph G₀ C).n : ℝ) ≤ G₀.n := by exact_mod_cast hn_le
        linarith
      have hlogC_nn : 0 ≤ Real.log (((compGraph G₀ C).n : ℝ) + 2) := by
        linarith [half_lt_log_add_two (compGraph G₀ C).n]
      have hsq : (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 2 ≤
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hlogC_nn hlogC 2
      have hd_r : ((compGraph G₀ C).maxDeg : ℝ) ≤ G₀.maxDeg := by exact_mod_cast hd_le
      have hU_nn : (0 : ℝ) ≤ projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G (D.U (t + 1)) :=
        Nat.cast_nonneg _
      exact le_trans hlen_w (mul_le_mul_of_nonneg_left (by linarith) hU_nn)
    refine ⟨rfl, htd_ds, hsc', hlen', fun b => ?_⟩
    obtain ⟨hdb_val, hdb_sub, hdb_E, _⟩ := hDyn_C b
    have hfb := filterBucketBatch_spec (origBucket := origB) (b := b)
      hT_C.hC_val hdb_val hdb_sub hdb_E htd_BV htd_ds
    refine ⟨hfb.1, ?_, hfb.2.2.2.2.2.1, hfb.2.2.2.2.2.2.1, hfb.2.2.2.2.2.2.2⟩
    change (DynSpanner.update _ _ _).state.G = _
    rw [update_G_eq]
    rfl
  have hFlat : ∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      Hb₀.BatchIsValid Us_b.flatten ∧
      (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
      batchSplitCount Us_b.flatten ≤
        (∑ s ∈ Finset.Icc 1 τ, (D.U s).length) * (G₀.maxDeg + 1) +
          (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cs.compSt C).R \
            (cs₀.compSt C).R).card := by
    intro C hC b
    let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
    let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
    have hPref : ∀ t ≤ τ,
        let pref := (Us_b.take t).flatten
        Hb₀.BatchIsValid pref ∧
        Hb₀.applyBatch pref = ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G ∧
        (∀ op ∈ pref, isDelOrSplit op) ∧
        batchSplitCount pref ≤
          (∑ s ∈ Finset.Icc 1 t, (D.U s).length) * (G₀.maxDeg + 1) +
            (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).R \
              (cs₀.compSt C).R).card := by
      intro t
      induction t with
      | zero =>
        intro _
        have h0_G : ((treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.dyn (C, b)).G = Hb₀ := rfl
        have h0_R : ((treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.cs.compSt C).R =
            (cs₀.compSt C).R := rfl
        rw [h0_G, h0_R]
        exact ⟨trivial, rfl, fun _ h => by simp at h, by simp [batchSplitCount]⟩
      | succ s ih =>
        intro hs_le
        obtain ⟨hBV_p, hApp_p, hds_p, hsc_p⟩ := ih (Nat.le_of_succ_le hs_le)
        have hs_lt : s < τ := hs_le
        have hStep_s := hStep s hs_lt
        have hget : Us_b[s]? = some ((stepTreeCoreAux sparsify
            (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 (D.U (s + 1))).U_b (C, b)) :=
          bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_lt
        have htake : (Us_b.take (s + 1)).flatten =
            (Us_b.take s).flatten ++ (stepTreeCoreAux sparsify
              (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 (D.U (s + 1))).U_b (C, b) := by
          rw [take_succ_of_getElem? hget, List.flatten_append]
          simp
        obtain ⟨_, _, hb_ds, hb_sc⟩ := (hStep_s.2.2.2 C hC).2.2.2.2 b
        obtain ⟨hb_BV, hb_G, _⟩ := (hStep_s.2.2.2 C hC).2.2.2.2 b
        have hb_s := hBase s (Nat.le_of_succ_le hs_le)
        have hb_s1 := hBase (s + 1) hs_le
        set st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
        set st_s1 := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
        have hG₀_s : st_s.cs.G₀ = G₀ := by rw [hb_s.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
        have hcomp_sp := compLSFBatch_compSt hb_s.2.2.2.2.2.2.2.2.1 hStep_s.1 (hG₀_s ▸ hC)
        have hI_sC := (hb_s.2.2.2.2.2.2.2.2.1.hCompLSF C (hG₀_s ▸ hC)).1
        have hS0_s : (cs₀.compSt C).R ⊆ (st_s.cs.compSt C).R :=
          (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1.hR_sub
        have hcomp_step : st_s1.cs.compSt C =
            applyLSFBatch (st_s.cs.compSt C)
              (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) := hcomp_sp.1
        have h_ss_R_sub : (st_s.cs.compSt C).R ⊆ (st_s1.cs.compSt C).R := hcomp_sp.2.2.2.1
        have hS0_s1 : (cs₀.compSt C).R ⊆ (st_s1.cs.compSt C).R :=
          Finset.Subset.trans hS0_s h_ss_R_sub
        have hR_tel : ((st_s.cs.compSt C).R \ (cs₀.compSt C).R).card +
            ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card =
            ((st_s1.cs.compSt C).R \ (cs₀.compSt C).R).card := by
          rw [Finset.card_sdiff_of_subset hS0_s, Finset.card_sdiff_of_subset h_ss_R_sub,
            Finset.card_sdiff_of_subset hS0_s1]
          have c1 := Finset.card_le_card hS0_s
          have c2 := Finset.card_le_card h_ss_R_sub
          omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [htake, batchIsValid_append]
          exact ⟨hBV_p, hApp_p ▸ hb_BV⟩
        · rw [htake, applyBatch_append, hApp_p, ← hb_G]
        · intro op hop
          rw [htake, List.mem_append] at hop
          exact hop.elim (hds_p op) (hb_ds op)
        · rw [htake, batchSplitCount_append]
          have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
            ext x; simp [Finset.mem_Icc]; omega
          rw [hIcc, Finset.sum_insert (by simp), add_comm, Nat.add_mul]
          have huc_sc := (hStep_s.2.2.2 C hC).2.2.1
          have hproj_len := projCompBatchWeight_le_length (D.U (s + 1)) st_s.cs.G (st_s.cs.compSt C).G
          have hmul_le : projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) *
              (G₀.maxDeg + 1) ≤ (D.U (s + 1)).length * (G₀.maxDeg + 1) :=
            Nat.mul_le_mul_right _ hproj_len
          omega
    obtain ⟨hBV_all, _, hds_all, hsc_all⟩ := hPref τ (le_refl τ)
    have hUs_len : Us_b.length = τ := by simp [Us_b, bucketBatchList]
    have hTake_all : Us_b.take τ = Us_b := List.take_of_length_le hUs_len.le
    rw [hTake_all] at hBV_all hds_all hsc_all
    exact ⟨hBV_all, hds_all, hsc_all⟩
  exact ⟨hBase, hStep, hFlat⟩

lemma treeRunSeq_tilde_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    (∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      st.m₀ = M ∧
      st.n₀ = N ∧
      st.Δ₀ = G₀.maxDeg ∧
      st.splitBound = splitB ∧
      st.origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) ∧
      st.activeBuckets = (fun C => (ts₀ C).C.E.image origB) ∧
      st.lazyInitCost = (fun C => ((ts₀ C).C.E.image origB).sum fun b =>
        (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
          (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)).cost) ∧
      st.cs = compLSFBatch cs₀ (dynBatches D t).flatten ∧
      CompLSFInv C_lsst ℓ₀ st.cs ∧
      st.cs.G = D.G t ∧
      (largeComps k G₀ ⊆ st.activeComps ∧ st.activeComps ⊆ components G₀) ∧
      (∀ C ∈ components G₀, C ∉ st.activeComps →
        st.cs.compSt C = cs₀.compSt C ∧ st.ts C = ts₀ C) ∧
      (∀ C ∈ components G₀,
        LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
        TildeInv (cs₀.compSt C) (st.cs.compSt C) (st.ts C) ∧
        (st.ts C).C.E ⊆ (ts₀ C).C.E ∧
        Disjoint (st.ts C).C.E (st.cs.compSt C).insertedEdges ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.IsValid ∧
          (st.ts C).C.IsSubgraph (st.dyn (C, b)).G ∧
          (st.dyn (C, b)).G.E = (st.ts C).C.E.filter (fun e => origB e = b) ∧
          st.dyn (C, b) = DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
            (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
            (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) t)) ∧
    (∀ t < τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      let st' := (treeRunSeq oracle C_lsst L sparsify k M N D j (t + 1)).1
      let info := stepTreeCoreAux sparsify st (D.U (t + 1))
      st.cs.G.BatchIsValid (D.U (t + 1)) ∧
      (info.newlyActive = touchedCompsBatch st.cs (D.U (t + 1)) \ st.activeComps ∧
        Disjoint st.activeComps info.newlyActive ∧
        st'.activeComps = st.activeComps ∪ info.newlyActive ∧
        info.newlyActive.card ≤ 2 * (D.U (t + 1)).length) ∧
      ((components G₀).sum fun C =>
        projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))) ≤
          2 * (D.U (t + 1)).length ∧
      (∀ C ∈ components G₀,
        let U_proj := projCompBatchG st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        let w_proj := projCompBatchWeight st.cs.G (st.cs.compSt C).G (D.U (t + 1))
        info.U_C C = (tildeStepBatch (st.cs.compSt C) (st.ts C) U_proj).1 ∧
        (∀ op ∈ info.U_C C, isDelOrSplit op) ∧
        batchSplitCount (info.U_C C) ≤
          w_proj * (G₀.maxDeg + 1) + ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card ∧
        ((info.U_C C).length : ℝ) ≤ (w_proj : ℝ) *
          ((G₀.maxDeg : ℝ) + 1 + 56 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
        ∀ b : ℤ,
          (st.dyn (C, b)).G.BatchIsValid (info.U_b (C, b)) ∧
          (st'.dyn (C, b)).G = (st.dyn (C, b)).G.applyBatch (info.U_b (C, b)) ∧
          (∀ op ∈ info.U_b (C, b), isDelOrSplit op) ∧
          (info.U_b (C, b)).length ≤ (info.U_C C).length ∧
          batchSplitCount (info.U_b (C, b)) ≤ batchSplitCount (info.U_C C))) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      Hb₀.BatchIsValid Us_b.flatten ∧
      (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
      batchSplitCount Us_b.flatten ≤ splitB) := by
  intro G₀ ℓ₀ cs₀ ts₀ origB splitB
  obtain ⟨hBase, hStep, hCoreFlat⟩ :=
    treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  refine ⟨hBase, hStep, fun C hC b => ?_⟩
  · obtain ⟨hBV_all, hds_all, hsc_all⟩ := hCoreFlat C hC b
    have hR_bound : ∀ t ≤ τ,
        ((((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).R \
          (cs₀.compSt C).R).card : ℝ) ≤
          56 * ((∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      intro t
      induction t with
      | zero =>
        intro _
        have h0_R : ((treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.cs.compSt C).R =
            (cs₀.compSt C).R := rfl
        simp [h0_R]
      | succ s ih =>
        intro hs_le
        have hs_lt : s < τ := hs_le
        have ih' := ih (Nat.le_of_succ_le hs_le)
        have hb_s := hBase s (Nat.le_of_succ_le hs_le)
        have hStep_s := hStep s hs_lt
        set st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
        set st_s1 := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
        have hG₀_s : st_s.cs.G₀ = G₀ := by rw [hb_s.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
        have hI_sC := (hb_s.2.2.2.2.2.2.2.2.1.hCompLSF C (hG₀_s ▸ hC)).1
        have hcomp_sp := compLSFBatch_compSt hb_s.2.2.2.2.2.2.2.2.1 hStep_s.1 (hG₀_s ▸ hC)
        have hstepR := compLSFBatch_compSt_R_le_compN hb_s.2.2.2.2.2.2.2.2.1 hStep_s.1 (hG₀_s ▸ hC)
        have hcomp_step : st_s1.cs.compSt C = (compLSFBatch st_s.cs (D.U (s + 1))).compSt C := rfl
        rw [← hcomp_step, hG₀_s] at hstepR
        have hsq : (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 2 ≤ (Real.log ((G₀.n : ℝ) + 2)) ^ 2 :=
          pow_le_pow_left₀ (by linarith [half_lt_log_add_two (compGraph G₀ C).n])
            (Real.log_le_log (by positivity)
              (by linarith [show ((compGraph G₀ C).n : ℝ) ≤ G₀.n from
                by exact_mod_cast compGraph_n_le hC])) 2
        have hstepR' : ((st_s1.cs.compSt C).R.card : ℝ) ≤ ((st_s.cs.compSt C).R.card : ℝ) +
            56 * ((D.U (s + 1)).length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
          have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 56 * ((D.U (s + 1)).length : ℝ))
          linarith
        have hS0_s : (cs₀.compSt C).R ⊆ (st_s.cs.compSt C).R := (hb_s.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1.hR_sub
        have h_ss_R_sub : (st_s.cs.compSt C).R ⊆ (st_s1.cs.compSt C).R := hcomp_step ▸ hcomp_sp.2.2.2.1
        have hdiff_le : (((st_s1.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) ≤
            (((st_s.cs.compSt C).R \ (cs₀.compSt C).R).card : ℝ) +
              (((st_s1.cs.compSt C).R.card : ℝ) - ((st_s.cs.compSt C).R.card : ℝ)) := by
          have c1 := Finset.card_le_card hS0_s; have c2 := Finset.card_le_card h_ss_R_sub
          rw [Finset.card_sdiff_of_subset hS0_s, Finset.card_sdiff_of_subset (hS0_s.trans h_ss_R_sub),
            Nat.cast_sub c1, Nat.cast_sub (c1.trans c2)]
          linarith
        have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by ext x; simp [Finset.mem_Icc]; omega
        rw [hIcc, Finset.sum_insert (by simp), add_comm, Nat.cast_add]
        linarith [show 56 * (((∑ x ∈ Finset.Icc 1 s, (D.U x).length : ℕ) : ℝ) +
            ((D.U (s + 1)).length : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 =
            56 * ((∑ x ∈ Finset.Icc 1 s, (D.U x).length : ℕ) : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 +
            56 * ((D.U (s + 1)).length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 by ring]
    have hlogG_pos : (0 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := by
      linarith [half_lt_log_add_two G₀.n]
    have hlogN_pos : (0 : ℝ) < Real.log ((N : ℝ) + 2) := by
      linarith [half_lt_log_add_two N]
    have hlog_sq_le : (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := by
      refine pow_le_pow_left₀ hlogG_pos.le (Real.log_le_log (by positivity) ?_) 2
      have : (G₀.n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlog2_pos : (0 : ℝ) < (Real.log ((N : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlogN_pos
    have hR_le : ((((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cs.compSt C).R \
        (cs₀.compSt C).R).card : ℝ) ≤ 56 * (M : ℝ) / (k : ℝ) := by
      have hr := hR_bound τ (le_refl τ)
      have hr' : ((((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cs.compSt C).R \
          (cs₀.compSt C).R).card : ℝ) ≤
          56 * ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) *
            (Real.log ((N : ℝ) + 2)) ^ 2 :=
        le_trans hr (mul_le_mul_of_nonneg_left hlog_sq_le (by positivity))
      have h1 : 56 * ((∑ s ∈ Finset.Icc 1 τ, (D.U s).length : ℕ) : ℝ) ≤
          56 * SparseCoreTool.updateThreshold k M N := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hlog2_pos.le
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have heq : 56 * SparseCoreTool.updateThreshold k M N *
          (Real.log ((N : ℝ) + 2)) ^ 2 = 56 * (M : ℝ) / (k : ℝ) := by
        rw [SparseCoreTool.updateThreshold]
        field_simp [hlog2_pos.ne', hk_pos.ne']
      exact le_trans hr' (heq ▸ h2)
    have hfloor : ∑ s ∈ Finset.Icc 1 τ, (D.U s).length ≤
        Nat.floor (SparseCoreTool.updateThreshold k M N) := Nat.le_floor hThresh
    have hceil : (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cs.compSt C).R \
        (cs₀.compSt C).R).card ≤ Nat.ceil (56 * (M : ℝ) / (k : ℝ)) := by
      exact_mod_cast le_trans hR_le (Nat.le_ceil _)
    exact ⟨hBV_all, hds_all, le_trans hsc_all (Nat.add_le_add (Nat.mul_le_mul_right _ hfloor) hceil)⟩

/-- Component-wise quotient batch-length bound using `min G₀.n (G₀.m + 1)` instead of `G₀.n`,
since every connected component `C ∈ components G₀` satisfies `(compGraph G₀ C).n ≤ G₀.m + 1`. -/
lemma treeRunSeq_U_C_len_le_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (j : ℕ) :
    let G₀ := D.G 0
    ∀ t < τ, ∀ C ∈ components G₀,
      (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
          (D.U (t + 1))).U_C C).length : ℝ) ≤
        (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G
          (D.U (t + 1)) : ℝ) *
          ((G₀.maxDeg : ℝ) + 1 + 56 * (Real.log (((min G₀.n (G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2) := by
  intro G₀ t ht C hC
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : (initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j |>.compSt C).G₀ = compGraph G₀ C ∧
      (initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j |>.compSt C).G = compGraph G₀ C ∧
      (initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j |>.compSt C).W_init.biUnion
        (inducedEdges (initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j |>.compSt C).RF.F) =
        (initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j |>.compSt C).RF.F.E := by
    set ℓs := safeLen G₀ (D.ℓ 0)
    have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
      rw [show ℓs e = D.ℓ 0 e from safeLen_eq_of_mem (D.ℓ 0) heG]
      exact hℓ₀ e heG
    have hsp := initLSF_spec hLSST (compGraph_isValid hG₀ hC) (compGraph_nonempty hC) hℓC
      (fun e _ => mwuWeights_pos oracle C_lsst (compGraph G₀ C) ℓs k j e) hk_real
    exact ⟨hsp.1, hsp.2.1, hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  have hb := hBase t (Nat.le_of_lt ht)
  have hs := hStep t ht
  have hG₀_t : (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G₀ = G₀ := by
    rw [hb.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hI_t := hb.2.2.2.2.2.2.2.2.1
  have hCI₀ := (hI₀.hCompLSF C hC).1
  have hD_C := (hb.2.2.2.2.2.2.2.2.2.2.2.2 C hC).1
  have hT_C := (hb.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1
  have htw := tildeStepBatch_projCompBatchG_spec hCI₀ hS₀C_spec.2.2 (D.U (t + 1))
    hI_t (hG₀_t ▸ hC) hD_C hT_C hs.1
  have htd_lenR := htw.2.1
  rw [hS₀C_spec.1, hS₀C_spec.2.1] at htd_lenR
  have hn_le : (compGraph G₀ C).n ≤ min G₀.n (G₀.m + 1) := compGraph_n_le_min hG₀ hC
  have hd_le : (compGraph G₀ C).maxDeg ≤ G₀.maxDeg := compGraph_maxDeg_le hC
  have hlogC : Real.log (((compGraph G₀ C).n : ℝ) + 2) ≤
      Real.log (((min G₀.n (G₀.m + 1) : ℕ) : ℝ) + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : ((compGraph G₀ C).n : ℝ) ≤ ((min G₀.n (G₀.m + 1) : ℕ) : ℝ) := by exact_mod_cast hn_le
    linarith
  have hlogC_nn : 0 ≤ Real.log (((compGraph G₀ C).n : ℝ) + 2) := by
    linarith [half_lt_log_add_two (compGraph G₀ C).n]
  have hsq : (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 2 ≤
      (Real.log (((min G₀.n (G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hlogC_nn hlogC 2
  have hd_r : ((compGraph G₀ C).maxDeg : ℝ) ≤ G₀.maxDeg := by exact_mod_cast hd_le
  have hU_nn : (0 : ℝ) ≤ projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.G
      ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.compSt C).G (D.U (t + 1)) :=
    Nat.cast_nonneg _
  exact le_trans htd_lenR (mul_le_mul_of_nonneg_left (by linarith) hU_nn)

end

end MinCostFlow.SparseCore
