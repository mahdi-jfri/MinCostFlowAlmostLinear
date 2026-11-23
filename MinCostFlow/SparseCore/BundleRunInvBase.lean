module

public import MinCostFlow.SparseCore.BundleStepBounds

/-!
# Tools for the run invariant of a branch on bundle graphs

This file collects what `bundleRunSeq_inv` (in `BundleRunInv.lean`) needs besides the step
lemmas of `BundleStepBounds.lean`.

* The proposition types `BundleRunSeqStageInvStmt` and `InitBundleTreeVertexSumLeStmt`
  for the bundle-stage invariant and initial bundle count (proved in `BundleStage.lean` and
  `BundleInitCount.lean`).
* The orders of `OrderedUpTo` as rotations of any graph equal to the input graph
  (`orderedUpTo_rot_at`, `orderedUpTo_rot_step`).
* At the start no component has extra edges (`initBundleTree_extraEdges`): each non-forest edge
  of a component lies in the bundle graph of its bucket.
* A batch of deletions and splits only removes edges, and an edge it removes is deleted by one of
  its updates.
* The spanner bounds of Theorem 8.2 for one bundle graph (`bundleBucket_theorem_8_2`), in the form
  that the run invariant states.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The statement of `bundleRunSeq_stage_inv` (the bundle stage of the run), with one more
clause in the step part: a bundle loses only edges that the input batch deletes. This clause
follows from the local count `bundleCompStep_local` of the same piece. -/
abbrev BundleRunSeqStageInvStmt : Prop :=
  ∀ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (_hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (_hk : 1 ≤ k) (D : DynamicInstance)
    (_hG₀ : (D.G 0).IsValid) (_hV₀ : (D.G 0).V.Nonempty)
    (_hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (_hD : D.IsValid τ) (_hN : (D.G 0).n ≤ N)
    (_hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (ord : ℕ → ℕ → List End) (_hOrd : OrderedUpTo D τ 2 ord) (j : ℕ),
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
        (st.bun (C, b)).edges \ (st'.bun (C, b)).edges ⊆ batchDeletes (D.U (t + 1)))) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := (st₀.bun (C, b)).graph
      let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
      Hb₀.BatchIsValid Us_b.flatten ∧
      (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
      batchSplitCount Us_b.flatten ≤ splitB ∧
      Hb₀.maxDeg ≤ k)

/-- The statement of `initBundleTree_vertex_sum_le` (the vertex and edge counts of the initial
bundle graphs). -/
abbrev InitBundleTreeVertexSumLeStmt : Prop :=
  ∀ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (_hLSST : HasLSSTSpec oracle C_lsst)
    (k M N : ℕ) (_hk : 1 ≤ k) (G₀ : MGraph) (_hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ) (B_bound : ℕ)
    (_hB : ∀ C ∈ components G₀,
      ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤
        B_bound),
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    k * ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).vertices.card) ≤ k * B_bound * st₀.cs.RF.R.card + 2 * G₀.m ∧
    (∀ C ∈ components G₀, C ∉ largeComps k G₀ → ∀ b : ℤ, (st₀.bun (C, b)).vertices.card ≤ 11) ∧
    ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).edges.card) ≤ G₀.m

/-- Casting a rotation along an equality of graphs keeps its order. -/
theorem rotation_cast_order {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

/-- Under `OrderedUpTo`, a graph equal to the input graph at a stage `t ≤ τ` has a rotation with
the order of that stage. -/
theorem orderedUpTo_rot_at {D : DynamicInstance} {τ β : ℕ} {ord : ℕ → ℕ → List End}
    (hOrd : OrderedUpTo D τ β ord) {t : ℕ} (ht : t ≤ τ) {G : MGraph} (hG : G = D.G t) :
    ∃ ρ : Rotation G, ρ.order = ord t := by
  obtain ⟨ρ, hρ, -⟩ := hOrd
  subst hG
  exact ⟨ρ t, hρ t ht⟩

/-- Under `OrderedUpTo`, a graph equal to the input graph at a stage `t < τ` has rotations before
and after the next batch with the orders of these stages, and the batch is ordered. -/
theorem orderedUpTo_rot_step {D : DynamicInstance} {τ β : ℕ} {ord : ℕ → ℕ → List End}
    (hOrd : OrderedUpTo D τ β ord) {t : ℕ} (ht : t < τ) {G : MGraph} (hG : G = D.G t) :
    ∃ (ρ : Rotation G) (σ : Rotation (G.applyBatch (D.U (t + 1)))),
      ρ.order = ord t ∧ σ.order = ord (t + 1) ∧ RotationBatch β (D.U (t + 1)) ρ σ := by
  obtain ⟨ρ, hρ, hB⟩ := hOrd
  obtain ⟨h, hrb⟩ := hB t ht
  subst hG
  exact ⟨ρ t, h ▸ ρ (t + 1), hρ t ht.le, by rw [rotation_cast_order]; exact hρ (t + 1) ht, hrb⟩

/-- A batch of deletions and splits only removes edges. -/
theorem applyBatch_E_subset_of_delOrSplit :
    ∀ (G : MGraph) (U : List Update), (∀ op ∈ U, isDelOrSplit op) → (G.applyBatch U).E ⊆ G.E
  | _, [], _ => by simp [MGraph.applyBatch]
  | G, u :: rest, h => by
    have ih := applyBatch_E_subset_of_delOrSplit (G.applyUpdate u) rest
      (fun op hop => h op (List.mem_cons_of_mem _ hop))
    refine ih.trans ?_
    have hu := h u List.mem_cons_self
    rcases u with ⟨e, a, b⟩ | e | ⟨v, v', St, Sh⟩
    · exact absurd hu id
    · exact Finset.erase_subset _ _
    · exact Finset.Subset.rfl

/-- An edge that a batch removes is deleted by one of its updates. -/
theorem exists_delete_of_mem_sdiff_applyBatch :
    ∀ (G : MGraph) (U : List Update) {e : ℕ}, e ∈ G.E → e ∉ (G.applyBatch U).E →
      Update.delete e ∈ U
  | _, [], _, he, hne => by simp [MGraph.applyBatch] at hne; exact absurd he hne
  | G, u :: rest, e, he, hne => by
    by_cases hd : u = Update.delete e
    · subst hd; exact List.mem_cons_self
    refine List.mem_cons_of_mem _ (exists_delete_of_mem_sdiff_applyBatch (G.applyUpdate u) rest
      ?_ hne)
    rcases u with ⟨e', a, b⟩ | e' | ⟨v, v', St, Sh⟩
    · exact Finset.mem_insert_of_mem he
    · exact Finset.mem_erase.mpr ⟨fun h => hd (by rw [h]), he⟩
    · exact he

/-- The initial bundle state of a component and bucket has the given edge set when the order is
the order of a rotation of the initial graph. -/
theorem initBundleFor_edges {cs : CompLSFState} {ord : ℕ → List End} {C_lsst : ℝ}
    {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ cs) {ρ : Rotation cs.G} (hρ : ρ.order = ord)
    (E : Finset ℕ) (k : ℕ) : (initBundleFor cs ord E k).edges = E := by
  have h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      ρ.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold initBundleFor
  rw [dite_eq_left h]
  rfl

/-- At the start no component has extra edges for `initBundleTreeWith`: every non-forest edge of a
component lies in the bundle graph of its bucket. -/
theorem initBundleTreeWith_extraEdges (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k : ℕ} (M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {ord : ℕ → List End} (j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {ρ : Rotation G₀} (hρ : ρ.order = ord)
    {C : Finset ℕ} (hC : C ∈ components G₀) :
    (initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).extraEdges C = ∅ := by
  classical
  set cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j with hcs₀
  have hI₀ : CompLSFInv C_lsst ℓ₀ cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hbasic := initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC
  dsimp only at hbasic
  rw [← hcs₀] at hbasic
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  unfold BundleTreeState.extraEdges at he
  change e ∈ ((cs₀.compSt C).G.E \ (cs₀.compSt C).RF.F.E) \
    ((((coreGraph G₀ cs₀.lsf).E.filter fun e =>
        (coreGraph G₀ cs₀.lsf).tail e ∈ C).image fun e =>
          bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)).biUnion fun b =>
      (initBundleFor cs₀ ord (bucketCoreEdges (coreGraph G₀ cs₀.lsf)
        (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) C b) k).edges) at he
  rw [Finset.mem_sdiff] at he
  obtain ⟨heX, hnB⟩ := he
  apply hnB
  have hC' : C ∈ components cs₀.G₀ := hC
  have heCore : e ∈ cs₀.G.E \ cs₀.RF.F.E := compLSF_comp_sdiff_sub hI₀ hC' heX
  have heC : e ∈ compEdgeSet G₀ C := by
    have h := (Finset.mem_sdiff.mp heX).1
    rw [hbasic.2.1] at h
    exact h
  have hv : G₀.tail e ∈ (cs₀.compSt C).G.V := by
    rw [hbasic.2.1]
    exact (mem_compEdgeSet_endpoints hG₀ hC heC).2.1
  have hroot : cs₀.RF.root (G₀.tail e) ∈ C := by
    have hIC := (hI₀.hCompLSF C hC').1
    rw [compLSF_RF_root_eq hI₀ hC' hv]
    have h := lsfInv_R_sub_V hIC (rootedForest_root_spec (lsfInv_to_RS hIC) hv).1
    rw [hbasic.2.1] at h
    exact h
  have heC₀ : e ∈ (coreGraph G₀ cs₀.lsf).E := heCore
  have htail : (coreGraph G₀ cs₀.lsf).tail e ∈ C := hroot
  have hρ' : ∃ ρ' : Rotation cs₀.G, ρ'.order = ord := ⟨ρ, hρ⟩
  obtain ⟨ρ', hρ'⟩ := hρ'
  refine Finset.mem_biUnion.mpr ⟨bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e),
    Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heC₀, htail⟩, rfl⟩, ?_⟩
  rw [initBundleFor_edges hI₀ hρ']
  unfold bucketCoreEdges
  exact Finset.mem_filter.mpr ⟨heC₀, htail, rfl⟩

/-- At the start no component has extra edges: every non-forest edge of a component lies in the
bundle graph of its bucket. -/
theorem initBundleTree_extraEdges
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst) {k : ℕ} (M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {ord : ℕ → List End} (j : ℕ) {ρ : Rotation G₀} (hρ : ρ.order = ord)
    {C : Finset ℕ} (hC : C ∈ components G₀) :
    (initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).extraEdges C = ∅ :=
  initBundleTreeWith_extraEdges (initLSFOnline oracle C_lsst) L sparsify M N hk hG₀ hV₀ hℓ₀ j
    (initLSFOnline_isValidLSFInitFor hLSST k j) hρ hC

/-- Theorem 8.2 (page 26) for the spanner of one bundle graph, in the form of the run invariant:
the initial size and cost, the stage invariants with the size bound in the current vertex count,
the step facts and the cumulative recourse and cost. -/
theorem bundleBucket_theorem_8_2 {Hb₀ : MGraph} {L M splitB τ : ℕ} {P_b : SparsifyParams}
    {sp : MGraph → MGraph → Embedding → SparsifyOut}
    (hV : Hb₀.IsValid) (hL : 1 ≤ L) (hGm : Hb₀.m ≤ M) (hSp : SparsifySpec M P_b sp)
    {Us : List (List Update)} (hlen : Us.length = τ) (hBV : Hb₀.BatchIsValid Us.flatten)
    (hds : ∀ u ∈ Us.flatten, isDelOrSplit u) (hsc : batchSplitCount Us.flatten ≤ splitB) :
    let nMax_b := Hb₀.n + splitB
    let q_b := phaseBase nMax_b L
    let initOut := DynSpanner.init Hb₀ L q_b sp
    let st_b : ℕ → DynSpannerState L := fun t => DynSpanner.runBatchState (L := L) Hb₀ q_b sp Us t
    let res_b : ℕ → StepOut L := fun t => DynSpanner.runBatchStepOut (L := L) Hb₀ q_b sp Us t
    let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
    let Λ_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)
    let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
      P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
    let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
      | some U => ((st_b t').G.batchEnc U : ℝ)
      | none => 0
    ((initOut.state.H.m : ℝ) ≤ P_b.K_s * (Hb₀.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log ((Hb₀.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s) ∧
    ((initOut.cost : ℝ) ≤ P_b.K_t * (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_t +
        (Hb₀.n : ℝ) + (Hb₀.m : ℝ) + (initOut.state.H.m : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) ∧
    (∀ t ≤ τ,
      (st_b t).G.IsSubgraph (st_b t).H ∧
      ((st_b t).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st_b t).G.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log (((st_b t).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
      ((st_b t).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
      Embedding.IsEmbedding (piTotal (st_b t)) (st_b t).G (st_b t).H ∧
      (Embedding.length (piTotal (st_b t)) (st_b t).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st_b t)) (st_b t).G (st_b t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
          (Hb₀.maxDeg : ℝ)) ∧
    (∀ t < τ, ∀ U, Us[t]? = some U →
      res_b t = DynSpanner.update (DynSpanner.runState (L := L) Hb₀ q_b sp Us.flatten
        (batchPrefixLen Us t)) U sp ∧
      (res_b t).state = st_b (t + 1) ∧
      (st_b t).H.BatchIsValid (res_b t).UH ∧
      (st_b t).H.applyBatch (res_b t).UH = (st_b (t + 1)).H ∧
      (res_b t).D ⊆ (st_b (t + 1)).H.E ∧
      (∀ eG ∈ (st_b (t + 1)).G.E, ∀ eH,
        eH ∈ walkEdges (piTotal (st_b (t + 1)) eG) → eH ∉ (res_b t).D →
        eH ∈ walkEdges (piTotal (st_b t) eG))) ∧
    (∀ t ≤ τ,
      (∑ t' ∈ Finset.range t, ((res_b t').UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res_b t').D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res_b t').cost : ℝ) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b * ((Hb₀.maxDeg : ℝ) + 1) *
          Λ_b * encTotal t)) := by
  intro nMax_b q_b initOut st_b res_b Λ_s_b Λ_b E_L_b nRoot_b batchTotal encTotal
  have hthm := DynSpanner.theorem_8_2 hV hL hGm hSp hBV hds hsc
  rcases hthm with ⟨hSp0, hCost0, hStage, hStep82, hCum⟩
  have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase _ L)
  have hSpars := DynSpanner.sparsity_H hV hL hq1 hGm hSp hBV hds
  have hTrace := DynSpanner.batchTrace_spec hV hL hq1 hGm hSp hBV hds
  refine ⟨hSp0, hCost0, ?_, ?_, ?_⟩
  · intro t ht
    have hs := hStage t (le_trans ht hlen.symm.le)
    have hbp_le : batchPrefixLen Us t ≤ Us.flatten.length := by
      have hsp : Us = Us.take t ++ Us.drop t := (List.take_append_drop t Us).symm
      change (Us.take t).flatten.length ≤ Us.flatten.length
      conv_rhs => rw [hsp, List.flatten_append, List.length_append]
      exact Nat.le_add_right _ _
    have htr := hTrace.1 t (le_trans ht hlen.symm.le)
    have hsp_t := hSpars.2 (batchPrefixLen _ t) hbp_le
    dsimp only at hsp_t
    rw [← htr.1, ← htr.2.1] at hsp_t
    exact ⟨hs.2.1, hsp_t, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
  · intro t ht U hget
    exact hStep82 t (lt_of_lt_of_le ht hlen.symm.le) U hget
  · intro t ht
    have hc := hCum t (le_trans ht hlen.symm.le)
    exact ⟨hc.1, hc.2.2.1, hc.2.2.2⟩

end MinCostFlow.SparseCore
