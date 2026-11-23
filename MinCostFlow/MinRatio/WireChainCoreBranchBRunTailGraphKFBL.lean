module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailBaseKFBL
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
import MinCostFlow.LSF.Walks
import WordRAM.Tactic

/-!
# The graph facts of the suffix of Branch B on a head (`WireChainCoreBranchBRunTailGraphKFBL`)

The suffix of Branch B runs on the new root graph `G1` (the old root graph with the internal
batch applied). Its run lemma `wireBranchBSuffixKFBL_runs` asks for facts on `G1`, on the forest
`F1` of the tree after Sync 1, on the new chain tree, and on the caps of the names. This file
proves them from the head of a run:

* `G1_fresh`, `G1_n`, `edgeOnly`: the names of `G1` and its vertex count, and the internal batch
  has only edge updates (`refreshBatch_edge_dichotomy`);
* `applyBatch_ends_of_noInsert`: an edge batch keeps the vertices, and the ends of an edge that
  it does not insert;
* `forest_F1`: `{G1 with E := F1}` is a forest, a subgraph of the old chain tree (a forest by
  `SolverWireInv`) with the same ends;
* `forest_new`, `newE_sub`: the new chain tree `Fp ∪ newE` on `G1` is a forest and lies in `G1`
  (`UpdateCoreModelInv`, with `X_G0`);
* `delCap`, `oldCap`, `insCap`: the deleted forest edges, the old forest edges and the inserted
  names are below `tok.rootECap`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- A batch of edge updates keeps the vertex set, and the ends of an edge that no update of the
batch inserts. -/
theorem applyBatch_ends_of_noInsert {e : ℕ} :
    ∀ (U : List Update) (G : MGraph), (∀ u ∈ U, IsEdgeUpdate u) → (∀ u ∈ U, ¬ u.Inserts e) →
      (G.applyBatch U).V = G.V ∧ (G.applyBatch U).tail e = G.tail e ∧
        (G.applyBatch U).head e = G.head e
  | [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | u :: us, G, hE, hI => by
    have ih := applyBatch_ends_of_noInsert us (G.applyUpdate u)
      (fun v hv => hE v (List.mem_cons_of_mem _ hv)) (fun v hv => hI v (List.mem_cons_of_mem _ hv))
    change ((G.applyUpdate u).applyBatch us).V = G.V ∧
      ((G.applyUpdate u).applyBatch us).tail e = G.tail e ∧
      ((G.applyUpdate u).applyBatch us).head e = G.head e
    rw [ih.1, ih.2.1, ih.2.2]
    have hu := hE u (by simp)
    have hiu := hI u (by simp)
    cases u with
    | insert e' a b =>
      have hne : e ≠ e' := fun h => hiu (by simp [Update.Inserts, h])
      exact ⟨rfl, Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
    | delete _ => exact ⟨rfl, rfl, rfl⟩
    | split _ _ _ _ => exact absurd hu (by simp [IsEdgeUpdate])

namespace BranchBRunHeadKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The names of the new root graph `G1` and the internal batch: `G1` has the new names of the
external edges (`FreshInv`), and the internal batch has only edge updates. -/
theorem G1_fresh :
    FreshInv model.extG Hd.G1
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.1 ∧
    ∀ u ∈ Hd.Uint, IsEdgeUpdate u := by
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := Hd.start.rep0
  obtain ⟨_, hFr1, hEdge, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 Hd.start.refresh
  rw [Hd.G1_eq, Hd.Uint_eq]
  exact ⟨hFr1, hEdge⟩

/-- The internal batch has only edge updates (the premise `hEdgeOnly` of the suffix). -/
theorem edgeOnly : ∀ u ∈ Hd.Uint, IsEdgeUpdate u := (G1_fresh Hd).2

/-- The vertex count of `G1` is the one of the external graph (the premise `hGn`). -/
theorem G1_n : Hd.G1.n = model.extG.n := by
  unfold MGraph.n; rw [← (G1_fresh Hd).1.hV]

/-- Every name that the internal batch inserts is fresh: it is not an edge of the old root
graph. -/
theorem ins_fresh {e : ℕ} (he : e ∈ (model.chain.G 0).E) : ∀ u ∈ Hd.Uint, ¬ u.Inserts e := by
  intro u hu hue
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := Hd.start.rep0
  obtain ⟨_, _, _, _, _, _, hInsFresh, _⟩ :=
    translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh hFreshInv0 Hd.start.refresh.1
  rw [Hd.Uint_eq] at hu
  have hlo : model.nextFresh ≤ e := (hInsFresh u hu e hue).1
  have := hFreshInv0.hLtFresh e he
  omega

/-- The ends of `G1` on the edges of the old root graph: the batch keeps the vertices, and the
ends of every edge of the old root graph, since it inserts only fresh names. -/
theorem G1_ends {e : ℕ} (he : e ∈ (model.chain.G 0).E) :
    Hd.G1.V = (model.chain.G 0).V ∧ Hd.G1.tail e = (model.chain.G 0).tail e ∧
      Hd.G1.head e = (model.chain.G 0).head e := by
  rw [Hd.G1_eq]
  exact applyBatch_ends_of_noInsert _ _ (edgeOnly Hd) (ins_fresh Hd he)

/-- **`hForest` of the suffix.** The tree after Sync 1 on the new root graph is a forest: it is a
subgraph of the old chain tree, a forest by `SolverWireInv`, with the same vertices and ends. -/
theorem forest_F1 : ({ Hd.G1 with E := Hd.F1 } : MGraph).IsForest := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, _⟩ := Hd.start.rep0
  obtain ⟨_, _, ⟨hForestF, _⟩, _, _⟩ := hWire0
  have hOldSub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E :=
    Hd.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hF1 : Hd.F1 ⊆ model.chain.toTreeChain.chainTree.E := by
    rw [Hd.F1_eq]; exact Finset.sdiff_subset
  have hEnds (e : ℕ) (he : e ∈ Hd.F1) := G1_ends Hd (hOldSub (hF1 he))
  have hV : Hd.G1.V = (model.chain.G 0).V := by
    obtain ⟨_, _, _, _, hFreshInv0, _⟩ := Hd.start.rep0
    rw [← (G1_fresh Hd).1.hV, hFreshInv0.hV]
  refine LSF.isForest_subgraph hForestF ⟨?_, hF1, fun e he => ?_⟩ fun e he => ?_
  · show Hd.G1.V ⊆ (model.chain.G 0).V
    rw [hV]
  · exact ⟨(hEnds e he).2.1, (hEnds e he).2.2⟩
  · have h := hForestF.1 e (hF1 he)
    show Hd.G1.tail e ∈ Hd.G1.V ∧ Hd.G1.head e ∈ Hd.G1.V
    rw [(hEnds e he).2.1, (hEnds e he).2.2, hV]
    exact h

/-- The model after the update is the chain of `alg2PreResetState`. -/
theorem X_eq : Hd.X = (alg2PreResetState cfg model U
    (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
    (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
  rw [Hd.modelEq, Hd.gVec_eq, Hd.lVec_eq]

/-- **`hNewForest` and `hNewSub` of the suffix.** The chain tree of the model after the update is
a forest on its root graph `G1` that lies in `G1` (`UpdateCoreModelInv`). -/
theorem forest_new :
    ({ Hd.G1 with E := Hd.X.toTreeChain.chainTree.E } : MGraph).IsForest ∧
      Hd.X.toTreeChain.chainTree.E ⊆ Hd.G1.E := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hNewF, _, hNewSub, _⟩ := Hd.start.modelInv
  rw [← X_eq Hd] at hNewF hNewSub
  rw [← X_G0 Hd]
  exact ⟨hNewF, hNewSub⟩

include Hd in
/-- The edges of the old root graph lie below `tok.rootECap` (the root graph of `SolverWireInv`
has this edge cap). -/
theorem G0_cap {e : ℕ} (he : e ∈ (model.chain.G 0).E) : e < tok.rootECap := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, _⟩ := Hd.start.rep0
  obtain ⟨_, hRG, _⟩ := hWire0
  exact hRG.2.2.1 e he

/-- **`hInsCap` of the suffix.** The inserted names lie below `tok.rootECap`
(`BatchWithinCaps` of `UpdateCoreModelInv`). -/
theorem insCap : ∀ e ∈ batchInsertedEdges Hd.Uint, e < tok.rootECap := by
  intro e he
  obtain ⟨_, _, _, _, _, _, _, _, _, hBW, _⟩ := Hd.start.modelInv
  obtain ⟨u, hu, hue⟩ := (mem_batchInsertedEdges_iff _ e).mp he
  rw [Hd.Uint_eq] at hu
  have h := hBW u hu
  cases u with
  | insert e' a b =>
    simp only [Update.Inserts] at hue
    subst hue
    exact h
  | delete _ => simp [Update.Inserts] at hue
  | split _ _ _ _ => simp [Update.Inserts] at hue

/-- **`hDelCap` of the suffix.** The edges that the finished levels delete from their forests
were edges of the old forests, which lie in the old root graph. -/
theorem delCap : ∀ j < Hd.i₀, ∀ e ∈ (Hd.D j).fDel, e < tok.rootECap := by
  intro j hj e he
  have hInv := Hd.loop.2.2.2.2.1
  have hi := Hd.loop.2.2.1
  have hsm := hInv.slotModel j hj
  have hFin := hsm.2.2.2.1
  have he' : e ∈ (Hd.D j).fDel.toFinset := List.mem_toFinset.mpr he
  rw [hFin] at he'
  have hOld := (Finset.mem_sdiff.mp he').1
  have hSc : Hd.st0.scState j = model.chain.scState j := by rw [Hd.st0_eq]
  have hBr : Hd.st0.bran j = model.chain.bran j := by rw [Hd.st0_eq]
  rw [hSc, hBr] at hOld
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLsf, _⟩ := Hd.start.modelInv
  exact G0_cap Hd ((hLsf j (by omega)).1 hOld)

/-- **`hOldCap` of the suffix.** The edges of the old forests of the levels from `fr` on lie in
the old root graph, so below `tok.rootECap`. -/
theorem oldCap : ∀ e ∈ graphListEdgeUnion
    (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []), e < tok.rootECap := by
  intro e he
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLsf, hLast, _⟩ := Hd.start.modelInv
  split_ifs at he with hfr
  · obtain ⟨F, hF, heF⟩ := mem_graphListEdgeUnion.mp he
    refine G0_cap Hd ?_
    unfold chainSuffixForests at hF
    rcases List.mem_append.mp hF with hF | hF
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
      have ht' := List.mem_range.mp ht
      have hSc : Hd.st0.scState = model.chain.scState := by rw [Hd.st0_eq]
      have hBr : Hd.st0.bran = model.chain.bran := by rw [Hd.st0_eq]
      rw [hSc, hBr] at heF
      exact (hLsf (Hd.fr + t) (by omega)).1 heF
    · rw [List.mem_singleton] at hF
      subst hF
      have hLs : Hd.st0.lastLSFs = model.chain.lastLSFs := by rw [Hd.st0_eq]
      have hLb : Hd.st0.lastBran = model.chain.lastBran := by rw [Hd.st0_eq]
      rw [hLs, hLb] at heF
      exact hLast heF
  · simp [mem_graphListEdgeUnion] at he

end BranchBRunHeadKFBL

end MinCostFlow.MinRatio
