module

public import MinCostFlow.MinRatio.WireChainCoreBranchBGraphKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTreeKeepKFBL
public import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import WordRAM.Tactic

/-!
# The tree state of Branch B on the new root graph (`WireChainCoreBranchBNewRootKFBL`)

Sync 1 leaves the tree state on the old root graph `G0` for the forest `F1`, the chain tree
without the deleted names (`wireBranchBPrefixKFBL_runs`). The later syncs of Branch B run on the
new root graph `G0'`, after the front, the loop and the exit. `branchBTreePhase_newRoot` moves the
tree state there with `TreeSyncPhaseAt.change_graph`, with the new names `N` as the deferred set.

The words that the tree state reads keep their values from the memory after Sync 1
(`branchBTreeWords_keep` gives this from the frames of the steps). Above `uIntBuf` these words lie
below the select slots, or from the end `h0` of the fixed part of the heap of Branch B on: the
tree words of Sync 1 lie in its own part of the heap or in the old tree, and each record of an
edge of `G0` off `F1` is a record of a cut edge, which Sync 1 wrote from `h0` on, or an old
record, which lies below `uIntBuf` (`treeSyncPhaseAt_of_rep` at the memory of the solver).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The tree state after Sync 1 (`hPh`, at `memS1`, for the forest `F \ deleted` of the old root
graph `G0`) moves to the new root graph `G0'` at a memory `mem'` that keeps the words of the tree
state (`hKeep`), with the new names `N` as the deferred set. The heap pointer of the result is any
`heapX' ≥ hS1` above the records of the new names. -/
theorem branchBTreePhase_newRoot
    {L P m V psi k epsExp drainUnit root uIntBuf heap hS1 heapX' rg offCnt : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 memS1 mem' : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0' : MGraph} {U_int : List Update} {N : Finset ℕ} {canonVal canonVal' : ℕ → PathEdgeValue}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hOldSub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap)
    (hGn : (model.chain.G 0).n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf hS1 rg (model.chain.G 0)
      (model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges U_int).toFinset) canonVal B R ∅
      curTree curTreeTok offCnt memS1)
    (hTreeFoot : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
        curTreeTok a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a ∧ a < hS1))
    (hCutRec : ∀ ei ∈ model.chain.toTreeChain.chainTree.E, Update.delete ei ∈ U_int →
      heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ memS1 (tok.edgeRecords + ei))
    (hOldRec : ∀ ei ∈ (model.chain.G 0).E, ei ∉ model.chain.toTreeChain.chainTree.E →
      memS1 (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei))
    (hKeep : ∀ a < hS1,
      (a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ (9 ≤ tok.tag a ∧ tok.tag a ≤ 16) ∨
        tok.tag a = 18) →
      (uIntBuf ≤ a → a < heap ∨ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) →
      (∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      mem' a = memS1 a)
    (hHeapLe : hS1 ≤ heapX')
    (hN : G0'.n = (model.chain.G 0).n) (hG' : DynGraphAt mem' rg G0'.n tok.rootECap G0')
    (hNewE : ∀ ei ∈ G0'.E, ei ∈ (model.chain.G 0).E ∨ ei ∈ N)
    (hFSub : model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges U_int).toFinset ⊆ G0'.E)
    (hEnds : ∀ e ∈ model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges U_int).toFinset,
      G0'.tail e = (model.chain.G 0).tail e ∧ G0'.head e = (model.chain.G 0).head e)
    (hCanonOld : ∀ ei ∈ (model.chain.G 0).E, ei ∈ G0'.E → canonVal' ei = canonVal ei)
    (hCanonNew : ∀ ei ∈ N, (canonVal' ei).forward = true ∧ |(canonVal' ei).gradient| ≤ B ∧
      |(canonVal' ei).length| ≤ B ∧ |(canonVal' ei).flow| ≤ B ∧ |(canonVal' ei).detector| ≤ B)
    (hCapN : ∀ ei ∈ N, ei < tok.intCap)
    (hNewSlot : ∀ ei ∈ N, mem' (tok.slots + ei) = 0)
    (hNewRec : ∀ ei ∈ N,
      PathEdgeAt mem' (mem' (tok.edgeRecords + ei)) 4 L (some (canonVal' ei)))
    (hNewRecLoc : ∀ ei ∈ N, hS1 ≤ mem' (tok.edgeRecords + ei) ∧
      mem' (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapX')
    (hNewDisj : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ →
      mem' (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ mem' (tok.edgeRecords + e₂) ∨
      mem' (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ mem' (tok.edgeRecords + e₁)) :
    TreeSyncPhaseAt L tok root uIntBuf heapX' rg G0'
      (model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges U_int).toFinset) canonVal' B R N
      curTree curTreeTok offCnt mem' := by
  classical
  have hRep0' := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0'
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _⟩ := hTags0
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := hFootLt x (Or.inl (hOwn x h))
  -- the old records lie below `uIntBuf`
  obtain ⟨_, hPh0, _⟩ := treeSyncPhaseAt_of_rep (heapX := uIntBuf) (mem := mem0) hRep0 hNum0
    hOffInv0 hOffBd0 hOldSub hFootLt le_rfl (fun _ _ _ => rfl) (fun _ _ => rfl)
  refine hPh.change_graph hRep0 hFootLt hGn hHeapLe hN hG' hNewE hFSub hEnds hCanonOld
    hCanonNew hCapN hNewSlot hNewRec (fun ei hei => ⟨le_trans le_rfl (hNewRecLoc ei hei).1,
      (hNewRecLoc ei hei).2⟩) hNewDisj
    (fun a => a < heap ∨ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a)
    (fun a ha hf => ?_) (fun ei hei hnot j hj hge => ?_)
    (fun a ha h1 h2 h3 => hKeep a ha h1 h2 h3)
  · rcases hTreeFoot a hf with h | h
    · exact absurd (hLt (by rw [hT16 a h]; decide)) (by omega)
    · exact Or.inr h.1
  · by_cases hF : ei ∈ model.chain.toTreeChain.chainTree.E
    · have hdel : Update.delete ei ∈ U_int := by
        by_contra hc
        exact hnot (Finset.mem_sdiff.mpr ⟨hF, fun h =>
          hc ((mem_batchDeletedEdges_iff U_int ei).mp (List.mem_toFinset.mp h))⟩)
      exact Or.inr (by have := hCutRec ei hF hdel; omega)
    · have h0 := (hPh0.recLoc ei hei hF j hj).2.2.2
      rw [hOldRec ei hei hF] at hge
      omega

end MinCostFlow.MinRatio
