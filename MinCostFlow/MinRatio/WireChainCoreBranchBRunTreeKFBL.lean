module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunFactsKFBL
import MinCostFlow.MinRatio.SelectUpdateModel
import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# The tree state after a run of Branch B (`WireChainCoreBranchBRunTreeKFBL`)

Branch B does not rebuild level `0` (the premise `noFire` of the start). So the root graph of the
model after the update is the root graph with the batch applied (`X_G0`), and the field `phase`
of `BranchBSufOutKFBL` follows from the tree state that the suffix leaves (`own_phase`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace BranchBRunKFBL

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

variable (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The root graph of the model after the update of Branch B is the old root graph with the
internal batch applied: level `0` does not fire (`noFire`), so the update does not rebuild it
(`level0Rebuilt_update_iff`), and then `algorithm1_update_G0_and_g` gives the graph. -/
theorem X_G0 : H.X.G 0 = H.G1 := by
  rw [H.modelEq, H.G1_eq, H.Uint_eq, H.gVec_eq, H.lVec_eq]
  have hNo := H.start.noFire
  rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
      (fun e' => updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
        ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
      (fun e' => updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
        ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    with ⟨h1, _, _⟩ | ⟨_, h2, _⟩
  · have hR := level0Rebuilt_update_iff cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
      (fun e' => updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
        ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
      (fun e' => updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
        ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    unfold level0Rebuilt at hR
    rw [h1] at hR
    exact absurd (of_decide_eq_true hR.symm) (by simpa using hNo)
  · exact h2

/-- The field `phase` of `BranchBSufOutKFBL` at the end of a run of Branch B. The suffix leaves
the tree state on the graph `G1` with the tree edges `Fp ∪ newE` and the pending set
`N \ inserted`, where `N = G1.E \ (model.chain.G 0).E`. Here `G1` is the root graph of the model
(`X_G0`), `Fp ∪ newE` is its chain tree (the split), and the pending set is empty, since an edge
of `G1` that no update of the batch inserts is an edge of the old root graph
(`mem_pre_of_mem_applyBatch`). -/
theorem own_phase :
    TreeSyncPhaseAt L tok root uIntBuf H.nextHeap tok.rootGraph
      ((alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G 0)
      (alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m)
            model.extℓ)).chain.toTreeChain.chainTree.E
      H.canonVal B R ∅ H.curTree H.curTreeTok H.offCnt H.out.mem := by
  have hX : H.X = (alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  obtain ⟨_, _, _, _, hPh, _⟩ := H.suf
  have hTree := H.split.2.2.2.2.1
  have hEmpty : (H.G1.E \ (model.chain.G 0).E) \
      (batchInsertedEdges H.Uint).toFinset = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    simp only [Finset.mem_sdiff, List.mem_toFinset] at he
    obtain ⟨⟨heG, heO⟩, heI⟩ := he
    rw [H.G1_eq] at heG
    exact heO (Chain.mem_pre_of_mem_applyBatch heG fun u hu hIu =>
      heI ((mem_batchInsertedEdges_iff _ _).2 ⟨u, hu, hIu⟩))
  rw [hEmpty, hTree, ← X_G0 H] at hPh
  rw [← hX]
  exact hPh

end BranchBRunKFBL

end MinCostFlow.MinRatio
