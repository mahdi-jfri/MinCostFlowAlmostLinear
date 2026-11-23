module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailGoalsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBNewRootKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBTreeKeepKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBOwnRestKeepKFBL
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainCoreBatch
import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.SelectUpdateModel
import MinCostFlow.SparseCore.BundleStageBase
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# The tree state on the new root graph after the exit (`WireChainCoreBranchBRunTailPhaseKFBL`)

Proves `BranchBTailPhaseGoalKFBL`, the field `phaseX` of `BranchBRunKFBL` from a head
`BranchBRunHeadKFBL`. The route is `branchBTreePhase_newRoot` on the tree state after Sync 1
(`Hd.pre` at `Hd.memS1`), moving to the new root graph `Hd.G1` at the end memory `Hd.sX.mem`
of the exit with deferred set `Hd.G1.E \ (model.chain.G 0).E`.

Helper lemmas restated on `BranchBRunHeadKFBL`:
* `heap_order`: order of the heap pointers from `uIntBuf` to `Hd.sX.regs 4`;
* `mid_keep`: edge-account words below `Hd.heap2` keep their values from `Hd.sP` to `Hd.sX`;
* `tree_words_keep`: tree-state words below `Hd.hS1` keep their values from `Hd.memS1` to `Hd.sX`;
* `names`: external/internal name correspondence on `(model.chain.G 0)` and `Hd.G1`;
* `X_G0` and `root_graph`: the root graph after the exit is `Hd.G1` at `tok.rootGraph` with
  caps `(Hd.G1.n, tok.rootECap)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

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
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed
      toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
      lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U B R)

/-- The heap pointers of the parts of a head run of Branch B are in order: `uIntBuf`, `heap`,
`hS1`, `heap2`, `sE.regs 4`, and `sX.regs 4`. -/
theorem heap_order :
    uIntBuf ≤ heap ∧ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ Hd.hS1 ∧
    Hd.hS1 + 3 * L ≤ Hd.heap2 ∧ Hd.heap2 ≤ Hd.sE.regs 4 ∧ Hd.sE.regs 4 ≤ Hd.sX.regs 4 := by
  have h1 := Hd.start.uLe
  have h2 := Hd.start.edHeap
  obtain ⟨_, _, _, hh0, _, hS1h, _⟩ := Hd.pre
  obtain ⟨_, _, hF4, _⟩ := Hd.front
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hL4, _⟩ := Hd.loop
  have hX := Hd.exitOut.heapLo
  refine ⟨by omega, hh0, hS1h, ?_, hX⟩
  rw [hF4] at hL4
  omega

/-- Words below `Hd.heap2` with a tag in `9, …, 18` (below `uIntBuf`) or outside the fixed part
of the heap (above `uIntBuf`) keep their values from `Hd.sP` to `Hd.sX` (`branchBMidWords_keep`). -/
theorem mid_keep {a : ℕ} (ha : a < Hd.heap2)
    (hT : a < uIntBuf → 9 ≤ tok.tag a ∧ tok.tag a ≤ 18)
    (hH : uIntBuf ≤ a → heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) :
    Hd.sX.mem a = Hd.sP.mem a := by
  obtain ⟨hU, _, _, _, _⟩ := heap_order Hd
  obtain ⟨_, _, hF4, hFr, _⟩ := Hd.front
  obtain ⟨_, _, _, _, _, _, _, _, hMem, _, _, _, _, _, hLFr, hLFoot, _⟩ := Hd.loop
  have hA := Hd.A_eq
  have hExit := Hd.exitOut.frame
  have hExitHeap := Hd.exitOut.frameHeap
  rw [hA] at hLFr hLFoot hExit hExitHeap
  exact branchBMidWords_keep (oldPtrs := heap + 1 + 12 * cfg.P.d)
    (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) (s := Hd.sF0) (sE := Hd.sE)
    (tokE := Hd.tokE) Hd.start.rep0 Hd.start.meta0 Hd.start.caps0 Hd.start.modelInv
    Hd.start.footLt hU ⟨by omega, by omega, by omega⟩ hFr (by omega)
    (fun a ha h1 h2 h3 h4 => by rw [← hMem]; exact hLFr a ha h1 h2 h3 h4) hLFoot hExit
    hExitHeap a ha hT (fun hu => Or.inr (hH hu))

/-- Words of the tree state below `Hd.hS1` keep their values from `Hd.memS1` (after Sync 1) to
`Hd.sX.mem` (after the exit), by `branchBTreeWords_keep`. -/
theorem tree_words_keep :
    ∀ a < Hd.hS1,
      (a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ (9 ≤ tok.tag a ∧ tok.tag a ≤ 16) ∨
        tok.tag a = 18) →
      (uIntBuf ≤ a → a < heap ∨ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) →
      (∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      Hd.sX.mem a = Hd.memS1 a := by
  obtain ⟨hU, hh0, hS1h, _, _⟩ := heap_order Hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hPreFr, _⟩ := Hd.pre
  obtain ⟨_, _, hF4, hFr, _⟩ := Hd.front
  obtain ⟨_, _, _, _, _, _, _, _, hMem, _, _, _, _, _, hLFr, hLFoot, _⟩ := Hd.loop
  have h0d : 0 < cfg.P.d := Hd.start.modelInv.1.1
  have hLm0 := (Hd.start.meta0.atCaps Hd.start.caps0 0 h0d).2.2.2.1
  have hLm : ∀ a, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ a →
      a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + Hd.ec0 * L →
      tok.tag a = 23 + cfg.P.d := by
    rw [Hd.ec0_eq]
    simpa only [Nat.add_zero] using hLm0
  have hA := Hd.A_eq
  have hExit := Hd.exitOut.frame
  have hExitHeap := Hd.exitOut.frameHeap
  rw [hA] at hLFr hLFoot hExit hExitHeap
  exact branchBTreeWords_keep (oldPtrs := heap + 1 + 12 * cfg.P.d)
    (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) (sP := Hd.sP) (s := Hd.sF0)
    (sE := Hd.sE) (out := Hd.sX) (tokE := Hd.tokE) Hd.start.rep0 Hd.start.meta0 Hd.start.caps0
    Hd.start.modelInv Hd.start.footLt hU hh0 (by omega) ⟨by omega, by omega, by omega⟩ hLm
    hPreFr hFr (by omega)
    (fun a ha h1 h2 h3 h4 => by rw [← hMem]; exact hLFr a ha h1 h2 h3 h4) hLFoot hExit
    hExitHeap

/-- Name correspondence on `(model.chain.G 0)` and `Hd.G1` (`refreshBatch_edge_dichotomy`). -/
theorem names :
    (∀ e ∈ model.extG.E,
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e ∈
        Hd.G1.E) ∧
    (∀ ei ∈ Hd.G1.E, ∃ e ∈ model.extG.E,
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e = ei) ∧
    (∀ ei ∈ (model.chain.G 0).E, ∃ e ∈ model.extG.E, model.extToInt e = ei) := by
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := Hd.start.rep0
  obtain ⟨_, hFr1, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 Hd.start.refresh
  have hE1 := hFr1.hE
  have hE0 := hFreshInv0.hE
  rw [← Hd.Uint_eq, ← Hd.G1_eq] at hE1
  refine ⟨fun e he => ?_, fun ei hei => ?_, fun ei hei => ?_⟩
  · rw [hE1]; exact Finset.mem_image_of_mem _ he
  · rw [hE1] at hei; simpa using hei
  · rw [hE0] at hei; simpa using hei

/-- The root graph of the model `Hd.X` after the update of Branch B is `Hd.G1`. -/
theorem X_G0 : Hd.X.G 0 = Hd.G1 := by
  rw [Hd.modelEq, Hd.G1_eq, Hd.Uint_eq, Hd.gVec_eq, Hd.lVec_eq]
  have hNo := Hd.start.noFire
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

/-- At the end memory `Hd.sX.mem` of the exit, `tok.rootGraph` stores `Hd.G1` with caps
`(Hd.G1.n, tok.rootECap)`. -/
theorem root_graph :
    DynGraphAt Hd.sX.mem tok.rootGraph Hd.G1.n tok.rootECap Hd.G1 := by
  have h0d : 0 < cfg.P.d := Hd.start.modelInv.1.1
  obtain ⟨_, _, _, _, hFreshInv0, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, _⟩ := Hd.start.rep0
  obtain ⟨_, hFr1, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 Hd.start.refresh
  have hG1n : Hd.G1.n = model.extG.n := by
    rw [Hd.G1_eq, Hd.Uint_eq]
    exact hFr1.n_eq
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootPtr, _⟩, _⟩ := Hd.start.modelInv
  have hCaps0 : DynGraphAt mem0 tok.rootGraph vCap eCap (model.chain.G 0) := by
    have h := Hd.start.caps0 0 h0d
    rwa [hRootPtr] at h
  obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hCaps0 hWire0.2.1
  have hDG := Hd.exitOut.graphs 0 h0d
  have hMK := (Hd.exitOut.metaKeep 0 (by omega)).2
  obtain ⟨_, _, _, _, hInv, _⟩ := Hd.loop
  have hCell := (hInv.cells 0 h0d).2.2.2.2.2.2.1
  have hGPtr : Hd.A.gPtr0 0 = tok.rootGraph := by
    rw [Hd.A_eq]
    exact hRootPtr
  rw [hMK, hCell, hGPtr, X_G0 Hd] at hDG
  have hCast : ∀ {vc ec vc' ec'}, vc = vc' → ec = ec' →
      DynGraphAt Hd.sX.mem tok.rootGraph vc ec Hd.G1 →
      DynGraphAt Hd.sX.mem tok.rootGraph vc' ec' Hd.G1 := by
    rintro _ _ _ _ rfl rfl h; exact h
  exact hCast (hvc.trans hG1n.symm) hec hDG

end BranchBRunHeadKFBL

/-- **Proof of `BranchBTailPhaseGoalKFBL`.** For every head `Hd` of a run of Branch B, the tree
state after Sync 1 moves to the new root graph `Hd.G1` at the end memory `Hd.sX.mem` of the exit,
with deferred set `Hd.G1.E \ (model.chain.G 0).E`. -/
theorem branchBTailPhaseGoalKFBL_proved : BranchBTailPhaseGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R Hd
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := BranchBRunHeadKFBL.heap_order Hd
  obtain ⟨_, _, _, _, hFreshInv0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := Hd.start.rep0
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, hT9, _, _, _, hT13, _⟩ := hTags0
  obtain ⟨_, hFr1, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 Hd.start.refresh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hCapG1, _, _, _, _, hOldSub, _⟩ := Hd.start.modelInv
  obtain ⟨_, _, _, _, _, _, _, _, hPh, hTreeFoot, hCutRec, hOldRec, _, _, hInsSlot, _, _,
    hCanon, hDisjPre, _⟩ := Hd.pre
  obtain ⟨_, hN2, _⟩ := BranchBRunHeadKFBL.names Hd
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := Hd.start.footLt x (Or.inl (hOwn x h))
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    have := Hd.start.refresh.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact this
  have hRange := (translateBatch_oldId_facts U model.extG (model.chain.G 0) model.extToInt
    model.intToExt model.nextFresh hFreshInv0 Hd.start.refresh.1 hEdgeU).2.2.1
  have hGn : (model.chain.G 0).n = model.extG.n := hFreshInv0.n_eq
  have hG1n : Hd.G1.n = (model.chain.G 0).n := by
    rw [Hd.G1_eq, Hd.Uint_eq]
    exact hFr1.n_eq.trans hGn.symm
  have hCapN : ∀ ei ∈ Hd.G1.E \ (model.chain.G 0).E, ei < tok.intCap := by
    intro ei hei
    have heiG1 : ei ∈ Hd.G1.E := (Finset.mem_sdiff.mp hei).1
    rw [Hd.G1_eq, Hd.Uint_eq] at heiG1
    exact (hCapG1 ei heiG1).2
  have hRecPtrKeep (ei : ℕ) (hei : ei ∈ Hd.G1.E \ (model.chain.G 0).E) :
      Hd.sX.mem (tok.edgeRecords + ei) = Hd.sP.mem (tok.edgeRecords + ei) := by
    have ht13 := hT13 ei (hCapN ei hei)
    have hlt := hLt (by rw [ht13]; decide)
    exact BranchBRunHeadKFBL.mid_keep Hd (by omega) (fun _ => by rw [ht13]; omega)
      (fun h => absurd h (by omega))
  rw [Hd.F1_eq]
  refine branchBTreePhase_newRoot (mem0 := mem0) (memS1 := Hd.memS1) (mem' := Hd.sX.mem)
    (G0' := Hd.G1) (U_int := Hd.Uint) (N := Hd.G1.E \ (model.chain.G 0).E)
    (canonVal := Hd.canonVal0) (canonVal' := Hd.canonVal)
    Hd.start.rep0 Hd.start.num0 Hd.start.offInv0 Hd.start.offBd0 hOldSub Hd.start.footLt
    hU hGn (by rw [Hd.Uint_eq]; exact hPh) hTreeFoot
    (fun ei hei hdel => (hCutRec ei hei (by rw [← Hd.Uint_eq]; exact hdel)).1) hOldRec
    (BranchBRunHeadKFBL.tree_words_keep Hd) (by omega) hG1n
    (BranchBRunHeadKFBL.root_graph Hd) ?_ ?_ ?_ ?_ ?_ hCapN ?_ ?_ ?_ ?_
  · -- hNewE
    intro ei hei
    by_cases h : ei ∈ (model.chain.G 0).E
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hei, h⟩)
  · -- hFSub
    intro ei hei
    obtain ⟨heF, heND⟩ := Finset.mem_sdiff.mp hei
    rw [Hd.G1_eq]
    refine SparseCore.mem_applyBatch_E_of_not_delete (model.chain.G 0) Hd.Uint (hOldSub heF)
      (fun hdel => ?_)
    exact heND (List.mem_toFinset.mpr ((mem_batchDeletedEdges_iff Hd.Uint ei).mpr hdel))
  · -- hEnds
    intro e he
    have he0 : e ∈ (model.chain.G 0).E := hOldSub (Finset.mem_sdiff.mp he).1
    have hltF : e < model.nextFresh := hFreshInv0.hLtFresh e he0
    rw [Hd.G1_eq]
    refine treeEdit_batch_preserves_endpoints (model.chain.G 0) Hd.Uint e (fun u hu => ?_)
    rw [Hd.Uint_eq] at hu
    have hr := hRange u hu
    cases u with
    | insert f _ _ => exact fun h => by omega
    | delete _ => trivial
    | split _ _ _ _ => exact hr
  · -- hCanonOld
    intro ei hei0 hei1
    obtain ⟨e, he, rfl⟩ := hN2 ei hei1
    exact ((hCanon e he).2.2.2.2.2.2.2.2.2.2.1 hei0).1
  · -- hCanonNew
    intro ei hei
    obtain ⟨e, he, rfl⟩ := hN2 ei (Finset.mem_sdiff.mp hei).1
    obtain ⟨_, hf, hg, hl, hfl, hdet, _⟩ := hCanon e he
    exact ⟨hf, hg, hl, hfl, hdet⟩
  · -- hNewSlot
    intro ei hei
    obtain ⟨heiG1, heiNot0⟩ := Finset.mem_sdiff.mp hei
    have hIns : ei ∈ batchInsertedEdges Hd.Uint := by
      rw [mem_batchInsertedEdges_iff]
      by_contra hno
      rw [Hd.G1_eq] at heiG1
      exact heiNot0 (mem_applyBatch_of_no_insert Hd.Uint (model.chain.G 0) ei heiG1 hno)
    have ht9 := hT9 ei (hCapN ei hei)
    have hlt := hLt (by rw [ht9]; decide)
    rw [BranchBRunHeadKFBL.mid_keep Hd (by omega) (fun _ => by rw [ht9]; omega)
      (fun h => absurd h (by omega))]
    exact hInsSlot ei (by rw [← Hd.Uint_eq]; exact hIns)
  · -- hNewRec
    intro ei hei
    obtain ⟨heiG1, heiNot0⟩ := Finset.mem_sdiff.mp hei
    obtain ⟨e, he, hEq⟩ := hN2 ei heiG1
    rw [hRecPtrKeep ei hei]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hNot⟩ := hCanon e he
    rw [hEq] at hNot
    obtain ⟨_, _, hlo, hhi, hRecP⟩ := hNot heiNot0
    refine hRecP.congr (fun x hx1 hx2 => ?_)
    exact BranchBRunHeadKFBL.mid_keep Hd (by omega) (fun h => absurd h (by omega))
      (fun _ => by omega)
  · -- hNewRecLoc
    intro ei hei
    obtain ⟨heiG1, heiNot0⟩ := Finset.mem_sdiff.mp hei
    obtain ⟨e, he, hEq⟩ := hN2 ei heiG1
    rw [hRecPtrKeep ei hei]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hNot⟩ := hCanon e he
    rw [hEq] at hNot
    obtain ⟨_, _, hlo, hhi, _⟩ := hNot heiNot0
    exact ⟨by omega, by omega⟩
  · -- hNewDisj
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨he1G1, he1Not0⟩ := Finset.mem_sdiff.mp he₁
    obtain ⟨he2G1, he2Not0⟩ := Finset.mem_sdiff.mp he₂
    rw [hRecPtrKeep e₁ he₁, hRecPtrKeep e₂ he₂]
    have hNotF1 : ∀ ei, ei ∉ (model.chain.G 0).E →
        ei ∉ model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).toFinset :=
      fun ei hnot hf => hnot (hOldSub (Finset.mem_sdiff.mp hf).1)
    rw [Hd.G1_eq, Hd.Uint_eq] at he1G1 he2G1
    exact hDisjPre e₁ he1G1 e₂ he2G1 hne (hNotF1 e₁ he1Not0) (hNotF1 e₂ he2Not0)

end MinCostFlow.MinRatio

end
