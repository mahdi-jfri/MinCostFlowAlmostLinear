module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailGoalsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBSplitKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofBase
import MinCostFlow.MinRatio.SelectUpdateModel
import MinCostFlow.Chain.Ordered.RenameFacts
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import MinCostFlow.SparseCore.BundleStageBase
import MinCostFlow.Chain.Algorithm2

/-!
# Proof of `BranchBTailSplitGoalKFBL` (`WireChainCoreBranchBRunTailSplitKFBL`)

Proves `branchBTailSplitGoalKFBL_proved : BranchBTailSplitGoalKFBL`, which derives the chain-tree
split before Sync 2a directly from a head `Hd : BranchBRunHeadKFBL` by applying `branchBSplit`
(`WireChainCoreBranchBSplitKFBL`) at `c0 := Hd.st0`, `c1 := Hd.X`, `G0 := model.chain.G 0`,
`G0' := Hd.G1`, `Del := (batchDeletedEdges Hd.Uint).toFinset`, and `fDel := fun j => (Hd.D j).fDel`.

Helper lemmas:
* `translateBatch_delete_notMem`: any internal edge deleted by `translateBatch` is absent from the
  resulting internal graph, even if an edge is refreshed multiple times in the same batch.
* `branchBHead_X_G0`: `Hd.X.G 0 = Hd.G1` (level `0` does not fire).
* `branchBHead_X_lt`: prefix preservation `Hd.X.{G,scState,bran} j = Hd.chE.{G,scState,bran} j`
  for `j < Hd.i₀`.
* `branchBHead_nonRebuiltBatches`: `NonRebuiltBatches cfg.T model.chain Hd.X Hd.levelU (Hd.i₀ - 1)`
  for applying `Hd.shrink`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Any internal edge deleted by `translateBatch` is absent from `curInt.applyBatch U_int`, because
every deleted edge ID is strictly below the fresh counter at the step of deletion and no later step
can insert an ID below that counter. -/
private theorem translateBatch_delete_notMem {e : ℕ} :
    ∀ (U : List Update) (curExt curInt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      FreshInv curExt curInt e2i i2e nf → curExt.BatchIsValid U →
      Update.delete e ∈ (translateBatch curExt e2i i2e nf U).2.2.2.2 →
      e ∉ (curInt.applyBatch (translateBatch curExt e2i i2e nf U).2.2.2.2).E
  | [], _, _, _, _, _, _, _, h => by simp [translateBatch] at h
  | u :: rest, curExt, curInt, e2i, i2e, nf, hF, ⟨hU, hRest⟩, hDel => by
    have hT := translateUpdate_preserves hF hU
    dsimp only at hT
    set tu := translateUpdate curExt e2i i2e nf u
    have htu1 : tu.1 = curExt.applyUpdate u := by cases u <;> rfl
    have hRestValid : tu.1.BatchIsValid rest := htu1 ▸ hRest
    set rest' := (translateBatch tu.1 tu.2.1 tu.2.2.1 tu.2.2.2.1 rest).2.2.2.2
    have hDel' : tu.2.2.2.2 = Update.delete e ∨ Update.delete e ∈ rest' := by
      simpa only [translateBatch, tu, rest', List.mem_cons, eq_comm] using hDel
    change e ∉ ((curInt.applyUpdate tu.2.2.2.2).applyBatch rest').E
    rcases hDel' with hEq | hInRest
    · cases u with
      | insert _ _ _ => simp [tu, translateUpdate] at hEq
      | split _ _ _ _ => simp [tu, translateUpdate] at hEq
      | delete a =>
        simp only [tu, translateUpdate, Update.delete.injEq] at hEq
        subst hEq
        have hea : e2i a ∈ curInt.E := hF.hE ▸ Finset.mem_image_of_mem e2i hU
        have heLt : e2i a < nf := hF.hLtFresh (e2i a) hea
        have hRestPres :=
          translateBatch_preserves rest tu.1 (curInt.applyUpdate tu.2.2.2.2) tu.2.1 tu.2.2.1
            tu.2.2.2.1 hT.1 hRestValid
        have hNoIns : ¬ ∃ v ∈ rest', v.Inserts (e2i a) := by
          rintro ⟨v, hv, hIns⟩
          have hGe := (hRestPres.2.2.2.2.2.2.1 v hv (e2i a) hIns).1
          have hnfEq : tu.2.2.2.1 = nf := rfl
          omega
        intro heMem
        have hIn1 := mem_applyBatch_of_no_insert rest' (curInt.applyUpdate tu.2.2.2.2) (e2i a)
          heMem hNoIns
        simp [tu, translateUpdate, MGraph.applyUpdate] at hIn1
    · exact translateBatch_delete_notMem rest tu.1 (curInt.applyUpdate tu.2.2.2.2) tu.2.1
        tu.2.2.1 tu.2.2.2.1 hT.1 hRestValid hInRest

section HeadHelpers

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

private theorem branchBHead_X_G0
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    Hd.X.G 0 = Hd.G1 := by
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

private theorem branchBHead_min_fr_d
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    min Hd.fr cfg.P.d = Hd.i₀ := by
  rcases Hd.exitCase with h1 | h2 | h3 <;> omega

private theorem branchBHead_X_lt
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {j : ℕ} (hj : j < Hd.i₀) :
    Hd.X.G j = Hd.chE.G j ∧ Hd.X.scState j = Hd.chE.scState j ∧ Hd.X.bran j = Hd.chE.bran j := by
  rcases Hd.exitCase with h1 | h2 | h3
  · obtain ⟨_, hiLt, _, _, _, hXeq, _⟩ := h1
    have hR := algorithm1_rebuild_lt cfg.T cfg.L cfg.P { Hd.chE with ℓ := Hd.ℓ', g := Hd.g' }
      hiLt Hd.curGE Hd.curEncE
    rw [hXeq]
    exact ⟨(hR.1 j hj).1, (hR.1 j hj).2.1, (hR.1 j hj).2.2.1⟩
  · obtain ⟨hiEq, hne, _, _, _, hXeq, _⟩ := h2
    have hG : Hd.X.G j = Hd.chE.G j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne, (show j ≠ cfg.P.d by omega)]
    have hSc : Hd.X.scState j = Hd.chE.scState j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne]
    have hBr : Hd.X.bran j = Hd.chE.bran j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne]
    exact ⟨hG, hSc, hBr⟩
  · obtain ⟨hiEq, hemp, _, _, _, hXeq, _⟩ := h3
    have hG : Hd.X.G j = Hd.chE.G j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp, (show j ≠ cfg.P.d by omega)]
    have hSc : Hd.X.scState j = Hd.chE.scState j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp]
    have hBr : Hd.X.bran j = Hd.chE.bran j := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp]
    exact ⟨hG, hSc, hBr⟩

private theorem branchBHead_nonRebuiltBatches
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    NonRebuiltBatches cfg.T model.chain Hd.X Hd.levelU (Hd.i₀ - 1) := by
  have hdPos : 0 < cfg.P.d := Hd.start.modelInv.1.1
  have hiLe : Hd.i₀ ≤ cfg.P.d := Hd.loop.2.2.1
  have hiPos : 0 < Hd.i₀ :=
    Hd.loop.2.2.2.1 (by rw [Hd.st0_eq, Hd.Uint_eq]; exact Hd.start.noFire) hdPos
  have hI := Hd.loop.2.2.2.2.1
  have hSt0G : Hd.st0.G = model.chain.G := by rw [Hd.st0_eq]
  have hSt0Sc : Hd.st0.scState = model.chain.scState := by rw [Hd.st0_eq]
  have hSt0Br : Hd.st0.bran = model.chain.bran := by rw [Hd.st0_eq]
  have hChEBr : Hd.chE.bran = model.chain.bran := hI.modelFrame.2.1.trans hSt0Br
  have hNR0 : NoBatchReinsert (model.chain.G 0) (Hd.levelU 0) := by
    rw [Hd.levelU0, Hd.Uint_eq]
    exact (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh Hd.start.rep0.2.2.2.2.1 Hd.start.refresh.1).2.2.2.1
  refine ⟨by omega, hNR0, ?_, ?_, fun hEq => absurd hEq (by omega)⟩
  · intro j hj
    have hlt : j < Hd.i₀ := by omega
    have hXlt := branchBHead_X_lt Hd hlt
    have hSm := hI.slotModel j hlt
    rw [hXlt.1, hSm.2.2.2.2.2.2.1, hSt0G]
    exact ⟨rfl, hSt0G ▸ hSm.2.2.2.2.2.2.2.1⟩
  · intro j hj _
    have hlt : j < Hd.i₀ := by omega
    have hXlt := branchBHead_X_lt Hd hlt
    have hSm := hI.slotModel j hlt
    obtain ⟨ℓj, gj, ordj, hSc, hUS⟩ := hSm.2.2.2.2.2.2.2.2.2
    rw [hXlt.2.2, hChEBr]
    refine ⟨rfl, ℓj, gj, ordj, ?_, fun _ => ?_⟩
    · rw [hXlt.2.1, hSc, hSt0Sc]
    · rw [hSm.2.2.2.2.2.2.2.2.1, hUS, hSt0Sc, hSt0Br]

end HeadHelpers

/-- **Proof of the split of the chain tree at the end of the exit (`BranchBTailSplitGoalKFBL`).**
Applies `branchBSplit` at `c0 := Hd.st0` and `c1 := Hd.X`. -/
theorem branchBTailSplitGoalKFBL_proved : BranchBTailSplitGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R Hd Fp oldFs newFs hFp hOldFs hNewFs
  subst hFp hOldFs hNewFs
  have hSt0TC : Hd.st0.toTreeChain = model.chain.toTreeChain := by rw [Hd.st0_eq]; rfl
  have hMod : Hd.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [Hd.modelEq, Hd.gVec_eq, Hd.lVec_eq]
  have hdPos : 0 < cfg.P.d := Hd.start.modelInv.1.1
  have hiLe : Hd.i₀ ≤ cfg.P.d := Hd.loop.2.2.1
  have hiPos : 0 < Hd.i₀ :=
    Hd.loop.2.2.2.1 (by rw [Hd.st0_eq, Hd.Uint_eq]; exact Hd.start.noFire) hdPos
  have hMin : min Hd.fr cfg.P.d = Hd.i₀ := branchBHead_min_fr_d Hd
  have hI := Hd.loop.2.2.2.2.1
  have hDisj0 : ∀ j₁ ≤ cfg.P.d, ∀ j₂ ≤ cfg.P.d, j₁ ≠ j₂ →
      Disjoint (Hd.st0.toTreeChain.activeLSF j₁).F.F.E
        (Hd.st0.toTreeChain.activeLSF j₂).F.F.E := by
    rw [hSt0TC]
    exact Hd.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.1
  have hDisj1 : ∀ j₁ ≤ cfg.P.d, ∀ j₂ ≤ cfg.P.d, j₁ ≠ j₂ →
      Disjoint (Hd.X.toTreeChain.activeLSF j₁).F.F.E
        (Hd.X.toTreeChain.activeLSF j₂).F.F.E := by
    rw [hMod]
    exact Hd.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSub0 : Hd.st0.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E := by
    rw [hSt0TC]
    exact Hd.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSub1 : Hd.X.toTreeChain.chainTree.E ⊆ Hd.G1.E := by
    rw [← branchBHead_X_G0 Hd, hMod]
    exact Hd.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hKeepE : ∀ e ∈ (model.chain.G 0).E, e ∉ (batchDeletedEdges Hd.Uint).toFinset →
      e ∈ Hd.G1.E := by
    intro e he hNotDel
    rw [Hd.G1_eq]
    refine SparseCore.mem_applyBatch_E_of_not_delete (model.chain.G 0) Hd.Uint he fun hDel => ?_
    exact hNotDel (List.mem_toFinset.mpr ((mem_batchDeletedEdges_iff Hd.Uint e).mpr hDel))
  have hDelOut : ∀ e ∈ (batchDeletedEdges Hd.Uint).toFinset, e ∉ Hd.G1.E := by
    intro e he
    have hDel : Update.delete e ∈ Hd.Uint :=
      (mem_batchDeletedEdges_iff Hd.Uint e).mp (List.mem_toFinset.mp he)
    rw [Hd.G1_eq, Hd.Uint_eq]
    rw [Hd.Uint_eq] at hDel
    exact translateBatch_delete_notMem U model.extG (model.chain.G 0) model.extToInt
      model.intToExt model.nextFresh Hd.start.rep0.2.2.2.2.1 Hd.start.refresh.1 hDel
  have hShrink :=
    Hd.shrink model.chain Hd.X Hd.levelU (Hd.i₀ - 1) Hd.start.shiftInv.1
      (branchBHead_nonRebuiltBatches Hd)
  have hPlain : ∀ j < min Hd.fr cfg.P.d,
      (Hd.X.toTreeChain.activeLSF j).F.F.E ⊆ (Hd.st0.toTreeChain.activeLSF j).F.F.E ∧
      (Hd.D j).fDel.toFinset =
        (Hd.st0.toTreeChain.activeLSF j).F.F.E \ (Hd.X.toTreeChain.activeLSF j).F.F.E := by
    intro j hj
    have hlt : j < Hd.i₀ := by rw [← hMin]; exact hj
    have hjd : j < cfg.P.d := by omega
    have hXlt := branchBHead_X_lt Hd hlt
    have hSm := hI.slotModel j hlt
    refine ⟨?_, ?_⟩
    · rw [hSt0TC]
      exact hShrink j (by omega)
    · have hAct0 : Hd.st0.toTreeChain.activeLSF j = cfg.T.lsfs (Hd.st0.scState j) (Hd.st0.bran j) :=
        by simp [ChainState.toTreeChain, TreeChain.activeLSF, hjd]
      have hAct1 : Hd.X.toTreeChain.activeLSF j = cfg.T.lsfs (Hd.X.scState j) (Hd.X.bran j) := by
        simp [ChainState.toTreeChain, TreeChain.activeLSF, hjd]
      rw [hAct0, hAct1, hXlt.2.1, hXlt.2.2]
      exact hSm.2.2.2.1
  have hSame : Hd.fr = cfg.P.d + 1 →
      (Hd.X.toTreeChain.activeLSF cfg.P.d).F.F.E = (Hd.st0.toTreeChain.activeLSF cfg.P.d).F.F.E := by
    intro hfr
    rcases Hd.exitCase with h1 | h2 | h3
    · omega
    · omega
    · obtain ⟨_, hemp, _, _, _, hXeq, _⟩ := h3
      have hLastL : Hd.X.lastLSFs = Hd.st0.lastLSFs := by
        rw [hXeq]; simp only [Chain.Ordered.updateLoop, hemp, ↓reduceIte]
        exact hI.modelFrame.2.2.2.1
      have hLastB : Hd.X.lastBran = Hd.st0.lastBran := by
        rw [hXeq]; simp only [Chain.Ordered.updateLoop, hemp, ↓reduceIte]
        exact hI.modelFrame.2.2.2.2.1
      simp only [ChainState.toTreeChain, TreeChain.activeLSF, lt_irrefl, ↓reduceIte, hLastL, hLastB]
  have hNd : ∀ j < min Hd.fr cfg.P.d, (Hd.D j).fDel.Nodup := by
    intro j hj
    exact (hI.slotModel j (by rw [← hMin]; exact hj)).2.2.1
  have hRes := branchBSplit Hd.st0 Hd.X (fr := Hd.fr) (G0 := model.chain.G 0) (G0' := Hd.G1)
    (Del := (batchDeletedEdges Hd.Uint).toFinset) (fDel := fun j => (Hd.D j).fDel)
    hDisj0 hDisj1 hSub0 hSub1 hKeepE hDelOut hPlain hSame Hd.exitOut.frLe hNd
  have hF1 : Hd.F1 = Hd.st0.toTreeChain.chainTree.E \ (batchDeletedEdges Hd.Uint).toFinset := by
    rw [Hd.F1_eq, hSt0TC]
  rw [hF1]
  exact hRes

end MinCostFlow.MinRatio
