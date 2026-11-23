module

public import MinCostFlow.MinRatio.WireChainCoreBranchBOwnKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBOwnRestFactsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBRunTreeKFBL
import WordRAM.Tactic

/-!
# The edge accounts after a run of Branch B (`WireChainCoreBranchBOwnRestKFBL`)

`BranchBOwnRestGoalKFBL` asks for the fields `canon`, `thrLoc`, `recLoc` and `thrRecDisj` of
`BranchBSufOutKFBL`: the threshold of each edge, the canonical values, and where the threshold
and record blocks lie at the end of the run. The prefix of Branch B writes the thresholds and the
records and says where they lie; the later parts keep these words
(`WireChainCoreBranchBOwnRestFactsKFBL`). The only words the suffix moves are the records of the
tree edges it cuts. For those, the facts of the suffix in `BranchBRunKFBL` do not say where the
new record lies, so this file takes it as the premise `BranchBSufRecCutGoalKFBL`. The field
`sufRecCut` of
`BranchBRunKFBL` gives it.

`branchBOwnRestGoal_of_sufRecCut` proves `BranchBOwnRestGoalKFBL` from it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The records of the edges that the suffix cuts.** At every run of Branch B,
an edge of the new root graph `G1` that is a tree edge after Sync 1 (in `F1`) and is off the new
chain tree `Fp ∪ newE` has its record in the new heap of the suffix, `[sX.regs 4, nextHeap)`.
The proof of `wireBranchBSuffixKFBL_runs` shows this (Sync 2a and Sync 2b write the record of
each edge they cut to fresh heap), but its conclusion does not state it. -/
@[expose] def BranchBSufRecCutGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    ∀ ei ∈ H.G1.E, ei ∈ H.F1 → ei ∉ H.Fp ∪ graphListEdgeUnion H.newFs →
      H.sX.regs 4 ≤ H.out.mem (tok.edgeRecords + ei) ∧
      H.out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ H.nextHeap

/-- `BranchBOwnRestGoalKFBL` from the premise `BranchBSufRecCutGoalKFBL`. The thresholds
and the canonical values are those the prefix wrote (`thr_facts`, `acct_keep`); the records lie
where `rec_place` says. -/
theorem branchBOwnRestGoal_of_sufRecCut (hRC : BranchBSufRecCutGoalKFBL) :
    BranchBOwnRestGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul
    treeMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
    lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
    g l heap pos ω mem0 mem model tok U B R H
  have hCut := hRC H
  have hX : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hG : (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G 0 = H.G1 := by
    rw [← hX]; exact BranchBRunKFBL.X_G0 H
  have hT : (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.toTreeChain.chainTree.E =
      H.Fp ∪ graphListEdgeUnion H.newFs := by
    rw [← hX]; exact H.split.2.2.2.2.1.symm
  have hG1 : H.G1 = (model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2 := by
    rw [H.G1_eq, H.Uint_eq]
  have hLpos : 0 < L := H.envA.lPos
  obtain ⟨hU, hh0, hS1h, hFl, hXh⟩ := BranchBRunKFBL.heap_order H
  obtain ⟨hN1, _, _⟩ := BranchBRunKFBL.names H
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCanon, _, hThrRec, _⟩ := H.pre
  refine { canon := ?_, thrLoc := ?_, recLoc := ?_, thrRecDisj := ?_ }
  · intro tr e he
    obtain ⟨hPtr, hBlk⟩ := BranchBRunKFBL.thr_facts H he
    obtain ⟨hThr, _, _, _, _, _, hF, hGr, hL, hAcc, _, _⟩ := hCanon e he
    refine ⟨?_, hF, hGr, hL, hAcc⟩
    rw [hPtr]
    refine hThr.congr fun j hj => ?_
    rcases hBlk with h | ⟨_, h1, h2⟩
    · exact BranchBRunKFBL.acct_keep H (fun _ => Or.inr (Or.inl (h j hj).2))
        (fun hu => absurd hu (not_le.mpr (h j hj).1))
    · exact BranchBRunKFBL.acct_keep H (fun hl => absurd hl (by omega))
        (fun _ => ⟨by omega, by omega⟩)
  · intro tr e he j hj
    obtain ⟨hPtr, hBlk⟩ := BranchBRunKFBL.thr_facts H he
    show (H.out.mem (tok.edgeThresholds + tr.2.1 e) + j < uIntBuf → _) ∧ _
    rw [hPtr]
    rcases hBlk with h | ⟨_, h1, h2⟩
    · obtain ⟨hlt, h17⟩ := h j hj
      refine ⟨fun _ => h17, fun hu => absurd hu (not_le.mpr hlt), fun hf => ?_⟩
      rcases BranchBRunKFBL.foot_cur H hf with ⟨_, h16⟩ | ⟨h3, _⟩ | ⟨h3, _⟩
      · omega
      · omega
      · omega
    · refine ⟨fun hl => absurd hl (by omega), fun _ => ⟨by omega, by omega⟩, fun hf => ?_⟩
      rcases BranchBRunKFBL.foot_cur H hf with ⟨h3, _⟩ | ⟨_, h3⟩ | ⟨h3, _⟩
      · omega
      · omega
      · omega
  · intro ei hei hnt j hj hu
    rw [hG] at hei
    rw [hT] at hnt
    rcases BranchBRunKFBL.rec_place H hCut hei hnt with h | ⟨h1, h2⟩ | ⟨_, _, h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd hu (not_le.mpr (h j hj).1)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · dsimp only
    intro e₁ he₁ e₂ he₂ hnt
    rw [hT] at hnt
    obtain ⟨hPtr, hBlk⟩ := BranchBRunKFBL.thr_facts H he₁
    rw [hPtr]
    rcases BranchBRunKFBL.rec_place H hCut (hN1 e₂ he₂) hnt with
        hR | ⟨h1, h2⟩ | ⟨hNo2, hEq, h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hBlk with hB | ⟨hNo1, h3, h4⟩
    · by_contra hc
      simp only [not_or, not_le] at hc
      by_cases hle : H.sP.mem (tok.edgeThresholds + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₁) ≤
          H.out.mem (tok.edgeRecords + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₂)
      · have h17 := (hB (H.out.mem (tok.edgeRecords + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₂) -
          H.sP.mem (tok.edgeThresholds + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₁)) (by omega)).2
        have h18 := (hR 0 (by omega)).2
        rw [Nat.add_sub_cancel' hle] at h17
        rw [Nat.add_zero] at h18
        omega
      · have h18 := (hR (H.sP.mem (tok.edgeThresholds + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₁) -
          H.out.mem (tok.edgeRecords + (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e₂)) (by omega)).2
        have h17 := (hB 0 hLpos).2
        rw [Nat.add_sub_cancel' (by omega)] at h18
        rw [Nat.add_zero] at h17
        omega
    · have := (hR (1 + 4 * L) (by omega)).1
      exact Or.inr (by omega)
    · have := (hB (L - 1) (by omega)).1
      exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · have := (hB (L - 1) (by omega)).1
      exact Or.inl (by omega)
    · rw [hEq]
      rw [hG1] at hN1
      exact hThrRec _ (hN1 e₁ he₁) hNo1 _ (hN1 e₂ he₂) hNo2
    · have := (hB (L - 1) (by omega)).1
      exact Or.inl (by omega)
    · exact Or.inl (by omega)

end MinCostFlow.MinRatio
