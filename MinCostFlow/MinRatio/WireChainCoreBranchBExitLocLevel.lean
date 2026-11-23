module

public import MinCostFlow.MinRatio.WireChainCoreBranchBOwnKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProof
import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import WordRAM.Tactic

/-!
# Where the levels lie after the exit of Branch B (`WireChainCoreBranchBExitLocLevel`)

This file proves `BranchBLevelLocGoalKFBL`
(`WireChainCoreBranchBOwnKFBL.lean`): at every run of Branch B (`H : BranchBRunKFBL …`), the
new last level, the level graphs and the length blocks after the exit lie in the zones
`BranchBSufZoneKFBL` that the suffix keeps (`BranchBExitLevelLocKFBL`).

* `last`: from `H.exitOut.lastFoot` and the terminal-handle placement `branchBSpace_lastHandle`,
  every word of the last-level footprint either lies in `[H.sE.regs 4, H.sX.regs 4)` (rebuilt
  exits `H.fr ≤ d`), in `[uIntBuf, H.A.selBase)`, or below `uIntBuf` in the old terminal footprint
  with tag `19 ≥ 17` (empty terminal exit `H.fr = d + 1`).
* `graph` and `len`: levels `j < min (H.fr + 1) d` keep their `mem0` pointers (`H.exitOut.metaKeep`
  and `I.cells`), whose blocks carry tag `20` or `23 + d ≥ 17` below `uIntBuf`
  (`SolverLevelMetaAt.atCaps`); rebuilt levels `H.fr + 1 ≤ j < d` lie in `[H.sE.regs 4, H.hT)`
  (`H.exitOut.metaNew` and `H.exitOut.hTle`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **Proof of `BranchBLevelLocGoalKFBL`.** At every run of Branch B, the new last level, the
level graphs and the length blocks after the exit lie in `BranchBSufZoneKFBL`. -/
theorem branchBLevelLocGoalKFBL_proved : BranchBLevelLocGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul
    fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc
    Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap
    pos ω mem0 mem model tok U B R H
  have hHeaps := BranchBRunKFBL.heap_order H
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hLastH := branchBSpace_lastHandle H
  have hTags := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases (H.exitOut.lastFoot a ha).1 with haLt | haIn
    · by_cases hU : a < uIntBuf
      · by_cases hfr : H.fr ≤ cfg.P.d
        · have hGe : H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d) := hLastH.1 hfr
          have hFoot : H.sX.mem (H.A.handleBase + cfg.P.d) ≤ a ∧ a < H.termTokN := ha
          omega
        · have hfrEq : H.fr = cfg.P.d + 1 := by
            have := H.exitOut.frLe; omega
          have hTokN : H.termTokN = tok.termTok := by
            rcases H.exitCase with hInt | hTerm | hEmpty
            · omega
            · omega
            · exact hEmpty.2.2.2.2.2.2.2.1
          have hHD : H.sX.mem (H.A.handleBase + cfg.P.d) = tok.termHandle := by
            rw [hLastH.2 hfrEq, H.A_eq]; simp [branchBAddrsOf]
          have hOldFoot : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L 0
              (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a := by
            change tok.termHandle ≤ a ∧ a < tok.termTok
            rw [← hHD, ← hTokN]
            exact ha
          have hTag : tok.tag a = 19 := hTags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hOldFoot
          exact Or.inl ⟨hU, by omega⟩
      · exact Or.inr (Or.inl ⟨by omega, haLt⟩)
    · exact Or.inr (Or.inr haIn)
  · intro j hj a ha1 ha2
    by_cases hjm : j < min (H.fr + 1) cfg.P.d
    · have hKeep := (H.exitOut.metaKeep j hjm).2
      have hCell := (H.loop.2.2.2.2.1.cells j hj).2.2.2.2.2.2.1
      have hG0 : H.A.gPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
        rw [H.A_eq]; rfl
      rw [hKeep, hCell, hG0] at ha1 ha2
      have hAt := H.start.meta0.atCaps H.start.caps0 j hj
      have hTag : tok.tag a = if j = 0 then 20 else 23 + cfg.P.d := hAt.2.2.2.2 a ha1 ha2
      have hTagGe : 17 ≤ tok.tag a := by split_ifs at hTag <;> omega
      have hOwn : tok.owned a := hTags.1 a (by omega)
      exact Or.inl ⟨H.start.footLt a (Or.inl hOwn), hTagGe⟩
    · have hNew := H.exitOut.metaNew j (by omega) hj
      have hTle := H.exitOut.hTle
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · intro j hj e he i hi
    have heCap : e < eCap := (H.exitOut.graphs j hj).2.2.1 e he
    have heL : e * L + i < eCap * L := by
      have hmul : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCap)
      rw [Nat.succ_mul] at hmul
      omega
    by_cases hjm : j < min (H.fr + 1) cfg.P.d
    · have hKeep := (H.exitOut.metaKeep j hjm).1
      have hCell := (H.loop.2.2.2.2.1.cells j hj).2.2.2.2.2.2.2.1
      have hL0 : H.A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := by
        rw [H.A_eq]; rfl
      have hAt := H.start.meta0.atCaps H.start.caps0 j hj
      have hTag : tok.tag (H.sX.mem (H.A.levelMeta + j) + e * L + i) = 23 + cfg.P.d := by
        rw [hKeep, hCell, hL0]
        exact hAt.2.2.2.1 _ (by omega) (by omega)
      have hOwn : tok.owned (H.sX.mem (H.A.levelMeta + j) + e * L + i) :=
        hTags.1 _ (by rw [hTag]; omega)
      exact Or.inl ⟨H.start.footLt _ (Or.inl hOwn), by rw [hTag]; omega⟩
    · have hNew := H.exitOut.metaNew j (by omega) hj
      have hTle := H.exitOut.hTle
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end MinCostFlow.MinRatio
