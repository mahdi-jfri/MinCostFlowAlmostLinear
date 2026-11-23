module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailGraphKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailKeepKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailPartGoalsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBSlotInKFBL
import WordRAM.Tactic

/-!
# The suffix of Branch B from a head (`WireChainCoreBranchBRunTailSufKFBL`)

From a head of a run of Branch B, the tree state on the new root graph after the exit (the field
`phaseX`), the split of the chain tree (the field `split`) and the room of the suffix
(`BranchBTailRoomGoalKFBL`), `suffix_run` runs the suffix of Branch B from the state `sX` after
the exit (`wireBranchBSuffixKFBL_runs`). It gives the facts `BranchBSuffixFactsKFBL` (the field
`suf`) and the place of the records of the cut tree edges (the field `sufRecCut`).

The premises of the suffix come from the head:
* the select slots of the finished levels from `exitOut.slots` (`branchBSlot_of_done`, with
  `min fr d = i₀`);
* the forest lists from `suffixLists`, and the keep facts of their words, of the select base and
  of the batch from `forestLoc` (`branchBSuffixKeep_of_forestLoc`, `keep_facts`);
* the graph facts and the caps (`WireChainCoreBranchBRunTailGraphKFBL`), the root word and the
  batch (`WireChainCoreBranchBRunTailKeepKFBL`), the registers (`sX_regs`);
* the split facts, at `n = min fr d = i₀`.
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
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

set_option maxHeartbeats 1600000 in
/-- The keep premises `hOldK`, `hNewK`, `hSelK`, `hBatchK` of the suffix at `sX`, from the places
of the forests after the exit (`forestLoc`): the core footprints at the end of the loop lie in
the old footprints (tag `21 + j`) or above the heap floor, the last level has tag `19`, and the
tree after Sync 1 lies below `uIntBuf` or in `[h0, hS1)`. -/
theorem keep_facts :
    let K := BranchBSuffixKeep L tok root uIntBuf (Hd.sX.regs 4) Hd.curTreeTok1
    let oldPtrs := heap + 1 + 12 * cfg.P.d
    let newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)
    let oldFs := if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []
    let newFs := if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else []
    (∀ (t : ℕ) (ht : t < oldFs.length), K (oldPtrs + Hd.fr + t) ∧
      ∀ vc ec, DynGraphAt Hd.sX.mem (Hd.sX.mem (oldPtrs + Hd.fr + t)) vc ec oldFs[t] →
        ∀ x, Hd.sX.mem (oldPtrs + Hd.fr + t) ≤ x →
          x < Hd.sX.mem (oldPtrs + Hd.fr + t) + dynGraphSize vc ec → K x) ∧
    (∀ (t : ℕ) (ht : t < newFs.length), K (newPtrs + Hd.fr + t) ∧
      ∀ vc ec, DynGraphAt Hd.sX.mem (Hd.sX.mem (newPtrs + Hd.fr + t)) vc ec newFs[t] →
        ∀ x, Hd.sX.mem (newPtrs + Hd.fr + t) ≤ x →
          x < Hd.sX.mem (newPtrs + Hd.fr + t) + dynGraphSize vc ec → K x) ∧
    K heap ∧ (∀ x, uIntBuf ≤ x → x < uIntBuf + (editsPtr - cfg.P.d - uIntBuf) → K x) := by
  intro K oldPtrs newPtrs oldFs newFs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
  obtain ⟨hOwn, hT1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, hT21⟩ := hTags
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order Hd
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := Hd.pre
  obtain ⟨_, _, hF4, _⟩ := Hd.front
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLFoot, _⟩ := Hd.loop
  obtain ⟨hfr, hOldLen, hNewLen, _, _⟩ := suffixLists Hd
  have hu := Hd.start.uLe
  have he := Hd.start.edHeap
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := Hd.start.footLt x (Or.inl (hOwn x h))
  have hR15 : root + 15 < uIntBuf := hLt (by rw [hT1 15 (by omega)]; decide)
  have hA := Hd.A_eq
  have hFloor : Hd.A.heapFloor = Hd.heap2 := by rw [hA]; rfl
  have hCH (j : ℕ) (hj : j < cfg.P.d) : Hd.A.coreH j = tok.coreHandle j := by
    rw [hA]; show (if j < cfg.P.d then tok.coreHandle j else tok.termHandle) = _
    simp only [hj, ↓reduceIte]
  have hCHd : Hd.A.coreH cfg.P.d = tok.termHandle := by
    rw [hA]; show (if cfg.P.d < cfg.P.d then tok.coreHandle cfg.P.d else tok.termHandle) = _
    simp
  have hCoreTag : ∀ j < cfg.P.d, ∀ a, Rcore.foot (Hd.A.coreH j) (Hd.tokE j) a →
      (a < uIntBuf ∧ tok.tag a = 21 + j) ∨ Hd.A.heapFloor ≤ a := by
    intro j hj a ha
    rcases hLFoot j hj a ha with h0 | ⟨h1, _⟩
    · rw [hCH j hj] at h0
      exact Or.inl ⟨Hd.start.footLt a (Or.inr (Or.inr ⟨j, hj, h0⟩)), hT21 j hj a h0⟩
    · rw [hFloor]; rw [hF4] at h1; exact Or.inr (by omega)
  have hFootX : ∀ j < cfg.P.d, ∀ a, Rcore.foot (Hd.A.coreH j) (Hd.tokE j) a →
      a < Hd.sX.regs 4 := by
    intro j hj a ha
    rcases hLFoot j hj a ha with h0 | ⟨_, h2⟩
    · rw [hCH j hj] at h0
      have := Hd.start.footLt a (Or.inr (Or.inr ⟨j, hj, h0⟩)); omega
    · omega
  have hLastTag : ∀ a, (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E).foot (Hd.A.coreH cfg.P.d) tok.termTok a →
      a < uIntBuf ∧ tok.tag a = 19 := by
    intro a ha
    rw [hCHd] at ha
    have ht : tok.tag a = 19 := hT19 a ha
    exact ⟨hLt (by rw [ht]; decide), ht⟩
  have hTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
      Hd.curTreeTok1 a →
      a < uIntBuf ∨ (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a ∧ a < Hd.hS1) := by
    intro a ha
    rcases hTreeFoot a ha with h | h
    · exact Or.inl (Hd.start.footLt a (Or.inr (Or.inl h)))
    · exact Or.inr h
  exact branchBSuffixKeep_of_forestLoc (tokS := tok) (root := root) (uIntBuf := uIntBuf)
    (selBase := heap) (totalWords := editsPtr - cfg.P.d - uIntBuf)
    Hd.forestLoc hCoreTag hFootX hLastTag hTree (hT1 11 (by omega)) (by omega) hh0
    (by rw [hFloor]; omega) (by rw [hFloor]; omega) (by omega) le_rfl (by omega)
    (by show Hd.fr + (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []).length ≤
      cfg.P.d + 1; omega)
    (by show Hd.fr + (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else []).length ≤
      cfg.P.d + 1; omega) hU (by omega) (by omega)

set_option maxHeartbeats 3200000 in
/-- **The suffix of Branch B from a head.** From the tree state `phaseX` on the new root graph at
the state `sX` after the exit, the split facts of the chain tree for `Fp`, `oldFs`, `newFs`, and
the room of the suffix, the suffix runs from `sX`, and its facts hold: the records of the cut tree
edges lie in its heap (the field `sufRecCut`), and `BranchBSuffixFactsKFBL` (the field `suf`). -/
theorem suffix_run
    (hPh : TreeSyncPhaseAt L tok root uIntBuf (Hd.sX.regs 4) tok.rootGraph Hd.G1 Hd.F1
      Hd.canonVal B R (Hd.G1.E \ (model.chain.G 0).E) Hd.curTree1 Hd.curTreeTok1 Hd.offCnt1
      Hd.sX.mem)
    {Fp : Finset ℕ} {oldFs newFs : List MGraph}
    (hOldFs : oldFs = if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else [])
    (hNewFs : newFs = if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])
    (hSp : (∀ Y : Finset ℕ,
      (∀ e, e ∈ Y ↔ (∃ j < min Hd.fr cfg.P.d, e ∈ (Hd.D j).fDel) ∧ e ∈ Hd.G1.E) →
      Hd.F1 \ Y = Fp ∪ (graphListEdgeUnion oldFs ∩ Hd.G1.E)) ∧
    (∀ j < min Hd.fr cfg.P.d, ∀ e ∈ (Hd.D j).fDel, e ∈ Hd.G1.E → e ∈ Hd.F1) ∧
    (∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs) ∧ (∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs) ∧
    Fp ∪ graphListEdgeUnion newFs = Hd.X.toTreeChain.chainTree.E ∧
    ((List.range (min Hd.fr cfg.P.d)).flatMap fun j => (Hd.D j).fDel).Nodup)
    (hRoom :
      let T := ∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length
      let S := graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
        graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])
      Hd.sX.regs 4 + (2 * T + T * wireTreeSyncEditSpace L) +
          (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) + 1 ≤
        heap + coreSpace U.length) :
    ∃ (out : State) (cS nextHeap : ℕ) (curTree : PathTreeState)
      (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ),
      (∀ ei ∈ Hd.G1.E, ei ∈ Hd.F1 → ei ∉ Fp ∪ graphListEdgeUnion newFs →
        Hd.sX.regs 4 ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ nextHeap) ∧
      BranchBSuffixFactsKFBL (w := w) L drainUnit emitCuts packEditsProc filterEdits bind
        canonCopy isNeg pushInsProc root uIntBuf (Hd.sX.regs 4) tok.rootGraph Hd.offCnt1 Hd.i₀
        cfg.P.d Hd.fr p opTree ω Hd.sX tok B R Hd.G1 Hd.F1 Fp (Hd.G1.E \ (model.chain.G 0).E)
        Hd.canonVal Hd.curTreeTok1 (fun j => (Hd.D j).fDel) oldFs newFs Hd.Uint out cS nextHeap
        curTree curTreeTok offCnt := by
  subst hOldFs hNewFs
  have hmin := min_fr Hd
  rw [hmin] at hSp
  obtain ⟨hSplit, hInF, hPOld, hPNew, hTreeEq, hNd⟩ := hSp
  obtain ⟨hNewF, hNewSubX⟩ := forest_new Hd
  rw [← hTreeEq] at hNewF hNewSubX
  obtain ⟨hi₀, hOldLen, hNewLen, hOld, hNew⟩ := suffixLists Hd
  obtain ⟨hOldK, hNewK, hSelK, hBatchK⟩ := keep_facts Hd
  obtain ⟨hSmall, hBatchW⟩ := batch_sX Hd
  obtain ⟨hRegs, hSel⟩ := sX_regs Hd
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order Hd
  have hi0d : Hd.i₀ ≤ cfg.P.d := Hd.loop.2.2.1
  -- the select slots of the finished levels
  have hSlots := Hd.exitOut.slots
  rw [hmin, Hd.A_eq] at hSlots
  have hSlot := branchBSlot_of_done hSlots (by show heap + 1 + 12 * Hd.i₀ ≤ Hd.sX.regs 4; omega)
  have hSelW : Hd.sX.mem heap = Hd.fr := by
    have h := Hd.exitOut.sel; rw [Hd.A_eq] at h; exact h
  have hRoomW := Hd.start.room
  have h : Hd.sX.regs 4 +
      (2 * (∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length) +
        (∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length) * wireTreeSyncEditSpace L) +
      (3 * tok.intCap +
        4 * (graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
          graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])) +
        (graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
          graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])) *
          wireTreeSyncEditSpace L) + 1 ≤
        heap + coreSpace U.length := hRoom
  have hRoom' : Hd.sX.regs 4 +
      (2 * (∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length) +
        (∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length) * wireTreeSyncEditSpace L) +
      (3 * tok.intCap +
        4 * (graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
          graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])) +
        (graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
          graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])) *
          wireTreeSyncEditSpace L) + 1 < 2 ^ w := by
    omega
  obtain ⟨out, cost, nextHeap, ct, ctt, oc, hRC, hRest⟩ :=
    wireBranchBSuffixKFBL_runs (n := Hd.i₀) (selBase := heap)
      (oldPtrs := heap + 1 + 12 * cfg.P.d) (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1))
      (dd := cfg.P.d) (i₀ := Hd.fr) (totalWords := editsPtr - cfg.P.d - uIntBuf)
      (Gb := model.chain.G 0) (fPtr := fun j => Hd.sX.mem (heap + 1 + 12 * j + 2))
      (fDel := fun j => (Hd.D j).fDel)
      Hd.envB.emitP Hd.envA.packP Hd.envB.filterP Hd.envB.pushP Hd.envB.pushInsP Hd.envA.four
      Hd.envA.w18 Hd.envA.treeImpl Hd.envA.bindC Hd.envA.canonC Hd.envA.isNegC Hd.start.rep0
      Hd.start.footLt (G1_n Hd) Hd.start.logW Hd.start.capT hPh (forest_F1 Hd) hSlot
      (delCap Hd) hInF hNd hSplit hNewF
      (fun e he => hNewSubX (Finset.mem_union_right _ he)) hPOld hPNew (oldCap Hd) hi₀
      hOldLen hNewLen hOld hNew hOldK hNewK (intCap_sX Hd) hSelW hSelK hSmall (edgeOnly Hd)
      hBatchW hBatchK (insCap Hd) hRegs hSel Hd.exitOut.zero hRoom' Hd.envA.lW
  exact ⟨out, cost, nextHeap, ct, ctt, oc, hRC, hRest⟩

end BranchBRunHeadKFBL

end MinCostFlow.MinRatio
