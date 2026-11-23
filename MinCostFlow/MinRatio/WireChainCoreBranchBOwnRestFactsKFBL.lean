module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunFactsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBOwnRestKeepKFBL
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import WordRAM.Tactic

/-!
# The edge accounts along a run of Branch B (`WireChainCoreBranchBOwnRestFactsKFBL`)

The fields of `BranchBSufOutKFBL` on the edge accounts (`canon`, `thrLoc`, `recLoc`,
`thrRecDisj`) read the threshold and record pointers of the edges at the end of the run. The
prefix of Branch B writes these pointers and says where their blocks lie (its fact on the
canonical values, at the end state `sP` of the prefix). This file moves those facts to the end
state `out`:
* `mid_keep`, `suffix_keep_acct`, `acct_keep`: the pointer words and the threshold and record
  blocks keep their values from `sP` to `out` (the front, the loop and the exit by
  `branchBMidWords_keep`, the suffix by its frame);
* `foot_cur`: where the tree lies at the end;
* `names`: each internal name of the new root graph `G1` is the new name of an external edge,
  and each name of the old root graph is the old name of an external edge
  (`refreshBatch_edge_dichotomy`);
* `thr_facts`: the threshold pointer at the end and the place of its block;
* `rec_place`: the place of the record block of an edge of `G1` off the new chain tree. For a tree
  edge after Sync 1 that the suffix cuts, it takes the place of the new record as a premise
  (`hCut`): the facts of the suffix in `BranchBRunKFBL.suf` do not say it.
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


/-- The words below the heap floor `heap2` with a tag in `9, …, 18` (below `uIntBuf`) or outside
the fixed part of the heap (above `uIntBuf`) keep their values from the end `sP` of the prefix
to the end `sX` of the exit (`branchBMidWords_keep`). -/
theorem mid_keep {a : ℕ} (ha : a < H.heap2)
    (hT : a < uIntBuf → 9 ≤ tok.tag a ∧ tok.tag a ≤ 18)
    (hH : uIntBuf ≤ a → heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a) :
    H.sX.mem a = H.sP.mem a := by
  obtain ⟨hU, _, _, _, _⟩ := heap_order H
  obtain ⟨_, _, hF4, hFr, _⟩ := H.front
  obtain ⟨_, _, _, _, _, _, _, _, hMem, _, _, _, _, _, hLFr, hLFoot, _⟩ := H.loop
  have hA := H.A_eq
  have hExit := H.exitOut.frame
  have hExitHeap := H.exitOut.frameHeap
  rw [hA] at hLFr hLFoot hExit hExitHeap
  exact branchBMidWords_keep (oldPtrs := heap + 1 + 12 * cfg.P.d)
    (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) (s := H.sF0) (sE := H.sE)
    (tokE := H.tokE) H.start.rep0 H.start.meta0 H.start.caps0 H.start.modelInv H.start.footLt hU
    ⟨by omega, by omega, by omega⟩ hFr (by omega)
    (fun a ha h1 h2 h3 h4 => by rw [← hMem]; exact hLFr a ha h1 h2 h3 h4) hLFoot hExit
    hExitHeap a ha hT (fun hu => Or.inr (hH hu))

/-- A word below `uIntBuf` with tag `12`, `17` or `18`, or a word of `[hS1, heap2)`, keeps its
value across the suffix: it is not the count word, its tag is not one the syncs write, and it
lies off the tree (by the place of the tree after Sync 1). -/
theorem suffix_keep_acct {a : ℕ}
    (hlo : a < uIntBuf → tok.tag a = 12 ∨ tok.tag a = 17 ∨ tok.tag a = 18)
    (hhi : uIntBuf ≤ a → H.hS1 ≤ a ∧ a < H.heap2) : H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order H
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, _, _, _, _, hFr, _⟩ := H.suf
  have hR11 : root + 11 < uIntBuf :=
    H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide)))
  by_cases hl : a < uIntBuf
  · have ht := hlo hl
    refine hFr a (by omega) (fun he => ?_) (fun _ => ?_) (fun h => absurd h (by omega))
    · rw [he, hT1 11 (by omega)] at ht; omega
    · rcases ht with h | h | h <;> rw [h] <;> decide
  · obtain ⟨h1, h2⟩ := hhi (by omega)
    refine hFr a (by omega) (by omega) (fun h => absurd h hl) (fun _ hf => ?_)
    rcases hTreeFoot a hf with h | h
    · have := H.start.footLt a (Or.inr (Or.inl h)); omega
    · omega

/-- The words of `suffix_keep_acct` keep their values from the end `sP` of the prefix to the
end `out` of the run. -/
theorem acct_keep {a : ℕ}
    (hlo : a < uIntBuf → tok.tag a = 12 ∨ tok.tag a = 17 ∨ tok.tag a = 18)
    (hhi : uIntBuf ≤ a → H.hS1 ≤ a ∧ a < H.heap2) : H.out.mem a = H.sP.mem a := by
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order H
  rw [suffix_keep_acct H hlo hhi]
  refine mid_keep H ?_ (fun h => by rcases hlo h with h | h | h <;> omega)
    (fun h => by have := hhi h; omega)
  by_cases hl : a < uIntBuf
  · omega
  · have := hhi (by omega); omega

/-- Where the tree lies at the end of the run: on the words of the old tree (tag `16`, below
`uIntBuf`), on the new words of Sync 1, or on the new words of the suffix. -/
theorem foot_cur {a : ℕ}
    (hf : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap H.curTreeTok a) :
    (a < uIntBuf ∧ tok.tag a = 16) ∨
      (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ a ∧ a < H.hS1) ∨
      (H.sX.regs 4 ≤ a ∧ a < H.nextHeap) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _⟩ := hTags
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, hSufFoot, _⟩ := H.suf
  rcases hSufFoot a hf with h | h
  · rcases hTreeFoot a h with h' | h'
    · exact Or.inl ⟨H.start.footLt a (Or.inr (Or.inl h')), hT16 a h'⟩
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h)

/-- The names: every external edge has a new name in `G1`, every name of `G1` is the new name of
an external edge, and every name of the old root graph is the old name of an external edge. -/
theorem names :
    (∀ e ∈ model.extG.E,
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e ∈
        H.G1.E) ∧
    (∀ ei ∈ H.G1.E, ∃ e ∈ model.extG.E,
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e = ei) ∧
    (∀ ei ∈ (model.chain.G 0).E, ∃ e ∈ model.extG.E, model.extToInt e = ei) := by
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := H.start.rep0
  obtain ⟨_, hFr1, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.start.refresh
  have hE1 := hFr1.hE
  have hE0 := hFreshInv0.hE
  rw [← H.Uint_eq, ← H.G1_eq] at hE1
  refine ⟨fun e he => ?_, fun ei hei => ?_, fun ei hei => ?_⟩
  · rw [hE1]; exact Finset.mem_image_of_mem _ he
  · rw [hE1] at hei; simpa using hei
  · rw [hE0] at hei; simpa using hei

/-- The threshold pointer of an external edge at the end of the run is the one at the end of the
prefix, and its block lies below `uIntBuf` with tag `17` (an old name) or in `[hS1 + 3L, heap2)`
(a new name). -/
theorem thr_facts {e : ℕ} (he : e ∈ model.extG.E) :
    let ei := (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e
    H.out.mem (tok.edgeThresholds + ei) = H.sP.mem (tok.edgeThresholds + ei) ∧
    ((∀ j < L, H.sP.mem (tok.edgeThresholds + ei) + j < uIntBuf ∧
        tok.tag (H.sP.mem (tok.edgeThresholds + ei) + j) = 17) ∨
      (ei ∉ (model.chain.G 0).E ∧ H.hS1 + 3 * L ≤ H.sP.mem (tok.edgeThresholds + ei) ∧
        H.sP.mem (tok.edgeThresholds + ei) + L ≤ H.heap2)) := by
  intro ei
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, _, _, _, hT12, _, _, _, _, hT1718, _⟩ := hTags
  obtain ⟨hN1, _, hN3⟩ := names H
  have hCap : ei < tok.intCap := H.phaseX.capE ei (hN1 e he)
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x h))
  have ht12 := hT12 ei hCap
  have hPtr : H.out.mem (tok.edgeThresholds + ei) = H.sP.mem (tok.edgeThresholds + ei) :=
    acct_keep H (fun _ => Or.inl ht12)
      (fun h => absurd h (not_le.mpr (hLt (by rw [ht12]; decide))))
  refine ⟨hPtr, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCanon, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hIn, hNot⟩ := hCanon e he
  by_cases hOld : ei ∈ (model.chain.G 0).E
  · left
    obtain ⟨e', he', hee'⟩ := hN3 ei hOld
    intro j hj
    have h17 := (hT1718 e' he').1 j hj
    rw [hee', ← (hIn hOld).2.1] at h17
    exact ⟨hLt (by rw [h17]; decide), h17⟩
  · obtain ⟨h1, h2, _⟩ := hNot hOld
    exact Or.inr ⟨hOld, h1, h2⟩

/-- The place of the record block of an edge of `G1` off the new chain tree `Fp ∪ newE`: below
`uIntBuf` with tag `18` (an old off-tree edge), in `[h0, hS1)` (an edge that Sync 1 cut), the
block that the refresh wrote for a new name (in `[hS1 + 3L, heap2)`), or in
`[sX.regs 4, nextHeap)` (an edge that the suffix cut, by the premise `hCut`). -/
theorem rec_place
    (hCut : ∀ ei ∈ H.G1.E, ei ∈ H.F1 → ei ∉ H.Fp ∪ graphListEdgeUnion H.newFs →
      H.sX.regs 4 ≤ H.out.mem (tok.edgeRecords + ei) ∧
      H.out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ H.nextHeap)
    {ei : ℕ} (hei : ei ∈ H.G1.E) (hnot : ei ∉ H.Fp ∪ graphListEdgeUnion H.newFs) :
    (∀ j < 2 + 4 * L, H.out.mem (tok.edgeRecords + ei) + j < uIntBuf ∧
        tok.tag (H.out.mem (tok.edgeRecords + ei) + j) = 18) ∨
      (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.out.mem (tok.edgeRecords + ei) ∧
        H.out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ H.hS1) ∨
      (ei ∉ (model.chain.G 0).E ∧
        H.out.mem (tok.edgeRecords + ei) = H.sP.mem (tok.edgeRecords + ei) ∧
        H.hS1 + 3 * L ≤ H.out.mem (tok.edgeRecords + ei) ∧
        H.out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ H.heap2) ∨
      (H.sX.regs 4 ≤ H.out.mem (tok.edgeRecords + ei) ∧
        H.out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ H.nextHeap) := by
  by_cases hF1 : ei ∈ H.F1
  · exact Or.inr (Or.inr (Or.inr (hCut ei hei hF1 hnot)))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, _, _, _, _, hT13, _, _, _, hT1718, _⟩ := hTags
  obtain ⟨_, hN2, hN3⟩ := names H
  have hLt {x : ℕ} (h : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x h))
  have ht13 := hT13 ei (H.phaseX.capE ei hei)
  obtain ⟨_, _, _, _, _, _, _, hRec2, _⟩ := H.suf
  have hl13 := hLt (show tok.tag (tok.edgeRecords + ei) ≠ 0 by rw [ht13]; decide)
  have hPtr : H.out.mem (tok.edgeRecords + ei) = H.sP.mem (tok.edgeRecords + ei) := by
    rw [hRec2 ei hei hF1 hnot]
    have := (heap_order H).1
    have := (heap_order H).2.1
    have := (heap_order H).2.2.1
    exact mid_keep H (by omega) (fun _ => by rw [ht13]; omega) (fun h => absurd h (by omega))
  obtain ⟨e, he, rfl⟩ := hN2 ei hei
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hDel, hOff, _, _, _, _, _, hCanon, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hIn, hNot⟩ := hCanon e he
  rw [hPtr]
  by_cases hOld : (translateBatch model.extG model.extToInt model.intToExt model.nextFresh
      U).2.1 e ∈ (model.chain.G 0).E
  · rw [(hIn hOld).2.2.1]
    by_cases hTree : (translateBatch model.extG model.extToInt model.intToExt model.nextFresh
        U).2.1 e ∈ model.chain.toTreeChain.chainTree.E
    · have hD : Update.delete ((translateBatch model.extG model.extToInt model.intToExt
          model.nextFresh U).2.1 e) ∈
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2 := by
        rw [← H.Uint_eq, ← mem_batchDeletedEdges_iff]
        by_contra hc
        exact hF1 (by rw [H.F1_eq]; exact Finset.mem_sdiff.mpr ⟨hTree, by simpa using hc⟩)
      exact Or.inr (Or.inl (hDel _ hTree hD))
    · left
      obtain ⟨e', he', hee'⟩ := hN3 _ hOld
      intro j hj
      have h18 := (hT1718 e' he').2 (by rw [hee']; exact hTree) j hj
      rw [hee', ← hOff _ hOld hTree] at h18
      exact ⟨hLt (by rw [h18]; decide), h18⟩
  · obtain ⟨_, _, h3, h4, _⟩ := hNot hOld
    exact Or.inr (Or.inr (Or.inl ⟨hOld, rfl, h3, h4⟩))

end BranchBRunKFBL

end MinCostFlow.MinRatio
