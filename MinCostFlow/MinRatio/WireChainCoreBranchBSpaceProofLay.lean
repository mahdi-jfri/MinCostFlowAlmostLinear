module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProofSpace

/-!
# The footprint, handle, metadata, and slot fields of Branch B (`WireChainCoreBranchBSpaceProofLay`)

Proves the remaining fields of `BranchBSpaceFieldsKFBL` from `BranchBRunKFBL`:
* `branchBSpace_zero`, `branchBSpace_treeFoot`, `branchBSpace_coreFoot`,
  `branchBSpace_coreHandleLoc`, `branchBSpace_metaKeep`, `branchBSpace_metaNew`,
  `branchBSpace_slots` directly from `BranchBRunKFBL`;
* `branchBSpace_lastFoot_of_lastHandle` and `branchBSpaceFields_of_lastHandle`, which also
  establish `lastFoot` and assemble the full `BranchBSpaceFieldsKFBL` structure given the
  terminal-handle location fact
  `(H.fr ≤ cfg.P.d → H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)) ∧
   (H.fr = cfg.P.d + 1 → H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section Helpers

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

private lemma branchBSpace_sufAgree_tag
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {a t : ℕ} (ht : tok.tag a = t) (h0 : t ≠ 0) (h1 : t ≠ 1) (h9 : t ≠ 9) (h10 : t ≠ 10)
    (h11 : t ≠ 11) (h13 : t ≠ 13) (h14 : t ≠ 14) (h15 : t ≠ 15) (h16 : t ≠ 16) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  have haU : a < uIntBuf := H.start.footLt a (Or.inl (hOwn a (ht ▸ h0)))
  have hHeaps := branchBSpace_heaps H
  have hne11 : a ≠ root + 11 := fun heq => by
    have h11t := hT1 11 (by omega)
    rw [← heq, ht] at h11t
    exact h1 h11t
  exact H.suf.2.2.2.2.2.2.2.2.1 a
    ⟨by omega, hne11, fun _ => ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩, fun hu => by omega⟩

private lemma branchBSpace_sufAgree_handle
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {r : ℕ} (hr : r ≤ cfg.P.d) :
    H.out.mem (tok.handle + 18 + r) = H.sX.mem (tok.handle + 18 + r) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨_, _, _, _, hT4, _⟩ := hTags
  exact branchBSpace_sufAgree_tag H (hT4 r (by omega)) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

private lemma branchBSpace_sufAgree_meta
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {r : ℕ} (hr : r < 2 * cfg.P.d) :
    H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + r) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + r) := by
  obtain ⟨_, _, _, _, hMetaTag, _⟩ := H.start.meta0
  exact branchBSpace_sufAgree_tag H (hMetaTag r hr) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)

private lemma branchBSpace_sufAgree_slot
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {a : ℕ} (ha1 : heap ≤ a) (ha2 : a < heap + 1 + 12 * cfg.P.d) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  have h11Lt : root + 11 < uIntBuf :=
    H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide)))
  have hHeaps := branchBSpace_heaps H
  have hTree1 := H.pre.2.2.2.2.2.2.2.2.2.1
  exact H.suf.2.2.2.2.2.2.2.2.1 a ⟨by omega, by omega, fun hu => by omega, fun _ hf => by
    rcases hTree1 a hf with hOld | hNew
    · have := H.start.footLt a (Or.inr (Or.inl hOld)); omega
    · omega⟩

private lemma branchBSpace_sufAgree_fresh
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {a : ℕ} (ha1 : H.heap2 ≤ a) (ha2 : a < H.sX.regs 4) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  have h11Lt : root + 11 < uIntBuf :=
    H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide)))
  have hHeaps := branchBSpace_heaps H
  have hhS1Le : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
  have hTree1 := H.pre.2.2.2.2.2.2.2.2.2.1
  exact H.suf.2.2.2.2.2.2.2.2.1 a ⟨ha2, by omega, fun hu => by omega, fun _ hf => by
    rcases hTree1 a hf with hOld | hNew
    · have := H.start.footLt a (Or.inr (Or.inl hOld)); omega
    · omega⟩

end Helpers

section Fields

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
  {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ}
  {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
  {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
  {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
  {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
  {stepCap : ℕ → ℕ → ℕ}
  {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
  {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

/-- Field `zero` of `BranchBSpaceFieldsKFBL`: memory is zero from `H.nextHeap` onward. -/
theorem branchBSpace_zero
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ZeroFrom H.out.mem H.nextHeap :=
  H.suf.2.2.2.1

/-- Field `treeFoot` of `BranchBSpaceFieldsKFBL`: every word of the final path-tree footprint
lies in the old tree footprint, in `[heap + 1 + 12 * d, H.heap2)`, or in `[H.sX.regs 4, H.nextHeap)`. -/
theorem branchBSpace_treeFoot
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ a,
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap H.curTreeTok a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap + 1 + 12 * cfg.P.d ≤ a ∧ a < H.heap2) ∨ (H.sX.regs 4 ≤ a ∧ a < H.nextHeap) := by
  intro a ha
  rcases H.suf.2.2.2.2.2.1 a ha with h1 | hSuf
  · rcases H.pre.2.2.2.2.2.2.2.2.2.1 a h1 with hOld | hPre
    · exact Or.inl hOld
    · have hhS1Le : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inr hSuf)

/-- Field `coreFoot` of `BranchBSpaceFieldsKFBL`: every word of core `j`'s footprint either lies
below `heap` with old tag `21 + j` or lies in `[H.heap2, H.sX.regs 4)`. -/
theorem branchBSpace_coreFoot
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < cfg.P.d, ∀ a, Rcore.foot (H.out.mem (tok.handle + 18 + j)) (H.tokN j) a →
      (a < heap → tok.tag a = 21 + j) ∧ (heap ≤ a → H.heap2 ≤ a ∧ a < H.sX.regs 4) := by
  intro j hj a ha
  rw [branchBSpace_sufAgree_handle H hj.le] at ha
  have hHeaps := branchBSpace_heaps H
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hCH : H.A.coreH j = tok.coreHandle j := by
    rw [H.A_eq]; simp [branchBAddrsOf, hj]
  rw [← hHB] at ha
  rcases (H.exitOut.reps j hj).2 a ha with hLoop | hExit
  · rcases H.loop.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj a hLoop with hOld | hMid
    · rw [hCH] at hOld
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
      have hTag : tok.tag a = 21 + j := hTags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj a hOld
      have haLt : a < uIntBuf := H.start.footLt a (Or.inr (Or.inr ⟨j, hj, hOld⟩))
      exact ⟨fun _ => hTag, fun hge => by omega⟩
    · have hsF0 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
      exact ⟨fun hlt => by omega, fun _ => ⟨by omega, by omega⟩⟩
  · exact ⟨fun hlt => by omega, fun _ => ⟨by omega, hExit.2⟩⟩

/-- Field `coreHandleLoc` of `BranchBSpaceFieldsKFBL`: each core handle either kept its start
value from `mem0` or lies in `[H.sE.regs 4, H.hT)`. -/
theorem branchBSpace_coreHandleLoc
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < cfg.P.d,
      H.out.mem (tok.handle + 18 + j) = mem0 (tok.handle + 18 + j) ∨
      (H.sE.regs 4 ≤ H.out.mem (tok.handle + 18 + j) ∧ H.out.mem (tok.handle + 18 + j) < H.hT) := by
  intro j hj
  rw [branchBSpace_sufAgree_handle H hj.le]
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  by_cases hlt : j < H.fr
  · left
    have hLow := H.exitOut.handlesLow j (by omega)
    rw [hHB] at hLow
    have hCH : H.A.coreH j = tok.coreHandle j := by
      rw [H.A_eq]; simp [branchBAddrsOf, hj]
    have hCore0 : mem0 (tok.handle + 18 + j) = tok.coreHandle j :=
      (H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).1
    rw [hLow, hCH, hCore0]
  · right
    have hge : H.fr ≤ j := by omega
    have hRep := (H.exitOut.reps j hj).1
    have hFoot := H.handleFoot _ _ _ _ hRep
    have hNew := (H.exitOut.newCores j hge hj).2.2 _ hFoot
    rwa [hHB] at hNew

/-- Field `metaKeep` of `BranchBSpaceFieldsKFBL`: for every level `j < min (H.fr + 1) cfg.P.d`,
both metadata pointers (graph and lengths) keep their `mem0` values. -/
theorem branchBSpace_metaKeep
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < min (H.fr + 1) cfg.P.d,
      H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
      H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := by
  intro j hj
  have hjd : j < cfg.P.d := by omega
  have hLM : H.A.levelMeta = solverLevelMetaAddr tok.table cfg.P.d := by rw [H.A_eq]; rfl
  have hG0 : H.A.gPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
    rw [H.A_eq]; rfl
  have hL0 : H.A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := by
    rw [H.A_eq]; rfl
  have hOutG : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
    rw [Nat.add_assoc]
    exact branchBSpace_sufAgree_meta H (by omega)
  have hOutL : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + j) :=
    branchBSpace_sufAgree_meta H (by omega)
  have hKeep := H.exitOut.metaKeep j hj
  have hCells := H.loop.2.2.2.2.1.cells j hjd
  rw [hLM] at hKeep hCells
  exact ⟨by rw [hOutG, hKeep.2, hCells.2.2.2.2.2.2.1, hG0],
    by rw [hOutL, hKeep.1, hCells.2.2.2.2.2.2.2.1, hL0]⟩

/-- Field `metaNew` of `BranchBSpaceFieldsKFBL`: for every rebuilt level `fr + 1 ≤ j < d`, its
new graph and length blocks lie in `[H.sE.regs 4, H.hT)` off all core and last-level footprints. -/
theorem branchBSpace_metaNew
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j, H.fr + 1 ≤ j → j < cfg.P.d →
      let gp := H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
      let lp := H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)
      H.sE.regs 4 ≤ gp ∧ gp + dynGraphSize vCap eCap ≤ H.hT ∧ H.sE.regs 4 ≤ lp ∧
        lp + eCap * L ≤ H.hT ∧
      ∀ a, ((gp ≤ a ∧ a < gp + dynGraphSize vCap eCap) ∨ (lp ≤ a ∧ a < lp + eCap * L)) →
        (∀ r < cfg.P.d, ¬ Rcore.foot (H.out.mem (tok.handle + 18 + r)) (H.tokN r) a) ∧
        ¬ (LastLevelProgram.lastLevelRepresentation H.vcL H.ecL 4 L P
          ((alg2PreResetState cfg model U
            (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
            (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G
            cfg.P.d).E).foot
          (H.out.mem (tok.handle + 18 + cfg.P.d)) H.termTokN a := by
  intro j hj1 hj2
  have hLM : H.A.levelMeta = solverLevelMetaAddr tok.table cfg.P.d := by rw [H.A_eq]; rfl
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hOutG : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
    rw [Nat.add_assoc]; exact branchBSpace_sufAgree_meta H (by omega)
  have hOutL : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + j) :=
    branchBSpace_sufAgree_meta H (by omega)
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hNew := H.exitOut.metaNew j hj1 hj2
  dsimp only at hNew ⊢
  rw [hLM, hHB] at hNew
  rw [hOutG, hOutL, ← hXEq]
  refine ⟨hNew.1, hNew.2.1, hNew.2.2.1, hNew.2.2.2.1, fun a ha => ?_⟩
  obtain ⟨hCores, hLast⟩ := hNew.2.2.2.2 a ha
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [branchBSpace_sufAgree_handle H hr.le]
    exact hCores r hr
  · rw [branchBSpace_sufAgree_handle H le_rfl]
    exact hLast

/-- Field `slots` of `BranchBSpaceFieldsKFBL`: for every finished level `j < min H.fr cfg.P.d`,
`SelOutLevelMemAt` transfers from `H.exitOut.zone` at `H.sX.mem` to `H.out.mem` across the
suffix of Branch B. -/
theorem branchBSpace_slots
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < min H.fr cfg.P.d,
      SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun x => BranchBSelZone H.heap2 (H.sE.regs 4) H.hT (H.sX.regs 4) x ∧
          ∀ r < cfg.P.d, ¬ Rcore.foot (H.out.mem (tok.handle + 18 + r)) (H.tokN r) x)
        (fun x => Rcore.foot (H.out.mem (tok.handle + 18 + j)) (H.tokN j) x ∨
          (H.heap2 ≤ x ∧ x < H.sX.regs 4))
        H.heap2 (H.sX.regs 4) H.out.mem (heap + 1 + 12 * j) (H.D j) (model.chain.G j)
        (H.levelU j)
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G j).E
        (cfg.T.lsfs ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.scState j)
          ((alg2PreResetState cfg model U
            (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
            (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.bran
            j)).wstr := by
  intro j hj
  have hjd : j < cfg.P.d := by omega
  have hZone := H.exitOut.zone j hj
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hSt0G : H.st0.G j = model.chain.G j := by rw [H.st0_eq]
  have hChEq := branchB_chain_lt_eq H hj
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  rw [hHF, hSB, hHB, hSt0G, hChEq.1, hChEq.2.1, hChEq.2.2, hXEq] at hZone
  have hCF := branchBSpace_coreFoot H
  refine hZone.transfer ?_ ?_ ?_ ?_ le_rfl le_rfl
  · intro i hi
    exact branchBSpace_sufAgree_slot H (by omega) (by omega)
  · intro a ha
    rcases ha with ⟨h1, h2, _⟩ | (hFoot | ⟨h1, h2⟩)
    · exact branchBSpace_sufAgree_fresh H h1 h2
    · rw [← branchBSpace_sufAgree_handle H hjd.le] at hFoot
      by_cases hlt : a < heap
      · have hTag := (hCF j hjd a hFoot).1 hlt
        exact branchBSpace_sufAgree_tag H hTag (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      · obtain ⟨h1, h2⟩ := (hCF j hjd a hFoot).2 (by omega)
        exact branchBSpace_sufAgree_fresh H h1 h2
    · exact branchBSpace_sufAgree_fresh H h1 h2
  · intro a _ _ ⟨hz, hr⟩
    refine ⟨hz, fun r hrLt => ?_⟩
    rw [branchBSpace_sufAgree_handle H hrLt.le]
    exact hr r hrLt
  · intro a ha
    rcases ha with hFoot | hFresh
    · left
      rw [branchBSpace_sufAgree_handle H hjd.le]
      exact hFoot
    · exact Or.inr hFresh

/-- Field `lastFoot` of `BranchBSpaceFieldsKFBL`, given the terminal-handle location fact
`hLastH` after the exit of Branch B. -/
theorem branchBSpace_lastFoot_of_lastHandle
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hLastH : (H.fr ≤ cfg.P.d → H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)) ∧
      (H.fr = cfg.P.d + 1 → H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d)) :
    ∀ a, (LastLevelProgram.lastLevelRepresentation H.vcL H.ecL 4 L P
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G
          cfg.P.d).E).foot
        (H.out.mem (tok.handle + 18 + cfg.P.d)) H.termTokN a →
      (a < heap → tok.tag a = 19) ∧ (heap ≤ a → H.sE.regs 4 ≤ a ∧ a < H.hT) ∧
      ∀ j < cfg.P.d, ¬ Rcore.foot (H.out.mem (tok.handle + 18 + j)) (H.tokN j) a := by
  intro a ha
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  rw [branchBSpace_sufAgree_handle H le_rfl, ← hXEq, ← hHB] at ha
  refine ⟨?_, ?_, ?_⟩
  · intro haLt
    have hHeaps := branchBSpace_heaps H
    by_cases hfr : H.fr ≤ cfg.P.d
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
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
      exact hTags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hOldFoot
  · intro haGe
    rcases H.exitOut.lastLoc a ha with hlt | hIn
    · rw [hSB] at hlt; omega
    · exact hIn
  · intro j hj
    rw [branchBSpace_sufAgree_handle H hj.le, ← hHB]
    exact (H.exitOut.lastFoot a ha).2 j hj

/-- All ten fields of `BranchBSpaceFieldsKFBL` from `BranchBRunKFBL` and the terminal-handle
location fact `hLastH`. -/
theorem branchBSpaceFields_of_lastHandle
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hLastH : (H.fr ≤ cfg.P.d → H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)) ∧
      (H.fr = cfg.P.d + 1 → H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d)) :
    BranchBSpaceFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost :=
  { heaps := branchBSpace_heaps H
    space := branchBSpace_space H
    zero := branchBSpace_zero H
    treeFoot := branchBSpace_treeFoot H
    coreFoot := branchBSpace_coreFoot H
    coreHandleLoc := branchBSpace_coreHandleLoc H
    lastFoot := branchBSpace_lastFoot_of_lastHandle H hLastH
    metaKeep := branchBSpace_metaKeep H
    metaNew := branchBSpace_metaNew H
    slots := branchBSpace_slots H }

end Fields

end MinCostFlow.MinRatio
