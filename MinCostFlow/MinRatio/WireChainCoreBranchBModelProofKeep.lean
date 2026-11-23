module

public import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofBase
import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import WordRAM.Tactic

/-!
# Kept-word and schedule fields for `BranchBModelGoalKFBL` (`WireChainCoreBranchBModelProofKeep`)

Proves the kept-word and schedule fields of `BranchBModelFieldsKFBL` from `BranchBRunKFBL`:
* `branchBModel_prefixFrame`: recovers the prefix frame at `ec0 := eCap` by invoking
  `wireBranchBPrefixKFBL_runs` and identifying the resulting state with `H.sP` via `Runs.det`.
* `branchBModel_keepMem`: chains the frames across all stages (`mem → sP → sF0 → sE → sX → out`)
  for any address `a < heap` outside the modified tags and counter arrays.
* `branchBModel_rootDir`, `branchBModel_header`, `branchBModel_table`, `branchBModel_metaCells`,
  `branchBModel_fresh`, `branchBModel_frameMem`, and `branchBModel_sched`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section KeepFields

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

/-- Prefix frame at `ec0 := eCap`: invokes `wireBranchBPrefixKFBL_runs` at `ec0 := eCap` and
identifies the end state with `H.sP` via `Runs.det`. Any address `a < heap` other than `root + 11`
outside `[mem0 lm, mem0 lm + eCap * L)` whose tag (when `a < uIntBuf`) avoids `{9, …, 16}` keeps
its value from `mem` to `H.sP`. -/
theorem branchBModel_prefixFrame
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ a < heap, a ≠ root + 11 →
      (a < uIntBuf →
        tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 12 ∧
        tok.tag a ≠ 13 ∧ tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
      (a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      H.sP.mem a = mem a := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, _, _, _, hT4, _, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, _⟩ := hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
  -- Level-0 metadata at `ec0 := eCap`
  set lm := solverLevelMetaAddr tok.table cfg.P.d
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootEq, vcOf, ecOf, hLev, _, _⟩, hBatchCaps, hG0'Cap, _⟩ :=
    H.start.modelInv
  have hCap0 : vcOf 0 = vCap ∧ ecOf 0 = eCap :=
    dynGraphAt_caps_eq (hLev 0 hdPos).1 (H.start.caps0 0 hdPos)
  have hRootCap : model.extG.n = vCap ∧ tok.rootECap = eCap := by
    have hDG0 := H.start.caps0 0 hdPos
    rw [hRootEq] at hDG0
    exact dynGraphAt_caps_eq hWire0.2.1 hDG0
  have hTagL0 : ∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d := by
    intro x h1 h2
    have hL := (hLev 0 hdPos).2.2.2.1
    rw [add_zero, hCap0.2] at hL
    exact hL x h1 h2
  have hLevel0Meta :
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < eCap) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < eCap) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < eCap | _ => True) := by
    refine ⟨by simpa [lm] using (hLev 0 hdPos).2.1, hTagL0, (H.start.caps0 0 hdPos).2.2.1,
      fun e he => by rw [← hRootCap.2]; exact (hG0'Cap e he).1, fun u hu => ?_⟩
    have hU := hBatchCaps u hu
    cases u with
    | insert ei _ _ => rw [← hRootCap.2]; exact hU
    | delete _ => trivial
    | split _ _ _ _ => trivial
  -- Terminal forest pointers at `mem`
  have hOldT := branchBOldTermForest_of_rep H.start.rep0 H.start.modelInv
  dsimp only at hOldT
  obtain ⟨hTermH0, hTermB0, hTagT1, hTagT2, _, _⟩ := hOldT
  set lsfHdr := mem0 (tok.termHandle + 1 + model.chain.lastBran)
  set forestPtr := mem0 (lsfHdr + 1)
  have hHB0Lt : tok.handle + 18 + cfg.P.d < uIntBuf :=
    hLt (by rw [hT4 cfg.P.d (by omega)]; decide)
  have hBB0Lt : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < uIntBuf := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [h1]
    exact hLt (by rw [hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
  have hTermHMem : mem (tok.handle + 18 + cfg.P.d) = tok.termHandle := by
    rw [H.start.memEq _ hHB0Lt (by rw [hT4 cfg.P.d (by omega)]; decide)
      (by rw [hT4 cfg.P.d (by omega)]; decide) (by rw [hT4 cfg.P.d (by omega)]; decide)]
    exact hTermH0
  have hTermBMem : mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = model.chain.lastBran := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [H.start.memEq _ hBB0Lt (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)]
    exact hTermB0
  have hT1Lt : tok.termHandle + 1 + model.chain.lastBran < uIntBuf :=
    hLt (by rw [hTagT1]; decide)
  have hT2Lt : lsfHdr + 1 < uIntBuf := hLt (by rw [hTagT2]; decide)
  have hLsfHdrMem : mem (tok.termHandle + 1 + model.chain.lastBran) = lsfHdr :=
    (H.start.memEq _ hT1Lt (by rw [hTagT1]; decide) (by rw [hTagT1]; decide)
      (by rw [hTagT1]; decide))
  have hForestPtrMem : mem (lsfHdr + 1) = forestPtr :=
    (H.start.memEq _ hT2Lt (by rw [hTagT2]; decide) (by rw [hTagT2]; decide)
      (by rw [hTagT2]; decide))
  have hSpB := H.envA.ops.spaceTotalBranchB U.length
  have hRoomH := H.start.room
  have hRoomPre : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L + 1 + 3 * L + U.length * wireRefreshOneSpace L < 2 ^ w := by
    omega
  obtain ⟨r4, r70, r71, _, r73, r75, _, r77, r78, _, r80, _, _, r83, _, _, r87, r90, r91, _, _,
    r94, _, _⟩ := H.dispatch.2.2.1
  obtain ⟨out', c', hS1', heap2', memS1', _, _, _, _, _, rPre', _, _, hh0', _, _, _, _, _, _, _,
    _, hFr1', hFr2', _⟩ :=
    wireBranchBPrefixKFBL_runs (ec0 := eCap) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      H.envB.collectP H.envB.emitP H.envB.zeroP H.envA.refAccP H.envA.refOneP H.envA.updLen0P
      H.envA.four H.envA.lPos H.envA.pW H.envA.w18 H.envA.treeImpl H.envA.bindC H.envA.canonC
      H.envA.isNegC H.envA.shiftC H.envA.divC H.envA.addC H.envA.subC H.envA.negC H.envA.copyC
      H.start.rep0 H.start.meta0 H.start.num0 H.start.offInv0 H.start.offBd0 H.start.modelInv
      H.start.logW H.start.capT H.start.refresh H.start.memEq H.start.fresh H.start.trNf
      H.start.batch H.start.small H.start.footLt H.start.gLt H.start.lLt H.start.uLe H.start.edHeap
      hLevel0Meta H.start.zero H.dispatch.1
      ⟨r4, r70, r71, r73, r75, r77, r78, r80, r83, r87, r90, r91, r94⟩
      hTermHMem hTermBMem hLsfHdrMem hForestPtrMem (by omega) (by omega) (by omega) hRoomPre
  have hDet := Runs.det H.pre.1 rPre'
  have hsPEq : H.sP = out' := hDet.2.1
  intro a ha hR11 hTag hOffL0
  have hNotSlot : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
      a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei := by
    intro ei hei _
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have ht := hT9 ei hei; rw [← h] at ht
      exact (hTag (hLt (by rw [ht]; decide))).1 ht
    · have ht := hT12 ei hei; rw [← h] at ht
      exact (hTag (hLt (by rw [ht]; decide))).2.2.2.1 ht
    · have ht := hT13 ei hei; rw [← h] at ht
      exact (hTag (hLt (by rw [ht]; decide))).2.2.2.2.1 ht
  rw [hsPEq]
  have hStep2 := hFr2' a (by omega) hNotSlot hOffL0
  have hStep1 := hFr1' a (by omega) hR11 (fun hU => by
    have ht := hTag hU
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2⟩)
  rw [hStep2, hStep1, Function.update_of_ne (by omega)]

/-- Unified memory preservation across all stages of Branch B (`mem → H.out.mem`) for any address
`a < heap` outside `root + 11`, the modified solver regions, and the level counter arrays
`rcBase[0..d)` and `ucBase[0..d)`. -/
theorem branchBModel_keepMem
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {a : ℕ} (ha : a < heap) (hR11 : a ≠ root + 11)
    (hTag : a < uIntBuf →
      tok.tag a ≠ 4 ∧ tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 12 ∧
      tok.tag a ≠ 13 ∧ tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16 ∧ tok.tag a ≠ 20 ∧
      tok.tag a ≠ 22 + cfg.P.d ∧ tok.tag a ≠ 23 + cfg.P.d ∧ ∀ j < cfg.P.d, tok.tag a ≠ 21 + j)
    (hOffRC : a < tok.levelsEnd + 2 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 2 * (cfg.P.d + 1) + cfg.P.d ≤ a)
    (hOffUC : a < tok.levelsEnd + 3 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 3 * (cfg.P.d + 1) + cfg.P.d ≤ a) :
    H.out.mem a = mem a := by
  set d := cfg.P.d
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, hT16, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, _, hMetaTag, _⟩ := H.start.meta0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := H.start.modelInv
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
  -- Heap ordering across stages
  obtain ⟨_, _, _, _, _, _, _, _, hsLm, _, _, hsEr4, _, _, hLoopFr, hLoopFoot, _⟩ := H.loop
  have hh0Le : heap + 1 + 12 * d + 3 * (d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
  have hhS1Le : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
  have hsF0r4 : H.sF0.regs 4 = H.heap2 + (editsPtr - d - uIntBuf) := H.front.2.2.1
  have hsXr4 : H.sE.regs 4 ≤ H.sX.regs 4 := H.exitOut.heapLo
  -- Separation from old cores, level graphs, and level lengths
  have hdPos : 0 < d := H.start.modelInv.1.1
  have hCapEq (j : ℕ) (hj : j < d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (H.start.caps0 j hj)
  have hOffL (j : ℕ) (hj : j < d) : a < H.A.lPtr0 j ∨ H.A.lPtr0 j + eCap * L ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    rw [H.A_eq] at hc
    obtain ⟨_, he⟩ := hCapEq j hj
    have hL := (hLev j hj).2.2.2.1
    rw [he] at hL
    have ht := hL a hc.1 hc.2
    exact (hTag (hLt (by rw [ht]; omega))).2.2.2.2.2.2.2.2.2.2.2.1 ht
  -- Stage 1: `mem → sP`
  have hOffL0 : a < mem0 (solverLevelMetaAddr tok.table d) ∨
      mem0 (solverLevelMetaAddr tok.table d) + eCap * L ≤ a := by
    have h := hOffL 0 hdPos
    rw [H.A_eq] at h
    simpa [branchBAddrsOf] using h
  have h1 : H.sP.mem a = mem a := branchBModel_prefixFrame H a ha hR11 (fun hU => by
    have ht := hTag hU
    exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.1⟩) hOffL0
  -- Stage 2: `sP → sF0`
  have h2 : H.sF0.mem a = H.sP.mem a := H.front.2.2.2.1 a (by omega)
  have hCoreH (j : ℕ) (hj : j < d) : H.A.coreH j = tok.coreHandle j := by
    rw [H.A_eq]; show (if j < d then tok.coreHandle j else tok.termHandle) = _; simp [hj]
  have hOffCore (j : ℕ) (hj : j < d) : ¬ Rcore.foot (H.A.coreH j) (tok.coreTok j) a := by
    rw [hCoreH j hj]
    intro hf
    have ht := hT21 j hj a hf
    exact (hTag (hLt (by rw [ht]; omega))).2.2.2.2.2.2.2.2.2.2.2.2 j hj ht
  have hOffG (j : ℕ) (hj : j < d) :
      a < H.A.gPtr0 j ∨ H.A.gPtr0 j + dynGraphSize vCap eCap ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    rw [H.A_eq] at hc
    obtain ⟨hv, he⟩ := hCapEq j hj
    have hG := (hLev j hj).2.2.2.2
    rw [hv, he] at hG
    have ht := (hG a hc.1 hc.2).1
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0] at ht
      exact (hTag (hLt (by rw [ht]; decide))).2.2.2.2.2.2.2.2.2.1 ht
    · rw [ite_eq_right hj0] at ht
      exact (hTag (hLt (by rw [ht]; omega))).2.2.2.2.2.2.2.2.2.2.2.1 ht
  have hSelEq : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hUCEq : H.A.ucBase = tok.levelsEnd + 3 * (d + 1) := by rw [H.A_eq]; rfl
  have hRCEq : H.A.rcBase = tok.levelsEnd + 2 * (d + 1) := by rw [H.A_eq]; rfl
  have hHBEq : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hBBEq : H.A.branchBase = tok.handle + 18 + (d + 1) := by rw [H.A_eq]; rfl
  have hLMEq : H.A.levelMeta = solverLevelMetaAddr tok.table d := by rw [H.A_eq]; rfl
  -- Stage 3: `sF0 → sE`
  have h3 : H.sE.mem a = H.sF0.mem a := by
    rw [← hsLm]
    exact hLoopFr a (by omega) hOffCore (fun j hj => ⟨hOffG j hj, hOffL j hj⟩)
      (fun j hj => by rw [hUCEq]; omega) (Or.inl (by rw [hSelEq]; exact ha))
  -- Stage 4: `sE → sX`
  have hOffCoreE (j : ℕ) (hj : j < d) : ¬ Rcore.foot (H.A.coreH j) (H.tokE j) a := fun hf => by
    rcases hLoopFoot j hj a hf with hOld | hNew
    · exact hOffCore j hj hOld
    · omega
  have hOffHB : a < H.A.handleBase ∨ H.A.handleBase + d < a := by
    by_contra hc
    simp only [not_or, not_lt] at hc
    rw [hHBEq] at hc
    have ht : tok.tag a = 4 := by
      have h := hT4 (a - (tok.handle + 18)) (by omega)
      rwa [show tok.handle + 18 + (a - (tok.handle + 18)) = a by omega] at h
    exact (hTag (hLt (by rw [ht]; decide))).1 ht
  have hOffBB : a < H.A.branchBase ∨ H.A.branchBase + d < a := by
    by_contra hc
    simp only [not_or, not_lt] at hc
    rw [hBBEq] at hc
    have ht : tok.tag a = 4 := by
      have h := hT4 (d + 1 + (a - (tok.handle + 18 + (d + 1)))) (by omega)
      rwa [show tok.handle + 18 + (d + 1 + (a - (tok.handle + 18 + (d + 1)))) = a by omega] at h
    exact (hTag (hLt (by rw [ht]; decide))).1 ht
  have hOffLM : a < H.A.levelMeta ∨ H.A.levelMeta + 2 * d ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    rw [hLMEq] at hc
    have ht : tok.tag a = 22 + d := by
      have h := hMetaTag (a - solverLevelMetaAddr tok.table d) (by omega)
      rwa [show solverLevelMetaAddr tok.table d + (a - solverLevelMetaAddr tok.table d) = a by
        omega] at h
    exact (hTag (hLt (by rw [ht]; omega))).2.2.2.2.2.2.2.2.2.2.1 ht
  have h4 : H.sX.mem a = H.sE.mem a :=
    H.exitOut.frame a (by rw [hSelEq]; exact ha) hOffCoreE hOffHB hOffBB hOffLM
      (by rw [hRCEq]; exact hOffRC) hOffG (by rw [hUCEq]; exact hOffUC)
  -- Stage 5: `sX → out`
  have hTreeFootPre := H.pre.2.2.2.2.2.2.2.2.2.1
  have hOffTree1 : uIntBuf ≤ a →
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap H.curTreeTok1 a := by
    intro hGe hf
    rcases hTreeFootPre a hf with hOld | hNew
    · have hlt := H.start.footLt a (Or.inr (Or.inl hOld))
      omega
    · omega
  have hSufFr := H.suf.2.2.2.2.2.2.2.2.2.1
  have h5 : H.out.mem a = H.sX.mem a :=
    hSufFr a (by omega) hR11 (fun hU => by
      have ht := hTag hU
      exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
        ht.2.2.2.2.2.2.2.2.1⟩) hOffTree1
  rw [h5, h4, h3, h2, h1]

/-- Any address whose old tag is `t` (with `t ≠ 0`, `t ≠ 4`, `t ≠ 5`, `t ∉ [9..16]`, `t ≠ 20`,
`t ≠ 22 + d`, `t ≠ 23 + d`, `∀ j < d, t ≠ 21 + j`) and that is not `root + 11` keeps its value from
`mem` to `H.out.mem`. -/
private theorem branchBModel_keepMem_of_tag
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {a t : ℕ} (ht : tok.tag a = t) (hR11 : a ≠ root + 11)
    (ht0 : t ≠ 0) (ht4 : t ≠ 4) (ht5 : t ≠ 5)
    (ht9 : t < 9 ∨ 16 < t) (ht20 : t ≠ 20) (ht22 : t ≠ 22 + cfg.P.d) (ht23 : t ≠ 23 + cfg.P.d)
    (htCore : ∀ j < cfg.P.d, t ≠ 21 + j) :
    H.out.mem a = mem a := by
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  obtain ⟨hOwn, _, _, _, _, hT5, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have haU : a < uIntBuf := H.start.footLt a (Or.inl (hOwn a (by rw [ht]; exact ht0)))
  have hOffRC : a < tok.levelsEnd + 2 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 2 * (cfg.P.d + 1) + cfg.P.d ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    have h5 := hT5 (2 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 2 * (cfg.P.d + 1)))) (by omega)
    rw [show tok.levelsEnd + (2 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 2 * (cfg.P.d + 1)))) = a by
      omega, ht] at h5
    exact ht5 h5
  have hOffUC : a < tok.levelsEnd + 3 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 3 * (cfg.P.d + 1) + cfg.P.d ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    have h5 := hT5 (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) (by omega)
    rw [show tok.levelsEnd + (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) = a by
      omega, ht] at h5
    exact ht5 h5
  refine branchBModel_keepMem H (by omega) hR11 (fun _ => ?_) hOffRC hOffUC
  rw [ht]
  exact ⟨ht4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ht20,
    ht22, ht23, htCore⟩

theorem branchBModel_rootDir
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < 16, j ≠ 11 → H.out.mem (root + j) = mem0 (root + j) := by
  intro j hj hne
  obtain ⟨hOwn, hT1, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ht := hT1 j hj
  have haU : root + j < uIntBuf := H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
  rw [branchBModel_keepMem_of_tag H ht (by omega) (by decide) (by decide) (by decide) (by omega)
    (by decide) (by omega) (by omega) (fun _ _ => by omega)]
  exact H.start.memEq _ haU (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)

theorem branchBModel_header
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j < 18, H.out.mem (tok.handle + j) = mem0 (tok.handle + j) := by
  intro j hj
  obtain ⟨hOwn, hT1, hT2, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ht := hT2 j hj
  have haU : tok.handle + j < uIntBuf := H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
  have hR11 : tok.handle + j ≠ root + 11 := fun h => by
    have h1 := hT1 11 (by omega); rw [← h, ht] at h1; omega
  rw [branchBModel_keepMem_of_tag H ht hR11 (by decide) (by decide) (by decide) (by omega)
    (by decide) (by omega) (by omega) (fun _ _ => by omega)]
  exact H.start.memEq _ haU (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)

theorem branchBModel_table
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ j ≤ cfg.P.d, H.out.mem (tok.table + j) = mem0 (tok.table + j) := by
  intro j hj
  obtain ⟨hOwn, hT1, _, hT3, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ht := hT3 j hj
  have haU : tok.table + j < uIntBuf := H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
  have hR11 : tok.table + j ≠ root + 11 := fun h => by
    have h1 := hT1 11 (by omega); rw [← h, ht] at h1; omega
  rw [branchBModel_keepMem_of_tag H ht hR11 (by decide) (by decide) (by decide) (by omega)
    (by decide) (by omega) (by omega) (fun _ _ => by omega)]
  exact H.start.memEq _ haU (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)

theorem branchBModel_metaCells
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.out.mem (solverN0Addr tok.table cfg.P.d) = mem0 (solverN0Addr tok.table cfg.P.d) ∧
    (∀ j < cfg.P.d, H.out.mem (solverLvlMAddr tok.table cfg.P.d + j) =
      mem0 (solverLvlMAddr tok.table cfg.P.d + j)) ∧
    H.out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
      mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
    H.out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
      mem0 (solverSelectBlocksAddr tok.table cfg.P.d) := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  obtain ⟨hOwn, hT1, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨_, hN0T, hSHT, hSBT⟩, _, _, hLvlMT, _⟩ := H.start.meta0
  have hKeep21 : ∀ a, tok.tag a = 21 + cfg.P.d → H.out.mem a = mem0 a := fun a ht => by
    have haU : a < uIntBuf := H.start.footLt a (Or.inl (hOwn a (by rw [ht]; omega)))
    have hR11 : a ≠ root + 11 := fun h => by
      have h1 := hT1 11 (by omega); rw [← h, ht] at h1; omega
    rw [branchBModel_keepMem_of_tag H ht hR11 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (fun j hj => by omega)]
    exact H.start.memEq a haU (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega)
  exact ⟨hKeep21 _ hN0T, fun j hj => hKeep21 _ (hLvlMT j hj), hKeep21 _ hSHT, hKeep21 _ hSBT⟩

theorem branchBModel_fresh
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    FreshTablesAt H.out.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 := by
  obtain ⟨_, hT1, _, _, _, _, hT6, hT7, hT8, _⟩ :=
    H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hCtr, hFwd, hInv⟩ := H.start.fresh
  have hR11Of {a t : ℕ} (ht : tok.tag a = t) (hne : t ≠ 1) : a ≠ root + 11 := fun h => by
    have h1 := hT1 11 (by omega); rw [← h, ht] at h1; exact hne h1
  refine ⟨?_, fun e he => ?_, fun e he => ?_⟩
  · rw [branchBModel_keepMem_of_tag H hT6 (hR11Of hT6 (by decide)) (by decide) (by decide)
      (by decide) (by omega) (by decide) (by omega) (by omega) (fun _ _ => by omega)]
    exact hCtr
  · have ht := hT7 e he
    rw [branchBModel_keepMem_of_tag H ht (hR11Of ht (by decide)) (by decide) (by decide)
      (by decide) (by omega) (by decide) (by omega) (by omega) (fun _ _ => by omega)]
    exact hFwd e he
  · have ht := hT8 e he
    rw [branchBModel_keepMem_of_tag H ht (hR11Of ht (by decide)) (by decide) (by decide)
      (by decide) (by omega) (by decide) (by omega) (by omega) (fun _ _ => by omega)]
    exact hInv e he

theorem branchBModel_frameMem
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    ∀ a < heap,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      H.out.mem a = mem a := by
  intro a ha hNotFoot
  obtain ⟨hOwn, hT1, _, _, _, hT5, _⟩ := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ht0 : tok.tag a = 0 := by
    by_contra hne
    exact hNotFoot (Or.inl (hOwn a hne))
  have hR11 : a ≠ root + 11 := fun h => by
    have h1 := hT1 11 (by omega); rw [← h, ht0] at h1; omega
  have hOffRC : a < tok.levelsEnd + 2 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 2 * (cfg.P.d + 1) + cfg.P.d ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    have h5 := hT5 (2 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 2 * (cfg.P.d + 1)))) (by omega)
    rw [show tok.levelsEnd + (2 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 2 * (cfg.P.d + 1)))) = a by
      omega, ht0] at h5
    omega
  have hOffUC : a < tok.levelsEnd + 3 * (cfg.P.d + 1) ∨
      tok.levelsEnd + 3 * (cfg.P.d + 1) + cfg.P.d ≤ a := by
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    have h5 := hT5 (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) (by omega)
    rw [show tok.levelsEnd + (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) = a by
      omega, ht0] at h5
    omega
  refine branchBModel_keepMem H ha hR11 (fun _ => ?_) hOffRC hOffUC
  rw [ht0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by omega, by omega, fun _ _ => by omega⟩

theorem branchBModel_sched
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    SolverScheduleAt H.out.mem tok.levelsEnd
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)) := by
  set d := cfg.P.d
  set gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  set lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  set modelPre := alg2PreResetState cfg model U gVec lVec
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hMod : modelPre.chain = H.X := by
    dsimp only [modelPre, gVec, lVec]
    rw [← H.gVec_eq, ← H.lVec_eq]; exact H.modelEq.symm
  obtain ⟨_, _, _, _, _, _, _, _, hSched0, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, _, hT5, _⟩ := hTags0
  -- Helper for schedule cells outside `rcBase[0..d)` and `ucBase[0..d)`
  have hKeepSched : ∀ idx < 4 * (d + 1) + 1,
      (idx < 2 * (d + 1) ∨ 2 * (d + 1) + d ≤ idx) →
      (idx < 3 * (d + 1) ∨ 3 * (d + 1) + d ≤ idx) →
      H.out.mem (tok.levelsEnd + idx) = mem0 (tok.levelsEnd + idx) := by
    intro idx hidx hRC hUC
    have ht := hT5 idx hidx
    have haU : tok.levelsEnd + idx < uIntBuf :=
      H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
    have hR11 : tok.levelsEnd + idx ≠ root + 11 := fun h => by
      have h1 := hT1 11 (by omega); rw [← h, ht] at h1; omega
    have h1 := branchBModel_keepMem H (by omega) hR11 (fun _ => by
      rw [ht]
      exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by omega, by omega, fun _ _ => by omega⟩) (by omega) (by omega)
    rw [h1]
    exact H.start.memEq _ haU (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
  -- Helper for suffix frame on schedule cells (tag 5)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsEr4, _⟩ := H.loop
  have hh0Le : heap + 1 + 12 * d + 3 * (d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
  have hhS1Le : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
  have hsF0r4 : H.sF0.regs 4 = H.heap2 + (editsPtr - d - uIntBuf) := H.front.2.2.1
  have hsXr4 : H.sE.regs 4 ≤ H.sX.regs 4 := H.exitOut.heapLo
  have hSufSched : ∀ idx < 4 * (d + 1) + 1,
      H.out.mem (tok.levelsEnd + idx) = H.sX.mem (tok.levelsEnd + idx) := by
    intro idx hidx
    have ht := hT5 idx hidx
    have haU : tok.levelsEnd + idx < uIntBuf :=
      H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
    have hR11 : tok.levelsEnd + idx ≠ root + 11 := fun h => by
      have h1 := hT1 11 (by omega); rw [← h, ht] at h1; omega
    exact H.suf.2.2.2.2.2.2.2.2.2.1 _ (by omega) hR11 (fun _ => by
      rw [ht]; exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (fun hge => absurd haU (by omega))
  -- Model invariance for `shiftCount`, `updCount d`, and `rebuildCount d`
  have hInvUpd := algorithm1_update_shiftCount_updCount_d cfg.T cfg.L cfg.TP cfg.P cfg.N₀
    model.chain (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
    (fun e' => gVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
    (fun e' => lVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
  have hRebD : H.X.rebuildCount d = model.chain.rebuildCount d := by
    have hChE : H.chE.rebuildCount = model.chain.rebuildCount := by
      rw [H.loop.2.2.2.2.1.modelFrame.2.2.2.2.2.2.2, H.st0_eq]
    rcases H.exitCase with h1 | h2 | h3
    · obtain ⟨_, hiLt, _, _, _, hXeq, _⟩ := h1
      have hR := algorithm1_rebuild_lt cfg.T cfg.L cfg.P { H.chE with ℓ := H.ℓ', g := H.g' }
        hiLt H.curGE H.curEncE
      rw [hXeq, hR.2.2.2]
      dsimp only
      rw [ite_eq_right (by omega), hChE]
    · obtain ⟨_, hne, _, _, _, hXeq, _⟩ := h2
      rw [hXeq]; simp only [Chain.Ordered.updateLoop, hne, ↓reduceIte]; exact congrFun hChE d
    · obtain ⟨_, hemp, _, _, _, hXeq, _⟩ := h3
      rw [hXeq]; simp only [Chain.Ordered.updateLoop, hemp, ↓reduceIte]; exact congrFun hChE d
  refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · -- passes
    exact (hKeepSched i.val (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (hSched0.1 i)
  · -- shiftCount
    have h1 : tok.levelsEnd + (d + 1) + i = tok.levelsEnd + (d + 1 + i) := by omega
    rw [h1, hKeepSched (d + 1 + i) (by omega) (Or.inl (by omega)) (Or.inl (by omega)), ← h1]
    exact (hSched0.2.1 i hi).trans (congrFun hInvUpd.1 i).symm
  · -- rebuildCount
    by_cases hid : i < d
    · have h1 : tok.levelsEnd + 2 * (d + 1) + i = tok.levelsEnd + (2 * (d + 1) + i) := by omega
      rw [h1, hSufSched (2 * (d + 1) + i) (by omega), ← h1, hMod]
      have hC := (H.exitOut.cells i hid).2.2
      rw [H.A_eq] at hC
      exact hC
    · have hidEq : i = d := by omega
      subst hidEq
      have h1 : tok.levelsEnd + 2 * (d + 1) + d = tok.levelsEnd + (2 * (d + 1) + d) := by omega
      rw [h1, hKeepSched (2 * (d + 1) + d) (by omega) (Or.inr le_rfl) (Or.inl (by omega)), ← h1,
        hMod, hRebD]
      exact hSched0.2.2.1 d le_rfl
  · -- updCount
    by_cases hid : i < d
    · have h1 : tok.levelsEnd + 3 * (d + 1) + i = tok.levelsEnd + (3 * (d + 1) + i) := by omega
      rw [h1, hSufSched (3 * (d + 1) + i) (by omega), ← h1, hMod]
      have hC := (H.exitOut.cells i hid).2.1
      rw [H.A_eq] at hC
      exact hC
    · have hidEq : i = d := by omega
      subst hidEq
      have h1 : tok.levelsEnd + 3 * (d + 1) + d = tok.levelsEnd + (3 * (d + 1) + d) := by omega
      rw [h1, hKeepSched (3 * (d + 1) + d) (by omega) (Or.inr (by omega)) (Or.inr le_rfl), ← h1]
      exact (hSched0.2.2.2.1 d le_rfl).trans hInvUpd.2.symm
  · -- branD
    exact (hKeepSched (4 * (d + 1)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans
      hSched0.2.2.2.2

end KeepFields

end MinCostFlow.MinRatio
