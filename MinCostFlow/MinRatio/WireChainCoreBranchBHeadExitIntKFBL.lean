module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitCasesKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelKFBL
import MinCostFlow.MinRatio.WireChainCoreMetaDisjBranchB
import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import MinCostFlow.MinRatio.WireSelectEvalKeyMath
import MinCostFlow.MinRatio.WireStmtNoWriteIn
import MinCostFlow.Chain.Ordered.Lemma5_11
import WordRAM.Tactic

/-!
# The interior exit of the head of Branch B (`WireChainCoreBranchBHeadExitIntKFBL`)

Proves `BranchBHeadExitIntGoalKFBL`
(`WireChainCoreBranchBHeadExitCasesKFBL.lean`): from a run of Branch B up to the exit of the
plain-step loop (`BranchBRunPreExitKFBL`) that stops at an interior level `0 < H.i₀ < cfg.P.d`,
the interior exit produces the five exit fields of the head (`BranchBExitOutKFBL`,
`BranchBExitCaseKFBL`, the chain equality with `alg2PreResetState`, `BranchBExitForestLocKFBL`,
and `BranchBRebuiltOrdKFBL`).

* `preExit_regs71_80_81`: registers `71`, `80`, and `81` keep their dispatch values across the
  prefix, front, and plain-step loop (`runs_regs_of_noWriteIn`).
* `preExit_modelEq_int`: the rebuilt chain `X` at the interior exit equals
  `(alg2PreResetState cfg model U H.gVec H.lVec).chain`, via `branchBUpdateLoop_int` and the
  `updateLoop` equation in `H.loop`; also records `X.G 0 = H.G1`, `(X.G j).m ≤ m`, and level
  agreement below `H.i₀`.
* `preExit_oldLast`: recovers the old terminal forest graph at `H.sE.mem (oldPtrs + cfg.P.d)` by
  matching `H.pre.1` against `wireBranchBPrefixKFBL_runs` via `Runs.det` and propagating tag-19
  words and the stored pointer across the front and loop.
* `preExit_room_int`: bounds the remaining heap room at `H.sE.regs 4` for the interior exit.
* `branchBHeadExitIntGoalKFBL_proved`: assembles all five conjuncts from `BranchBIntExitLayGoalKFBL`,
  `BranchBExitOutKFBL.of_int_lay`, `BranchBIntExitForestLocGoalKFBL`, and
  `wireBranchBIntKFBL_exit_rebuiltOrd`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

private lemma wireBranchBLoopKFBL_noWrite_71_80_81
    (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    stmtNoWriteIn (fun r => r = 71 ∨ r = 80 ∨ r = 81)
      (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc) := by
  simp [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL, wireBranchBStepKFBL,
    wireBranchBStepHeadKFBL, wireBranchBStepTailKFBL, wireBranchBStepTailFrontKFBL,
    wireBranchBCopyListsStmt, wireBranchBReadDescStmt, wireBranchBNextLenStmt,
    wireBranchBSlotStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt, ordCoreReadLSFStmt,
    wireStretchDescCopyStmt, wireGuardCopyWordStmt, stmtNoWriteIn]

private lemma rebuildSuffix_lt_preExit (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ)
      {j : ℕ}, j < idx →
      let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec
        cFwd
      res.1 j = G j ∧ res.2.1 j = sc j ∧ res.2.2.1 j = bran j
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, j, hj => by
    dsimp only [Chain.Ordered.rebuildSuffix]
    have hne1 : j ≠ idx + 1 := by omega
    have hne0 : j ≠ idx := by omega
    refine (fun h => ⟨h.1.trans (ite_eq_right hne1), h.2.1.trans (ite_eq_right hne0),
      h.2.2.trans (ite_eq_right hne0)⟩)
      (rebuildSuffix_lt_preExit T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ (by omega))

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

/-- Registers `71`, `80`, and `81` retain their dispatch values at `H.sE`. -/
private theorem preExit_regs71_80_81
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 71 = 0 ∧ H.sE.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      H.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := by
  have hPreR := H.pre.2.2.1
  have hFrR := H.front.2.2.2.2
  have hLER := H.loop.2.2.2.2.2.2.2.2.2.1
  have hNW := runs_regs_of_noWriteIn H.loop.1 (wireBranchBLoopKFBL_noWrite_71_80_81 _ _ _ _ _ _)
  have hD := H.dispatch.2.2.1
  have hPres (r : ℕ) (hS : r = 71 ∨ r = 80 ∨ r = 81) : H.sE.regs r = H.st.regs r := by
    have h1 : H.sL.regs r = H.sE.regs r := hLER r (by omega) (by omega) (by omega) (by omega)
    have h2 : H.sL.regs r = H.sF0.regs r := hNW r hS
    have h3 : H.sF0.regs r = H.sP.regs r :=
      hFrR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    have h4 : H.sP.regs r = H.st.regs r := hPreR r (by omega)
    rw [← h1, h2, h3, h4]
  obtain ⟨_, _, h71, _, _, _, _, _, _, _, h80, h81, _⟩ := hD
  exact ⟨(hPres 71 (Or.inl rfl)).trans h71,
    (hPres 80 (Or.inr (Or.inl rfl))).trans h80,
    (hPres 81 (Or.inr (Or.inr rfl))).trans h81⟩

/-- At the interior exit (`0 < H.i₀ < d`), the rebuilt chain `X` equals the chain of
`alg2PreResetState`, its root graph is `H.G1`, every level graph has at most `m` edges, and
levels below `H.i₀` agree with `H.chE`. -/
private theorem preExit_modelEq_int
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hPos : 0 < H.i₀) (hLt : H.i₀ < cfg.P.d)
    {X : ChainState cfg.T cfg.P}
    (hX : X = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { H.chE with ℓ := H.ℓ', g := H.g' } H.i₀ H.curGE H.curEncE).1) :
    X = (alg2PreResetState cfg model U H.gVec H.lVec).chain ∧
    X.G 0 = H.G1 ∧
    (∀ j ≤ cfg.P.d, (X.G j).m ≤ m) ∧
    (∀ j < H.i₀, H.chE.G j = X.G j ∧ H.chE.scState j = X.scState j ∧ H.chE.bran j = X.bran j) := by
  have hFire := H.loop.2.2.2.2.2.2.1 hLt
  have hLoopEq := H.loop.2.2.2.2.2.2.2.1
  have hModelEq : X = (alg2PreResetState cfg model U H.gVec H.lVec).chain := by
    rw [hX]
    dsimp only [alg2PreResetState, Chain.Ordered.algorithm1_update]
    rw [← H.Uint_eq, ← H.g'_eq, ← H.ℓ'_eq, ← H.st0_eq, ← H.G1_eq, hLoopEq]
    exact (branchBUpdateLoop_int hLt hPos hFire).symm
  have hXG0 : X.G 0 = H.G1 := by
    rw [hModelEq, H.G1_eq, H.Uint_eq]
    dsimp only [alg2PreResetState]
    rw [(Chain.Ordered.update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _).1,
      ite_eq_right H.start.noFire]
  have hXGm : ∀ j ≤ cfg.P.d, (X.G j).m ≤ m := by
    intro j hj
    have hXEq : X = (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
      rw [hModelEq, H.gVec_eq, H.lVec_eq]
    have hFacts : ShiftLoopLevelFacts cfg X := hXEq ▸ H.start.modelInvKFBL.2.1
    have hLe0 : (X.G j).m ≤ (X.G 0).m := hFacts.2.2.2 j hj
    rw [hXG0, H.G1_eq, H.Uint_eq] at hLe0
    have hFresh0 : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hTr := translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt
      model.intToExt model.nextFresh hFresh0 H.start.refresh.1
    have hE1 : ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).E =
        (model.extG.applyBatch U).E.image
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 := by
      rw [← hTr.1]; exact hTr.2.1.hE
    have hCard : ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m ≤
        model.extG.m := by
      unfold MGraph.m
      rw [hE1, H.start.refresh.2.1]
      exact Finset.card_image_le
    exact (hLe0.trans hCard).trans H.start.extM.le
  have hLtEq : ∀ j < H.i₀,
      H.chE.G j = X.G j ∧ H.chE.scState j = X.scState j ∧ H.chE.bran j = X.bran j := by
    intro j hj
    rw [hX]
    simp only [Chain.Ordered.algorithm1_rebuild, dite_eq_left_of_eq_true (eq_true hLt)]
    have hR := rebuildSuffix_lt_preExit cfg.T cfg.L cfg.P H.chE.lvlM H.chE.N₀ H.ℓ' H.g'
      (cfg.P.d - H.i₀) H.i₀
      (fun r => if r = H.i₀ then H.curGE else H.chE.G r) H.chE.scState H.chE.bran H.chE.updCount
      H.chE.curEnc H.chE.curDecUpdates H.chE.curFwd hj
    have hne : j ≠ H.i₀ := by omega
    exact ⟨by rw [hR.1, ite_eq_right hne], hR.2.1.symm, hR.2.2.symm⟩
  exact ⟨hModelEq, hXG0, hXGm, hLtEq⟩

/-- At the end `H.sP` of the prefix, the cell `heap + 1 + 12 * d + d` holds the pointer to the
old terminal forest, recovered by determinism (`Runs.det`) against `wireBranchBPrefixKFBL_runs`. -/
private theorem preExit_sP_oldTermForest
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sP.mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) =
      mem0 (mem0 (tok.termHandle + 1 + model.chain.lastBran) + 1) := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hSpB := H.envA.ops.spaceTotalBranchB U.length
  have hRoomH := H.start.room
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, hT4, _, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, _⟩ := hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
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
  have hOldT := branchBOldTermForest_of_rep H.start.rep0 H.start.modelInv
  dsimp only at hOldT
  obtain ⟨hTermH0, hTermB0, hTagT1, hTagT2, _, _⟩ := hOldT
  set lsfHdr := mem0 (tok.termHandle + 1 + model.chain.lastBran)
  set forestPtr0 := mem0 (lsfHdr + 1)
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
    H.start.memEq _ hT1Lt (by rw [hTagT1]; decide) (by rw [hTagT1]; decide)
      (by rw [hTagT1]; decide)
  have hForestPtrMem : mem (lsfHdr + 1) = forestPtr0 :=
    H.start.memEq _ hT2Lt (by rw [hTagT2]; decide) (by rw [hTagT2]; decide)
      (by rw [hTagT2]; decide)
  have hRoomPre : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L + 1 + 3 * L + U.length * wireRefreshOneSpace L <
      2 ^ w := by
    omega
  have hR11 : root + 11 < uIntBuf := hLt (by rw [hT1 11 (by omega)]; decide)
  set addr := heap + 1 + 12 * cfg.P.d + cfg.P.d
  have hUAddr : uIntBuf ≤ addr := Nat.le_trans hUH (by omega)
  have hAddrLtH0 : addr < heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 := by omega
  have hAddrNeR11 : addr ≠ root + 11 := ne_of_gt (lt_of_lt_of_le hR11 hUAddr)
  have hAddrNotU : ¬ addr < uIntBuf := not_lt.mpr hUAddr
  have hAddrOff : addr < mem0 lm ∨ mem0 lm + eCap * L ≤ addr := by
    by_contra hc
    have h1 : mem0 lm ≤ addr ∧ addr < mem0 lm + eCap * L := by
      exact ⟨not_lt.mp (fun h => hc (Or.inl h)), not_le.mp (fun h => hc (Or.inr h))⟩
    have h2 : addr < uIntBuf := hLt (by rw [hTagL0 addr h1.1 h1.2]; omega)
    exact hAddrNotU h2
  have hAddrMiss : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
      addr ≠ tok.slots + ei ∧ addr ≠ tok.edgeThresholds + ei ∧ addr ≠ tok.edgeRecords + ei := by
    intro ei hei _
    refine ⟨ne_of_gt (lt_of_lt_of_le (hLt (by rw [hT9 ei hei]; decide)) hUAddr),
      ne_of_gt (lt_of_lt_of_le (hLt (by rw [hT12 ei hei]; decide)) hUAddr),
      ne_of_gt (lt_of_lt_of_le (hLt (by rw [hT13 ei hei]; decide)) hUAddr)⟩
  obtain ⟨r4, r70, r71, _, r73, r75, _, r77, r78, _, r80, _, _, r83, _, _, r87, r90, r91, _, _,
    r94, _, _⟩ := H.dispatch.2.2.1
  obtain ⟨sP', _, hS1', _, memS1', _, _, _, _, _, rP', _, _, h0S1', _, _, _, _, _, _, _, _,
    hFrS1', hFrP', _⟩ :=
    wireBranchBPrefixKFBL_runs (ec0 := eCap) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr0)
      H.envB.collectP H.envB.emitP H.envB.zeroP H.envA.refAccP H.envA.refOneP H.envA.updLen0P
      H.envA.four H.envA.lPos H.envA.pW H.envA.w18 H.envA.treeImpl H.envA.bindC H.envA.canonC
      H.envA.isNegC H.envA.shiftC H.envA.divC H.envA.addC H.envA.subC H.envA.negC H.envA.copyC
      H.start.rep0 H.start.meta0 H.start.num0 H.start.offInv0 H.start.offBd0 H.start.modelInv
      H.start.logW H.start.capT H.start.refresh H.start.memEq H.start.fresh H.start.trNf
      H.start.batch H.start.small H.start.footLt H.start.gLt H.start.lLt H.start.uLe H.start.edHeap
      hLevel0Meta H.start.zero H.dispatch.1
      ⟨r4, r70, r71, r73, r75, r77, r78, r80, r83, r87, r90, r91, r94⟩
      hTermHMem hTermBMem hLsfHdrMem hForestPtrMem (by omega) (by omega) (by omega) hRoomPre
  have hsPEq : H.sP = sP' := (Runs.det H.pre.1 rP').2.1
  rw [hsPEq]
  have hEq1 : sP'.mem addr = memS1' addr :=
    hFrP' addr (lt_of_lt_of_le hAddrLtH0 h0S1') hAddrMiss hAddrOff
  have hEq2 : memS1' addr = Function.update mem addr forestPtr0 addr :=
    hFrS1' addr hAddrLtH0 hAddrNeR11 (fun h => absurd h hAddrNotU)
  rw [hEq1, hEq2, Function.update_self]

/-- The old terminal forest at `H.sE.mem (oldPtrs + cfg.P.d)`, obtained from
`preExit_sP_oldTermForest` and memory preservation across the front and loop. -/
private theorem preExit_oldLast
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap) (fun _ => eCap)
      H.A.gPtr0 H.A.lPtr0 H.A.coreH) :
    let oldPtrs := heap + 1 + 12 * cfg.P.d
    let RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E
    ∃ vc ec, DynGraphAt H.sE.mem (H.sE.mem (oldPtrs + cfg.P.d)) vc ec
        (H.st0.lastLSFs H.st0.lastBran).F.F ∧
      ∀ a, H.sE.mem (oldPtrs + cfg.P.d) ≤ a →
        a < H.sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec →
        RL.foot (H.A.coreH cfg.P.d) tok.termTok a := by
  intro oldPtrs RL
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, _, hT5, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, hT21⟩ :=
    hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
  set lm := solverLevelMetaAddr tok.table cfg.P.d
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := H.start.modelInv
  have hCapEq (j : ℕ) (hj : j < cfg.P.d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (H.start.caps0 j hj)
  have hTagL0 : ∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d := by
    intro x h1 h2
    have hL := (hLev 0 hdPos).2.2.2.1
    rw [add_zero, (hCapEq 0 hdPos).2] at hL
    exact hL x h1 h2
  have hOldT := branchBOldTermForest_of_rep H.start.rep0 H.start.modelInv
  dsimp only at hOldT
  obtain ⟨_, _, _, _, hOldDG0, hOldFoot0⟩ := hOldT
  set forestPtr0 := mem0 (mem0 (tok.termHandle + 1 + model.chain.lastBran) + 1)
  have hsPOld : H.sP.mem (oldPtrs + cfg.P.d) = forestPtr0 := preExit_sP_oldTermForest H
  have hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
  have hhS1 : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
  have hsF0r4 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
  have hLoopFr := H.loop.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLMem : H.sL.mem = H.sE.mem := H.loop.2.2.2.2.2.2.2.2.1
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hsEOld : H.sE.mem (oldPtrs + cfg.P.d) = forestPtr0 := by
    rw [← hLMem]
    have h1 : H.sL.mem (oldPtrs + cfg.P.d) = H.sF0.mem (oldPtrs + cfg.P.d) := by
      refine hLoopFr (oldPtrs + cfg.P.d) (by omega) (fun j hj hf => ?_) (fun j hj => ?_)
        (fun j hj => ?_) (Or.inr (by rw [hSB]; exact Nat.le_add_right _ _))
      · have hCH : H.A.coreH j = tok.coreHandle j := by rw [H.A_eq]; simp [branchBAddrsOf, hj]
        rw [hCH] at hf
        have := H.start.footLt _ (Or.inr (Or.inr ⟨j, hj, hf⟩)); omega
      · have hg := hS.gLt j hj; have hl := hS.lLt j hj; rw [hSB] at hg hl
        exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
      · have hu := hS.ucLt; rw [hSB] at hu; omega
    rw [h1, H.front.2.2.2.1 _ (by omega), hsPOld]
  -- Every tag-19 word keeps its `mem0` value through the prefix, front, and loop
  have hTag19Keep : ∀ a, tok.tag a = 19 → H.sE.mem a = mem0 a := by
    intro a ha19
    have haU : a < uIntBuf := hLt (by rw [ha19]; decide)
    have hMem : mem a = mem0 a :=
      H.start.memEq a haU (by rw [ha19]; decide) (by rw [ha19]; decide) (by rw [ha19]; decide)
    have hFrS1 := H.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hFrP := H.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hS1a : H.memS1 a = mem a := by
      have h1 := hFrS1 a (by omega) (fun h => by
        have := hT1 11 (by omega); rw [← h, ha19] at this; exact absurd this (by decide))
        (fun _ => ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
      rw [h1, Function.update_of_ne (by omega)]
    have hsPa : H.sP.mem a = H.memS1 a := by
      have hOff : a < mem0 lm ∨ mem0 lm + H.ec0 * L ≤ a := by
        rw [H.ec0_eq]
        by_contra hc
        have := hTagL0 a (by omega) (by omega)
        omega
      exact hFrP a (by omega) (fun ei hei _ =>
        ⟨fun h => by have := hT9 ei hei; rw [← h, ha19] at this; omega,
         fun h => by have := hT12 ei hei; rw [← h, ha19] at this; omega,
         fun h => by have := hT13 ei hei; rw [← h, ha19] at this; omega⟩) hOff
    have hsFa : H.sF0.mem a = H.sP.mem a := H.front.2.2.2.1 a (by omega)
    have hsLa : H.sL.mem a = H.sF0.mem a := by
      refine hLoopFr a (by omega) (fun j hj hf => ?_) (fun j hj => ?_) (fun j hj => ?_)
        (Or.inl (by rw [hSB]; omega))
      · have hCH : H.A.coreH j = tok.coreHandle j := by rw [H.A_eq]; simp [branchBAddrsOf, hj]
        rw [hCH] at hf
        have := hT21 j hj a hf
        omega
      · constructor
        · by_contra hc
          have hg0 : H.A.gPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
            rw [H.A_eq]; rfl
          rw [hg0, not_or, not_lt, not_le] at hc
          have hCap := hCapEq j hj
          have ht := ((hLev j hj).2.2.2.2 a hc.1 (by rw [hCap.1, hCap.2]; exact hc.2)).1
          split_ifs at ht <;> omega
        · by_contra hc
          have hl0 : H.A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := by
            rw [H.A_eq]; rfl
          rw [hl0, not_or, not_lt, not_le] at hc
          have hCap := hCapEq j hj
          have ht := (hLev j hj).2.2.2.1 a hc.1 (by rw [hCap.2]; exact hc.2)
          omega
      · intro h
        have huc : H.A.ucBase = tok.levelsEnd + 3 * (cfg.P.d + 1) := by rw [H.A_eq]; rfl
        rw [huc] at h
        have ht := hT5 (3 * (cfg.P.d + 1) + j) (by omega)
        rw [show tok.levelsEnd + (3 * (cfg.P.d + 1) + j) =
          tok.levelsEnd + 3 * (cfg.P.d + 1) + j by omega, ← h] at ht
        omega
    rw [← hLMem, hsLa, hsFa, hsPa, hS1a, hMem]
  have hSt0Last : (H.st0.lastLSFs H.st0.lastBran).F.F =
      (model.chain.lastLSFs model.chain.lastBran).F.F := by
    rw [H.st0_eq]
  have hCHd : H.A.coreH cfg.P.d = tok.termHandle := by
    rw [H.A_eq]; simp [branchBAddrsOf]
  refine ⟨tok.vcLast, tok.ecLast, ?_, ?_⟩
  · rw [hsEOld, hSt0Last]
    exact dynGraphAt_of_agree hOldDG0 fun x hx1 hx2 => hTag19Keep x (hOldFoot0 x hx1 hx2).2.2
  · intro a ha1 ha2
    rw [hsEOld] at ha1 ha2
    have hF := hOldFoot0 a ha1 ha2
    rw [hCHd]
    exact ⟨hF.1, hF.2.1⟩

/-- Heap room at `H.sE.regs 4` for the interior exit (`0 < H.i₀ < cfg.P.d`). -/
private theorem preExit_room_int
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hPos : 0 < H.i₀) (hLt : H.i₀ < cfg.P.d)
    {X : ChainState cfg.T cfg.P}
    (hModelEq : X = (alg2PreResetState cfg model U H.gVec H.lVec).chain)
    (hChEq : H.chE.scState (H.i₀ - 1) = X.scState (H.i₀ - 1) ∧
      H.chE.bran (H.i₀ - 1) = X.bran (H.i₀ - 1)) :
    H.sE.regs 4 + 10 * (cfg.P.d - H.i₀) +
      (1 + ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1))) +
      (Finset.Ico H.i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w := by
  have hhS1 : H.hS1 ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 +
      (3 * U.length + U.length * wireTreeSyncEditSpace L) := by
    have := H.pre.2.2.2.2.1; omega
  have hheap2 : H.heap2 ≤ H.hS1 + 3 * L + U.length * wireRefreshOneSpace L :=
    H.pre.2.2.2.2.2.2.1
  have hsF0 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
  have hbW : editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 := by
    have hEdits := branchBLevel0Edits_of_rep H.start.rep0 H.start.caps0 H.start.modelInv
      H.start.refresh
    have hLe := smallBatchAt_words_le_edgeOnly H.start.small hEdits.2.2.1
    have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hLen : (translateBatch model.extG model.extToInt model.intToExt
        model.nextFresh U).2.2.2.2.length = U.length :=
      (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh hFresh H.start.refresh.1).2.2.2.2.1
    rw [hLen] at hLe; exact hLe
  have hsE : H.sE.regs 4 ≤ H.sF0.regs 4 +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) := by
    have hL := H.loop.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSub : Finset.Ico 0 H.i₀ ⊆ Finset.range cfg.P.d := fun j hj =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hLt.le)
    exact hL.trans (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hSub) _)
  have hXEq : X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [hModelEq, H.gVec_eq, H.lVec_eq]
  have hFactsX : ShiftLoopLevelFacts cfg X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hRotBd : ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 := by
    have hRotEq : ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) =
        ordRotWords (chainLevelOrdAbs X (H.i₀ - 1)) (X.bran (H.i₀ - 1)) := by
      unfold ordRotWords chainLevelOrdAbs; dsimp only; rw [hChEq.1, hChEq.2]
    rw [hRotEq]
    have h1 := (hXEq ▸ H.start.modelInvKFBL.2.2.2.2.1) (H.i₀ - 1) (by omega)
    have hNLe : (X.G H.i₀).n ≤ cfg.N₀ := by
      have hN := (hXEq ▸ H.start.modelInvKFBL.2.2.2.1) H.i₀ hLt.le
      rw [hFactsX.2.2.1] at hN; exact hN
    have hMLe : (X.G H.i₀).m ≤ levelM cfg.TP cfg.P 0 :=
      (hFactsX.2.2.2 H.i₀ hLt.le).trans
        ((hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) 0 (Nat.zero_le _))
    rw [show H.i₀ - 1 + 1 = H.i₀ by omega] at h1
    omega
  have hSumLe : (Finset.Ico H.i₀ cfg.P.d).sum levelSpace ≤
      (Finset.range cfg.P.d).sum levelSpace :=
    Finset.sum_le_sum_of_subset fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have hTot := H.envA.ops.spaceTotalBranchB U.length
  have hRoom := H.start.room
  omega

end Helpers

/-- **Proof of `BranchBHeadExitIntGoalKFBL`.** From a pre-exit run of Branch B that stops at an
interior level `0 < H.i₀ < cfg.P.d`, instantiates `BranchBIntExitLayGoalKFBL`,
`BranchBExitOutKFBL.of_int_lay`, `BranchBIntExitForestLocGoalKFBL`, and
`wireBranchBIntKFBL_exit_rebuiltOrd` to produce all five exit fields of the head. -/
theorem branchBHeadExitIntGoalKFBL_proved : BranchBHeadExitIntGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R hInt _ hIntF _ H hPos hLt
  set oldPtrs := heap + 1 + 12 * cfg.P.d
  set newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)
  set X := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
    { H.chE with ℓ := H.ℓ', g := H.g' } H.i₀ H.curGE H.curEncE).1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap) (fun _ => eCap)
      H.A.gPtr0 H.A.lPtr0 H.A.coreH := by
    rw [H.A_eq]
    exact (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0 H.start.caps0
      H.start.modelInv H.start.footLt hUH).1
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  have hLM : H.A.levelMeta = solverLevelMetaAddr tok.table cfg.P.d := by rw [H.A_eq]; rfl
  have hOldLo : H.A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs := by rw [hSB]
  have hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs := le_rfl
  have hNewHi : newPtrs + (cfg.P.d + 1) ≤ H.A.heapFloor := by
    have hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
    have hhS1 : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
    rw [hHF]; omega
  obtain ⟨h71, h80, h81⟩ := preExit_regs71_80_81 H
  obtain ⟨hModelEq, hXG0, hXGm, hLtEq⟩ := preExit_modelEq_int H hPos hLt (X := X) rfl
  have hXEq : X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [hModelEq, H.gVec_eq, H.lVec_eq]
  have hLvlM : ∀ j < cfg.P.d, H.st0.lvlM j = levelM cfg.TP cfg.P j := fun j _ => by
    have h1 : H.st0.lvlM = model.chain.lvlM := by rw [H.st0_eq]
    rw [h1, H.start.modelInvKFBL.1.2.1]
  have hN00 : H.st0.N₀ = cfg.N₀ := by
    have h1 : H.st0.N₀ = model.chain.N₀ := by rw [H.st0_eq]
    rw [h1, H.start.modelInv.2.1.1]
  have hIn0 : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (H.st0.lvlM j) H.st0.N₀ (H.st0.scState j) (H.st0.G j)
        (H.st0.levelOrd j) (H.st0.updCount j) := fun j _ hj => by
    have h1 := H.start.modelInv.2.2.2.2.2.2.2.1 j hj
    have hEq : H.st0.lvlM = model.chain.lvlM ∧ H.st0.N₀ = model.chain.N₀ ∧
        H.st0.scState = model.chain.scState ∧ H.st0.G = model.chain.G ∧
        H.st0.bran = model.chain.bran ∧ H.st0.updCount = model.chain.updCount := by
      rw [H.st0_eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [ChainState.levelOrd, chainLevelOrd, hEq.1, hEq.2.1, hEq.2.2.1, hEq.2.2.2.1,
      hEq.2.2.2.2.1, hEq.2.2.2.2.2]
    exact h1
  have hOldLast := preExit_oldLast H hS
  have hOldG0Cap : ∀ e ∈ (model.chain.G 0).E, e < tok.intCap := by
    intro e he
    have hWire0 := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact lt_of_lt_of_le (hWire0.2.1.2.2.1 e he) H.start.modelInv.2.1.2.2
  have hOldFCap : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (H.st0.scState j) (H.st0.bran j)).F.F.E, e < tok.intCap := by
    intro j _ hj e he
    have hEq : H.st0.scState = model.chain.scState ∧ H.st0.bran = model.chain.bran := by
      rw [H.st0_eq]; exact ⟨rfl, rfl⟩
    rw [hEq.1, hEq.2] at he
    exact hOldG0Cap e ((H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).1 he)
  have hOldLastFCap : ∀ e ∈ (H.st0.lastLSFs H.st0.lastBran).F.F.E, e < tok.intCap := by
    intro e he
    have hEq : H.st0.lastLSFs = model.chain.lastLSFs ∧ H.st0.lastBran = model.chain.lastBran := by
      rw [H.st0_eq]; exact ⟨rfl, rfl⟩
    rw [hEq.1, hEq.2] at he
    exact hOldG0Cap e (H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 he)
  have hFactsX : ShiftLoopLevelFacts cfg X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hNextN : ∀ j ≤ cfg.P.d, (X.G j).n ≤ X.N₀ := hXEq ▸ H.start.modelInvKFBL.2.2.2.1
  have hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs X j) (X.bran j) ≤
      1 + 2 * (X.G (j + 1)).n + 2 * (X.G (j + 1)).m :=
    hXEq ▸ H.start.modelInvKFBL.2.2.2.2.1
  have hImpl : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (X.G j) cfg.P.k (X.lvlM j)
          X.N₀ vCap eCap capExp Psc allocation) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (X.G j) cfg.P.k (X.lvlM j) X.N₀ vCap
        eCap capExp Psc allocation Rcore p opCore := by
    intro j _ hj
    have hci := H.envA.coreImpl j hj (X.G j) (hFactsX.1 j hj.le) (hXGm j hj.le)
    rw [← H.envB.depthEq] at hci
    rw [hFactsX.2.1, hFactsX.2.2.1]
    exact ⟨hci.1, hci.2⟩
  have hLastImpl : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
      (X.G cfg.P.d).E).Implements w p lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L (X.G cfg.P.d) vCap eCap lastMul
        stretchPrec lastAlloc) :=
    H.envA.lastImpl (X.G cfg.P.d) (hXGm cfg.P.d le_rfl)
      (hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.1) (hFactsX.1 cfg.P.d le_rfl)
      (hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hLevelSpaceDom : ∀ j gB lB grB oB h, H.i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (allocation 6 [gB, lB, grB, oB, cfg.P.k, X.lvlM j, X.N₀, L, fmt.precision, depth, h])
        (X.lvlM j) X.N₀ (X.G (j + 1)).m ≤ levelSpace j := fun j gB lB grB oB h _ hj => by
    have hDom := H.envA.ops.levelSpaceDom X j gB lB grB oB h hj hFactsX
      ((hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (j + 1) (by omega))
    rwa [← H.envB.depthEq] at hDom
  have hLevelCostDom : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc X j ≤ levelCost X j := fun j _ hj =>
    H.envA.ops.levelCostDom X j hj
  have hG0Cap : ∀ e ∈ (X.G 0).E, e < tok.intCap := by
    intro e he
    rw [hXG0, H.G1_eq, H.Uint_eq] at he
    exact (H.start.modelInv.2.2.2.2.2.2.2.2.2.2.1 e he).2
  have hFCap : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (X.scState j) (X.bran j)).F.F.E, e < tok.intCap := fun j _ hj e he =>
    hG0Cap e ((hXEq ▸ H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).2 he)
  have hLastFCap : ∀ e ∈ (X.lastLSFs X.lastBran).F.F.E, e < tok.intCap := fun e he =>
    hG0Cap e ((hXEq ▸ H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) he)
  have hRoom := preExit_room_int H hPos hLt hModelEq
    ⟨(hLtEq (H.i₀ - 1) (by omega)).2.1, (hLtEq (H.i₀ - 1) (by omega)).2.2⟩
  have hInv := H.loop.2.2.2.2.1
  have hM := H.loop.2.2.2.2.2.1
  have hFire := H.loop.2.2.2.2.2.2.1 hLt
  have hstMem := H.loop.2.2.2.2.2.2.2.2.1
  have hstRegs := H.loop.2.2.2.2.2.2.2.2.2.1
  obtain ⟨sX, cX, termTokN, tokN, hRun, hHeapOut, hIntOut, hCost, hT, hLay⟩ :=
    hInt (ω := ω) (st := H.sL) (opLast := opLast) (lastAlloc := lastAlloc) (lastMul := lastMul)
      (lastSpace := lastSpace) (levelSpace := levelSpace) (levelCost := levelCost X)
      H.envB.loop hS hOldLo hOldNew hNewHi rfl hLvlM hN00 hPos hLt hInv hM hFire hstMem hstRegs
      h71 h80 h81 hIn0 hOldLast hOldFCap hOldLastFCap X rfl H.envA.wordExpEq H.envA.initOrdEq
      hNextN hNextRot hImpl H.envA.capLim H.envA.coreLenP hLastImpl hLevelSpaceDom hLevelCostDom
      H.envA.ops.lastSpaceDom hFCap hLastFCap H.envA.lW H.envA.pW H.envA.width
      (H.envB.depthEq ▸ H.envA.depthW) H.envA.nW hRoom
  have hLoc :=
    hIntF (ω := ω) (st := H.sL) (opLast := opLast) (lastAlloc := lastAlloc) (lastMul := lastMul)
      (lastSpace := lastSpace) (levelSpace := levelSpace) (levelCost := levelCost X)
      H.envB.loop hS hOldLo hOldNew hNewHi rfl hLvlM hN00 hPos hLt hInv hM hFire hstMem hstRegs
      h71 h80 h81 hIn0 hOldLast hOldFCap hOldLastFCap X rfl H.envA.wordExpEq H.envA.initOrdEq
      hNextN hNextRot hImpl H.envA.capLim H.envA.coreLenP hLastImpl hLevelSpaceDom hLevelCostDom
      H.envA.ops.lastSpaceDom hFCap hLastFCap H.envA.lW H.envA.pW H.envA.width
      (H.envB.depthEq ▸ H.envA.depthW) H.envA.nW hRoom sX cX hRun
  have hOrd :=
    (wireBranchBIntKFBL_exit_rebuiltOrd (ω := ω) (st := H.sL) (opLast := opLast)
      (lastAlloc := lastAlloc) (lastMul := lastMul) (lastSpace := lastSpace)
      (levelSpace := levelSpace) (levelCost := levelCost X)
      H.envB.loop hS hOldLo hOldNew hNewHi rfl hLvlM hN00 hPos hLt hInv hM hFire hstMem hstRegs
      h71 h80 h81 hIn0 X rfl H.envA.wordExpEq H.envA.initOrdEq
      hNextN hNextRot hImpl H.envA.capLim H.envA.coreLenP hLastImpl hLevelSpaceDom hLevelCostDom
      H.envA.ops.lastSpaceDom hFCap hLastFCap H.envA.lW H.envA.pW H.envA.width
      (H.envB.depthEq ▸ H.envA.depthW) H.envA.nW hRoom hRun).2
  rw [hLM, hSB] at hOrd
  refine ⟨sX, cX, H.i₀, vCap, eCap, termTokN, hT, tokN, X,
    BranchBExitOutKFBL.of_int_lay hLt hIntOut hLay,
    Or.inl ⟨hPos, hLt, rfl, rfl, rfl, rfl, hRun, hHeapOut, hCost⟩,
    hModelEq, ?_, hOrd⟩
  simp only [ite_eq_left hLt.le]
  exact hLoc

end MinCostFlow.MinRatio

end
