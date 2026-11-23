module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProofLastTerm
import MinCostFlow.MinRatio.WireChainCoreBranchBIntExitKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL

/-!
# Proof of `BranchBSpaceGoalKFBL` (`WireChainCoreBranchBSpaceProof`)

Proves `BranchBSpaceGoalKFBL` (`WireChainCoreBranchBSpaceGoalKFBL.lean`):
for every `H : BranchBRunKFBL …`, all ten fields of `BranchBSpaceFieldsKFBL` hold.

* `branchBSpace_lastHandle_int`: in the interior exit (`0 < H.i₀ < cfg.P.d`), runs
  `wireBranchBIntOldKFBL_runs`, `wireBranchBIntRebNewKFBL_runs`, and
  `wireBranchBIntTailKFBL_runs`, matches the composed run against `H.exitCase` via `Runs.det`,
  and concludes `H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)`.
* `branchBSpace_lastHandle`: combines the interior, non-empty terminal, and empty terminal cases.
* `branchBSpaceGoalKFBL_proved`: proves `BranchBSpaceGoalKFBL` by combining
  `branchBSpaceFields_of_lastHandle` and `branchBSpace_lastHandle`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section InteriorAndGoal

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

set_option maxHeartbeats 3200000 in
/-- Interior exit (`0 < H.i₀ < cfg.P.d`): the new terminal handle lies at or above
`H.sE.regs 4`. -/
theorem branchBSpace_lastHandle_int
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hiPos : 0 < H.i₀) (hiLt : H.i₀ < cfg.P.d) (hfr : H.fr = H.i₀)
    (hNext : H.X = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { H.chE with ℓ := H.ℓ', g := H.g' } H.i₀ H.curGE H.curEncE).1)
    (hRun : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) H.sL .normal H.sX H.cX) :
    H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d) := by
  have hHeaps := branchBSpace_heaps H
  have hS0 := (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0
    H.start.caps0 H.start.modelInv H.start.footLt hHeaps.1).1
  have hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap) (fun _ => eCap)
      H.A.gPtr0 H.A.lPtr0 H.A.coreH := by
    rw [H.A_eq]; exact hS0
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  set oldPtrs := heap + 1 + 12 * cfg.P.d
  set newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)
  have hOldLo : H.A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs := by rw [hSB]
  have hNewLo : H.A.selBase + 1 + 12 * cfg.P.d ≤ newPtrs := by rw [hSB]; omega
  have hOldHi : oldPtrs + (cfg.P.d + 1) ≤ H.A.heapFloor := by
    have hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
    have hhS1 : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
    rw [hHF]; omega
  have hNewHi : newPtrs + (cfg.P.d + 1) ≤ H.A.heapFloor := by
    have hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
    have hhS1 : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
    rw [hHF]; omega
  obtain ⟨h71, h80, h81⟩ := branchB_loop_regs71_80_81 H
  have hInv := H.loop.2.2.2.2.1
  have hM := H.loop.2.2.2.2.2.1
  have hFire := H.loop.2.2.2.2.2.2.1 hiLt
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
  -- Extract rebuild facts from `hM`
  obtain ⟨rem, hrem⟩ : ∃ rem, cfg.P.d - H.i₀ = rem + 1 := ⟨cfg.P.d - H.i₀ - 1, by omega⟩
  rw [hrem] at hM
  obtain ⟨_, hValid, hCaps, hCurG, _, hIf⟩ := hM
  have hFire' : intRebuildThreshold cfg.P H.chE.N₀ H.i₀ < H.chE.updCount H.i₀ + H.curUE.length := by
    rw [hInv.modelFrame.2.2.2.2.2.1]; exact hFire
  simp only [hFire', ↓reduceIte] at hIf
  obtain ⟨hReb, hInPrev0⟩ := hIf
  have hi0ne : H.i₀ ≠ 0 := by omega
  rw [rebuildStartGraph_pos hi0ne, rebuildStartFn_pos hi0ne, rebuildStartFn_pos hi0ne] at hReb
  have hInPrev := hInPrev0 hiPos
  have hRebW : H.chE.rebuildCount H.i₀ + 1 < 2 ^ w := hReb.1
  -- Bounds on `H.X = modelPre.chain`
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hFactsX : ShiftLoopLevelFacts cfg H.X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hNextN : ∀ j ≤ cfg.P.d, (H.X.G j).n ≤ H.X.N₀ := hXEq ▸ H.start.modelInvKFBL.2.2.2.1
  have hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs H.X j) (H.X.bran j) ≤
      1 + 2 * (H.X.G (j + 1)).n + 2 * (H.X.G (j + 1)).m :=
    hXEq ▸ H.start.modelInvKFBL.2.2.2.2.1
  have hImpl : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (H.X.G j) cfg.P.k (H.X.lvlM j)
          H.X.N₀ vCap eCap capExp Psc allocation) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (H.X.G j) cfg.P.k (H.X.lvlM j) H.X.N₀ vCap
        eCap capExp Psc allocation Rcore p opCore := by
    intro j _ hj
    have hci := H.envA.coreImpl j hj (H.X.G j) (hFactsX.1 j hj.le) (branchB_XG_m_le H hj.le)
    rw [← H.envB.depthEq] at hci
    rw [hFactsX.2.1, hFactsX.2.2.1]
    exact ⟨hci.1, hci.2⟩
  have hLastImpl : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
      (H.X.G cfg.P.d).E).Implements w p lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L (H.X.G cfg.P.d) vCap eCap lastMul
        stretchPrec lastAlloc) :=
    H.envA.lastImpl (H.X.G cfg.P.d) (branchB_XG_m_le H le_rfl)
      (hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.1) (hFactsX.1 cfg.P.d le_rfl)
      (hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hLevelSpaceDom : ∀ j gB lB grB oB h, H.i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (allocation 6 [gB, lB, grB, oB, cfg.P.k, H.X.lvlM j, H.X.N₀, L, fmt.precision, depth, h])
        (H.X.lvlM j) H.X.N₀ (H.X.G (j + 1)).m ≤ levelSpace j := fun j gB lB grB oB h _ hj => by
    have hDom := H.envA.ops.levelSpaceDom H.X j gB lB grB oB h hj hFactsX
      ((hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (j + 1) (by omega))
    rwa [← H.envB.depthEq] at hDom
  have hLevelCostDom : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc H.X j ≤ levelCost H.X j := fun j _ hj =>
    H.envA.ops.levelCostDom H.X j hj
  have hG0Cap : ∀ e ∈ (H.X.G 0).E, e < tok.intCap := by
    intro e he
    rw [branchB_XG0_eq H, H.G1_eq, H.Uint_eq] at he
    exact (H.start.modelInv.2.2.2.2.2.2.2.2.2.2.1 e he).2
  have hFCap : ∀ j, H.i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (H.X.scState j) (H.X.bran j)).F.F.E, e < tok.intCap := fun j _ hj e he =>
    hG0Cap e ((hXEq ▸ H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).2 he)
  have hLastFCap : ∀ e ∈ (H.X.lastLSFs H.X.lastBran).F.F.E, e < tok.intCap := fun e he => by
    have hInTree : e ∈ H.X.toTreeChain.chainTree.E := by
      simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion,
        Finset.mem_range]
      exact ⟨cfg.P.d, show cfg.P.d < cfg.P.d + 1 by omega,
        by simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he⟩
    exact hG0Cap e ((hXEq ▸ H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hInTree)
  -- Room bound for the interior exit
  have hRotBd : ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 := by
    have hChEq := branchB_chain_lt_eq H (j := H.i₀ - 1) (by omega)
    have hRotEq : ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) =
        ordRotWords (chainLevelOrdAbs H.X (H.i₀ - 1)) (H.X.bran (H.i₀ - 1)) := by
      unfold ordRotWords chainLevelOrdAbs; dsimp only; rw [hChEq.2.1, hChEq.2.2]
    rw [hRotEq]
    have h1 := hNextRot (H.i₀ - 1) (by omega)
    have hNLe : (H.X.G H.i₀).n ≤ cfg.N₀ := by
      have hN := hNextN H.i₀ hiLt.le; rw [hFactsX.2.2.1] at hN; exact hN
    have hMLe : (H.X.G H.i₀).m ≤ levelM cfg.TP cfg.P 0 :=
      (hFactsX.2.2.2 H.i₀ hiLt.le).trans
        ((hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) 0 (Nat.zero_le _))
    rw [show H.i₀ - 1 + 1 = H.i₀ by omega] at h1
    omega
  have hRoomAll : H.sE.regs 4 + 10 * (cfg.P.d - H.i₀) +
      (1 + ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1))) +
      (Finset.Ico H.i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w := by
    have hPFL := branchB_prefixFrontLoop_room H
    have hSumLe : (Finset.Ico H.i₀ cfg.P.d).sum levelSpace ≤
        (Finset.range cfg.P.d).sum levelSpace :=
      Finset.sum_le_sum_of_subset fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
    omega
  -- Part 1: `wireBranchBIntOldKFBL_runs`
  obtain ⟨s, c1, tokM, ordPtr, ordWords, r1, h1hi, M, _⟩ :=
    wireBranchBIntOldKFBL_runs (ω := ω) (st := H.sL) H.envB.loop hS hOldLo hOldHi rfl hLvlM hN00
      hiPos hiLt hInv H.loop.2.2.2.2.2.2.2.2.1 H.loop.2.2.2.2.2.2.2.2.2.1 h71 h80 hIn0 hValid
      hCaps hCurG hRebW hInPrev (by omega)
  -- Part 2: `wireBranchBIntRebNewKFBL_runs`
  obtain ⟨s3, c2, termTokN', coreTok, r2, h3hi, B, _⟩ :=
    wireBranchBIntRebNewKFBL_runs (ω := ω) (lastAlloc := lastAlloc) (opLast := opLast)
      (lastMul := lastMul) (lastSpace := lastSpace) (levelSpace := levelSpace)
      (levelCost := levelCost H.X) H.envB.loop hS hOldLo hOldHi hNewLo hNewHi hiPos hiLt hInv M
      h71 h81 H.X hNext hReb H.envA.wordExpEq H.envA.initOrdEq hNextN hNextRot hImpl H.envA.capLim
      H.envA.coreLenP hLastImpl hLevelSpaceDom hLevelCostDom H.envA.ops.lastSpaceDom hFCap
      hLastFCap H.envA.lW H.envA.pW H.envA.width (H.envB.depthEq ▸ H.envA.depthW) H.envA.nW
      (by omega)
  -- Part 3: `wireBranchBIntTailKFBL_runs` (keeps `A.handleBase + d`)
  obtain ⟨hFloor, _, _, _, _, hr72, _, _, hr75, _, hr77, hr78, _, hr83, hr85, _, _, _, hr96,
    _, _, _⟩ := hInv.regs
  have hm1 : H.i₀ - 1 < cfg.P.d := by omega
  have hsE4 : H.sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hs3 : s.regs 4 ≤ s3.regs 4 := B.heapLo
  have hHBLt := hS.hbLt
  have hBBLt := hS.bbLt
  have hMetaLt := hS.metaLt
  have hUCLt := hS.ucLt
  have hGLt1 : H.A.gPtr0 (H.i₀ - 1) + dynGraphSize vCap eCap ≤ H.A.selBase := hS.gLt (H.i₀ - 1) hm1
  have hSlotLe : H.A.selBase + 1 + 12 * cfg.P.d ≤ H.A.heapFloor := by
    rw [hSB, hHF]; exact hHeaps.2.1
  have hR3 (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s3.regs r = H.sE.regs r :=
    (B.regs r h70).trans (M.regs r h70 h99)
  have hTokM1 : ∀ a, Rcore.foot (H.A.coreH (H.i₀ - 1)) (tokM (H.i₀ - 1)) a →
      Rcore.foot (H.A.coreH (H.i₀ - 1)) (H.tokE (H.i₀ - 1)) a ∨
        (H.sE.regs 4 ≤ a ∧ a < s.regs 4) :=
    (M.reps (H.i₀ - 1) hm1).2
  have hKeep3 : ∀ a < H.sE.regs 4,
      (∀ j, H.i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (H.A.coreH j) (H.tokE j) a) →
      (a < H.A.gPtr0 H.i₀ ∨ H.A.gPtr0 H.i₀ + dynGraphSize vCap eCap ≤ a) →
      BranchBIntKeepCell cfg.P.d H.i₀ H.A a →
      (a < oldPtrs + H.i₀ ∨ oldPtrs + cfg.P.d ≤ a) →
      (a < newPtrs + H.i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) → s3.mem a = H.sE.mem a :=
    fun a ha hc hg hk ho hn =>
      (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 hn).trans (M.frame a ha hc hg hk.1 ho)
  have hK3S : ∀ x, BranchBStaticWord cfg.P.d H.A x → BranchBIntKeepCell cfg.P.d H.i₀ H.A x →
      s3.mem x = H.sE.mem x := fun x hx hk => by
    obtain ⟨hxs, hxf, hxg, _⟩ := branchBStaticWord_off hS hInv.static hx
    exact hKeep3 x (by omega) (fun j _ hj => hxf j hj) (hxg H.i₀ hiLt).1 hk
      (Or.inl (by omega)) (Or.inl (by omega))
  have h3HB1 : s3.mem (H.A.handleBase + (H.i₀ - 1)) = H.sE.mem (H.A.handleBase + (H.i₀ - 1)) :=
    hK3S _ (.hb (by omega) (by omega)) (.hb hS (by omega) hiLt)
  have h3BB1 : s3.mem (H.A.branchBase + (H.i₀ - 1)) = H.sE.mem (H.A.branchBase + (H.i₀ - 1)) :=
    hK3S _ (.bb (by omega) (by omega)) (.bb hS (by omega) hiLt)
  have h3LMd1 : s3.mem (H.A.levelMeta + cfg.P.d + (H.i₀ - 1)) =
      H.sE.mem (H.A.levelMeta + cfg.P.d + (H.i₀ - 1)) :=
    hK3S _ (.lm (by omega) (by omega)) (.lmd hS (by omega) hiLt)
  have hLoc1 := H.envB.loop.loc (H.A.coreH (H.i₀ - 1)) (chainLevelOrdAbs H.chE (H.i₀ - 1))
    (tokM (H.i₀ - 1)) s.mem s3.mem (fun a ha => by
      rcases hTokM1 a ha with h0 | ⟨_, h2⟩
      · have hlt := (hInv.reps (H.i₀ - 1) hm1).2 a h0
        obtain ⟨f1, f2, f3, _, f5, _⟩ := branchBCoresDisjStatic_footSep hInv.static hm1 h0
        have hk : BranchBIntKeepCell cfg.P.d H.i₀ H.A a := .of_sep f1 f2 f3 f5 hiLt
        refine (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 ?_).symm
        rcases hInv.footLoc (H.i₀ - 1) hm1 a h0 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · exact (B.frame a h2 (Or.inr (by omega)) (Or.inr (by omega))
          ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega))).symm)
  have hRep1 : Rcore.rep (H.A.coreH (H.i₀ - 1)) (chainLevelOrdAbs H.chE (H.i₀ - 1))
      (tokM (H.i₀ - 1)) s3.mem := by
    have h := (M.reps (H.i₀ - 1) hm1).1
    simp only [show ¬ H.i₀ ≤ H.i₀ - 1 by omega, ↓reduceIte] at h
    exact hLoc1.1 h
  obtain ⟨_, _, c3t, c4t, c5t, c6t, c7t, _, _, _⟩ := hInv.cells (H.i₀ - 1) hm1
  have hG1 : DynGraphAt s3.mem (H.A.gPtr0 (H.i₀ - 1)) vCap eCap (H.chE.G (H.i₀ - 1)) :=
    dynGraphAt_of_agree (hInv.graphs (H.i₀ - 1) hm1) (fun x hx1 hx2 => by
      obtain ⟨_, _, g3, g4, _, g6, g7, _, g9⟩ := hS.gSep (H.i₀ - 1) hm1 x hx1 hx2
      exact hKeep3 x (by omega)
        (fun j _ hj => (hInv.static j hj).2.2.2.2.1 (H.i₀ - 1) hm1 x hx1 hx2)
        ((g9 H.i₀ hiLt).2 (by omega)) (.of_sep g3 g4 g6 (g7.imp_right Nat.le_of_lt) hiLt)
        (Or.inl (by omega)) (Or.inl (by omega)))
  have hInT : SparseCoreOrdInput cfg.T cfg.P.k (levelM cfg.TP cfg.P (H.i₀ - 1)) cfg.N₀
      (H.chE.scState (H.i₀ - 1)) (H.chE.G (H.i₀ - 1)) (H.chE.levelOrd (H.i₀ - 1))
      (H.chE.updCount (H.i₀ - 1)) := by
    have hLvlCh : H.chE.lvlM (H.i₀ - 1) = levelM cfg.TP cfg.P (H.i₀ - 1) := by
      rw [hInv.modelFrame.2.2.2.2.2.2.1]; exact hLvlM (H.i₀ - 1) hm1
    rw [← hLvlCh, ← hInv.modelFrame.2.2.2.2.2.1]; exact hInPrev
  obtain ⟨out, c3, _, _, r3, _, _, _, _, _, _, _, _, _, _, hFrT, _, _, _, _, _, _⟩ :=
    wireBranchBIntTailKFBL_runs (tool := cfg.T) (ω := ω) (st := s3) (d := cfg.P.d) (idx := H.i₀)
      (selBase := H.A.selBase) (ucBase := H.A.ucBase) (cur := s3.regs 4)
      (handleBase := H.A.handleBase) (branchBase := H.A.branchBase) (levelMeta := H.A.levelMeta)
      (handle := H.A.coreH (H.i₀ - 1)) (branch := H.chE.bran (H.i₀ - 1))
      (graph := H.A.gPtr0 (H.i₀ - 1))
      (a := ⟨H.chE.scState (H.i₀ - 1), H.chE.G (H.i₀ - 1), H.chE.levelOrd (H.i₀ - 1),
        H.chE.updCount (H.i₀ - 1)⟩)
      (x := tokM (H.i₀ - 1)) H.envB.loop.loc (H.envB.loop.footAt (H.i₀ - 1) hm1)
      ⟨rfl, (hR3 72 (by omega) (by omega)).trans hr72,
        (hR3 75 (by omega) (by omega)).trans hr75, (hR3 77 (by omega) (by omega)).trans hr77,
        (hR3 78 (by omega) (by omega)).trans hr78, (hR3 83 (by omega) (by omega)).trans hr83,
        (hR3 85 (by omega) (by omega)).trans hr85, (hR3 96 (by omega) (by omega)).trans hr96⟩
      hiLt.le (by omega)
      ⟨h3HB1.trans c3t, h3BB1.trans c4t, h3LMd1.trans c7t⟩
      ⟨by omega, by omega, by omega⟩ c5t H.envB.loop.kW c6t hG1 (by omega) hRep1 hInT
      (fun z hz => by
        rcases hTokM1 z hz with h | h
        · have := (hInv.reps (H.i₀ - 1) hm1).2 z h; omega
        · omega)
      B.zero (by omega) (by omega)
      ⟨fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hInv.footLoc (H.i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega,
       fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hInv.footLoc (H.i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega⟩
      (fun z hz => by
        rcases hz with ⟨hz1, hz2⟩ | hz
        · obtain ⟨n1, n2, n3⟩ := branchBStatic_uc_ne hS (z := z) (by omega) hz2 hm1
          refine ⟨by omega, fun hf => ?_, ?_, n1, n2, n3, by omega, by omega⟩
          · rcases hTokM1 z hf with h | h
            · obtain ⟨_, _, _, f4, _, _⟩ := branchBCoresDisjStatic_footSep hInv.static hm1 h
              rcases f4 with f4 | f4 <;> omega
            · omega
          · by_contra hc
            simp only [not_or, not_lt, not_le] at hc
            obtain ⟨_, _, _, _, _, _, _, g8, _⟩ := hS.gSep (H.i₀ - 1) hm1 z hc.1 hc.2
            rcases g8 with g8 | g8 <;> omega
        · subst hz
          refine ⟨by omega, fun hf => ?_, Or.inr (by omega), by omega, by omega, by omega,
            by omega, by omega⟩
          rcases hTokM1 _ hf with h | h
          · rcases hInv.footLoc (H.i₀ - 1) hm1 _ h with h' | h' <;> omega
          · omega)
      (Or.inr (by omega))
  -- Compose the three parts and identify `out` with `H.sX` via `Runs.det`
  have rAll : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) H.sL .normal out (c1 + (c2 + c3 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s, c1, c2 + c3 + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s3, c2, c3, r2, r3, rfl⟩), rfl⟩)
  have houtEq : H.sX = out := (Runs.det hRun rAll).2.1
  rw [houtEq]
  have hKeepD : out.mem (H.A.handleBase + cfg.P.d) = s3.mem (H.A.handleBase + cfg.P.d) := by
    refine hFrT (H.A.handleBase + cfg.P.d) (by omega) ?_ ?_ (by omega) (by omega) (by omega)
    · intro hf
      rcases hTokM1 _ hf with h | h
      · obtain ⟨f1, _, _, _, _, _⟩ := branchBCoresDisjStatic_footSep hInv.static hm1 h
        rcases f1 with f1 | f1 <;> omega
      · omega
    · have hSep := hS.sepUCHB
      rcases hSep with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
  rw [hKeepD]
  exact le_trans hsE4.le B.lastH

/-- Terminal-handle location after all three exits of Branch B: when the last level is rebuilt
(`H.fr ≤ cfg.P.d`), its handle lies at or above `H.sE.regs 4`; when the last level is kept
(`H.fr = cfg.P.d + 1`), its handle stays at `H.A.coreH cfg.P.d`. -/
theorem branchBSpace_lastHandle
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    (H.fr ≤ cfg.P.d → H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)) ∧
      (H.fr = cfg.P.d + 1 → H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d) := by
  rcases H.exitCase with hInt | hTerm | hEmpty
  · obtain ⟨hiPos, hiLt, hfr, _, _, hNext, hRun, _, _⟩ := hInt
    exact ⟨fun _ => branchBSpace_lastHandle_int H hiPos hiLt hfr hNext hRun,
      fun h => by omega⟩
  · obtain ⟨hi₀, hneU, hfr, _, _, hX, _, hRun, _, _⟩ := hTerm
    exact ⟨fun _ => branchBSpace_lastHandle_term H hi₀ hneU hX hRun,
      fun h => by omega⟩
  · obtain ⟨hi₀, hEmp, hfr, _, _, _, _, _, _, hRun, _, _, _⟩ := hEmpty
    exact ⟨fun h => by omega,
      fun _ => branchBSpace_lastHandle_empty H hi₀ hEmp hRun⟩

/-- **Proof of `BranchBSpaceGoalKFBL`.** For every run of Branch B with its parts
(`BranchBRunKFBL`), all ten space and placement fields of `BranchBSpaceFieldsKFBL` hold at the
final state. -/
theorem branchBSpaceGoalKFBL_proved : BranchBSpaceGoalKFBL :=
  fun H => branchBSpaceFields_of_lastHandle H (branchBSpace_lastHandle H)

end InteriorAndGoal

end MinCostFlow.MinRatio
