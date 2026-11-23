module

public import MinCostFlow.MinRatio.WireShiftDeepAux
import MinCostFlow.MinRatio.WireShiftTerm
import WordRAM.Tactic

/-!
# Deep-shift chain synchronization (`ShiftDeepChainSyncSpecWExtKFBL`)

Proves `shiftDeepChainBody_meets_spec`, establishing `ShiftDeepChainSyncSpecWExtKFBL` for
`shiftDeepChainBodyKFBL` under the layout contract `sparseCoreOrdMachineContractKFBL`
(Algorithm 2 non-terminal shift `i < d`, pages 20 and 29):
1. Runs Phases 0–4a via `shiftDeep_phases_0_to_4a_runs` (`WireShiftDeepAux.lean`).
2. Packs the symmetric difference of old and new suffix forests `[i, d]` via
   `wireSuffixPackEdits_runs` (`WireSuffixEdits.lean`), lifting it to `oldF.E` vs `newF.E` via
   `treeEditDiff_chainSuffix` and matching `model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates`
   via `shiftDeep_totalTreeUpdates_sub`.
3. Synchronizes the path tree and off-tree records via `shiftTermSetupLoop_runs` and
   `wireTreeSyncLoop_runs`.
4. Reconstructs `tok'`, proving `solverStateRep.rep`, `SolverLevelMetaAt`, `SolverLevelCapsAt`
   (through `SolverLevelMetaCapsAt`), `PathTreeNumericInv`,
   `OffTreeRecInv`, `OffTreeRecBound`, frame, footprint, and exact amortized cost bound.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program IPM.Machine Bundle

set_option maxHeartbeats 800000 in
/-- `shiftDeepChainBodyKFBL` satisfies `ShiftDeepChainSyncSpecWExtKFBL` under
`sparseCoreOrdMachineContractKFBL`, maintaining `solverStateRep.rep`, `SolverLevelMetaAt` and
`SolverLevelCapsAt`,
with exact per-tree-update cost `wireTreeSyncEditCost L drainUnit + 2` and tool cost dominated by
`deepFixed + toolMul * Δ totalRuntime`. -/
theorem shiftDeepChainBody_meets_spec
    {w L P m V psi k epsExp drainUnit capExp limbMul wordExp stretchPrec lastMul
      intCapMax forestEdgeCap deepSpace deepFixed toolMul vCap eCap capLimit fcap restartSpace
      lastSpace
      shiftDeepChainProc initCore coreLenProc edgeProc signExt mul intDiv copy lastInit
      packEditsProc initTree bind canonCopy isNeg : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {opCore opLast opTree : ℕ → ℕ}
    (levelSpace : ℕ → ℕ) (levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ)
    (hProc : p.procs[shiftDeepChainProc]? =
      some (shiftDeepChainBodyKFBL initCore (opCore 1) (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg))
    (hPackProc : p.procs[packEditsProc]? = some wireSuffixPackEditsBody)
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hFmtPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hL4W : 4 * L + 2 < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hdW : cfg.P.d < 2 ^ w) (hN0W : cfg.N₀ < 2 ^ w)
    (hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T) (hWordExpEq : Psc.wordExp = wordExp)
    (hCore : DeepShiftCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hFCap : DeepShiftForestCapKFBL fmt L vCap eCap capExp cfg Psc allocation fcap Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hLastImpl : ∀ G : MGraph, G.m ≤ m → G.m ≤ levelM cfg.TP cfg.P cfg.P.d → G.n ≤ G.m + 1 →
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L G vCap eCap lastMul stretchPrec lastAlloc))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hOps : DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace) (deepFixed := deepFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) restartSpace levelSpace levelCost lastSpace) :
    ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p shiftDeepChainProc deepSpace
      deepFixed toolMul (wireTreeSyncEditCost L drainUnit + 2) := by
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  refine ⟨_, hProc, ?_⟩
  intro root heap pos i ω mem0 mem model tok B R
  dsimp only
  let d := cfg.P.d
  let i0 := i.val
  let model' := alg2LoopShiftStep cfg model i
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let n0Cell := solverN0Addr tok.table cfg.P.d
  let lvlMTable := solverLvlMAddr tok.table cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table cfg.P.d
  let cnt := d - i0 + 1
  intro hiLt hRep0 hMeta0 hCaps0 hMemEq hSched' hNum0 hOffInv0 hOffBd0 _hCapFacts hBranLt
    hModelInv hModelK hIntCapLe hForestCap hLogW hCapT hFootLt hzHeap hHeapRoom
  have hChain' : model'.chain = (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i0).1 := by
    simp [model', alg2LoopShiftStep, i0]
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hRep0Full : Rrep.rep root model tok mem0 := hRep0
  have hMeta0Full : SolverLevelMetaAt P V model tok mem0 := hMeta0
  have hModelInvFull : ShiftDeepModelInv w L P wordExp stretchPrec model i := hModelInv
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, hFreshInv, hFreshTab0, hExtLtM,
    ⟨hG0Cap, hIntCapPos, hNextFreshLe, hI2EId⟩, _, hOffReady0, hTreeN0, hLct0,
    hTreeRep0, hAccounts0, _, _, _, _, hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hT13, hT14,
    hT15, hT16, hT1718, _, hT20, hT21⟩ := hTags0
  obtain ⟨hTable0, hRootG0, _, hNamed0, _⟩ := hWire0
  obtain ⟨⟨hN0Val, hTagN0, hTagSH, hTagSB⟩, hCoreOwn0, hLvlM0, hTagM0, hTagMeta0, -⟩ := hMeta0
  obtain ⟨_, _, _, _, _, _, _, _, _, hNewForest, hOldSub, hNewSub, _, _, _, hDisjPref⟩ := hModelInv
  let G0 := model.chain.G 0
  let oldF := model.chain.toTreeChain.chainTree
  let newF := model'.chain.toTreeChain.chainTree
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hG0nEq : G0.n = model.extG.n := by unfold MGraph.n; rw [← hFreshInv.hV]
  have hRootW : root + 16 ≤ heap := by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ heap := by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hRootGW : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ heap := by
    have hpos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
    have := htagLt (by rw [hT20 (tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1)
      (by omega) (by omega)]; decide); omega
  -- Phases 0–4a via `shiftDeep_phases_0_to_4a_runs`
  obtain ⟨s5, c04a, newTermH, newTermTok, newCoreHandle, newCoreTok,
      r04a, hHeapLo5, hHeapHi5, hz5, h5_70, _, h5_73, _, h5_79, h5_80, h5_81,
      hOldForests5, hNewForests5, hCores5, hCoreDisj5, hTermH5, hTermB5, hTermRep5, hTermFoot5,
      hMeta5, hMetaOrd5, hFrame5, hCost5⟩ :=
    shiftDeep_phases_0_to_4a_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi)
      (k := k) (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (wordExp := wordExp)
      (stretchPrec := stretchPrec) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace) (deepFixed := deepFixed)
      (toolMul := toolMul) (vCap := vCap) (eCap := eCap) (capLimit := capLimit) (fcap := fcap)
      (restartSpace := restartSpace)
      (lastSpace := lastSpace) (initCore := initCore) (coreLenProc := coreLenProc)
      (edgeProc := edgeProc) (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
      (lastInit := lastInit) (root := root) (heap := heap) (pos := pos) (fmt := fmt) (cfg := cfg)
      (Psc := Psc) (allocation := allocation) (lastAlloc := lastAlloc) (Rcore := Rcore) (p := p)
      (opCore := opCore) (opLast := opLast) (ω := ω) (mem0 := mem0) (mem := mem) (model := model)
      (tok := tok) (i := i) levelSpace levelCost hCoreLocal hFmtBits hFmtPrec hWidth hL4W hw17
      hkPos hkW hdW hN0W hDepthW hInitOrdEq hCore hFCap hcapLim hLastImpl hCoreLenProc hEdgeProc
      hSign hMul hDiv hCopy hOps hiLt hRep0Full hMeta0Full hCaps0 hMemEq hBranLt hModelInvFull
      hModelK hWordExpEq hFootLt hzHeap hHeapRoom
  have h5_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
      (hv22 : v ≠ 22 + d) (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s5.mem a = mem0 a :=
    (hFrame5 a (htagLt (ht ▸ hv0)) (ht ▸ hv4) (ht ▸ hv22) (fun j hj1 hj2 => ht ▸ hvC j hj1 hj2)).trans
      (hMemEq a (ht ▸ hv5))
  -- Phase 4b: load `intCap`, compute `editsBuf = s5.regs 4 + 3 * intCap`, call `packEditsProc`
  let editsBuf := s5.regs 4 + 3 * tok.intCap
  let s6 := { s5 with regs := Function.update s5.regs 10 tok.intCap }
  let s7 := { s6 with regs := Function.update s6.regs 6 editsBuf }
  have hIntCap5 : s5.mem (root + 15) = tok.intCap :=
    (h5_eq_mem0 (hT1 15 (by omega)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)).trans
      (by simpa using hRootDir0 15 (by simp))
  have r6 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 15)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by simp [Expr.eval, BinOp.eval, h5_70,
      show 15 < 2 ^ w by omega, show root + 15 < 2 ^ w by omega, hIntCap5], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10)))) s6 .normal s7 6 :=
    runs_assign_iff.mpr ⟨editsBuf, by simp [Expr.eval, BinOp.eval, s6,
      show 3 < 2 ^ w by omega, show 3 * tok.intCap < 2 ^ w by omega,
      show editsBuf < 2 ^ w by dsimp [editsBuf]; omega, editsBuf], rfl, rfl, rfl⟩
  have hPackRoom : s5.regs 4 + 3 * tok.intCap +
      2 * (graphListEdgeSum (chainSuffixForests model.chain i0) +
        graphListEdgeSum (chainSuffixForests model'.chain i0)) < 2 ^ w := by
    have hmul : 2 * forestEdgeCap ≤ forestEdgeCap * (2 + wireTreeSyncEditSpace L) := by
      have : 2 * forestEdgeCap = forestEdgeCap * 2 := Nat.mul_comm _ _
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    dsimp only [model', i0] at hForestCap ⊢; omega
  obtain ⟨outPack, cPack, edits, rPackBody, hcPack, hEditsLe, hEditsAt8, hDiffSuffix, hz8, hFr8⟩ :=
    wireSuffixPackEdits_runs (w := w) (oldPtrs := heap) (newPtrs := heap + cnt) (cnt := cnt)
      (intCap := tok.intCap) (heap := s5.regs 4) (pos := s7.pos)
      (oldFs := chainSuffixForests model.chain i0) (newFs := chainSuffixForests model'.chain i0)
      (p := p) (ω := ω) (mem := s7.mem)
      (chainSuffixForests_length _ _) (chainSuffixForests_length _ _)
      hOldForests5 hNewForests5 hz5 hPackRoom (by omega)
  let s8 : State := { regs := Function.update s7.regs 18 edits.length, mem := outPack.mem, pos := outPack.pos }
  have r8 : Runs w p ω (.call 18 packEditsProc [.reg 80, .reg 81, .reg 79, .reg 10, .reg 4])
      s7 .normal s8 (5 + cPack + 1) :=
    runs_call_iff.mpr ⟨[heap, heap + cnt, cnt, tok.intCap, s5.regs 4], wireSuffixPackEditsBody,
      .returned edits.length, outPack, cPack, by
        simp [evalArgs, Expr.eval, s7, s6, h5_80, h5_81, h5_79, cnt, d, i0],
      hPackProc, rPackBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- Lift suffix edit difference to full chain tree difference
  obtain ⟨hDiffFull, hDiffLen⟩ :=
    treeEditDiff_chainSuffix (le_of_lt hiLt)
      (fun j hj => by rw [hChain']; exact ⟨(hEx.2.1 j hj).1, (hEx.2.1 j hj).2.1⟩)
      hDisjPref hDiffSuffix
  have hEditsLenEq : edits.length = model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates := by
    rw [hDiffLen, hChain', shiftDeep_totalTreeUpdates_sub cfg.T cfg.L cfg.P model.chain hiLt]
  have hEditsLeCap : edits.length ≤ forestEdgeCap := hEditsLe.trans hForestCap
  -- Phase 4c: set up `reg 27, 29`, run `shiftTermSetupLoop`, `wireTreeSyncLoop`, and `.ret (.reg 3)`
  let s9a := { s8 with regs := Function.update s8.regs 27 root }
  let s9b := { s9a with regs := Function.update s9a.regs 29 tok.handle }
  have r9a : Runs w p ω (.assign 27 (.reg 70)) s8 .normal s9a 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s8, s7, s6, h5_70], rfl, rfl, rfl⟩
  have r9b : Runs w p ω (.assign 29 (.reg 73)) s9a .normal s9b 2 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s9a, s8, s7, s6, h5_73], rfl, rfl, rfl⟩
  have h8_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
      (hv22 : v ≠ 22 + d) (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s8.mem a = mem0 a :=
    (hFr8 a (lt_of_lt_of_le (htagLt (ht ▸ hv0)) (by omega))).trans
      (h5_eq_mem0 ht hv0 hv4 hv5 hv22 hvC)
  have hRootG8 : DynGraphAt s8.mem tok.rootGraph model.extG.n tok.rootECap G0 :=
    dynGraphAt_of_agree hRootG0 (fun a ha1 ha2 =>
      h8_eq_mem0 (hT20 a ha1 ha2) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega))
  have hLoadRoot (j : ℕ) (hj : j < 16) : s8.mem (root + j) = mem0 (root + j) :=
    h8_eq_mem0 (hT1 j hj) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
  have hLoadHdr (j : ℕ) (hj : j < 18) : s8.mem (tok.handle + j) = mem0 (tok.handle + j) :=
    h8_eq_mem0 (hT2 j hj) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
  obtain ⟨s10, cSetup, rSetup, hcSetup, hs10Mem, h10_0, h10_1, h10_2, h10_3, h10_6, h10_18, h10_9, h10_10,
      h10_11, h10_19, h10_20, h10_22, h10_23, h10_24, h10_25, h10_26⟩ :=
    shiftTermSetupLoop_runs (w := w) (st := s9b) (editPtr := editsBuf) (nEdits := edits.length)
      (root := root) (handle := tok.handle) (by simp [s9b, s9a, s8, s7])
      (by simp [s9b, s9a, s8]) (by simp [s9b, s9a]) (by simp [s9b])
      ((hLoadHdr 0 (by omega)).trans (by simpa using hDetHdr0 0 (by simp)))
      ((hLoadHdr 5 (by omega)).trans (by simpa using hDetHdr0 5 (by simp)))
      ((hLoadRoot 14 (by omega)).trans (by simpa using hRootDir0 14 (by simp)))
      (by simpa [dgVCapOff] using hRootG8.2.2.2.1)
      (by simpa [dgECapOff] using hRootG8.2.2.2.2.1)
      ((hLoadRoot 6 (by omega)).trans (by simpa using hRootDir0 6 (by simp)))
      ((hLoadRoot 7 (by omega)).trans (by simpa using hRootDir0 7 (by simp)))
      ((hLoadRoot 8 (by omega)).trans (by simpa using hRootDir0 8 (by simp)))
      ((hLoadRoot 9 (by omega)).trans (by simpa using hRootDir0 9 (by simp)))
      ((hLoadRoot 10 (by omega)).trans (by simpa using hRootDir0 10 (by simp)))
      ((hLoadRoot 12 (by omega)).trans (by simpa using hRootDir0 12 (by simp)))
      ((hLoadRoot 13 (by omega)).trans (by simpa using hRootDir0 13 (by simp)))
      (by omega) (by omega) (by dsimp only [editsBuf]; omega) (by omega)
  -- Build `WireSyncCtx` and `WireSyncInv`, run `wireTreeSyncLoop`
  let heap0 := editsBuf + 2 * edits.length
  obtain ⟨canonVal, hLive0, hCanonExt⟩ :=
    liveAccounts_of_solverStateRep hRep0Full hNum0 hOffInv0 hOffBd0 hOldSub
  have hCanonProp : ∀ ei ∈ G0.E, (canonVal ei).forward = true ∧
      |(canonVal ei).gradient| ≤ B ∧ |(canonVal ei).length| ≤ B ∧
      |(canonVal ei).flow| ≤ B ∧ |(canonVal ei).detector| ≤ B := fun ei heiG => by
    obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
    obtain ⟨hf, hg, hl, hfl, hd, _⟩ := hCanonExt (model.intToExt ei) heExt
    rw [heMap] at hf hg hl hfl hd; exact ⟨hf, hg, hl, hfl, hd⟩
  have hOffAt0 : ∀ ei ∈ G0.E, ei ∉ oldF.E →
      PathEdgeAt mem0 (mem0 (tok.edgeRecords + ei)) 4 L (some (canonVal ei)) := fun ei heiG hnot => by
    obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
    have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
    rwa [heMap] at hrec
  have hAgree10 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
      (hv22 : v ≠ 22 + d) (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s10.mem a = mem0 a :=
    hs10Mem.symm ▸ h8_eq_mem0 ht hv0 hv4 hv5 hv22 hvC
  have h2nW : 2 * G0.n + 1 < 2 ^ w := by
    rw [hG0nEq]
    by_cases hn0 : model.extG.n = 0
    · omega
    · have hEnd : tok.names + 2 * tok.tree.n ≤ heap := by
        have := htagLt (by rw [hT10 (2 * tok.tree.n - 1) (by omega)]; decide); omega
      omega
  have hTreeHeapLt : tok.treeHeap < 2 ^ w :=
    lt_trans (htagLt (by rw [hT16 tok.treeHeap (pathRep_foot_base_mem_deep hTreeRep0)]; decide)) (by omega)
  have hSyncRoom : heap0 + edits.length * wireTreeSyncEditSpace L < 2 ^ w := by
    have h1 : 2 * edits.length + edits.length * wireTreeSyncEditSpace L =
        edits.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits.length * (2 + wireTreeSyncEditSpace L) ≤
        forestEdgeCap * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEditsLeCap
    dsimp [heap0, editsBuf]; omega
  have hM'_G0 : model'.chain.G 0 = G0 := hChain' ▸ hEx.1 0 (Nat.zero_le _)
  let ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editsBuf heap0 s10.mem G0 oldF newF edits tok canonVal B R :=
    { fmtBits := hFmtBits, hw11 := by omega, treeImpl := hTreeImpl, bindOk := hBindOk,
      canonOk := hCanonOk, isNegOk := hIsNegOk, treeHeapLt := hTreeHeapLt, nW := h2nW,
      logW := hG0nEq.symm ▸ hLogW, capT := hG0nEq.symm ▸ hCapT, diff := hDiffFull,
      oldSub := hOldSub, newSub := hNewSub, newForest := hNewForest,
      oldEnds := fun _ _ => ⟨rfl, rfl⟩,
      newEnds := fun _ _ => by
        show G0.tail _ = newF.tail _ ∧ G0.head _ = newF.head _
        simp [newF, TreeChain.chainTree, ChainState.toTreeChain, hM'_G0],
      vtxE := fun ei hei => by
        obtain ⟨h1, h2⟩ := hRootG0.1 ei hei
        exact ⟨hG0nEq.symm ▸ hRootG0.2.1 _ h1, hG0nEq.symm ▸ hRootG0.2.1 _ h2⟩,
      capE := hG0Cap, rootGraph := hG0nEq.symm ▸ (hs10Mem.symm ▸ hRootG8),
      editsAt := hs10Mem.symm ▸ hEditsAt8, editsEnd := le_rfl,
      editsTag0 := fun a ha1 _ => ⟨by by_contra hne; have := htagLt hne; dsimp [editsBuf] at ha1; omega,
        by dsimp [editsBuf] at ha1; omega⟩,
      tags := by
        refine ⟨fun a h => lt_of_lt_of_le (htagLt h) (by dsimp only [heap0, editsBuf]; omega), hT1, hT9,
          fun sl hsl => hT10 sl (by omega), fun sl hsl => hT11 sl (by omega),
          hT12, hT13, hT14, hT15, hT16, fun ei hei hnot j hj => ?_, fun a ha1 ha2 =>
            hT20 a ha1 (by rwa [← hG0nEq])⟩
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei hei
        have hrecEq : s10.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
          hAgree10 (hT13 ei (hG0Cap ei hei)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
        rw [hrecEq]
        have ht18 := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) j hj
        rwa [heMap] at ht18,
      canonProp := hCanonProp, room := hSyncRoom }
  have hSlotEq10 (ei : ℕ) (hei : ei ∈ oldF.E) : s10.mem (tok.slots + ei) = mem0 (tok.slots + ei) :=
    hAgree10 (hT9 ei (hG0Cap ei (hOldSub hei))) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
  have hNameEq10 (sl : ℕ) (hsl : isEdgeSlot tok.tree.n sl) : s10.mem (tok.names + sl) = mem0 (tok.names + sl) := by
    have hlt : sl < 2 * tok.tree.n := by unfold isEdgeSlot at hsl; omega
    exact hAgree10 (hT10 sl hlt) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
  obtain ⟨hTreeRep10_iff, hTreePhi10_eq⟩ := hTreeImpl.1 tok.treeHeap tok.tree tok.treeTok mem0 s10.mem
    (fun a ha => (hAgree10 (hT16 a ha) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)).symm)
  have hInvInit : WireSyncInv root editsBuf heap0 s10.mem G0 oldF newF edits tok canonVal B R
      [] edits tok.tree tok.treeTok heap0 tok.offReadyCount s10 := by
    refine ⟨rfl, h10_0, h10_1, h10_2, h10_3, by simpa using h10_6, h10_18, hG0nEq.symm ▸ h10_9,
      hG0nEq.symm ▸ h10_10, hG0nEq.symm ▸ h10_11, h10_19, h10_20, h10_22, h10_23, h10_24, h10_25,
      h10_26, le_rfl, by simp, hs10Mem.symm ▸ hz8, fun a ha => Or.inl ha,
      fun _ _ _ _ _ _ _ _ _ _ => rfl, hTreeN0.trans hG0nEq.symm,
      ⟨tok.trees, tok.free, tok.depth, hLct0, hNum0,
        namedSlots_congr_slot hNamed0 hSlotEq10 (fun sl _ hsl => hNameEq10 sl hsl),
        liveAccounts_congr_slot hLive0 hSlotEq10⟩,
      hTreeRep10_iff hTreeRep0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ei hei; change ei ∈ oldF.E at hei
      have hcap := hG0Cap ei (hOldSub hei)
      have hsl : isEdgeSlot tok.tree.n (mem0 (tok.slots + ei)) := (hNamed0.forward ei hei).2.1
      have hslLt : mem0 (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hsl; omega
      rw [hSlotEq10 ei hei,
        hAgree10 (hT11 _ hslLt) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega),
        hAgree10 (hT12 ei hcap) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei (hOldSub hei)
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact hacc.2.2.2.1
      · exact (hmem hei).elim
    · intro ei heiG hnot; change ei ∉ oldF.E at hnot
      rw [hAgree10 (hT9 ei (hG0Cap ei heiG)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact (hnot hmem).elim
      · exact hacc.1
    · intro ei heiG hnot; change ei ∉ oldF.E at hnot
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      rw [hAgree10 (hT13 ei (hG0Cap ei heiG)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
      refine (hOffAt0 ei heiG hnot).congr fun a ha1 ha2 => ?_
      have ht18 := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) (a - mem0 (tok.edgeRecords + ei)) (by omega)
      rw [heMap, show mem0 (tok.edgeRecords + ei) + (a - mem0 (tok.edgeRecords + ei)) = a by omega] at ht18
      exact hAgree10 ht18 (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
    · intro ei heiG hnot hdet; change ei ∉ oldF.E at hnot
      rw [hAgree10 (hT15 ei (hG0Cap ei heiG)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact (hnot hmem).elim
      · obtain ⟨_, val, _, hAt, _, _, _, hPush⟩ := hacc
        have hEq := (readPathEdge_eq hAt).symm.trans (readPathEdge_eq (hOffAt0 ei heiG hnot))
        exact hPush (Option.some.inj hEq ▸ hdet)
    · intro ei _ hnot; change ei ∉ oldF.E at hnot; exact ⟨fun h => (hnot h).elim, fun _ => rfl⟩
    · intro e1 he1 e2 he2 hne hnot1 hnot2; change e1 ∉ oldF.E at hnot1; change e2 ∉ oldF.E at hnot2
      rw [hAgree10 (hT13 e1 (hG0Cap e1 he1)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega),
        hAgree10 (hT13 e2 (hG0Cap e2 he2)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
      obtain ⟨hm1, hx1⟩ := hFreshInv.hRight e1 he1
      obtain ⟨hm2, hx2⟩ := hFreshInv.hRight e2 he2
      have hxe : model.intToExt e1 ≠ model.intToExt e2 := fun h => hne (hm1.symm.trans (h ▸ hm2))
      simpa [hm1, hm2] using hOffInv0.2 (model.intToExt e1) hx1 (model.intToExt e2) hx2 hxe
        (hm1.symm ▸ hnot1) (hm2.symm ▸ hnot2)
    · exact hs10Mem.symm ▸ (hLoadRoot 11 (by omega)).trans (by simpa using hRootDir0 11 (by simp))
    · have hAL (j : ℕ) (hj : j < tok.intCap) : s10.mem (tok.offReadyList + j) = mem0 (tok.offReadyList + j) :=
        hAgree10 (hT14 j hj) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
      have hAI (j : ℕ) (hj : j < tok.intCap) : s10.mem (tok.inOffReady + j) = mem0 (tok.inOffReady + j) :=
        hAgree10 (hT15 j hj) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)
      obtain ⟨hc, h1', h2', h3', h4'⟩ := hOffReady0
      refine ⟨hc, fun j hj => ?_, fun j1 hj1 j2 hj2 hne => ?_, fun k hk => ?_, fun k hk h1'' => ?_⟩
      · rw [hAL j (by omega)]; exact ⟨(h1' j hj).1, (hAI _ (h1' j hj).1).trans (h1' j hj).2⟩
      · rw [hAL j1 (by omega), hAL j2 (by omega)]; exact h2' j1 hj1 j2 hj2 hne
      · rw [hAI k hk]; exact h3' k hk
      · rw [hAI k hk] at h1''; obtain ⟨j, hj, hje⟩ := h4' k hk h1''
        exact ⟨j, hj, (hAL j (by omega)).trans hje⟩
  obtain ⟨s11, cLoop, curTree', curTreeTok', nextHeap, curOffCnt', rLoop, hInvEnd, hcLoop⟩ :=
    wireTreeSyncLoop_runs ctx hInvInit
  obtain ⟨_, _, _, _, h11_3, _, _, _, _, _, _, _, _, _, _, _, _,
    hNextGe0, hNextLe0, hzNext, hFootEnd, hFrameEnd, hTreeNEnd,
    ⟨curTrees', curFree', curDepth', hLctEnd, hNumEnd, hNamedEnd, hLiveEnd⟩,
    hTreeRepEnd, hSlotThrEnd, hOffSlotEnd, hOffRecEnd, hOffPushEnd,
    hOffWhereEnd, hOffDisjEnd, hOffCntEnd, hOffReadyEnd⟩ := hInvEnd
  rw [hDiffFull.result.2] at hNamedEnd hLiveEnd hSlotThrEnd hOffSlotEnd hOffRecEnd hOffPushEnd hOffWhereEnd hOffDisjEnd
  have rRet : Runs w p ω (.ret (.reg 3)) s11 (.returned nextHeap) s11 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, h11_3], rfl, rfl, rfl⟩
  -- Compose tail and re-associate `r04a` + tail into `shiftDeepChainBody`
  have rTail : Runs w p ω
      (.assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
       .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
       .call 18 packEditsProc [.reg 80, .reg 81, .reg 79, .reg 10, .reg 4] ;;
       .assign 27 (.reg 70) ;; .assign 29 (.reg 73) ;;
       shiftTermSetupLoop ;;
       wireTreeSyncLoop (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg ;;
       .ret (.reg 3))
      s5 (.returned nextHeap) s11
      (5 + (6 + ((5 + cPack + 1) + (2 + (2 + (cSetup + (cLoop + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 6, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5 + cPack + 1, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9a, 2, _, r9a,
    runs_seq_iff.mpr (Or.inr ⟨s9b, 2, _, r9b,
    runs_seq_iff.mpr (Or.inr ⟨s10, cSetup, _, rSetup,
    runs_seq_iff.mpr (Or.inr ⟨s11, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have rAll := shiftDeep_compose_body_runs r04a rTail
  -- Memory agreement between `s11` and `s5` / `mem` / `mem0`
  have h11_eq_s5 (a : ℕ) (ha : a < s5.regs 4) (hne11 : a ≠ root + 11)
      (h9 : tok.tag a ≠ 9) (h10 : tok.tag a ≠ 10) (h11 : tok.tag a ≠ 11) (h13 : tok.tag a ≠ 13)
      (h14 : tok.tag a ≠ 14) (h15 : tok.tag a ≠ 15) (h16 : tok.tag a ≠ 16) : s11.mem a = s5.mem a :=
    (hFrameEnd a (by dsimp [heap0, editsBuf]; omega) hne11 h9 h10 h11 h13 h14 h15 h16).trans
      (hs10Mem.symm ▸ hFr8 a ha)
  have h11_eq_s5_geHeap (a : ℕ) (haLo : heap ≤ a) (haHi : a < s5.regs 4) : s11.mem a = s5.mem a := by
    have htag0 : tok.tag a = 0 := by by_contra hne; have := htagLt hne; omega
    exact h11_eq_s5 a haHi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h11_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hv4 : v ≠ 4)
      (hv5 : v ≠ 5) (hv9 : v ≠ 9) (hv10 : v ≠ 10) (hv11 : v ≠ 11) (hv13 : v ≠ 13)
      (hv14 : v ≠ 14) (hv15 : v ≠ 15) (hv16 : v ≠ 16) (hv22 : v ≠ 22 + d)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s11.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    have hne11 : a ≠ root + 11 := fun h => hv1 (ht.symm.trans (h ▸ hT1 11 (by omega)))
    exact (h11_eq_s5 a (by omega) hne11 (ht ▸ hv9) (ht ▸ hv10) (ht ▸ hv11) (ht ▸ hv13)
      (ht ▸ hv14) (ht ▸ hv15) (ht ▸ hv16)).trans (h5_eq_mem0 ht hv0 hv4 hv5 hv22 hvC)
  -- Preserve rebuilt cores, terminal level, and `levelMeta` from `s5` to `s11`
  have hCores11 (j : ℕ) (hj : j < d) :
      s11.mem (handleBase + j) = newCoreHandle j ∧ s11.mem (branchBase + j) = model'.chain.bran j ∧
      Rcore.rep (newCoreHandle j) (chainLevelOrdAbs model'.chain j) (newCoreTok j) s11.mem ∧
      Rcore.phi (newCoreHandle j) (newCoreTok j) s11.mem =
        Rcore.phi (newCoreHandle j) (newCoreTok j) s5.mem := by
    obtain ⟨_, _, _, hH5, hB5, hRep5, hFoot5⟩ := hCores5 j hj
    have h4a := hT4 j (by omega)
    have h4b : tok.tag (branchBase + j) = 4 := by
      have := hT4 ((d + 1) + j) (by omega)
      rwa [show tok.handle + 18 + ((d + 1) + j) = branchBase + j by dsimp [branchBase, handleBase]; omega] at this
    have hloc := hCoreLocal (newCoreHandle j) (chainLevelOrdAbs model'.chain j) (newCoreTok j) s5.mem s11.mem
      (fun a ha => by
        rcases hFoot5 a ha with ⟨_, h0⟩ | ⟨hlo, hhi⟩
        · have ht := hT21 j hj a h0
          exact (h11_eq_s5 a (by have := htagLt (by rw [ht]; omega); omega)
            (fun h => by rw [h, hT1 11 (by omega)] at ht; omega) (by rw [ht]; omega) (by rw [ht]; omega)
            (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega)).symm
        · exact (h11_eq_s5_geHeap a hlo hhi).symm)
    exact ⟨(h11_eq_s5 _ (by have := htagLt (by rw [h4a]; decide); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at h4a; omega) (by rw [h4a]; decide) (by rw [h4a]; decide)
        (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide)).trans hH5,
      (h11_eq_s5 _ (by have := htagLt (by rw [h4b]; decide); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at h4b; omega) (by rw [h4b]; decide) (by rw [h4b]; decide)
        (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide)).trans hB5,
      hloc.1 hRep5, hloc.2.symm⟩
  have hTerm11 :
      s11.mem (handleBase + d) = newTermH ∧ s11.mem (branchBase + d) = model'.chain.lastBran ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (model'.chain.G d).E).rep
        newTermH (model'.chain.lastK, model'.chain.lastLSFs) newTermTok s11.mem := by
    have h4a := hT4 d (by omega)
    have h4b : tok.tag (branchBase + d) = 4 := by
      have := hT4 ((d + 1) + d) (by omega)
      rwa [show tok.handle + 18 + ((d + 1) + d) = branchBase + d by dsimp [branchBase, handleBase]; omega] at this
    refine ⟨(h11_eq_s5 _ (by have := htagLt (by rw [h4a]; decide); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at h4a; omega) (by rw [h4a]; decide) (by rw [h4a]; decide)
        (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide)).trans hTermH5,
      (h11_eq_s5 _ (by have := htagLt (by rw [h4b]; decide); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at h4b; omega) (by rw [h4b]; decide) (by rw [h4b]; decide)
        (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide)).trans hTermB5,
      (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P (model'.chain.G d).E
        newTermH (model'.chain.lastK, model'.chain.lastLSFs) newTermTok s5.mem s11.mem
        (fun a ha => (h11_eq_s5_geHeap a (hTermFoot5 a ha).1 (hTermFoot5 a ha).2.1).symm)).1 hTermRep5⟩
  -- Build `tok'` with classical tag dispatch above `heap`
  classical
  let Rterm' := LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (model'.chain.G d).E
  let tok' : SolverToken cfg L Rcore :=
    { tok with
      offReadyCount := curOffCnt'
      tree := curTree', trees := curTrees', free := curFree', depth := curDepth', treeTok := curTreeTok'
      coreHandle := newCoreHandle, coreTok := newCoreTok
      termHandle := newTermH, vcLast := vCap, ecLast := eCap, termTok := newTermTok
      owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < nextHeap)
      tag := fun a =>
        if a < heap then tok.tag a
        else if tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L then 16
        else if s5.regs 4 ≤ a ∧ a < nextHeap then 18
        else if Rterm'.foot newTermH newTermTok a then 19
        else if h : ∃ j : Fin d, i0 ≤ j.val ∧ Rcore.foot (newCoreHandle j.val) (newCoreTok j.val) a then
          21 + (Classical.choose h).val
        else if a < s5.regs 4 then 23 + d
        else 0 }
  have hFreshInv' : FreshInv model'.extG (model'.chain.G 0) model'.extToInt model'.intToExt model'.nextFresh :=
    hM'_G0.symm ▸ hFreshInv
  have hG0Cap' : ∀ e ∈ (model'.chain.G 0).E, e < tok.intCap := hM'_G0.symm ▸ hG0Cap
  have h11_fixed {a v : ℕ} (ht : tok.tag a = v)
      (hv : v = 2 ∨ v = 3 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 12 ∨ v = 17 ∨ v = 20 ∨ v = 21 + d ∨ v = 23 + d) :
      s11.mem a = mem0 a :=
    h11_eq_mem0 ht (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (fun _ _ _ => by omega)
  have hThrSame (e : ℕ) (he : e ∈ model.extG.E) :
      let ei := model.extToInt e
      s11.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
      ∀ j < L, s11.mem (mem0 (tok.edgeThresholds + ei) + j) = mem0 (mem0 (tok.edgeThresholds + ei) + j) := by
    intro ei
    have hcap := hG0Cap ei (hFreshInv.hE ▸ Finset.mem_image_of_mem model.extToInt he)
    exact ⟨h11_fixed (hT12 ei hcap) (by omega), fun j hj => h11_fixed ((hT1718 e he).1 j hj) (by omega)⟩
  have hGraphEq : ({ G0 with E := newF.E } : MGraph) = model'.chain.toTreeChain.chainTree := by
    show ({ V := G0.V, E := newF.E, tail := G0.tail, head := G0.head } : MGraph) =
      { V := newF.V, E := newF.E, tail := newF.tail, head := newF.head }
    simp only [newF, TreeChain.chainTree, ChainState.toTreeChain, hM'_G0]
  have hNamedEnd' : TreeEditNamedSlots curTree' curTrees' model'.chain.toTreeChain.chainTree
      (fun ei => s11.mem (tok.slots + ei)) (fun sl => s11.mem (tok.names + sl)) := hGraphEq ▸ hNamedEnd
  have hLiveEnd' : TreeEditLiveAccounts curTree' curTrees' model'.chain.toTreeChain.chainTree
      (fun ei => s11.mem (tok.slots + ei)) canonVal := hGraphEq ▸ hLiveEnd
  obtain ⟨hAccountsEnd, hOrientEnd, hOffInvEnd, hOffBdEnd⟩ :=
    solverEdgeAccounts_of_treeSync (model := model') (P := P) (B := B) hFreshInv' hLctEnd
      hNamedEnd' hLiveEnd' (hM'_G0.symm ▸ hNewSub) hG0Cap'
      (fun e he => by
        obtain ⟨hptr, hlimbs⟩ := hThrSame e he
        change PathIntAt s11.mem (s11.mem (tok.edgeThresholds + model.extToInt e)) 4 L _
        rw [hptr]; exact (hAccounts0.1 e he).2.1.congr (fun i hi => hlimbs i hi))
      (fun e he => by obtain ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4, _⟩ := hCanonExt e he; exact ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4⟩)
      hSlotThrEnd
      (fun e he hnot => hOffSlotEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot)
      (fun e he hnot => hOffRecEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot)
      (fun e he hnot hdet => hOffPushEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot hdet)
      (fun e1 he1 e2 he2 hne hnot1 hnot2 =>
        hOffDisjEnd (model.extToInt e1) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he1)
          (model.extToInt e2) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he2)
          (fun h => hne ((hFreshInv.hLeft e1 he1).symm.trans (h ▸ hFreshInv.hLeft e2 he2))) hnot1 hnot2)
  have hOldTag {a : ℕ} (h : tok.tag a ≠ 0) : tok'.tag a = tok.tag a := by
    dsimp only [tok']; simp only [htagLt h, ↓reduceIte]
  have hTreeFootNotMid (a : ℕ) (ha : Rtree.foot tok.treeHeap curTreeTok' a) :
      a < heap ∨ (s5.regs 4 ≤ a ∧ a < nextHeap) := by
    rcases hFootEnd a ha with h0 | ⟨hlo, hhi⟩
    · exact Or.inl (htagLt (by rw [hT16 a h0]; decide))
    · exact Or.inr ⟨by dsimp only [heap0, editsBuf] at hlo; omega, hhi⟩
  -- Prove `Rrep.rep root model' tok' s11.mem`
  have hRepEnd : Rrep.rep root model' tok' s11.mem := by
    refine ⟨?_, ?_, ?_, ?_, hFreshInv', ?_, hExtLtM,
      ⟨hG0Cap', hIntCapPos, hNextFreshLe, hI2EId⟩, ?_, hOffReadyEnd,
      hTreeNEnd.trans hG0nEq, hLctEnd, hTreeRepEnd, hAccountsEnd,
      fun j hj => ⟨(hCores11 j hj).1, (hCores11 j hj).2.1, (hCores11 j hj).2.2.1⟩,
      hTerm11.1, hTerm11.2.1, hTerm11.2.2, ?_, ?_⟩
    · intro j hj
      have hj16 : j < 16 := by simpa using hj
      by_cases h11 : j = 11
      · subst h11; simpa [tok'] using hOffCntEnd
      · rw [h11_eq_s5 (root + j) (by omega) (by omega) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
          (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
          (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide),
          h5_eq_mem0 (hT1 j hj16) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
        have h0 := hRootDir0 j hj
        have : [tok'.handle, tok'.table, tok'.levelsEnd, tok'.forward, tok'.inverse,
            tok'.freshCounter, tok'.slots, tok'.names, tok'.slotThresholds, tok'.edgeThresholds,
            tok'.edgeRecords, tok'.offReadyCount, tok'.offReadyList, tok'.inOffReady,
            tok'.rootGraph, tok'.intCap][j] =
          [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse,
            tok.freshCounter, tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds,
            tok.edgeRecords, tok.offReadyCount, tok.offReadyList, tok.inOffReady,
            tok.rootGraph, tok.intCap][j] := by interval_cases j <;> first | rfl | contradiction
        exact h0.trans this.symm
    · intro j hj; have hj8 : j < 8 := by simpa using hj
      rw [h11_fixed (hT2 j (by omega)) (by omega)]; exact hDetHdr0 j hj
    · intro j hj; have hj4 : j < 4 := by simpa using hj
      have h2 : tok.tag (tok.handle + 5 + j) = 2 := by have := hT2 (5 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [h11_fixed h2 (by omega)]; exact hNumHdr0 j hj
    · intro j hj; have hj8 : j < 9 := by simpa using hj
      have h2 : tok.tag (tok.handle + 9 + j) = 2 := by have := hT2 (9 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [h11_fixed h2 (by omega)]; exact hInitPar0 j hj
    · exact ⟨by rw [h11_fixed hT6 (by omega)]; exact hFreshTab0.1,
        fun e he => by rw [h11_fixed (hT7 e he) (by omega)]; exact hFreshTab0.2.1 e he,
        fun j hj => by rw [h11_fixed (hT8 j hj) (by omega)]; exact hFreshTab0.2.2 j hj⟩
    · have hS5 (j : ℕ) (hj : j < 4 * (d + 1) + 1) : s11.mem (tok.levelsEnd + j) = mem (tok.levelsEnd + j) :=
        (h11_eq_s5 _ (by have := htagLt (by rw [hT5 j hj]; decide); omega)
          (fun h => by have := hT5 j hj; rw [h, hT1 11 (by omega)] at this; omega)
          (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide)
          (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide)).trans
          (hFrame5 _ (htagLt (by rw [hT5 j hj]; decide)) (by rw [hT5 j hj]; decide)
            (by rw [hT5 j hj]; omega) (fun _ _ _ => by rw [hT5 j hj]; omega))
      refine ⟨fun r => (hS5 r.val (by omega)).trans (hSched'.1 r),
        fun r hr => by rw [Nat.add_assoc]; exact (hS5 ((d + 1) + r) (by omega)).trans (by simpa [Nat.add_assoc] using hSched'.2.1 r hr),
        fun r hr => by rw [Nat.add_assoc]; exact (hS5 (2 * (d + 1) + r) (by omega)).trans (by simpa [Nat.add_assoc] using hSched'.2.2.1 r hr),
        fun r hr => by rw [Nat.add_assoc]; exact (hS5 (3 * (d + 1) + r) (by omega)).trans (by simpa [Nat.add_assoc] using hSched'.2.2.2.1 r hr),
        (hS5 (4 * (d + 1)) (by omega)).trans hSched'.2.2.2.2⟩
    · refine ⟨fun j hj => ?_, ?_, ⟨hNewForest, fun ei hei => ?_⟩, hNamedEnd', hOrientEnd⟩
      · rw [h11_eq_mem0 (hT3 j hj) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega)]
        exact hTable0 j hj
      · rw [hM'_G0]
        exact dynGraphAt_of_agree hRootG0 (fun a ha1 ha2 =>
          h11_eq_mem0 (hT20 a ha1 ha2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega))
      · have heiG0 := hNewSub hei
        obtain ⟨h1, h2⟩ := hRootG0.1 ei heiG0
        have hEndN : newF.tail ei = G0.tail ei ∧ newF.head ei = G0.head ei := by
          simp [newF, TreeChain.chainTree, ChainState.toTreeChain, hM'_G0]
        have hne := named_account_endpoints_ne (G := newF) hLctEnd hNamedEnd' hei
          (by rw [hTreeNEnd, hG0nEq, hEndN.1]; exact hRootG0.2.1 _ h1)
        exact ⟨hG0Cap ei heiG0, hEndN.1.symm ▸ hRootG0.2.1 _ h1, hEndN.2.symm ▸ hRootG0.2.1 _ h2, hne⟩
    · have hTreeNEq : tok'.tree.n = tok.tree.n := by dsimp [tok']; omega
      refine ⟨fun a ha => ?_, fun j hj => (hOldTag (by rw [hT1 j hj]; decide)).trans (hT1 j hj),
        fun j hj => (hOldTag (by rw [hT2 j hj]; decide)).trans (hT2 j hj),
        fun j hj => (hOldTag (by rw [hT3 j hj]; decide)).trans (hT3 j hj),
        fun j hj => (hOldTag (by rw [hT4 j hj]; decide)).trans (hT4 j hj),
        fun j hj => (hOldTag (by rw [hT5 j hj]; decide)).trans (hT5 j hj),
        (hOldTag (by rw [hT6]; decide)).trans hT6,
        fun j hj => (hOldTag (by rw [hT7 j hj]; decide)).trans (hT7 j hj),
        fun j hj => (hOldTag (by rw [hT8 j hj]; decide)).trans (hT8 j hj),
        fun j hj => (hOldTag (by rw [hT9 j hj]; decide)).trans (hT9 j hj),
        fun j hj => (hOldTag (by rw [hT10 j (by omega)]; decide)).trans (hT10 j (by omega)),
        fun j hj => (hOldTag (by rw [hT11 j (by omega)]; decide)).trans (hT11 j (by omega)),
        fun j hj => (hOldTag (by rw [hT12 j hj]; decide)).trans (hT12 j hj),
        fun j hj => (hOldTag (by rw [hT13 j hj]; decide)).trans (hT13 j hj),
        fun j hj => (hOldTag (by rw [hT14 j hj]; decide)).trans (hT14 j hj),
        fun j hj => (hOldTag (by rw [hT15 j hj]; decide)).trans (hT15 j hj),
        fun a ha => ?_, fun e he => ?_, fun a ha => ?_,
        fun a ha1 ha2 => (hOldTag (by rw [hT20 a ha1 ha2]; decide)).trans (hT20 a ha1 ha2),
        fun j hj a ha => ?_⟩
      · -- `tok'.tag a ≠ 0 → tok'.owned a`
        dsimp only [tok'] at ha ⊢
        split_ifs at ha with hlt hft hmid hterm hcore hlt5
        · exact Or.inl (hOwnOfTag a ha)
        · rcases hTreeFootNotMid a hft with h0 | ⟨_, hhi'⟩
          · omega
          · exact Or.inr ⟨by omega, hhi'⟩
        · exact Or.inr ⟨by omega, hmid.2⟩
        · exact Or.inr ⟨(hTermFoot5 a hterm).1, lt_of_lt_of_le (hTermFoot5 a hterm).2.1 (by dsimp [heap0, editsBuf] at hNextGe0; omega)⟩
        · obtain ⟨j', _, hfj'⟩ := hcore
          rcases (hCores5 j'.val j'.isLt).2.2.2.2.2.2 a hfj' with ⟨_, h0⟩ | ⟨hlo, hhi⟩
          · have := htagLt (by rw [hT21 j'.val j'.isLt a h0]; omega); omega
          · exact Or.inr ⟨hlo, lt_of_lt_of_le hhi (by dsimp [heap0, editsBuf] at hNextGe0; omega)⟩
        · exact Or.inr ⟨by omega, lt_of_lt_of_le hlt5 (by dsimp [heap0, editsBuf] at hNextGe0; omega)⟩
        · exact (ha rfl).elim
      · -- Tag 16 (`Rtree.foot`)
        rcases hTreeFootNotMid a ha with h0 | ⟨hlo, _⟩
        · rcases hFootEnd a ha with h0' | ⟨hlo', _⟩
          · exact (hOldTag (by rw [hT16 a h0']; decide)).trans (hT16 a h0')
          · dsimp only [heap0, editsBuf] at hlo'; omega
        · have ha' : tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L := ha
          dsimp only [tok']; simp [show ¬ a < heap by omega, ha']
      · -- Tags 17 and 18
        refine ⟨fun j hj => ?_, fun hnot j hj => ?_⟩
        · change tok'.tag (s11.mem (tok.edgeThresholds + model.extToInt e) + j) = 17
          rw [(hThrSame e he).1]
          exact (hOldTag (by rw [(hT1718 e he).1 j hj]; decide)).trans ((hT1718 e he).1 j hj)
        · set ei := model.extToInt e
          change tok'.tag (s11.mem (tok.edgeRecords + ei) + j) = 18
          have heiG0 := hFreshInv.hE ▸ Finset.mem_image_of_mem model.extToInt he
          by_cases hOld : ei ∈ oldF.E
          · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhereEnd ei heiG0 hnot).1 hOld
            have hnf' : ¬ (tok.treeHeap ≤ s11.mem (tok.edgeRecords + ei) + j ∧
                s11.mem (tok.edgeRecords + ei) + j <
                LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L) := hnf _ (by omega) (by omega)
            dsimp only [tok']
            simp only [show ¬ s11.mem (tok.edgeRecords + ei) + j < heap by dsimp only [heap0, editsBuf] at hlo; omega,
              ↓reduceIte, hnf', and_self, show s5.regs 4 ≤ s11.mem (tok.edgeRecords + ei) + j ∧
                s11.mem (tok.edgeRecords + ei) + j < nextHeap by dsimp only [heap0, editsBuf] at hlo; exact ⟨by omega, by omega⟩]
          · have hrecEq : s11.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
              ((hOffWhereEnd ei heiG0 hnot).2 hOld).trans
                (hAgree10 (hT13 ei (hG0Cap ei heiG0)) (by decide) (by decide) (by decide) (by omega) (fun _ _ _ => by omega))
            rw [hrecEq]
            exact (hOldTag (by rw [(hT1718 e he).2 hOld j hj]; decide)).trans ((hT1718 e he).2 hOld j hj)
      · -- Tag 19 (`Rterm'.foot`)
        have ha' : Rterm'.foot newTermH newTermTok a := ha
        obtain ⟨hlo, hhi, _⟩ := hTermFoot5 a ha'
        have hnotTree : ¬ (tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L) :=
          fun h => by rcases hTreeFootNotMid a h with h0 | ⟨hlo', _⟩ <;> omega
        dsimp only [tok']
        simp only [show ¬ a < heap by omega, ↓reduceIte, hnotTree, show ¬ (s5.regs 4 ≤ a ∧ a < nextHeap) by omega, ha']
      · -- Tag `21 + j` (`Rcore.foot`)
        rcases (hCores5 j hj).2.2.2.2.2.2 a ha with ⟨hle, h0⟩ | ⟨hlo, hhi⟩
        · exact (hOldTag (by rw [hT21 j hj a h0]; omega)).trans (hT21 j hj a h0)
        · have hjGe : i0 ≤ j := by
            by_contra hlt; push Not at hlt
            dsimp only [tok'] at ha
            rw [(hCores5 j hj).1 (le_of_lt hlt), (hCores5 j hj).2.1 hlt] at ha
            have := htagLt (by rw [hT21 j hj a ha]; omega); omega
          have hnotTree : ¬ (tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L) :=
            fun h => by rcases hTreeFootNotMid a h with h0 | ⟨hlo', _⟩ <;> omega
          have hnotTerm : ¬ Rterm'.foot newTermH newTermTok a := fun ht => (hTermFoot5 a ht).2.2 j hj ha
          have hex : ∃ j' : Fin d, i0 ≤ j'.val ∧ Rcore.foot (newCoreHandle j'.val) (newCoreTok j'.val) a :=
            ⟨⟨j, hj⟩, hjGe, ha⟩
          dsimp only [tok']
          simp only [show ¬ a < heap by omega, ↓reduceIte, ↓reduceDIte, hnotTree,
            show ¬ (s5.regs 4 ≤ a ∧ a < nextHeap) by omega, hnotTerm, hex]
          have hEq : (Classical.choose hex).val = j := by
            by_contra hne
            exact hCoreDisj5 (Classical.choose hex).val (Classical.choose hex).isLt j hj hne a
              (Classical.choose_spec hex).2 ha
          rw [hEq]
  -- Prove `SolverLevelMetaAt P V model' tok' s11.mem` and `SolverLevelCapsAt` at once
  have hMetaCapsEnd : SolverLevelMetaCapsAt P V vCap eCap model' tok' s11.mem := by
    have hMetaMem {a v : ℕ} (ht : tok.tag a = v) (hv : v = 20 ∨ v = 21 + d ∨ v = 23 + d) :
        s11.mem a = mem0 a ∧ tok'.tag a = v :=
      ⟨h11_fixed ht (by rcases hv with rfl | rfl | rfl <;> simp),
       (hOldTag (by rw [ht]; rcases hv with rfl | rfl | rfl <;> omega)).trans ht⟩
    have hTag22 {a : ℕ} (ht : tok.tag a = 22 + d) : s11.mem a = s5.mem a :=
      h11_eq_s5 a (by have := htagLt (by rw [ht]; omega); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at ht; omega)
        (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega)
        (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega)
    dsimp only [SolverLevelMetaCapsAt]
    refine ⟨⟨by rw [(hMetaMem hTagN0 (Or.inr (Or.inl rfl))).1, hN0Val, hChain',
        hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2], (hMetaMem hTagN0 (Or.inr (Or.inl rfl))).2,
        (hMetaMem hTagSH (Or.inr (Or.inl rfl))).2, (hMetaMem hTagSB (Or.inr (Or.inl rfl))).2⟩,
      fun j hj => ?_, fun j hj => by rw [(hMetaMem (hTagM0 j hj) (Or.inr (Or.inl rfl))).1,
        hLvlM0 j hj, hChain', hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1],
      fun j hj => (hMetaMem (hTagM0 j hj) (Or.inr (Or.inl rfl))).2,
      fun j hj => (hOldTag (by rw [hTagMeta0 j hj]; omega)).trans (hTagMeta0 j hj), fun j hj => ?_⟩
    · by_cases hle : j ≤ i0
      · dsimp only [tok']; rw [(hCores5 j hj).1 hle]; exact Or.inl (hCoreOwn0 j hj)
      · obtain ⟨hlo, hhi⟩ := (hCores5 j hj).2.2.1 (by omega)
        dsimp only [tok']; exact Or.inr ⟨hlo, lt_of_le_of_lt hhi (by dsimp [heap0, editsBuf] at hNextGe0; omega)⟩
    · obtain ⟨hDG5, hLen5, hLe5, hGt5⟩ := hMeta5 j hj
      have hLP11 : s11.mem (levelMeta + j) = s5.mem (levelMeta + j) := hTag22 (hTagMeta0 j (by omega))
      have hGP11 : s11.mem (levelMeta + d + j) = s5.mem (levelMeta + d + j) :=
        hTag22 (by have := hTagMeta0 (d + j) (by omega); rwa [show levelMeta + (d + j) = levelMeta + d + j by omega] at this)
      by_cases hle : j ≤ i0
      · obtain ⟨hDG0, hLen0, hOwn0, hTagL0, hTagG0⟩ := SolverLevelMetaAt.atCaps hMeta0Full hCaps0 j hj
        obtain ⟨hL0Eq, hG0Eq⟩ := hLe5 hle
        have hGKind : (if j = 0 then 20 else 23 + d) = 20 ∨ (if j = 0 then 20 else 23 + d) = 21 + d ∨
            (if j = 0 then 20 else 23 + d) = 23 + d := by split_ifs <;> simp
        refine ⟨?_, ?_, by rw [hLP11, hL0Eq]; exact Or.inl hOwn0,
          fun a ha1 ha2 => by rw [hLP11, hL0Eq] at ha1 ha2; exact (hMetaMem (hTagL0 a ha1 ha2) (Or.inr (Or.inr rfl))).2,
          fun a ha1 ha2 => by rw [hGP11, hG0Eq] at ha1 ha2; exact (hMetaMem (hTagG0 a ha1 ha2) hGKind).2⟩
        · rw [hGP11, hG0Eq, hChain', hEx.1 j hle]
          exact dynGraphAt_of_agree hDG0 (fun a ha1 ha2 => (hMetaMem (hTagG0 a ha1 ha2) hGKind).1)
        · rw [hLP11, hL0Eq, hChain', hEx.1 j hle, shiftDeep_chainLen_le model.chain hiLt j hle]
          exact hLen0.congr (fun e he t ht => by
            have heLt := hDG0.2.2.1 e he
            have hmul : e * L + L ≤ eCap * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
            exact (hMetaMem (hTagL0 _ (by omega) (by omega)) (Or.inr (Or.inr rfl))).1)
      · obtain ⟨hLLo, hLHi, hGLo, hGHi, hDisjL, hDisjG⟩ := hGt5 (by omega)
        have hTag23 (a : ℕ) (hlo : heap ≤ a) (hhi : a < s5.regs 4)
            (hnT : ¬ Rterm'.foot newTermH newTermTok a)
            (hnC : ∀ r < d, ¬ Rcore.foot (newCoreHandle r) (newCoreTok r) a) : tok'.tag a = 23 + d := by
          have hnotTree : ¬ (tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L) :=
            fun h => by rcases hTreeFootNotMid a h with h0 | ⟨hlo', _⟩ <;> omega
          have hnotCore : ¬ ∃ r : Fin d, i0 ≤ r.val ∧ Rcore.foot (newCoreHandle r.val) (newCoreTok r.val) a :=
            fun ⟨r, _, hfr⟩ => hnC r.val r.isLt hfr
          dsimp only [tok']
          simp only [show ¬ a < heap by omega, ↓reduceIte, ↓reduceDIte, hnotTree,
            show ¬ (s5.regs 4 ≤ a ∧ a < nextHeap) by omega, hnT, hnotCore, hhi]
        dsimp only [levelMeta, lvlMTable, n0Cell, d] at hLLo hLHi hGLo hGHi hDisjL hDisjG hLP11 hGP11 hDG5 hLen5 ⊢
        refine ⟨hGP11.symm ▸ dynGraphAt_of_agree hDG5 (fun a ha1 ha2 => h11_eq_s5_geHeap a (by omega) (by omega)),
          hLP11.symm ▸ hLen5.congr (fun e he t ht => by
            have heLt := hDG5.2.2.1 e he
            have hmul : e * L + L ≤ eCap * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
            exact h11_eq_s5_geHeap _ (by omega) (by omega)),
          by rw [hLP11]; exact Or.inr ⟨hLLo, lt_of_le_of_lt (le_trans (Nat.le_add_right _ (eCap * L)) hLHi)
            (by dsimp only [heap0, editsBuf] at hNextGe0; omega)⟩,
          fun a ha1 ha2 => by
            rw [hLP11] at ha1 ha2; exact hTag23 a (by omega) (by omega) (hDisjL a ha1 ha2).1 (hDisjL a ha1 ha2).2,
          fun a ha1 ha2 => by
            rw [hGP11] at ha1 ha2; rw [ite_eq_right (by omega)]
            exact hTag23 a (by omega) (by omega) (hDisjG a ha1 ha2).1 (hDisjG a ha1 ha2).2⟩
  -- Final bounds, frame, footprint, and amortized cost
  have hNextLe : nextHeap ≤ heap + deepSpace := by
    have h1 : 2 * edits.length + edits.length * wireTreeSyncEditSpace L =
        edits.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits.length * (2 + wireTreeSyncEditSpace L) ≤
        forestEdgeCap * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEditsLeCap
    dsimp [heap0, editsBuf] at hNextLe0; omega
  have hPhiCores11 :
      (∑ j : Fin d, Rcore.phi (newCoreHandle j.val) (newCoreTok j.val) s11.mem) =
      (∑ j : Fin d, Rcore.phi (newCoreHandle j.val) (newCoreTok j.val) s5.mem) :=
    Finset.sum_congr rfl (fun j _ => (hCores11 j.val j.isLt).2.2.2)
  have hSelPtrs11 :
      s11.mem (solverSelectHeapAddr tok.table d) = mem0 (solverSelectHeapAddr tok.table d) ∧
      s11.mem (solverSelectBlocksAddr tok.table d) = mem0 (solverSelectBlocksAddr tok.table d) :=
    ⟨h11_fixed hTagSH (by simp [d]), h11_fixed hTagSB (by simp [d])⟩
  refine ⟨nextHeap, _, s11, tok', rAll, by dsimp [heap0, editsBuf] at hNextGe0; omega, hNextLe,
    rfl, rfl, rfl, rfl, hSelPtrs11.1, hSelPtrs11.2, hRepEnd, hMetaCapsEnd.meta_caps.1,
    hMetaCapsEnd.meta_caps.2, fun hLay0 => hLay0.of_shiftDeep hOwnOfTag (fun _ h => hFootLt _ (Or.inl h))
      hMeta0Full hCaps0 rfl rfl (fun _ ht => h11_eq_s5 _ (by have := htagLt (by rw [ht]; omega); omega)
        (fun h => by rw [h, hT1 11 (by omega)] at ht; omega) (by rw [ht]; omega) (by rw [ht]; omega)
        (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega))
      (fun j hle hj => (hMeta5 j hj).2.2.1 hle) (fun j hgt hj => ⟨((hMeta5 j hj).2.2.2 hgt).2.2.1, hMetaOrd5.1 j hgt hj⟩)
      hMetaOrd5.2, hNumEnd, hOffInvEnd, hOffBdEnd, hzNext, ?_, ?_, ?_⟩
  · -- Frame below `heap` outside `Rrep.foot root tok`
    intro a ha hnf
    have htag0 : tok.tag a = 0 := by by_contra hne; exact hnf (Or.inl (hOwnOfTag a hne))
    have hne11 : a ≠ root + 11 := fun h => by rw [h, hT1 11 (by omega)] at htag0; omega
    exact (h11_eq_s5 a (by omega) hne11 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans (hFrame5 a ha (by omega) (by omega) (fun _ _ _ => by omega))
  · intro a ha
    rcases ha with (h0 | hnew) | hft | ⟨j, hj, hcore⟩
    · exact Or.inl (Or.inl h0)
    · exact Or.inr hnew
    · rcases hFootEnd a hft with h0 | ⟨hlo, hhi⟩
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inr ⟨by dsimp only [heap0, editsBuf] at hlo; omega, hhi⟩
    · rcases (hCores5 j hj).2.2.2.2.2.2 a hcore with ⟨_, h0⟩ | ⟨hlo, hhi⟩
      · exact Or.inl (Or.inr (Or.inr ⟨j, hj, h0⟩))
      · exact Or.inr ⟨hlo, lt_of_lt_of_le hhi (by dsimp [heap0, editsBuf] at hNextGe0; omega)⟩
  · change _ + (Rtree.phi tok.treeHeap curTreeTok' s11.mem +
        (∑ j : Fin d, Rcore.phi (newCoreHandle j.val) (newCoreTok j.val) s11.mem) + curOffCnt' * drainUnit) ≤
      deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        (wireTreeSyncEditCost L drainUnit + 2) * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        (Rtree.phi tok.treeHeap tok.treeTok mem0 +
          (∑ j : Fin d, Rcore.phi (tok.coreHandle j.val) (tok.coreTok j.val) mem0) + tok.offReadyCount * drainUnit)
    rw [hPhiCores11, ← hEditsLenEq, hTreePhi10_eq]; dsimp only [Rtree] at hcLoop ⊢
    have hmul : edits.length * (wireTreeSyncEditCost L drainUnit + 2) =
        (wireTreeSyncEditCost L drainUnit + 2) * edits.length := Nat.mul_comm _ _
    have hPackCost : cPack ≤
        85 * (graphListEdgeSum (chainSuffixForests model.chain i0) +
          graphListEdgeSum (chainSuffixForests model'.chain i0)) + 210 * (d + 1) + 120 := by
      have hcntLe : cnt ≤ d + 1 := by dsimp only [cnt]; omega
      dsimp only [d, i0, model', cnt] at hcPack hcntLe ⊢; omega
    clear hRepEnd hMetaCapsEnd hAccountsEnd hOrientEnd hOffInvEnd hOffBdEnd hCores11 hTerm11 hInvInit
      rAll rTail rLoop rSetup r8 r7 r6 r04a hRep0Full hMeta0Full hModelInvFull
    dsimp only [d, i0, model'] at hCost5 hPackCost hcLoop hcSetup hmul ⊢; omega

end MinCostFlow.MinRatio
