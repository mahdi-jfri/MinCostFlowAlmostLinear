module

public import MinCostFlow.MinRatio.WireChainCoreBranchAEnvKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchATokKFBL
import WordRAM.Tactic

/-!
# The run of all of Branch A (`WireChainCoreBranchAAllKFBL`)

This file runs Branch A (`wireBranchAKFBL`) from the state after Phase 0. It chains the run
lemmas of the parts: Steps 0–2 (`wireBranchASteps0To2KFBL_runs`), Step 3
(`wireBranchAStep3KFBL_runs`), Step 4 (`wireBranchAStep4KFBL_runs`), the second tree sync
(`wireBranchASync2LoopKFBL_runs`) and Step 5b (`wireBranchAReadyAndTokKFBL_runs`). Each part
takes the facts that the part before it gives. The model facts that the parts need come from
the premises of `OrdChainUpdateCoreSpecWExtKFBL` and from the rebuild test at level `0`.

The heap bounds of the parts sum to at most `coreSpace` (by `spaceTotalBranchA`). The costs of
the parts sum to at most the left side of `costTotalBranchA`, plus the potential of the old
token, with `1000` steps to spare for Phase 0 and the rebuild test. The only result used later is
`wireBranchAKFBL_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The heap bounds of the parts of Branch A: each part has room, and the end lies within
`coreSpace`. The later bounds are implications, since the later heap pointers are only known
after the earlier parts run. -/
private theorem branchA_space_arith {w heap d heap1 heapSync heap2 iC iCM sO sN fEC W L uL wR cl
    vC eC sLS lS cs : ℕ}
    (h1 : heap1 ≤ heap + 1 + 12 * d + 3 * (d + 1) + 4 + 5 * d)
    (h2 : heapSync ≤ heap1 + 3 * iC + sO * (2 + W))
    (h3 : heap2 ≤ heapSync + 3 * L + uL * wR)
    (hS : (1 + 12 * d) + 3 * (d + 1) + 4 + d * 5 + (3 * iCM + fEC * (2 + W)) +
      (3 * L + uL * wR) + 2 * iCM + cl + (1 + 4 * vC + 2 * eC) + sLS + lS + 5 * d +
      (3 * iCM + fEC * (2 + W)) + 1 ≤ cs)
    (hIC : iC ≤ iCM) (hF : sO + sN ≤ fEC) (hRoom : heap + cs < 2 ^ w) :
    heap2 + 2 * iC + cl + (1 + 4 * vC + 2 * eC) < 2 ^ w ∧
    (∀ heap3, heap3 ≤ heap2 + 2 * iC + cl + (1 + 4 * vC + 2 * eC) →
      heap3 + sLS + lS + 5 * d < 2 ^ w ∧
      ∀ heap4, heap4 ≤ heap3 + sLS + lS + 5 * d →
        heap4 + (3 * iC + sN * (2 + W)) < 2 ^ w ∧
        ∀ nextHeap, nextHeap ≤ heap4 + (3 * iC + sN * (2 + W)) →
          nextHeap + 1 ≤ heap + cs ∧ nextHeap + 1 < 2 ^ w) := by
  have hO := Nat.mul_le_mul_right (2 + W) (show sO ≤ fEC by omega)
  have hN := Nat.mul_le_mul_right (2 + W) (show sN ≤ fEC by omega)
  refine ⟨by omega, fun heap3 h4 => ⟨by omega, fun heap4 h5 => ⟨by omega, fun nextHeap h6 =>
    ⟨by omega, by omega⟩⟩⟩⟩

/-- The costs of the parts of Branch A sum to at most the left side of `costTotalBranchA`, plus
the old potential, with `1000` steps to spare for Phase 0 and the rebuild test. The tree
potentials of the parts cancel in the sum. -/
private theorem branchA_cost_arith {c02 c3 c4 cS cR t0 t2 t3 t4 t5 o sc0 pc4 pE phi0 d R sO X
    iC uL Y L m cl cl' eC vC sLC lM sN mN dU : ℕ}
    (h02 : c02 + t2 ≤ d * (R + 48) + (230 * (d + 1) + 85 * sO + 300) + sO * (X + 2) +
      (15 * iC + 30) + (uL * (Y + 120) + 71 * L + 210) + (670 * (4 * uL + 1) + 30) +
      (uL * (17 * L + 70) + 80) + 70 + (t0 + o + sc0))
    (h3 : c3 ≤ (70 * iC + 40 * m + 80) + cl + (150 * eC + 60 * vC + 120) + 165)
    (hp3 : t3 = t2)
    (h4 : c4 + pc4 ≤ sLC + lM + d * (R + 68) + 15 * d + 270)
    (hp4 : t4 = t3)
    (hS : cS + t5 ≤ (230 * (d + 1) + 85 * sN + 260) + sN * (X + 2) + 20 + t4)
    (hR : cR + pE ≤ (80 * mN + mN * dU + 120) + (t5 + pc4))
    (hcl : cl' = cl) (hphi : phi0 = t0 + sc0 + o) :
    c02 + (c3 + (c4 + (cS + cR + 1) + 1) + 1) + 1 + pE + 1000 ≤
      d * (R + 48) + (230 * (d + 1) + 85 * sO + 300) + sO * (X + 2) +
      (uL * (Y + 120) + 71 * L + 220) + (670 * (4 * uL + 1) + 30) +
      (uL * (17 * L + 70) + 80) + (85 * iC + 40 * m + 110) + cl' +
      (150 * eC + 60 * vC + 120) + 150 + sLC + lM + d * (R + 48) + 40 * d +
      (230 * (d + 1) + 85 * sN + 260) + sN * (X + 2) + (80 * mN + mN * dU + 120) + 1500 +
      phi0 := by
  have : d * (R + 68) = d * (R + 48) + 20 * d := by ring
  omega

set_option maxHeartbeats 1600000 in
/-- The run of all of Branch A from the state `st` after Phase 0, when the rebuild test fires at
level `0`. It returns `nextHeap` within `coreSpace` of `heap`, with every Branch A
postcondition of `OrdChainUpdateCoreSpecWExtKFBL` at the new token. Its cost plus `1000` (room
for Phase 0 and the rebuild test) is at most the left side of `costTotalBranchA` plus the old
potential. -/
theorem wireBranchAKFBL_runs
    {w L P m V psi k epsExp drainUnit capExp capLimit fcap lastMul intCapMax forestEdgeCap edMul
      mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc root uIntBuf editsPtr g l heap : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    {stepCap : ℕ → ℕ → ℕ}
    (E : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    (hIntCapMax : tok.intCap ≤ intCapMax)
    (hForestCap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hTrNfLe :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.1 ≤ tok.intCap)
    (hBatchMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      IPM.Machine.BatchAt mem uIntBuf tr.2.2.2.2)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf))
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr) (hEdLeHeap : editsPtr ≤ heap)
    (hz0 : ZeroFrom mem heap) (hRoom : heap + coreSpace U.length < 2 ^ w)
    (hOver :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length)
    (hStMem : st.mem = mem)
    (hRegs :
      let d := cfg.P.d
      let cnt := d + 1
      let arrBase := heap + 1 + 12 * d
      let handleBase := tok.handle + 18
      st.regs 4 = arrBase + 3 * cnt + 4 ∧ st.regs 70 = root ∧ st.regs 71 = 0 ∧
      st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = d ∧ st.regs 76 = cfg.P.k ∧
      st.regs 77 = handleBase ∧ st.regs 78 = handleBase + cnt ∧ st.regs 79 = cnt ∧
      st.regs 80 = arrBase ∧ st.regs 81 = arrBase + cnt ∧
      st.regs 82 = solverLvlMAddr tok.table d ∧ st.regs 83 = solverLevelMetaAddr tok.table d ∧
      st.regs 85 = tok.levelsEnd + 3 * cnt ∧ st.regs 86 = tok.levelsEnd + 2 * cnt ∧
      st.regs 87 = uIntBuf ∧ st.regs 90 = g ∧ st.regs 91 = l ∧
      st.regs 92 = arrBase + 2 * cnt ∧ st.regs 93 = arrBase + 3 * cnt ∧
      st.regs 94 = L ∧ st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2)) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let d := cfg.P.d
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let n := model.extG.n
    let mNew := (modelPre.chain.G 0).m
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
    ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore)
      (levelU levelUS : ℕ → List Update) (diffLists : ℕ → LevelDiffLists),
      Runs w p ω (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
          isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        st (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧ tok'.rootECap = tok.rootECap ∧
      tok'.table = tok.table ∧
      Rrep.rep root modelPre tok' out.mem ∧
      SolverLevelMetaAt P V modelPre tok' out.mem ∧
      SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
      out.mem (solverLevelMetaAddr tok'.table d + d) = tok'.rootGraph ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      OffTreeRecInv modelPre L out.mem tok'.edgeRecords B ∧
      OffTreeRecBound modelPre L out.mem tok'.edgeRecords B ∧
      out.mem (solverSelectHeapAddr tok.table d) = mem0 (solverSelectHeapAddr tok.table d) ∧
      out.mem (solverSelectBlocksAddr tok.table d) = mem0 (solverSelectBlocksAddr tok.table d) ∧
      UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn (Rrep.foot root tok') out.mem heap
        nextHeap 0 model.chain modelPre.chain levelU levelUS diffLists ∧
      ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
      cost + Rrep.phi root tok' out.mem + 1000 ≤
        d * (Psc.readout + 48) +
          (230 * (d + 1) + 85 * sumOld + 300) +
          sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
          (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
          (670 * (4 * U.length + 1) + 30) +
          (U.length * (17 * L + 70) + 80) +
          (85 * tok.intCap + 40 * m + 110) +
          wireCompactLevel0Cost n tok.rootECap tok.intCap L mNew +
          (150 * tok.rootECap + 60 * n + 120) + 150 +
          (Finset.range d).sum (fun j => levelCost modelPre.chain j + 9) +
          lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) +
          d * (Psc.readout + 48) + 40 * d +
          (230 * (d + 1) + 85 * sumNew + 260) +
          sumNew * (wireTreeSyncEditCost L drainUnit + 2) +
          (80 * mNew + mNew * drainUnit + 120) + 1500 +
        Rrep.phi root tok mem0 ∧
      SolverLevelMetaDisjAt vCap eCap tok' out.mem := by
  classical
  dsimp only
  have hModelInv_keep := hModelInv
  obtain ⟨⟨hdPos, hmPos⟩, ⟨hN0Eq, hExtNLe, hRootCapLe⟩, _, _, _, _, _, _,
    ⟨hLMd0Eq, _, _, _, _, hLoop⟩, _, hG0'Cap, hG0'mLeR, hG0'mLeI, _, hNewForest, _, hNewSub,
    _, _, _⟩ := hModelInv
  have hRootG0 := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hT2 := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hvCapEq, heCapEq⟩ : vCap = model.extG.n ∧ eCap = tok.rootECap := by
    have hCap0 := hCaps0 0 hdPos; rw [hLMd0Eq] at hCap0; exact dynGraphAt_caps_eq hCap0 hRootG0
  subst hvCapEq heCapEq
  obtain ⟨hr4, hr70, hr71, hr72, hr73, hr75, hr76, hr77, hr78, hr79, hr80, hr81, hr82, hr83,
    hr85, hr86, hr87, hr90, hr91, hr92, hr93, hr94, hr95, hr98⟩ := hRegs
  obtain ⟨hChPreEq, hRenTrue⟩ := branchA_modelPre_chain_eq model U
    (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
    (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) hdPos hN0Eq hOver
  have hRebInv0 := updateLoopModelInv_rebuild_zero hdPos hLoop hOver
  have hULeHeap : uIntBuf ≤ heap := by omega
  -- Steps 0–2
  obtain ⟨s2, c02, heap1, heapSync, heap2, curTree1, curTrees1, curFree1, curDepth1,
    curTreeTok1, newCanonVal, r02, -, -, hH1Lo, hH1Hi, hSyncLo, hSyncHi, hH2Lo, hH2Hi, hr4_2,
    hz2, hRegs2, hHeap0_2, hEmpty2, hEmptyG2, hTreeN1, hLct1, hNum1, hNamed1, _, hTreeRep1,
    hTreeFoot1, hSlots2, hRootG2, hLen0_2, hFr2, hCanon2, hOffDisj2, hThrOffDisj2, hc02⟩ :=
    wireBranchASteps0To2KFBL_runs (opTree := opTree) (opCore := opCore) (ω := ω)
      E.coreLocal E.four E.lPos E.pW E.dW E.kW E.w18 E.packP E.refAccP E.refOneP E.updLen0P
      E.treeImpl E.bindC E.canonC E.isNegC E.shiftC E.divC E.addC E.subC E.negC E.copyC
      (E.dgApplyC _ _ _) E.coreImpl E.ops hRep0 hMeta0 hCaps0 hNum0 hOffInv0 hOffBd0
      hModelInv_keep hModelInvKFBL hIntCapMax hForestCap hLogW hCapT hMemEq hFreshMem hTrNfLe
      hBatchMem hSmallMem hRef hFootLt hGLt hLLt hULeEd hEdLeHeap hStMem hz0
      ⟨hr4, hr70, hr71, hr72, hr73, hr75, hr77, hr78, hr79, hr80, hr83, hr87, hr90, hr91, hr92,
        hr93, hr94⟩ hRoom
  -- Step 3
  have hSpace := E.ops.spaceTotalBranchA model.extG.n tok.rootECap U.length
    ((model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m
    hExtNLe (hRootCapLe.trans hIntCapMax)
    (hG0'mLeI.trans hIntCapMax)
  obtain ⟨hRoom3, hRoomLater⟩ :=
    branchA_space_arith hH1Hi hSyncHi hH2Hi hSpace hIntCapMax hForestCap hRoom
  obtain ⟨s3, c3, newLen0, newRootGraph, ordPtr0, heap3, r3, hc3, hNL0Lo, hNRGLo, hOrdLo, hH3Lo,
    hH3Hi, hr4_3, hr28_3, hr29_3, hr30_3, hz3, hRegs3, hHeap0_3, hEmpty3, hEmptyG3, hFresh3,
    hR14_3, hR11_3, hLM0_3, hLMd_3, hRG3, hLen3, hOrd3, hOrdW3, hSlots3, hZeroIn3, hOffInv3,
    hTreeRep3, hPhi3, hCanon3, hOffDisj3, hThrOffDisj3, hFr3⟩ :=
    wireBranchAStep3KFBL_runs (ω := ω) hdPos hmPos E.lPos E.eCapPos E.w18 rfl rfl E.renP
      E.compP E.sortP E.copyC (fun vL eT => E.dgInitC _ vL eT) hRep0 hMeta0 hCaps0 hG0'Cap hRef
      hMemEq hFreshMem hFootLt hULeHeap ⟨hH1Lo, hSyncLo, hH2Lo⟩
      ⟨hr4_2, (hRegs2 70 (by omega)).trans hr70, (hRegs2 73 (by omega)).trans hr73,
        (hRegs2 75 (by omega)).trans hr75, (hRegs2 83 (by omega)).trans hr83⟩
      hz2 hHeap0_2 hEmpty2 hEmptyG2 hTreeRep1 hTreeFoot1 hSlots2 hRootG2 hLen0_2 hFr2 hCanon2
      hOffDisj2 hThrOffDisj2
      hRoom3
  -- Step 4
  have hR3 : ∀ r, 70 ≤ r → s3.regs r = st.regs r :=
    fun r hr => (hRegs3 r hr).trans (hRegs2 r hr)
  obtain ⟨hRoom4, hRoomLater4⟩ := hRoomLater heap3 hH3Hi
  obtain ⟨s4, c4, heap4, termTok4, coreTok4, r4, hH4Lo, hH4Hi, hr4_4, hz4, hRegs4, hHeap0_4,
    hEmpty4, hEmptyG4, hNewF4, hFresh4, hR14_4, hR11_4, hLM0_4, hLMd_4, hRG4, hLen4, hSlots4,
    hZeroIn4, hOffInv4, hTreeRep4, hPhi4, hCanon4, hOffDisj4, hThrOffDisj4, hCores4,
    hCoreDisj4, hMeta4, hTermB4, _, hTermRep4, hTermFoot4, hRc4, hUc4, hFr4, hFr4_0, hc4,
    hMetaOrd4⟩ :=
    wireBranchAStep4KFBL_runs (ω := ω) (opLast := opLast) E.coreLocal E.four E.prec E.width
      E.lW E.pW E.depthW hdPos E.dW E.kPos E.kW E.nW E.w18 E.capLim rfl rfl hN0Eq E.initOrdEq
      E.wordExpEq E.coreLenP E.edgeP E.signC E.mulC E.intDivC E.copyC E.coreImpl E.lastImpl
      E.ops hRep0 hMeta0 hRef hChPreEq hRebInv0 hModelInvKFBL ⟨hG0'mLeR, hG0'mLeI⟩ hMemEq hFootLt
      hULeHeap ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hOrdLo, hH3Lo⟩
      ⟨hr4_3, hr28_3, hr29_3, hr30_3, (hR3 71 (by omega)).trans hr71,
        (hR3 72 (by omega)).trans hr72, (hR3 75 (by omega)).trans hr75,
        (hR3 76 (by omega)).trans hr76, (hR3 77 (by omega)).trans hr77,
        (hR3 78 (by omega)).trans hr78, (hR3 81 (by omega)).trans hr81,
        (hR3 82 (by omega)).trans hr82, (hR3 83 (by omega)).trans hr83,
        (hR3 85 (by omega)).trans hr85, (hR3 86 (by omega)).trans hr86,
        (hR3 94 (by omega)).trans hr94, (hR3 95 (by omega)).trans hr95,
        (hR3 98 (by omega)).trans hr98⟩
      hz3 hHeap0_3 hEmpty3 hEmptyG3 hFresh3 hR14_3 hR11_3 hLM0_3 hLMd_3 hRG3 hLen3 hOrd3 hOrdW3
      hSlots3 hZeroIn3 hOffInv3 hTreeRep3 hTreeFoot1 hCanon3 hOffDisj3 hThrOffDisj3 hFr3 hRoom4
      (tok.coreTok 0)
  -- the second tree sync
  have hR4 : ∀ r, 70 ≤ r → s4.regs r = st.regs r :=
    fun r hr => (hRegs4 r hr).trans (hR3 r hr)
  obtain ⟨hRoomS, hRoomEnd⟩ := hRoomLater4 heap4 hH4Hi
  obtain ⟨s5g, cS, nextHeap, curTree2, curTrees2, curFree2, curDepth2, curTreeTok2, rS, hr3_5,
    hr70_5, hNextLo, hNextHi, hz5, hTreeN2, hLct2, hNum2, hNamed2, hLive2, hTreeRep2, hFoot2,
    hSlotThr2, hOffSlot2, hOffRec2, hOffDisj5, hR11_5, hOffReady5, hFr5, hcS⟩ :=
    wireBranchASync2LoopKFBL_runs (ω := ω) (opTree := opTree) E.packP E.four hdPos E.w18 rfl rfl
      E.treeImpl E.bindC E.canonC E.isNegC hRep0 hRef hChPreEq hRenTrue hNewForest hNewSub
      ⟨hG0'mLeR, hG0'mLeI⟩ hLogW hCapT hFootLt hULeHeap
      ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, by omega, hH4Lo⟩
      ⟨hr4_4, (hR4 70 (by omega)).trans hr70, (hR4 73 (by omega)).trans hr73,
        (hR4 79 (by omega)).trans hr79, (hR4 81 (by omega)).trans hr81,
        (hR4 92 (by omega)).trans hr92⟩
      hz4 hEmpty4 hEmptyG4 hNewF4 hR14_4 hR11_4 hRG4 hSlots4 hZeroIn4 hOffInv4 hTreeN1 hLct1
      hNum1 (treeEditNamedSlots_empty_noEdge hNamed1) hTreeRep4 hTreeFoot1 hCanon4 hOffDisj4
      (fun j hj h11 h14 => branchA_frame0_root hRep0 hFootLt hFr4_0 j hj h11 h14)
      (fun j hj => branchA_frame0_tag hRep0 hFootLt hFr4_0 (hT2 j hj) (by decide) (by omega)
        (by omega) (fun _ _ => by omega))
      hRoomS
  obtain ⟨hNextRoom1, hNextRoom2⟩ := hRoomEnd nextHeap hNextHi
  -- the facts that Step 5b starts from
  have hI2E0 := (solverStateRep_intCap hRep0).2.2
  have H : WireBranchATokHypKFBL w L P m V psi k epsExp drainUnit model.extG.n tok.rootECap root
      uIntBuf heap heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap termTok4 cfg
      Rcore mem0 mem s4 s5g model tok U B R
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)
      curTree2 curTrees2 curFree2 curDepth2 curTreeTok1 curTreeTok2 newCanonVal coreTok4 :=
    { coreLocal := E.coreLocal, lpos := E.lPos, dPos := hdPos, w18 := E.w18, vCapEq := rfl,
      eCapEq := rfl, rep0 := hRep0, meta0 := hMeta0, ref := hRef, chPreEq := hChPreEq,
      renTrue := hRenTrue, newForest := hNewForest, newSub := hNewSub,
      g0'mLeR := ⟨hG0'mLeR, hG0'mLeI⟩,
      i2eGe := fun j hj => ((translateBatch_i2e_ge model.extG model.extToInt model.intToExt
        model.nextFresh U).2 j (le_trans hTrNfLe hj)).trans (hI2E0 j hj),
      footLt := hFootLt, uLeHeap := hULeHeap,
      heaps := ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, by omega, hH4Lo, hNextLo, hNextRoom2⟩,
      heap0_4 := hHeap0_4, fresh4 := hFresh4, r14_4 := hR14_4, lm0_4 := hLM0_4,
      lmd_4 := hLMd_4, rg4 := hRG4, len4 := hLen4, treeFoot1 := hTreeFoot1, canon4 := hCanon4,
      thrOffDisj4 := hThrOffDisj4, cores4 := hCores4, coreDisj4 := hCoreDisj4,
      meta4 := hMeta4, termB4 := hTermB4, termRep4 := hTermRep4, termFoot4 := hTermFoot4,
      rc4 := hRc4, uc4 := hUc4, frame4 := hFr4, frame4_0 := hFr4_0, r3_5g := hr3_5,
      r70_5g := hr70_5, z5g := hz5, treeN2 := hTreeN2, lctEnd := hLct2, numEnd := hNum2,
      namedEnd := hNamed2, liveEnd := hLive2, treeRepEnd := hTreeRep2, footEnd := hFoot2,
      slotThrEnd := hSlotThr2, offSlotEnd := hOffSlot2, offRecEnd := hOffRec2,
      offDisjEnd := hOffDisj5, r11_5g := hR11_5, offReady5g := hOffReady5, frame5g := hFr5,
      metaOrd4 := hMetaOrd4 }
  -- Step 5b
  obtain ⟨cR, out, tok', levelU, levelUS, diffLists, rR, hLE, hIC, hRE, hTab, hRepEnd,
    hMetaEnd, hCapsEnd, hLmd, hNumEnd, hOffInvEnd, hOffBdEnd, hSH, hSB, hSel, hZ, hFrame, hFoot,
    hcR, hMetaDisj⟩ :=
    wireBranchAReadyAndTokKFBL_runs (ω := ω) (reembFn := reembFn) (capExp := capExp) H
      E.rebuildP E.isNegC
  have rS5 : Runs w p ω (wireBranchASync2AndReadyStmt packEditsProc (opTree 4) (opTree 1)
      (opTree 0) bind canonCopy isNeg rebuildOffReadyProc) s4 (.returned (nextHeap + 1)) out
      (cS + cR + 1) := runs_seq_iff.mpr (Or.inr ⟨s5g, cS, cR, rS, rR, rfl⟩)
  have r45 := runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4, rS5, rfl⟩)
  have r35 := runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3, r45, rfl⟩)
  have r05 := runs_seq_iff.mpr (Or.inr ⟨s2, c02, _, r02, r35, rfl⟩)
  have hPhi0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem0 =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem0 +
        (Finset.range cfg.P.d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) +
        tok.offReadyCount * drainUnit := by
    show _ + _ + _ = _
    rw [Fin.sum_univ_eq_sum_range (fun i => Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem0)]
  have hPreG0m := H.preG0m
  refine ⟨nextHeap + 1, c02 + (c3 + (c4 + (cS + cR + 1) + 1) + 1) + 1, out, tok', levelU,
    levelUS, diffLists, r05, by omega, hNextRoom1, hLE, hIC, hRE, hTab, hRepEnd, hMetaEnd,
    hCapsEnd, hLmd, hNumEnd, hOffInvEnd, hOffBdEnd, hSH, hSB, hSel, hZ, hFrame, hFoot, ?_,
    hMetaDisj⟩
  exact branchA_cost_arith hc02 hc3 hPhi3 hc4 hPhi4 hcS hcR
    (congrArg (wireCompactLevel0Cost model.extG.n tok.rootECap tok.intCap L) hPreG0m) hPhi0

end MinCostFlow.MinRatio
