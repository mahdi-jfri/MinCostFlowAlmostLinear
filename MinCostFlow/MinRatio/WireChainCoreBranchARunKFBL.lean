module

public import MinCostFlow.MinRatio.WireChainCoreBranchAPrefixRunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchASuffixKFBL
import WordRAM.Tactic

/-!
# Branch A Step 4 execution under `KFBL` (`WireChainCoreBranchARunKFBL`)

Executes Step 4 (`wireBranchASuffixStmtKFBL`) starting from state `s3` produced by
`wireBranchAStep3KFBL_runs`, lifting all Branch A invariants (`FreshTablesAt`, `root+14`,
`root+11`, `levelMeta`, `DynGraphAt`, `EdgeValuesAt`, `slots`, `inOffReady`, `OffReadyInv`,
`Rtree.rep`, compacted `edgeThresholds`/`edgeRecords`, and frame bounds) cleanly to `s4`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 800000 in
/-- Execute Branch A Step 4 (`s3 → s4`): increment `rebuildCount[0]`, rebuild levels `0 .. d`
with uniform caps `(vCap, eCap)`, zero `updCount[0 .. d - 1]`, collect `newPtrs[0 .. d]`, and lift
all Step 3 invariants to `s4`. -/
theorem wireBranchAStep4KFBL_runs
    {w L P m V psi k epsExp drainUnit capExp capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap
      initCore coreLenProc edgeProc signExt mul intDiv copy lastInit
      root uIntBuf heap heap1 heapSync heap2 newLen0 newRootGraph ordPtr0 heap3 : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {s3 : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {gVec lVec : ℕ → ℝ}
    {curTree1 : PathTreeState}
    {curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {newCanonVal : ℕ → PathEdgeValue}
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w)
    (hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (hdW : cfg.P.d < 2 ^ w) (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w)
    (hNW : cfg.N₀ < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hCapLim : vCap + eCap + 2 ≤ capLimit)
    (hvCapEq : vCap = model.extG.n) (heCapEq : eCap = tok.rootECap)
    (hN0Eq : model.chain.N₀ = cfg.N₀)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T) (hWordExpEq : Psc.wordExp = wordExp)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hCoreImpl : UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hLastImpl : ∀ H : MGraph,
      H.m ≤ m → H.m ≤ levelM cfg.TP cfg.P cfg.P.d → H.n ≤ H.m + 1 →
      (∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision H.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L H vCap eCap lastMul stretchPrec lastAlloc))
    {stepCap : ℕ → ℕ → ℕ}
    (hOps : UpdateCoreOpsHypKFBL (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (capLimit := capLimit) (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (drainUnit := drainUnit) (edMul := edMul)
      (mThresh := mThresh) (coreSpace := coreSpace) (coreFixed := coreFixed) (toolMul := toolMul)
      (fmt := fmt) (cfg := cfg) (G := G) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) levelSpace levelCost updStepSpace lastSpace termUpdSpace stepCap)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hRef : RefreshBatch model.extG U)
    (hChPreEq :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let U_int := tr.2.2.2.2
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch U_int
      let st0 : ChainState cfg.T cfg.P :=
        { model.chain with
          recUpdates := fun j =>
            if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
      let stLG : ChainState cfg.T cfg.P :=
        { st0 with
          ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j))
          g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) }
      (alg2PreResetState cfg model U gVec lVec).chain =
        (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 G0'.compact (G0.batchEnc U_int)).1)
    (hRebInv0 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let U_int := tr.2.2.2.2
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch U_int
      let st0 : ChainState cfg.T cfg.P :=
        { model.chain with
          recUpdates := fun j =>
            if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
      UpdateRebuildModelInv w L P wordExp stretchPrec st0 0 G0'.compact
        (fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j)))
        (fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j))) (G0.batchEnc U_int))
    (hModelInvKFBL : UpdateCoreModelInvKFBL model U gVec lVec)
    (hG0'mLeR :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.rootECap ∧
      ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.intCap)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hULeHeap : uIntBuf ≤ heap)
    (hHeaps :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ heap1 ∧
      heap1 ≤ heapSync ∧ heapSync + 3 * L ≤ heap2 ∧
      heap2 ≤ newLen0 ∧ newLen0 + eCap * L ≤ newRootGraph ∧
      newRootGraph + dynGraphSize vCap eCap ≤ ordPtr0 ∧
      ordPtr0 + (1 + 2 * vCap + 2 * G0'.compact.m) ≤ heap3)
    (hRegs3 :
      let d := cfg.P.d
      let cnt := d + 1
      let arrBase := heap + 1 + 12 * d
      let handleBase := tok.handle + 18
      let branchBase := handleBase + cnt
      let lvlMTable := solverLvlMAddr tok.table d
      let levelMeta := solverLevelMetaAddr tok.table d
      let rebuildCountBase := tok.levelsEnd + 2 * cnt
      let updCountBase := tok.levelsEnd + 3 * cnt
      s3.regs 4 = heap3 ∧ s3.regs 28 = newLen0 ∧ s3.regs 29 = newRootGraph ∧ s3.regs 30 = ordPtr0 ∧
      s3.regs 71 = 0 ∧ s3.regs 72 = heap ∧ s3.regs 75 = d ∧
      s3.regs 76 = cfg.P.k ∧ s3.regs 77 = handleBase ∧ s3.regs 78 = branchBase ∧
      s3.regs 81 = arrBase + cnt ∧ s3.regs 82 = lvlMTable ∧ s3.regs 83 = levelMeta ∧
      s3.regs 85 = updCountBase ∧ s3.regs 86 = rebuildCountBase ∧
      s3.regs 94 = L ∧ s3.regs 95 = P ∧ s3.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2))
    (hz3 : ZeroFrom s3.mem heap3)
    (hHeap0_3 : s3.mem heap = 0)
    (hEmptyPtrs3 : ∀ j < cfg.P.d + 1,
      s3.mem (heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) + j) =
        heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1))
    (hEmptyG3 : ∀ j < 4, s3.mem (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + j) = 0)
    (hFresh3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      FreshTablesAt s3.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        (level0E2I true G0' tr.2.1) (level0I2E true G0' tr.2.2.1) (level0NF true G0' tr.2.2.2.1))
    (hR14_3 : s3.mem (root + 14) = newRootGraph) (hR11_3 : s3.mem (root + 11) = 0)
    (hLM0_3 : s3.mem (solverLevelMetaAddr tok.table cfg.P.d) = newLen0)
    (hLMd_3 : s3.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d) = newRootGraph)
    (hRG3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      DynGraphAt s3.mem newRootGraph vCap eCap ((model.chain.G 0).applyBatch tr.2.2.2.2).compact)
    (hLen3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      EdgeValuesAt s3.mem newLen0 4 L P G0'.compact.E (fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j))))
    (hOrd3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      OrdListAt s3.mem ordPtr0 (sortedEnds G0'.compact) (1 + 2 * vCap + 2 * G0'.compact.m))
    (hOrdW3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      ∀ t < 1 + 2 * vCap + 2 * G0'.compact.m, s3.mem (ordPtr0 + t) < 2 ^ w)
    (hSlots3 : ∀ e < tok.intCap, s3.mem (tok.slots + e) = 0)
    (hZeroIn3 : ∀ e < tok.intCap, s3.mem (tok.inOffReady + e) = 0)
    (hOffInv3 : OffReadyInv s3.mem 0 tok.offReadyList tok.inOffReady tok.intCap)
    (hTreeRep3 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree1 curTreeTok1 s3.mem)
    (hTreeFoot1 : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap1 ≤ a ∧ a < heapSync))
    (hCanon3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch tr.2.2.2.2
      ∀ e ∈ model.extG.E,
        let eiOld := tr.2.1 e
        let eiNew := level0E2I true G0' tr.2.1 e
        let v := newCanonVal eiOld
        eiNew < G0'.m ∧ compactUnrank G0'.E eiNew = eiOld ∧
        PathIntAt s3.mem (s3.mem (tok.edgeThresholds + eiNew)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt s3.mem (s3.mem (tok.edgeRecords + eiNew)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (eiOld ∈ G0.E →
          s3.mem (tok.edgeThresholds + eiNew) = mem0 (tok.edgeThresholds + eiOld) ∧
          ((eiOld ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ s3.mem (tok.edgeRecords + eiNew) ∧
              s3.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, s3.mem (tok.edgeRecords + eiNew) ≤ a →
                a < s3.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
                ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a) ∧
           (eiOld ∉ model.chain.toTreeChain.chainTree.E →
              s3.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + eiOld)))) ∧
        (eiOld ∉ G0.E →
          heapSync + 3 * L ≤ s3.mem (tok.edgeThresholds + eiNew) ∧
          s3.mem (tok.edgeThresholds + eiNew) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ s3.mem (tok.edgeRecords + eiNew) ∧
          s3.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2))
    (hOffDisj3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
        s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁) + (2 + 4 * L) ≤
          s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁))
    (hThrOffDisj3 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch tr.2.2.2.2
      ∀ e₁ ∈ model.extG.E, tr.2.1 e₁ ∉ G0.E → ∀ e₂ ∈ model.extG.E, tr.2.1 e₂ ∉ G0.E →
        s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L ≤
          s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁))
    (hs3_frame : ∀ a < heap + 1 + 12 * cfg.P.d, a ≠ root + 11 → a ≠ root + 14 →
      tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 12 → tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
      tok.tag a ≠ 16 → tok.tag a ≠ 20 → tok.tag a ≠ 22 + cfg.P.d → tok.tag a ≠ 23 + cfg.P.d →
      (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → s3.mem a = mem a)
    (hSufRoom : heap3 + (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d < 2 ^ w)
    (hTok0 : Rcore.τ) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let cnt := d + 1
    let arrBase := heap + 1 + 12 * d
    let newPtrs := arrBase + cnt
    let emptyPtrs := arrBase + 2 * cnt
    let emptyGraphPtr := arrBase + 3 * cnt
    let handleBase := tok.handle + 18
    let branchBase := handleBase + cnt
    let levelMeta := solverLevelMetaAddr tok.table d
    let rebuildCountBase := tok.levelsEnd + 2 * cnt
    let updCountBase := tok.levelsEnd + 3 * cnt
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch tr.2.2.2.2
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∃ (out : State) (cost heap4 termTok : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchASuffixStmtKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        s3 .normal out cost ∧
      heap3 ≤ heap4 ∧ heap4 ≤ heap3 + (Finset.range d).sum levelSpace + lastSpace + 5 * d ∧
      out.regs 4 = heap4 ∧ ZeroFrom out.mem heap4 ∧
      (∀ r, 70 ≤ r → out.regs r = s3.regs r) ∧
      out.mem heap = 0 ∧
      (∀ j < cnt, out.mem (emptyPtrs + j) = emptyGraphPtr) ∧
      (∀ j < 4, out.mem (emptyGraphPtr + j) = 0) ∧
      ForestPtrListAt out.mem newPtrs (chainSuffixForests modelPre.chain 0) tok.intCap heap4 ∧
      FreshTablesAt out.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        (level0E2I true G0' tr.2.1) (level0I2E true G0' tr.2.2.1) (level0NF true G0' tr.2.2.2.1) ∧
      out.mem (root + 14) = newRootGraph ∧ out.mem (root + 11) = 0 ∧
      out.mem levelMeta = newLen0 ∧ out.mem (levelMeta + d) = newRootGraph ∧
      DynGraphAt out.mem newRootGraph vCap eCap (modelPre.chain.G 0) ∧
      EdgeValuesAt out.mem newLen0 4 L P (modelPre.chain.G 0).E
        (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ 0) ∧
      (∀ e < tok.intCap, out.mem (tok.slots + e) = 0) ∧
      (∀ e < tok.intCap, out.mem (tok.inOffReady + e) = 0) ∧
      OffReadyInv out.mem 0 tok.offReadyList tok.inOffReady tok.intCap ∧
      Rtree.rep tok.treeHeap curTree1 curTreeTok1 out.mem ∧
      Rtree.phi tok.treeHeap curTreeTok1 out.mem = Rtree.phi tok.treeHeap curTreeTok1 s3.mem ∧
      (∀ e ∈ model.extG.E,
        let eiOld := tr.2.1 e
        let eiNew := level0E2I true G0' tr.2.1 e
        let v := newCanonVal eiOld
        eiNew < G0'.m ∧ compactUnrank G0'.E eiNew = eiOld ∧
        PathIntAt out.mem (out.mem (tok.edgeThresholds + eiNew)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt out.mem (out.mem (tok.edgeRecords + eiNew)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (eiOld ∈ G0.E →
          out.mem (tok.edgeThresholds + eiNew) = mem0 (tok.edgeThresholds + eiOld) ∧
          ((eiOld ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ out.mem (tok.edgeRecords + eiNew) ∧
              out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, out.mem (tok.edgeRecords + eiNew) ≤ a →
                a < out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
                ¬ Rtree.foot tok.treeHeap curTreeTok1 a) ∧
           (eiOld ∉ model.chain.toTreeChain.chainTree.E →
              out.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + eiOld)))) ∧
        (eiOld ∉ G0.E →
          heapSync + 3 * L ≤ out.mem (tok.edgeThresholds + eiNew) ∧
          out.mem (tok.edgeThresholds + eiNew) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ out.mem (tok.edgeRecords + eiNew) ∧
          out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2)) ∧
      (∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁) + (2 + 4 * L) ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁)) ∧
      (∀ e₁ ∈ model.extG.E, tr.2.1 e₁ ∉ G0.E → ∀ e₂ ∈ model.extG.E, tr.2.1 e₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          out.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁)) ∧
      (∀ j < d,
        out.mem (branchBase + j) = modelPre.chain.bran j ∧
        heap3 ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ heap4 ∧
        Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs modelPre.chain j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok j) a → heap3 ≤ a ∧ a < heap4)) ∧
      (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok j₂) a) ∧
      (∀ j, 1 ≤ j → j < d →
        DynGraphAt out.mem (out.mem (levelMeta + d + j)) vCap eCap (modelPre.chain.G j) ∧
        heap3 ≤ out.mem (levelMeta + d + j) ∧
        out.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ heap4 ∧
        EdgeValuesAt out.mem (out.mem (levelMeta + j)) 4 L P (modelPre.chain.G j).E
          (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ j) ∧
        heap3 ≤ out.mem (levelMeta + j) ∧
        out.mem (levelMeta + j) + eCap * L ≤ heap4 ∧
        (∀ r < d,
          (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + eCap * L →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
          (∀ a, out.mem (levelMeta + d + j) ≤ a →
            a < out.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a)) ∧
        (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E).foot
            (out.mem (handleBase + d)) termTok a) ∧
        (∀ a, out.mem (levelMeta + d + j) ≤ a →
          a < out.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E).foot
            (out.mem (handleBase + d)) termTok a)) ∧
      out.mem (branchBase + d) = modelPre.chain.lastBran ∧
      heap3 ≤ out.mem (handleBase + d) ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E).rep
        (out.mem (handleBase + d)) (modelPre.chain.lastK, modelPre.chain.lastLSFs) termTok out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E).foot
          (out.mem (handleBase + d)) termTok a →
        heap3 ≤ a ∧ a < heap4 ∧ ∀ j < d, ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok j) a) ∧
      out.mem rebuildCountBase = model.chain.rebuildCount 0 + 1 ∧
      (∀ j < d, out.mem (updCountBase + j) = 0) ∧
      (∀ a < heap, ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
        out.mem a = mem a) ∧
      (∀ a < uIntBuf, a ≠ root + 11 → a ≠ root + 14 → a ≠ rebuildCountBase →
        (a < handleBase ∨ handleBase + d < a) →
        (a < branchBase ∨ branchBase + d < a) →
        (a < updCountBase ∨ updCountBase + d ≤ a) →
        tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
        tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
        tok.tag a ≠ 12 → tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
        tok.tag a ≠ 16 → tok.tag a ≠ 20 →
        tok.tag a ≠ 22 + d → tok.tag a ≠ 23 + d →
        (∀ j < d, tok.tag a ≠ 21 + j) → out.mem a = mem0 a) ∧
      cost + (Finset.range d).sum (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok j) out.mem) ≤
        (Finset.range d).sum (fun j => levelCost modelPre.chain j + 9) +
        lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) +
        d * (Psc.readout + 68) + 15 * d + 270 ∧
      ((∀ j, 1 ≤ j → j < d →
          out.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ out.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
          out.mem (levelMeta + j₁) + eCap * L ≤ out.mem (levelMeta + d + j₂))) := by
  dsimp only
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let ℓ' := fun e' => lVec (tr.2.2.1 e')
  let g' := fun e' => gVec (tr.2.2.1 e')
  let modelPre := alg2PreResetState cfg model U gVec lVec
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, hFreshInv0, _, hExtM0, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _, _, hT4, hT5, hT6, hT7, hT8, hT9, _, _, hT12, hT13, _, hT15,
    hT16, hT1718, _, _, _⟩ := hTags0
  obtain ⟨⟨hN0Mem0, hTagN0_0, _, _⟩, _, hLvlM0, hTagLvlM0, hTagMeta0, _⟩ := hMeta0
  obtain ⟨_, hSFLPre, hValidAll, hNPreLe, hRotPre, hSubKFBL, _, hLastFSubPre, _, _, _, _, _,
    hMLePre, hConnPre⟩ := hModelInvKFBL
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hOrdLo, hOrdEnd3⟩ := hHeaps
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  obtain ⟨hTr1Eq, hFreshTr, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 hRef
  have hG0'cm : G0'.compact.m ≤ m := by
    have h1 : G0'.compact.m = G0'.m := by simp [MGraph.compact, MGraph.m]
    rw [h1, hFreshTr.m_eq]
    exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
      (Finset.card_range m)
  have hTagSep (a b va vb : ℕ) (ha : tok.tag a = va) (hb : tok.tag b = vb) (hne : va ≠ vb) : a ≠ b :=
    fun h => hne (ha.symm.trans (h ▸ hb))
  have hDisjTag (b1 n1 v1 b2 n2 v2 : ℕ) (hn1 : 0 < n1) (hn2 : 0 < n2)
      (h1 : ∀ i < n1, tok.tag (b1 + i) = v1)
      (h2 : ∀ i < n2, tok.tag (b2 + i) = v2) (hne : v1 ≠ v2) : b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 := by
    by_contra h; push Not at h
    rcases le_total b1 b2 with hle | hle
    · exact hne ((h1 (b2 - b1) (by omega)).symm.trans
        (by rw [show b1 + (b2 - b1) = b2 by omega]; simpa using h2 0 hn2))
    · exact hne.symm ((h2 (b1 - b2) (by omega)).symm.trans
        (by rw [show b2 + (b1 - b2) = b1 by omega]; simpa using h1 0 hn1))
  have hDisjTagSingle (c vc b n vb : ℕ) (hc : tok.tag c = vc) (hb : ∀ i < n, tok.tag (b + i) = vb)
      (hne : vc ≠ vb) : c < b ∨ b + n ≤ c := by
    by_contra h; push Not at h
    exact hne (hc.symm.trans (by have := hb (c - b) (by omega); rwa [show b + (c - b) = c by omega] at this))
  have hs3_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (h0 : v ≠ 0) (h6 : v ≠ 6) (h7 : v ≠ 7)
      (h8 : v ≠ 8) (h9 : v ≠ 9) (h10 : v ≠ 10) (h11 : v ≠ 11) (h12 : v ≠ 12) (h13 : v ≠ 13)
      (h14 : v ≠ 14) (h15 : v ≠ 15) (h16 : v ≠ 16) (h20 : v ≠ 20) (h22 : v ≠ 22 + cfg.P.d)
      (h23 : v ≠ 23 + cfg.P.d) (hc : ∀ j < cfg.P.d, v ≠ 21 + j) (hne11 : a ≠ root + 11) (hne14 : a ≠ root + 14) :
      s3.mem a = mem0 a := by
    have hlt := htagLt (by rw [ht]; exact h0)
    exact (hs3_frame a (by omega) hne11 hne14 (by rw [ht]; exact h6) (by rw [ht]; exact h7)
      (by rw [ht]; exact h8) (by rw [ht]; exact h9) (by rw [ht]; exact h10)
      (by rw [ht]; exact h11) (by rw [ht]; exact h12) (by rw [ht]; exact h13)
      (by rw [ht]; exact h14) (by rw [ht]; exact h15) (by rw [ht]; exact h16)
      (by rw [ht]; exact h20) (by rw [ht]; exact h22) (by rw [ht]; exact h23)
      (fun j hj => by rw [ht]; exact hc j hj)).trans
      (hMemEq a hlt (by rw [ht]; exact h6) (by rw [ht]; exact h7) (by rw [ht]; exact h8))
  let st0A : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
  have hN0AddrEq : solverLvlMAddr tok.table cfg.P.d - 1 = solverN0Addr tok.table cfg.P.d := by
    simp [solverLvlMAddr]
  have hS3_N0 : s3.mem (solverLvlMAddr tok.table cfg.P.d - 1) = st0A.N₀ := by
    rw [hN0AddrEq]
    exact (hs3_eq_mem0 hTagN0_0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ => by omega)
      (hTagSep _ _ _ _ hTagN0_0 (hT1 11 (by omega)) (by omega))
      (hTagSep _ _ _ _ hTagN0_0 (hT1 14 (by omega)) (by omega))).trans hN0Mem0
  have hS3_RC0 : s3.mem (tok.levelsEnd + 2 * (cfg.P.d + 1)) = st0A.rebuildCount 0 :=
    (hs3_eq_mem0 (hT5 (2 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (fun _ _ => by omega)
      (hTagSep _ _ _ _ (hT5 (2 * (cfg.P.d + 1)) (by omega)) (hT1 11 (by omega)) (by decide))
      (hTagSep _ _ _ _ (hT5 (2 * (cfg.P.d + 1)) (by omega)) (hT1 14 (by omega)) (by decide))).trans
      (by simpa [st0A] using hRep0_keep.2.2.2.2.2.2.2.2.1.2.2.1 0 (Nat.zero_le cfg.P.d))
  have hS3_LvlM : ∀ j < cfg.P.d, s3.mem (solverLvlMAddr tok.table cfg.P.d + j) = st0A.lvlM j := fun j hj =>
    (hs3_eq_mem0 (hTagLvlM0 j hj) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (fun _ _ => by omega)
      (hTagSep _ _ _ _ (hTagLvlM0 j hj) (hT1 11 (by omega)) (by omega))
      (hTagSep _ _ _ _ (hTagLvlM0 j hj) (hT1 14 (by omega)) (by omega))).trans (hLvlM0 j hj)
  have hG0'CompactN : G0'.compact.n = model.extG.n := by
    change G0'.V.card = model.extG.V.card
    rw [← hFreshTr.hV]
  have hChPreEq' : modelPre.chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
        { st0A with ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j)),
                    g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) }
        0 G0'.compact (G0.batchEnc U_int)).1 := hChPreEq
  have hGSub0 : ∀ j ≤ cfg.P.d, (modelPre.chain.G j).E ⊆ (modelPre.chain.G 0).E := by
    intro j hj
    induction j with
    | zero => exact Finset.Subset.rfl
    | succ r ih => exact (hSubKFBL r (by omega)).2.2.2.2.trans (ih (by omega))
  obtain ⟨s4, cSuf, termTok, coreTok4, rSuf, hs4_lo, hs4_hi, hz4, hs4_ge70, hNewForests4,
      hCores4, hCoreDisj4, hMeta4, hTermB4, hTermHLo4, hTermRep4, hTermFoot4,
      hRC4, hUC4, hs4_frame, hcSuf, hMetaOrd4⟩ :=
    wireBranchASuffixKFBL_runs (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (capLimit := capLimit) (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (drainUnit := drainUnit) (edMul := edMul)
      (mThresh := mThresh) (wordExp := wordExp) (stretchPrec := stretchPrec)
      (vCap := vCap) (eCap := eCap) (initCore := initCore) (coreLenProc := coreLenProc)
      (edgeProc := edgeProc) (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
      (lastInit := lastInit) (intCap := tok.intCap) (ordW := 1 + 2 * vCap + 2 * G0'.compact.m)
      (handleBase := tok.handle + 18)
      (branchBase := tok.handle + 18 + (cfg.P.d + 1))
      (lvlMTable := solverLvlMAddr tok.table cfg.P.d)
      (levelMeta := solverLevelMetaAddr tok.table cfg.P.d)
      (rebuildCountBase := tok.levelsEnd + 2 * (cfg.P.d + 1))
      (updCountBase := tok.levelsEnd + 3 * (cfg.P.d + 1))
      (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1))
      (newLen0 := newLen0) (newLvlGraph0 := newRootGraph) (ordPtr0 := ordPtr0)
      (heap0 := heap2) (heap1 := heap2) (heap3 := heap3) (p := p) (opCore := opCore)
      (opLast := opLast) (ω := ω) (st := s3)
      st0A G0'.compact (fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j)))
      (fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)))
      (G0.batchEnc U_int)
      hCoreLocal hFour hPrec hWidth hLWord hPWord hDepthW hdPos hdW hkPos hkW
      (by simpa [st0A, hN0Eq] using hNW) hw18 hCapLim hInitOrdEq hWordExpEq hCoreImpl
      hCoreLenProc hEdgeProc hSign hMul hDiv hcopy hLastImpl hOps hRebInv0 hG0'cm
      ⟨hChPreEq' ▸ hSFLPre,
       fun j hj => hChPreEq' ▸ ⟨(hValidAll j hj).2, hNPreLe j hj⟩,
       fun j hj => hChPreEq' ▸ hRotPre j hj,
       fun j hj => by
         have h : (cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j)).F.F.E ⊆
             (modelPre.chain.G 0).E := (hSubKFBL j hj).2.2.2.1.trans (hGSub0 j (le_of_lt hj))
         have hEq : modelPre.chain.G 0 = G0'.compact := by
           rw [hChPreEq']; exact (ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P _ hdPos _ _).2.1
         rw [hEq] at h; rwa [← hChPreEq'],
       by
         have hEq : modelPre.chain.G 0 = G0'.compact := by
           rw [hChPreEq']; exact (ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P _ hdPos _ _).2.1
         have h : (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.E ⊆
             (modelPre.chain.G 0).E := hLastFSubPre.trans (hGSub0 cfg.P.d le_rfl)
         rw [hEq] at h; rwa [← hChPreEq'],
       fun j hj => hChPreEq' ▸ hMLePre j hj,
       hChPreEq' ▸ hConnPre⟩
      (by
        obtain ⟨a1, a2, a3, a4, a5, _, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
          a18⟩ := hRegs3
        exact ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩)
      hS3_N0 hS3_RC0 hS3_LvlM hRG3 hLen3 hOrd3 hOrdW3
      (by rw [hG0'CompactN, hvCapEq]; omega) hLMd_3
      (fun e he => by
        have hlt : e < G0'.m := by simpa [MGraph.compact, MGraph.m] using he
        exact lt_of_lt_of_le hlt hG0'mLeR.2)
      ⟨by simp [solverLvlMAddr, solverN0Addr],
       by have := htagLt (by rw [hT4 cfg.P.d (by omega)]; decide); omega,
       by have := htagLt (by rw [hT4 (cfg.P.d + 1 + cfg.P.d) (by omega)]; decide); omega,
       by have := htagLt (by rw [hTagLvlM0 (cfg.P.d - 1) (by omega)]; omega); omega,
       by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); omega,
       by have := htagLt (by rw [hT5 (2 * (cfg.P.d + 1)) (by omega)]; decide); omega,
       by have := htagLt (by rw [hT5 (3 * (cfg.P.d + 1) + cfg.P.d - 1) (by omega)]; decide); omega,
       by omega, le_rfl, by omega, hNL0Lo, by omega, by omega, by omega, by omega, hOrdEnd3⟩
      ⟨Or.inl (by omega),
       (hDisjTag (tok.handle + 18) (cfg.P.d + 1) 4 (solverLvlMAddr tok.table cfg.P.d) cfg.P.d (21 + cfg.P.d)
         (by omega) (by omega) (fun i hi => hT4 i (by omega)) hTagLvlM0 (by omega)).imp (by omega) id,
       (hDisjTag (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4 (solverLvlMAddr tok.table cfg.P.d) cfg.P.d (21 + cfg.P.d)
         (by omega) (by omega) (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) hTagLvlM0 (by omega)).imp (by omega) id,
       (hDisjTag (tok.handle + 18) (cfg.P.d + 1) 4 (solverLevelMetaAddr tok.table cfg.P.d) (2 * cfg.P.d) (22 + cfg.P.d)
         (by omega) (by omega) (fun i hi => hT4 i (by omega)) hTagMeta0 (by omega)).imp (by omega) id,
       (hDisjTag (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4 (solverLevelMetaAddr tok.table cfg.P.d) (2 * cfg.P.d) (22 + cfg.P.d)
         (by omega) (by omega) (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega)).imp (by omega) id,
       hDisjTag _ _ (21 + cfg.P.d) _ _ (22 + cfg.P.d) (by omega) (by omega) hTagLvlM0 hTagMeta0 (by omega),
       by rw [hN0AddrEq]; exact hTagSep _ _ _ _ (hT5 (2 * (cfg.P.d + 1)) (by omega)) hTagN0_0 (by omega),
       hDisjTagSingle _ 5 _ _ (21 + cfg.P.d) (hT5 (2 * (cfg.P.d + 1)) (by omega)) hTagLvlM0 (by omega),
       (hDisjTagSingle _ 5 (tok.handle + 18) (cfg.P.d + 1) 4 (hT5 (2 * (cfg.P.d + 1)) (by omega))
         (fun i hi => hT4 i (by omega)) (by decide)).imp id (by omega),
       (hDisjTagSingle _ 5 (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4 (hT5 (2 * (cfg.P.d + 1)) (by omega))
         (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) (by decide)).imp id (by omega),
       hDisjTagSingle _ 5 _ _ (22 + cfg.P.d) (hT5 (2 * (cfg.P.d + 1)) (by omega)) hTagMeta0 (by omega),
       Or.inl (by omega),
       (hDisjTag (tok.levelsEnd + 3 * (cfg.P.d + 1)) cfg.P.d 5 (tok.handle + 18) (cfg.P.d + 1) 4
         (by omega) (by omega) (fun i hi => by have := hT5 (3 * (cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this)
         (fun i hi => hT4 i (by omega)) (by decide)).imp id (by omega),
       (hDisjTag (tok.levelsEnd + 3 * (cfg.P.d + 1)) cfg.P.d 5 (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4
         (by omega) (by omega) (fun i hi => by have := hT5 (3 * (cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this)
         (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) (by decide)).imp id (by omega),
       hDisjTag _ _ 5 _ _ (22 + cfg.P.d) (by omega) (by omega) (fun i hi => by have := hT5 (3 * (cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega),
       Or.inl (by have := htagLt (by rw [hT4 cfg.P.d (by omega)]; decide); omega),
       Or.inl (by have := htagLt (by rw [hT4 (cfg.P.d + 1 + cfg.P.d) (by omega)]; decide); omega),
       Or.inl (by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); omega),
       Or.inl (by have := htagLt (by rw [hT5 (3 * (cfg.P.d + 1) + cfg.P.d - 1) (by omega)]; decide); omega),
       Or.inl (by have := htagLt (by rw [hT5 (2 * (cfg.P.d + 1)) (by omega)]; decide); omega)⟩
      hz3 hSufRoom hTok0
  rw [← hChPreEq'] at hNewForests4 hCores4 hMeta4 hTermB4
  rw [← hChPreEq'] at hTermRep4 hTermFoot4 hcSuf
  let lm := solverLevelMetaAddr tok.table cfg.P.d
  let newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)
  have hs4_eq_s3_ge (a : ℕ) (ha1 : heap ≤ a) (ha2 : a < heap3)
      (hNP : a < newPtrs ∨ newPtrs + (cfg.P.d + 1) ≤ a) :
      s4.mem a = s3.mem a :=
    hs4_frame a ha2
      (Or.inr (by have := htagLt (by rw [hT4 cfg.P.d (by omega)]; decide); omega))
      (Or.inr (by have := htagLt (by rw [hT4 (cfg.P.d + 1 + cfg.P.d) (by omega)]; decide); omega))
      ⟨Or.inr (by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); omega),
       Or.inr (by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); omega)⟩
      (by have := htagLt (by rw [hT5 (2 * (cfg.P.d + 1)) (by omega)]; decide); omega)
      (Or.inr (by have := htagLt (by rw [hT5 (3 * (cfg.P.d + 1) + cfg.P.d - 1) (by omega)]; decide); omega))
      hNP
  have hs4_eq_s3_tag {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (h4 : v ≠ 4) (h5 : v ≠ 5)
      (h22 : v ≠ 22 + cfg.P.d) : s4.mem a = s3.mem a := by
    have hlt := htagLt (by rw [ht]; exact hv0)
    exact hs4_frame a (by omega)
      (by by_contra h; push Not at h; exact h4 (ht.symm.trans (by have := hT4 (a - (tok.handle + 18)) (by omega); rwa [show tok.handle + 18 + (a - (tok.handle + 18)) = a by omega] at this)))
      (by by_contra h; push Not at h; exact h4 (ht.symm.trans (by have := hT4 (cfg.P.d + 1 + (a - (tok.handle + 18 + (cfg.P.d + 1)))) (by omega); rwa [show tok.handle + 18 + (cfg.P.d + 1 + (a - (tok.handle + 18 + (cfg.P.d + 1)))) = a by omega] at this)))
      ⟨by by_contra h; push Not at h; exact h22 (ht.symm.trans (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this)),
       by by_contra h; push Not at h; exact h22 (ht.symm.trans (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this))⟩
      (fun h => h5 (ht.symm.trans (h ▸ hT5 (2 * (cfg.P.d + 1)) (by omega))))
      (by by_contra h; push Not at h; exact h5 (ht.symm.trans (by have := hT5 (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) (by omega); rwa [show tok.levelsEnd + (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) = a by omega] at this)))
      (Or.inl (by omega))
  have hTreeAgree4 : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      s4.mem a = s3.mem a := fun a ha => by
    rcases hTreeFoot1 a ha with h0 | ⟨hlo, hhi⟩
    · exact hs4_eq_s3_tag (hT16 a h0) (by decide) (by decide) (by decide) (by omega)
    · exact hs4_eq_s3_ge a (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))
  have hTreeLoc4 := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC)
    tok.treeHeap curTree1 curTreeTok1 s3.mem s4.mem (fun a ha => (hTreeAgree4 a ha).symm)
  have hMPreG0 : modelPre.chain.G 0 = G0'.compact := by
    rw [hChPreEq]; exact (ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P _ hdPos _ _).2.1
  have hMPreEll0 : modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ 0 =
      fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j)) := by
    rw [hChPreEq']
    have hEx := ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P
      { st0A with ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j)),
                  g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) } hdPos G0'.compact (G0.batchEnc U_int)
    simp [TreeChain.chainLen, hEx.2.2.2.2.2.2.1]
  refine ⟨s4, cSuf, s4.regs 4, termTok, coreTok4, rSuf, hs4_lo, hs4_hi, rfl, hz4, hs4_ge70,
    (hs4_eq_s3_ge heap le_rfl (by omega) (Or.inl (by dsimp [newPtrs]; omega))).trans hHeap0_3,
    fun j hj => (hs4_eq_s3_ge _ (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))).trans (hEmptyPtrs3 j hj),
    fun j hj => (hs4_eq_s3_ge _ (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))).trans (hEmptyG3 j hj),
    hNewForests4, ?_,
    (hs4_eq_s3_tag (hT1 14 (by omega)) (by decide) (by decide) (by decide) (by omega)).trans hR14_3,
    (hs4_eq_s3_tag (hT1 11 (by omega)) (by decide) (by decide) (by decide) (by omega)).trans hR11_3,
    ?_, ?_, ?_, ?_,
    fun e he => (hs4_eq_s3_tag (hT9 e he) (by decide) (by decide) (by decide) (by omega)).trans (hSlots3 e he),
    fun e he => (hs4_eq_s3_tag (hT15 e he) (by decide) (by decide) (by decide) (by omega)).trans (hZeroIn3 e he),
    ?_, hTreeLoc4.1 hTreeRep3, hTreeLoc4.2.symm, ?_, ?_, ?_,
    hCores4, hCoreDisj4, hMeta4, hTermB4, hTermHLo4, hTermRep4, hTermFoot4,
    hRC4, hUC4, ?_, ?_, hcSuf, hMetaOrd4⟩
  · exact ⟨(hs4_eq_s3_tag hT6 (by decide) (by decide) (by decide) (by omega)).trans hFresh3.1,
      fun e he => (hs4_eq_s3_tag (hT7 e he) (by decide) (by decide) (by decide) (by omega)).trans (hFresh3.2.1 e he),
      fun j hj => (hs4_eq_s3_tag (hT8 j hj) (by decide) (by decide) (by decide) (by omega)).trans (hFresh3.2.2 j hj)⟩
  · have hHDisjM := hDisjTag (tok.handle + 18) (cfg.P.d + 1) 4 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => hT4 i (by omega)) hTagMeta0 (by omega)
    have hBDisjM := hDisjTag (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega)
    have hUDisjM := hDisjTag (tok.levelsEnd + 3 * (cfg.P.d + 1)) cfg.P.d 5 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => by have := hT5 (3 * (cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega)
    exact (hs4_frame lm (by have := htagLt (by rw [show tok.tag lm = 22 + cfg.P.d by simpa [lm] using hTagMeta0 0 (by omega)]; omega); omega)
      (by omega) (by omega) ⟨Or.inl (by omega), Or.inl (by omega)⟩
      (hTagSep _ _ _ _ (by simpa [lm] using hTagMeta0 0 (by omega)) (hT5 (2 * (cfg.P.d + 1)) (by omega)) (by omega))
      (by omega)
      (Or.inl (by have := htagLt (by rw [show tok.tag lm = 22 + cfg.P.d by simpa [lm] using hTagMeta0 0 (by omega)]; omega); omega))).trans hLM0_3
  · have hHDisjM := hDisjTag (tok.handle + 18) (cfg.P.d + 1) 4 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => hT4 i (by omega)) hTagMeta0 (by omega)
    have hBDisjM := hDisjTag (tok.handle + 18 + (cfg.P.d + 1)) (cfg.P.d + 1) 4 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => by have := hT4 (cfg.P.d + 1 + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega)
    have hUDisjM := hDisjTag (tok.levelsEnd + 3 * (cfg.P.d + 1)) cfg.P.d 5 lm (2 * cfg.P.d) (22 + cfg.P.d)
      (by omega) (by omega) (fun i hi => by have := hT5 (3 * (cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this) hTagMeta0 (by omega)
    exact (hs4_frame (lm + cfg.P.d) (by have := htagLt (by rw [hTagMeta0 cfg.P.d (by omega)]; omega); omega)
      (by omega) (by omega) ⟨Or.inr (by omega), Or.inl (by omega)⟩
      (hTagSep _ _ _ _ (hTagMeta0 cfg.P.d (by omega)) (hT5 (2 * (cfg.P.d + 1)) (by omega)) (by omega))
      (by omega)
      (Or.inl (by have := htagLt (by rw [hTagMeta0 cfg.P.d (by omega)]; omega); omega))).trans hLMd_3
  · rw [hMPreG0]
    exact dynGraphAt_of_agree hRG3 (fun a ha1 ha2 => hs4_eq_s3_ge a (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega)))
  · rw [hMPreG0, hMPreEll0]
    exact hLen3.congr (fun e he t ht => by
      have hlt : e < G0'.m := by simpa [MGraph.compact, MGraph.m] using he
      have heL : e * L + L ≤ eCap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (lt_of_lt_of_le hlt (heCapEq ▸ hG0'mLeR.1)))
      exact hs4_eq_s3_ge _ (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega)))
  · obtain ⟨hc, _, _, h3', _⟩ := hOffInv3
    refine ⟨hc, fun j hj => by omega, fun j1 hj1 => by omega, fun e he => by
      rw [hs4_eq_s3_tag (hT15 e he) (by decide) (by decide) (by decide) (by omega)]; exact h3' e he,
      fun e he h1 => by rw [hs4_eq_s3_tag (hT15 e he) (by decide) (by decide) (by decide) (by omega)] at h1
                        exact False.elim (by have := hZeroIn3 e he; omega)⟩
  · intro e he
    obtain ⟨hLt, hUnr, hThr3, hRec3, hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc, hInG0, hNotG0⟩ := hCanon3 e he
    have hThrCell : s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) =
        s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) :=
      hs4_eq_s3_tag (hT12 _ (lt_of_lt_of_le hLt hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega)
    have hRecCell : s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) =
        s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) :=
      hs4_eq_s3_tag (hT13 _ (lt_of_lt_of_le hLt hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega)
    have hOldEq (hOld : tr.2.1 e ∈ G0.E) : model.extToInt e = tr.2.1 e := by
      by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
      · exact False.elim ((hDichRep e he hRepE).2.2.2.1 hOld)
      · exact (hDichUnch e he hRepE).2.1.symm
    refine ⟨hLt, hUnr, ?_, ?_, hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc,
      fun hOld => by rw [hThrCell, hRecCell]; exact hInG0 hOld,
      fun hNot => by rw [hThrCell, hRecCell]; exact hNotG0 hNot⟩
    · rw [hThrCell]; refine hThr3.congr fun t ht => ?_
      by_cases hOld : tr.2.1 e ∈ G0.E
      · rw [(hInG0 hOld).1]
        have hTag17 : tok.tag (mem0 (tok.edgeThresholds + tr.2.1 e) + t) = 17 := by
          rw [← hOldEq hOld]; exact (hT1718 e he).1 t ht
        exact hs4_eq_s3_tag hTag17 (by decide) (by decide) (by decide) (by omega)
      · obtain ⟨hlo, hhi, _, _⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) at hlo
        change s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) + L ≤ heap2 at hhi
        exact hs4_eq_s3_ge _ (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))
    · rw [hRecCell]; refine hRec3.congr fun a ha1 ha2 => ?_
      change s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) ≤ a at ha1
      change a < s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + 2 + 4 * L at ha2
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨hlo, hhi, _⟩ := (hInG0 hOld).2.1 hTree
          change heap1 ≤ s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
          change s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heapSync at hhi
          exact hs4_eq_s3_ge a (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))
        · have hPtrEq : s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) = mem0 (tok.edgeRecords + tr.2.1 e) :=
            (hInG0 hOld).2.2 hTree
          have heOld := hOldEq hOld
          have hTag18 : tok.tag a = 18 := by
            have := (hT1718 e he).2 (heOld.symm ▸ hTree) (a - mem0 (tok.edgeRecords + tr.2.1 e)) (by omega)
            rwa [heOld, show mem0 (tok.edgeRecords + tr.2.1 e) + (a - mem0 (tok.edgeRecords + tr.2.1 e)) = a by omega] at this
          exact hs4_eq_s3_tag hTag18 (by decide) (by decide) (by decide) (by omega)
      · obtain ⟨_, _, hlo, hhi⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
        change s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heap2 at hhi
        exact hs4_eq_s3_ge a (by omega) (by omega) (Or.inr (by dsimp [newPtrs]; omega))
  · intro e₁ he1 e₂ he2 hne
    have h1 := (hCanon3 e₁ he1).1; have h2 := (hCanon3 e₂ he2).1
    rw [hs4_eq_s3_tag (hT13 _ (lt_of_lt_of_le h1 hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega),
        hs4_eq_s3_tag (hT13 _ (lt_of_lt_of_le h2 hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega)]
    exact hOffDisj3 e₁ he1 e₂ he2 hne
  · intro e₁ he1 hnot1 e₂ he2 hnot2
    have h1 := (hCanon3 e₁ he1).1; have h2 := (hCanon3 e₂ he2).1
    rw [hs4_eq_s3_tag (hT12 _ (lt_of_lt_of_le h1 hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega),
        hs4_eq_s3_tag (hT13 _ (lt_of_lt_of_le h2 hG0'mLeR.2)) (by decide) (by decide) (by decide) (by omega)]
    exact hThrOffDisj3 e₁ he1 hnot1 e₂ he2 hnot2
  · intro a ha hnf
    have ht0 : tok.tag a = 0 := by by_contra h; exact hnf (Or.inl (hOwnOfTag a h))
    have hneTag (v : ℕ) (hv : v ≠ 0) : tok.tag a ≠ v := by rw [ht0]; exact hv.symm
    refine (hs4_frame a (by omega)
      (by by_contra h; push Not at h; exact hneTag 4 (by decide) (by have := hT4 (a - (tok.handle + 18)) (by omega); rwa [show tok.handle + 18 + (a - (tok.handle + 18)) = a by omega] at this))
      (by by_contra h; push Not at h; exact hneTag 4 (by decide) (by have := hT4 (cfg.P.d + 1 + (a - (tok.handle + 18 + (cfg.P.d + 1)))) (by omega); rwa [show tok.handle + 18 + (cfg.P.d + 1 + (a - (tok.handle + 18 + (cfg.P.d + 1)))) = a by omega] at this))
      ⟨by by_contra h; push Not at h; exact hneTag (22 + cfg.P.d) (by omega) (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this),
       by by_contra h; push Not at h; exact hneTag (22 + cfg.P.d) (by omega) (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this)⟩
      (fun h => hneTag 5 (by decide) (h ▸ hT5 (2 * (cfg.P.d + 1)) (by omega)))
      (by by_contra h; push Not at h; exact hneTag 5 (by decide) (by have := hT5 (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) (by omega); rwa [show tok.levelsEnd + (3 * (cfg.P.d + 1) + (a - (tok.levelsEnd + 3 * (cfg.P.d + 1)))) = a by omega] at this))
      (Or.inl (by omega))).trans ?_
    exact hs3_frame a (by omega)
      (fun h => hneTag 1 (by decide) (h ▸ hT1 11 (by omega)))
      (fun h => hneTag 1 (by decide) (h ▸ hT1 14 (by omega)))
      (hneTag 6 (by decide)) (hneTag 7 (by decide)) (hneTag 8 (by decide))
      (hneTag 9 (by decide)) (hneTag 10 (by decide)) (hneTag 11 (by decide))
      (hneTag 12 (by decide)) (hneTag 13 (by decide)) (hneTag 14 (by decide))
      (hneTag 15 (by decide)) (hneTag 16 (by decide)) (hneTag 20 (by decide))
      (hneTag (22 + cfg.P.d) (by omega)) (hneTag (23 + cfg.P.d) (by omega)) (fun j _ => hneTag (21 + j) (by omega))
  · intro a ha hne11 hne14 hneRC hH hB hUC h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h20 h22 h23 hc
    refine (hs4_frame a (by omega) hH hB
      ⟨by by_contra h; push Not at h; exact h22 (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this),
       by by_contra h; push Not at h; exact h22 (by have := hTagMeta0 (a - lm) (by omega); rwa [show lm + (a - lm) = a by omega] at this)⟩
      hneRC hUC (Or.inl (by omega))).trans ?_
    exact (hs3_frame a (by omega) hne11 hne14 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h20 h22 h23 hc).trans
      (hMemEq a ha h6 h7 h8)

end MinCostFlow.MinRatio
