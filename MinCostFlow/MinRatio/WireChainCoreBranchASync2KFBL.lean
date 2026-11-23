module

public import MinCostFlow.MinRatio.WireChainCoreBranchARunKFBL
public import MinCostFlow.MinRatio.WireChainCoreReady
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# Branch A Step 5a: Sync 2 (`∅ → newF`) execution (`WireChainCoreBranchASync2KFBL`)

Executes the Sync 2 loop (`wireBranchASync2LoopStmt`) after `wireBranchAStep4KFBL_runs`:
1. Packs `∅ → newF` via `wireSuffixPackEditsBody` (`emptyPtrs → newPtrs`, `cnt = d + 1`).
2. Sets up path-tree registers (`shiftTermSetupLoop`) and inserts every edge of `newF` into the
   empty path tree via `wireTreeSyncLoop_insertOnly_defer_runs` (`deferSet := (modelPre.chain.G 0).E`),
   preserving `offReadyCount = 0` and `inOffReady[0..intCap) = 0`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch A Step 5a statement: pack `∅ → newF`, set up path-tree registers, and run
`wireTreeSyncLoop`. -/
@[expose] def wireBranchASync2LoopStmt
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
  .call 18 packEditsProc [.reg 92, .reg 81, .reg 79, .reg 10, .reg 4] ;;
  .assign 27 (.reg 70) ;;
  .assign 29 (.reg 73) ;;
  shiftTermSetupLoop ;;
  wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg

/-- Branch A Step 5b statement: save `reg 4 := reg 3 + 1`, load `mNew`, call
`rebuildOffReadyProc`, and return `reg 4`. The returned heap pointer skips one word, so that the
words below it that Branch A owns include the new core handle and lens base, which may lie at
`reg 3`. -/
@[expose] def wireBranchAReadyRetStmt (rebuildOffReadyProc : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 10 (.load (.bin .add (.reg 70) (.const 14))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.const 3))) ;;
  .call 12 rebuildOffReadyProc [.reg 70, .reg 11] ;;
  .ret (.reg 4)

/-- Full Branch A Step 5 statement: Sync 2 (`∅ → newF`), off-ready rebuild, and return. -/
@[expose] def wireBranchASync2AndReadyStmt
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg rebuildOffReadyProc : ℕ) : Stmt :=
  wireBranchASync2LoopStmt packEditsProc readTree cutTree linkTree bind canonCopy isNeg ;;
  wireBranchAReadyRetStmt rebuildOffReadyProc

theorem wireBranchASync2AndReadyStmt_noRand
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg rebuildOffReadyProc : ℕ) :
    (wireBranchASync2AndReadyStmt packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      rebuildOffReadyProc).NoRand := by
  simp [wireBranchASync2AndReadyStmt, wireBranchASync2LoopStmt, wireBranchAReadyRetStmt,
    shiftTermSetupLoop, wireTreeSyncLoop_noRand, Stmt.NoRand]

private theorem treeEditDiff_empty_all_insert {newE : Finset ℕ} {edits : List TreeChange}
    (hd : TreeEditDifference ∅ newE edits) : ∀ ch ∈ edits, ∃ e, ch = .insert e := by
  intro ch hch
  cases ch with
  | insert e => exact ⟨e, rfl⟩
  | delete e =>
    have h := hd.delete_mem_sdiff hch
    simp at h

theorem offReadyInv_zero_inOffReady {mem : ℕ → ℕ} {ol io cap : ℕ}
    (h : OffReadyInv mem 0 ol io cap) : ∀ e < cap, mem (io + e) = 0 := by
  intro e he
  rcases h.2.2.2.1 e he with h0 | h1
  · exact h0
  · obtain ⟨j, hj, _⟩ := h.2.2.2.2 e he h1
    omega

private theorem pathRep_foot_base_s2 {L C b : ℕ} {s : PathTreeState}
    {x : (LinkCut.PathProg.pathRep 4 L C).τ} {mem : ℕ → ℕ}
    (_ : (LinkCut.PathProg.pathRep 4 L C).rep b s x mem) :
    (LinkCut.PathProg.pathRep 4 L C).foot b x b := by
  refine ⟨le_rfl, ?_⟩
  unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
  have h1 : 1 ≤ LinkCut.PathProg.recW (LinkCut.PathProg.treeLimbs L) := by
    unfold LinkCut.PathProg.recW; omega
  have h3 := Nat.mul_pos h1 (by omega : 0 < 2 * x.1.n + 1)
  unfold LinkCut.PathProg.recW at h3; omega

/-- Helper: `translateBatch` leaves `i2e` unchanged at all indices `≥ tr.2.2.2.1`. -/
theorem translateBatch_i2e_ge (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (U : List Update) :
    nf ≤ (translateBatch curExt e2i i2e nf U).2.2.2.1 ∧
    ∀ j, (translateBatch curExt e2i i2e nf U).2.2.2.1 ≤ j →
      (translateBatch curExt e2i i2e nf U).2.2.1 j = i2e j := by
  induction U generalizing curExt e2i i2e nf with
  | nil => exact ⟨le_rfl, fun _ _ => rfl⟩
  | cons u rest ih =>
    dsimp only [translateBatch]
    cases u with
    | delete e =>
      dsimp only [translateUpdate]
      exact ih _ _ _ _
    | insert e u0 v0 =>
      dsimp only [translateUpdate]
      obtain ⟨hLe, hGe⟩ := ih _ (Function.update e2i e nf) (Function.update i2e nf e) (nf + 1)
      refine ⟨Nat.le_trans (Nat.le_succ nf) hLe, fun j hj => ?_⟩
      rw [hGe j hj, Function.update_of_ne (Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self nf) (le_trans hLe hj)))]
    | split v v' St Sh =>
      dsimp only [translateUpdate]
      exact ih _ _ _ _

set_option maxHeartbeats 800000 in
/-- Execute Branch A Step 5a (`s4 → s5g`): pack `∅ → newF`, set up path-tree registers, and
synchronize the path tree with `newF`, preserving `offReadyCount = 0` and all memory outside
`{root + 11, slots, names, slotThresholds, edgeRecords, offReadyList, inOffReady, Rtree}` below
`heap4`. -/
theorem wireBranchASync2LoopKFBL_runs
    {w L P m V psi k epsExp drainUnit vCap eCap
      packEditsProc initTree bind canonCopy isNeg
      root uIntBuf heap heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {s4 : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    {gVec lVec : ℕ → ℝ}
    {curTree1 : PathTreeState} {curTrees1 : List AuxTree} {curFree1 : List ℕ}
    {curDepth1 : ℕ → ℕ}
    {curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {newCanonVal : ℕ → PathEdgeValue}
    (hPackProc : p.procs[packEditsProc]? = some wireSuffixPackEditsBody)
    (hFmtBits : fmt.limbBits = 4) (hdPos : 0 < cfg.P.d) (hw18 : 18 < 2 ^ w)
    (hvCapEq : vCap = model.extG.n) (heCapEq : eCap = tok.rootECap)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
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
    (hRenTrue :
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount = true)
    (hNewForest : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.IsForest)
    (hNewSub : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E ⊆
      ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E)
    (hG0'mLeR :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.rootECap ∧
      ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.intCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hULeHeap : uIntBuf ≤ heap)
    (hHeaps :
      heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ heap1 ∧
      heap1 ≤ heapSync ∧ heapSync + 3 * L ≤ heap2 ∧
      heap2 ≤ newLen0 ∧ newLen0 + eCap * L ≤ newRootGraph ∧
      newRootGraph + dynGraphSize vCap eCap ≤ heap3 ∧ heap3 ≤ heap4)
    (hRegs4 :
      let d := cfg.P.d
      let cnt := d + 1
      let arrBase := heap + 1 + 12 * d
      s4.regs 4 = heap4 ∧ s4.regs 70 = root ∧ s4.regs 73 = tok.handle ∧
      s4.regs 79 = cnt ∧ s4.regs 81 = arrBase + cnt ∧ s4.regs 92 = arrBase + 2 * cnt)
    (hz4 : ZeroFrom s4.mem heap4)
    (hEmptyPtrs4 : ∀ j < cfg.P.d + 1,
      s4.mem (heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) + j) =
        heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1))
    (hEmptyG4 : ∀ j < 4, s4.mem (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + j) = 0)
    (hNewForests4 : ForestPtrListAt s4.mem (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1))
      (chainSuffixForests (alg2PreResetState cfg model U gVec lVec).chain 0) tok.intCap heap4)
    (hR14_4 : s4.mem (root + 14) = newRootGraph) (hR11_4 : s4.mem (root + 11) = 0)
    (hRG4 : DynGraphAt s4.mem newRootGraph vCap eCap ((alg2PreResetState cfg model U gVec lVec).chain.G 0))
    (hSlots4 : ∀ e < tok.intCap, s4.mem (tok.slots + e) = 0)
    (hZeroIn4 : ∀ e < tok.intCap, s4.mem (tok.inOffReady + e) = 0)
    (hOffInv4 : OffReadyInv s4.mem 0 tok.offReadyList tok.inOffReady tok.intCap)
    (hTreeN1 : curTree1.n = model.extG.n)
    (hLct1 : LctInvWith pathPayload curTree1 curTrees1 curFree1 curDepth1)
    (hNum1 : PathTreeNumericInv curTree1 curTrees1 B R)
    (hNoEdgeSlots1 : ∀ sl ∈ curTrees1.flatMap AuxTree.toList, ¬ isEdgeSlot curTree1.n sl)
    (hTreeRep4 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree1 curTreeTok1 s4.mem)
    (hTreeFoot1 : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap1 ≤ a ∧ a < heapSync))
    (hCanon4 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch tr.2.2.2.2
      ∀ e ∈ model.extG.E,
        let eiOld := tr.2.1 e
        let eiNew := level0E2I true G0' tr.2.1 e
        let v := newCanonVal eiOld
        eiNew < G0'.m ∧ compactUnrank G0'.E eiNew = eiOld ∧
        PathIntAt s4.mem (s4.mem (tok.edgeThresholds + eiNew)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt s4.mem (s4.mem (tok.edgeRecords + eiNew)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (eiOld ∈ G0.E →
          s4.mem (tok.edgeThresholds + eiNew) = mem0 (tok.edgeThresholds + eiOld) ∧
          ((eiOld ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ s4.mem (tok.edgeRecords + eiNew) ∧
              s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, s4.mem (tok.edgeRecords + eiNew) ≤ a →
                a < s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
                ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a) ∧
           (eiOld ∉ model.chain.toTreeChain.chainTree.E →
              s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + eiOld)))) ∧
        (eiOld ∉ G0.E →
          heapSync + 3 * L ≤ s4.mem (tok.edgeThresholds + eiNew) ∧
          s4.mem (tok.edgeThresholds + eiNew) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + eiNew) ∧
          s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2))
    (hOffDisj4 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
        s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁) + (2 + 4 * L) ≤
          s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁))
    (hs4_root : ∀ j < 16, j ≠ 11 → j ≠ 14 → s4.mem (root + j) = mem0 (root + j))
    (hs4_hdr : ∀ j < 18, s4.mem (tok.handle + j) = mem0 (tok.handle + j))
    (hSync2Room :
      let sumNew := graphListEdgeSum (chainSuffixForests (alg2PreResetState cfg model U gVec lVec).chain 0)
      heap4 + (3 * tok.intCap + sumNew * (2 + wireTreeSyncEditSpace L)) < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
    let newF := modelPre.chain.toTreeChain.chainTree
    let canonC : ℕ → PathEdgeValue := fun j => newCanonVal (compactUnrank G0'.E j)
    ∃ (s5g : State) (cost nextHeap : ℕ) (curTree2 : PathTreeState)
      (curTrees2 : List AuxTree) (curFree2 : List ℕ) (curDepth2 : ℕ → ℕ)
      (curTreeTok2 : Rtree.τ),
      Runs w p ω
        (wireBranchASync2LoopStmt packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
        s4 .normal s5g cost ∧
      s5g.regs 3 = nextHeap ∧ s5g.regs 70 = root ∧
      heap4 ≤ nextHeap ∧ nextHeap ≤ heap4 + (3 * tok.intCap + sumNew * (2 + wireTreeSyncEditSpace L)) ∧
      ZeroFrom s5g.mem nextHeap ∧
      curTree2.n = model.extG.n ∧
      LctInvWith pathPayload curTree2 curTrees2 curFree2 curDepth2 ∧
      PathTreeNumericInv curTree2 curTrees2 B R ∧
      TreeEditNamedSlots curTree2 curTrees2 newF
        (fun ei => s5g.mem (tok.slots + ei)) (fun sl => s5g.mem (tok.names + sl)) ∧
      TreeEditLiveAccounts curTree2 curTrees2 newF
        (fun ei => s5g.mem (tok.slots + ei)) canonC ∧
      Rtree.rep tok.treeHeap curTree2 curTreeTok2 s5g.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok2 a →
        Rtree.foot tok.treeHeap curTreeTok1 a ∨ (heap4 ≤ a ∧ a < nextHeap)) ∧
      (∀ ei ∈ newF.E, s5g.mem (tok.slotThresholds + s5g.mem (tok.slots + ei)) =
        s5g.mem (tok.edgeThresholds + ei)) ∧
      (∀ ei ∈ (modelPre.chain.G 0).E, ei ∉ newF.E → s5g.mem (tok.slots + ei) = 0) ∧
      (∀ ei ∈ (modelPre.chain.G 0).E, ei ∉ newF.E →
        PathEdgeAt s5g.mem (s5g.mem (tok.edgeRecords + ei)) 4 L (some (canonC ei)) ∧
        s5g.mem (tok.edgeRecords + ei) = s4.mem (tok.edgeRecords + ei)) ∧
      (∀ e₁ ∈ (modelPre.chain.G 0).E, ∀ e₂ ∈ (modelPre.chain.G 0).E, e₁ ≠ e₂ →
        e₁ ∉ newF.E → e₂ ∉ newF.E →
        s5g.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ s5g.mem (tok.edgeRecords + e₂) ∨
        s5g.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ s5g.mem (tok.edgeRecords + e₁)) ∧
      s5g.mem (root + 11) = 0 ∧
      OffReadyInv s5g.mem 0 tok.offReadyList tok.inOffReady tok.intCap ∧
      (∀ a < heap4, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
          tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
          s5g.mem a = s4.mem a) ∧
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok1 a → s5g.mem a = s4.mem a)) ∧
      cost + Rtree.phi tok.treeHeap curTreeTok2 s5g.mem ≤
        (230 * (d + 1) + 85 * sumNew + 260) +
        sumNew * (wireTreeSyncEditCost L drainUnit + 2) + 20 +
        Rtree.phi tok.treeHeap curTreeTok1 s4.mem := by
  classical
  dsimp only
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let d := cfg.P.d
  let cnt := d + 1
  let arrBase := heap + 1 + 12 * d
  let newPtrs := arrBase + cnt
  let emptyPtrs := arrBase + 2 * cnt
  let emptyGraphPtr := arrBase + 3 * cnt
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
  let newF := modelPre.chain.toTreeChain.chainTree
  have hRep0_keep := hRep0
  obtain ⟨hRootDir0, hDetHdr0, _, _, hFreshInv0, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, hT14, hT15,
    hT16, hT1718, _, _, _⟩ := hTags0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo⟩ := hHeaps
  obtain ⟨hr4_4, hr70_4, hr73_4, hr79_4, hr81_4, hr92_4⟩ := hRegs4
  obtain ⟨hTr1Eq, hFreshTr, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 hRef
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  -- Exact algebraic identities for `modelPre`
  have hPreExtG : modelPre.extG = model.extG := by dsimp [modelPre, alg2PreResetState]; exact hTr1Eq
  have hPreE2I : modelPre.extToInt = level0E2I true G0' tr.2.1 := by
    have hR : Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount
        (Chain.Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
          tr.2.2.2.2 (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1.rebuildCount = true := hRenTrue
    dsimp [modelPre, alg2PreResetState]; rw [hR]
  have hPreG0 : modelPre.chain.G 0 = G0'.compact := by
    rw [hChPreEq]; exact (ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P _ hdPos _ _).2.1
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := by
    have hUp := Chain.Ordered.update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
      gVec lVec hFreshTr
    rw [hPreExtG]
    simpa [modelPre, alg2PreResetState] using hUp.1
  have hPreG0n : (modelPre.chain.G 0).n = model.extG.n := by
    unfold MGraph.n; rw [← hFreshPre.hV, hPreExtG]
  have hPreG0Cap : ∀ e ∈ (modelPre.chain.G 0).E, e < tok.intCap := fun e he => by
    rw [hPreG0] at he; have hlt : e < G0'.m := by simpa [MGraph.compact, MGraph.m] using he
    exact lt_of_lt_of_le hlt hG0'mLeR.2
  -- Pack `∅ → newF` via `wireSuffixPackEditsBody`
  let editsBuf := heap4 + 3 * tok.intCap
  let s5a := { s4 with regs := Function.update s4.regs 10 tok.intCap }
  let s5b := { s5a with regs := Function.update s5a.regs 6 editsBuf }
  have hr5a : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 15)))) s4 .normal s5a 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by
      simp [Expr.eval, BinOp.eval, hr70_4, show 15 < 2 ^ w by omega,
        show root + 15 < 2 ^ w by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega,
        hs4_root 15 (by omega) (by decide) (by decide), show mem0 (root + 15) = tok.intCap by simpa using hRootDir0 15 (by simp)],
      rfl, rfl, rfl⟩
  have hr5b : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10)))) s5a .normal s5b 6 :=
    runs_assign_iff.mpr ⟨editsBuf, by
      have hW : heap4 + 3 * tok.intCap < 2 ^ w := by dsimp only [sumNew, modelPre] at hSync2Room ⊢; omega
      simp [Expr.eval, BinOp.eval, s5a, hr4_4, show 3 < 2 ^ w by omega,
        show 3 * tok.intCap < 2 ^ w by omega, hW, editsBuf],
      rfl, rfl, rfl⟩
  have hEmptyForests4 : ForestPtrListAt s4.mem emptyPtrs (List.replicate cnt emptyZeroGraph) tok.intCap heap4 := by
    refine ⟨by simp [emptyPtrs, arrBase, cnt]; omega, fun j hj => ?_⟩
    have hj' : j < cnt := by simpa using hj
    refine ⟨0, 0, ?_, ?_, fun _ he => by simp [emptyZeroGraph] at he⟩
    · rw [hEmptyPtrs4 j hj', List.getElem_replicate hj]
      exact emptyZeroGraph_dynGraphAt (fun t ht => hEmptyG4 t ht)
    · rw [hEmptyPtrs4 j hj']; unfold dynGraphSize; omega
  have hPackRoom : heap4 + 3 * tok.intCap +
      2 * (graphListEdgeSum (List.replicate cnt emptyZeroGraph) + sumNew) < 2 ^ w := by
    rw [graphListEdgeSum_replicate_empty, zero_add]
    have h2 : 2 * sumNew ≤ sumNew * (2 + wireTreeSyncEditSpace L) := by
      rw [Nat.mul_add, Nat.mul_comm 2]; exact Nat.le_add_right _ _
    dsimp only [sumNew, modelPre] at hSync2Room h2 ⊢; omega
  obtain ⟨outPack, cPack, edits2, rPackBody, hcPack, hEdits2Le, hEditsAt2, hDiff2Raw, hzPack, hFrPack⟩ :=
    wireSuffixPackEdits_runs (w := w) (oldPtrs := emptyPtrs) (newPtrs := newPtrs) (cnt := cnt)
      (intCap := tok.intCap) (heap := heap4) (pos := s5b.pos)
      (oldFs := List.replicate cnt emptyZeroGraph) (newFs := chainSuffixForests modelPre.chain 0)
      (p := p) (ω := ω) (mem := s5b.mem)
      List.length_replicate (chainSuffixForests_length modelPre.chain 0)
      hEmptyForests4 hNewForests4 hz4 hPackRoom (by omega)
  rw [graphListEdgeSum_replicate_empty, zero_add] at hcPack hEdits2Le
  have hNewUnionEq : graphListEdgeUnion (chainSuffixForests modelPre.chain 0) = newF.E := by
    have := chainTree_E_eq_prefix_union_suffix modelPre.chain (Nat.zero_le _)
    simpa [newF] using this.symm
  have hDiff2 : TreeEditDifference ∅ newF.E edits2 := by
    rwa [graphListEdgeUnion_replicate_empty, hNewUnionEq] at hDiff2Raw
  let s5c : State := { regs := Function.update s5b.regs 18 edits2.length, mem := outPack.mem, pos := outPack.pos }
  have hr5c : Runs w p ω (.call 18 packEditsProc [.reg 92, .reg 81, .reg 79, .reg 10, .reg 4])
      s5b .normal s5c (5 + cPack + 1) :=
    runs_call_iff.mpr ⟨[emptyPtrs, newPtrs, cnt, tok.intCap, heap4], wireSuffixPackEditsBody,
      .returned edits2.length, outPack, cPack,
      by simp [evalArgs, Expr.eval, s5b, s5a, hr92_4, hr81_4, hr79_4, hr4_4, emptyPtrs, newPtrs, arrBase, cnt, d],
      hPackProc, rPackBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- `shiftTermSetupLoop`
  let s5d := { s5c with regs := Function.update s5c.regs 27 root }
  let s5e := { s5d with regs := Function.update s5d.regs 29 tok.handle }
  have hr5d : Runs w p ω (.assign 27 (.reg 70)) s5c .normal s5d 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s5c, s5b, s5a, hr70_4], rfl, rfl, rfl⟩
  have hr5e : Runs w p ω (.assign 29 (.reg 73)) s5d .normal s5e 2 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s5d, s5c, s5b, s5a, hr73_4], rfl, rfl, rfl⟩
  have hULeH4 : uIntBuf ≤ heap4 := by omega
  have h5eEq4 (a : ℕ) (ha : a < heap4) : s5e.mem a = s4.mem a := hFrPack a ha
  have hRG5e : DynGraphAt s5e.mem newRootGraph vCap eCap (modelPre.chain.G 0) :=
    dynGraphAt_of_agree hRG4 (fun a ha1 ha2 => h5eEq4 a (by omega))
  let heap0S2 := editsBuf + 2 * edits2.length
  have hSync2Room' : heap0S2 + edits2.length * wireTreeSyncEditSpace L < 2 ^ w := by
    have h1 : 2 * edits2.length + edits2.length * wireTreeSyncEditSpace L =
        edits2.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits2.length * (2 + wireTreeSyncEditSpace L) ≤
        sumNew * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEdits2Le
    dsimp only [heap0S2, editsBuf, sumNew, modelPre] at hSync2Room h2 ⊢; omega
  obtain ⟨s5f, cSetup, rSetup, hcSetup, hs5fMem, h5f_0, h5f_1, h5f_2, h5f_3, h5f_6, h5f_18,
      h5f_9, h5f_10, h5f_11, h5f_19, h5f_20, h5f_22, h5f_23, h5f_24, h5f_25, h5f_26⟩ :=
    shiftTermSetupLoop_runs (w := w) (p := p) (ω := ω) (st := s5e) (editPtr := editsBuf) (nEdits := edits2.length)
      (root := root) (handle := tok.handle) (by simp [s5e, s5d, s5c, s5b])
      (by simp [s5e, s5d, s5c]) (by simp [s5e, s5d]) (by simp [s5e])
      ((h5eEq4 _ (by have := htagLt (by rw [hT2 0 (by omega)]; decide); omega)).trans
        ((hs4_hdr 0 (by omega)).trans (by simpa using hDetHdr0 0 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT2 5 (by omega)]; decide); omega)).trans
        ((hs4_hdr 5 (by omega)).trans (by simpa using hDetHdr0 5 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 14 (by omega)]; decide); omega)).trans hR14_4)
      (by simpa [dgVCapOff] using hRG5e.2.2.2.1)
      (by simpa [dgECapOff] using hRG5e.2.2.2.2.1)
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 6 (by omega)]; decide); omega)).trans
        ((hs4_root 6 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 6 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 7 (by omega)]; decide); omega)).trans
        ((hs4_root 7 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 7 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 8 (by omega)]; decide); omega)).trans
        ((hs4_root 8 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 8 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 9 (by omega)]; decide); omega)).trans
        ((hs4_root 9 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 9 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 10 (by omega)]; decide); omega)).trans
        ((hs4_root 10 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 10 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 12 (by omega)]; decide); omega)).trans
        ((hs4_root 12 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 12 (by simp))))
      ((h5eEq4 _ (by have := htagLt (by rw [hT1 13 (by omega)]; decide); omega)).trans
        ((hs4_root 13 (by omega) (by decide) (by decide)).trans (by simpa using hRootDir0 13 (by simp))))
      (by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega)
      (by have := htagLt (by rw [hT2 5 (by omega)]; decide); omega)
      (by dsimp only [heap0S2, editsBuf] at hSync2Room'; omega)
      (by omega)
  -- Build `tokMid` and `WireSyncCtx`
  let canonC : ℕ → PathEdgeValue := fun j => newCanonVal (compactUnrank G0'.E j)
  let tokMid : SolverToken cfg L Rcore :=
    { tok with
      offReadyCount := 0
      rootGraph := newRootGraph
      tree := curTree1, trees := curTrees1, free := curFree1, depth := curDepth1, treeTok := curTreeTok1
      owned := fun a => a < heap4
      tag := fun a =>
        if a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
            tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15) then tok.tag a
        else if Rtree.foot tok.treeHeap curTreeTok1 a then 16
        else if newRootGraph ≤ a ∧ a < newRootGraph + dynGraphSize vCap eCap then 20
        else if ∃ e ∈ model.extG.E,
            let eiNew := level0E2I true G0' tr.2.1 e
            s4.mem (tok.edgeRecords + eiNew) ≤ a ∧ a < s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) then 18
        else 0 }
  have hMidTagBasic {a v : ℕ} (ht : tok.tag a = v)
      (hv : v = 1 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15) :
      tokMid.tag a = v := by
    have hlt : a < uIntBuf := htagLt (by rw [ht]; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hcond : a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15) := ⟨hlt, ht ▸ hv⟩
    dsimp only [tokMid]; rw [ite_eq_left_iff.mpr fun h => (h hcond).elim, ht]
  have hMidTag16 (a : ℕ) (ha : Rtree.foot tok.treeHeap curTreeTok1 a) : tokMid.tag a = 16 := by
    have hnotB : ¬ (a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15)) := by
      rintro ⟨hlt, htag⟩
      rcases hTreeFoot1 a ha with h0 | ⟨hlo, _⟩
      · have h16 := hT16 a h0; rcases htag with h | h | h | h | h | h | h | h <;> omega
      · omega
    dsimp only [tokMid]; simp only [hnotB, ha, ↓reduceIte]
  have hMidTag20 (a : ℕ) (ha1 : newRootGraph ≤ a) (ha2 : a < newRootGraph + dynGraphSize vCap eCap) :
      tokMid.tag a = 20 := by
    have hnot16 : ¬ Rtree.foot tok.treeHeap curTreeTok1 a := fun hf => by
      rcases hTreeFoot1 a hf with h0 | ⟨_, hhi⟩
      · have := htagLt (by rw [hT16 a h0]; decide); omega
      · omega
    have hnotB : ¬ (a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15)) := fun ⟨h, _⟩ => by omega
    dsimp only [tokMid]
    rw [ite_eq_right_iff.mpr fun h => (hnotB h).elim,
        ite_eq_right_iff.mpr fun h => (hnot16 h).elim]
    exact ite_eq_left_iff.mpr fun h => (h ⟨ha1, ha2⟩).elim
  have hMidTag18 (e : ℕ) (he : e ∈ model.extG.E) (j : ℕ) (hj : j < 2 + 4 * L) :
      tokMid.tag (s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + j) = 18 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hInG0, hNotG0⟩ := hCanon4 e he
    let eiNew := level0E2I true G0' tr.2.1 e
    let a := s4.mem (tok.edgeRecords + eiNew) + j
    have hOldEq (hOld : tr.2.1 e ∈ G0.E) : model.extToInt e = tr.2.1 e := by
      by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
      · exact False.elim ((hDichRep e he hRepE).2.2.2.1 hOld)
      · exact (hDichUnch e he hRepE).2.1.symm
    have hnotB : ¬ (a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15)) := by
      rintro ⟨hlt, htag⟩
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨hlo, _, _⟩ := (hInG0 hOld).2.1 hTree
          change heap1 ≤ s4.mem (tok.edgeRecords + eiNew) at hlo; omega
        · have hPtr : s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
          have heOld := hOldEq hOld
          have h18 : tok.tag a = 18 := by
            dsimp only [a]; rw [hPtr, ← heOld]; exact (hT1718 e he).2 (heOld.symm ▸ hTree) j hj
          rcases htag with h | h | h | h | h | h | h | h <;> omega
      · obtain ⟨_, _, hlo, _⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + eiNew) at hlo; omega
    have hnot16 : ¬ Rtree.foot tok.treeHeap curTreeTok1 a := by
      intro hf
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨_, _, hnf⟩ := (hInG0 hOld).2.1 hTree
          change ∀ x, s4.mem (tok.edgeRecords + eiNew) ≤ x →
            x < s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
            ¬ Rtree.foot tok.treeHeap curTreeTok1 x at hnf
          exact hnf a (by omega) (by omega) hf
        · have hPtr : s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
          have heOld := hOldEq hOld
          have h18 : tok.tag a = 18 := by
            dsimp only [a]; rw [hPtr, ← heOld]; exact (hT1718 e he).2 (heOld.symm ▸ hTree) j hj
          rcases hTreeFoot1 a hf with h0 | ⟨hlo, _⟩
          · have h16 := hT16 a h0; omega
          · have := htagLt (by rw [h18]; decide); omega
      · obtain ⟨_, _, hlo, _⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + eiNew) at hlo
        rcases hTreeFoot1 a hf with h0 | ⟨_, hhi⟩
        · have := htagLt (by rw [hT16 a h0]; decide); omega
        · omega
    have hnot20 : ¬ (newRootGraph ≤ a ∧ a < newRootGraph + dynGraphSize vCap eCap) := by
      rintro ⟨hlo20, _⟩
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨_, hhi, _⟩ := (hInG0 hOld).2.1 hTree
          change s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync at hhi; omega
        · have hPtr : s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
          have heOld := hOldEq hOld
          have h18 : tok.tag a = 18 := by
            dsimp only [a]; rw [hPtr, ← heOld]; exact (hT1718 e he).2 (heOld.symm ▸ hTree) j hj
          have := htagLt (by rw [h18]; decide); omega
      · obtain ⟨_, _, _, hhi⟩ := hNotG0 hOld
        change s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2 at hhi; omega
    have h18ex : ∃ e' ∈ model.extG.E,
        let eiNew' := level0E2I true G0' tr.2.1 e'
        s4.mem (tok.edgeRecords + eiNew') ≤ a ∧ a < s4.mem (tok.edgeRecords + eiNew') + (2 + 4 * L) :=
      ⟨e, he, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩
    dsimp only [tokMid]
    rw [ite_eq_right_iff.mpr fun h => (hnotB h).elim,
        ite_eq_right_iff.mpr fun h => (hnot16 h).elim,
        ite_eq_right_iff.mpr fun h => (hnot20 h).elim]
    exact ite_eq_left_iff.mpr fun h => (h h18ex).elim
  have hMidTagLt (a : ℕ) (hne : tokMid.tag a ≠ 0) : a < heap4 := by
    dsimp only [tokMid] at hne
    split_ifs at hne with h1 h2 h3 h4
    · omega
    · rcases hTreeFoot1 a h2 with h0 | ⟨_, hhi⟩
      · have := htagLt (by rw [hT16 a h0]; decide); omega
      · omega
    · omega
    · obtain ⟨e, he, ha1, ha2⟩ := h4
      let eiNew := level0E2I true G0' tr.2.1 e
      change s4.mem (tok.edgeRecords + eiNew) ≤ a at ha1
      change a < s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) at ha2
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hInG0, hNotG0⟩ := hCanon4 e he
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨_, hhi, _⟩ := (hInG0 hOld).2.1 hTree
          change s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync at hhi; omega
        · have hPtr : s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
          have heOld : model.extToInt e = tr.2.1 e := by
            by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
            · exact False.elim ((hDichRep e he hRepE).2.2.2.1 hOld)
            · exact (hDichUnch e he hRepE).2.1.symm
          have h18 : tok.tag a = 18 := by
            have := (hT1718 e he).2 (heOld.symm ▸ hTree) (a - mem0 (tok.edgeRecords + tr.2.1 e)) (by omega)
            rwa [heOld, show mem0 (tok.edgeRecords + tr.2.1 e) + (a - mem0 (tok.edgeRecords + tr.2.1 e)) = a by omega] at this
          have := htagLt (by rw [h18]; decide); omega
      · obtain ⟨_, _, _, hhi⟩ := hNotG0 hOld
        change s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2 at hhi; omega
    · exact (hne rfl).elim
  have h2nW : 2 * (modelPre.chain.G 0).n + 1 < 2 ^ w := by
    rw [hPreG0n]
    by_cases hn0 : model.extG.n = 0
    · omega
    · have hEnd : tok.names + 2 * tok.tree.n ≤ uIntBuf := by
        have := htagLt (by rw [hT10 (2 * tok.tree.n - 1) (by omega)]; decide); omega
      omega
  have hTreeHeapLt : tok.treeHeap < 2 ^ w :=
    lt_trans (htagLt (by rw [hT16 tok.treeHeap (pathRep_foot_base_s2 hRep0_keep.2.2.2.2.2.2.2.2.2.2.2.2.1)]; decide)) (by omega)
  let emptyF : MGraph := { modelPre.chain.G 0 with E := ∅ }
  let ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editsBuf heap0S2 s5f.mem (modelPre.chain.G 0) emptyF newF edits2 tokMid canonC B R :=
    { fmtBits := hFmtBits, hw11 := by omega, treeImpl := hTreeImpl, bindOk := hBindOk,
      canonOk := hCanonOk, isNegOk := hIsNegOk, treeHeapLt := hTreeHeapLt, nW := h2nW,
      logW := hPreG0n.symm ▸ hLogW, capT := hPreG0n.symm ▸ hCapT, diff := hDiff2,
      oldSub := Finset.empty_subset _, newSub := hNewSub, newForest := hNewForest,
      oldEnds := fun _ h => (Finset.notMem_empty _ h).elim,
      newEnds := fun _ _ => ⟨rfl, rfl⟩,
      vtxE := fun ei hei => by
        obtain ⟨h1, h2⟩ := hRG5e.1 ei hei
        exact ⟨hPreG0n.symm ▸ (hvCapEq ▸ hRG5e.2.1 _ h1), hPreG0n.symm ▸ (hvCapEq ▸ hRG5e.2.1 _ h2)⟩,
      capE := hPreG0Cap,
      rootGraph := by rw [hPreG0n, ← hvCapEq, ← heCapEq]; exact hs5fMem.symm ▸ hRG5e,
      editsAt := hs5fMem.symm ▸ hEditsAt2, editsEnd := le_rfl,
      editsTag0 := fun a ha1 _ => ⟨by by_contra hne; have := hMidTagLt a hne; dsimp [editsBuf] at ha1; omega,
        by have := htagLt (by rw [hT1 11 (by omega)]; decide); dsimp [editsBuf] at ha1; omega⟩,
      tags := by
        refine ⟨fun a h => lt_of_lt_of_le (hMidTagLt a h) (by dsimp [heap0S2, editsBuf]; omega),
          fun j hj => hMidTagBasic (hT1 j hj) (Or.inl rfl),
          fun j hj => hMidTagBasic (hT9 j hj) (Or.inr (Or.inl rfl)),
          fun sl hsl => hMidTagBasic (hT10 sl (by omega)) (Or.inr (Or.inr (Or.inl rfl))),
          fun sl hsl => hMidTagBasic (hT11 sl (by omega)) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          fun j hj => hMidTagBasic (hT12 j hj) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
          fun j hj => hMidTagBasic (hT13 j hj) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
          fun j hj => hMidTagBasic (hT14 j hj) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
          fun j hj => hMidTagBasic (hT15 j hj) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))),
          hMidTag16, fun ei hei _ j hj => ?_, fun a ha1 ha2 =>
            hMidTag20 a ha1 (by rw [hvCapEq, heCapEq, ← hPreG0n]; exact ha2)⟩
        obtain ⟨heMap, heExt⟩ := hFreshPre.hRight ei hei
        have hEqRec : s5f.mem (tok.edgeRecords + ei) = s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 (modelPre.intToExt ei)) := by
          rw [hs5fMem, h5eEq4 _ (by have := htagLt (by rw [hT13 ei (hPreG0Cap ei hei)]; decide); omega), ← hPreE2I, heMap]
        rw [hEqRec]; exact hMidTag18 (modelPre.intToExt ei) (hPreExtG ▸ heExt) j hj,
      canonProp := fun ei hei => by
        obtain ⟨heMap, heExt⟩ := hFreshPre.hRight ei hei
        obtain ⟨_, hUnr, _, _, hvf, hvg, hvl, hvfl, hvd, _⟩ := hCanon4 (modelPre.intToExt ei) (hPreExtG ▸ heExt)
        rw [← hPreE2I, heMap] at hUnr
        have hEq : canonC ei = newCanonVal (tr.2.1 (modelPre.intToExt ei)) := by dsimp [canonC]; rw [hUnr]
        rw [hEq]; exact ⟨hvf, hvg, hvl, hvfl, hvd⟩,
      room := hSync2Room' }
  have hTreeLoc5f := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC)
    tok.treeHeap curTree1 curTreeTok1 s4.mem s5f.mem
    (fun a ha => by rw [hs5fMem]; exact (h5eEq4 a (hMidTagLt a (by rw [hMidTag16 a ha]; decide))).symm)
  have hInvInit : WireSyncDeferInv (modelPre.chain.G 0).E root editsBuf heap0S2 s5f.mem
      (modelPre.chain.G 0) emptyF newF edits2 tokMid canonC B R
      [] edits2 curTree1 curTreeTok1 heap0S2 0 s5f := by
    refine ⟨rfl, h5f_0, h5f_1, h5f_2, h5f_3, by simpa using h5f_6, h5f_18,
      by rw [hPreG0n, ← hvCapEq, ← heCapEq]; exact h5f_9,
      by rw [hPreG0n, ← hvCapEq, ← heCapEq]; exact h5f_10,
      by rw [hPreG0n, ← hvCapEq]; exact h5f_11,
      h5f_19, h5f_20, h5f_22, h5f_23, h5f_24, h5f_25, h5f_26,
      le_rfl, by simp, hs5fMem.symm ▸ hzPack, fun a ha => Or.inl ha,
      fun _ _ _ _ _ _ _ _ _ _ => rfl, hTreeN1.trans hPreG0n.symm,
      ⟨curTrees1, curFree1, curDepth1, hLct1, hNum1,
        ⟨fun _ h => (Finset.notMem_empty _ h).elim,
         fun sl hsl his => (hNoEdgeSlots1 sl hsl his).elim,
         fun _ h => (Finset.notMem_empty _ h).elim⟩,
        fun _ h => (Finset.notMem_empty _ h).elim⟩,
      hTreeLoc5f.1 hTreeRep4,
      fun _ h => (Finset.notMem_empty _ h).elim,
      fun ei hei _ => by
        dsimp only [tokMid]
        rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT9 ei (hPreG0Cap ei hei)]; decide)) hULeH4)]
        exact hSlots4 ei (hPreG0Cap ei hei),
      fun ei hei _ => by
        dsimp only [tokMid]
        obtain ⟨heMap, heExt⟩ := hFreshPre.hRight ei hei
        have hRec := (hCanon4 (modelPre.intToExt ei) (hPreExtG ▸ heExt)).2.2.2.1
        have hUnr := (hCanon4 (modelPre.intToExt ei) (hPreExtG ▸ heExt)).2.1
        rw [← hPreE2I, heMap] at hRec hUnr
        rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT13 ei (hPreG0Cap ei hei)]; decide)) hULeH4)]
        have hEqV : canonC ei = newCanonVal (tr.2.1 (modelPre.intToExt ei)) := by dsimp [canonC]; rw [hUnr]
        rw [hEqV]
        exact hRec.congr (fun a ha1 ha2 =>
          h5eEq4 a (hMidTagLt a (by
            have h18 := hMidTag18 (modelPre.intToExt ei) (hPreExtG ▸ heExt) (a - s4.mem (tok.edgeRecords + ei)) (by omega)
            rw [← hPreE2I, heMap, show s4.mem (tok.edgeRecords + ei) + (a - s4.mem (tok.edgeRecords + ei)) = a by omega] at h18
            rw [h18]; decide))),
      fun _ hei _ hnd => (hnd hei).elim,
      fun _ _ _ => ⟨fun h => (Finset.notMem_empty _ h).elim, fun _ => rfl⟩,
      fun e1 he1 e2 he2 hne _ _ => by
        dsimp only [tokMid]
        obtain ⟨hm1, hx1⟩ := hFreshPre.hRight e1 he1
        obtain ⟨hm2, hx2⟩ := hFreshPre.hRight e2 he2
        have hneX : modelPre.intToExt e1 ≠ modelPre.intToExt e2 := fun h => hne (hm1.symm.trans (h ▸ hm2))
        rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT13 e1 (hPreG0Cap e1 he1)]; decide)) hULeH4),
            h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT13 e2 (hPreG0Cap e2 he2)]; decide)) hULeH4)]
        have hDisj := hOffDisj4 _ (hPreExtG ▸ hx1) _ (hPreExtG ▸ hx2) hneX
        rw [← hPreE2I, hm1, hm2] at hDisj
        exact hDisj,
      by rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT1 11 (by omega)]; decide)) hULeH4)]; exact hR11_4,
      by
        dsimp only [tokMid]
        obtain ⟨hc, _, _, h3', _⟩ := hOffInv4
        refine ⟨hc, fun _ h => by omega, fun _ h => by omega, fun e he => by
          rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT15 e he]; decide)) hULeH4)]; exact h3' e he,
          fun e he h1 => by
            rw [hs5fMem, h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT15 e he]; decide)) hULeH4)] at h1
            have h0 := hZeroIn4 e he; omega⟩⟩
  obtain ⟨s5g, cLoop, curTree2, curTreeTok2, nextHeap, rLoop, hInvEnd, hcLoop⟩ :=
    wireTreeSyncLoop_insertOnly_defer_runs ctx hInvInit (treeEditDiff_empty_all_insert hDiff2)
  obtain ⟨_, _, _, _, hr3_5g, _, _, _, _, _, _, _, _, _, _, _, _,
    hNextGe0, hNextLe0, hzNext, hFootEnd, hFrameEnd, hTreeNEnd,
    ⟨curTrees2, curFree2, curDepth2, hLctEnd, hNumEnd, hNamedEnd, hLiveEnd⟩,
    hTreeRepEnd, hSlotThrEnd, hOffSlotEnd, hOffRecEnd, _, hOffWhereEnd, hOffDisjEnd,
    hOffCnt5g, hOffReady5g⟩ := hInvEnd
  rw [hDiff2.result.2] at hNamedEnd hLiveEnd hSlotThrEnd hOffSlotEnd hOffRecEnd hOffWhereEnd hOffDisjEnd
  have hGraphEq : ({ modelPre.chain.G 0 with E := newF.E } : MGraph) = newF := by
    show MGraph.mk (modelPre.chain.G 0).V newF.E (modelPre.chain.G 0).tail (modelPre.chain.G 0).head =
      MGraph.mk newF.V newF.E newF.tail newF.head
    rfl
  have h5g_70 : s5g.regs 70 = root := by
    have hnwLoop : stmtNoWriteGe 70 (wireTreeSyncLoop (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg) := by
      simp [wireTreeSyncLoop, wireTreeSyncStep, wireTreeSyncInsert, wireTreeSyncDelete, stmtNoWriteGe]
    have hnwSetup : stmtNoWriteGe 70 shiftTermSetupLoop := by
      simp [shiftTermSetupLoop, stmtNoWriteGe]
    rw [runs_regs_ge_of_noWriteGe rLoop hnwLoop 70 le_rfl,
      runs_regs_ge_of_noWriteGe rSetup hnwSetup 70 le_rfl]
    simp [s5e, s5d, s5c, s5b, s5a, hr70_4]
  have rLoopAll :=
    runs_seq_iff.mpr (Or.inr ⟨s5a, 5, _, hr5a,
    runs_seq_iff.mpr (Or.inr ⟨s5b, 6, _, hr5b,
    runs_seq_iff.mpr (Or.inr ⟨s5c, 5 + cPack + 1, _, hr5c,
    runs_seq_iff.mpr (Or.inr ⟨s5d, 2, _, hr5d,
    runs_seq_iff.mpr (Or.inr ⟨s5e, 2, _, hr5e,
    runs_seq_iff.mpr (Or.inr ⟨s5f, cSetup, cLoop, rSetup, rLoop, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨s5g, _, nextHeap, curTree2, curTrees2, curFree2, curDepth2, curTreeTok2,
    rLoopAll, hr3_5g, h5g_70,
    le_trans (by dsimp [heap0S2, editsBuf]; omega) hNextGe0,
    by
      have h1 : 2 * edits2.length + edits2.length * wireTreeSyncEditSpace L =
          edits2.length * (2 + wireTreeSyncEditSpace L) := by ring
      have h2 : edits2.length * (2 + wireTreeSyncEditSpace L) ≤
          sumNew * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEdits2Le
      dsimp only [heap0S2, editsBuf, sumNew, modelPre] at hNextLe0 h2 ⊢; omega,
    hzNext, hTreeNEnd.trans hPreG0n, hLctEnd, hNumEnd,
    by rwa [hGraphEq] at hNamedEnd, by rwa [hGraphEq] at hLiveEnd, hTreeRepEnd,
    fun a ha => by
      rcases hFootEnd a ha with h1 | ⟨hlo, hhi⟩
      · exact Or.inl h1
      · exact Or.inr ⟨le_trans (by dsimp [heap0S2, editsBuf]; omega) hlo, hhi⟩,
    hSlotThrEnd, hOffSlotEnd,
    fun ei hei hnot => ⟨hOffRecEnd ei hei hnot,
      ((hOffWhereEnd ei hei hnot).2 (Finset.notMem_empty _)).trans
        (hs5fMem.symm ▸ h5eEq4 _ (lt_of_lt_of_le (htagLt (by rw [hT13 ei (hPreG0Cap ei hei)]; decide)) hULeH4))⟩,
    hOffDisjEnd, hOffCnt5g, hOffReady5g, ?_, ?_⟩
  · intro a ha hne11
    refine ⟨fun hlt h9 h10 h11 h13 h14 h15 h16 => ?_, fun hge hnf1 => ?_⟩
    · have hneM (u : ℕ) (hu : u = 9 ∨ u = 10 ∨ u = 11 ∨ u = 13 ∨ u = 14 ∨ u = 15 ∨ u = 16)
          (hvu : tok.tag a ≠ u) : tokMid.tag a ≠ u := by
        dsimp only [tokMid]; split_ifs with hA hB hC hD
        · exact hvu
        · by_cases h16u : u = 16
          · subst h16u
            rcases hTreeFoot1 a hB with h0 | ⟨hlo, _⟩
            · exact (h16 (hT16 a h0)).elim
            · omega
          · exact Ne.symm h16u
        · omega
        · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hFrameEnd a (by dsimp [heap0S2, editsBuf]; omega) hne11
        (hneM 9 (by omega) h9) (hneM 10 (by omega) h10) (hneM 11 (by omega) h11)
        (hneM 13 (by omega) h13) (hneM 14 (by omega) h14) (hneM 15 (by omega) h15)
        (hneM 16 (by omega) h16)).trans (hs5fMem.symm ▸ h5eEq4 a ha)
    · have hneM (u : ℕ) (hu : u = 9 ∨ u = 10 ∨ u = 11 ∨ u = 13 ∨ u = 14 ∨ u = 15 ∨ u = 16) :
          tokMid.tag a ≠ u := by
        have hnotA : ¬ (a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
            tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15)) := fun ⟨h, _⟩ => by omega
        dsimp only [tokMid]
        simp only [hnotA, ↓reduceIte]
        split_ifs with hB
        · exact (hnf1 hB).elim
        · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hFrameEnd a (by dsimp [heap0S2, editsBuf]; omega) hne11
        (hneM 9 (by omega)) (hneM 10 (by omega)) (hneM 11 (by omega))
        (hneM 13 (by omega)) (hneM 14 (by omega)) (hneM 15 (by omega))
        (hneM 16 (by omega))).trans (hs5fMem.symm ▸ h5eEq4 a ha)
  · have hPhi4Eq : Rtree.phi tok.treeHeap curTreeTok1 s5f.mem = Rtree.phi tok.treeHeap curTreeTok1 s4.mem :=
      hTreeLoc5f.2.symm
    rw [hPhi4Eq, zero_mul, add_zero, add_zero] at hcLoop
    have hLoopLe : edits2.length * (wireTreeSyncEditCost L drainUnit + 2) ≤
        sumNew * (wireTreeSyncEditCost L drainUnit + 2) := Nat.mul_le_mul_right _ hEdits2Le
    dsimp only [Rtree, tokMid, sumNew, modelPre, cnt, d] at hcPack hcSetup hcLoop hLoopLe ⊢
    omega

end MinCostFlow.MinRatio
