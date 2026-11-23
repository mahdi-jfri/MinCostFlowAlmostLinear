module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPostTok
import MinCostFlow.MinRatio.WireChainCoreBranchASync2KFBL
import MinCostFlow.MinRatio.OrdSolverReachInv

/-!
# Branch B post: edge accounts, solver representation, and `BranchBPostGoalKFBL` (`WireChainCoreBranchBPostRep`)

This file completes the proof of `BranchBPostGoalKFBL` (`WireChainCoreBranchBSufOutKFBL.lean`)
from `BranchBSufOutKFBL` and `wireBranchBTokNew` (`WireChainCoreBranchBPostTok.lean`):

* `branchB_accounts`: reconstructs `SolverEdgeAccountsAt`, `SolverEdgeOrientInv`, `OffTreeRecInv`,
  and `OffTreeRecBound` from `TreeSyncPhaseAt` and `BranchBSufOutKFBL.canon` via
  `solverEdgeAccounts_of_treeSync`;
* `branchB_rep`: proves `(solverStateRep …).rep root modelPre tok' out.mem` for `wireBranchBTokNew`;
* `branchBPostGoalKFBL_proved`: proves `BranchBPostGoalKFBL` by assembling all conjuncts of
  `OrdChainCoreExtPost`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Edge accounts, orientation invariant, and off-tree record invariants/bounds at the final state
of Branch B, reconstructed from `BranchBSufOutKFBL.phase` and `BranchBSufOutKFBL.canon` via
`solverEdgeAccounts_of_treeSync`. -/
theorem branchB_accounts
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hRef : RefreshBatch model.extG U)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost)
    (hLct : LctInvWith pathPayload curTree curTrees curFree curDepth)
    (hNamed : TreeEditNamedSlots curTree curTrees
      { (alg2PreResetState cfg model U gVec lVec).chain.G 0 with
        E := (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E }
      (fun ei => out.mem (tok.slots + ei)) (fun sl => out.mem (tok.names + sl)))
    (hLive : TreeEditLiveAccounts curTree curTrees
      { (alg2PreResetState cfg model U gVec lVec).chain.G 0 with
        E := (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E }
      (fun ei => out.mem (tok.slots + ei)) canonVal) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    SolverEdgeAccountsAt modelPre L P out.mem tok.slots tok.names tok.slotThresholds
      tok.edgeThresholds tok.edgeRecords tok.inOffReady tok.intCap curTree curTrees ∧
    SolverEdgeOrientInv L P modelPre out.mem tok.slots tok.edgeRecords curTree curTrees ∧
    OffTreeRecInv modelPre L out.mem tok.edgeRecords B ∧
    OffTreeRecBound modelPre L out.mem tok.edgeRecords B := by
  intro modelPre
  have hPreExtG : modelPre.extG = model.extG := branchB_modelPre_extG hRep0 hRef
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := branchB_modelPre_freshInv hRep0 hRef
  have hE2I : modelPre.extToInt =
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 :=
    S.names.1
  exact solverEdgeAccounts_of_treeSync (model := modelPre) (P := P) (B := B) (mem := out.mem)
    (slots := tok.slots) (names := tok.names) (slotThresholds := tok.slotThresholds)
    (edgeThresholds := tok.edgeThresholds) (edgeRecords := tok.edgeRecords)
    (inOffReady := tok.inOffReady) (intCap := tok.intCap)
    hFreshPre hLct hNamed hLive S.newSub S.phase.capE
    (fun e he => by
      have he0 : e ∈ model.extG.E := hPreExtG ▸ he
      rw [hE2I]; exact (S.canon e he0).1)
    (fun e he => by
      have he0 : e ∈ model.extG.E := hPreExtG ▸ he
      have hei : modelPre.extToInt e ∈ (modelPre.chain.G 0).E :=
        hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
      obtain ⟨hvf, hvg, hvl, hvfl, hvd⟩ := S.phase.canonProp _ hei
      obtain ⟨_, hof, hog, hol, hacc⟩ := S.canon e he0
      dsimp only
      rw [hE2I] at hvf hvg hvl hvfl hvd ⊢
      exact ⟨hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc⟩)
    S.phase.slotThr
    (fun e he hnot =>
      S.phase.offSlot _ (hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he) hnot)
    (fun e he hnot =>
      S.phase.offRec _ (hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he) hnot)
    (fun e he hnot hdet =>
      S.phase.offReady _ (hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he) hnot
        (Finset.notMem_empty _) hdet)
    (fun e₁ he₁ e₂ he₂ hne hnot₁ hnot₂ => by
      have h1 := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he₁
      have h2 := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he₂
      have hneI : modelPre.extToInt e₁ ≠ modelPre.extToInt e₂ := fun h =>
        hne ((hFreshPre.hLeft e₁ he₁).symm.trans (h ▸ hFreshPre.hLeft e₂ he₂))
      exact S.phase.offDisj _ h1 _ h2 hneI hnot₁ hnot₂)

set_option maxHeartbeats 600000 in
/-- `(solverStateRep …).rep` holds for `wireBranchBTokNew` at the final state of Branch B. -/
theorem branchB_rep
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hTrNfLe :
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.1 ≤
        tok.intCap)
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost)
    (hLct : LctInvWith pathPayload curTree curTrees curFree curDepth)
    (hNamed : TreeEditNamedSlots curTree curTrees
      { (alg2PreResetState cfg model U gVec lVec).chain.G 0 with
        E := (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E }
      (fun ei => out.mem (tok.slots + ei)) (fun sl => out.mem (tok.names + sl)))
    (hLive : TreeEditLiveAccounts curTree curTrees
      { (alg2PreResetState cfg model U gVec lVec).chain.G 0 with
        E := (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E }
      (fun ei => out.mem (tok.slots + ei)) canonVal) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
      out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
    Rrep.rep root modelPre tok' out.mem := by
  intro Rrep modelPre tok'
  have hRep0_keep := hRep0
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, _, _, hExtLtM0,
    ⟨_, hIntCapPos, _, hI2E0⟩, _, _, _, _, _, _, _, _, _, _, hWire0, _⟩ := hRep0
  have hPreExtG : modelPre.extG = model.extG := branchB_modelPre_extG hRep0_keep hRef
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := branchB_modelPre_freshInv hRep0_keep hRef
  have hG0n : (modelPre.chain.G 0).n = modelPre.extG.n := by
    simp only [MGraph.n, hFreshPre.hV]
  obtain ⟨hAccounts, hOrient, _, _⟩ := branchB_accounts hRep0_keep hRef S hLct hNamed hLive
  refine ⟨?_, ?_, ?_, ?_, hFreshPre, ?_, hPreExtG.symm ▸ hExtLtM0,
    ⟨S.phase.capE, hIntCapPos, by rw [S.names.2.2]; exact hTrNfLe, fun j hj => by
      rw [S.names.2.1]
      exact ((translateBatch_i2e_ge model.extG model.extToInt model.intToExt model.nextFresh U).2 j
        (le_trans hTrNfLe hj)).trans (hI2E0 j hj)⟩,
    S.sched, S.phase.offInv, S.phase.treeN.trans hG0n, hLct, S.phase.treeRep, hAccounts,
    fun j hj => ⟨rfl, S.bran j hj, S.reps j hj⟩, rfl, S.lastB, S.lastRep, ?_,
    branchB_tagsNew hRep0_keep hRef hFootLt S⟩
  · -- root directory
    intro j hj
    have hj16 : j < 16 := by simpa using hj
    by_cases h11 : j = 11
    · subst h11; simpa [tok', wireBranchBTokNew] using S.phase.offCntAt
    · rw [S.rootDir j hj16 h11]
      have h0 := hRootDir0 j hj
      have hEq : [tok'.handle, tok'.table, tok'.levelsEnd, tok'.forward, tok'.inverse,
          tok'.freshCounter, tok'.slots, tok'.names, tok'.slotThresholds, tok'.edgeThresholds,
          tok'.edgeRecords, tok'.offReadyCount, tok'.offReadyList, tok'.inOffReady,
          tok'.rootGraph, tok'.intCap][j] =
        [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse,
          tok.freshCounter, tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds,
          tok.edgeRecords, tok.offReadyCount, tok.offReadyList, tok.inOffReady,
          tok.rootGraph, tok.intCap][j] := by
        interval_cases j <;> first | rfl | contradiction
      exact h0.trans hEq.symm
  · -- detector header
    intro j hj
    have hj8 : j < 8 := by simpa using hj
    exact (S.header j (by omega)).trans (hDetHdr0 j hj)
  · -- numeric header
    intro j hj
    have hj4 : j < 4 := by simpa using hj
    rw [show tok'.handle + 5 + j = tok.handle + (5 + j) by dsimp [tok', wireBranchBTokNew]; omega]
    exact (S.header (5 + j) (by omega)).trans (by simpa [Nat.add_assoc] using hNumHdr0 j hj)
  · -- chain header
    intro j hj
    have hj9 : j < 9 := by simpa using hj
    rw [show tok'.handle + 9 + j = tok.handle + (9 + j) by dsimp [tok', wireBranchBTokNew]; omega]
    exact (S.header (9 + j) (by omega)).trans (by simpa [Nat.add_assoc] using hInitPar0 j hj)
  · -- fresh tables
    rw [S.names.1, S.names.2.1, S.names.2.2]
    exact S.fresh
  · -- `SolverWireInv`
    refine ⟨fun j hj => (S.table j hj).trans (hWire0.1 j hj),
      hG0n ▸ S.phase.graph,
      ⟨S.newForest, fun ei hei => by
        have hei0 := S.newSub hei
        obtain ⟨h1, h2⟩ := S.phase.graph.1 ei hei0
        have hv1 : modelPre.chain.toTreeChain.chainTree.tail ei < modelPre.extG.n :=
          hG0n ▸ S.phase.graph.2.1 _ h1
        have hv2 : modelPre.chain.toTreeChain.chainTree.head ei < modelPre.extG.n :=
          hG0n ▸ S.phase.graph.2.1 _ h2
        exact ⟨S.phase.capE ei hei0, hv1, hv2,
          named_account_endpoints_ne hLct hNamed hei (by rw [S.phase.treeN, hG0n]; exact hv1)⟩⟩,
      hNamed, hOrient⟩

/-- **The post of Branch B (`BranchBPostGoalKFBL`).** From the premises of
`OrdChainCoreBranchBPostKFBL`, a run of the core returning `nextHeap`, and `BranchBSufOutKFBL` at
its final state, every conjunct of `OrdChainCoreExtPost` holds. -/
theorem branchBPostGoalKFBL_proved
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (G : MGraph) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ) (B_bound R_bound : ℤ)
    (body : Stmt) :
    BranchBPostGoalKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p coreSpace coreFixed
      toolMul treeMul B_bound R_bound body := by
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R _tr gVec lVec
    _modelPre hRep0 hMeta0 hCaps0 _hIntCapEq hExtM _hNum0 _hOffInv0 _hOffBd0 hBLe hRLe _hShiftInv
    _hCapFacts _hBranLt hModelInv _hModelInvKFBL _hIntCapMax _hForestCap _hLogW _hCapT _hMemEq
    _hFreshMem hTrNfLe _hBatchMem _hSmallMem _hOrdMem _hEdW _hEdEnd hRef hFootLt _hGLt _hLLt
    _hULeEd _hZ0 _hRoom _hNotOver0 heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
    curTree curTreeTok offCnt canonVal out nextHeap cost hRun S
  obtain ⟨curTrees, curFree, curDepth, hLct, hNum, hNamed, hLive⟩ := S.phase.lct
  let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
    out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
  obtain ⟨_, _, hOffInv, hOffBd⟩ := branchB_accounts hRep0 hRef S hLct hNamed hLive
  have hRepEnd := branchB_rep hRep0 hTrNfLe hRef hFootLt S hLct hNamed hLive
  have hMetaEnd := branchB_levelMetaNew (curTrees := curTrees) (curFree := curFree)
    (curDepth := curDepth) hRep0 hMeta0 hCaps0 hExtM hModelInv hFootLt S
  have hSelEnd := branchB_selectOut (curTrees := curTrees) (curFree := curFree)
    (curDepth := curDepth) hFootLt S
  have hFootEnd := branchB_foot_growth (curTrees := curTrees) (curFree := curFree)
    (curDepth := curDepth) hRep0 S
  have hHeaps := S.heaps
  have hLM0 : out.mem (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d) = tok'.rootGraph := by
    change out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d) = tok.rootGraph
    have h0 : 0 < min (fr + 1) cfg.P.d := Nat.lt_min.mpr ⟨Nat.succ_pos _, S.dPos⟩
    have hK := (S.metaKeep 0 h0).1
    rw [Nat.add_zero] at hK
    have hM0 : mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + 0) = tok.rootGraph :=
      hModelInv.2.2.2.2.2.2.2.2.1.1
    rw [Nat.add_zero] at hM0
    exact hK.trans hM0
  have hCostEnd :
      cost + (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok' out.mem ≤
      coreFixed U.length +
        toolMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalRuntime -
          model.chain.totalRuntime) +
        treeMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalTreeUpdates -
          model.chain.totalTreeUpdates) +
        40 * (Finset.range (min fr cfg.P.d)).sum (fun j => (D j).reemb.length) +
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem0 := by
    change cost + ((LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap
        curTreeTok out.mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (out.mem (tok.handle + 18 + i.val)) (tokN i.val) out.mem) +
      offCnt * drainUnit) ≤ _
    rw [Fin.sum_univ_eq_sum_range
      (fun j => Rcore.phi (out.mem (tok.handle + 18 + j)) (tokN j) out.mem)]
    exact S.costLe
  exact ⟨nextHeap, cost, out, tok', B, R, fr, levelU, levelUS, D,
    hRun, by omega, S.space, rfl, rfl, rfl, rfl, hBLe, hRLe,
    hRepEnd, hMetaEnd, S.graphs, hLM0, hNum, hOffInv, hOffBd,
    S.metaCells.2.2.1, S.metaCells.2.2.2, S.link, hSelEnd, S.zero, S.frameMem, hFootEnd, hCostEnd⟩

end MinCostFlow.MinRatio
