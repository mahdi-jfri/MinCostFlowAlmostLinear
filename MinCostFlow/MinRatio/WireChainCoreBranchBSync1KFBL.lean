module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPhaseKFBL
public import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import WordRAM.Tactic

/-!
# Sync 1 of Branch B: cut the deleted names of the batch (`WireChainCoreBranchBSync1KFBL`)

Before the level loop of Branch B runs, the core cuts from the path tree every deleted name of the
batch that is on the tree. Two reasons force this order. The sync finds the ends of an edge in
the root graph, and the plain step of level `0` applies the batch to the root graph, so after the
loop the deleted names have no ends there. And the refresh of the accounts reads the records of
the deleted names, so they must be off the tree first.

`wireBranchBSync1Stmt` collects the deleted names of the batch at `uIntBuf` into fresh heap
(`wireCollectDeletedEdgesBody`), turns those whose slot is not `0` into cuts
(`wireEmitTreeCutsBody`), and runs one sync (`wireSyncPhaseStmt`). The cut set `D` is the set of
deleted names on the tree. `wireBranchBSync1Stmt_runs` gives the tree state for `F \ D` after the
sync, with the heap pointer in `reg 4`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Sync 1 of Branch B: collect the deleted names of the batch (`reg 87`) at the heap pointer
(`reg 4`), write the cuts of those on the tree after them, run the sync, and move the heap pointer
past the work space of the sync. -/
@[expose] def wireBranchBSync1Stmt
    (collectDel emitCuts readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .call 14 collectDel [.reg 87, .reg 4] ;;
  .assign 15 (.load (.bin .add (.reg 70) (.const 6))) ;;
  .assign 6 (.bin .add (.reg 4) (.reg 14)) ;;
  .call 18 emitCuts [.reg 4, .reg 14, .const 1, .const 0, .reg 15, .reg 6] ;;
  wireSyncPhaseStmt readTree cutTree linkTree bind canonCopy isNeg ;;
  .assign 4 (.reg 3)

theorem wireBranchBSync1Stmt_noRand
    (collectDel emitCuts readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (wireBranchBSync1Stmt collectDel emitCuts readTree cutTree linkTree bind canonCopy
      isNeg).NoRand := by
  simp [wireBranchBSync1Stmt, wireSyncPhaseStmt_noRand, Stmt.NoRand]

/-- A set of edges inside a forest is a forest. -/
theorem isForest_with_sub {G : MGraph} {F F' : Finset ℕ}
    (hF : ({ G with E := F } : MGraph).IsForest) (hsub : F' ⊆ F) :
    ({ G with E := F' } : MGraph).IsForest :=
  ⟨fun e he => hF.1 e (hsub he), fun P ⟨hne, hnd, u, hW⟩ =>
    hF.2 P ⟨hne, hnd, u,
      MGraph.isWalk_of_isSubgraph (G := { G with E := F }) (H := { G with E := F' })
        ⟨subset_rfl, hsub, fun _ _ => ⟨rfl, rfl⟩⟩ hW⟩⟩

set_option maxHeartbeats 1600000 in
/-- The run of Sync 1 of Branch B from the tree state for `F` at the heap pointer `heap`. The
batch `U` at `uIntBuf` has only edge updates. Its deleted names lie below `intCap`, those that are
edges of `G0` have no repeats, and the others have slot `0`. A batch may refresh an edge twice,
and then it deletes a fresh name that it inserted before; the core zeroes the slots of the fresh
names first, so the emitter skips them. The cut set `D` holds the deleted names on the tree (those
in `F`). Afterwards the tree state holds for `F \ D` with the heap pointer `heapEnd = reg 4`, the
records of the cut names lie in the new heap, and no word below `heap` changes but those that a
sync may write. -/
theorem wireBranchBSync1Stmt_runs
    {w L P m V psi k epsExp drainUnit initTree bind canonCopy isNeg collectDel emitCuts
      root uIntBuf heap rg offCnt bW : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {U : List Update}
    (hCollect : p.procs[collectDel]? = some wireCollectDeletedEdgesBody)
    (hEmit : p.procs[emitCuts]? = some wireEmitTreeCutsBody)
    (hFmtBits : fmt.limbBits = 4) (hw18 : 18 < 2 ^ w)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree
      opTree (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heap rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt st.mem)
    (hForest : ({ G0 with E := F } : MGraph).IsForest)
    (hSmall : SmallBatchAt st.mem uIntBuf G0 U bW)
    (hEdgeOnly : ∀ u ∈ U, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < bW, st.mem (uIntBuf + j) < 2 ^ w)
    (hBatchLe : uIntBuf + bW ≤ heap)
    (hDelCap : ∀ e ∈ batchDeletedEdges U, e < tok.intCap)
    (hDelOff : ∀ e ∈ batchDeletedEdges U, e ∉ G0.E → st.mem (tok.slots + e) = 0)
    (hDelNd : ((batchDeletedEdges U).filter (fun e => decide (e ∈ G0.E))).Nodup)
    (hRegs : st.regs 4 = heap ∧ st.regs 70 = root ∧ st.regs 73 = tok.handle ∧
      st.regs 87 = uIntBuf)
    (hz : ZeroFrom st.mem heap)
    (hRoom : heap + 3 * U.length + U.length * wireTreeSyncEditSpace L + 1 < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let D := treeCutsOf (fun e => st.mem (tok.slots + e)) (batchDeletedEdges U)
    ∃ (out : State) (cost heapEnd : ℕ) (curTree' : PathTreeState) (curTreeTok' : Rtree.τ)
      (offCnt' : ℕ),
      Runs w p ω (wireBranchBSync1Stmt collectDel emitCuts (opTree 4) (opTree 1) (opTree 0) bind
        canonCopy isNeg) st .normal out cost ∧
      out.regs 4 = heapEnd ∧ (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      heap ≤ heapEnd ∧ heapEnd ≤ heap + 3 * U.length + U.length * wireTreeSyncEditSpace L ∧
      ZeroFrom out.mem heapEnd ∧
      TreeSyncPhaseAt L tok root uIntBuf heapEnd rg G0 (F \ D.toFinset) canonVal B R deferSet
        curTree' curTreeTok' offCnt' out.mem ∧
      (∀ e, e ∈ D ↔ Update.delete e ∈ U ∧ e ∈ F) ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap curTreeTok a ∨ (heap ≤ a ∧ a < heapEnd)) ∧
      (∀ ei ∈ G0.E, ei ∉ F →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ ei ∈ D, heap ≤ out.mem (tok.edgeRecords + ei) ∧
        out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapEnd) ∧
      (∀ a < heap, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
        U.length * (wireTreeSyncEditCost L drainUnit + 2) + 90 * U.length + 230 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := by
  classical
  intro Rtree D
  obtain ⟨hr4, hr70, hr73, hr87⟩ := hRegs
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _, _, _, _, _, _, _, hT9, _, _, _, hT13, _, _, _, _, _, _, _⟩ :=
    hTags0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hBaseLe := hPh.baseLe
  have hCapE := hPh.capE
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hSlotLtU (e : ℕ) (he : e < tok.intCap) : tok.slots + e < uIntBuf :=
    htagLt (by rw [hT9 e he]; decide)
  have hDelsLe : (batchDeletedEdges U).length ≤ U.length := batchDeletedEdges_length_le U
  -- the collector
  obtain ⟨outC, cC, rCBody, hcC, hListC, hzC, hFrC⟩ :=
    wireCollectDeletedEdgesBody_runs (w := w) (p := p) (ω := ω) (pos := st.pos) (outBuf := heap)
      hSmall hEdgeOnly hBatchW hBatchLe hz (by omega) (by omega)
  let s1 : State :=
    { regs := Function.update st.regs 14 (batchDeletedEdges U).length, mem := outC.mem,
      pos := outC.pos }
  have r1 : Runs w p ω (.call 14 collectDel [.reg 87, .reg 4]) st .normal s1 (2 + cC + 1) :=
    runs_call_iff.mpr ⟨[uIntBuf, heap], wireCollectDeletedEdgesBody,
      .returned (batchDeletedEdges U).length, outC,
      cC, by simp [evalArgs, Expr.eval, hr87, hr4], hCollect, rCBody, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
  -- the slots pointer and the cut buffer
  have hSlotsAt : outC.mem (root + 6) = tok.slots := (hFrC _ (by omega)).trans hPh.dir.1
  let s2 := { s1 with regs := Function.update s1.regs 15 tok.slots }
  have r2 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 70) (.const 6)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨tok.slots, by
      simp [Expr.eval, BinOp.eval, s1, hr70, show 6 < 2 ^ w by omega,
        show root + 6 < 2 ^ w by omega, hSlotsAt], rfl, rfl, rfl⟩
  let s3 := { s2 with regs := Function.update s2.regs 6 (heap + (batchDeletedEdges U).length) }
  have r3 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.reg 14))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨heap + (batchDeletedEdges U).length, by
      simp [Expr.eval, BinOp.eval, s2, s1, hr4,
        show heap + (batchDeletedEdges U).length < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- the cuts
  have hListS3 : ∀ i (h : i < (batchDeletedEdges U).length),
      outC.mem (heap + 1 * i + 0) = (batchDeletedEdges U)[i] :=
    fun i h => by simpa using hListC i h
  obtain ⟨outE, cE, rEBody, hcE, hEditsE, hzE, hFrE⟩ :=
    wireEmitTreeCutsBody_runs (w := w) (p := p) (ω := ω) (src := heap)
      (len := (batchDeletedEdges U).length) (stride := 1) (off := 0) (slots := tok.slots)
      (outBuf := heap + (batchDeletedEdges U).length) (pos := outC.pos)
      (mem := outC.mem) (es := batchDeletedEdges U) rfl hListS3 (fun i hi => by omega)
      (fun e he => by have := hSlotLtU e (hDelCap e he); omega)
      hzC (by omega) (by omega)
  have hCutsEq : treeCutsOf (fun e => outC.mem (tok.slots + e)) (batchDeletedEdges U) = D := by
    show treeCutsOf _ (batchDeletedEdges U) = treeCutsOf _ (batchDeletedEdges U)
    unfold treeCutsOf
    exact List.filter_congr (fun e he => by
      dsimp only
      rw [hFrC _ (lt_of_lt_of_le (hSlotLtU e (hDelCap e he)) (by omega))])
  rw [hCutsEq] at rEBody hEditsE hzE
  let s4 : State :=
    { regs := Function.update s3.regs 18 D.length, mem := outE.mem, pos := outE.pos }
  have r4 : Runs w p ω (.call 18 emitCuts [.reg 4, .reg 14, .const 1, .const 0, .reg 15, .reg 6])
      s3 .normal s4 (6 + cE + 1) :=
    runs_call_iff.mpr ⟨[heap, (batchDeletedEdges U).length, 1, 0, tok.slots,
      heap + (batchDeletedEdges U).length], wireEmitTreeCutsBody,
      .returned D.length, outE, cE,
      by simp [evalArgs, Expr.eval, s3, s2, s1, hr4, show 1 < 2 ^ w by omega],
      hEmit, rEBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- the tree state at the start of the sync
  have hS4Lt (a : ℕ) (ha : a < heap) : s4.mem a = st.mem a :=
    (hFrE a (by omega)).trans (hFrC a ha)
  have hPh4 := TreeSyncPhaseAt.of_agree hRep0_keep hFootLt hGn hPh hS4Lt
  obtain ⟨curTrees0, curFree0, curDepth0, _, _, hNamed0, _⟩ := hPh.lct
  have hDsub : ∀ e ∈ D, e ∈ F := fun e he => by
    obtain ⟨hed, hslot⟩ := mem_treeCutsOf.mp he
    by_contra hnF
    by_cases hG : e ∈ G0.E
    · exact hslot (hPh.offSlot e hG hnF)
    · exact hslot (hDelOff e hed hG)
  have hDNd : D.Nodup := by
    have hEq : D = treeCutsOf (fun e => st.mem (tok.slots + e))
        ((batchDeletedEdges U).filter (fun e => decide (e ∈ G0.E))) := by
      show treeCutsOf _ _ = _
      unfold treeCutsOf
      rw [List.filter_filter]
      refine List.filter_congr (fun e he => ?_)
      by_cases hG : e ∈ G0.E
      · simp [hG]
      · simp [hG, hDelOff e he hG]
    rw [hEq]
    exact treeCutsOf_nodup hDelNd
  have hDiff : TreeEditDifference F (F \ D.toFinset) (D.map TreeChange.delete) :=
    treeEditDifference_cuts hDNd hDsub
  have hNewSub : F \ D.toFinset ⊆ G0.E := fun e he => hPh.sub (Finset.mem_sdiff.mp he).1
  have hNewForest := isForest_with_sub hForest (Finset.sdiff_subset (s := F) (t := D.toFinset))
  have hDle : D.length ≤ (batchDeletedEdges U).length := treeCutsOf_length_le _ _
  have hDS : D.length * wireTreeSyncEditSpace L ≤ U.length * wireTreeSyncEditSpace L :=
    Nat.mul_le_mul_right _ (le_trans hDle hDelsLe)
  have hDE : D.length * (wireTreeSyncEditCost L drainUnit + 2) ≤
      U.length * (wireTreeSyncEditCost L drainUnit + 2) :=
    Nat.mul_le_mul_right _ (le_trans hDle hDelsLe)
  obtain ⟨s5, cS, heapEnd, curTree', curTreeTok', offCnt', rS, hr3, hRegsS, hEndGe, hEndLe, hzEnd,
      hPhEnd, hFootEnd, hCutRec, hKeepRec, hFrameS, hcS⟩ :=
    wireSyncPhaseStmt_runs (initTree := initTree) (drainUnit := drainUnit) hFmtBits hw18 hTreeImpl
      hBindOk hCanonOk hIsNegOk hRep0_keep hFootLt hGn hLogW hCapT hPh4 hDiff hNewSub hNewForest
      hEditsE (by omega : heap ≤ heap + (batchDeletedEdges U).length) (by simpa using hzE)
      ⟨by simp [s4, s3], by simp [s4], by simp [s4, s3, s2, s1, hr70],
        by simp [s4, s3, s2, s1, hr73]⟩
      (by simp only [List.length_map]; omega)
  simp only [List.length_map] at hEndGe hEndLe hcS
  let s6 := { s5 with regs := Function.update s5.regs 4 heapEnd }
  have r6 : Runs w p ω (.assign 4 (.reg 3)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨heapEnd, by simp [Expr.eval, hr3], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (wireBranchBSync1Stmt collectDel emitCuts (opTree 4) (opTree 1)
      (opTree 0) bind canonCopy isNeg) st .normal s6
      ((2 + cC + 1) + (5 + (4 + ((6 + cE + 1) + (cS + 2 + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, _, _, rS, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨s6, _, heapEnd, curTree', curTreeTok', offCnt', rAll, by simp [s6], ?_, by omega,
    by omega, hzEnd, hPhEnd, ?_, fun a ha => ?_, fun ei hei hnot => ?_, fun ei hei => ?_,
    fun a ha hne11 hlo hhi => ?_, ?_⟩
  · intro r hr
    have h5 := hRegsS r hr
    simp only [s6, Function.update_of_ne (by omega : r ≠ 4)]
    rw [h5]
    simp [s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 18),
      Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 15),
      Function.update_of_ne (by omega : r ≠ 14)]
  · intro e
    constructor
    · intro he
      obtain ⟨hed, _⟩ := mem_treeCutsOf.mp he
      exact ⟨(mem_batchDeletedEdges_iff U e).mp hed, hDsub e he⟩
    · rintro ⟨hdel, heF⟩
      refine mem_treeCutsOf.mpr ⟨(mem_batchDeletedEdges_iff U e).mpr hdel, ?_⟩
      have hslot := (hNamed0.forward e heF).2.1
      unfold isEdgeSlot at hslot
      show st.mem (tok.slots + e) ≠ 0
      omega
  · rcases hFootEnd a ha with h | ⟨hlo, hhi⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hhi⟩
  · have hnot' : ei ∉ F \ D.toFinset := fun h => hnot (Finset.mem_sdiff.mp h).1
    exact (hKeepRec ei hei hnot' hnot).trans
      (hS4Lt _ (lt_of_lt_of_le (htagLt (by rw [hT13 ei (hCapE ei hei)]; decide)) (by omega)))
  · have heF := hDsub ei hei
    have hnot' : ei ∉ F \ D.toFinset := fun h =>
      (Finset.mem_sdiff.mp h).2 (List.mem_toFinset.mpr hei)
    obtain ⟨hlo, hhi⟩ := hCutRec ei (hPh.sub heF) hnot' heF
    simp only [List.length_map] at hlo
    exact ⟨show heap ≤ s5.mem (tok.edgeRecords + ei) by omega, hhi⟩
  · exact (hFrameS a (by omega) hne11 hlo hhi).trans (hS4Lt a ha)
  · have hPhi : Rtree.phi tok.treeHeap curTreeTok s4.mem =
        Rtree.phi tok.treeHeap curTreeTok st.mem := rfl
    have hPhi2 : Rtree.phi tok.treeHeap curTreeTok' s6.mem =
        Rtree.phi tok.treeHeap curTreeTok' s5.mem := rfl
    rw [hPhi] at hcS
    rw [hPhi2]
    dsimp only [Rtree] at hcS ⊢
    omega

end MinCostFlow.MinRatio
