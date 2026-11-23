module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSync1KFBL
public import MinCostFlow.MinRatio.WireChainCoreLevelCutsKFBL
import WordRAM.Tactic

/-!
# Sync 2a of Branch B: cut the edges that the plain levels drop (`WireChainCoreBranchBSync2aKFBL`)

After the loop of Branch B, each plain level `j < n` has a list `fDel j` of the edges that left
its forest, named by words `2` and `3` of its slot. The path tree must lose those of them that are
still edges of the root graph. An edge of a list that is not in the root graph is a deleted name of
the batch, and Sync 1 has cut it already.

`wireBranchBSync2aStmt` finds the presence array of the root graph, writes the cuts of the levels
at the heap pointer (`wireEmitLevelCutsLoop`, which tests the presence array) and runs one sync
(`wireSyncPhaseStmt`). `wireBranchBSync2aStmt_runs` gives the tree state for `F \ X` afterwards,
where `X` holds the edges of the lists that are in the root graph.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Sync 2a of Branch B. `reg 99` is the number of plain levels (`reg 96`, the level at which the
loop of Branch B stopped; it is `min firstReb d`), `reg 14` is the root graph (word `14` of the root directory) and `reg 15` its
presence array, whose base is `4 + 7 · vCap` words after the graph. The loop writes
the cuts at the heap pointer (`reg 4`) and counts them in `reg 17`. The sync then applies them,
and the heap pointer moves past its work space. -/
@[expose] def wireBranchBSync2aStmt
    (emitCuts readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 99 (.reg 96) ;;
  .assign 14 (.load (.bin .add (.reg 70) (.const 14))) ;;
  .assign 15
    (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 7) (.load (.reg 14)))) ;;
  .assign 16 (.reg 4) ;;
  .assign 17 (.const 0) ;;
  wireEmitLevelCutsLoop emitCuts ;;
  .assign 6 (.reg 16) ;;
  .assign 18 (.reg 17) ;;
  wireSyncPhaseStmt readTree cutTree linkTree bind canonCopy isNeg ;;
  .assign 4 (.reg 3)

theorem wireBranchBSync2aStmt_noRand
    (emitCuts readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (wireBranchBSync2aStmt emitCuts readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [wireBranchBSync2aStmt, wireSyncPhaseStmt_noRand, wireEmitLevelCutsLoop_noRand,
    Stmt.NoRand]

/-- The cuts of the levels are the cuts of the joined list. -/
theorem levelCutsOf_eq_treeCutsOf (pres : ℕ → ℕ) (fDel : ℕ → List ℕ) (n : ℕ) :
    levelCutsOf pres fDel n = treeCutsOf pres ((List.range n).flatMap fDel) := by
  induction n with
  | zero => simp [levelCutsOf, treeCutsOf]
  | succ n ih =>
    rw [levelCutsOf_succ, ih, List.range_succ, List.flatMap_append]
    simp [treeCutsOf, List.filter_append]

set_option maxHeartbeats 1600000 in
/-- The run of Sync 2a of Branch B from the tree state for `F` at the heap pointer `heap`. The
register `96` holds the number `n` of plain levels, and the slot of each plain
level `j < n` names its list `fDel j` below `heap`. The lists have no repeats
together, their entries are below the edge capacity of the root graph, and every entry in the
root graph is on the tree. The cut set `X` holds the entries in the root graph. Afterwards the
tree state holds for `F \ X` with the heap pointer `heapEnd = reg 4`, the records of the cut edges
lie in the new heap, and no word below `heap` changes but those that a sync may write. -/
theorem wireBranchBSync2aStmt_runs
    {w L P m V psi k epsExp drainUnit initTree bind canonCopy isNeg emitCuts
      root uIntBuf heap rg offCnt selBase n : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {fPtr : ℕ → ℕ} {fDel : ℕ → List ℕ}
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
    (hSlot : ∀ j < n, st.mem (selBase + 1 + 12 * j + 2) = fPtr j ∧
      st.mem (selBase + 1 + 12 * j + 3) = (fDel j).length ∧ ListAt st.mem (fPtr j) (fDel j) ∧
      fPtr j + (fDel j).length ≤ heap ∧ selBase + 1 + 12 * j + 3 < heap)
    (hDelCap : ∀ j < n, ∀ e ∈ fDel j, e < tok.rootECap)
    (hInF : ∀ j < n, ∀ e ∈ fDel j, e ∈ G0.E → e ∈ F)
    (hNd : ((List.range n).flatMap fDel).Nodup)
    (hRegs : st.regs 4 = heap ∧ st.regs 70 = root ∧ st.regs 72 = selBase ∧
      st.regs 73 = tok.handle)
    (hSel : st.regs 96 = n)
    (hz : ZeroFrom st.mem heap)
    (hRoom : heap + 2 * ∑ j ∈ Finset.range n, (fDel j).length +
      (∑ j ∈ Finset.range n, (fDel j).length) * wireTreeSyncEditSpace L + 1 < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let T := ∑ j ∈ Finset.range n, (fDel j).length
    let X := levelCutsOf (fun e => st.mem (dgEPresBase rg G0.n + e)) fDel n
    ∃ (out : State) (cost heapEnd : ℕ) (curTree' : PathTreeState) (curTreeTok' : Rtree.τ)
      (offCnt' : ℕ),
      Runs w p ω (wireBranchBSync2aStmt emitCuts (opTree 4) (opTree 1) (opTree 0) bind
        canonCopy isNeg) st .normal out cost ∧
      out.regs 4 = heapEnd ∧ out.regs 99 = n ∧
      (∀ r, 70 ≤ r → r ≠ 96 → r ≠ 99 → out.regs r = st.regs r) ∧
      heap ≤ heapEnd ∧ heapEnd ≤ heap + 2 * T + T * wireTreeSyncEditSpace L ∧
      ZeroFrom out.mem heapEnd ∧
      TreeSyncPhaseAt L tok root uIntBuf heapEnd rg G0 (F \ X.toFinset) canonVal B R deferSet
        curTree' curTreeTok' offCnt' out.mem ∧
      (∀ e, e ∈ X ↔ (∃ j < n, e ∈ fDel j) ∧ e ∈ G0.E) ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap curTreeTok a ∨ (heap ≤ a ∧ a < heapEnd)) ∧
      (∀ ei ∈ G0.E, ei ∉ F →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ ei ∈ X, heap ≤ out.mem (tok.edgeRecords + ei) ∧
        out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapEnd) ∧
      (∀ a < heap, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
        T * (wireTreeSyncEditCost L drainUnit + 2) + 40 * T + 64 * n + 175 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := by
  classical
  intro Rtree T X
  obtain ⟨hr4, hr70, hr72, hr73⟩ := hRegs
  have hT : T = ∑ j ∈ Finset.range n, (fDel j).length := rfl
  have hRoomT : heap + 2 * T + T * wireTreeSyncEditSpace L + 1 < 2 ^ w := hRoom
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _, _, _, _, _, _, _, _, _, _, _, hT13, _, _, _, _, _, _, _⟩ :=
    hTags0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hBaseLe := hPh.baseLe
  have hCapE := hPh.capE
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hRgW : rg + dynGraphSize G0.n tok.rootECap ≤ heap := by
    have hpos : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have := (hPh.graphLoc (rg + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)).2.2
    omega
  unfold dynGraphSize at hRgW
  obtain ⟨_, _, _, hVCap, _, _, _, _, _, _, _, hEPres, _⟩ := hPh.graph
  have hVCap' : st.mem rg = G0.n := by simpa [dgVCapOff] using hVCap
  have hRgAt : st.mem (root + 14) = rg := hPh.dir.2.2.2.2.2.2.2
  -- the cut set
  have hPresVal (j : ℕ) (hj : j < n) (e : ℕ) (he : e ∈ fDel j) :
      st.mem (dgEPresBase rg G0.n + e) = if e ∈ G0.E then 1 else 0 :=
    hEPres e (hDelCap j hj e he)
  have hMemX : ∀ e, e ∈ X ↔ (∃ j < n, e ∈ fDel j) ∧ e ∈ G0.E := by
    intro e
    simp only [X, mem_levelCutsOf]
    constructor
    · rintro ⟨j, hj, he, hp⟩
      refine ⟨⟨j, hj, he⟩, ?_⟩
      rw [hPresVal j hj e he] at hp
      by_contra hn
      simp [hn] at hp
    · rintro ⟨⟨j, hj, he⟩, hE⟩
      refine ⟨j, hj, he, ?_⟩
      rw [hPresVal j hj e he]
      simp [hE]
  have hXnd : X.Nodup := by
    simp only [X]
    rw [levelCutsOf_eq_treeCutsOf]
    exact treeCutsOf_nodup hNd
  have hXsub : ∀ e ∈ X, e ∈ F := fun e he => by
    obtain ⟨⟨j, hj, hej⟩, hE⟩ := (hMemX e).mp he
    exact hInF j hj e hej hE
  have hXle : X.length ≤ T := levelCutsOf_length_le _ fDel n
  -- the five set-up moves
  let pres := dgEPresBase rg G0.n
  have hpres : pres = rg + 4 + 7 * G0.n := rfl
  let s0 := { st with regs := Function.update st.regs 99 n }
  have r0 : Runs w p ω (.assign 99 (.reg 96)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨n, by simp [Expr.eval, hSel],
      rfl, rfl, rfl⟩
  let s1 := { s0 with regs := Function.update s0.regs 14 rg }
  have r1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 70) (.const 14)))) s0 .normal s1 5 :=
    runs_assign_iff.mpr ⟨rg, by
      simp [Expr.eval, BinOp.eval, s0, hr70, show 14 < 2 ^ w by omega,
        show root + 14 < 2 ^ w by omega, hRgAt], rfl, rfl, rfl⟩
  let s2 := { s1 with regs := Function.update s1.regs 15 pres }
  have r2 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 14) (.const 4))
      (.bin .mul (.const 7) (.load (.reg 14))))) s1 .normal s2 9 :=
    runs_assign_iff.mpr ⟨pres, by
      simp [Expr.eval, BinOp.eval, s1, s0, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        hVCap', show rg + 4 < 2 ^ w by omega,
        show 7 * G0.n < 2 ^ w by omega, show rg + 4 + 7 * G0.n < 2 ^ w by omega, hpres],
      rfl, rfl, rfl⟩
  let s3 := { s2 with regs := Function.update s2.regs 16 heap }
  have r3 : Runs w p ω (.assign 16 (.reg 4)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s2, s1, s0, hr4], rfl, rfl, rfl⟩
  let s4 := { s3 with regs := Function.update s3.regs 17 0 }
  have r4 : Runs w p ω (.assign 17 (.const 0)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  -- the cuts of the levels
  obtain ⟨sL, cL, rL, hcL, h17L, hRegsL, hEdL, hZL, hFrL⟩ :=
    wireEmitLevelCutsLoop_runs (w := w) (p := p) (ω := ω) (st := s4) (selBase := selBase)
      (pres := pres) (base := heap) (n := n) (fPtr := fPtr) (fDel := fDel) hEmit
      ⟨by simp [s4, s3, s2, s1, s0, hr72], by simp [s4, s3, s2, s1, s0], by simp [s4, s3, s2],
        by simp [s4, s3], by simp [s4]⟩
      hSlot (fun j hj e he => by have := hDelCap j hj e he; omega) hz (by omega) (by omega)
  have h17L' : sL.regs 17 = X.length := h17L
  have hEdL' : TreeEditsAt sL.mem heap (X.map TreeChange.delete) := hEdL
  have hZL' : ZeroFrom sL.mem (heap + 2 * X.length) := hZL
  have hRegsL' (r : ℕ) (h1 : r ≠ 17) (h2 : r ≠ 18) (h3 : r ≠ 33) (h4 : r ≠ 34) (h5 : r ≠ 35)
      (h6 : r ≠ 36) (h7 : r ≠ 96) (h8 : r ≠ 16) (h9 : r ≠ 15) (h10 : r ≠ 14) (h11 : r ≠ 99) :
      sL.regs r = st.regs r := by
    rw [hRegsL r h1 h2 h3 h4 h5 h6 h7]
    simp [s4, s3, s2, s1, s0, Function.update_of_ne h1, Function.update_of_ne h8,
      Function.update_of_ne h9, Function.update_of_ne h10, Function.update_of_ne h11]
  have h16L : sL.regs 16 = heap :=
    (hRegsL 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans (by simp [s4, s3])
  -- the sync
  let s6 := { sL with regs := Function.update sL.regs 6 heap }
  have r6 : Runs w p ω (.assign 6 (.reg 16)) sL .normal s6 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, h16L], rfl, rfl, rfl⟩
  let s7 := { s6 with regs := Function.update s6.regs 18 X.length }
  have r7 : Runs w p ω (.assign 18 (.reg 17)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨X.length, by simp [Expr.eval, s6, h17L'], rfl, rfl, rfl⟩
  have hPhL := TreeSyncPhaseAt.of_agree hRep0_keep hFootLt hGn hPh hFrL
  have hDiff : TreeEditDifference F (F \ X.toFinset) (X.map TreeChange.delete) :=
    treeEditDifference_cuts hXnd hXsub
  have hNewSub : F \ X.toFinset ⊆ G0.E := fun e he => hPh.sub (Finset.mem_sdiff.mp he).1
  have hNewForest := isForest_with_sub hForest (Finset.sdiff_subset (s := F) (t := X.toFinset))
  have hXS : X.length * wireTreeSyncEditSpace L ≤ T * wireTreeSyncEditSpace L :=
    Nat.mul_le_mul_right _ hXle
  have hXE : X.length * (wireTreeSyncEditCost L drainUnit + 2) ≤
      T * (wireTreeSyncEditCost L drainUnit + 2) :=
    Nat.mul_le_mul_right _ hXle
  obtain ⟨s8, cS, heapEnd, curTree', curTreeTok', offCnt', rS, hr3, hRegsS, hEndGe, hEndLe, hzEnd,
      hPhEnd, hFootEnd, hCutRec, hKeepRec, hFrameS, hcS⟩ :=
    wireSyncPhaseStmt_runs (st := s7) (initTree := initTree) (drainUnit := drainUnit) hFmtBits
      hw18 hTreeImpl hBindOk hCanonOk hIsNegOk hRep0_keep hFootLt hGn hLogW hCapT hPhL hDiff
      hNewSub hNewForest hEdL' (le_refl heap) (by simpa using hZL')
      ⟨by simp [s7, s6], by simp [s7],
        by simp [s7, s6, hRegsL' 70 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr70],
        by simp [s7, s6, hRegsL' 73 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr73]⟩
      (by simp only [List.length_map]; omega)
  simp only [List.length_map] at hEndGe hEndLe hcS
  let s9 := { s8 with regs := Function.update s8.regs 4 heapEnd }
  have r9 : Runs w p ω (.assign 4 (.reg 3)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨heapEnd, by simp [Expr.eval, hr3], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (wireBranchBSync2aStmt emitCuts (opTree 4) (opTree 1) (opTree 0) bind
      canonCopy isNeg) st .normal s9
      (2 + (5 + (9 + (2 + (2 + (cL + (2 + (2 + (cS + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
        1) :=
    runs_seq_iff.mpr (Or.inr ⟨s0, _, _, r0,
    runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨sL, _, _, rL,
      runs_seq_iff.mpr (Or.inr ⟨s6, _, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, _, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, _, _, rS, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        rfl⟩), rfl⟩), rfl⟩)
  have h99L : sL.regs 99 = n :=
    (hRegsL 99 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans (by simp [s4, s3, s2, s1, s0])
  refine ⟨s9, _, heapEnd, curTree', curTreeTok', offCnt', rAll, by simp [s9], ?_, ?_, by omega,
    by omega, hzEnd, hPhEnd, hMemX, fun a ha => ?_, fun ei hei hnot => ?_, fun ei hei => ?_,
    fun a ha hne11 hlo hhi => ?_, ?_⟩
  · simp only [s9, Function.update_of_ne (by omega : (99 : ℕ) ≠ 4)]
    rw [hRegsS 99 (by omega)]
    simp only [s7, s6, Function.update_of_ne (by omega : (99 : ℕ) ≠ 18),
      Function.update_of_ne (by omega : (99 : ℕ) ≠ 6)]
    exact h99L
  · intro r hr h96 h99
    simp only [s9, Function.update_of_ne (by omega : r ≠ 4)]
    rw [hRegsS r hr]
    simp only [s7, s6, Function.update_of_ne (by omega : r ≠ 18),
      Function.update_of_ne (by omega : r ≠ 6)]
    exact hRegsL' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h96
      (by omega) (by omega) (by omega) h99
  · rcases hFootEnd a ha with h | ⟨hlo, hhi⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hhi⟩
  · have hnot' : ei ∉ F \ X.toFinset := fun h => hnot (Finset.mem_sdiff.mp h).1
    exact (hKeepRec ei hei hnot' hnot).trans
      (hFrL _ (lt_of_lt_of_le (htagLt (by rw [hT13 ei (hCapE ei hei)]; decide)) (by omega)))
  · have heF := hXsub ei hei
    have hnot' : ei ∉ F \ X.toFinset := fun h =>
      (Finset.mem_sdiff.mp h).2 (List.mem_toFinset.mpr hei)
    obtain ⟨hlo, hhi⟩ := hCutRec ei (hPh.sub heF) hnot' heF
    exact ⟨show heap ≤ s8.mem (tok.edgeRecords + ei) by omega, hhi⟩
  · exact (hFrameS a (by omega) hne11 hlo hhi).trans (hFrL a ha)
  · have hPhi : Rtree.phi tok.treeHeap curTreeTok s7.mem =
        Rtree.phi tok.treeHeap curTreeTok st.mem := rfl
    have hPhi2 : Rtree.phi tok.treeHeap curTreeTok' s9.mem =
        Rtree.phi tok.treeHeap curTreeTok' s8.mem := rfl
    rw [hPhi] at hcS
    rw [hPhi2]
    dsimp only [Rtree] at hcS ⊢
    omega

end MinCostFlow.MinRatio
