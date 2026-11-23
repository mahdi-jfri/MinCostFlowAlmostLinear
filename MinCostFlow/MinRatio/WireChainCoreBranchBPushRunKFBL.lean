module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPushKFBL
public import MinCostFlow.MinRatio.WireChainCoreZeroInsKFBL
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Step 6 of Branch B: push the fresh names off the tree (`WireChainCoreBranchBPushRunKFBL`)

After the last sync, the fresh names of the batch are the deferred set of the tree state: the
ready clause of `TreeSyncPhaseAt` does not cover them yet. Step 6 walks the batch. For each
inserted name that is an edge of the root graph it reads the slot: a slot `0` means that the name
is off the tree, and then `offTreePushBody` pushes the name onto the ready list when its detector
is nonnegative. A batch that refreshes an edge twice inserts a fresh name that it deletes again,
so the walk first tests the presence array of the root graph.

`wirePushIfOffStmt_runs` is one test of the slot and push, and `wirePushIfLiveStmt_runs` adds the
test of presence. `wirePushInsertedBody_runs` is the walk over the batch: afterwards the deferred
set has lost every inserted name, the ready list has grown by at most one entry per update, and
the cost is at most `160` per update plus `60`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Push the name `e = reg 9` when its slot (`reg 5` is the slot table) is `0`. The push reads the
record of `e` from the record table (`reg 6`); `reg 0` is the root and `reg 2` the limb count. -/
@[expose] def wirePushIfOffStmt (pushProc : ℕ) : Stmt :=
  .cond (.load (.bin .add (.reg 5) (.reg 9))) .nop
    (.call 10 pushProc [.reg 0, .reg 9, .load (.bin .add (.reg 6) (.reg 9)), .reg 2])

/-- Push the name `e = reg 9` when it is an edge of the root graph (`reg 11` is the presence
array of the root graph) and its slot is `0`. A batch that refreshes an edge twice inserts a fresh
name and deletes it again; that name is not an edge of the root graph, and the test skips it. -/
@[expose] def wirePushIfLiveStmt (pushProc : ℕ) : Stmt :=
  .cond (.load (.bin .add (.reg 11) (.reg 9))) (wirePushIfOffStmt pushProc) .nop

/-- Procedure `[root, batchPtr, L]` (`regs 0..2`): walk an edge-only batch and push each inserted
name that is off the tree. An insertion (tag `0`) takes four words and a deletion two. It returns
`0`. -/
@[expose] def wirePushInsertedBody (pushProc : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 14))) ;;
  .assign 11
    (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.load (.reg 11)))) ;;
  forRange 7 (.const 0) (.reg 3)
    (.assign 8 (.load (.reg 4)) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.assign 9 (.load (.bin .add (.reg 4) (.const 1))) ;;
        wirePushIfLiveStmt pushProc ;;
        .assign 4 (.bin .add (.reg 4) (.const 4)))
       (.assign 4 (.bin .add (.reg 4) (.const 2)))) ;;
  .ret (.const 0)

theorem wirePushInsertedBody_noRand (pushProc : ℕ) : (wirePushInsertedBody pushProc).NoRand := by
  simp [wirePushInsertedBody, wirePushIfLiveStmt, wirePushIfOffStmt, forRange, forUp,
    Stmt.NoRand]

set_option maxHeartbeats 1600000 in
/-- One test and push of a name `e` of the root graph. If its slot is not `0`, `e` is on the tree
and nothing changes. Otherwise `e` is off the tree and `offTreePushBody` runs. Either way the tree
state holds without `e` in the deferred set, the count grows by at most one, and only the count
word and words of the two ready arrays change. -/
theorem wirePushIfOffStmt_runs
    {w L P m V psi k epsExp drainUnit isNeg pushProc root uIntBuf heapX rg offCnt e : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hPush : p.procs[pushProc]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt st.mem)
    (he : e ∈ G0.E)
    (hRegs : st.regs 0 = root ∧ st.regs 2 = L ∧ st.regs 5 = tok.slots ∧
      st.regs 6 = tok.edgeRecords ∧ st.regs 9 = e)
    (hHeapW : heapX < 2 ^ w) (hLW : L < 2 ^ w) (hw13 : 13 < 2 ^ w) :
    ∃ out cost offCnt',
      Runs w p ω (wirePushIfOffStmt pushProc) st .normal out cost ∧
      cost ≤ 110 ∧ offCnt' ≤ offCnt + 1 ∧
      (∀ r, r ≠ 10 → out.regs r = st.regs r) ∧
      TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R (deferSet.erase e) curTree
        curTreeTok offCnt' out.mem ∧
      ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
        out.mem a = st.mem a := by
  obtain ⟨hr0, hr2, hr5, hr6, hr9⟩ := hRegs
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _, _, _, _, _, _, _, hT9, _, _, _, hT13, hT14, hT15, _, _, _, _,
    _⟩ := hTags0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hBaseLe := hPh.baseLe
  have heCap := hPh.capE e he
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hSlotLt : tok.slots + e < uIntBuf := htagLt (by rw [hT9 e heCap]; decide)
  have hRecPLt : tok.edgeRecords + e < uIntBuf := htagLt (by rw [hT13 e heCap]; decide)
  obtain ⟨_, _, _, _, _, hNamed, _⟩ := hPh.lct
  by_cases hslot : st.mem (tok.slots + e) = 0
  · -- `e` is off the tree: push it
    have heF : e ∉ F := fun h => by
      have := (hNamed.forward e h).2.1
      unfold isEdgeSlot at this
      omega
    let newRec := st.mem (tok.edgeRecords + e)
    have hRecAt := hPh.offRec e he heF
    have hRecLocE := hPh.recLoc e he heF
    let tg : ℕ → ℕ := fun a => if newRec ≤ a ∧ a < newRec + (2 + 4 * L) then 18 else tok.tag a
    have hNotRec {a : ℕ} (ha : a < uIntBuf) (ht : tok.tag a ≠ 18) : tg a = tok.tag a := by
      have hnot : ¬ (newRec ≤ a ∧ a < newRec + (2 + 4 * L)) := by
        rintro ⟨h1, h2⟩
        have := (hRecLocE (a - newRec) (by omega)).1
        rw [show newRec + (a - newRec) = a by omega] at this
        exact ht (this ha)
      simp only [tg, hnot, ↓reduceIte]
    have hRecEnd := (hRecLocE (1 + 4 * L) (by omega)).2.2.2
    have hIO : tok.inOffReady + e < uIntBuf := htagLt (by rw [hT15 e heCap]; decide)
    have hOL : tok.offReadyList + (tok.intCap - 1) < uIntBuf :=
      htagLt (by rw [hT14 (tok.intCap - 1) (by omega)]; decide)
    have hdir := hPh.dir
    obtain ⟨cP, outP, cnt', rP, hcP, hcnt, hCntAt, hRecEq, hInvP, hReadyP, hKeepP, hFrP⟩ :=
      offTreePushBody_runs (w := w) (isNeg := isNeg) (root := root) (ei := e) (newRec := newRec)
        (L := L) (pos := st.pos) (offReadyCount := offCnt) (offReadyList := tok.offReadyList)
        (inOffReady := tok.inOffReady) (edgeRecords := tok.edgeRecords) (intCap := tok.intCap)
        (p := p) (ω := ω) (mem := st.mem) (val := canonVal e) tg hIsNeg hPh.offInv heCap
        hdir.2.2.2.2.1 hPh.offCntAt hdir.2.2.2.2.2.1 hdir.2.2.2.2.2.2.1 hRecAt
        (fun j hj => (hNotRec (by omega) (by rw [hT1 j (by omega)]; decide)).trans
          (hT1 j (by omega)))
        ((hNotRec hRecPLt (by rw [hT13 e heCap]; decide)).trans (hT13 e heCap))
        (fun j hj => by
          have h14 := hT14 j hj
          have hlt : tok.offReadyList + j < uIntBuf := htagLt (by rw [h14]; decide)
          exact (hNotRec hlt (by rw [h14]; decide)).trans h14)
        (fun j hj => by
          have h15 := hT15 j hj
          have hlt : tok.inOffReady + j < uIntBuf := htagLt (by rw [h15]; decide)
          exact (hNotRec hlt (by rw [h15]; decide)).trans h15)
        (fun x hx => by
          have hin : newRec ≤ newRec + x ∧ newRec + x < newRec + (2 + 4 * L) := by omega
          simp only [tg, hin, and_self, ↓reduceIte])
        hw13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hLW
    let s1 : State := { regs := Function.update st.regs 10 0, mem := outP.mem, pos := outP.pos }
    have rCall : Runs w p ω
        (.call 10 pushProc [.reg 0, .reg 9, .load (.bin .add (.reg 6) (.reg 9)), .reg 2]) st
        .normal s1 (7 + cP + 1) :=
      runs_call_iff.mpr ⟨[root, e, newRec, L], offTreePushBody isNeg, .returned 0, outP, cP,
        by simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr9, hr6, hr2,
          show tok.edgeRecords + e < 2 ^ w by omega, newRec],
        hPush, rP, rfl, rfl, by simp [argsSize, Expr.size]⟩
    have rC : Runs w p ω (wirePushIfOffStmt pushProc) st .normal s1 (4 + (7 + cP + 1) + 1) :=
      runs_cond_iff.mpr ⟨0, _, by
        simp [Expr.eval, BinOp.eval, hr5, hr9, show tok.slots + e < 2 ^ w by omega, hslot],
        by simpa only [↓reduceIte] using rCall, rfl⟩
    have hag : ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
        s1.mem a = st.mem a := by
      intro a h11 htag
      by_cases har : a = tok.edgeRecords + e
      · subst har
        exact hRecEq
      · refine hFrP a har (fun hio => ?_) (fun hc hol => ?_) h11
        · subst hio
          exact (htag hIO).2 (hT15 e heCap)
        · subst hol
          have hlt : offCnt < tok.intCap := by have := hInvP.1; omega
          exact (htag (htagLt (by rw [hT14 offCnt hlt]; decide))).1 (hT14 offCnt hlt)
    refine ⟨s1, _, cnt', rC, by omega, by omega, fun r hr => ?_,
      TreeSyncPhaseAt.of_push hRep0_keep hFootLt hGn hPh hag hCntAt hInvP
        (fun _ hdet => hReadyP hdet) hKeepP, hag⟩
    simp [s1, Function.update_of_ne hr]
  · -- `e` is on the tree: nothing to do
    have heF : e ∈ F := by
      by_contra h
      exact hslot (hPh.offSlot e he h)
    refine ⟨st, 4 + 1 + 1, offCnt, runs_cond_iff.mpr ⟨st.mem (tok.slots + e), 1, by
        simp [Expr.eval, BinOp.eval, hr5, hr9, show tok.slots + e < 2 ^ w by omega],
        by simpa only [hslot, ↓reduceIte] using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ :
          Runs w p ω .nop st .normal st 1), rfl⟩,
      by omega, by omega, fun _ _ => rfl, hPh.erase_of_mem heF, fun _ _ _ => rfl⟩

/-- The tree state reads the deferred set only at the edges of `G0`, so a name that is not an
edge of `G0` can leave the deferred set. -/
theorem TreeSyncPhaseAt.erase_of_not_mem_graph
    {L root uIntBuf heapX rg offCnt ei : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem : ℕ → ℕ}
    {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt mem)
    (he : ei ∉ G0.E) :
    TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R (deferSet.erase ei) curTree
      curTreeTok offCnt mem :=
  { hPh with
    offReady := fun e he' hnF hnd hdet => hPh.offReady e he' hnF
      (fun h => hnd (Finset.mem_erase.mpr ⟨fun h' => he (h' ▸ he'), h⟩)) hdet }

set_option maxHeartbeats 1600000 in
/-- One test and push of a name `e` below the edge capacity of the root graph. If `e` is an edge
of the root graph, this is `wirePushIfOffStmt_runs`. Otherwise nothing changes, and the tree state
does not read the deferred set at `e`. -/
theorem wirePushIfLiveStmt_runs
    {w L P m V psi k epsExp drainUnit isNeg pushProc root uIntBuf heapX rg offCnt e : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hPush : p.procs[pushProc]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt st.mem)
    (heCap : e < tok.rootECap)
    (hRegs : st.regs 0 = root ∧ st.regs 2 = L ∧ st.regs 5 = tok.slots ∧
      st.regs 6 = tok.edgeRecords ∧ st.regs 9 = e ∧ st.regs 11 = dgEPresBase rg G0.n)
    (hHeapW : heapX < 2 ^ w) (hLW : L < 2 ^ w) (hw13 : 13 < 2 ^ w) :
    ∃ out cost offCnt',
      Runs w p ω (wirePushIfLiveStmt pushProc) st .normal out cost ∧
      cost ≤ 120 ∧ offCnt' ≤ offCnt + 1 ∧
      (∀ r, r ≠ 10 → out.regs r = st.regs r) ∧
      TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R (deferSet.erase e) curTree
        curTreeTok offCnt' out.mem ∧
      ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
        out.mem a = st.mem a := by
  obtain ⟨hr0, hr2, hr5, hr6, hr9, hr11⟩ := hRegs
  have hPres := hPh.graph.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
  have hAddrLt : dgEPresBase rg G0.n + e < heapX :=
    (hPh.graphLoc (dgEPresBase rg G0.n + e) (by unfold dgEPresBase; omega)
      (by unfold dgEPresBase; simp [dynGraphSize]; omega)).2.2
  by_cases he : e ∈ G0.E
  · obtain ⟨out, c, cnt', r, hc, hcnt, hregs, hph, hfr⟩ :=
      wirePushIfOffStmt_runs hPush hIsNeg hRep0 hFootLt hGn hPh he ⟨hr0, hr2, hr5, hr6, hr9⟩
        hHeapW hLW hw13
    simp only [he, ↓reduceIte] at hPres
    refine ⟨out, 4 + c + 1, cnt', runs_cond_iff.mpr ⟨1, c, by
        simp [Expr.eval, BinOp.eval, hr11, hr9, show dgEPresBase rg G0.n + e < 2 ^ w by omega,
          hPres], by simpa using r, rfl⟩, by omega, hcnt, hregs, hph, hfr⟩
  · simp only [he, ↓reduceIte] at hPres
    refine ⟨st, 4 + 1 + 1, offCnt, runs_cond_iff.mpr ⟨0, 1, by
        simp [Expr.eval, BinOp.eval, hr11, hr9, show dgEPresBase rg G0.n + e < 2 ^ w by omega,
          hPres], by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ :
            Runs w p ω .nop st .normal st 1), rfl⟩,
      by omega, by omega, fun _ _ => rfl, hPh.erase_of_not_mem_graph he, fun _ _ _ => rfl⟩

set_option maxHeartbeats 3200000 in
/-- The walk of step 6 over an edge-only batch whose inserted names lie below the edge capacity of
the root graph `G0`. Afterwards the tree state holds without the inserted names in the deferred
set, the count of the ready list has grown by at most `|U|`, only the count word and words of the
two ready arrays have changed, and the cost is at most `160 |U| + 60`. The batch lies at or above
`uIntBuf`, so the pushes do not write it. -/
theorem wirePushInsertedBody_runs
    {w L P m V psi k epsExp drainUnit isNeg pushProc root uIntBuf heapX rg offCnt batchPtr
      totalWords pos : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 G : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {U : List Update}
    (hPush : p.procs[pushProc]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt mem)
    (hSmall : SmallBatchAt mem batchPtr G U totalWords)
    (hEdgeOnly : ∀ u ∈ U, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hBatchLo : uIntBuf ≤ batchPtr) (hRoom : batchPtr + totalWords < 2 ^ w)
    (hInsCap : ∀ e ∈ batchInsertedEdges U, e < tok.rootECap)
    (hHeapW : heapX < 2 ^ w) (hLW : L < 2 ^ w) (hw13 : 13 < 2 ^ w) :
    ∃ out cost offCnt',
      Runs w p ω (wirePushInsertedBody pushProc) (startState [root, batchPtr, L] mem pos)
        (.returned 0) out cost ∧
      cost ≤ 160 * U.length + 60 ∧ offCnt' ≤ offCnt + U.length ∧
      TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R
        (deferSet \ (batchInsertedEdges U).toFinset) curTree curTreeTok offCnt' out.mem ∧
      ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
        out.mem a = mem a := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _⟩ := hTags0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  obtain ⟨⟨hTotPos, hLen0, hBody0⟩, _⟩ := hSmall
  have hULenW : U.length < 2 ^ w := by simpa [hLen0] using hBatchW 0 (by omega)
  have hdir := hPh.dir
  let s0 := startState [root, batchPtr, L] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 3 U.length }
  let s2 := { s1 with regs := Function.update s1.regs 4 (batchPtr + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 5 tok.slots }
  let s4 := { s3 with regs := Function.update s3.regs 6 tok.edgeRecords }
  let pres := dgEPresBase rg G0.n
  let s4a := { s4 with regs := Function.update s4.regs 11 rg }
  let s4b := { s4a with regs := Function.update s4a.regs 11 pres }
  have r1 : Runs w p ω (.assign 3 (.load (.reg 1))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hLen0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 4 (.bin .add (.reg 1) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show batchPtr + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 6)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨tok.slots, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 6 < 2 ^ w by omega,
        show root + 6 < 2 ^ w by omega, hdir.1], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 10)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨tok.edgeRecords, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 10 < 2 ^ w by omega,
        show root + 10 < 2 ^ w by omega, hdir.2.2.2.2.1], rfl, rfl, rfl⟩
  have hVCap : mem rg = G0.n := by simpa [dgVCapOff] using hPh.graph.2.2.2.1
  have hRgLt : rg + dynGraphSize G0.n tok.rootECap ≤ heapX := by
    have hpos : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have := (hPh.graphLoc (rg + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)).2.2
    omega
  have hGS : 4 + 7 * G0.n ≤ dynGraphSize G0.n tok.rootECap := by simp [dynGraphSize]
  have r4a : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const 14)))) s4 .normal s4a 5 :=
    runs_assign_iff.mpr ⟨rg, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 14 < 2 ^ w by omega,
        show root + 14 < 2 ^ w by omega, hdir.2.2.2.2.2.2.2], rfl, rfl, rfl⟩
  have r4b : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 11) (.const 4))
      (.bin .mul (.const 7) (.load (.reg 11))))) s4a .normal s4b 9 :=
    runs_assign_iff.mpr ⟨pres, by
      simp [Expr.eval, BinOp.eval, s4a, s4, s3, s2, s1, s0, startState, show 4 < 2 ^ w by omega,
        show 7 < 2 ^ w by omega, hVCap, show rg + 4 < 2 ^ w by omega,
        show 7 * G0.n < 2 ^ w by omega, show rg + 4 + 7 * G0.n < 2 ^ w by omega, pres,
        dgEPresBase], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ ptr remW cnt,
      s.regs 0 = root ∧ s.regs 1 = batchPtr ∧ s.regs 2 = L ∧ s.regs 3 = U.length ∧
      s.regs 4 = ptr ∧ s.regs 5 = tok.slots ∧ s.regs 6 = tok.edgeRecords ∧ s.regs 7 = i ∧
      s.regs 11 = pres ∧ batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      cnt ≤ offCnt + i ∧
      TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R
        (deferSet \ (batchInsertedEdges (U.take i)).toFinset) curTree curTreeTok cnt s.mem ∧
      ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) → s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 3)
    (P := fun s => s = s4b) (Inv := Inv) (fun _ => 140) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      have hD0 : deferSet \ (batchInsertedEdges (U.take 0)).toFinset = deferSet := by
        simp [batchInsertedEdges]
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        batchPtr + 1, totalWords - 1, offCnt,
        by simp [s4b, s4a, s4, s3, s2, s1, s0, startState],
        by simp [s4b, s4a, s4, s3, s2, s1, s0, startState],
        by simp [s4b, s4a, s4, s3, s2, s1, s0, startState], by simp [s4b, s4a, s4, s3, s2, s1],
        by simp [s4b, s4a, s4, s3, s2], by simp [s4b, s4a, s4, s3], by simp [s4b, s4a, s4],
        by simp, by simp [s4b], le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0, by omega,
        by rw [hD0]; exact hPh, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ h => by
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, h7, _⟩; exact h7)
    (fun _ s _ _ h => by
      rcases h with ⟨_, _, _, _, _, _, h3, _⟩; simp [Expr.eval, h3])
    (fun i _ hi s ω' ⟨ptr, remW, cnt, h0, h1, h2, h3, h4, h5, h6, h7, h11, hPtrLo, hPtrEnd,
        hBody, hCnt, hPhS, hFr⟩ => by
      have hDrop : U.drop i = U[i] :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hDrop] at hBody
      obtain ⟨uLen, hULenLe, hUAt, hRest⟩ := hBody
      have hTakeSucc : U.take (i + 1) = U.take i ++ [U[i]] :=
        List.take_succ_eq_append_getElem hi
      have hGStep : G.applyBatch (U.take (i + 1)) =
          (G.applyBatch (U.take i)).applyUpdate U[i] := by
        unfold MGraph.applyBatch
        rw [hTakeSucc, List.foldl_append]
        rfl
      have hBatchKeep (a : ℕ) (ha : batchPtr ≤ a) : s.mem a = mem a :=
        hFr a (by omega) (fun h => absurd h (by omega))
      have hEdge := hEdgeOnly U[i] (List.getElem_mem hi)
      cases hu : U[i] with
      | delete e =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 1 := by simpa using hLA 0 (by simp)
        have hm0 : s.mem ptr = 1 := (hBatchKeep ptr (by omega)).trans hTag
        let t1 := { s with regs := Function.update s.regs 8 1 }
        let t2 := { t1 with regs := Function.update t1.regs 4 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 8 (.load (.reg 4))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h4, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by
            simp [Expr.eval, BinOp.eval, t1, h4, show 2 < 2 ^ w by omega,
              show ptr + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 8) (.const 0))
              (.assign 9 (.load (.bin .add (.reg 4) (.const 1))) ;;
               wirePushIfLiveStmt pushProc ;;
               .assign 4 (.bin .add (.reg 4) (.const 4)))
              (.assign 4 (.bin .add (.reg 4) (.const 2))))
            t1 .normal t2 (3 + 4 + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, Nat.two_pow_pos w],
            by simpa only [↓reduceIte] using rt2, rfl⟩
        have rstep : Runs w p ω' _ s .normal t2 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) = batchInsertedEdges (U.take i) := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; simp [batchInsertedEdges]
        refine ⟨.normal, t2, _, rstep, ⟨⟨ptr + 2, remW - 2, cnt,
          by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2, t1, h3],
          by simp [t2], by simp [t2, t1, h5], by simp [t2, t1, h6], by simp, by simp [t2, t1, h11],
          by omega, by omega, by rw [hGStep]; exact hRest, by omega,
          by rw [hNewPref]; exact hPhS, hFr⟩, by simp [t2, t1, h7]⟩, by dsimp only; omega⟩
      | insert e u v =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 0 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 0 := (hBatchKeep ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hBatchKeep (ptr + 1) (by omega)).trans hE
        have hEIns : e ∈ batchInsertedEdges U := by
          rw [mem_batchInsertedEdges_iff]
          exact ⟨U[i], List.getElem_mem hi, by rw [hu]; rfl⟩
        let t1 := { s with regs := Function.update s.regs 8 0 }
        let t2 := { t1 with regs := Function.update t1.regs 9 e }
        have rt1 : Runs w p ω' (.assign 8 (.load (.reg 4))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h4, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 9 (.load (.bin .add (.reg 4) (.const 1)))) t1 .normal
            t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h4, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        obtain ⟨t3, cPu, cnt', rPu, hcPu, hcnt', hRegsPu, hPhPu, hFrPu⟩ :=
          wirePushIfLiveStmt_runs (st := t2) (ω := ω') hPush hIsNeg hRep0_keep hFootLt hGn hPhS
            (hInsCap e hEIns)
            ⟨by simp [t2, t1, h0], by simp [t2, t1, h2], by simp [t2, t1, h5],
              by simp [t2, t1, h6], by simp [t2], by simp [t2, t1, h11, pres]⟩ hHeapW hLW hw13
        have h34 : t3.regs 4 = ptr := (hRegsPu 4 (by decide)).trans (by simp [t2, t1, h4])
        let t4 := { t3 with regs := Function.update t3.regs 4 (ptr + 4) }
        have rt4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 4))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by
            simp [Expr.eval, BinOp.eval, h34, hw4, show ptr + 4 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 8) (.const 0))
              (.assign 9 (.load (.bin .add (.reg 4) (.const 1))) ;;
               wirePushIfLiveStmt pushProc ;;
               .assign 4 (.bin .add (.reg 4) (.const 4)))
              (.assign 4 (.bin .add (.reg 4) (.const 2))))
            t1 .normal t4 (3 + (5 + (cPu + 4 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1, Nat.two_pow_pos w],
            by simpa using
              runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
                runs_seq_iff.mpr (Or.inr ⟨t3, cPu, 4, rPu, rt4, rfl⟩), rfl⟩), rfl⟩
        have rstep : Runs w p ω' _ s .normal t4 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) =
            batchInsertedEdges (U.take i) ++ [e] := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; rfl
        have hSetEq : deferSet \ (batchInsertedEdges (U.take (i + 1))).toFinset =
            (deferSet \ (batchInsertedEdges (U.take i)).toFinset).erase e := by
          rw [hNewPref]
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_append,
            List.mem_singleton]
          tauto
        have hr (r : ℕ) (h10 : r ≠ 10) (h9 : r ≠ 9) (h8 : r ≠ 8) (h4' : r ≠ 4) :
            t4.regs r = s.regs r := by
          simp only [t4, Function.update_of_ne h4']
          rw [hRegsPu r h10]
          simp [t2, t1, Function.update_of_ne h9, Function.update_of_ne h8]
        refine ⟨.normal, t4, _, rstep, ⟨⟨ptr + 4, remW - 4, cnt',
          by simp [hr 0 (by decide) (by decide) (by decide) (by decide), h0],
          by simp [hr 1 (by decide) (by decide) (by decide) (by decide), h1],
          by simp [hr 2 (by decide) (by decide) (by decide) (by decide), h2],
          by simp [hr 3 (by decide) (by decide) (by decide) (by decide), h3],
          by simp [t4], by simp [hr 5 (by decide) (by decide) (by decide) (by decide), h5],
          by simp [hr 6 (by decide) (by decide) (by decide) (by decide), h6], by simp,
          by simp [hr 11 (by decide) (by decide) (by decide) (by decide), h11], by omega, by omega, by rw [hGStep]; exact hRest, by omega,
          by rw [hSetEq]; exact hPhPu,
          fun a h11 htag => (hFrPu a h11 htag).trans (hFr a h11 htag)⟩,
          by rw [hr 7 (by decide) (by decide) (by decide) (by decide)]; exact h7⟩,
          by dsimp only; omega⟩
      | split v v' St Sh =>
        rw [hu] at hEdge
        exact hEdge.elim)
  obtain ⟨o, s5, cLoop, rLoop, hInv5, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv5
  | normal =>
    rcases hInv5 with ⟨_, _, cnt, _, _, _, _, _, _, _, _, _, _, _, _, hCnt5, hPh5, hFr5⟩
    have hTakeAll : U.take U.length = U := List.take_of_length_le le_rfl
    rw [hTakeAll] at hPh5
    have rRet : Runs w p ω (.ret (.const 0)) s5 (.returned 0) s5 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
    have rAll : Runs w p ω (wirePushInsertedBody pushProc) s0 (.returned 0) s5
        (3 + (4 + (5 + (5 + (5 + (9 + (cLoop + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
            runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
              runs_seq_iff.mpr (Or.inr ⟨s4a, 5, _, r4a,
                runs_seq_iff.mpr (Or.inr ⟨s4b, 9, _, r4b,
                  runs_seq_iff.mpr (Or.inr ⟨s5, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩),
              rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 140) 0 U.length = U.length * 140 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s5, _, cnt, rAll, by omega, hCnt5, hPh5, hFr5⟩

end MinCostFlow.MinRatio
