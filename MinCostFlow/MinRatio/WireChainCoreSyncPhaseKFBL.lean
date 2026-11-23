module

public import MinCostFlow.MinRatio.WireChainCoreSyncLoop
public import MinCostFlow.MinRatio.WireShiftTermPhases
import WordRAM.Tactic

/-!
# One sync of the path tree between two states of Branch B (`WireChainCoreSyncPhaseKFBL`)

Branch B of the chain-update core changes the path tree three times: before the level loop it
cuts the deleted names of the batch, and after the loop it cuts the edges that the plain levels
dropped and then swaps the old suffix forests for the new ones. Each time the core writes a list
of tree edits to fresh heap and runs the sync loop `wireTreeSyncLoop` on it.

The three syncs start from different states, so we name the part of the state that a sync reads
and keeps: `TreeSyncPhaseAt`. It says that the path tree holds the forest `F` of the graph `G0`
at the root-graph pointer `rg`, that every edge of `G0` off `F` has slot `0` and a saved record,
and where the tree, the root graph and the records lie: below the heap pointer `heapX`, and,
below `uIntBuf`, on the words of the solver that carry the matching tag. The last part lets us
give the sync a tag function for the current state (`tagMid` in the proof), as the sync loop asks.

`wireSyncPhaseStmt_runs` runs the setup and the loop on edits from `F` to `F'` and gives
`TreeSyncPhaseAt` for `F'` again, with the new heap pointer. So the three syncs of Branch B use
this one lemma.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The setup of the sync registers and the sync loop, on the edits at `reg 6` (`reg 18` of
them). -/
@[expose] def wireSyncPhaseStmt (readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 27 (.reg 70) ;;
  .assign 29 (.reg 73) ;;
  shiftTermSetupLoop ;;
  wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg

theorem wireSyncPhaseStmt_noRand (readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (wireSyncPhaseStmt readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [wireSyncPhaseStmt, shiftTermSetupLoop, wireTreeSyncLoop_noRand, Stmt.NoRand]

/-- The tree part of the solver state at a sync of Branch B. The path tree holds the forest `F`
of the graph `G0`, which lies at `rg`; each edge of `G0` off `F` has slot `0` and a saved record
with value `canonVal`. The tree, the root graph and the records lie below `heapX`, and each of
their words below `uIntBuf` carries the tag of its kind in `tok` (`16`, `20` and `18`). -/
structure TreeSyncPhaseAt (L : ℕ) {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (root uIntBuf heapX rg : ℕ) (G0 : MGraph) (F : Finset ℕ)
    (canonVal : ℕ → PathEdgeValue) (B R : ℤ) (deferSet : Finset ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (mem : ℕ → ℕ) : Prop where
  baseLe : uIntBuf ≤ heapX
  dir : mem (root + 6) = tok.slots ∧ mem (root + 7) = tok.names ∧
    mem (root + 8) = tok.slotThresholds ∧ mem (root + 9) = tok.edgeThresholds ∧
    mem (root + 10) = tok.edgeRecords ∧ mem (root + 12) = tok.offReadyList ∧
    mem (root + 13) = tok.inOffReady ∧ mem (root + 14) = rg
  hdr : mem tok.handle = tok.treeHeap ∧ mem (tok.handle + 5) = L
  graph : DynGraphAt mem rg G0.n tok.rootECap G0
  sub : F ⊆ G0.E
  capE : ∀ ei ∈ G0.E, ei < tok.intCap
  canonProp : ∀ ei ∈ G0.E, (canonVal ei).forward = true ∧ |(canonVal ei).gradient| ≤ B ∧
    |(canonVal ei).length| ≤ B ∧ |(canonVal ei).flow| ≤ B ∧ |(canonVal ei).detector| ≤ B
  treeN : curTree.n = G0.n
  lct : ∃ (curTrees : List AuxTree) (curFree : List ℕ) (curDepth : ℕ → ℕ),
    LctInvWith pathPayload curTree curTrees curFree curDepth ∧
    PathTreeNumericInv curTree curTrees B R ∧
    TreeEditNamedSlots curTree curTrees { G0 with E := F }
      (fun ei => mem (tok.slots + ei)) (fun sl => mem (tok.names + sl)) ∧
    TreeEditLiveAccounts curTree curTrees { G0 with E := F }
      (fun ei => mem (tok.slots + ei)) canonVal
  treeRep : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree
    curTreeTok mem
  slotThr : ∀ ei ∈ F,
    mem (tok.slotThresholds + mem (tok.slots + ei)) = mem (tok.edgeThresholds + ei)
  offSlot : ∀ ei ∈ G0.E, ei ∉ F → mem (tok.slots + ei) = 0
  offRec : ∀ ei ∈ G0.E, ei ∉ F →
    PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei))
  offReady : ∀ ei ∈ G0.E, ei ∉ F → ei ∉ deferSet → 0 ≤ (canonVal ei).detector →
    mem (tok.inOffReady + ei) = 1
  offDisj : ∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ F → e₂ ∉ F →
    mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ mem (tok.edgeRecords + e₂) ∨
    mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ mem (tok.edgeRecords + e₁)
  offCntAt : mem (root + 11) = offCnt
  offInv : OffReadyInv mem offCnt tok.offReadyList tok.inOffReady tok.intCap
  footLoc : ∀ a,
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a →
    (a < uIntBuf → tok.tag a = 16) ∧ a < heapX
  graphLoc : ∀ a, rg ≤ a → a < rg + dynGraphSize G0.n tok.rootECap →
    (a < uIntBuf → tok.tag a = 20) ∧
    ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a ∧
    a < heapX
  recLoc : ∀ ei ∈ G0.E, ei ∉ F → ∀ j < 2 + 4 * L,
    (mem (tok.edgeRecords + ei) + j < uIntBuf →
      tok.tag (mem (tok.edgeRecords + ei) + j) = 18) ∧
    ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok
      (mem (tok.edgeRecords + ei) + j) ∧
    (mem (tok.edgeRecords + ei) + j < rg ∨
      rg + dynGraphSize G0.n tok.rootECap ≤ mem (tok.edgeRecords + ei) + j) ∧
    mem (tok.edgeRecords + ei) + j < heapX

private theorem pathRep_foot_base_p {L C b : ℕ} {s : PathTreeState}
    {x : (LinkCut.PathProg.pathRep 4 L C).τ} {mem : ℕ → ℕ}
    (_hrep : (LinkCut.PathProg.pathRep 4 L C).rep b s x mem) :
    (LinkCut.PathProg.pathRep 4 L C).foot b x b := by
  refine ⟨le_rfl, ?_⟩
  unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
  have h1 : 1 ≤ LinkCut.PathProg.recW (LinkCut.PathProg.treeLimbs L) := by
    unfold LinkCut.PathProg.recW; omega
  have h3 := Nat.mul_pos h1 (by omega : 0 < 2 * x.1.n + 1)
  unfold LinkCut.PathProg.recW at h3; omega

set_option maxHeartbeats 1600000 in
/-- The run of `wireSyncPhaseStmt` on edits from `F` to `F'` at `editPtr`, from a state with
`TreeSyncPhaseAt` for `F`. Afterwards `TreeSyncPhaseAt` holds for `F'` with the heap pointer
`heapEnd = reg 3`. The records of the cut edges lie in the new heap, the other records stay,
and the sync writes no word below the end of the edits but the slots, names, slot thresholds,
record pointers, the off-ready list and its bits, the tree and the count `root + 11`. -/
theorem wireSyncPhaseStmt_runs
    {w L P m V psi k epsExp drainUnit initTree bind canonCopy isNeg
      root uIntBuf heapX rg editPtr offCnt : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F F' : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {edits : List TreeChange}
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
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt st.mem)
    (hDiff : TreeEditDifference F F' edits) (hNewSub : F' ⊆ G0.E)
    (hNewForest : ({ G0 with E := F' } : MGraph).IsForest)
    (hEditsAt : TreeEditsAt st.mem editPtr edits) (hEdLe : heapX ≤ editPtr)
    (hz : ZeroFrom st.mem (editPtr + 2 * edits.length))
    (hRegs : st.regs 6 = editPtr ∧ st.regs 18 = edits.length ∧ st.regs 70 = root ∧
      st.regs 73 = tok.handle)
    (hRoom : editPtr + 2 * edits.length + edits.length * wireTreeSyncEditSpace L < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let heap0 := editPtr + 2 * edits.length
    ∃ (out : State) (cost heapEnd : ℕ) (curTree' : PathTreeState) (curTreeTok' : Rtree.τ)
      (offCnt' : ℕ),
      Runs w p ω (wireSyncPhaseStmt (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
        st .normal out cost ∧
      out.regs 3 = heapEnd ∧ (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      heap0 ≤ heapEnd ∧ heapEnd ≤ heap0 + edits.length * wireTreeSyncEditSpace L ∧
      ZeroFrom out.mem heapEnd ∧
      TreeSyncPhaseAt L tok root uIntBuf heapEnd rg G0 F' canonVal B R deferSet curTree'
        curTreeTok' offCnt' out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap curTreeTok a ∨ (heap0 ≤ a ∧ a < heapEnd)) ∧
      (∀ ei ∈ G0.E, ei ∉ F' → ei ∈ F →
        heap0 ≤ out.mem (tok.edgeRecords + ei) ∧
        out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapEnd) ∧
      (∀ ei ∈ G0.E, ei ∉ F' → ei ∉ F →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ a < heap0, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
        edits.length * (wireTreeSyncEditCost L drainUnit + 2) + 130 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := by
  classical
  intro Rtree heap0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTreeN0, _, hTreeRep0, _, _, _, _, _, _, hTags0⟩ :=
    hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, hT14, hT15,
    hT16, _, _, _, _⟩ := hTags0
  obtain ⟨hBaseLe, ⟨hD6, hD7, hD8, hD9, hD10, hD12, hD13, hD14⟩, ⟨hH0, hH5⟩, hRG, hSub, hCapE,
    hCanonP, hTreeN, hLct, hTreeRep, hSlotThr, hOffSlot, hOffRec, hOffReady, hOffDisj, hOffCnt,
    hOffInv, hFootLoc, hGraphLoc, hRecLoc⟩ := hPh
  obtain ⟨hr6, hr18, hr70, hr73⟩ := hRegs
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ uIntBuf := by
    have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hRgW : rg + dynGraphSize G0.n tok.rootECap ≤ heapX := by
    have hpos : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have := (hGraphLoc (rg + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)).2.2
    omega
  -- the two register moves and the setup
  let s1 := { st with regs := Function.update st.regs 27 root }
  let s2 := { s1 with regs := Function.update s1.regs 29 tok.handle }
  have r1 : Runs w p ω (.assign 27 (.reg 70)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, hr70], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 29 (.reg 73)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s1, hr73], rfl, rfl, rfl⟩
  obtain ⟨s3, cSetup, rSetup, hcSetup, hs3Mem, h3_0, h3_1, h3_2, h3_3, h3_6, h3_18, h3_9, h3_10,
      h3_11, h3_19, h3_20, h3_22, h3_23, h3_24, h3_25, h3_26⟩ :=
    shiftTermSetupLoop_runs (w := w) (p := p) (ω := ω) (st := s2) (editPtr := editPtr)
      (nEdits := edits.length) (root := root) (handle := tok.handle) (rootGraph := rg)
      (nV := G0.n) (rootECap := tok.rootECap)
      (by simp [s2, s1, hr6]) (by simp [s2, s1, hr18]) (by simp [s2, s1]) (by simp [s2])
      hH0 hH5 hD14
      (by simpa [dgVCapOff] using hRG.2.2.2.1)
      (by simpa [dgECapOff] using hRG.2.2.2.2.1)
      hD6 hD7 hD8 hD9 hD10 hD12 hD13
      (by omega) (by omega) (by omega) (by omega)
  have hs3 : s3.mem = st.mem := hs3Mem
  -- the tag function of the current state
  let tagMid : ℕ → ℕ := fun a =>
    if a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15) then tok.tag a
    else if Rtree.foot tok.treeHeap curTreeTok a then 16
    else if rg ≤ a ∧ a < rg + dynGraphSize G0.n tok.rootECap then 20
    else if ∃ ei ∈ G0.E, ei ∉ F ∧ st.mem (tok.edgeRecords + ei) ≤ a ∧
        a < st.mem (tok.edgeRecords + ei) + (2 + 4 * L) then 18
    else 0
  let tokMid : SolverToken cfg L Rcore :=
    { tok with rootGraph := rg, treeTok := curTreeTok, tag := tagMid }
  have hBasic {a v : ℕ} (ht : tok.tag a = v)
      (hv : v = 1 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15) :
      tagMid a = v := by
    have hlt : a < uIntBuf := htagLt (by
      rw [ht]; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hcond : a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨
        tok.tag a = 11 ∨ tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15) :=
      ⟨hlt, ht ▸ hv⟩
    dsimp only [tagMid]; rw [ite_eq_left_iff.mpr fun h => (h hcond).elim, ht]
  have hNotBasic {a : ℕ} (h : a < uIntBuf → tok.tag a = 16 ∨ tok.tag a = 18 ∨ tok.tag a = 20) :
      ¬ (a < uIntBuf ∧ (tok.tag a = 1 ∨ tok.tag a = 9 ∨ tok.tag a = 10 ∨ tok.tag a = 11 ∨
        tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15)) := by
    rintro ⟨hlt, htag⟩
    rcases h hlt with h' | h' | h' <;>
      rcases htag with h'' | h'' | h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  have hTag16 (a : ℕ) (ha : Rtree.foot tok.treeHeap curTreeTok a) : tagMid a = 16 := by
    have hnb := hNotBasic (a := a) (fun hlt => Or.inl ((hFootLoc a ha).1 hlt))
    dsimp only [tagMid]; simp only [hnb, ha, ↓reduceIte]
  have hTag20 (a : ℕ) (h1 : rg ≤ a) (h2 : a < rg + dynGraphSize G0.n tok.rootECap) :
      tagMid a = 20 := by
    obtain ⟨h20, hnf, _⟩ := hGraphLoc a h1 h2
    have hnb := hNotBasic (a := a) (fun hlt => Or.inr (Or.inr (h20 hlt)))
    dsimp only [tagMid]
    rw [ite_eq_right_iff.mpr fun h => (hnb h).elim, ite_eq_right_iff.mpr fun h => (hnf h).elim]
    exact ite_eq_left_iff.mpr fun h => (h ⟨h1, h2⟩).elim
  have hTag18 (ei : ℕ) (hei : ei ∈ G0.E) (hnot : ei ∉ F) (j : ℕ) (hj : j < 2 + 4 * L) :
      tagMid (st.mem (tok.edgeRecords + ei) + j) = 18 := by
    obtain ⟨h18, hnf, hnrg, _⟩ := hRecLoc ei hei hnot j hj
    have hnb := hNotBasic (a := st.mem (tok.edgeRecords + ei) + j)
      (fun hlt => Or.inr (Or.inl (h18 hlt)))
    have hnrg' : ¬ (rg ≤ st.mem (tok.edgeRecords + ei) + j ∧
        st.mem (tok.edgeRecords + ei) + j < rg + dynGraphSize G0.n tok.rootECap) := by
      rintro ⟨h1, h2⟩; omega
    dsimp only [tagMid]
    rw [ite_eq_right_iff.mpr fun h => (hnb h).elim, ite_eq_right_iff.mpr fun h => (hnf h).elim,
      ite_eq_right_iff.mpr fun h => (hnrg' h).elim]
    exact ite_eq_left_iff.mpr fun h =>
      (h ⟨ei, hei, hnot, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩).elim
  have hTagLtMid (a : ℕ) (hne : tagMid a ≠ 0) : a < heapX := by
    dsimp only [tagMid] at hne
    split_ifs at hne with h1 h2 h3 h4
    · exact lt_of_lt_of_le h1.1 hBaseLe
    · exact (hFootLoc a h2).2
    · exact (hGraphLoc a h3.1 h3.2).2.2
    · obtain ⟨ei, hei, hnot, ha1, ha2⟩ := h4
      have := (hRecLoc ei hei hnot (a - st.mem (tok.edgeRecords + ei)) (by omega)).2.2.2
      rwa [show st.mem (tok.edgeRecords + ei) + (a - st.mem (tok.edgeRecords + ei)) = a by
        omega] at this
    · exact (hne rfl).elim
  -- the context and the start of the sync loop
  have hTreeHeapLt : tok.treeHeap < 2 ^ w :=
    lt_trans (htagLt (by rw [hT16 tok.treeHeap (pathRep_foot_base_p hTreeRep0)]; decide))
      (by omega)
  have h2nW : 2 * G0.n + 1 < 2 ^ w := by
    by_cases hn0 : model.extG.n = 0
    · omega
    · have hEnd : tok.names + 2 * tok.tree.n ≤ uIntBuf := by
        have := htagLt (by rw [hT10 (2 * tok.tree.n - 1) (by omega)]; decide); omega
      -- the header word `handle` (tag `2`) lies off the names (tag `10`)
      have hSep : tok.handle < tok.names ∨ tok.names + 2 * tok.tree.n ≤ tok.handle := by
        by_contra hc
        have h10 := hT10 (tok.handle - tok.names) (by omega)
        have h2 := hT2 0 (by omega)
        rw [show tok.names + (tok.handle - tok.names) = tok.handle + 0 by omega] at h10
        omega
      omega
  let oldF : MGraph := { G0 with E := F }
  let newF : MGraph := { G0 with E := F' }
  have ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editPtr heap0 s3.mem G0 oldF newF edits tokMid canonVal B R :=
    { fmtBits := hFmtBits, treeImpl := hTreeImpl, bindOk := hBindOk, canonOk := hCanonOk,
      isNegOk := hIsNegOk, diff := hDiff, editsAt := by rw [hs3]; exact hEditsAt,
      editsEnd := le_rfl,
      editsTag0 := fun a ha1 _ =>
        ⟨by by_contra hne; have := hTagLtMid a hne; omega, by omega⟩,
      rootGraph := by rw [hs3]; exact hRG,
      oldSub := hSub, newSub := hNewSub, newForest := hNewForest,
      oldEnds := fun _ _ => ⟨rfl, rfl⟩, newEnds := fun _ _ => ⟨rfl, rfl⟩,
      capE := hCapE,
      vtxE := fun ei hei => by
        obtain ⟨h1, h2⟩ := hRG.1 ei hei; exact ⟨hRG.2.1 _ h1, hRG.2.1 _ h2⟩,
      canonProp := hCanonP,
      tags := ⟨fun a ha => lt_of_lt_of_le (hTagLtMid a ha) (by omega),
        fun j hj => hBasic (hT1 j hj) (Or.inl rfl),
        fun j hj => hBasic (hT9 j hj) (Or.inr (Or.inl rfl)),
        fun j hj => hBasic (hT10 j (by omega)) (Or.inr (Or.inr (Or.inl rfl))),
        fun j hj => hBasic (hT11 j (by omega)) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        fun j hj => hBasic (hT12 j hj) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
        fun j hj => hBasic (hT13 j hj)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
        fun j hj => hBasic (hT14 j hj)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
        fun j hj => hBasic (hT15 j hj)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))),
        hTag16,
        fun ei hei hnot j hj => by rw [hs3]; exact hTag18 ei hei hnot j hj,
        fun a ha1 ha2 => hTag20 a ha1 ha2⟩,
      treeHeapLt := hTreeHeapLt, nW := h2nW, logW := hGn.symm ▸ hLogW,
      capT := hGn.symm ▸ hCapT, hw11 := by omega, room := hRoom }
  obtain ⟨curTrees, curFree, curDepth, hL1, hL2, hL3, hL4⟩ := hLct
  have hInvInit : WireSyncDeferInv deferSet root editPtr heap0 s3.mem G0 oldF newF edits tokMid
      canonVal B R [] edits curTree curTreeTok heap0 offCnt s3 := by
    refine ⟨rfl, h3_0, h3_1, h3_2, h3_3, by simpa using h3_6, h3_18, h3_9, h3_10, h3_11,
      h3_19, h3_20, h3_22, h3_23, h3_24, h3_25, h3_26, le_rfl, by simp, by rw [hs3]; exact hz,
      fun a ha => Or.inl ha, fun _ _ _ _ _ _ _ _ _ _ => rfl, hTreeN,
      ⟨curTrees, curFree, curDepth, hL1, hL2, by rw [hs3]; exact hL3, by rw [hs3]; exact hL4⟩,
      by rw [hs3]; exact hTreeRep, fun ei hei => by rw [hs3]; exact hSlotThr ei hei,
      fun ei hei hnot => by rw [hs3]; exact hOffSlot ei hei hnot,
      fun ei hei hnot => by rw [hs3]; exact hOffRec ei hei hnot,
      fun ei hei hnot hnd hdet => by rw [hs3]; exact hOffReady ei hei hnot hnd hdet,
      fun ei _ hnot => ⟨fun h => (hnot h).elim, fun _ => rfl⟩,
      fun e₁ he₁ e₂ he₂ hne h₁ h₂ => by rw [hs3]; exact hOffDisj e₁ he₁ e₂ he₂ hne h₁ h₂,
      by rw [hs3]; exact hOffCnt, by rw [hs3]; exact hOffInv⟩
  obtain ⟨s4, cLoop, curTree', curTreeTok', heapEnd, offCnt', rLoop, hInvEnd, hcLoop⟩ :=
    wireTreeSyncLoop_defer_runs ctx hInvInit
  obtain ⟨_, _, _, _, hr3End, _, _, _, _, _, _, _, _, _, _, _, _,
    hEndGe, hEndLe, hzEnd, hFootEnd, hFrameEnd, hTreeNEnd,
    ⟨curTrees2, curFree2, curDepth2, hLctEnd, hNumEnd, hNamedEnd, hLiveEnd⟩,
    hTreeRepEnd, hSlotThrEnd, hOffSlotEnd, hOffRecEnd, hOffReadyEnd, hOffWhereEnd, hOffDisjEnd,
    hOffCntEnd, hOffInvEnd⟩ := hInvEnd
  have hRes : applyTreeChanges oldF.E edits = F' := hDiff.result.2
  rw [hRes] at hNamedEnd hLiveEnd hSlotThrEnd hOffSlotEnd hOffRecEnd hOffReadyEnd
  rw [hRes] at hOffWhereEnd hOffDisjEnd
  dsimp only [tokMid] at hOffWhereEnd hFootEnd
  have rAll : Runs w p ω (wireSyncPhaseStmt (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
      st .normal s4 (2 + (2 + (cSetup + cLoop + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, cSetup, cLoop, rSetup, rLoop, rfl⟩), rfl⟩), rfl⟩)
  -- the frame of the sync
  have hFrame : ∀ a < heap0, a ≠ root + 11 →
      (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
      (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → s4.mem a = st.mem a := by
    intro a ha hne11 hlo hhi
    have hMid : tagMid a ≠ 9 ∧ tagMid a ≠ 10 ∧ tagMid a ≠ 11 ∧ tagMid a ≠ 13 ∧
        tagMid a ≠ 14 ∧ tagMid a ≠ 15 ∧ tagMid a ≠ 16 := by
      dsimp only [tagMid]
      split_ifs with h1 h2 h3 h4
      · exact hlo h1.1
      · by_cases hlt : a < uIntBuf
        · exact absurd ((hFootLoc a h2).1 hlt) (hlo hlt).2.2.2.2.2.2
        · exact absurd h2 (hhi (by omega))
      · decide
      · decide
      · decide
    obtain ⟨m9, m10, m11, m13, m14, m15, m16⟩ := hMid
    exact (hFrameEnd a ha hne11 m9 m10 m11 m13 m14 m15 m16).trans (by rw [hs3])
  have hTagNe (v : ℕ) (hv : v = 1 ∨ v = 2 ∨ v = 12 ∨ v = 18 ∨ v = 20) :
      v ≠ 9 ∧ v ≠ 10 ∧ v ≠ 11 ∧ v ≠ 13 ∧ v ≠ 14 ∧ v ≠ 15 ∧ v ≠ 16 := by
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide
  have hKeepTag {a v : ℕ} (ht : tok.tag a = v) (hv : v = 2 ∨ v = 12 ∨ v = 18 ∨ v = 20) :
      s4.mem a = st.mem a := by
    have hlt : a < uIntBuf := htagLt (by
      rw [ht]; rcases hv with rfl | rfl | rfl | rfl <;> decide)
    have hne11 : a ≠ root + 11 := fun h => by
      rw [h, hT1 11 (by omega)] at ht; rcases hv with rfl | rfl | rfl | rfl <;> omega
    exact hFrame a (by omega) hne11 (fun _ => ht ▸ hTagNe v (Or.inr hv)) (fun h => by omega)
  have hRoot (j : ℕ) (hj : j < 16) (hj11 : j ≠ 11) : s4.mem (root + j) = st.mem (root + j) :=
    hFrame _ (by omega) (by omega) (fun _ => by rw [hT1 j hj]; decide) (fun h => by omega)
  -- the state after the sync
  have hFootNew (a : ℕ) (ha : Rtree.foot tok.treeHeap curTreeTok' a) :
      (a < uIntBuf → tok.tag a = 16) ∧ a < heapEnd := by
    rcases hFootEnd a ha with h1 | ⟨hlo, hhi⟩
    · exact ⟨(hFootLoc a h1).1, by have := (hFootLoc a h1).2; omega⟩
    · exact ⟨fun h => by omega, hhi⟩
  have hNotFootNew {a : ℕ} (ha : a < heapX) (hnf : ¬ Rtree.foot tok.treeHeap curTreeTok a) :
      ¬ Rtree.foot tok.treeHeap curTreeTok' a := fun hf => by
    rcases hFootEnd a hf with h1 | ⟨hlo, _⟩
    · exact hnf h1
    · omega
  have hGraphNew : DynGraphAt s4.mem rg G0.n tok.rootECap G0 :=
    hRG.of_agree fun a ha1 ha2 => by
      obtain ⟨h20, hnf, hlt⟩ := hGraphLoc a ha1 ha2
      have hne11 : a ≠ root + 11 := fun h => by
        by_cases hu : a < uIntBuf
        · have := h20 hu; rw [h, hT1 11 (by omega)] at this; omega
        · omega
      exact hFrame a (by omega) hne11 (fun hu => by rw [h20 hu]; decide) (fun _ => hnf)
  have hPhEnd : TreeSyncPhaseAt L tok root uIntBuf heapEnd rg G0 F' canonVal B R deferSet
      curTree' curTreeTok' offCnt' s4.mem :=
    { baseLe := by omega
      dir := ⟨(hRoot 6 (by omega) (by omega)).trans hD6, (hRoot 7 (by omega) (by omega)).trans hD7,
        (hRoot 8 (by omega) (by omega)).trans hD8, (hRoot 9 (by omega) (by omega)).trans hD9,
        (hRoot 10 (by omega) (by omega)).trans hD10, (hRoot 12 (by omega) (by omega)).trans hD12,
        (hRoot 13 (by omega) (by omega)).trans hD13, (hRoot 14 (by omega) (by omega)).trans hD14⟩
      hdr := ⟨(hKeepTag (by simpa using hT2 0 (by omega)) (Or.inl rfl)).trans hH0,
        (hKeepTag (hT2 5 (by omega)) (Or.inl rfl)).trans hH5⟩
      graph := hGraphNew
      sub := hNewSub
      capE := hCapE
      canonProp := hCanonP
      treeN := hTreeNEnd
      lct := ⟨curTrees2, curFree2, curDepth2, hLctEnd, hNumEnd, hNamedEnd, hLiveEnd⟩
      treeRep := hTreeRepEnd
      slotThr := hSlotThrEnd
      offSlot := hOffSlotEnd
      offRec := hOffRecEnd
      offReady := hOffReadyEnd
      offDisj := hOffDisjEnd
      offCntAt := hOffCntEnd
      offInv := hOffInvEnd
      footLoc := hFootNew
      graphLoc := fun a ha1 ha2 => by
        obtain ⟨h20, hnf, hlt⟩ := hGraphLoc a ha1 ha2
        exact ⟨h20, hNotFootNew hlt hnf, by omega⟩
      recLoc := fun ei hei hnot j hj => by
        by_cases hF : ei ∈ F
        · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhereEnd ei hei hnot).1 hF
          exact ⟨fun h => by omega, hnf _ (by omega) (by omega), Or.inr (by omega), by omega⟩
        · have hEq : s4.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) :=
            ((hOffWhereEnd ei hei hnot).2 hF).trans (by rw [hs3])
          obtain ⟨h18, hnf, hnrg, hlt⟩ := hRecLoc ei hei hF j hj
          rw [hEq]
          exact ⟨h18, hNotFootNew hlt hnf, hnrg, by omega⟩ }
  refine ⟨s4, _, heapEnd, curTree', curTreeTok', offCnt', rAll, hr3End, ?_, hEndGe, hEndLe,
    hzEnd, hPhEnd, hFootEnd, fun ei hei hnot hF => ?_, fun ei hei hnot hF => ?_, hFrame, ?_⟩
  · intro r hr
    rw [runs_regs_ge_of_noWriteGe rLoop (wireTreeSyncLoop_noWriteGe70 _ _ _ _ _ _) r hr,
      runs_regs_ge_of_noWriteGe rSetup shiftTermSetupLoop_noWriteGe70 r hr]
    simp [s2, s1, Function.update_of_ne (by omega : r ≠ 29),
      Function.update_of_ne (by omega : r ≠ 27)]
  · obtain ⟨hlo, hhi, _⟩ := (hOffWhereEnd ei hei hnot).1 hF
    exact ⟨hlo, hhi⟩
  · exact ((hOffWhereEnd ei hei hnot).2 hF).trans (by rw [hs3])
  · rw [hs3] at hcLoop
    dsimp only [Rtree, tokMid] at hcLoop hcSetup ⊢
    omega

end MinCostFlow.MinRatio
