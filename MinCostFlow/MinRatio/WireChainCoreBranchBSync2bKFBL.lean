module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSync1KFBL
public import MinCostFlow.MinRatio.WireChainCoreFilterEditsKFBL
public import MinCostFlow.MinRatio.WireSuffixEdits
import WordRAM.Tactic

/-!
# Sync 2b of Branch B: the new suffix forests (`WireChainCoreBranchBSync2bKFBL`)

After Sync 2a the path tree holds the forests of the plain levels (the set `P`) and the old
forests of the rebuilt levels `i₀, …, d`, minus the deleted names of the batch. The last sync
replaces these old forests by the new ones.

The edit packer (`wireSuffixPackEditsBody`) writes the edits from the union `A` of the old forests
to the union of the new ones. Some of its cuts name deleted edges, which Sync 1 has cut already.
The filter (`wireFilterPresentEditsBody`) drops each cut whose edge is absent from the root graph,
by its presence array. Then one sync (`wireSyncPhaseStmt`) applies the rest.
`wireBranchBSync2bStmt_runs` gives the tree state for `P ∪ newE` afterwards, where `newE` is the
union of the new forests.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Sync 2b of Branch B. The forests of the levels `i₀ = reg 99, …, d = reg 75` are listed at
`reg 80 + i₀` (old) and `reg 81 + i₀` (new). The packer writes its edits after its marks, which
take `3 · intCap` words from the heap pointer (`reg 4`, with `intCap` at word `15` of the root
directory). The filter copies the edits it keeps after them, testing the presence array of the
root graph (`reg 15`). The sync then applies the kept edits, and the heap pointer moves past its
work space. -/
@[expose] def wireBranchBSync2bStmt
    (packEdits filterEdits readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
  .assign 11 (.bin .add (.reg 80) (.reg 99)) ;;
  .assign 12 (.bin .add (.reg 81) (.reg 99)) ;;
  .assign 13 (.bin .sub (.bin .add (.reg 75) (.const 1)) (.reg 99)) ;;
  .call 18 packEdits [.reg 11, .reg 12, .reg 13, .reg 10, .reg 4] ;;
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
  .assign 7 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 18))) ;;
  .assign 14 (.load (.bin .add (.reg 70) (.const 14))) ;;
  .assign 15
    (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 7) (.load (.reg 14)))) ;;
  .call 18 filterEdits [.reg 6, .reg 18, .reg 15, .reg 7] ;;
  .assign 6 (.reg 7) ;;
  wireSyncPhaseStmt readTree cutTree linkTree bind canonCopy isNeg ;;
  .assign 4 (.reg 3)

theorem wireBranchBSync2bStmt_noRand
    (packEdits filterEdits readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (wireBranchBSync2bStmt packEdits filterEdits readTree cutTree linkTree bind canonCopy
      isNeg).NoRand := by
  simp [wireBranchBSync2bStmt, wireSyncPhaseStmt_noRand, Stmt.NoRand]

set_option maxHeartbeats 1600000 in
/-- The run of Sync 2b of Branch B from the tree state for `P ∪ (oldE ∩ G0.E)` at the heap
pointer `heap`. The old and new forests of the levels `i₀, …, d` are listed below `heap`. The new
ones lie in the root graph `G0`, the old ones below its edge capacity, and neither meets `P`.
Afterwards the tree state holds for `P ∪ newE` with the heap pointer `heapEnd = reg 4`, the
records of the cut edges lie in the new heap, and no word below `heap` changes but those that a
sync may write. The packer and the filter cost linear time in the size `S` of the forests, and
the sync pays for at most `|oldE \ newE| + |newE \ oldE|` edits. -/
theorem wireBranchBSync2bStmt_runs
    {w L P m V psi k epsExp drainUnit initTree bind canonCopy isNeg packEdits filterEdits
      root uIntBuf heap rg offCnt oldPtrs newPtrs dd i₀ : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {Fp : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {oldFs newFs : List MGraph}
    (hPack : p.procs[packEdits]? = some wireSuffixPackEditsBody)
    (hFilter : p.procs[filterEdits]? = some wireFilterPresentEditsBody)
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
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heap rg G0 (Fp ∪ (graphListEdgeUnion oldFs ∩ G0.E))
      canonVal B R deferSet curTree curTreeTok offCnt st.mem)
    (hNewForest : ({ G0 with E := Fp ∪ graphListEdgeUnion newFs } : MGraph).IsForest)
    (hNewSub : graphListEdgeUnion newFs ⊆ G0.E)
    (hPOld : ∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs)
    (hPNew : ∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs)
    (hOldCap : ∀ e ∈ graphListEdgeUnion oldFs, e < tok.rootECap)
    (hi₀ : i₀ ≤ dd + 1) (hOldLen : oldFs.length = dd + 1 - i₀)
    (hNewLen : newFs.length = dd + 1 - i₀)
    (hOld : ForestPtrListAt st.mem (oldPtrs + i₀) oldFs tok.intCap heap)
    (hNew : ForestPtrListAt st.mem (newPtrs + i₀) newFs tok.intCap heap)
    (hIntCap : st.mem (root + 15) = tok.intCap)
    (hRegs : st.regs 4 = heap ∧ st.regs 70 = root ∧ st.regs 73 = tok.handle ∧
      st.regs 75 = dd ∧ st.regs 80 = oldPtrs ∧ st.regs 81 = newPtrs ∧ st.regs 99 = i₀)
    (hz : ZeroFrom st.mem heap)
    (hRoom : heap + 3 * tok.intCap + 4 * (graphListEdgeSum oldFs + graphListEdgeSum newFs) +
      (graphListEdgeSum oldFs + graphListEdgeSum newFs) * wireTreeSyncEditSpace L + 1 < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let oldE := graphListEdgeUnion oldFs
    let newE := graphListEdgeUnion newFs
    let S := graphListEdgeSum oldFs + graphListEdgeSum newFs
    ∃ (out : State) (cost heapEnd : ℕ) (curTree' : PathTreeState) (curTreeTok' : Rtree.τ)
      (offCnt' : ℕ),
      Runs w p ω (wireBranchBSync2bStmt packEdits filterEdits (opTree 4) (opTree 1) (opTree 0)
        bind canonCopy isNeg) st .normal out cost ∧
      out.regs 4 = heapEnd ∧ (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      heap ≤ heapEnd ∧
      heapEnd ≤ heap + 3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L ∧
      ZeroFrom out.mem heapEnd ∧
      TreeSyncPhaseAt L tok root uIntBuf heapEnd rg G0 (Fp ∪ newE) canonVal B R deferSet
        curTree' curTreeTok' offCnt' out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap curTreeTok a ∨ (heap ≤ a ∧ a < heapEnd)) ∧
      (∀ ei ∈ G0.E, ei ∉ Fp ∪ newE → ei ∉ Fp ∪ (oldE ∩ G0.E) →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ ei ∈ G0.E, ei ∉ Fp ∪ newE → ei ∈ Fp ∪ (oldE ∩ G0.E) →
        heap ≤ out.mem (tok.edgeRecords + ei) ∧
        out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapEnd) ∧
      (∀ a < heap, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
        ((oldE \ newE).card + (newE \ oldE).card) * (wireTreeSyncEditCost L drainUnit + 2) +
          155 * S + 210 * (dd + 1 - i₀) + 350 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := by
  classical
  intro Rtree oldE newE S
  obtain ⟨hr4, hr70, hr73, hr75, hr80, hr81, hr99⟩ := hRegs
  have hS : S = graphListEdgeSum oldFs + graphListEdgeSum newFs := rfl
  have hRoomS : heap + 3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L + 1 < 2 ^ w := hRoom
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
  obtain ⟨_, _, hGCap, hVCap, _, _, _, _, _, _, _, hEPres, _⟩ := hPh.graph
  have hVCap' : st.mem rg = G0.n := by simpa [dgVCapOff] using hVCap
  have hRgAt : st.mem (root + 14) = rg := hPh.dir.2.2.2.2.2.2.2
  have hOldB := hOld.1
  have hNewB := hNew.1
  -- the set-up moves
  let s1 := { st with regs := Function.update st.regs 10 tok.intCap }
  have r1 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 15)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by
      simp [Expr.eval, BinOp.eval, hr70, show 15 < 2 ^ w by omega,
        show root + 15 < 2 ^ w by omega, hIntCap], rfl, rfl, rfl⟩
  let s2 := { s1 with regs := Function.update s1.regs 11 (oldPtrs + i₀) }
  have r2 : Runs w p ω (.assign 11 (.bin .add (.reg 80) (.reg 99))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨oldPtrs + i₀, by
      simp [Expr.eval, BinOp.eval, s1, hr80, hr99, show oldPtrs + i₀ < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  let s3 := { s2 with regs := Function.update s2.regs 12 (newPtrs + i₀) }
  have r3 : Runs w p ω (.assign 12 (.bin .add (.reg 81) (.reg 99))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨newPtrs + i₀, by
      simp [Expr.eval, BinOp.eval, s2, s1, hr81, hr99, show newPtrs + i₀ < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  let cnt := dd + 1 - i₀
  have hcnt : cnt = dd + 1 - i₀ := rfl
  let s4 := { s3 with regs := Function.update s3.regs 13 cnt }
  have r4 : Runs w p ω (.assign 13 (.bin .sub (.bin .add (.reg 75) (.const 1)) (.reg 99))) s3
      .normal s4 6 :=
    runs_assign_iff.mpr ⟨cnt, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, hr75, hr99, show 1 < 2 ^ w by omega,
        show dd + 1 < 2 ^ w by omega, show dd + 1 - i₀ < 2 ^ w by omega, cnt], rfl, rfl, rfl⟩
  -- the packer
  obtain ⟨outP, cP, edits, rP, hcP, hLenP, hEdP, hDiffP, hzP, hFrP⟩ :=
    wireSuffixPackEdits_runs (w := w) (p := p) (ω := ω) (pos := s4.pos) (mem := s4.mem)
      (oldPtrs := oldPtrs + i₀) (newPtrs := newPtrs + i₀) (cnt := cnt) (intCap := tok.intCap)
      (heap := heap) (oldFs := oldFs) (newFs := newFs) hOldLen hNewLen hOld hNew hz
      (by omega) (by omega)
  have hFrP' : ∀ a < heap, outP.mem a = st.mem a := hFrP
  let s5 : State :=
    { regs := Function.update s4.regs 18 edits.length, mem := outP.mem, pos := outP.pos }
  have r5 : Runs w p ω (.call 18 packEdits [.reg 11, .reg 12, .reg 13, .reg 10, .reg 4]) s4
      .normal s5 (5 + cP + 1) :=
    runs_call_iff.mpr ⟨[oldPtrs + i₀, newPtrs + i₀, cnt, tok.intCap, heap],
      wireSuffixPackEditsBody, .returned edits.length, outP, cP,
      by simp [evalArgs, Expr.eval, s4, s3, s2, s1, hr4], hPack, rP, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
  -- the filter
  let src := heap + 3 * tok.intCap
  have hsrc : src = heap + 3 * tok.intCap := rfl
  let outBuf := src + 2 * edits.length
  have houtBuf : outBuf = src + 2 * edits.length := rfl
  let s6 := { s5 with regs := Function.update s5.regs 6 src }
  have r6 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10)))) s5
      .normal s6 6 :=
    runs_assign_iff.mpr ⟨src, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, hr4, show 3 < 2 ^ w by omega,
        show 3 * tok.intCap < 2 ^ w by omega, show heap + 3 * tok.intCap < 2 ^ w by omega, src],
      rfl, rfl, rfl⟩
  let s7 := { s6 with regs := Function.update s6.regs 7 outBuf }
  have r7 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 18)))) s6
      .normal s7 6 :=
    runs_assign_iff.mpr ⟨outBuf, by
      simp [Expr.eval, BinOp.eval, s6, s5, show 2 < 2 ^ w by omega,
        show 2 * edits.length < 2 ^ w by omega,
        show heap + 3 * tok.intCap + 2 * edits.length < 2 ^ w by omega, src, outBuf],
      rfl, rfl, rfl⟩
  let s8 := { s7 with regs := Function.update s7.regs 14 rg }
  have r8 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 70) (.const 14)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨rg, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, hr70, show 14 < 2 ^ w by omega,
        show root + 14 < 2 ^ w by omega, hFrP' (root + 14) (by omega), hRgAt], rfl, rfl, rfl⟩
  let pres := dgEPresBase rg G0.n
  have hpres : pres = rg + 4 + 7 * G0.n := rfl
  let s9 := { s8 with regs := Function.update s8.regs 15 pres }
  have r9 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 14) (.const 4))
      (.bin .mul (.const 7) (.load (.reg 14))))) s8 .normal s9 9 :=
    runs_assign_iff.mpr ⟨pres, by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, show 4 < 2 ^ w by omega,
        show 7 < 2 ^ w by omega, hFrP' rg (by omega), hVCap', show rg + 4 < 2 ^ w by omega,
        show 7 * G0.n < 2 ^ w by omega, show rg + 4 + 7 * G0.n < 2 ^ w by omega, hpres],
      rfl, rfl, rfl⟩
  have hLenS : edits.length ≤ S := hLenP
  have hEdgeCap : ∀ ch ∈ edits, ∀ tg e, treeEditWords ch = [tg, e] → e < tok.rootECap := by
    intro ch hch tg e hw
    cases ch with
    | insert e' =>
      simp only [treeEditWords, List.cons.injEq, and_true] at hw
      rw [← hw.2]
      exact hGCap e' (hNewSub (Finset.mem_sdiff.mp (hDiffP.insert_mem_sdiff hch)).1)
    | delete e' =>
      simp only [treeEditWords, List.cons.injEq, and_true] at hw
      rw [← hw.2]
      exact hOldCap e' (Finset.mem_sdiff.mp (hDiffP.delete_mem_sdiff hch)).1
  have hPresAt (e : ℕ) (he : e < tok.rootECap) :
      outP.mem (pres + e) = if e ∈ G0.E then 1 else 0 :=
    (hFrP' _ (by omega)).trans (hEPres e he)
  have hPresF : ∀ i (h : i < edits.length), ∀ tg e, treeEditWords edits[i] = [tg, e] →
      pres + e < outBuf ∧ s9.mem (pres + e) ≤ 1 := fun i hi tg e hw => by
    have he := hEdgeCap _ (List.getElem_mem hi) tg e hw
    refine ⟨by omega, ?_⟩
    show outP.mem (pres + e) ≤ 1
    rw [hPresAt e he]
    split_ifs <;> omega
  obtain ⟨outF, cF, rF, hcF, hEdF, hzF, hFrF⟩ :=
    wireFilterPresentEditsBody_runs (w := w) (p := p) (ω := ω) (src := src)
      (len := edits.length) (pres := pres) (outBuf := outBuf) (pos := s9.pos) (mem := s9.mem)
      (edits := edits) rfl hEdP (le_refl _) hPresF hzP (by omega) (by omega)
  let kept := filterPresentEdits (fun e => outP.mem (pres + e)) edits
  have hKeptLe : kept.length ≤ edits.length := filterPresentEdits_length_le _ _
  let s10 : State :=
    { regs := Function.update s9.regs 18 kept.length, mem := outF.mem, pos := outF.pos }
  have r10 : Runs w p ω (.call 18 filterEdits [.reg 6, .reg 18, .reg 15, .reg 7]) s9 .normal s10
      (4 + cF + 1) :=
    runs_call_iff.mpr ⟨[src, edits.length, pres, outBuf], wireFilterPresentEditsBody,
      .returned kept.length, outF, cF, by simp [evalArgs, Expr.eval, s9, s8, s7, s6, s5],
      hFilter, rF, rfl, rfl, by simp [argsSize, Expr.size]⟩
  let s11 := { s10 with regs := Function.update s10.regs 6 outBuf }
  have r11 : Runs w p ω (.assign 6 (.reg 7)) s10 .normal s11 2 :=
    runs_assign_iff.mpr ⟨outBuf, by simp [Expr.eval, s10, s9, s8, s7], rfl, rfl, rfl⟩
  -- the sync
  have hFrAll : ∀ a < heap, s11.mem a = st.mem a := fun a ha =>
    (hFrF a (by omega)).trans (hFrP' a ha)
  have hPh11 := TreeSyncPhaseAt.of_agree hRep0_keep hFootLt hGn hPh hFrAll
  have hPresIff : ∀ e ∈ oldE, outP.mem (pres + e) ≠ 0 ↔ e ∈ G0.E := fun e he => by
    rw [hPresAt e (hOldCap e he)]
    split_ifs with h <;> simp [h]
  have hDiffK : TreeEditDifference (Fp ∪ (oldE ∩ G0.E)) (Fp ∪ newE) kept :=
    treeEditDifference_filterPresent (pres := fun e => outP.mem (pres + e)) hDiffP hPresIff
      hNewSub hPOld hPNew
  have hFSub : Fp ∪ newE ⊆ G0.E := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hPh.sub (Finset.mem_union_left _ h)
    · exact hNewSub h
  have hKS : kept.length * wireTreeSyncEditSpace L ≤ S * wireTreeSyncEditSpace L :=
    Nat.mul_le_mul_right _ (by omega)
  have hEdLen : edits.length = (oldE \ newE).card + (newE \ oldE).card := hDiffP.result.1
  have hKE : kept.length * (wireTreeSyncEditCost L drainUnit + 2) ≤
      ((oldE \ newE).card + (newE \ oldE).card) * (wireTreeSyncEditCost L drainUnit + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨s12, cS, heapEnd, curTree', curTreeTok', offCnt', rS, hr3, hRegsS, hEndGe, hEndLe,
      hzEnd, hPhEnd, hFootEnd, hCutRec, hKeepRec, hFrameS, hcS⟩ :=
    wireSyncPhaseStmt_runs (st := s11) (initTree := initTree) (drainUnit := drainUnit) hFmtBits
      hw18 hTreeImpl hBindOk hCanonOk hIsNegOk hRep0_keep hFootLt hGn hLogW hCapT hPh11 hDiffK
      hFSub hNewForest hEdF (by omega : heap ≤ outBuf) hzF
      ⟨by simp [s11], by simp [s11, s10],
        by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr70],
        by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr73]⟩
      (by omega)
  let s13 := { s12 with regs := Function.update s12.regs 4 heapEnd }
  have r13 : Runs w p ω (.assign 4 (.reg 3)) s12 .normal s13 2 :=
    runs_assign_iff.mpr ⟨heapEnd, by simp [Expr.eval, hr3], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (wireBranchBSync2bStmt packEdits filterEdits (opTree 4) (opTree 1)
      (opTree 0) bind canonCopy isNeg) st .normal s13
      (5 + (4 + (4 + (6 + ((5 + cP + 1) + (6 + (6 + (5 + (9 + ((4 + cF + 1) +
        (2 + (cS + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, _, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, _, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, _, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, _, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, _, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨s10, _, _, r10,
      runs_seq_iff.mpr (Or.inr ⟨s11, _, _, r11,
      runs_seq_iff.mpr (Or.inr ⟨s12, _, _, rS, r13, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨s13, _, heapEnd, curTree', curTreeTok', offCnt', rAll, by simp [s13], ?_, by omega,
    by omega, hzEnd, hPhEnd, fun a ha => ?_, fun ei hei hnot hnot' => ?_,
    fun ei hei hnot hin => ?_, fun a ha hne11 hlo hhi => ?_, ?_⟩
  · intro r hr
    simp only [s13, Function.update_of_ne (by omega : r ≠ 4)]
    rw [hRegsS r hr]
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 6),
      Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 15),
      Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 7),
      Function.update_of_ne (by omega : r ≠ 13), Function.update_of_ne (by omega : r ≠ 12),
      Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 10)]
  · rcases hFootEnd a ha with h | ⟨hlo, hhi⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hhi⟩
  · exact (hKeepRec ei hei hnot hnot').trans
      (hFrAll _ (lt_of_lt_of_le (htagLt (by rw [hT13 ei (hCapE ei hei)]; decide)) (by omega)))
  · obtain ⟨hlo, hhi⟩ := hCutRec ei hei hnot hin
    exact ⟨show heap ≤ s12.mem (tok.edgeRecords + ei) by omega, hhi⟩
  · exact (hFrameS a (by omega) hne11 hlo hhi).trans (hFrAll a ha)
  · have hPhi : Rtree.phi tok.treeHeap curTreeTok s11.mem =
        Rtree.phi tok.treeHeap curTreeTok st.mem := rfl
    have hPhi2 : Rtree.phi tok.treeHeap curTreeTok' s13.mem =
        Rtree.phi tok.treeHeap curTreeTok' s12.mem := rfl
    rw [hPhi] at hcS
    rw [hPhi2]
    dsimp only [Rtree] at hcS ⊢
    omega

end MinCostFlow.MinRatio
