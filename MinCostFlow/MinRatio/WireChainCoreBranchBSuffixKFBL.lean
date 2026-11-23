module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSync2aKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSync2bKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBPushRunKFBL
import WordRAM.Tactic

/-!
# The suffix of Branch B (`WireChainCoreBranchBSuffixKFBL`)

After the exit of its loop, Branch B brings the path tree up to date and returns:
1. Sync 2a cuts the edges that the plain levels drop from their forests (`wireBranchBSync2aStmt`);
2. `reg 99` gets `firstReb` from the select base;
3. Sync 2b swaps the old forests of the rebuilt levels for the new ones (`wireBranchBSync2bStmt`);
4. the inserted names of the batch that are off the tree go onto the off-ready list
   (`wirePushInsertedBody`, called with the root, the batch and `L`);
5. the core returns the heap pointer.

`wireBranchBSuffixKFBL_runs` runs these five steps from a tree state on the new root graph. The
words that the later steps read (the select base, the forest lists of Sync 2b, the batch of the
push) must keep their values across the syncs. The proof takes a set `K` of words for this: each
word of `K` lies below the heap pointer, is not the count word, has none of the tags the syncs
write, and is off the tree when it lies above `uIntBuf`. `ForestPtrListAt.of_agree_on` moves a
forest list across a memory change that keeps such words.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The suffix of Branch B: Sync 2a, the load of `firstReb` into `reg 99`, Sync 2b, the push of
the inserted names (root, batch and `L` as arguments), and the return of the heap pointer. -/
@[expose] def wireBranchBSuffixKFBL (emitCuts packEdits filterEdits readTree cutTree linkTree
    bind canonCopy isNeg pushInsProc : ℕ) : Stmt :=
  wireBranchBSync2aStmt emitCuts readTree cutTree linkTree bind canonCopy isNeg ;;
  .assign 99 (.load (.reg 72)) ;;
  wireBranchBSync2bStmt packEdits filterEdits readTree cutTree linkTree bind canonCopy isNeg ;;
  .call 10 pushInsProc [.reg 70, .reg 87, .reg 94] ;;
  .ret (.reg 4)

theorem wireBranchBSuffixKFBL_noRand (emitCuts packEdits filterEdits readTree cutTree linkTree
    bind canonCopy isNeg pushInsProc : ℕ) :
    (wireBranchBSuffixKFBL emitCuts packEdits filterEdits readTree cutTree linkTree bind
      canonCopy isNeg pushInsProc).NoRand := by
  simp only [wireBranchBSuffixKFBL, Stmt.NoRand]
  exact ⟨wireBranchBSync2aStmt_noRand .., trivial, wireBranchBSync2bStmt_noRand .., trivial,
    trivial⟩

/-- A forest list moves to a memory that agrees with the old one on a set `K` that holds its
pointer cells and the words of its graphs, and to any larger bound. -/
theorem ForestPtrListAt.of_agree_on {mem mem' : ℕ → ℕ} {ptrBase intCap bound bound' : ℕ}
    {Fs : List MGraph} {K : ℕ → Prop} (h : ForestPtrListAt mem ptrBase Fs intCap bound)
    (hK : ∀ (t : ℕ) (ht : t < Fs.length), K (ptrBase + t) ∧
      ∀ vc ec, DynGraphAt mem (mem (ptrBase + t)) vc ec Fs[t] →
        ∀ x, mem (ptrBase + t) ≤ x → x < mem (ptrBase + t) + dynGraphSize vc ec → K x)
    (hag : ∀ x, K x → mem' x = mem x) (hb : bound ≤ bound') :
    ForestPtrListAt mem' ptrBase Fs intCap bound' := by
  refine ⟨h.1.trans hb, fun t ht => ?_⟩
  obtain ⟨vc, ec, hG, hEnd, hCap⟩ := h.2 t ht
  obtain ⟨hKp, hKb⟩ := hK t ht
  have hp := hag _ hKp
  refine ⟨vc, ec, ?_, by rw [hp]; omega, hCap⟩
  rw [hp]
  exact dynGraphAt_of_agree hG (fun x h1 h2 => hag x (hKb vc ec hG x h1 h2))

/-- The words that the suffix of Branch B keeps across its two syncs and the push, for the tree
token `curTreeTok` at the start of the suffix and the heap pointer `heapX`: below `heapX`, not the
count word `root + 11`, with none of the tags `9`, …, `16` but `12` below `uIntBuf`, and off the
tree above `uIntBuf`. -/
@[expose] def BranchBSuffixKeep (L : ℕ) {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (root uIntBuf heapX : ℕ)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (a : ℕ) : Prop :=
  a < heapX ∧ a ≠ root + 11 ∧
  (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
    tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) ∧
  (uIntBuf ≤ a →
    ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a)

set_option maxHeartbeats 3200000 in
/-- **The suffix of Branch B.** From the tree state on the root graph `G0` (at `rg`) for the forest
`F` with deferred set `N` and heap pointer `heapX = reg 4`, the suffix runs and returns the heap
pointer `nextHeap`. Sync 2a cuts the entries of the lists `fDel j` of the `n` plain levels that are
in `G0` (the set `Y`); the rest of `F` is `Fp ∪ (oldE ∩ G0.E)` (`hSplit`), with `oldE` the union of
the old forests `oldFs` of the rebuilt levels `i₀, …, dd`, which Sync 2b swaps for the new forests
`newFs`. The push takes the inserted names of the batch `Ub` at `uIntBuf` out of the deferred set.
Afterwards the tree state holds for `Fp ∪ newE` with deferred set `N \ ins Ub`, the new words of
the tree and the records of the cut edges lie in `[heapX, nextHeap)`, and below `heapX` only the
words that the syncs and the push may write change. -/
theorem wireBranchBSuffixKFBL_runs
    {w L P m V psi k epsExp drainUnit initTree bind canonCopy isNeg emitCuts packEdits
      filterEdits pushProc pushInsProc root uIntBuf heapX rg offCnt selBase n oldPtrs newPtrs dd i₀
      totalWords : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 Gb : MGraph} {F Fp N : Finset ℕ} {canonVal : ℕ → PathEdgeValue}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {fPtr : ℕ → ℕ} {fDel : ℕ → List ℕ} {oldFs newFs : List MGraph} {Ub : List Update}
    (hEmit : p.procs[emitCuts]? = some wireEmitTreeCutsBody)
    (hPack : p.procs[packEdits]? = some wireSuffixPackEditsBody)
    (hFilter : p.procs[filterEdits]? = some wireFilterPresentEditsBody)
    (hPushP : p.procs[pushProc]? = some (offTreePushBody isNeg))
    (hPushIns : p.procs[pushInsProc]? = some (wirePushInsertedBody pushProc))
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
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R N curTree
      curTreeTok offCnt st.mem)
    -- Sync 2a
    (hForest : ({ G0 with E := F } : MGraph).IsForest)
    (hSlot : ∀ j < n, st.mem (selBase + 1 + 12 * j + 2) = fPtr j ∧
      st.mem (selBase + 1 + 12 * j + 3) = (fDel j).length ∧ ListAt st.mem (fPtr j) (fDel j) ∧
      fPtr j + (fDel j).length ≤ heapX ∧ selBase + 1 + 12 * j + 3 < heapX)
    (hDelCap : ∀ j < n, ∀ e ∈ fDel j, e < tok.rootECap)
    (hInF : ∀ j < n, ∀ e ∈ fDel j, e ∈ G0.E → e ∈ F)
    (hNd : ((List.range n).flatMap fDel).Nodup)
    -- Sync 2b
    (hSplit : ∀ Y : Finset ℕ, (∀ e, e ∈ Y ↔ (∃ j < n, e ∈ fDel j) ∧ e ∈ G0.E) →
      F \ Y = Fp ∪ (graphListEdgeUnion oldFs ∩ G0.E))
    (hNewForest : ({ G0 with E := Fp ∪ graphListEdgeUnion newFs } : MGraph).IsForest)
    (hNewSub : graphListEdgeUnion newFs ⊆ G0.E)
    (hPOld : ∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs)
    (hPNew : ∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs)
    (hOldCap : ∀ e ∈ graphListEdgeUnion oldFs, e < tok.rootECap)
    (hi₀ : i₀ ≤ dd + 1) (hOldLen : oldFs.length = dd + 1 - i₀)
    (hNewLen : newFs.length = dd + 1 - i₀)
    (hOld : ForestPtrListAt st.mem (oldPtrs + i₀) oldFs tok.intCap heapX)
    (hNew : ForestPtrListAt st.mem (newPtrs + i₀) newFs tok.intCap heapX)
    (hOldK : ∀ (t : ℕ) (ht : t < oldFs.length),
      BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok (oldPtrs + i₀ + t) ∧
      ∀ vc ec, DynGraphAt st.mem (st.mem (oldPtrs + i₀ + t)) vc ec oldFs[t] →
        ∀ x, st.mem (oldPtrs + i₀ + t) ≤ x → x < st.mem (oldPtrs + i₀ + t) + dynGraphSize vc ec →
          BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok x)
    (hNewK : ∀ (t : ℕ) (ht : t < newFs.length),
      BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok (newPtrs + i₀ + t) ∧
      ∀ vc ec, DynGraphAt st.mem (st.mem (newPtrs + i₀ + t)) vc ec newFs[t] →
        ∀ x, st.mem (newPtrs + i₀ + t) ≤ x → x < st.mem (newPtrs + i₀ + t) + dynGraphSize vc ec →
          BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok x)
    (hIntCap : st.mem (root + 15) = tok.intCap)
    (hSelW : st.mem selBase = i₀)
    (hSelK : BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok selBase)
    -- the push
    (hSmall : SmallBatchAt st.mem uIntBuf Gb Ub totalWords)
    (hEdgeOnly : ∀ u ∈ Ub, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < totalWords, st.mem (uIntBuf + j) < 2 ^ w)
    (hBatchK : ∀ x, uIntBuf ≤ x → x < uIntBuf + totalWords →
      BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok x)
    (hInsCap : ∀ e ∈ batchInsertedEdges Ub, e < tok.rootECap)
    -- registers and room
    (hRegs : st.regs 4 = heapX ∧ st.regs 70 = root ∧ st.regs 72 = selBase ∧
      st.regs 73 = tok.handle ∧ st.regs 75 = dd ∧ st.regs 80 = oldPtrs ∧
      st.regs 81 = newPtrs ∧ st.regs 87 = uIntBuf ∧ st.regs 94 = L)
    (hSel : st.regs 96 = n)
    (hz : ZeroFrom st.mem heapX)
    (hRoom :
      let T := ∑ j ∈ Finset.range n, (fDel j).length
      let S := graphListEdgeSum oldFs + graphListEdgeSum newFs
      heapX + (2 * T + T * wireTreeSyncEditSpace L) +
        (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) + 1 < 2 ^ w)
    (hLW : L < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let T := ∑ j ∈ Finset.range n, (fDel j).length
    let oldE := graphListEdgeUnion oldFs
    let newE := graphListEdgeUnion newFs
    let S := graphListEdgeSum oldFs + graphListEdgeSum newFs
    ∃ (out : State) (cost nextHeap : ℕ) (curTree' : PathTreeState) (curTreeTok' : Rtree.τ)
      (offCnt' : ℕ),
      (∀ ei ∈ G0.E, ei ∈ F → ei ∉ Fp ∪ newE →
        heapX ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ nextHeap) ∧
      Runs w p ω (wireBranchBSuffixKFBL emitCuts packEdits filterEdits (opTree 4) (opTree 1)
        (opTree 0) bind canonCopy isNeg pushInsProc) st (.returned nextHeap) out cost ∧
      heapX ≤ nextHeap ∧
      nextHeap ≤ heapX + (2 * T + T * wireTreeSyncEditSpace L) +
        (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) ∧
      ZeroFrom out.mem nextHeap ∧
      TreeSyncPhaseAt L tok root uIntBuf nextHeap rg G0 (Fp ∪ newE) canonVal B R
        (N \ (batchInsertedEdges Ub).toFinset) curTree' curTreeTok' offCnt' out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap curTreeTok a ∨ (heapX ≤ a ∧ a < nextHeap)) ∧
      (∀ ei ∈ G0.E, ei ∉ Fp ∪ newE →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∨
        (heapX ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ nextHeap)) ∧
      (∀ ei ∈ G0.E, ei ∉ F → ei ∉ Fp ∪ newE →
        out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
      (∀ a, BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok a → out.mem a = st.mem a) ∧
      (∀ a < heapX, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
        T * (wireTreeSyncEditCost L drainUnit + 2) + 40 * T + 64 * n + 175 +
          ((oldE \ newE).card + (newE \ oldE).card) * (wireTreeSyncEditCost L drainUnit + 2) +
          155 * S + 210 * (dd + 1 - i₀) + 350 +
          (160 * Ub.length + 60 + Ub.length * drainUnit) + 20 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := by
  classical
  intro Rtree T oldE newE S
  obtain ⟨hr4, hr70, hr72, hr73, hr75, hr80, hr81, hr87, hr94⟩ := hRegs
  have hRoom' : heapX + (2 * T + T * wireTreeSyncEditSpace L) +
      (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) + 1 < 2 ^ w := hRoom
  have hRoomT : heapX + 2 * T + T * wireTreeSyncEditSpace L + 1 < 2 ^ w := by omega
  -- Sync 2a
  obtain ⟨s1, c1, h1, tr1, tt1, oc1, r1, hs1r4, hs1r99, hs1regs, hH1lo, hH1hi, hz1, hPh1, hX,
      hFoot1, hRecKeep1, hRecCut1, hFr1, hc1⟩ :=
    wireBranchBSync2aStmt_runs (n := n) (selBase := selBase) (fPtr := fPtr) (fDel := fDel)
      hEmit hFmtBits hw18 hTreeImpl hBindOk hCanonOk hIsNegOk hRep0 hFootLt hGn hLogW hCapT hPh
      hForest hSlot hDelCap hInF hNd ⟨hr4, hr70, hr72, hr73⟩ hSel hz hRoomT
  set X := levelCutsOf (fun e => st.mem (dgEPresBase rg G0.n + e)) fDel n with hXdef
  -- the words of `K` keep their values across Sync 2a
  have hK1 : ∀ a, BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok a → s1.mem a = st.mem a :=
    fun a ⟨ha, h11, htag, hft⟩ => hFr1 a ha h11 htag hft
  have hSplitX : F \ X.toFinset = Fp ∪ (oldE ∩ G0.E) :=
    hSplit X.toFinset (fun e => by rw [List.mem_toFinset]; exact hX e)
  rw [hSplitX] at hPh1
  -- `reg 99 := firstReb`
  let s2 : State := { s1 with regs := Function.update s1.regs 99 i₀ }
  have r2 : Runs w p ω (.assign 99 (.load (.reg 72))) s1 .normal s2 3 := by
    refine runs_assign_iff.mpr ⟨i₀, ?_, rfl, rfl, rfl⟩
    have h72 : s1.regs 72 = selBase := by
      rw [hs1regs 72 (by omega) (by omega) (by omega)]; exact hr72
    simp [Expr.eval, h72, hK1 selBase hSelK, hSelW]
  have hs2regs : ∀ r, 70 ≤ r → r ≠ 96 → r ≠ 99 → s2.regs r = st.regs r := fun r hr h96 h99 => by
    simp only [s2, Function.update_of_ne h99]; exact hs1regs r hr h96 h99
  -- Sync 2b
  have hOld2 : ForestPtrListAt s2.mem (oldPtrs + i₀) oldFs tok.intCap h1 :=
    ForestPtrListAt.of_agree_on hOld (fun t ht => hOldK t ht) hK1 hH1lo
  have hNew2 : ForestPtrListAt s2.mem (newPtrs + i₀) newFs tok.intCap h1 :=
    ForestPtrListAt.of_agree_on hNew (fun t ht => hNewK t ht) hK1 hH1lo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := id hRep0
  obtain ⟨hOwnOfTag, hT1, _⟩ := hTags0
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hRoot15 : root + 15 < uIntBuf := htagLt (by rw [hT1 15 (by omega)]; decide)
  have hBaseLe := hPh.baseLe
  have hK15 : BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok (root + 15) := by
    have h1t := hT1 15 (by omega)
    refine ⟨by omega, by omega, fun _ => ?_, fun h => absurd h (by omega)⟩
    rw [h1t]; decide
  have hRoomS : h1 + 3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L + 1 < 2 ^ w := by
    have : h1 ≤ heapX + 2 * T + T * wireTreeSyncEditSpace L := hH1hi
    omega
  obtain ⟨s3, c3, h3, tr3, tt3, oc3, r3, hs3r4, hs3regs, hH3lo, hH3hi, hz3, hPh3, hFoot3,
      hRecKeep3, hRecCut3, hFr3, hc3⟩ :=
    wireBranchBSync2bStmt_runs (st := s2) (oldPtrs := oldPtrs) (newPtrs := newPtrs) (dd := dd) (i₀ := i₀)
      (oldFs := oldFs) (newFs := newFs) (Fp := Fp)
      hPack hFilter hFmtBits hw18 hTreeImpl hBindOk hCanonOk hIsNegOk hRep0 hFootLt hGn hLogW
      hCapT hPh1 hNewForest hNewSub hPOld hPNew hOldCap hi₀ hOldLen hNewLen hOld2 hNew2
      (by show s1.mem (root + 15) = tok.intCap; rw [hK1 _ hK15]; exact hIntCap)
      ⟨hs1r4, by rw [hs2regs 70 le_rfl (by omega) (by omega)]; exact hr70,
        by rw [hs2regs 73 (by omega) (by omega) (by omega)]; exact hr73,
        by rw [hs2regs 75 (by omega) (by omega) (by omega)]; exact hr75,
        by rw [hs2regs 80 (by omega) (by omega) (by omega)]; exact hr80,
        by rw [hs2regs 81 (by omega) (by omega) (by omega)]; exact hr81,
        by simp [s2]⟩ hz1 hRoomS
  -- the words of `K` keep their values across Sync 2b
  have hK3 : ∀ a, BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok a → s3.mem a = st.mem a :=
    fun a ⟨ha, h11, htag, hft⟩ => by
      rw [← hK1 a ⟨ha, h11, htag, hft⟩]
      refine hFr3 a (by omega) h11 htag (fun hu hf => ?_)
      rcases hFoot1 a hf with h | ⟨h, _⟩
      · exact hft hu h
      · omega
  -- the push
  have hSmall3 : SmallBatchAt s3.mem uIntBuf Gb Ub totalWords :=
    smallBatchAt_of_agree hSmall (fun x hx1 hx2 => hK3 x (hBatchK x hx1 hx2))
  have hBatchW3 : ∀ j < totalWords, s3.mem (uIntBuf + j) < 2 ^ w := fun j hj => by
    rw [hK3 _ (hBatchK _ (by omega) (by omega))]; exact hBatchW j hj
  have hTW : uIntBuf + totalWords ≤ heapX := by
    by_contra hc
    have := (hBatchK (uIntBuf + totalWords - 1) (by have := hSmall.1.1; omega)
      (by have := hSmall.1.1; omega)).1
    omega
  obtain ⟨s4, c4, oc4, r4, hc4, hoc4, hPh4, hFr4⟩ :=
    wirePushInsertedBody_runs (pos := s3.pos) (ω := ω) hPushP hIsNegOk hRep0 hFootLt hGn hPh3
      hSmall3 hEdgeOnly hBatchW3 le_rfl (by omega) hInsCap (by omega) hLW (by omega)
  let s5 : State := { s4 with regs := Function.update s3.regs 10 (Outcome.returned 0).value }
  have hs3r70 : s3.regs 70 = root := by
    rw [hs3regs 70 le_rfl, hs2regs 70 le_rfl (by omega) (by omega)]; exact hr70
  have hs3r87 : s3.regs 87 = uIntBuf := by
    rw [hs3regs 87 (by omega), hs2regs 87 (by omega) (by omega) (by omega)]; exact hr87
  have hs3r94 : s3.regs 94 = L := by
    rw [hs3regs 94 (by omega), hs2regs 94 (by omega) (by omega) (by omega)]; exact hr94
  have rCall : Runs w p ω (.call 10 pushInsProc [.reg 70, .reg 87, .reg 94]) s3 .normal s5
      (3 + c4 + 1) :=
    runs_call_iff.mpr ⟨[root, uIntBuf, L], wirePushInsertedBody pushProc, .returned 0, s4, c4,
      by simp [evalArgs, Expr.eval, hs3r70, hs3r87, hs3r94], hPushIns, r4, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
  have hs5r4 : s5.regs 4 = h3 := by simp [s5, hs3r4]
  have rRet : Runs w p ω (.ret (.reg 4)) s5 (.returned h3) s5 2 :=
    runs_ret_iff.mpr ⟨h3, by simp [Expr.eval, hs5r4], rfl, rfl, rfl⟩
  have hs5mem : s5.mem = s4.mem := rfl
  -- memory after the push
  have hag4 : ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
      s5.mem a = s3.mem a := hFr4
  -- the tree potential does not change in the push
  have hTreePhi : Rtree.phi tok.treeHeap tt3 s5.mem = Rtree.phi tok.treeHeap tt3 s3.mem := by
    have hloc := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap tr3 tt3
      s3.mem s5.mem (fun a ha => by
        obtain ⟨hlt, _⟩ := hPh3.footLoc a ha
        refine (hag4 a (fun h => ?_) (fun hu => ?_)).symm
        · have h16 := hlt (by omega)
          rw [h] at h16
          rw [hT1 11 (by omega)] at h16; omega
        · have h16 := hlt hu
          rw [h16]; decide)
    exact hloc.2.symm
  have hRoot11 : root + 11 < uIntBuf := htagLt (by rw [hT1 11 (by omega)]; decide)
  have hCapE := hPh.capE
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT13, hT14, hT15, _⟩ := (id hRep0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hRec5 : ∀ ei ∈ G0.E, s5.mem (tok.edgeRecords + ei) = s3.mem (tok.edgeRecords + ei) :=
    fun ei hei => hag4 _ (fun h => by
        have h13 := hT13 ei (hCapE ei hei)
        rw [h, hT1 11 (by omega)] at h13; omega)
      (fun _ => by rw [hT13 ei (hCapE ei hei)]; decide)
  have hKeep5 : ∀ a, BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok a →
      s5.mem a = st.mem a := fun a hK => by
    rw [← hK3 a hK]
    obtain ⟨_, h11, htag, _⟩ := hK
    exact hag4 a h11 (fun h => ⟨(htag h).2.2.2.2.1, (htag h).2.2.2.2.2.1⟩)
  refine ⟨s5, (c1 + (3 + (c3 + ((3 + c4 + 1) + 2 + 1) + 1) + 1) + 1), h3, tr3, tt3, oc4, ?_, ?_,
    by omega, ?_, ?_, hPh4, ?_, ?_, ?_, hKeep5, fun a ha h11 htag hft => hKeep5 a ⟨ha, h11, htag, hft⟩, ?_⟩
  · -- the records of the cut edges of the tree lie in the new heap
    intro ei hei hF hnot
    have e1 : heapX ≤ h1 := hH1lo
    have e3 : h1 ≤ h3 := hH3lo
    rw [hRec5 ei hei]
    by_cases hin : ei ∈ Fp ∪ (oldE ∩ G0.E)
    · obtain ⟨hlo, hhi⟩ := hRecCut3 ei hei hnot hin
      exact ⟨by omega, hhi⟩
    · rw [hRecKeep3 ei hei hnot hin]
      show heapX ≤ s1.mem (tok.edgeRecords + ei) ∧
        s1.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ h3
      have hX' : ei ∈ X := by
        by_contra hc
        exact hin (hSplitX ▸ Finset.mem_sdiff.mpr ⟨hF, by rwa [List.mem_toFinset]⟩)
      obtain ⟨hlo, hhi⟩ := hRecCut1 ei hX'
      exact ⟨hlo, by omega⟩
  · -- the run
    refine runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s5, 3 + c4 + 1, 2, rCall, rRet, rfl⟩)
  · have e1 : h1 ≤ heapX + 2 * T + T * wireTreeSyncEditSpace L := hH1hi
    have e3 : h3 ≤ h1 + 3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L := hH3hi
    omega
  · intro a ha
    have := hRoot11; have := hBaseLe; have := hH1lo; have := hH3lo
    rw [hag4 a (by omega) (fun h => absurd h (by omega))]
    exact hz3 a ha
  · intro a ha
    rcases hFoot3 a ha with h | ⟨h1a, h2a⟩
    · rcases hFoot1 a h with h' | ⟨h1b, h2b⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1b, by omega⟩
    · exact Or.inr ⟨by omega, h2a⟩
  · intro ei hei hnot
    rw [hRec5 ei hei]
    by_cases hin : ei ∈ Fp ∪ (oldE ∩ G0.E)
    · obtain ⟨hlo, hhi⟩ := hRecCut3 ei hei hnot hin
      exact Or.inr ⟨by omega, hhi⟩
    · rw [hRecKeep3 ei hei hnot hin]
      show s1.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∨
        (heapX ≤ s1.mem (tok.edgeRecords + ei) ∧
          s1.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ h3)
      by_cases hF : ei ∈ F
      · have hX' : ei ∈ X := by
          by_contra hc
          exact hin (hSplitX ▸ Finset.mem_sdiff.mpr ⟨hF, by rwa [List.mem_toFinset]⟩)
        obtain ⟨hlo, hhi⟩ := hRecCut1 ei hX'
        exact Or.inr ⟨hlo, by omega⟩
      · exact Or.inl (hRecKeep1 ei hei hF)
  · intro ei hei hF hnot
    have hin : ei ∉ Fp ∪ (oldE ∩ G0.E) := fun h => by
      rw [← hSplitX] at h; exact hF (Finset.mem_sdiff.mp h).1
    rw [hRec5 ei hei, hRecKeep3 ei hei hnot hin]
    exact hRecKeep1 ei hei hF
  · have hc4' : c4 ≤ 160 * Ub.length + 60 := hc4
    have hoc : oc4 * drainUnit ≤ oc3 * drainUnit + Ub.length * drainUnit := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hoc4
    have hc1' : c1 + (Rtree.phi tok.treeHeap tt1 s1.mem + oc1 * drainUnit) ≤
        T * (wireTreeSyncEditCost L drainUnit + 2) + 40 * T + 64 * n + 175 +
          (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit) := hc1
    have hc3' : c3 + (Rtree.phi tok.treeHeap tt3 s3.mem + oc3 * drainUnit) ≤
        ((oldE \ newE).card + (newE \ oldE).card) * (wireTreeSyncEditCost L drainUnit + 2) +
          155 * S + 210 * (dd + 1 - i₀) + 350 +
          (Rtree.phi tok.treeHeap tt1 s1.mem + oc1 * drainUnit) := hc3
    simp only [s5, hTreePhi]
    omega

end MinCostFlow.MinRatio
