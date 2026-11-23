module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPhaseKFBL
public import MinCostFlow.MinRatio.UpdateOffTreePush
import WordRAM.Tactic

/-!
# The tree state across a push onto the ready list (`WireChainCoreBranchBPushKFBL`)

The last step of Branch B pushes each fresh name that ended off the tree onto the ready list
(`offTreePushBody`). Until then the fresh names are the deferred set of the tree state
(`TreeSyncPhaseAt`): its ready clause skips them. Each push changes only the count word
`root + 11`, one word of the ready list and one bit of `inOffReady`.

`TreeSyncPhaseAt.of_push` moves the tree state across such a change and takes the pushed name out
of the deferred set. `TreeSyncPhaseAt.erase_of_mem` takes a tree edge out of the deferred set,
since the ready clause speaks only of edges off the tree.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- A tree edge leaves the deferred set: the ready clause speaks only of edges off the tree. -/
theorem TreeSyncPhaseAt.erase_of_mem
    {L root uIntBuf heapX rg offCnt ei : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem : ℕ → ℕ}
    {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt mem)
    (hF : ei ∈ F) :
    TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R (deferSet.erase ei) curTree
      curTreeTok offCnt mem :=
  { hPh with
    offReady := fun e he hnot hnd hdet => by
      have hne : e ≠ ei := fun h => hnot (h ▸ hF)
      exact hPh.offReady e he hnot (fun h => hnd (Finset.mem_erase.mpr ⟨hne, h⟩)) hdet }

set_option maxHeartbeats 1200000 in
/-- The tree state across a push of the edge `ei`. The memory changes only at the count word
`root + 11` and at words of the ready list and of `inOffReady` (tags `14` and `15`). The ready
list is consistent afterwards, its count is `cnt'`, the bit of `ei` is set when `ei` is off the
tree with a nonnegative detector, and no set bit is cleared. Then the tree state holds with
`cnt'` and without `ei` in the deferred set. -/
theorem TreeSyncPhaseAt.of_push
    {L P m V psi k epsExp drainUnit root uIntBuf heapX rg offCnt ei cnt' : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem mem' : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 : MGraph} {F : Finset ℕ} {canonVal : ℕ → PathEdgeValue} {deferSet : Finset ℕ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree
      curTreeTok offCnt mem)
    (hag : ∀ a, a ≠ root + 11 → (a < uIntBuf → tok.tag a ≠ 14 ∧ tok.tag a ≠ 15) →
      mem' a = mem a)
    (hCnt : mem' (root + 11) = cnt')
    (hInv : OffReadyInv mem' cnt' tok.offReadyList tok.inOffReady tok.intCap)
    (hReady : ei ∉ F → 0 ≤ (canonVal ei).detector → mem' (tok.inOffReady + ei) = 1)
    (hKeep : ∀ e < tok.intCap, mem (tok.inOffReady + e) = 1 → mem' (tok.inOffReady + e) = 1) :
    TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R (deferSet.erase ei) curTree
      curTreeTok cnt' mem' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, _, _,
    _, _, _, _, _⟩ := hTags0
  obtain ⟨hBaseLe, ⟨hD6, hD7, hD8, hD9, hD10, hD12, hD13, hD14⟩, ⟨hH0, hH5⟩, hRG, hSub, hCapE,
    hCanonP, hTreeN, ⟨curTrees, curFree, curDepth, hL1, hL2, hL3, hL4⟩, hTreeRep, hSlotThr,
    hOffSlot, hOffRec, hOffReady, hOffDisj, _, _, hFootLoc, hGraphLoc, hRecLoc⟩ := hPh
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hOfT {a v : ℕ} (ht : a < uIntBuf → tok.tag a = v) (h1 : v ≠ 1) (h14 : v ≠ 14)
      (h15 : v ≠ 15) : mem' a = mem a := by
    refine hag a (fun hEq => ?_) (fun hlt => by rw [ht hlt]; exact ⟨h14, h15⟩)
    have h11 := ht (by omega)
    rw [hEq, hT1 11 (by omega)] at h11
    exact h1 h11.symm
  have hOf {a v : ℕ} (ht : tok.tag a = v) (h1 : v ≠ 1) (h14 : v ≠ 14) (h15 : v ≠ 15) :
      mem' a = mem a :=
    hOfT (fun _ => ht) h1 h14 h15
  have hRoot {j : ℕ} (hj : j < 16) (hj11 : j ≠ 11) : mem' (root + j) = mem (root + j) :=
    hag _ (by omega) (fun _ => by rw [hT1 j hj]; decide)
  have hSl (e : ℕ) (he : e ∈ G0.E) : mem' (tok.slots + e) = mem (tok.slots + e) :=
    hOf (hT9 e (hCapE e he)) (by decide) (by decide) (by decide)
  have hRec (e : ℕ) (he : e ∈ G0.E) :
      mem' (tok.edgeRecords + e) = mem (tok.edgeRecords + e) :=
    hOf (hT13 e (hCapE e he)) (by decide) (by decide) (by decide)
  have hEdgeSl {sl : ℕ} (his : isEdgeSlot curTree.n sl) : sl < 2 * tok.tree.n := by
    unfold isEdgeSlot at his; omega
  exact
    { baseLe := hBaseLe
      dir := ⟨(hRoot (by omega) (by omega)).trans hD6, (hRoot (by omega) (by omega)).trans hD7,
        (hRoot (by omega) (by omega)).trans hD8, (hRoot (by omega) (by omega)).trans hD9,
        (hRoot (by omega) (by omega)).trans hD10, (hRoot (by omega) (by omega)).trans hD12,
        (hRoot (by omega) (by omega)).trans hD13, (hRoot (by omega) (by omega)).trans hD14⟩
      hdr := ⟨(hOf (by simpa using hT2 0 (by omega)) (by decide) (by decide) (by decide)).trans
          hH0,
        (hOf (hT2 5 (by omega)) (by decide) (by decide) (by decide)).trans hH5⟩
      graph := hRG.of_agree fun a ha1 ha2 =>
        hOfT (hGraphLoc a ha1 ha2).1 (by decide) (by decide) (by decide)
      sub := hSub
      capE := hCapE
      canonProp := hCanonP
      treeN := hTreeN
      lct := ⟨curTrees, curFree, curDepth, hL1, hL2,
        namedSlots_congr_slot hL3 (fun e he => hSl e (hSub he))
          (fun sl _ his => hOf (hT10 sl (hEdgeSl his)) (by decide) (by decide) (by decide)),
        liveAccounts_congr_slot hL4 (fun e he => hSl e (hSub he))⟩
      treeRep := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap curTree
        curTreeTok mem mem' (fun a ha =>
          (hOfT (hFootLoc a ha).1 (by decide) (by decide) (by decide)).symm)).1 hTreeRep
      slotThr := fun e he => by
        have hslot := (hL3.forward e he).2.1
        rw [hSl e (hSub he)]
        rw [hOf (hT11 _ (hEdgeSl hslot)) (by decide) (by decide) (by decide),
          hOf (hT12 e (hCapE e (hSub he))) (by decide) (by decide) (by decide)]
        exact hSlotThr e he
      offSlot := fun e he hnot => (hSl e he).trans (hOffSlot e he hnot)
      offRec := fun e he hnot => by
        rw [hRec e he]
        exact (hOffRec e he hnot).congr (fun a ha1 ha2 => by
          have := (hRecLoc e he hnot (a - mem (tok.edgeRecords + e)) (by omega)).1
          rw [show mem (tok.edgeRecords + e) + (a - mem (tok.edgeRecords + e)) = a by
            omega] at this
          exact hOfT this (by decide) (by decide) (by decide))
      offReady := fun e he hnot hnd hdet => by
        by_cases hne : e = ei
        · subst hne
          exact hReady hnot hdet
        · exact hKeep e (hCapE e he)
            (hOffReady e he hnot (fun h => hnd (Finset.mem_erase.mpr ⟨hne, h⟩)) hdet)
      offDisj := fun e₁ he₁ e₂ he₂ hne h₁ h₂ => by
        rw [hRec e₁ he₁, hRec e₂ he₂]; exact hOffDisj e₁ he₁ e₂ he₂ hne h₁ h₂
      offCntAt := hCnt
      offInv := hInv
      footLoc := hFootLoc
      graphLoc := hGraphLoc
      recLoc := fun e he hnot j hj => by rw [hRec e he]; exact hRecLoc e he hnot j hj }

end MinCostFlow.MinRatio
