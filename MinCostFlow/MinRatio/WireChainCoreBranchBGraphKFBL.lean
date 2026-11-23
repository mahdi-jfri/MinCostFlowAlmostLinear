module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPhaseKFBL
import WordRAM.Tactic

/-!
# The tree state of Branch B after the root graph changes (`WireChainCoreBranchBGraphKFBL`)

The first sync of Branch B runs on the old graph `G0` of level `0`. Then the core refreshes the
accounts, and the plain step of level `0` in the loop applies the batch to the root graph, which
becomes the new graph `G0'`. The later syncs of Branch B need the tree state on `G0'`.

`TreeSyncPhaseAt.change_graph` gives it. The forest `F` stays: its edges survive the batch and
keep their ends. The edges of `G0'` off `F` are the old ones, whose records and values stay, and
the new names `N`. The refresh wrote a record for each new name above the old heap pointer, and
the core set its slot to `0`. A new name may have a value that the off-ready list must see, so the
new names are the deferred set: the core pushes them at the end of Branch B.

The steps between the first sync and this point write the root graph, the slots, thresholds and
records of names that are not edges of `G0` (the new names, and the fresh names that a batch
inserts and deletes again), and words that the tree state does not read. The hypothesis `hag` says
that every other word of the kinds the tree state reads keeps its value. Above `uIntBuf` the tree
state reads only the words of the tree and of the records, so `hag` asks it only for the heap words
in a set `keep` that holds those (the select slots of the core, which the loop writes, lie outside
it).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1600000 in
/-- The tree state moves from the old graph `G0` to the new graph `G0'` of level `0`, with the
new names `N` as the deferred set. -/
theorem TreeSyncPhaseAt.change_graph
    {L P m V psi k epsExp drainUnit root uIntBuf heapX heapX' rg offCnt : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem mem' : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {G0 G0' : MGraph} {F N : Finset ℕ} {canonVal canonVal' : ℕ → PathEdgeValue}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGn : G0.n = model.extG.n)
    (hPh : TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R ∅ curTree
      curTreeTok offCnt mem)
    (hHeapLe : heapX ≤ heapX')
    (hN : G0'.n = G0.n) (hG' : DynGraphAt mem' rg G0'.n tok.rootECap G0')
    (hNewE : ∀ ei ∈ G0'.E, ei ∈ G0.E ∨ ei ∈ N)
    (hFSub : F ⊆ G0'.E)
    (hEnds : ∀ e ∈ F, G0'.tail e = G0.tail e ∧ G0'.head e = G0.head e)
    (hCanonOld : ∀ ei ∈ G0.E, ei ∈ G0'.E → canonVal' ei = canonVal ei)
    (hCanonNew : ∀ ei ∈ N, (canonVal' ei).forward = true ∧ |(canonVal' ei).gradient| ≤ B ∧
      |(canonVal' ei).length| ≤ B ∧ |(canonVal' ei).flow| ≤ B ∧ |(canonVal' ei).detector| ≤ B)
    (hCapN : ∀ ei ∈ N, ei < tok.intCap)
    (hNewSlot : ∀ ei ∈ N, mem' (tok.slots + ei) = 0)
    (hNewRec : ∀ ei ∈ N,
      PathEdgeAt mem' (mem' (tok.edgeRecords + ei)) 4 L (some (canonVal' ei)))
    (hNewRecLoc : ∀ ei ∈ N, heapX ≤ mem' (tok.edgeRecords + ei) ∧
      mem' (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapX')
    (hNewDisj : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ →
      mem' (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ mem' (tok.edgeRecords + e₂) ∨
      mem' (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ mem' (tok.edgeRecords + e₁))
    (keep : ℕ → Prop)
    (hKeepFoot : ∀ a, uIntBuf ≤ a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a →
      keep a)
    (hKeepRec : ∀ ei ∈ G0.E, ei ∉ F → ∀ j < 2 + 4 * L, uIntBuf ≤ mem (tok.edgeRecords + ei) + j →
      keep (mem (tok.edgeRecords + ei) + j))
    (hag : ∀ a < heapX,
      (a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ (9 ≤ tok.tag a ∧ tok.tag a ≤ 16) ∨
        tok.tag a = 18) →
      (uIntBuf ≤ a → keep a) →
      (∀ ei < tok.intCap, ei ∉ G0.E → a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧
        a ≠ tok.edgeRecords + ei) →
      mem' a = mem a) :
    TreeSyncPhaseAt L tok root uIntBuf heapX' rg G0' F canonVal' B R N curTree curTreeTok
      offCnt mem' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, hT14, hT15,
    _, _, _, _, _⟩ := hTags0
  obtain ⟨hBaseLe, ⟨hD6, hD7, hD8, hD9, hD10, hD12, hD13, hD14⟩, ⟨hH0, hH5⟩, hRG, hSub, hCapE,
    hCanonP, hTreeN, ⟨curTrees, curFree, curDepth, hL1, hL2, hL3, hL4⟩, hTreeRep, hSlotThr,
    hOffSlot, hOffRec, hOffReady, hOffDisj, hOffCnt, hOffInv, hFootLoc, hGraphLoc,
    hRecLoc⟩ := hPh
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hNotNW {a : ℕ}
      (hcase : a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 12 ∧ tok.tag a ≠ 13) :
      ∀ ei < tok.intCap, ei ∉ G0.E → a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧
        a ≠ tok.edgeRecords + ei := by
    intro ei hc _
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h9 := hT9 ei hc
      rw [← h] at h9
      exact (hcase (htagLt (by rw [h9]; decide))).1 h9
    · have h12 := hT12 ei hc
      rw [← h] at h12
      exact (hcase (htagLt (by rw [h12]; decide))).2.1 h12
    · have h13 := hT13 ei hc
      rw [← h] at h13
      exact (hcase (htagLt (by rw [h13]; decide))).2.2 h13
  have hOf {a : ℕ} (ha : a < heapX)
      (hcase : a < uIntBuf → tok.tag a = 1 ∨ tok.tag a = 2 ∨ tok.tag a = 10 ∨
        tok.tag a = 11 ∨ tok.tag a = 14 ∨ tok.tag a = 15 ∨ tok.tag a = 16 ∨ tok.tag a = 18)
      (hk : uIntBuf ≤ a → keep a) :
      mem' a = mem a :=
    hag a ha (fun h => by rcases hcase h with h | h | h | h | h | h | h | h <;> rw [h] <;> omega)
      hk (hNotNW fun h => by
        rcases hcase h with h | h | h | h | h | h | h | h <;> rw [h] <;> omega)
  have hOfT {a v : ℕ} (ht : tok.tag a = v)
      (hv : v = 1 ∨ v = 2 ∨ v = 10 ∨ v = 11 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 18) :
      mem' a = mem a :=
    hOf (lt_of_lt_of_le (htagLt (by rw [ht]; omega)) hBaseLe) (fun _ => by rw [ht]; exact hv)
      (fun h => absurd (htagLt (by rw [ht]; omega)) (by omega))
  have hOldW {ei a v : ℕ} (hei : ei ∈ G0.E) (ht : tok.tag a = v) (hv : 9 ≤ v ∧ v ≤ 13)
      (hne : ∀ e' < tok.intCap, a = tok.slots + e' ∨ a = tok.edgeThresholds + e' ∨
        a = tok.edgeRecords + e' → e' = ei) :
      mem' a = mem a := by
    refine hag a (lt_of_lt_of_le (htagLt (by rw [ht]; omega)) hBaseLe)
      (fun _ => Or.inr (Or.inr (Or.inl (by rw [ht]; omega))))
      (fun h => absurd (htagLt (by rw [ht]; omega)) (by omega)) (fun e' he' hnd => ?_)
    refine ⟨fun h => hnd ?_, fun h => hnd ?_, fun h => hnd ?_⟩
    · rw [hne e' he' (Or.inl h)]; exact hei
    · rw [hne e' he' (Or.inr (Or.inl h))]; exact hei
    · rw [hne e' he' (Or.inr (Or.inr h))]; exact hei
  have hSl (ei : ℕ) (hei : ei ∈ G0.E) : mem' (tok.slots + ei) = mem (tok.slots + ei) := by
    have ht := hT9 ei (hCapE ei hei)
    refine hOldW hei ht (by omega) (fun e' hc h => ?_)
    rcases h with h | h | h
    · omega
    · have h12 := hT12 e' hc; rw [← h, ht] at h12; omega
    · have h13 := hT13 e' hc; rw [← h, ht] at h13; omega
  have hThr (ei : ℕ) (hei : ei ∈ G0.E) :
      mem' (tok.edgeThresholds + ei) = mem (tok.edgeThresholds + ei) := by
    have ht := hT12 ei (hCapE ei hei)
    refine hOldW hei ht (by omega) (fun e' hc h => ?_)
    rcases h with h | h | h
    · have h9 := hT9 e' hc; rw [← h, ht] at h9; omega
    · omega
    · have h13 := hT13 e' hc; rw [← h, ht] at h13; omega
  have hRec (ei : ℕ) (hei : ei ∈ G0.E) :
      mem' (tok.edgeRecords + ei) = mem (tok.edgeRecords + ei) := by
    have ht := hT13 ei (hCapE ei hei)
    refine hOldW hei ht (by omega) (fun e' hc h => ?_)
    rcases h with h | h | h
    · have h9 := hT9 e' hc; rw [← h, ht] at h9; omega
    · have h12 := hT12 e' hc; rw [← h, ht] at h12; omega
    · omega
  have hEdgeSl {sl : ℕ} (his : isEdgeSlot curTree.n sl) : sl < 2 * tok.tree.n := by
    unfold isEdgeSlot at his; omega
  have hFootOf (a : ℕ)
      (ha : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
        curTreeTok a) : mem' a = mem a :=
    hOf (hFootLoc a ha).2 (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ((hFootLoc a ha).1 h)))))))) (fun h => hKeepFoot a h ha)
  have hRGEnd : rg + dynGraphSize G0.n tok.rootECap ≤ heapX := by
    have hpos : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have := (hGraphLoc (rg + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)).2.2
    omega
  have hCntLe := hOffInv.1
  exact
    { baseLe := le_trans hBaseLe hHeapLe
      dir := ⟨(hOfT (hT1 6 (by omega)) (by omega)).trans hD6,
        (hOfT (hT1 7 (by omega)) (by omega)).trans hD7,
        (hOfT (hT1 8 (by omega)) (by omega)).trans hD8,
        (hOfT (hT1 9 (by omega)) (by omega)).trans hD9,
        (hOfT (hT1 10 (by omega)) (by omega)).trans hD10,
        (hOfT (hT1 12 (by omega)) (by omega)).trans hD12,
        (hOfT (hT1 13 (by omega)) (by omega)).trans hD13,
        (hOfT (hT1 14 (by omega)) (by omega)).trans hD14⟩
      hdr := ⟨(hOfT (by simpa using hT2 0 (by omega)) (by omega)).trans hH0,
        (hOfT (hT2 5 (by omega)) (by omega)).trans hH5⟩
      graph := hG'
      sub := hFSub
      capE := fun ei hei => (hNewE ei hei).elim (hCapE ei) (hCapN ei)
      canonProp := fun ei hei => (hNewE ei hei).elim
        (fun h => by rw [hCanonOld ei h hei]; exact hCanonP ei h) (hCanonNew ei)
      treeN := hTreeN.trans hN.symm
      lct := ⟨curTrees, curFree, curDepth, hL1, hL2,
        (namedSlots_congr_slot hL3 (fun ei hei => hSl ei (hSub hei))
          (fun sl _ his => hOfT (hT10 sl (hEdgeSl his)) (by omega))).congrGraph rfl
          (fun f hf => hEnds f hf),
        fun e he => by
          have h := hL4 e he
          obtain ⟨ht, hh⟩ := hEnds e he
          show TreeEditDirectedAccount curTree curTrees (mem' (tok.slots + e))
            (vid (G0'.tail e)) (vid (G0'.head e)) (canonVal' e)
          rw [ht, hh, hSl e (hSub he), hCanonOld e (hSub he) (hFSub he)]
          exact h⟩
      treeRep := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap curTree
        curTreeTok mem mem' (fun a ha => (hFootOf a ha).symm)).1 hTreeRep
      slotThr := fun ei hei => by
        have hslot := (hL3.forward ei hei).2.1
        rw [hSl ei (hSub hei)]
        rw [hOfT (hT11 _ (hEdgeSl hslot)) (by omega), hThr ei (hSub hei)]
        exact hSlotThr ei hei
      offSlot := fun ei hei hnot => (hNewE ei hei).elim
        (fun h => (hSl ei h).trans (hOffSlot ei h hnot)) (fun h => hNewSlot ei h)
      offRec := fun ei hei hnot => (hNewE ei hei).elim
        (fun h => by
          rw [hRec ei h, hCanonOld ei h hei]
          exact (hOffRec ei h hnot).congr (fun a ha1 ha2 => by
            have hl := hRecLoc ei h hnot (a - mem (tok.edgeRecords + ei)) (by omega)
            rw [show mem (tok.edgeRecords + ei) + (a - mem (tok.edgeRecords + ei)) = a by
              omega] at hl
            exact hOf hl.2.2.2 (fun hlt => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (hl.1 hlt)))))))) (fun hge => by
                have hk := hKeepRec ei h hnot (a - mem (tok.edgeRecords + ei)) (by omega)
                  (by omega)
                rwa [show mem (tok.edgeRecords + ei) + (a - mem (tok.edgeRecords + ei)) = a by
                  omega] at hk)))
        (fun h => hNewRec ei h)
      offReady := fun ei hei hnot hnd hdet => by
        have h : ei ∈ G0.E := (hNewE ei hei).resolve_right hnd
        rw [hCanonOld ei h hei] at hdet
        exact (hOfT (hT15 ei (hCapE ei h)) (by omega)).trans
          (hOffReady ei h hnot (by simp) hdet)
      offDisj := fun e₁ he₁ e₂ he₂ hne h₁ h₂ => by
        have hEnd (e : ℕ) (he : e ∈ G0.E) (hn : e ∉ F) :
            mem (tok.edgeRecords + e) + (2 + 4 * L) ≤ heapX := by
          have := (hRecLoc e he hn (1 + 4 * L) (by omega)).2.2.2
          omega
        rcases hNewE e₁ he₁ with h1 | h1 <;> rcases hNewE e₂ he₂ with h2 | h2
        · rw [hRec e₁ h1, hRec e₂ h2]; exact hOffDisj e₁ h1 e₂ h2 hne h₁ h₂
        · rw [hRec e₁ h1]
          have := hEnd e₁ h1 h₁
          have := (hNewRecLoc e₂ h2).1
          exact Or.inl (by omega)
        · rw [hRec e₂ h2]
          have := hEnd e₂ h2 h₂
          have := (hNewRecLoc e₁ h1).1
          exact Or.inr (by omega)
        · exact hNewDisj e₁ h1 e₂ h2 hne
      offCntAt := (hOfT (hT1 11 (by omega)) (by omega)).trans hOffCnt
      offInv := ⟨hCntLe,
        fun j hj => by
          rw [hOfT (hT14 j (by omega)) (by omega)]
          exact ⟨(hOffInv.2.1 j hj).1,
            (hOfT (hT15 _ (hOffInv.2.1 j hj).1) (by omega)).trans (hOffInv.2.1 j hj).2⟩,
        fun j1 hj1 j2 hj2 hne => by
          rw [hOfT (hT14 j1 (by omega)) (by omega), hOfT (hT14 j2 (by omega)) (by omega)]
          exact hOffInv.2.2.1 j1 hj1 j2 hj2 hne,
        fun e he => by rw [hOfT (hT15 e he) (by omega)]; exact hOffInv.2.2.2.1 e he,
        fun e he h1 => by
          rw [hOfT (hT15 e he) (by omega)] at h1
          obtain ⟨j, hj, hje⟩ := hOffInv.2.2.2.2 e he h1
          exact ⟨j, hj, (hOfT (hT14 j (by omega)) (by omega)).trans hje⟩⟩
      footLoc := fun a ha => ⟨(hFootLoc a ha).1, lt_of_lt_of_le (hFootLoc a ha).2 hHeapLe⟩
      graphLoc := fun a ha1 ha2 => by
        rw [hN] at ha2
        obtain ⟨h1, h2, h3⟩ := hGraphLoc a ha1 ha2
        exact ⟨h1, h2, by omega⟩
      recLoc := fun ei hei hnot j hj => (hNewE ei hei).elim
        (fun h => by
          rw [hRec ei h, hN]
          obtain ⟨h1, h2, h3, h4⟩ := hRecLoc ei h hnot j hj
          exact ⟨h1, h2, h3, by omega⟩)
        (fun h => by
          obtain ⟨hlo, hhi⟩ := hNewRecLoc ei h
          refine ⟨fun hlt => by omega, fun hf => ?_, Or.inr (by rw [hN]; omega), by omega⟩
          have := (hFootLoc _ hf).2
          omega) }

end MinCostFlow.MinRatio
