module

public import MinCostFlow.MinRatio.WireChainCoreSyncPhaseKFBL
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.WireTreeSyncBase
import WordRAM.Tactic

/-!
# The tree state of Branch B: its start and its frame (`WireChainCoreBranchBPhaseKFBL`)

The syncs of Branch B read and keep `TreeSyncPhaseAt` (`WireChainCoreSyncPhaseKFBL.lean`). This
file gives the two facts that link it to the rest of the core.
- `treeSyncPhaseAt_of_rep`: at the start of Branch B, the solver state gives `TreeSyncPhaseAt`
  for the tree of the chain, as long as the memory still agrees with the memory of the solver on
  the words of the tree, the edge tables, the root graph and the records. Only the slots of the
  edges of the root graph must agree, so the slots of fresh names may already be zeroed.
- `TreeSyncPhaseAt.of_agree`: the steps between two syncs write only to fresh heap, from the heap
  pointer on, and `TreeSyncPhaseAt` reads only words below it, so it stays.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

set_option maxHeartbeats 1200000 in
/-- At the start of Branch B the tree state holds for the tree of the chain of `model`, with no
deferred pushes. The memory `mem` needs to agree with the memory `mem0` of the solver only on the
words of the kinds that the tree state reads, and on the slots of the edges of the root graph
(the slots of other names may differ). The second part gives the values `canonVal` of the
live edges, which the refresh of the accounts reads. -/
theorem treeSyncPhaseAt_of_rep
    {L P m V psi k epsExp drainUnit root uIntBuf heapX : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hOldSub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hBase : uIntBuf ≤ heapX)
    (hAg : ∀ a < uIntBuf, (tok.tag a = 1 ∨ tok.tag a = 2 ∨ tok.tag a = 10 ∨
      tok.tag a = 11 ∨ tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15 ∨
      tok.tag a = 16 ∨ tok.tag a = 18 ∨ tok.tag a = 20) → mem a = mem0 a)
    (hAgSlot : ∀ ei ∈ (model.chain.G 0).E, mem (tok.slots + ei) = mem0 (tok.slots + ei)) :
    ∃ canonVal : ℕ → PathEdgeValue,
      TreeSyncPhaseAt L tok root uIntBuf heapX tok.rootGraph (model.chain.G 0)
        model.chain.toTreeChain.chainTree.E canonVal B R ∅ tok.tree tok.treeTok
        tok.offReadyCount mem ∧
      (∀ e ∈ model.extG.E,
        let ei := model.extToInt e
        let v := canonVal ei
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧
        |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        ∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (model.extℓ e)) := by
  classical
  have hRep0_keep := hRep0
  obtain ⟨hRootDir0, hDetHdr0, _, _, hFreshInv, _, _, ⟨hG0Cap, _, _, _⟩, _,
    hOffReady0, hTreeN0, hLct0, hTreeRep0, hAccounts0, _, _, _, _, hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, _, hT10, hT11, hT12, hT13, hT14, hT15,
    hT16, hT1718, _, hT20, _⟩ := hTags0
  obtain ⟨_, hRootG0, _, hNamed0, _⟩ := hWire0
  set G0 := model.chain.G 0
  set oldF := model.chain.toTreeChain.chainTree
  have hG0nEq : G0.n = model.extG.n := by unfold MGraph.n; rw [← hFreshInv.hV]
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hOf {a v : ℕ} (ht : tok.tag a = v) (hv : v = 1 ∨ v = 2 ∨ v = 10 ∨ v = 11 ∨
      v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 18 ∨ v = 20) : mem a = mem0 a :=
    hAg a (htagLt (by
      rw [ht]; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> decide)) (ht ▸ hv)
  obtain ⟨canonVal, hLive0, hCanonExt⟩ :=
    liveAccounts_of_solverStateRep hRep0_keep hNum0 hOffInv0 hOffBd0 hOldSub
  have hRoot (j : ℕ) (hj : j < 16) : mem (root + j) = mem0 (root + j) :=
    hOf (hT1 j hj) (by decide)
  have hHdr (j : ℕ) (hj : j < 18) : mem (tok.handle + j) = mem0 (tok.handle + j) :=
    hOf (hT2 j hj) (by decide)
  have hGr0 : ({ G0 with E := oldF.E } : MGraph) = oldF := rfl
  refine ⟨canonVal, ?_, fun e he => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := hCanonExt e he
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩
  refine
    { baseLe := hBase
      dir := ⟨(hRoot 6 (by omega)).trans (by simpa using hRootDir0 6 (by simp)),
        (hRoot 7 (by omega)).trans (by simpa using hRootDir0 7 (by simp)),
        (hRoot 8 (by omega)).trans (by simpa using hRootDir0 8 (by simp)),
        (hRoot 9 (by omega)).trans (by simpa using hRootDir0 9 (by simp)),
        (hRoot 10 (by omega)).trans (by simpa using hRootDir0 10 (by simp)),
        (hRoot 12 (by omega)).trans (by simpa using hRootDir0 12 (by simp)),
        (hRoot 13 (by omega)).trans (by simpa using hRootDir0 13 (by simp)),
        (hRoot 14 (by omega)).trans (by simpa using hRootDir0 14 (by simp))⟩
      hdr := ⟨(hHdr 0 (by omega)).trans (by simpa using hDetHdr0 0 (by simp)),
        (hHdr 5 (by omega)).trans (by simpa using hDetHdr0 5 (by simp))⟩
      graph := by
        rw [hG0nEq]
        exact hRootG0.of_agree fun a ha1 ha2 => hOf (hT20 a ha1 ha2) (by decide)
      sub := hOldSub
      capE := hG0Cap
      canonProp := fun ei heiG => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        obtain ⟨hf, hg, hl, hfl, hd, _⟩ := hCanonExt (model.intToExt ei) heExt
        rw [heMap] at hf hg hl hfl hd; exact ⟨hf, hg, hl, hfl, hd⟩
      treeN := hTreeN0.trans hG0nEq.symm
      lct := ⟨tok.trees, tok.free, tok.depth, hLct0, hNum0,
        hGr0.symm ▸ namedSlots_congr_slot hNamed0
          (fun ei hei => hAgSlot ei (hOldSub hei))
          (fun sl _ his => hOf (hT10 sl (by unfold isEdgeSlot at his; omega)) (by decide)),
        hGr0.symm ▸ liveAccounts_congr_slot hLive0
          (fun ei hei => hAgSlot ei (hOldSub hei))⟩
      treeRep := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap tok.tree
        tok.treeTok mem0 mem (fun a ha => (hOf (hT16 a ha) (by decide)).symm)).1 hTreeRep0
      slotThr := fun ei hei => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei (hOldSub hei)
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hei' : ei ∈ model.chain.toTreeChain.chainTree.E := hei
        rw [heMap] at hAcc; simp only [hei', ↓reduceIte] at hAcc
        have hS := hAgSlot ei (hOldSub hei)
        have hT := hOf (hT12 ei (hG0Cap ei (hOldSub hei))) (by decide)
        rw [hS, hT]
        exact (hOf (hT11 _ (by unfold isEdgeSlot at hAcc; omega)) (by decide)).trans
          hAcc.2.2.2.2.2.1
      offSlot := fun ei heiG hnot => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hnot' : ei ∉ model.chain.toTreeChain.chainTree.E := hnot
        rw [heMap] at hAcc; simp only [hnot', ↓reduceIte] at hAcc
        exact (hAgSlot ei heiG).trans hAcc.2.2.1
      offRec := fun ei heiG hnot => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
        rw [heMap] at hrec
        rw [hOf (hT13 ei (hG0Cap ei heiG)) (by decide)]
        exact hrec.congr (fun a ha1 ha2 => by
          have ht := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot)
            (a - mem0 (tok.edgeRecords + ei)) (by omega)
          rw [heMap, show mem0 (tok.edgeRecords + ei) + (a - mem0 (tok.edgeRecords + ei)) = a by
            omega] at ht
          exact hOf ht (by decide))
      offReady := fun ei heiG hnot _ hdet => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hnot' : ei ∉ model.chain.toTreeChain.chainTree.E := hnot
        rw [heMap] at hAcc; simp only [hnot', ↓reduceIte] at hAcc
        obtain ⟨v, acc, hpa, _, _, _, hpush⟩ := hAcc.2.2.2
        have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
        rw [heMap] at hrec
        have hveq : v.detector = (canonVal ei).detector := by
          have h1 := hpa.2.2.2.2.2.2; have h2 := hrec.2.2.2.2.2.2; omega
        exact (hOf (hT15 ei (hG0Cap ei heiG)) (by decide)).trans (hpush (hveq.symm ▸ hdet))
      offDisj := fun e1 h1G e2 h2G hne hnot1 hnot2 => by
        obtain ⟨hm1, he1⟩ := hFreshInv.hRight e1 h1G
        obtain ⟨hm2, he2⟩ := hFreshInv.hRight e2 h2G
        rw [hOf (hT13 e1 (hG0Cap e1 h1G)) (by decide), hOf (hT13 e2 (hG0Cap e2 h2G)) (by decide)]
        have hd := hOffInv0.2 _ he1 _ he2 (fun h => hne (hm1.symm.trans (h ▸ hm2)))
          (hm1.symm ▸ hnot1) (hm2.symm ▸ hnot2)
        rwa [hm1, hm2] at hd
      offCntAt := (hRoot 11 (by omega)).trans (by simpa using hRootDir0 11 (by simp))
      offInv := ⟨hOffReady0.1,
        fun j hj => by
          have hCntLe := hOffReady0.1
          rw [hOf (hT14 j (by omega)) (by decide)]
          exact ⟨(hOffReady0.2.1 j hj).1,
            (hOf (hT15 _ (hOffReady0.2.1 j hj).1) (by decide)).trans (hOffReady0.2.1 j hj).2⟩,
        fun j1 hj1 j2 hj2 hne => by
          have hCntLe := hOffReady0.1
          rw [hOf (hT14 j1 (by omega)) (by decide), hOf (hT14 j2 (by omega)) (by decide)]
          exact hOffReady0.2.2.1 j1 hj1 j2 hj2 hne,
        fun e he => by rw [hOf (hT15 e he) (by decide)]; exact hOffReady0.2.2.2.1 e he,
        fun e he h1 => by
          have hCntLe := hOffReady0.1
          rw [hOf (hT15 e he) (by decide)] at h1
          obtain ⟨j, hj, hje⟩ := hOffReady0.2.2.2.2 e he h1
          exact ⟨j, hj, (hOf (hT14 j (by omega)) (by decide)).trans hje⟩⟩
      footLoc := fun a ha =>
        ⟨fun _ => hT16 a ha, lt_of_lt_of_le (htagLt (by rw [hT16 a ha]; decide)) hBase⟩
      graphLoc := fun a ha1 ha2 => by
        have ha2' : a < tok.rootGraph + dynGraphSize model.extG.n tok.rootECap := by
          rw [← hG0nEq]; exact ha2
        have h20 := hT20 a ha1 ha2'
        exact ⟨fun _ => h20, fun hf => by have := hT16 a hf; omega,
          lt_of_lt_of_le (htagLt (by rw [h20]; decide)) hBase⟩
      recLoc := fun ei heiG hnot j hj => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have ht18 := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) j hj
        rw [heMap] at ht18
        rw [hOf (hT13 ei (hG0Cap ei heiG)) (by decide)]
        refine ⟨fun _ => ht18, fun hf => by have := hT16 _ hf; omega, ?_,
          lt_of_lt_of_le (htagLt (by rw [ht18]; decide)) hBase⟩
        by_contra hc
        push Not at hc
        have := hT20 _ hc.1 (by rw [← hG0nEq]; exact hc.2)
        omega }

set_option maxHeartbeats 1200000 in
/-- `TreeSyncPhaseAt` reads only words below the heap pointer, so it stays when no word below the
heap pointer changes. -/
theorem TreeSyncPhaseAt.of_agree
    {L P m V psi k epsExp drainUnit root uIntBuf heapX rg offCnt : ℕ}
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
    (hag : ∀ a < heapX, mem' a = mem a) :
    TreeSyncPhaseAt L tok root uIntBuf heapX rg G0 F canonVal B R deferSet curTree curTreeTok
      offCnt mem' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, hT14, hT15,
    _, _, _, _, _⟩ := hTags0
  obtain ⟨hBaseLe, ⟨hD6, hD7, hD8, hD9, hD10, hD12, hD13, hD14⟩, ⟨hH0, hH5⟩, hRG, hSub, hCapE,
    hCanonP, hTreeN, ⟨curTrees, curFree, curDepth, hL1, hL2, hL3, hL4⟩, hTreeRep, hSlotThr,
    hOffSlot, hOffRec, hOffReady, hOffDisj, hOffCnt, hOffInv, hFootLoc, hGraphLoc,
    hRecLoc⟩ := hPh
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hOf {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : mem' a = mem a :=
    hag a (lt_of_lt_of_le (htagLt (by rw [ht]; exact hv)) hBaseLe)
  have hSl (ei : ℕ) (hei : ei ∈ G0.E) : mem' (tok.slots + ei) = mem (tok.slots + ei) :=
    hOf (hT9 ei (hCapE ei hei)) (by decide)
  have hRec (ei : ℕ) (hei : ei ∈ G0.E) :
      mem' (tok.edgeRecords + ei) = mem (tok.edgeRecords + ei) :=
    hOf (hT13 ei (hCapE ei hei)) (by decide)
  have hEdgeSl {sl : ℕ} (his : isEdgeSlot curTree.n sl) : sl < 2 * tok.tree.n := by
    unfold isEdgeSlot at his; omega
  have hCntLe := hOffInv.1
  exact
    { baseLe := hBaseLe
      dir := ⟨(hOf (hT1 6 (by omega)) (by decide)).trans hD6,
        (hOf (hT1 7 (by omega)) (by decide)).trans hD7,
        (hOf (hT1 8 (by omega)) (by decide)).trans hD8,
        (hOf (hT1 9 (by omega)) (by decide)).trans hD9,
        (hOf (hT1 10 (by omega)) (by decide)).trans hD10,
        (hOf (hT1 12 (by omega)) (by decide)).trans hD12,
        (hOf (hT1 13 (by omega)) (by decide)).trans hD13,
        (hOf (hT1 14 (by omega)) (by decide)).trans hD14⟩
      hdr := ⟨(hOf (by simpa using hT2 0 (by omega)) (by decide)).trans hH0,
        (hOf (hT2 5 (by omega)) (by decide)).trans hH5⟩
      graph := hRG.of_agree fun a ha1 ha2 => hag a (hGraphLoc a ha1 ha2).2.2
      sub := hSub
      capE := hCapE
      canonProp := hCanonP
      treeN := hTreeN
      lct := ⟨curTrees, curFree, curDepth, hL1, hL2,
        namedSlots_congr_slot hL3 (fun ei hei => hSl ei (hSub hei))
          (fun sl _ his => hOf (hT10 sl (hEdgeSl his)) (by decide)),
        liveAccounts_congr_slot hL4 (fun ei hei => hSl ei (hSub hei))⟩
      treeRep := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap curTree
        curTreeTok mem mem' (fun a ha => (hag a (hFootLoc a ha).2).symm)).1 hTreeRep
      slotThr := fun ei hei => by
        have hslot := (hL3.forward ei hei).2.1
        rw [hSl ei (hSub hei)]
        rw [hOf (hT11 _ (hEdgeSl hslot)) (by decide),
          hOf (hT12 ei (hCapE ei (hSub hei))) (by decide)]
        exact hSlotThr ei hei
      offSlot := fun ei hei hnot => (hSl ei hei).trans (hOffSlot ei hei hnot)
      offRec := fun ei hei hnot => by
        rw [hRec ei hei]
        exact (hOffRec ei hei hnot).congr (fun a ha1 ha2 => by
          have := (hRecLoc ei hei hnot (a - mem (tok.edgeRecords + ei)) (by omega)).2.2.2
          rw [show mem (tok.edgeRecords + ei) + (a - mem (tok.edgeRecords + ei)) = a by
            omega] at this
          exact hag a this)
      offReady := fun ei hei hnot hnd hdet =>
        (hOf (hT15 ei (hCapE ei hei)) (by decide)).trans (hOffReady ei hei hnot hnd hdet)
      offDisj := fun e₁ he₁ e₂ he₂ hne h₁ h₂ => by
        rw [hRec e₁ he₁, hRec e₂ he₂]; exact hOffDisj e₁ he₁ e₂ he₂ hne h₁ h₂
      offCntAt := (hOf (hT1 11 (by omega)) (by decide)).trans hOffCnt
      offInv := ⟨hCntLe,
        fun j hj => by
          rw [hOf (hT14 j (by omega)) (by decide)]
          exact ⟨(hOffInv.2.1 j hj).1,
            (hOf (hT15 _ (hOffInv.2.1 j hj).1) (by decide)).trans (hOffInv.2.1 j hj).2⟩,
        fun j1 hj1 j2 hj2 hne => by
          rw [hOf (hT14 j1 (by omega)) (by decide), hOf (hT14 j2 (by omega)) (by decide)]
          exact hOffInv.2.2.1 j1 hj1 j2 hj2 hne,
        fun e he => by rw [hOf (hT15 e he) (by decide)]; exact hOffInv.2.2.2.1 e he,
        fun e he h1 => by
          rw [hOf (hT15 e he) (by decide)] at h1
          obtain ⟨j, hj, hje⟩ := hOffInv.2.2.2.2 e he h1
          exact ⟨j, hj, (hOf (hT14 j (by omega)) (by decide)).trans hje⟩⟩
      footLoc := hFootLoc
      graphLoc := hGraphLoc
      recLoc := fun ei hei hnot j hj => by rw [hRec ei hei]; exact hRecLoc ei hei hnot j hj }

end MinCostFlow.MinRatio
