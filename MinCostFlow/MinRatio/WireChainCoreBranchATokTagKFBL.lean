module

public import MinCostFlow.MinRatio.WireChainCoreBranchATokHypKFBL
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# Branch A Step 5b: the new token and its tags (`WireChainCoreBranchATokTagKFBL`)

After Branch A, the solver token changes in the parts that Branch A rebuilt: the tree of the new
forest, the cores and the last level from Step 4, the new root graph, and the off-ready count.
This file defines that token, `wireBranchATokNew`, and proves the two parts of its
representation that are about tags:
* `tagsNew`: the tag map `SolverTagsAt`;
* `levelMetaNew`, `levelCapsNew`: the level metadata `SolverLevelMetaAt`, `SolverLevelCapsAt`.

The new tag map keeps the old tags below `uIntBuf`, except the tags of the parts that Branch A
rebuilt (19, 20, `21 + j`, `23 + d`), which it clears. Above `uIntBuf` it tags the words that
Branch A allocated, by region: the tree, the records of Sync 1, the thresholds and records of the
new edges, the new root graph, the new lengths of level 0, the last level, the cores, and the
other words of Step 4.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

open Classical in
/-- The solver token after Branch A. `mem4` is the memory after Step 4, which holds the handles
of the new cores and of the last level, and the threshold pointers of the new edges. -/
@[expose, reducible] noncomputable def wireBranchATokNew {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap
      termTok4 newOffCnt : ℕ) (mem4 : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ)
    (curTree2 : PathTreeState) (curTrees2 : List AuxTree) (curFree2 : List ℕ)
    (curDepth2 : ℕ → ℕ)
    (curTreeTok2 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (coreTok4 : ℕ → Rcore.τ) : SolverToken cfg L Rcore :=
  let d := cfg.P.d
  let handleBase := tok.handle + 18
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch tr.2.2.2.2
  let Rterm := LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
    ((alg2PreResetState cfg model U gVec lVec).chain.G d).E
  { tok with
    offReadyCount := newOffCnt
    rootGraph := newRootGraph
    tree := curTree2, trees := curTrees2, free := curFree2, depth := curDepth2
    treeTok := curTreeTok2
    coreHandle := fun j => mem4 (handleBase + j), coreTok := coreTok4
    termHandle := mem4 (handleBase + d), vcLast := vCap, ecLast := eCap, termTok := termTok4
    owned := fun a => tok.owned a ∨ (heap + 1 ≤ a ∧ a < nextHeap + 1)
    tag := fun a =>
      if a < uIntBuf then
        if tok.tag a = 19 ∨ tok.tag a = 20 ∨ tok.tag a = 23 + d ∨ (∃ j < d, tok.tag a = 21 + j)
        then 0
        else tok.tag a
      else if (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
          curTreeTok2 a then 16
      else if heap1 ≤ a ∧ a < heapSync then 18
      else if heapSync + 3 * L ≤ a ∧ a < heap2 then
        if ∃ e ∈ model.extG.E, tr.2.1 e ∉ G0.E ∧
            mem4 (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) ≤ a ∧
            a < mem4 (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) + L then 17 else 18
      else if newRootGraph ≤ a ∧ a < newRootGraph + dynGraphSize vCap eCap then 20
      else if newLen0 ≤ a ∧ a < newLen0 + eCap * L then 23 + d
      else if Rterm.foot (mem4 (handleBase + d)) termTok4 a then 19
      else if h : ∃ j : Fin d, Rcore.foot (mem4 (handleBase + j.val)) (coreTok4 j.val) a then
        21 + (Classical.choose h).val
      else if heap3 ≤ a ∧ a < heap4 then 23 + d
      else 0 }

namespace WireBranchATokHypKFBL

variable {w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap heap1 heapSync heap2
  newLen0 newRootGraph heap3 heap4 nextHeap termTok4 : ℕ} {cfg : Alg2Config}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem : ℕ → ℕ} {s4 s5g : State}
  {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
  {gVec lVec : ℕ → ℝ} {curTree2 : PathTreeState} {curTrees2 : List AuxTree}
  {curFree2 : List ℕ} {curDepth2 : ℕ → ℕ}
  {curTreeTok1 curTreeTok2 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
  {newCanonVal : ℕ → PathEdgeValue} {coreTok4 : ℕ → Rcore.τ}

variable (H : WireBranchATokHypKFBL w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap
  heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap termTok4 cfg Rcore mem0 mem s4
  s5g model tok U B R gVec lVec curTree2 curTrees2 curFree2 curDepth2 curTreeTok1 curTreeTok2
  newCanonVal coreTok4)
include H

/-- The new token keeps every old tag that Branch A does not clear. -/
theorem tagPre {newOffCnt a v : ℕ} (ht : tok.tag a = v) (hv : v ∉ [0, 19, 20])
    (h23 : v ≠ 23 + cfg.P.d) (hc : ∀ j < cfg.P.d, v ≠ 21 + j) :
    (wireBranchATokNew P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0 newRootGraph heap3
      heap4 nextHeap termTok4 newOffCnt s4.mem model tok U gVec lVec curTree2 curTrees2 curFree2
      curDepth2 curTreeTok2 coreTok4).tag a = v := by
  have hv' : ∀ c ∈ [0, 19, 20], v ≠ c := fun c hc' h => hv (h ▸ hc')
  have hlt := H.tagLt (ht ▸ hv' 0 (by simp))
  dsimp only [wireBranchATokNew]
  rw [ite_eq_left hlt, ite_eq_right (by
    rw [ht]; push Not; exact ⟨hv' 19 (by simp), hv' 20 (by simp), h23, hc⟩), ht]

set_option maxHeartbeats 800000 in
/-- The tag map of the new token. -/
theorem tagsNew {memK : ℕ → ℕ} (newOffCnt : ℕ)
    (hFr : ∀ a, a ≠ root + 11 → (a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a) →
      (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) → memK a = s5g.mem a) :
    let tok' := wireBranchATokNew P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0
      newRootGraph heap3 heap4 nextHeap termTok4 newOffCnt s4.mem model tok U gVec lVec curTree2
      curTrees2 curFree2 curDepth2 curTreeTok2 coreTok4
    SolverTagsAt root m (alg2PreResetState cfg model U gVec lVec) tok' memK := by
  intro tok'
  classical
  obtain ⟨_, _, _, _, hFreshInv0, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _,
    hTags0⟩ := H.rep0
  obtain ⟨hOwnOfTag, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hT13,
    hT14, hT15, hT16, hT1718, _, _, _⟩ := hTags0
  obtain ⟨_, _, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.ref
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, hNextLo, hNextW⟩ := H.heaps
  have hULe := H.uLeHeap
  let d := cfg.P.d
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch tr.2.2.2.2
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let Rterm' := LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E
  have hPreExtG : modelPre.extG = model.extG := H.preExtG
  have hPreE2I : modelPre.extToInt = level0E2I true G0' tr.2.1 := H.preE2I
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := H.freshPre
  have hTreeN : tok'.tree.n = tok.tree.n := H.treeN2.trans hTreeN0.symm
  refine ⟨fun a hne => ?_,
    fun j hj => H.tagPre (hT1 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT2 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT3 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT4 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT5 j hj) (by decide) (by omega) (fun _ _ => by omega),
    H.tagPre hT6 (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT7 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT8 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT9 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT10 j (by omega)) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT11 j (by omega)) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT12 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT13 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT14 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun j hj => H.tagPre (hT15 j hj) (by decide) (by omega) (fun _ _ => by omega),
    fun a ha => ?_, fun e he => ?_, fun a ha => ?_, fun a ha1 ha2 => ?_, fun i hi a ha => ?_⟩
  · -- a word with a nonzero tag is owned
    dsimp only [tok', wireBranchATokNew] at hne ⊢
    split_ifs at hne with hU hSkip hTr h18 hN hN17 h20 hL0 hRm hRc hM3
    · exact (hne rfl).elim
    · exact Or.inl (hOwnOfTag a hne)
    · rcases H.treeFoot2 a hTr with h0 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · exact Or.inl (hOwnOfTag a (by rw [hT16 a h0]; decide))
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · have h1 := (H.termFoot4 a hRm).1
      have h2 := (H.termFoot4 a hRm).2.1
      exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨j, hj⟩ := hRc
      have h1 := ((H.cores4 j.val j.isLt).2.2.2.2 a hj).1
      have h2 := ((H.cores4 j.val j.isLt).2.2.2.2 a hj).2
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact (hne rfl).elim
  · -- the foot of the new tree
    rcases H.treeFoot2 a ha with h0 | ⟨hlo, _⟩ | ⟨hlo, _⟩
    · exact H.tagPre (hT16 a h0) (by decide) (by omega) (fun _ _ => by omega)
    · dsimp only [tok', wireBranchATokNew]; rw [ite_eq_right (by omega), ite_eq_left ha]
    · dsimp only [tok', wireBranchATokNew]; rw [ite_eq_right (by omega), ite_eq_left ha]
  · -- the thresholds and the off-forest records of the live edges
    have he0 : e ∈ model.extG.E := hPreExtG ▸ he
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hInG0, hNotG0⟩ := H.canon4 e he0
    have hOldEq (hOld : tr.2.1 e ∈ G0.E) : model.extToInt e = tr.2.1 e := by
      by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
      · exact False.elim ((hDichRep e he0 hRepE).2.2.2.1 hOld)
      · exact (hDichUnch e he0 hRepE).2.1.symm
    refine ⟨fun j hj => ?_, fun hnot j hj => ?_⟩
    · rw [(H.thrK hFr e he).1, hPreE2I]
      by_cases hOld : tr.2.1 e ∈ G0.E
      · rw [(hInG0 hOld).1]
        have h17 : tok.tag (mem0 (tok.edgeThresholds + tr.2.1 e) + j) = 17 := by
          rw [← hOldEq hOld]; exact (hT1718 e he0).1 j hj
        exact H.tagPre h17 (by decide) (by omega) (fun _ _ => by omega)
      · obtain ⟨hlo, hhi, _, _⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e)
          at hlo
        change s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) + L ≤ heap2 at hhi
        dsimp only [tok', wireBranchATokNew]
        rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi _ (by omega) (by omega)),
          ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left ⟨e, he0, hOld, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩]
    · have hei := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
      rw [(H.recOffK hFr _ hei hnot).1, (H.recOffK hFr _ hei hnot).2, hPreE2I]
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨hlo, hhi, hnf0⟩ := (hInG0 hOld).2.1 hTree
          have hnf1 : ∀ a, s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) ≤ a →
              a < s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) →
              ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
                curTreeTok1 a := hnf0
          change heap1 ≤ s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
          change s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heapSync
            at hhi
          have hNotTr : ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot
              tok.treeHeap curTreeTok2
              (s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + j) := fun hf => by
            rcases H.footEnd _ hf with h1 | ⟨hlo', _⟩
            · exact hnf1 _ (by omega) (by omega) h1
            · omega
          dsimp only [tok', wireBranchATokNew]
          rw [ite_eq_right (by omega), ite_eq_right hNotTr, ite_eq_left ⟨by omega, by omega⟩]
        · rw [(hInG0 hOld).2.2 hTree]
          have h18 : tok.tag (mem0 (tok.edgeRecords + tr.2.1 e) + j) = 18 := by
            rw [← hOldEq hOld]; exact (hT1718 e he0).2 ((hOldEq hOld).symm ▸ hTree) j hj
          exact H.tagPre h18 (by decide) (by omega) (fun _ _ => by omega)
      · obtain ⟨_, _, hlo, hhi⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
        change s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heap2
          at hhi
        have hNot17 : ¬ ∃ e₁ ∈ model.extG.E, tr.2.1 e₁ ∉ G0.E ∧
            s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) ≤
              s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + j ∧
            s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + j <
              s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L := by
          rintro ⟨e₁, he1, hnot1, h1, h2⟩
          have hD : s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L ≤
                s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) ∨
              s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤
                s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) :=
            H.thrOffDisj4 e₁ he1 hnot1 e he0 hOld
          rcases hD with hd1 | hd2 <;> omega
        dsimp only [tok', wireBranchATokNew]
        rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi _ (by omega) (by omega)),
          ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_right hNot17]
  · -- the foot of the last level
    have haP : Rterm'.foot (s4.mem (tok.handle + 18 + d)) termTok4 a :=
      (lastLevelRepresentation_foot_indep_P vCap eCap 4 L P 0 (modelPre.chain.G d).E _ _
        a).mpr ha
    obtain ⟨hlo, hhi, _⟩ := H.termFoot4 a haP
    dsimp only [tok', wireBranchATokNew]
    rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) hhi),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left haP]
  · -- the new root graph
    rw [hPreExtG, ← H.vCapEq, ← H.eCapEq] at ha2
    change newRootGraph ≤ a at ha1
    change a < newRootGraph + dynGraphSize vCap eCap at ha2
    dsimp only [tok', wireBranchATokNew]
    rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) (by omega)),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨ha1, ha2⟩]
  · -- the feet of the cores
    obtain ⟨hlo, hhi⟩ := (H.cores4 i hi).2.2.2.2 a ha
    have hNotRm : ¬ Rterm'.foot (s4.mem (tok.handle + 18 + d)) termTok4 a := fun hr =>
      (H.termFoot4 a hr).2.2 i hi ha
    have hex : ∃ j : Fin d, Rcore.foot (s4.mem (tok.handle + 18 + j.val)) (coreTok4 j.val) a :=
      ⟨⟨i, hi⟩, ha⟩
    have hChoose : (Classical.choose hex).val = i := by
      by_contra hne
      exact H.coreDisj4 _ (Classical.choose hex).isLt i hi hne a (Classical.choose_spec hex) ha
    dsimp only [tok', wireBranchATokNew]
    rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) hhi),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right hNotRm, dite_eq_left hex, hChoose]

/-- The level graphs of the new token. -/
theorem levelCapsNew {memK : ℕ → ℕ} (newOffCnt : ℕ)
    (hFr : ∀ a, a ≠ root + 11 → (a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a) →
      (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) → memK a = s5g.mem a) :
    let tok' := wireBranchATokNew P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0
      newRootGraph heap3 heap4 nextHeap termTok4 newOffCnt s4.mem model tok U gVec lVec curTree2
      curTrees2 curFree2 curDepth2 curTreeTok2 coreTok4
    SolverLevelCapsAt vCap eCap (alg2PreResetState cfg model U gVec lVec) tok' memK := by
  intro tok'
  obtain ⟨_, _, _, _, hTagMeta0, _⟩ := H.meta0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, _⟩ := H.heaps
  let d := cfg.P.d
  let lm := solverLevelMetaAddr tok.table d
  have hLM5k (j : ℕ) (hj : j < 2 * d) : memK (lm + j) = s4.mem (lm + j) :=
    H.k_eq4_tag hFr (hTagMeta0 j hj) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hRG5k : DynGraphAt memK newRootGraph vCap eCap
      ((alg2PreResetState cfg model U gVec lVec).chain.G 0) :=
    dynGraphAt_of_agree H.rg4 (fun a ha1 ha2 => H.k_eq4_hi hFr a (by omega) (by omega))
  exact fun j hj => by
    rw [show memK (lm + d + j) = s4.mem (lm + d + j) by
      have := hLM5k (d + j) (by omega); simpa [Nat.add_assoc] using this]
    by_cases hj0 : j = 0
    · subst hj0; rw [Nat.add_zero, H.lmd_4]
      exact hRG5k
    · obtain ⟨hDG, hlo, hhi, _⟩ := H.meta4 j (by omega) hj
      have hlo' : heap3 ≤ s4.mem (lm + d + j) := hlo
      have hhi' : s4.mem (lm + d + j) + dynGraphSize vCap eCap ≤ heap4 := hhi
      exact dynGraphAt_of_agree hDG (fun a ha1 ha2 => H.k_eq4_hi hFr a (by omega) (by omega))

set_option maxHeartbeats 400000 in
/-- The level metadata of the new token. -/
theorem levelMetaNew {memK : ℕ → ℕ} (newOffCnt : ℕ)
    (hFr : ∀ a, a ≠ root + 11 → (a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a) →
      (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) → memK a = s5g.mem a) :
    let tok' := wireBranchATokNew P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0
      newRootGraph heap3 heap4 nextHeap termTok4 newOffCnt s4.mem model tok U gVec lVec curTree2
      curTrees2 curFree2 curDepth2 curTreeTok2 coreTok4
    SolverLevelMetaAt P V (alg2PreResetState cfg model U gVec lVec) tok' memK := by
  intro tok'
  obtain ⟨⟨hN0Mem0, hTagN0_0, hTagSH_0, hTagSB_0⟩, _, hLvlM0, hTagLvlM0, hTagMeta0, _⟩ := H.meta0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, hNextLo, _⟩ := H.heaps
  have hULe := H.uLeHeap
  have hdPos := H.dPos
  let d := cfg.P.d
  let lm := solverLevelMetaAddr tok.table d
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  have hEx := ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j
      ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j))
      g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) } hdPos G0'.compact (G0.batchEnc U_int)
  have hLM5k (j : ℕ) (hj : j < 2 * d) : memK (lm + j) = s4.mem (lm + j) :=
    H.k_eq4_tag hFr (hTagMeta0 j hj) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hOwnNew (a : ℕ) (h1 : heap + 1 ≤ a) (h2 : a < nextHeap + 1) : tok'.owned a :=
    Or.inr ⟨h1, h2⟩
  refine ⟨⟨by
      rw [H.k_eq4_tag hFr hTagN0_0
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
        H.s4_tag hTagN0_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
          (by omega) (by omega) (fun _ _ => by omega),
        H.chPreEq, hEx.2.2.2.2.2.2.2.2.2.1]; exact hN0Mem0,
      H.tagPre hTagN0_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        (by omega) (fun _ _ => by omega),
      H.tagPre hTagSH_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        (by omega) (fun _ _ => by omega),
      H.tagPre hTagSB_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        (by omega) (fun _ _ => by omega)⟩,
    fun j hj => hOwnNew (s4.mem (tok.handle + 18 + j)) (by have := (H.cores4 j hj).2.1; omega)
      (by have := (H.cores4 j hj).2.2.1; omega),
    fun j hj => by
      rw [H.k_eq4_tag hFr (hTagLvlM0 j hj)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
        H.s4_tag (hTagLvlM0 j hj) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
          (by omega) (by omega) (fun _ _ => by omega),
        H.chPreEq, congrFun hEx.2.2.2.2.2.2.2.2.1 j]; exact hLvlM0 j hj,
    fun j hj => H.tagPre (hTagLvlM0 j hj)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega)
      (fun _ _ => by omega),
    fun j hj => H.tagPre (hTagMeta0 j hj)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega)
      (fun _ _ => by omega),
    fun j hj => ⟨vCap, eCap, H.levelCapsNew newOffCnt hFr j hj, ?_, ?_, ?_, ?_⟩⟩
  · rw [hLM5k j (by omega)]
    by_cases hj0 : j = 0
    · subst hj0; rw [Nat.add_zero, H.lm0_4]
      exact H.len4.congr (fun e he t ht => by
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (H.rg4.2.2.1 e he))
        exact H.k_eq4_hi hFr _ (by omega) (by omega))
    · obtain ⟨hDG, _, _, hEV, hlo, hhi, _⟩ := H.meta4 j (by omega) hj
      exact hEV.congr (fun e he t ht => by
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hDG.2.2.1 e he))
        exact H.k_eq4_hi hFr _ (by omega) (by omega))
  · rw [hLM5k j (by omega)]
    by_cases hj0 : j = 0
    · subst hj0; rw [Nat.add_zero, H.lm0_4]; exact hOwnNew newLen0 (by omega) (by omega)
    · obtain ⟨_, _, _, _, hlo, hhi, _⟩ := H.meta4 j (by omega) hj
      exact hOwnNew (s4.mem (solverLevelMetaAddr tok.table cfg.P.d + j)) (by omega) (by omega)
  · intro a ha1 ha2; rw [hLM5k j (by omega)] at ha1 ha2
    by_cases hj0 : j = 0
    · subst hj0; rw [Nat.add_zero, H.lm0_4] at ha1 ha2
      dsimp only [tok', wireBranchATokNew]
      rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) (by omega)),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left ⟨ha1, ha2⟩]
    · obtain ⟨_, _, _, _, hlo, hhi, hNoC, hNoTL, _⟩ := H.meta4 j (by omega) hj
      change s4.mem (solverLevelMetaAddr tok.table cfg.P.d + j) ≤ a at ha1
      change a < s4.mem (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L at ha2
      dsimp only [tok', wireBranchATokNew]
      rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) (by omega)),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (hNoTL a ha1 ha2),
        dite_eq_right (fun ⟨r, hr⟩ => (hNoC r.val r.isLt).1 a ha1 ha2 hr),
        ite_eq_left ⟨by omega, by omega⟩]
  · intro a ha1 ha2
    rw [show memK (lm + d + j) = s4.mem (lm + d + j) by
      have := hLM5k (d + j) (by omega); simpa [Nat.add_assoc] using this] at ha1 ha2
    by_cases hj0 : j = 0
    · subst hj0; simp only [Nat.add_zero, ↓reduceIte] at ha1 ha2 ⊢; rw [H.lmd_4] at ha1 ha2
      dsimp only [tok', wireBranchATokNew]
      rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) (by omega)),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨ha1, ha2⟩]
    · simp only [hj0, ↓reduceIte]
      obtain ⟨_, hlo, hhi, _, _, _, hNoC, _, hNoTG⟩ := H.meta4 j (by omega) hj
      change s4.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ≤ a at ha1
      change a < s4.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) +
        dynGraphSize vCap eCap at ha2
      dsimp only [tok', wireBranchATokNew]
      rw [ite_eq_right (by omega), ite_eq_right (H.notTr2_hi a (by omega) (by omega)),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (hNoTG a ha1 ha2),
        dite_eq_right (fun ⟨r, hr⟩ => (hNoC r.val r.isLt).2 a ha1 ha2 hr),
        ite_eq_left ⟨by omega, by omega⟩]

end WireBranchATokHypKFBL

end MinCostFlow.MinRatio
