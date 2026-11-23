module

public import MinCostFlow.MinRatio.WireChainCoreBranchATokRunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchATokTagKFBL
public import MinCostFlow.MinRatio.SolverLevelLayout
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# Branch A Step 5b: the post (`WireChainCoreBranchATokKFBL`)

This file puts Step 5b together. From the facts `WireBranchATokHypKFBL` on the states `s4` and
`s5g`, the run `readyRet_runs` gives the final state. Its memory differs from `s5g` only in the
count word `root + 11` and in the two off-ready arrays. With the new token `wireBranchATokNew`,
we then prove the Branch A postconditions of `OrdChainUpdateCoreSpecWExtKFBL`:
* the representation `solverStateRep` of the model after the reset, at the new token;
* the level metadata and level graphs (from `WireChainCoreBranchATokTagKFBL.lean`);
* the numeric invariants of the tree and of the off-forest records;
* the empty select outputs, since Branch A rebuilds every level;
* the frame below `heap`, the footprint, and the cost against the potentials.

The only result used later is `wireBranchAReadyAndTokKFBL_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine
open WireBranchATokHypKFBL (tagSep tag_of_block)

/-- Level-block disjointness when level `0` has its length block before its graph block below
`heap3`, and levels `1 ≤ j < d` lie at or above `heap3` with each graph block before its length
block and each length block before the next level's graph block. -/
private theorem solverLevelMetaDisjAt_of_level0_and_suffix {cfg : Alg2Config}
    {L vCap eCap newLen0 newRootGraph heap3 : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem : ℕ → ℕ}
    (htab : tok'.table = tok.table)
    (h0L : mem (solverLevelMetaAddr tok.table cfg.P.d) = newLen0)
    (h0G : mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d) = newRootGraph)
    (h0LG : newLen0 + eCap * L ≤ newRootGraph)
    (h0GHi : newRootGraph + dynGraphSize vCap eCap ≤ heap3)
    (hSufLo : ∀ j, 1 ≤ j → j < cfg.P.d →
      heap3 ≤ mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hSufGL : ∀ j, 1 ≤ j → j < cfg.P.d →
      mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hSufLG : ∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < cfg.P.d →
      mem (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelMetaDisjAt vCap eCap tok' mem := by
  dsimp only [SolverLevelMetaDisjAt]
  rw [htab]
  set d := cfg.P.d
  set lm := solverLevelMetaAddr tok.table d
  refine ⟨fun j hj a ha1 ha2 r hr => ⟨?_, fun hne => ?_⟩, fun j₁ hj₁ j₂ hj₂ hne => ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [Nat.add_zero, h0G] at ha1 ha2
      rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [Nat.add_zero, h0L]; exact Or.inr (le_trans h0LG ha1)
      · exact Or.inl (lt_of_lt_of_le ha2 (le_trans h0GHi (le_trans (hSufLo r hr1 hr)
          (le_trans (Nat.le_add_right _ _) (hSufGL r hr1 hr)))))
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [Nat.add_zero, h0L]
        exact Or.inr (le_trans h0LG (le_trans (Nat.le_add_right _ _)
          (le_trans h0GHi (le_trans (hSufLo j hj1 hj) ha1))))
      · rcases lt_trichotomy r j with hlt | rfl | hgt
        · exact Or.inr (le_trans (hSufLG r j hr1 hlt hj) ha1)
        · exact Or.inl (lt_of_lt_of_le ha2 (hSufGL r hr1 hr))
        · exact Or.inl (lt_of_lt_of_le ha2 (le_trans (hSufGL j hj1 hj)
            (le_trans (Nat.le_add_right _ _) (le_trans (hSufLG j r hj1 hgt hr)
              (le_trans (Nat.le_add_right _ _) (hSufGL r hr1 hr))))))
  · rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [Nat.add_zero, h0G] at ha1 ha2
      have hr1 : 1 ≤ r := by omega
      exact Or.inl (lt_of_lt_of_le ha2 (le_trans h0GHi (hSufLo r hr1 hr)))
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [Nat.add_zero, h0G]
        exact Or.inr (le_trans h0GHi (le_trans (hSufLo j hj1 hj) ha1))
      · rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inr (le_trans (hSufGL r hr1 hr) (le_trans (Nat.le_add_right _ _)
            (le_trans (hSufLG r j hr1 hlt hj) ha1)))
        · exact Or.inl (lt_of_lt_of_le ha2 (le_trans (hSufGL j hj1 hj)
            (le_trans (Nat.le_add_right _ _) (hSufLG j r hj1 hgt hr))))
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : 1 ≤ j₂ := by omega
      rcases Nat.eq_zero_or_pos j₁ with rfl | h1
      · rw [Nat.add_zero, h0L]
        exact Or.inl (le_trans h0LG (le_trans (Nat.le_add_right _ _)
          (le_trans h0GHi (le_trans (hSufLo j₂ h2 hj₂)
            (le_trans (Nat.le_add_right _ _) (hSufGL j₂ h2 hj₂))))))
      · exact Or.inl (le_trans (hSufLG j₁ j₂ h1 hlt hj₂)
          (le_trans (Nat.le_add_right _ _) (hSufGL j₂ h2 hj₂)))
    · have h1 : 1 ≤ j₁ := by omega
      rcases Nat.eq_zero_or_pos j₂ with rfl | h2
      · rw [Nat.add_zero, h0L]
        exact Or.inr (le_trans h0LG (le_trans (Nat.le_add_right _ _)
          (le_trans h0GHi (le_trans (hSufLo j₁ h1 hj₁)
            (le_trans (Nat.le_add_right _ _) (hSufGL j₁ h1 hj₁))))))
      · exact Or.inr (le_trans (hSufLG j₂ j₁ h2 hgt hj₁)
          (le_trans (Nat.le_add_right _ _) (hSufGL j₁ h1 hj₁)))

set_option maxHeartbeats 1000000 in
/-- Branch A Step 5b: the run from `s5g` and all Branch A postconditions of
`OrdChainUpdateCoreSpecWExtKFBL` at the new token. -/
theorem wireBranchAReadyAndTokKFBL_runs
    {w L P m V psi k epsExp drainUnit vCap eCap capExp isNeg rebuildOffReadyProc root uIntBuf
      heap heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap termTok4 : ℕ}
    {cfg : Alg2Config} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {s4 s5g : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    {gVec lVec : ℕ → ℝ}
    {curTree2 : PathTreeState} {curTrees2 : List AuxTree} {curFree2 : List ℕ}
    {curDepth2 : ℕ → ℕ}
    {curTreeTok1 curTreeTok2 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {newCanonVal : ℕ → PathEdgeValue} {coreTok4 : ℕ → Rcore.τ}
    (H : WireBranchATokHypKFBL w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap
      heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap termTok4 cfg Rcore mem0 mem
      s4 s5g model tok U B R gVec lVec curTree2 curTrees2 curFree2 curDepth2 curTreeTok1
      curTreeTok2 newCanonVal coreTok4)
    (hRebuildProc : p.procs[rebuildOffReadyProc]? = some (wireRebuildOffReadyBody isNeg))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4)) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let handleBase := tok.handle + 18
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let mNew := (modelPre.chain.G 0).m
    ∃ (cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore)
      (levelU levelUS : ℕ → List Update) (diffLists : ℕ → LevelDiffLists),
      Runs w p ω (wireBranchAReadyRetStmt rebuildOffReadyProc) s5g (.returned (nextHeap + 1)) out
        cost ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧ tok'.rootECap = tok.rootECap ∧
      tok'.table = tok.table ∧
      Rrep.rep root modelPre tok' out.mem ∧
      SolverLevelMetaAt P V modelPre tok' out.mem ∧
      SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
      out.mem (solverLevelMetaAddr tok'.table d + d) = tok'.rootGraph ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      OffTreeRecInv modelPre L out.mem tok'.edgeRecords B ∧
      OffTreeRecBound modelPre L out.mem tok'.edgeRecords B ∧
      out.mem (solverSelectHeapAddr tok.table d) = mem0 (solverSelectHeapAddr tok.table d) ∧
      out.mem (solverSelectBlocksAddr tok.table d) = mem0 (solverSelectBlocksAddr tok.table d) ∧
      UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn (Rrep.foot root tok') out.mem heap
        (nextHeap + 1) 0 model.chain modelPre.chain levelU levelUS diffLists ∧
      ZeroFrom out.mem (nextHeap + 1) ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap + 1)) ∧
      cost + Rrep.phi root tok' out.mem ≤
        (80 * mNew + mNew * drainUnit + 120) +
        (Rtree.phi tok.treeHeap curTreeTok2 s5g.mem +
          (Finset.range d).sum
            (fun j => Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s4.mem)) ∧
      SolverLevelMetaDisjAt vCap eCap tok' out.mem := by
  classical
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let d := cfg.P.d
  let cnt := d + 1
  let handleBase := tok.handle + 18
  let branchBase := handleBase + cnt
  let lm := solverLevelMetaAddr tok.table d
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let newF := modelPre.chain.toTreeChain.chainTree
  let mNew := (modelPre.chain.G 0).m
  let canonC : ℕ → PathEdgeValue := fun j => newCanonVal (compactUnrank G0'.E j)
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, _, _, hExtLtM0,
    ⟨_, hIntCapPos, _, _⟩, hSched0, _, hTreeN0, _, _, _, _, _, _, _, hWire0, hTags0⟩ := H.rep0
  obtain ⟨hOwnOfTag, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hT13,
    hT14, hT15, hT16, _, _, _, _⟩ := hTags0
  obtain ⟨⟨_, _, hTagSH_0, hTagSB_0⟩, _, _, _, hTagMeta0, _⟩ := H.meta0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, hNextLo, hNextW⟩ := H.heaps
  have hULe := H.uLeHeap
  have hdPos := H.dPos
  have hTreeN2 := H.treeN2
  have hPreExtG : modelPre.extG = model.extG := H.preExtG
  have hPreE2I : modelPre.extToInt = level0E2I true G0' tr.2.1 := H.preE2I
  have hPreI2E : modelPre.intToExt = level0I2E true G0' tr.2.2.1 := H.preI2E
  have hPreNF : modelPre.nextFresh = level0NF true G0' tr.2.2.2.1 := H.preNF
  have hPreG0 : modelPre.chain.G 0 = G0'.compact := H.preG0
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := H.freshPre
  have hPreG0m : mNew = G0'.m := H.preG0m
  have hRecLoc : ∀ e ∈ model.extG.E, ∀ a,
      s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) ≤ a →
      a < s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) →
      a < heap2 ∧ (a < uIntBuf → tok.tag a = 18) := H.recLoc
  -- the run
  obtain ⟨newOffCnt, cRun, s5k, rReadyRet, hcRun, hNewOffLe, hR11End, hOffInvEnd, hInOffDone,
    hFrRdy⟩ := H.readyRet_runs (ω := ω) hRebuildProc hIsNegOk
  have hcRun' : cRun ≤ 80 * mNew + 120 := hcRun
  -- the tree, the cores, the slots and the names after the run
  have hTreeLocEnd := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC)
    tok.treeHeap curTree2 curTreeTok2 s5g.mem s5k.mem (fun a ha => by
      rcases H.treeFoot2 a ha with h0 | ⟨hlo, _⟩ | ⟨hlo, _⟩
      · exact (H.k_eq5g_tag hFrRdy (hT16 a h0) (by decide)).symm
      · exact (H.k_eq5g_geU hFrRdy a (by omega)).symm
      · exact (H.k_eq5g_geU hFrRdy a (by omega)).symm)
  have hCoresEnd (j : ℕ) (hj : j < d) :
      s5k.mem (handleBase + j) = s4.mem (handleBase + j) ∧
      s5k.mem (branchBase + j) = modelPre.chain.bran j ∧
      Rcore.rep (s4.mem (handleBase + j)) (chainLevelOrdAbs modelPre.chain j) (coreTok4 j)
        s5k.mem ∧
      Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s5k.mem =
        Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s4.mem := by
    obtain ⟨hB4, _, _, hRep4, hFt4⟩ := H.cores4 j hj
    have h4a := hT4 j (by omega)
    have h4b : tok.tag (branchBase + j) = 4 := tag_of_block tok.tag hT4 _ (by omega) (by omega)
    have hloc := H.coreLocal (s4.mem (handleBase + j)) (chainLevelOrdAbs modelPre.chain j)
      (coreTok4 j) s4.mem s5k.mem (fun a ha =>
        (H.k_eq4_hi hFrRdy a (by have := (hFt4 a ha).1; omega) (hFt4 a ha).2).symm)
    exact ⟨H.k_eq4_tag hFrRdy h4a (by decide), (H.k_eq4_tag hFrRdy h4b (by decide)).trans hB4,
      hloc.1 hRep4, hloc.2.symm⟩
  have hSlotEqEnd (ei : ℕ) (hei : ei < tok.intCap) :
      s5k.mem (tok.slots + ei) = s5g.mem (tok.slots + ei) :=
    H.k_eq5g_tag hFrRdy (hT9 ei hei) (by decide)
  have hNameEqEnd (sl : ℕ) (hsl : isEdgeSlot curTree2.n sl) :
      s5k.mem (tok.names + sl) = s5g.mem (tok.names + sl) := by
    have hlt : sl < 2 * tok.tree.n := by unfold isEdgeSlot at hsl; omega
    exact H.k_eq5g_tag hFrRdy (hT10 sl hlt) (by decide)
  have hNamedFinal : TreeEditNamedSlots curTree2 curTrees2 newF
      (fun ei => s5k.mem (tok.slots + ei)) (fun sl => s5k.mem (tok.names + sl)) :=
    namedSlots_congr_slot H.namedEnd
      (fun ei hei => hSlotEqEnd ei (H.preG0Cap ei (H.newSub hei)))
      (fun sl _ hsl => hNameEqEnd sl hsl)
  have hLiveFinal : TreeEditLiveAccounts curTree2 curTrees2 newF
      (fun ei => s5k.mem (tok.slots + ei)) canonC :=
    liveAccounts_congr_slot H.liveEnd
      (fun ei hei => hSlotEqEnd ei (H.preG0Cap ei (H.newSub hei)))
  -- the edge accounts
  obtain ⟨hAccountsEnd, hOrientEnd, hOffInvAccEnd, hOffBdEnd⟩ :=
    solverEdgeAccounts_of_treeSync (model := modelPre) (P := P) (B := B) (mem := s5k.mem)
      (slots := tok.slots) (names := tok.names) (slotThresholds := tok.slotThresholds)
      (edgeThresholds := tok.edgeThresholds) (edgeRecords := tok.edgeRecords)
      (inOffReady := tok.inOffReady) (intCap := tok.intCap)
      hFreshPre H.lctEnd hNamedFinal hLiveFinal H.newSub H.preG0Cap
      (fun e he => (H.thrK hFrRdy e he).2)
      (fun e he => by
        have he0 : e ∈ model.extG.E := hPreExtG ▸ he
        obtain ⟨_, hUnr, _, _, hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc, _, _⟩ :=
          H.canon4 e he0
        have hEq : canonC (modelPre.extToInt e) = newCanonVal (tr.2.1 e) := by
          dsimp [canonC]; rw [hPreE2I, hUnr]
        dsimp only; rw [hEq]; exact ⟨hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc⟩)
      (fun ei hei => by
        have hCap := H.preG0Cap ei (H.newSub hei)
        have hsl := (H.namedEnd.forward ei hei).2.1
        have hslLt : s5g.mem (tok.slots + ei) < 2 * tok.tree.n := by
          unfold isEdgeSlot at hsl; omega
        rw [hSlotEqEnd ei hCap, H.k_eq5g_tag hFrRdy (hT11 _ hslLt) (by decide),
          H.k_eq5g_tag hFrRdy (hT12 ei hCap) (by decide)]
        exact H.slotThrEnd ei hei)
      (fun e he hnot => by
        have hei := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
        rw [hSlotEqEnd _ (H.preG0Cap _ hei)]; exact H.offSlotEnd _ hei hnot)
      (fun e he hnot => by
        have hei := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
        have he0 : e ∈ model.extG.E := hPreExtG ▸ he
        obtain ⟨hRec5k, hRec5g⟩ := H.recOffK hFrRdy _ hei hnot
        rw [hRec5k]
        refine (H.offRecEnd _ hei hnot).1.congr fun a ha1 ha2 => ?_
        have hLoc := hRecLoc e he0 a (by rw [← hPreE2I, ← hRec5g]; exact ha1)
          (by rw [← hPreE2I, ← hRec5g]; omega)
        refine hFrRdy a (fun h => ?_) ?_ ?_
        · have h1 : tok.tag a = 1 := by rw [h]; exact hT1 11 (by omega)
          have := hLoc.2 (H.tagLt (by rw [h1]; decide)); omega
        · by_contra h; push Not at h
          have h14 := tag_of_block tok.tag hT14 a h.1 h.2
          have := hLoc.2 (H.tagLt (by rw [h14]; decide)); omega
        · by_contra h; push Not at h
          have h15 := tag_of_block tok.tag hT15 a h.1 h.2
          have := hLoc.2 (H.tagLt (by rw [h15]; decide)); omega)
      (fun e he hnot hdet => by
        have hei := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
        have hlt : modelPre.extToInt e < mNew := by
          have h := hei; rw [hPreG0] at h; simpa [MGraph.compact, MGraph.m, mNew, hPreG0m] using h
        have hSl0 := H.offSlotEnd _ hei hnot
        rw [hInOffDone _ hlt]
        exact ite_eq_left ⟨hSl0, hdet⟩)
      (fun e1 he1 e2 he2 hne hnot1 hnot2 => by
        have h1 := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he1
        have h2 := hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he2
        have hneI : modelPre.extToInt e1 ≠ modelPre.extToInt e2 := fun h =>
          hne ((hFreshPre.hLeft e1 he1).symm.trans (h ▸ hFreshPre.hLeft e2 he2))
        rw [(H.recOffK hFrRdy _ h1 hnot1).1, (H.recOffK hFrRdy _ h2 hnot2).1]
        exact H.offDisjEnd _ h1 _ h2 hneI hnot1 hnot2)
  -- the new token and its representation
  let tok' := wireBranchATokNew P vCap eCap uIntBuf heap heap1 heapSync heap2 newLen0
    newRootGraph heap3 heap4 nextHeap termTok4 newOffCnt s4.mem model tok U gVec lVec curTree2
    curTrees2 curFree2 curDepth2 curTreeTok2 coreTok4
  have hEx := ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j
      ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j))
      g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) } hdPos G0'.compact (G0.batchEnc U_int)
  have hRG5k : DynGraphAt s5k.mem newRootGraph vCap eCap (modelPre.chain.G 0) :=
    dynGraphAt_of_agree H.rg4 (fun a ha1 ha2 => H.k_eq4_hi hFrRdy a (by omega) (by omega))
  have hRepEnd : Rrep.rep root modelPre tok' s5k.mem := by
    refine ⟨?_, ?_, ?_, ?_, hFreshPre, ?_, hPreExtG.symm ▸ hExtLtM0,
      ⟨H.preG0Cap, hIntCapPos, by rw [hPreNF]; exact H.g0'mLeR.2, H.preI2EGe⟩, ?_, hOffInvEnd,
      H.treeN2.trans (congrArg MGraph.n hPreExtG.symm), H.lctEnd, hTreeLocEnd.1 H.treeRepEnd,
      hAccountsEnd, fun j hj => ⟨(hCoresEnd j hj).1, (hCoresEnd j hj).2.1, (hCoresEnd j hj).2.2.1⟩,
      ?_, ?_, ?_, ?_, H.tagsNew newOffCnt hFrRdy⟩
    · -- the root directory
      intro j hj
      have hj16 : j < 16 := by simpa using hj
      by_cases h11 : j = 11
      · subst h11; simpa [tok', wireBranchATokNew] using hR11End
      · by_cases h14 : j = 14
        · subst h14
          simpa [tok', wireBranchATokNew] using
            (H.k_eq4_root hFrRdy 14 (by omega) (by omega)).trans H.r14_4
        · rw [H.k_eq4_root hFrRdy j hj16 h11, H.s4_root j hj16 h11 h14]
          have h0 := hRootDir0 j hj
          have : [tok'.handle, tok'.table, tok'.levelsEnd, tok'.forward, tok'.inverse,
              tok'.freshCounter, tok'.slots, tok'.names, tok'.slotThresholds, tok'.edgeThresholds,
              tok'.edgeRecords, tok'.offReadyCount, tok'.offReadyList, tok'.inOffReady,
              tok'.rootGraph, tok'.intCap][j] =
            [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse,
              tok.freshCounter, tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds,
              tok.edgeRecords, tok.offReadyCount, tok.offReadyList, tok.inOffReady,
              tok.rootGraph, tok.intCap][j] := by interval_cases j <;> first | rfl | contradiction
          exact h0.trans this.symm
    · -- the detector header
      intro j hj; have hj8 : j < 8 := by simpa using hj
      rw [H.k_eq4_tag hFrRdy (hT2 j (by omega)) (by decide),
        H.s4_tag (hT2 j (by omega)) (by decide) (by omega) (by omega) (fun _ _ => by omega)]
      exact hDetHdr0 j hj
    · -- the numeric header
      intro j hj; have hj4 : j < 4 := by simpa using hj
      have h2 : tok.tag (tok.handle + 5 + j) = 2 := by
        have := hT2 (5 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [H.k_eq4_tag hFrRdy h2 (by decide),
        H.s4_tag h2 (by decide) (by omega) (by omega) (fun _ _ => by omega)]
      exact hNumHdr0 j hj
    · -- the parameters
      intro j hj; have hj9 : j < 9 := by simpa using hj
      have h2 : tok.tag (tok.handle + 9 + j) = 2 := by
        have := hT2 (9 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [H.k_eq4_tag hFrRdy h2 (by decide),
        H.s4_tag h2 (by decide) (by omega) (by omega) (fun _ _ => by omega)]
      exact hInitPar0 j hj
    · -- the fresh tables
      rw [hPreE2I, hPreI2E, hPreNF]
      exact ⟨(H.k_eq4_tag hFrRdy hT6 (by decide)).trans H.fresh4.1,
        fun e he => (H.k_eq4_tag hFrRdy (hT7 e he) (by decide)).trans (H.fresh4.2.1 e he),
        fun j hj => (H.k_eq4_tag hFrRdy (hT8 j hj) (by decide)).trans (H.fresh4.2.2 j hj)⟩
    · -- the schedule
      have hS5k (j : ℕ) (hj : j < 4 * cnt + 1) :
          s5k.mem (tok.levelsEnd + j) = s4.mem (tok.levelsEnd + j) :=
        H.k_eq4_tag hFrRdy (hT5 j hj) (by decide)
      have hS4M0 (j : ℕ) (hj : j < 4 * cnt + 1) (hneRC : j ≠ 2 * cnt)
          (hnotUC : j < 3 * cnt ∨ 3 * cnt + d ≤ j) :
          s4.mem (tok.levelsEnd + j) = mem0 (tok.levelsEnd + j) := by
        have h5 := hT5 j hj
        exact H.frame4_0 (tok.levelsEnd + j) (H.tagLt (by rw [h5]; decide))
          (tagSep _ _ _ _ _ h5 (hT1 11 (by omega)) (by decide))
          (tagSep _ _ _ _ _ h5 (hT1 14 (by omega)) (by decide)) (by omega)
          (by
            by_contra h; push Not at h
            have := tag_of_block tok.tag hT4 _ h.1 (by omega); omega)
          (by
            by_contra h; push Not at h
            have := tag_of_block tok.tag hT4 (tok.levelsEnd + j) (by omega) (by omega); omega)
          (by omega)
          (by rw [h5]; decide) (by rw [h5]; decide) (by rw [h5]; decide)
          (by rw [h5]; decide) (by rw [h5]; decide) (by rw [h5]; decide)
          (by rw [h5]; decide) (by rw [h5]; decide) (by rw [h5]; decide)
          (by rw [h5]; decide) (by rw [h5]; decide) (by rw [h5]; decide)
          (by rw [h5]; omega) (by rw [h5]; omega) (fun _ _ => by rw [h5]; omega)
      have hPreShift : modelPre.chain.shiftCount = model.chain.shiftCount := by
        rw [H.chPreEq]; exact hEx.2.2.2.2.2.2.2.2.2.2
      have hPreRC (i : ℕ) : modelPre.chain.rebuildCount i =
          if i = 0 then model.chain.rebuildCount 0 + 1 else model.chain.rebuildCount i := by
        rw [H.chPreEq]; exact hEx.2.2.2.2.2.1 i
      have hPreUpd (i : ℕ) (hi : i < d) : modelPre.chain.updCount i = 0 := by
        rw [H.chPreEq]; exact (hEx.2.2.1 i (Nat.zero_le _) hi).2.2.2
      have hPreUpdD : modelPre.chain.updCount cfg.P.d = model.chain.updCount cfg.P.d := by
        rw [H.chPreEq, (algorithm1_rebuild_counts cfg.T cfg.L cfg.P _ hdPos _ _).2.2.2 cfg.P.d,
          ite_eq_right (by omega)]
      refine ⟨fun i => by
          rw [hS5k i.val (by omega), hS4M0 i.val (by omega) (by omega) (Or.inl (by omega))]
          exact hSched0.1 i,
        fun i hi => by
          rw [show tok'.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cnt + i) from
            Nat.add_assoc _ _ _, hS5k (cnt + i) (by omega),
            hS4M0 (cnt + i) (by omega) (by omega) (Or.inl (by omega)), hPreShift, ← Nat.add_assoc]
          exact hSched0.2.1 i hi,
        fun i hi => by
          rw [show tok'.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * cnt + i) from
            Nat.add_assoc _ _ _, hS5k (2 * cnt + i) (by omega), hPreRC i]
          by_cases hi0 : i = 0
          · subst hi0; simpa using H.rc4
          · rw [hS4M0 (2 * cnt + i) (by omega) (by omega) (Or.inl (by omega)), ← Nat.add_assoc]
            simpa [hi0] using hSched0.2.2.1 i hi,
        fun i hi => by
          rw [show tok'.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * cnt + i) from
            Nat.add_assoc _ _ _, hS5k (3 * cnt + i) (by omega)]
          by_cases hilt : i < d
          · rw [hPreUpd i hilt, ← Nat.add_assoc]; exact H.uc4 i hilt
          · have hid : i = d := by omega
            subst hid
            rw [hS4M0 (3 * cnt + d) (by omega) (by omega) (Or.inr le_rfl), hPreUpdD,
              ← Nat.add_assoc]
            exact hSched0.2.2.2.1 d le_rfl,
        by
          rw [hS5k (4 * cnt) (by omega), hS4M0 (4 * cnt) (by omega) (by omega) (Or.inr (by omega))]
          exact hSched0.2.2.2.2⟩
    · -- the handle of the last level
      exact H.k_eq4_tag hFrRdy (hT4 d (by omega)) (by decide)
    · -- the branch of the last level
      have h4b : tok.tag (branchBase + d) = 4 := tag_of_block tok.tag hT4 _ (by omega) (by omega)
      exact (H.k_eq4_tag hFrRdy h4b (by decide)).trans H.termB4
    · -- the last level
      exact (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P
        (modelPre.chain.G d).E (s4.mem (handleBase + d))
        (modelPre.chain.lastK, modelPre.chain.lastLSFs) termTok4 s4.mem s5k.mem
        (fun a ha => (H.k_eq4_hi hFrRdy a (by have := (H.termFoot4 a ha).1; omega)
          (H.termFoot4 a ha).2.1).symm)).1 H.termRep4
    · -- `SolverWireInv`
      refine ⟨fun j hj => by
          rw [H.k_eq4_tag hFrRdy (hT3 j hj) (by decide),
            H.s4_tag (hT3 j hj) (by decide) (by omega) (by omega) (fun _ _ => by omega)]
          exact hWire0.1 j hj,
        by rw [hPreExtG, ← H.vCapEq, ← H.eCapEq]; exact hRG5k,
        ⟨H.newForest, fun ei hei => by
          have hei0 := H.newSub hei
          obtain ⟨h1, h2⟩ := H.rg4.1 ei hei0
          have hv1 : newF.tail ei < modelPre.extG.n := by
            rw [hPreExtG, ← H.vCapEq]; exact H.rg4.2.1 _ h1
          have hv2 : newF.head ei < modelPre.extG.n := by
            rw [hPreExtG, ← H.vCapEq]; exact H.rg4.2.1 _ h2
          exact ⟨H.preG0Cap ei hei0, hv1, hv2, named_account_endpoints_ne H.lctEnd hNamedFinal
            hei (by rw [H.treeN2, ← hPreExtG]; exact hv1)⟩⟩,
        hNamedFinal, hOrientEnd⟩
  -- the rest of the post
  have hLM5k (j : ℕ) (hj : j < 2 * d) : s5k.mem (lm + j) = s4.mem (lm + j) :=
    H.k_eq4_tag hFrRdy (hTagMeta0 j hj) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hHeapOff : ¬ Rrep.foot root tok' heap := by
    rintro (hOwn | hTree | ⟨j, hj, hCore⟩)
    · rcases hOwn with h0 | h1
      · have := H.footLt heap (Or.inl h0); omega
      · omega
    · rcases H.treeFoot2 heap hTree with h0 | ⟨hlo, _⟩ | ⟨hlo, _⟩
      · have := H.footLt heap (Or.inr (Or.inl h0)); omega
      · omega
      · omega
    · have := ((H.cores4 j hj).2.2.2.2 heap hCore).1; omega
  refine ⟨_, s5k, tok', fun _ => [], fun _ => [], fun _ => ⟨[], [], [], []⟩,
    rReadyRet, rfl, rfl, rfl, rfl, hRepEnd, H.levelMetaNew newOffCnt hFrRdy,
    H.levelCapsNew newOffCnt hFrRdy, by rw [hLM5k d (by omega), H.lmd_4], H.numEnd,
    hOffInvAccEnd, hOffBdEnd,
    (H.k_eq4_tag hFrRdy hTagSH_0 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
      (H.s4_tag hTagSH_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        (by omega) (by omega) (fun _ _ => by omega)),
    (H.k_eq4_tag hFrRdy hTagSB_0 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)).trans
      (H.s4_tag hTagSB_0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        (by omega) (by omega) (fun _ _ => by omega)),
    ⟨(H.k_eq4_sel hFrRdy heap le_rfl (by omega)).trans H.heap0_4,
      ⟨le_rfl, by simp only [Nat.zero_min, Nat.mul_zero, Nat.add_zero]; omega, fun t ht => by
        simp only [Nat.zero_min, Nat.mul_zero, Nat.add_zero, Nat.lt_one_iff] at ht
        subst ht; rw [Nat.add_zero]; exact hHeapOff⟩,
      fun j hj => by simp at hj⟩,
    fun a ha => (H.k_eq5g_geU hFrRdy a (by omega)).trans (H.z5g a (by omega)),
    fun a ha hnf => ?_, fun a ha => ?_, ?_, ?_⟩
  · -- the frame below `heap`
    have ht0 : tok.tag a = 0 := by by_contra h; exact hnf (Or.inl (hOwnOfTag a h))
    have hne11 : a ≠ root + 11 := fun h => by rw [h, hT1 11 (by omega)] at ht0; omega
    have hne14 : a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a := by
      by_contra h; push Not at h
      have := tag_of_block tok.tag hT14 a h.1 h.2; omega
    have hne15 : a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a := by
      by_contra h; push Not at h
      have := tag_of_block tok.tag hT15 a h.1 h.2; omega
    refine (hFrRdy a hne11 hne14 hne15).trans (Eq.trans ?_ (H.frame4 a ha hnf))
    by_cases hU : a < uIntBuf
    · exact (H.frame5g a (by omega) hne11).1 hU
        (by rw [ht0]; decide) (by rw [ht0]; decide) (by rw [ht0]; decide)
        (by rw [ht0]; decide) (by rw [ht0]; decide) (by rw [ht0]; decide) (by rw [ht0]; decide)
    · exact (H.frame5g a (by omega) hne11).2 (by omega) (fun hf => by
        rcases H.treeFoot1 a hf with h0 | ⟨hlo, _⟩
        · exact hnf (Or.inr (Or.inl h0))
        · omega)
  · -- the footprint
    rcases ha with hOwn | hTree | ⟨j, hj, hCore⟩
    · rcases hOwn with h0 | hnew
      · exact Or.inl (Or.inl h0)
      · exact Or.inr ⟨by omega, hnew.2⟩
    · rcases H.treeFoot2 a hTree with h0 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨hlo, hhi⟩ := (H.cores4 j hj).2.2.2.2 a hCore
      exact Or.inr ⟨by omega, by omega⟩
  · -- the cost against the potentials
    change _ + (Rtree.phi tok.treeHeap curTreeTok2 s5k.mem +
        (∑ j : Fin d, Rcore.phi (s4.mem (handleBase + j.val)) (coreTok4 j.val) s5k.mem) +
        newOffCnt * drainUnit) ≤ _
    rw [← hTreeLocEnd.2]
    have hSumPhi :
        (∑ j : Fin d, Rcore.phi (s4.mem (handleBase + j.val)) (coreTok4 j.val) s5k.mem) =
        (Finset.range d).sum
          (fun j => Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s4.mem) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j => Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s5k.mem)]
      exact Finset.sum_congr rfl (fun j hj => (hCoresEnd j (Finset.mem_range.mp hj)).2.2.2)
    rw [hSumPhi]
    have hOffMul : newOffCnt * drainUnit ≤ mNew * drainUnit := Nat.mul_le_mul_right _ hNewOffLe
    linarith [hcRun', hOffMul]
  · -- level-block pairwise disjointness
    refine solverLevelMetaDisjAt_of_level0_and_suffix (tok := tok) (heap3 := heap3) rfl
      (by simpa [Nat.add_zero] using (hLM5k 0 (by omega)).trans (by simpa [lm] using H.lm0_4))
      ((hLM5k d (by omega)).trans H.lmd_4) hNRGLo hH3Lo
      (fun j hj1 hj2 => by
        rw [show lm + d + j = lm + (d + j) from Nat.add_assoc _ _ _, hLM5k (d + j) (by omega),
          ← Nat.add_assoc]
        exact (H.meta4 j hj1 hj2).2.1)
      (fun j hj1 hj2 => by
        rw [show lm + d + j = lm + (d + j) from Nat.add_assoc _ _ _, hLM5k (d + j) (by omega),
          ← Nat.add_assoc, hLM5k j (by omega)]
        exact H.metaOrd4.1 j hj1 hj2)
      (fun j₁ j₂ hj1 hlt hj2 => by
        rw [hLM5k j₁ (by omega), show lm + d + j₂ = lm + (d + j₂) from Nat.add_assoc _ _ _,
          hLM5k (d + j₂) (by omega), ← Nat.add_assoc]
        exact H.metaOrd4.2 j₁ j₂ hj1 hlt hj2)

end MinCostFlow.MinRatio
