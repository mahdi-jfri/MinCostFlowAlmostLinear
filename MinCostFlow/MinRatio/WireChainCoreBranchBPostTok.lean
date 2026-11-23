module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSufOutKFBL
import MinCostFlow.Chain.Ordered.RenameFacts
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainCoreAlgebra

/-!
# Branch B post: the new token, select output, footprint, tags, and level metadata (`WireChainCoreBranchBPostTok`)

This file builds the new solver token `wireBranchBTokNew` from the final state `BranchBSufOutKFBL`
of Branch B and proves the postcondition conjuncts of `OrdChainCoreExtPost` that depend on the
token's ownership and region-tag partition:

* the model identities of `alg2PreResetState` (`branchB_modelPre_extG`,
  `branchB_modelPre_freshInv`, `branchB_modelPre_n0_lvlM`);
* the footprint growth bound (`branchB_foot_growth`);
* the select-block output `UpdateCoreSelectOutAt` (`branchB_selectOut`), using
  `branchBSufSlots_level` on `BranchBSelZone heap2 hS hT hX` and excluding non-core words of the
  select zone and `[heap, heap + 1 + 12 * d)` from `tok'.owned`;
* the region-tag invariant `SolverTagsAt` (`branchB_tagsNew`);
* the level metadata `SolverLevelMetaAt` (`branchB_levelMetaNew`), using `S.coreHandleLoc`,
  `S.metaKeep` below `min (fr + 1) d`, and `S.metaNew` from `fr + 1` on.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

open Classical in
/-- The solver token after Branch B, built from the final state `out` of `BranchBSufOutKFBL` and
the LCT witness `(curTrees, curFree, curDepth)` from `phase.lct`.

Below `uIntBuf` it keeps `tok.owned` and `tok.tag`. Above `uIntBuf` it owns:
* `[heap + 1 + 12 * d, heap2)`: tree words (tag `16`), new thresholds (`17`), and new/cut records
  (`18`);
* `BranchBSelZone heap2 hS hT hX` (`[heap2, hS) ∪ [hT, hX)`): ONLY the core footprints (`21 + j`),
  leaving all select lists, batches, and descriptors off `Rrep.foot root tok'`;
* `[hS, hT)`: the rebuilt last level (`19`), core footprints (`21 + j`), new core handles, and
  rebuilt level blocks (`23 + d`);
* `[hX, nextHeap)`: Sync 2a/2b tree words (`16`) and cut records (`18`).
The select header and slot array `[heap, heap + 1 + 12 * d)` lie off `tok'.owned`. -/
@[expose, reducible] noncomputable def wireBranchBTokNew {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt : ℕ)
    (outMem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update)
    (gVec lVec : ℕ → ℝ) (tokN : ℕ → Rcore.τ) (curTree : PathTreeState) (curTrees : List AuxTree)
    (curFree : List ℕ) (curDepth : ℕ → ℕ)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) :
    SolverToken cfg L Rcore :=
  let d := cfg.P.d
  let handleBase := tok.handle + 18
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let Rterm := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
    ((alg2PreResetState cfg model U gVec lVec).chain.G d).E
  { tok with
    offReadyCount := offCnt
    tree := curTree, trees := curTrees, free := curFree, depth := curDepth
    treeTok := curTreeTok
    coreHandle := fun j => outMem (handleBase + j), coreTok := tokN
    termHandle := outMem (handleBase + d), vcLast := vcL, ecLast := ecL, termTok := termTokN
    owned := fun a =>
      if a < uIntBuf then tok.owned a
      else if heap + 1 + 12 * d ≤ a ∧ a < heap2 then True
      else if BranchBSelZone heap2 hS hT hX a then
        ∃ j < d, Rcore.foot (outMem (handleBase + j)) (tokN j) a
      else if hS ≤ a ∧ a < hT then True
      else if hX ≤ a ∧ a < nextHeap then True
      else False
    tag := fun a =>
      if a < uIntBuf then tok.tag a
      else if heap + 1 + 12 * d ≤ a ∧ a < heap2 then
        if Rtree.foot tok.treeHeap curTreeTok a then 16
        else if ∃ e ∈ model.extG.E,
            outMem (tok.edgeThresholds + tr.2.1 e) ≤ a ∧
            a < outMem (tok.edgeThresholds + tr.2.1 e) + L then 17
        else 18
      else if BranchBSelZone heap2 hS hT hX a then
        if h : ∃ j : Fin d, Rcore.foot (outMem (handleBase + j.val)) (tokN j.val) a then
          21 + (Classical.choose h).val
        else 0
      else if hS ≤ a ∧ a < hT then
        if Rterm.foot (outMem (handleBase + d)) termTokN a then 19
        else if h : ∃ j : Fin d, Rcore.foot (outMem (handleBase + j.val)) (tokN j.val) a then
          21 + (Classical.choose h).val
        else 23 + d
      else if hX ≤ a ∧ a < nextHeap then
        if Rtree.foot tok.treeHeap curTreeTok a then 16 else 18
      else 0 }

/-! ### Model identities for `alg2PreResetState` -/

/-- A refresh batch leaves `modelPre.extG` equal to `model.extG`. -/
theorem branchB_modelPre_extG {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {U : List Update} {gVec lVec : ℕ → ℝ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hRef : RefreshBatch model.extG U) :
    (alg2PreResetState cfg model U gVec lVec).extG = model.extG := by
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := hRep0
  exact (refreshBatch_edge_dichotomy hFreshInv0 hRef).1

/-- After `alg2PreResetState`, `FreshInv` holds on the new level-`0` graph and name maps. -/
theorem branchB_modelPre_freshInv {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {U : List Update} {gVec lVec : ℕ → ℝ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hRef : RefreshBatch model.extG U) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt modelPre.intToExt
      modelPre.nextFresh := by
  intro modelPre
  have hFreshInv0 := hRep0.2.2.2.2.1
  obtain ⟨_, hFreshTr, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 hRef
  have hUp := Chain.Ordered.update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    gVec lVec hFreshTr
  rw [branchB_modelPre_extG hRep0 hRef]
  exact hUp.1

private theorem updateLoop_preserves_n0_lvlM {cfg : Alg2Config} (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ), idx + rem = cfg.P.d →
      let ch' := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N₀ ℓ' g' rem idx ch curG
        curU curEnc).1
      ch'.N₀ = ch.N₀ ∧ ch'.lvlM = ch.lvlM := by
  intro rem
  induction rem with
  | zero =>
    intro idx ch curG curU curEnc _
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs <;> exact ⟨rfl, rfl⟩
  | succ rem ih =>
    intro idx ch curG curU curEnc hSum
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs
    · have hEx := ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P
        { ch with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
        (show idx < cfg.P.d by omega) (rebuildStartGraph idx curG) curEnc
      exact ⟨hEx.2.2.2.2.2.2.2.2.2.1, hEx.2.2.2.2.2.2.2.2.1⟩
    · exact ih (idx + 1) _ _ _ _ (by omega)

/-- `alg2PreResetState` preserves `chain.N₀` and `chain.lvlM`. -/
theorem branchB_modelPre_n0_lvlM {cfg : Alg2Config} (model : Alg2State cfg) (U : List Update)
    (gVec lVec : ℕ → ℝ) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    modelPre.chain.N₀ = model.chain.N₀ ∧ modelPre.chain.lvlM = model.chain.lvlM :=
  updateLoop_preserves_n0_lvlM cfg.N₀ _ _ cfg.P.d 0 _ _ _ _ (by omega)

/-! ### Helper: old nonzero tags lie below `uIntBuf` -/

private theorem oldTagLt {L P m V psi k epsExp drainUnit : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root uIntBuf : ℕ} {mem0 : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf :=
  hFootLt a (Or.inl (hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a h))

/-! ### Footprint growth and select output -/

/-- The footprint of `wireBranchBTokNew` lies in the old footprint or in `[heap, nextHeap)`. -/
theorem branchB_foot_growth
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
      out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
    ∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap) := by
  intro Rrep tok' a ha
  obtain ⟨hUHeap, hSlot2, h2S, hST, hTX, hXN, _⟩ := S.heaps
  have hOwnOfTag := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases ha with hOwn | hTree | ⟨j, hj, hCore⟩
  · dsimp only [tok', wireBranchBTokNew] at hOwn
    split_ifs at hOwn with h1 h2 h3 h4 h5
    · exact Or.inl (Or.inl hOwn)
    · exact Or.inr ⟨by omega, by omega⟩
    · rcases h3 with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · rcases S.treeFoot a hTree with h0 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inl (Or.inr (Or.inl h0))
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · obtain ⟨hLt, hGe⟩ := S.coreFoot j hj a hCore
    by_cases hlt : a < heap
    · exact Or.inl (Or.inl (hOwnOfTag a (by rw [hLt hlt]; omega)))
    · obtain ⟨hlo, hhi⟩ := hGe (Nat.le_of_not_lt hlt)
      exact Or.inr ⟨by omega, by omega⟩

private theorem selOutWordsAt_mono_hi {foot : ℕ → Prop} {lo hi hi' a n : ℕ}
    (h : SelOutWordsAt foot lo hi a n) (hle : hi ≤ hi') :
    SelOutWordsAt foot lo hi' a n :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

private theorem selOutTableAt_mono_hi {w lo hi hi' a Lw : ℕ} {foot : ℕ → Prop} {mem : ℕ → ℕ}
    {E : Finset ℕ} (h : SelOutTableAt w foot lo hi mem a Lw E) (hle : hi ≤ hi') :
    SelOutTableAt w foot lo hi' mem a Lw E :=
  ⟨h.1, fun e he => ⟨le_trans (h.2 e he).1 hle, fun t ht =>
    (h.2 e he).2 t ht |>.imp id fun ⟨h1, h2⟩ => ⟨h1, lt_of_lt_of_le h2 hle⟩⟩⟩

/-- `UpdateCoreSelectOutAt` holds at `heap` after Branch B for `wireBranchBTokNew`. -/
theorem branchB_selectOut
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
      out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
    UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn (Rrep.foot root tok') out.mem heap
      nextHeap fr model.chain modelPre.chain levelU levelUS D := by
  intro Rrep modelPre tok'
  obtain ⟨hUHeap, hSlot2, h2S, hST, hTX, hXN, _⟩ := S.heaps
  have hNotTree_mid : ∀ a, heap ≤ a → a < heap + 1 + 12 * cfg.P.d →
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a := by
    intro a h1 h2 hT'
    rcases S.treeFoot a hT' with h0 | ⟨hlo, _⟩ | ⟨hlo, _⟩
    · have := hFootLt a (Or.inr (Or.inl h0)); omega
    · omega
    · omega
  have hNotTree_zone : ∀ a, BranchBSelZone heap2 hS hT hX a →
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a := by
    intro a hz hT'
    rcases S.treeFoot a hT' with h0 | ⟨_, hhi⟩ | ⟨hlo, _⟩
    · have := hFootLt a (Or.inr (Or.inl h0))
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hSlotOff : ∀ t < 1 + 12 * min fr cfg.P.d, ¬ Rrep.foot root tok' (heap + t) := by
    intro t ht hF
    have hmin : min fr cfg.P.d ≤ cfg.P.d := Nat.min_le_right _ _
    rcases hF with hOwn | hTree | ⟨j, hj, hCore⟩
    · dsimp only [tok', wireBranchBTokNew] at hOwn
      split_ifs at hOwn with h1 h2 h3 h4 h5
      · omega
      · omega
      · rcases h3 with ⟨hlo, _⟩ | ⟨hlo, _⟩ <;> omega
      · omega
      · omega
    · exact hNotTree_mid (heap + t) (by omega) (by omega) hTree
    · have hGe := (S.coreFoot j hj (heap + t) hCore).2 (by omega)
      omega
  refine ⟨S.sel, ⟨le_rfl, by have := Nat.min_le_right fr cfg.P.d; omega, hSlotOff⟩, fun j hj => ?_⟩
  have hF_zone : ∀ a, BranchBSelZone heap2 hS hT hX a →
      (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + r)) (tokN r) a) →
      ¬ Rrep.foot root tok' a := by
    intro a hz hNoCore hF
    rcases hF with hOwn | hTree | ⟨r, hr, hCore⟩
    · dsimp only [tok', wireBranchBTokNew] at hOwn
      have hNotU : ¬ a < uIntBuf := by rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      have hNot1 : ¬ (heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2) := by
        rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      rw [ite_eq_right hNotU, ite_eq_right hNot1, ite_eq_left hz] at hOwn
      obtain ⟨r, hr, hCore⟩ := hOwn
      exact hNoCore r hr hCore
    · exact hNotTree_zone a hz hTree
    · exact hNoCore r hr hCore
  obtain ⟨hDiff, hW0, hW2, hW4, hW6, hBat, hBatW, hWBat, hWDesc, hLw, hSV, hT0, hT1⟩ :=
    branchBSufSlots_level (S.slots j hj) (by omega : heap ≤ heap2) hF_zone
      (fun a ha => Or.inr (Or.inr ⟨j, lt_of_lt_of_le hj (Nat.min_le_right _ _), ha⟩))
  obtain ⟨hUG, hUS, hFDelNd, hFDelFin, hReemb, hCaps⟩ := S.slotModel j hj
  exact ⟨hDiff, hUG, hFDelNd, hFDelFin, hUS, hReemb,
    selOutWordsAt_mono_hi hW0 hXN, selOutWordsAt_mono_hi hW2 hXN,
    selOutWordsAt_mono_hi hW4 hXN, selOutWordsAt_mono_hi hW6 hXN,
    hBat, hCaps, hBatW, selOutWordsAt_mono_hi hWBat hXN,
    selOutWordsAt_mono_hi hWDesc hXN, hLw, hSV,
    selOutTableAt_mono_hi hT0 hXN, selOutTableAt_mono_hi hT1 hXN⟩

/-! ### Tags and level metadata -/

set_option maxHeartbeats 800000 in
/-- `SolverTagsAt` holds for `wireBranchBTokNew` at `out.mem`. -/
theorem branchB_tagsNew
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
      out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
    SolverTagsAt root m modelPre tok' out.mem := by
  intro modelPre tok'
  classical
  have hRep0_keep := hRep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hTreeN0, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hT13,
    hT14, hT15, hT16, _, _, hT20, _⟩ := hTags0
  obtain ⟨hUHeap, hSlot2, h2S, hST, hTX, hXN, _⟩ := S.heaps
  have hPreExtG : modelPre.extG = model.extG := branchB_modelPre_extG hRep0_keep hRef
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := branchB_modelPre_freshInv hRep0_keep hRef
  have hTreeN : tok'.tree.n = tok.tree.n := by
    change curTree.n = tok.tree.n
    rw [S.phase.treeN, MGraph.n, ← hFreshPre.hV, hPreExtG, ← MGraph.n, hTreeN0]
  have hTagKeep : ∀ {a v : ℕ}, tok.tag a = v → v ≠ 0 → tok'.tag a = v := fun {a v} ht hne => by
    have hlt := oldTagLt hRep0_keep hFootLt (ht ▸ hne)
    dsimp only [tok', wireBranchBTokNew]
    rw [ite_eq_left hlt, ht]
  let d := cfg.P.d
  let Rterm' := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P (modelPre.chain.G d).E
  refine ⟨fun a hne => ?_,
    fun j hj => hTagKeep (hT1 j hj) (by decide),
    fun j hj => hTagKeep (hT2 j hj) (by decide),
    fun j hj => hTagKeep (hT3 j hj) (by decide),
    fun j hj => hTagKeep (hT4 j hj) (by decide),
    fun j hj => hTagKeep (hT5 j hj) (by decide),
    hTagKeep hT6 (by decide),
    fun j hj => hTagKeep (hT7 j hj) (by decide),
    fun j hj => hTagKeep (hT8 j hj) (by decide),
    fun j hj => hTagKeep (hT9 j hj) (by decide),
    fun j hj => hTagKeep (hT10 j (by omega)) (by decide),
    fun j hj => hTagKeep (hT11 j (by omega)) (by decide),
    fun j hj => hTagKeep (hT12 j hj) (by decide),
    fun j hj => hTagKeep (hT13 j hj) (by decide),
    fun j hj => hTagKeep (hT14 j hj) (by decide),
    fun j hj => hTagKeep (hT15 j hj) (by decide),
    fun a ha => ?_, fun e he => ?_, fun a ha => ?_, fun a ha1 ha2 => ?_, fun i hi a ha => ?_⟩
  · -- a word with a nonzero tag is owned
    dsimp only [tok', wireBranchBTokNew] at hne ⊢
    by_cases hU : a < uIntBuf
    · rw [ite_eq_left hU] at hne ⊢; exact hOwnOfTag a hne
    · rw [ite_eq_right hU] at hne ⊢
      by_cases h1 : heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2
      · rw [ite_eq_left h1]; trivial
      · rw [ite_eq_right h1] at hne ⊢
        by_cases h2 : BranchBSelZone heap2 hS hT hX a
        · rw [ite_eq_left h2] at hne ⊢
          by_cases hC : ∃ j : Fin cfg.P.d,
              Rcore.foot (out.mem (tok.handle + 18 + j.val)) (tokN j.val) a
          · obtain ⟨j, hj⟩ := hC; exact ⟨j.val, j.isLt, hj⟩
          · rw [dite_eq_right hC] at hne; exact (hne rfl).elim
        · rw [ite_eq_right h2] at hne ⊢
          by_cases h3 : hS ≤ a ∧ a < hT
          · rw [ite_eq_left h3]; trivial
          · rw [ite_eq_right h3] at hne ⊢
            by_cases h4 : hX ≤ a ∧ a < nextHeap
            · rw [ite_eq_left h4]; trivial
            · rw [ite_eq_right h4] at hne ⊢; exact (hne rfl).elim
  · -- tag 16: the foot of the path tree
    rcases S.treeFoot a ha with h0 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact hTagKeep (hT16 a h0) (by decide)
    · dsimp only [tok', wireBranchBTokNew]
      rw [ite_eq_right (by omega), ite_eq_left ⟨hlo, hhi⟩, ite_eq_left ha]
    · have hNotZ : ¬ BranchBSelZone heap2 hS hT hX a := by
        rintro (⟨_, h2⟩ | ⟨_, h2⟩) <;> omega
      dsimp only [tok', wireBranchBTokNew]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hNotZ,
        ite_eq_right (by omega), ite_eq_left ⟨hlo, hhi⟩, ite_eq_left ha]
  · -- tags 17 & 18: thresholds and off-tree edge records
    have he0 : e ∈ model.extG.E := hPreExtG ▸ he
    have hE2I : modelPre.extToInt =
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 :=
      S.names.1
    refine ⟨fun j hj => ?_, fun hnot j hj => ?_⟩
    · rw [hE2I]
      obtain ⟨hLt, hGe, hNotTr⟩ := S.thrLoc e he0 j hj
      by_cases hU : out.mem (tok.edgeThresholds +
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 e) + j <
          uIntBuf
      · exact hTagKeep (hLt hU) (by decide)
      · obtain ⟨hlo, hhi⟩ := hGe (Nat.le_of_not_lt hU)
        dsimp only [tok', wireBranchBTokNew]
        rw [ite_eq_right hU, ite_eq_left ⟨hlo, hhi⟩, ite_eq_right hNotTr,
          ite_eq_left ⟨e, he0, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩]
    · have hei : modelPre.extToInt e ∈ (modelPre.chain.G 0).E :=
        hFreshPre.hE ▸ Finset.mem_image_of_mem modelPre.extToInt he
      obtain ⟨hLt, hNotTr, _, _⟩ := S.phase.recLoc _ hei hnot j hj
      by_cases hU : out.mem (tok.edgeRecords + modelPre.extToInt e) + j < uIntBuf
      · exact hTagKeep (hLt hU) (by decide)
      · rcases S.recLoc _ hei hnot j hj (Nat.le_of_not_lt hU) with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
        · have hNot17 : ¬ ∃ e₁ ∈ model.extG.E,
              out.mem (tok.edgeThresholds +
                (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1
                  e₁) ≤ out.mem (tok.edgeRecords + modelPre.extToInt e) + j ∧
              out.mem (tok.edgeRecords + modelPre.extToInt e) + j <
                out.mem (tok.edgeThresholds +
                  (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1
                    e₁) + L := by
            rintro ⟨e₁, he1, h1, h2⟩
            have hD := S.thrRecDisj e₁ he1 e he0 (hE2I ▸ hnot)
            rw [hE2I] at h1 h2
            rcases hD with hd1 | hd2 <;> omega
          dsimp only [tok', wireBranchBTokNew]
          rw [ite_eq_right hU, ite_eq_left ⟨hlo, hhi⟩, ite_eq_right hNotTr, ite_eq_right hNot17]
        · have hNotZ : ¬ BranchBSelZone heap2 hS hT hX
              (out.mem (tok.edgeRecords + modelPre.extToInt e) + j) := by
            rintro (⟨_, h2⟩ | ⟨_, h2⟩) <;> omega
          dsimp only [tok', wireBranchBTokNew]
          rw [ite_eq_right hU, ite_eq_right (by omega), ite_eq_right hNotZ,
            ite_eq_right (by omega), ite_eq_left ⟨hlo, hhi⟩, ite_eq_right hNotTr]
  · -- tag 19: the foot of the last level
    have haP : Rterm'.foot (out.mem (tok.handle + 18 + d)) termTokN a :=
      (lastLevelRepresentation_foot_indep_P vcL ecL 4 L P 0 (modelPre.chain.G d).E _ _ a).mpr ha
    obtain ⟨hLt, hGe, _⟩ := S.lastFoot a haP
    by_cases hH : a < heap
    · exact hTagKeep (hLt hH) (by decide)
    · obtain ⟨hlo, hhi⟩ := hGe (Nat.le_of_not_lt hH)
      have hNotZ : ¬ BranchBSelZone heap2 hS hT hX a := by
        rintro (⟨_, h2⟩ | ⟨h1, _⟩) <;> omega
      dsimp only [tok', wireBranchBTokNew]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hNotZ,
        ite_eq_left ⟨hlo, hhi⟩, ite_eq_left haP]
  · -- tag 20: the root graph (kept in place in Branch B)
    rw [hPreExtG] at ha2
    exact hTagKeep (hT20 a ha1 ha2) (by decide)
  · -- tag 21 + i: the foot of core i
    obtain ⟨hLt, hGe⟩ := S.coreFoot i hi a ha
    by_cases hH : a < heap
    · exact hTagKeep (hLt hH) (by omega)
    · obtain ⟨hlo, hhi⟩ := hGe (Nat.le_of_not_lt hH)
      have hex : ∃ j : Fin d, Rcore.foot (out.mem (tok.handle + 18 + j.val)) (tokN j.val) a :=
        ⟨⟨i, hi⟩, ha⟩
      have hChoose : (Classical.choose hex).val = i := by
        by_contra hne
        exact S.coreDisj _ (Classical.choose hex).isLt i hi hne a (Classical.choose_spec hex) ha
      by_cases hZ : BranchBSelZone heap2 hS hT hX a
      · dsimp only [tok', wireBranchBTokNew]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hZ,
          dite_eq_left hex, hChoose]
      · have hSTa : hS ≤ a ∧ a < hT := by
          unfold BranchBSelZone at hZ; push Not at hZ; omega
        have hNotRm : ¬ Rterm'.foot (out.mem (tok.handle + 18 + d)) termTokN a := fun hr =>
          (S.lastFoot a hr).2.2 i hi ha
        dsimp only [tok', wireBranchBTokNew]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hZ,
          ite_eq_left hSTa, ite_eq_right hNotRm, dite_eq_left hex, hChoose]

set_option maxHeartbeats 600000 in
/-- `SolverLevelMetaAt` holds for `wireBranchBTokNew` at `out.mem`. -/
theorem branchB_levelMetaNew
    {w L P m V psi k epsExp drainUnit capExp wordExp stretchPrec vCap eCap : ℕ}
    {cfg : Alg2Config} {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul root uIntBuf heap g l : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {gVec lVec : ℕ → ℝ} {B R : ℤ} {heap2 hS hT hX fr : ℕ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {tokN : ℕ → Rcore.τ} {vcL ecL termTokN : ℕ}
    {curTree : PathTreeState} {curTrees : List AuxTree} {curFree : List ℕ} {curDepth : ℕ → ℕ}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt : ℕ}
    {canonVal : ℕ → PathEdgeValue} {out : State} {nextHeap cost : ℕ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hExtM : model.extG.m = m)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (S : BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let tok' := wireBranchBTokNew P uIntBuf heap heap2 hS hT hX nextHeap vcL ecL termTokN offCnt
      out.mem model tok U gVec lVec tokN curTree curTrees curFree curDepth curTreeTok
    SolverLevelMetaAt P V modelPre tok' out.mem := by
  intro modelPre tok'
  have hMeta0_keep := hMeta0
  obtain ⟨⟨hN0Mem0, hTagN0_0, hTagSH_0, hTagSB_0⟩, hCoreOwn0, hLvlM0, hTagLvlM0, hTagMeta0, _⟩ :=
    hMeta0
  obtain ⟨hUHeap, hSlot2, h2S, hST, hTX, hXN, _⟩ := S.heaps
  obtain ⟨hN0Pre, hLvlMPre⟩ := branchB_modelPre_n0_lvlM model U gVec lVec
  have hCores0 := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTagKeep : ∀ {a v : ℕ}, tok.tag a = v → v ≠ 0 → tok'.tag a = v := fun {a v} ht hne => by
    have hlt := oldTagLt hRep0 hFootLt (ht ▸ hne)
    dsimp only [tok', wireBranchBTokNew]
    rw [ite_eq_left hlt, ht]
  have hOwnOld : ∀ {a : ℕ}, tok.owned a → tok'.owned a := fun {a} ho => by
    have hlt : a < uIntBuf := hFootLt a (Or.inl ho)
    dsimp only [tok', wireBranchBTokNew]
    rw [ite_eq_left hlt]; exact ho
  have hOwnST : ∀ {a : ℕ}, hS ≤ a → a < hT → tok'.owned a := fun {a} h1 h2 => by
    have hNotZ : ¬ BranchBSelZone heap2 hS hT hX a := by
      rintro (⟨_, h'⟩ | ⟨h', _⟩) <;> omega
    dsimp only [tok', wireBranchBTokNew]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hNotZ,
      ite_eq_left ⟨h1, h2⟩]
    trivial
  -- `0 < eCap * L` so every new length block `[lp, lp + eCap * L)` has `lp < hT`.
  have hECapLPos : 0 < eCap * L := by
    have hmPos : 0 < m := hModelInv.1.2
    have hLPos : 0 < L := by
      have h4L : P - epsExp + 1 < 4 * L := hModelInv.2.2.2.2.2.1.2.2.1
      omega
    have hFresh0 := hRep0.2.2.2.2.1
    have hNE : model.extG.E.Nonempty :=
      Finset.card_pos.mp (by rw [← MGraph.m, hExtM]; exact hmPos)
    obtain ⟨e, he⟩ := hNE
    have hei : model.extToInt e ∈ (model.chain.G 0).E :=
      hFresh0.hE ▸ Finset.mem_image_of_mem model.extToInt he
    have hECapPos : 0 < eCap := Nat.lt_of_le_of_lt (Nat.zero_le _) ((hCaps0 0 S.dPos).2.2.1 _ hei)
    exact Nat.mul_pos hECapPos hLPos
  refine ⟨⟨S.metaCells.1.trans (hN0Mem0.trans hN0Pre.symm),
      hTagKeep hTagN0_0 (by omega),
      hTagKeep hTagSH_0 (by omega),
      hTagKeep hTagSB_0 (by omega)⟩,
    fun j hj => by
      change tok'.owned (out.mem (tok.handle + 18 + j))
      rcases S.coreHandleLoc j hj with hEq | ⟨h1, h2⟩
      · rw [hEq, (hCores0 j hj).1]
        exact hOwnOld (hCoreOwn0 j hj)
      · exact hOwnST h1 h2,
    fun j hj => (S.metaCells.2.1 j hj).trans ((hLvlM0 j hj).trans (congrFun hLvlMPre.symm j)),
    fun j hj => hTagKeep (hTagLvlM0 j hj) (by omega),
    fun j hj => hTagKeep (hTagMeta0 j hj) (by omega),
    fun j hj => ⟨vCap, eCap, S.graphs j hj, S.lens j hj, ?_, ?_, ?_⟩⟩
  · -- `tok'.owned (out.mem (levelMeta + j))`
    change tok'.owned (out.mem (solverLevelMetaAddr tok.table cfg.P.d + j))
    by_cases hlt : j < fr + 1
    · have hmin : j < min (fr + 1) cfg.P.d := Nat.lt_min.mpr ⟨hlt, hj⟩
      rw [(S.metaKeep j hmin).2]
      exact hOwnOld (hMeta0_keep.atCaps hCaps0 j hj).2.2.1
    · obtain ⟨_, _, hlpLo, hlpHi, _⟩ := S.metaNew j (Nat.le_of_not_lt hlt) hj
      exact hOwnST hlpLo (by omega)
  · -- tag `23 + d` on the length block
    intro a ha1 ha2
    change out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) ≤ a at ha1
    change a < out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L at ha2
    by_cases hlt : j < fr + 1
    · have hmin : j < min (fr + 1) cfg.P.d := Nat.lt_min.mpr ⟨hlt, hj⟩
      rw [(S.metaKeep j hmin).2] at ha1 ha2
      exact hTagKeep ((hMeta0_keep.atCaps hCaps0 j hj).2.2.2.1 a ha1 ha2) (by omega)
    · obtain ⟨_, _, hlpLo, hlpHi, hDisj⟩ := S.metaNew j (Nat.le_of_not_lt hlt) hj
      obtain ⟨hNoC, hNoL⟩ := hDisj a (Or.inr ⟨ha1, ha2⟩)
      have hNotZ : ¬ BranchBSelZone heap2 hS hT hX a := by
        rintro (⟨_, h'⟩ | ⟨h', _⟩) <;> omega
      dsimp only [tok', wireBranchBTokNew]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hNotZ,
        ite_eq_left ⟨by omega, by omega⟩, ite_eq_right hNoL,
        dite_eq_right (fun ⟨r, hr⟩ => hNoC r.val r.isLt hr)]
  · -- tag `if j = 0 then 20 else 23 + d` on the graph block
    intro a ha1 ha2
    change out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ≤ a at ha1
    change a < out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) +
      dynGraphSize vCap eCap at ha2
    by_cases hlt : j < fr + 1
    · have hmin : j < min (fr + 1) cfg.P.d := Nat.lt_min.mpr ⟨hlt, hj⟩
      rw [(S.metaKeep j hmin).1] at ha1 ha2
      exact hTagKeep ((hMeta0_keep.atCaps hCaps0 j hj).2.2.2.2 a ha1 ha2) (by split_ifs <;> omega)
    · have hjNe0 : j ≠ 0 := by omega
      simp only [hjNe0, ↓reduceIte]
      obtain ⟨hgpLo, hgpHi, _, _, hDisj⟩ := S.metaNew j (Nat.le_of_not_lt hlt) hj
      obtain ⟨hNoC, hNoL⟩ := hDisj a (Or.inl ⟨ha1, ha2⟩)
      have hNotZ : ¬ BranchBSelZone heap2 hS hT hX a := by
        rintro (⟨_, h'⟩ | ⟨h', _⟩) <;> omega
      dsimp only [tok', wireBranchBTokNew]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hNotZ,
        ite_eq_left ⟨by omega, by omega⟩, ite_eq_right hNoL,
        dite_eq_right (fun ⟨r, hr⟩ => hNoC r.val r.isLt hr)]

end MinCostFlow.MinRatio
