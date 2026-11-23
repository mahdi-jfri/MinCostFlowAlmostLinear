module

public import MinCostFlow.MinRatio.WireChainCoreBranchASync2KFBL
import MinCostFlow.Chain.Ordered.RenameFacts
import WordRAM.Tactic

/-!
# Branch A Step 5b: the facts it starts from (`WireChainCoreBranchATokHypKFBL`)

Step 5b of Branch A runs `wireBranchAReadyRetStmt` from the state `s5g` that the second tree
sync leaves, and then builds the new solver token. This file puts what Step 5b knows into one
structure, `WireBranchATokHypKFBL`: facts on the state `s4` after the rebuild of the chain
(Steps 0–4), and facts on the state `s5g`. The later files take this structure, so that their
statements stay short.

The file also proves the helper facts that the later files share:
* which words of `s4` and `s5g` still hold their old values (`s4_tag`, `s5g_eq4_tag`, …);
* the same for the memory after the off-ready rebuild, which changes only the count word and
  the two off-ready arrays (`k_eq4_tag`, …);
* the identities of the model after the reset (`preE2I`, `preG0`, `freshPre`, …);
* where the edge records of the new level 0 lie (`recLoc`), and the threshold and record words
  after the off-ready rebuild (`thrK`, `recOffK`).

The run of Step 5b is in `WireChainCoreBranchATokRunKFBL.lean`, the new token and its tags in
`WireChainCoreBranchATokTagKFBL.lean`, and the post in `WireChainCoreBranchATokKFBL.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The facts that Branch A Step 5b starts from: the state `s4` after the rebuild of the chain
(Steps 0–4), and the state `s5g` after the second tree sync (`wireBranchASync2LoopKFBL_runs`).
The facts on the program itself are separate hypotheses of the run lemma. -/
structure WireBranchATokHypKFBL
    (w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap heap1 heapSync heap2 newLen0
      newRootGraph heap3 heap4 nextHeap termTok4 : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (mem0 mem : ℕ → ℕ)
    (s4 s5g : State) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update)
    (B R : ℤ) (gVec lVec : ℕ → ℝ) (curTree2 : PathTreeState) (curTrees2 : List AuxTree)
    (curFree2 : List ℕ) (curDepth2 : ℕ → ℕ)
    (curTreeTok1 curTreeTok2 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (newCanonVal : ℕ → PathEdgeValue) (coreTok4 : ℕ → Rcore.τ) : Prop where
  coreLocal : Rcore.Local
  lpos : 0 < L
  dPos : 0 < cfg.P.d
  w18 : 18 < 2 ^ w
  vCapEq : vCap = model.extG.n
  eCapEq : eCap = tok.rootECap
  rep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0
  meta0 : SolverLevelMetaAt P V model tok mem0
  ref : RefreshBatch model.extG U
  chPreEq :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    let stLG : ChainState cfg.T cfg.P :=
      { st0 with
        ℓ := fun j => lVec (tr.2.2.1 (compactUnrank G0'.E j))
        g := fun j => gVec (tr.2.2.1 (compactUnrank G0'.E j)) }
    (alg2PreResetState cfg model U gVec lVec).chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 G0'.compact
        (G0.batchEnc U_int)).1
  renTrue :
    Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount
      (alg2PreResetState cfg model U gVec lVec).chain.rebuildCount = true
  newForest : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.IsForest
  newSub : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E ⊆
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E
  g0'mLeR :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.rootECap ∧
    ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.intCap
  i2eGe :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ j ≥ tok.intCap, tr.2.2.1 j = j
  footLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
    a < uIntBuf
  uLeHeap : uIntBuf ≤ heap
  heaps :
    heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ heap1 ∧
    heap1 ≤ heapSync ∧ heapSync + 3 * L ≤ heap2 ∧
    heap2 ≤ newLen0 ∧ newLen0 + eCap * L ≤ newRootGraph ∧
    newRootGraph + dynGraphSize vCap eCap ≤ heap3 ∧ heap3 ≤ heap4 ∧ heap4 ≤ nextHeap ∧
    nextHeap + 1 < 2 ^ w
  -- facts on `s4`
  heap0_4 : s4.mem heap = 0
  fresh4 :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    FreshTablesAt s4.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      (level0E2I true G0' tr.2.1) (level0I2E true G0' tr.2.2.1) (level0NF true G0' tr.2.2.2.1)
  r14_4 : s4.mem (root + 14) = newRootGraph
  lm0_4 : s4.mem (solverLevelMetaAddr tok.table cfg.P.d) = newLen0
  lmd_4 : s4.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d) = newRootGraph
  rg4 : DynGraphAt s4.mem newRootGraph vCap eCap
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0)
  len4 : EdgeValuesAt s4.mem newLen0 4 L P
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E
    ((alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainLen
      (alg2PreResetState cfg model U gVec lVec).chain.ℓ 0)
  treeFoot1 : ∀ a,
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
      (heap1 ≤ a ∧ a < heapSync)
  canon4 :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch tr.2.2.2.2
    ∀ e ∈ model.extG.E,
      let eiOld := tr.2.1 e
      let eiNew := level0E2I true G0' tr.2.1 e
      let v := newCanonVal eiOld
      eiNew < G0'.m ∧ compactUnrank G0'.E eiNew = eiOld ∧
      PathIntAt s4.mem (s4.mem (tok.edgeThresholds + eiNew)) 4 L
        (detectorThreshold P cfg.ε (lVec e)) ∧
      PathEdgeAt s4.mem (s4.mem (tok.edgeRecords + eiNew)) 4 L (some v) ∧
      v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
      (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
      (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
      (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
      (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
      (eiOld ∈ G0.E →
        s4.mem (tok.edgeThresholds + eiNew) = mem0 (tok.edgeThresholds + eiOld) ∧
        ((eiOld ∈ model.chain.toTreeChain.chainTree.E →
            heap1 ≤ s4.mem (tok.edgeRecords + eiNew) ∧
            s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync ∧
            ∀ a, s4.mem (tok.edgeRecords + eiNew) ≤ a →
              a < s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
              ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
                curTreeTok1 a) ∧
         (eiOld ∉ model.chain.toTreeChain.chainTree.E →
            s4.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + eiOld)))) ∧
      (eiOld ∉ G0.E →
        heapSync + 3 * L ≤ s4.mem (tok.edgeThresholds + eiNew) ∧
        s4.mem (tok.edgeThresholds + eiNew) + L ≤ heap2 ∧
        heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + eiNew) ∧
        s4.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2)
  thrOffDisj4 :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch tr.2.2.2.2
    ∀ e₁ ∈ model.extG.E, tr.2.1 e₁ ∉ G0.E → ∀ e₂ ∈ model.extG.E, tr.2.1 e₂ ∉ G0.E →
      s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L ≤
        s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
      s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
        s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁)
  cores4 :
    let d := cfg.P.d
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ j < d,
      s4.mem (branchBase + j) = modelPre.chain.bran j ∧
      heap3 ≤ s4.mem (handleBase + j) ∧ s4.mem (handleBase + j) ≤ heap4 ∧
      Rcore.rep (s4.mem (handleBase + j)) (chainLevelOrdAbs modelPre.chain j) (coreTok4 j)
        s4.mem ∧
      (∀ a, Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a → heap3 ≤ a ∧ a < heap4)
  coreDisj4 :
    let handleBase := tok.handle + 18
    ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
      ∀ a, Rcore.foot (s4.mem (handleBase + j₁)) (coreTok4 j₁) a →
        ¬ Rcore.foot (s4.mem (handleBase + j₂)) (coreTok4 j₂) a
  meta4 :
    let d := cfg.P.d
    let handleBase := tok.handle + 18
    let levelMeta := solverLevelMetaAddr tok.table d
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let Rterm := LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (modelPre.chain.G d).E
    ∀ j, 1 ≤ j → j < d →
      DynGraphAt s4.mem (s4.mem (levelMeta + d + j)) vCap eCap (modelPre.chain.G j) ∧
      heap3 ≤ s4.mem (levelMeta + d + j) ∧
      s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ heap4 ∧
      EdgeValuesAt s4.mem (s4.mem (levelMeta + j)) 4 L P (modelPre.chain.G j).E
        (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ j) ∧
      heap3 ≤ s4.mem (levelMeta + j) ∧
      s4.mem (levelMeta + j) + eCap * L ≤ heap4 ∧
      (∀ r < d,
        (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
          ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a) ∧
        (∀ a, s4.mem (levelMeta + d + j) ≤ a →
          a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a)) ∧
      (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
        ¬ Rterm.foot (s4.mem (handleBase + d)) termTok4 a) ∧
      (∀ a, s4.mem (levelMeta + d + j) ≤ a →
        a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
        ¬ Rterm.foot (s4.mem (handleBase + d)) termTok4 a)
  termB4 : s4.mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) =
    (alg2PreResetState cfg model U gVec lVec).chain.lastBran
  termRep4 :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
        (modelPre.chain.G cfg.P.d).E).rep
      (s4.mem (tok.handle + 18 + cfg.P.d)) (modelPre.chain.lastK, modelPre.chain.lastLSFs)
      termTok4 s4.mem
  termFoot4 :
    let handleBase := tok.handle + 18
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
          (modelPre.chain.G cfg.P.d).E).foot (s4.mem (handleBase + cfg.P.d)) termTok4 a →
      heap3 ≤ a ∧ a < heap4 ∧ ∀ j < cfg.P.d, ¬ Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a
  rc4 : s4.mem (tok.levelsEnd + 2 * (cfg.P.d + 1)) = model.chain.rebuildCount 0 + 1
  uc4 : ∀ j < cfg.P.d, s4.mem (tok.levelsEnd + 3 * (cfg.P.d + 1) + j) = 0
  frame4 : ∀ a < heap,
    ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → s4.mem a = mem a
  frame4_0 :
    let d := cfg.P.d
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let rebuildCountBase := tok.levelsEnd + 2 * (d + 1)
    let updCountBase := tok.levelsEnd + 3 * (d + 1)
    ∀ a < uIntBuf, a ≠ root + 11 → a ≠ root + 14 → a ≠ rebuildCountBase →
      (a < handleBase ∨ handleBase + d < a) →
      (a < branchBase ∨ branchBase + d < a) →
      (a < updCountBase ∨ updCountBase + d ≤ a) →
      tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 12 → tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
      tok.tag a ≠ 16 → tok.tag a ≠ 20 →
      tok.tag a ≠ 22 + d → tok.tag a ≠ 23 + d →
      (∀ j < d, tok.tag a ≠ 21 + j) → s4.mem a = mem0 a
  -- facts on `s5g`, from `wireBranchASync2LoopKFBL_runs`
  r3_5g : s5g.regs 3 = nextHeap
  r70_5g : s5g.regs 70 = root
  z5g : ZeroFrom s5g.mem nextHeap
  treeN2 : curTree2.n = model.extG.n
  lctEnd : LctInvWith pathPayload curTree2 curTrees2 curFree2 curDepth2
  numEnd : PathTreeNumericInv curTree2 curTrees2 B R
  namedEnd : TreeEditNamedSlots curTree2 curTrees2
    (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree
    (fun ei => s5g.mem (tok.slots + ei)) (fun sl => s5g.mem (tok.names + sl))
  liveEnd :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    TreeEditLiveAccounts curTree2 curTrees2
      (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree
      (fun ei => s5g.mem (tok.slots + ei)) (fun j => newCanonVal (compactUnrank G0'.E j))
  treeRepEnd : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree2
    curTreeTok2 s5g.mem
  footEnd : ∀ a,
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok2 a →
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a ∨
      (heap4 ≤ a ∧ a < nextHeap)
  slotThrEnd :
    ∀ ei ∈ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E,
      s5g.mem (tok.slotThresholds + s5g.mem (tok.slots + ei)) =
        s5g.mem (tok.edgeThresholds + ei)
  offSlotEnd : ∀ ei ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
    ei ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
    s5g.mem (tok.slots + ei) = 0
  offRecEnd :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    ∀ ei ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
      ei ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
      PathEdgeAt s5g.mem (s5g.mem (tok.edgeRecords + ei)) 4 L
        (some (newCanonVal (compactUnrank G0'.E ei))) ∧
      s5g.mem (tok.edgeRecords + ei) = s4.mem (tok.edgeRecords + ei)
  offDisjEnd : ∀ e₁ ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
    ∀ e₂ ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E, e₁ ≠ e₂ →
    e₁ ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
    e₂ ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
    s5g.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ s5g.mem (tok.edgeRecords + e₂) ∨
    s5g.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ s5g.mem (tok.edgeRecords + e₁)
  r11_5g : s5g.mem (root + 11) = 0
  offReady5g : OffReadyInv s5g.mem 0 tok.offReadyList tok.inOffReady tok.intCap
  frame5g : ∀ a < heap4, a ≠ root + 11 →
    (a < uIntBuf → tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
      s5g.mem a = s4.mem a) ∧
    (uIntBuf ≤ a →
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      s5g.mem a = s4.mem a)
  metaOrd4 :
    let d := cfg.P.d
    let levelMeta := solverLevelMetaAddr tok.table d
    (∀ j, 1 ≤ j → j < d →
      s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.mem (levelMeta + j)) ∧
    (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
      s4.mem (levelMeta + j₁) + eCap * L ≤ s4.mem (levelMeta + d + j₂))

namespace WireBranchATokHypKFBL

/-- Two addresses with different tags are different. -/
theorem tagSep (tag : ℕ → ℕ) (a b va vb : ℕ) (ha : tag a = va) (hb : tag b = vb)
    (hne : va ≠ vb) : a ≠ b :=
  fun h => hne (ha.symm.trans (h ▸ hb))

/-- Two nonempty blocks of addresses with different constant tags do not overlap. -/
theorem tagBlocksDisj (tag : ℕ → ℕ) (b1 n1 v1 b2 n2 v2 : ℕ) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (h1 : ∀ i < n1, tag (b1 + i) = v1) (h2 : ∀ i < n2, tag (b2 + i) = v2) (hne : v1 ≠ v2) :
    b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 := by
  by_contra h; push Not at h
  rcases le_total b1 b2 with hle | hle
  · exact hne ((h1 (b2 - b1) (by omega)).symm.trans
      (by rw [show b1 + (b2 - b1) = b2 by omega]; simpa using h2 0 hn2))
  · exact hne.symm ((h2 (b1 - b2) (by omega)).symm.trans
      (by rw [show b2 + (b1 - b2) = b1 by omega]; simpa using h1 0 hn1))

/-- An address in a block of constant tag `v` has tag `v`. -/
theorem tag_of_block (tag : ℕ → ℕ) {b n v : ℕ} (h : ∀ i < n, tag (b + i) = v) (a : ℕ)
    (h1 : b ≤ a) (h2 : a < b + n) : tag a = v := by
  have := h (a - b) (by omega)
  rwa [show b + (a - b) = a by omega] at this

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

/-- The words with a nonzero old tag lie below `uIntBuf`. -/
theorem tagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  exact H.footLt a (Or.inl (hTags0.1 a h))

/-- The words of `s4` below `uIntBuf` whose old tag is not changed by Steps 0–4 hold their
values in `mem0`. -/
theorem s4_tag {a v : ℕ} (ht : tok.tag a = v)
    (hv : v ∉ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20])
    (h22 : v ≠ 22 + cfg.P.d) (h23 : v ≠ 23 + cfg.P.d) (hc : ∀ j < cfg.P.d, v ≠ 21 + j) :
    s4.mem a = mem0 a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, hT4, hT5, _⟩ := hTags0
  have hv' : ∀ c ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20], v ≠ c :=
    fun c hc' h => hv (h ▸ hc')
  have hlt := H.tagLt (ht ▸ hv' 0 (by simp))
  have hT4' := tag_of_block tok.tag hT4
  have hT5' := tag_of_block tok.tag hT5
  exact H.frame4_0 a hlt
    (tagSep _ _ _ _ _ ht (hT1 11 (by omega)) (hv' 1 (by simp)))
    (tagSep _ _ _ _ _ ht (hT1 14 (by omega)) (hv' 1 (by simp)))
    (tagSep _ _ _ _ _ ht (hT5 (2 * (cfg.P.d + 1)) (by omega)) (hv' 5 (by simp)))
    (by by_contra h; push Not at h; exact hv' 4 (by simp) (ht.symm.trans (hT4' _ h.1 (by omega))))
    (by by_contra h; push Not at h; exact hv' 4 (by simp) (ht.symm.trans (hT4' _ (by omega)
      (by omega))))
    (by by_contra h; push Not at h; exact hv' 5 (by simp) (ht.symm.trans (hT5' _ (by omega)
      (by omega))))
    (ht ▸ hv' 6 (by simp)) (ht ▸ hv' 7 (by simp)) (ht ▸ hv' 8 (by simp))
    (ht ▸ hv' 9 (by simp)) (ht ▸ hv' 10 (by simp)) (ht ▸ hv' 11 (by simp))
    (ht ▸ hv' 12 (by simp)) (ht ▸ hv' 13 (by simp)) (ht ▸ hv' 14 (by simp))
    (ht ▸ hv' 15 (by simp)) (ht ▸ hv' 16 (by simp)) (ht ▸ hv' 20 (by simp))
    (ht ▸ h22) (ht ▸ h23) (fun j hj => ht ▸ hc j hj)

/-- The root words of `s4` other than `root + 11` and `root + 14` hold their values in
`mem0`. -/
theorem s4_root (j : ℕ) (hj : j < 16) (hne11 : j ≠ 11) (hne14 : j ≠ 14) :
    s4.mem (root + j) = mem0 (root + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, hT4, hT5, _⟩ := hTags0
  have h1 := hT1 j hj
  have hT4' := tag_of_block tok.tag hT4
  have hT5' := tag_of_block tok.tag hT5
  exact H.frame4_0 (root + j) (H.tagLt (by rw [h1]; decide)) (by omega) (by omega)
    (tagSep _ _ _ _ _ h1 (hT5 (2 * (cfg.P.d + 1)) (by omega)) (by decide))
    (by by_contra h; push Not at h; have := hT4' _ h.1 (by omega); omega)
    (by by_contra h; push Not at h; have := hT4' (root + j) (by omega) (by omega); omega)
    (by by_contra h; push Not at h; have := hT5' (root + j) (by omega) (by omega); omega)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; omega) (by rw [h1]; omega) (fun _ _ => by rw [h1]; omega)

/-- The words of `s5g` below `uIntBuf` whose old tag the tree sync does not touch hold their
values in `s4`. -/
theorem s5g_eq4_tag {a v : ℕ} (ht : tok.tag a = v) (hv : v ∉ [0, 1, 9, 10, 11, 13, 14, 15, 16]) :
    s5g.mem a = s4.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  have hT1 := hTags0.2.1
  have hv' : ∀ c ∈ [0, 1, 9, 10, 11, 13, 14, 15, 16], v ≠ c := fun c hc' h => hv (h ▸ hc')
  have hlt := H.tagLt (ht ▸ hv' 0 (by simp))
  have := H.heaps
  have := H.uLeHeap
  exact (H.frame5g a (by omega) (tagSep _ _ _ _ _ ht (hT1 11 (by omega)) (hv' 1 (by simp)))).1
    hlt (ht ▸ hv' 9 (by simp)) (ht ▸ hv' 10 (by simp)) (ht ▸ hv' 11 (by simp))
    (ht ▸ hv' 13 (by simp)) (ht ▸ hv' 14 (by simp)) (ht ▸ hv' 15 (by simp))
    (ht ▸ hv' 16 (by simp))

/-- The root words of `s5g` other than `root + 11` hold their values in `s4`. -/
theorem s5g_eq4_root (j : ℕ) (hj : j < 16) (hne11 : j ≠ 11) :
    s5g.mem (root + j) = s4.mem (root + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  have h1 := hTags0.2.1 j hj
  have hlt := H.tagLt (by rw [h1]; decide)
  have := H.heaps
  have := H.uLeHeap
  exact (H.frame5g (root + j) (by omega) (by omega)).1 hlt
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)

/-- The words of `s5g` in `[heapSync, heap4)` hold their values in `s4`. -/
theorem s5g_eq4_hi (a : ℕ) (ha1 : heapSync ≤ a) (ha2 : a < heap4) : s5g.mem a = s4.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _⟩ := hTags0
  obtain ⟨hH1Lo, hSyncLo, _⟩ := H.heaps
  have hU := H.uLeHeap
  exact (H.frame5g a ha2 (by have := H.tagLt (by rw [hT1 11 (by omega)]; decide); omega)).2
    (by omega) (fun hf => by
      rcases H.treeFoot1 a hf with h0 | ⟨_, hhi⟩
      · have := H.tagLt (by rw [hT16 a h0]; decide); omega
      · omega)

/-- The words of `s5g` in `[heap, heap1)` hold their values in `s4`. -/
theorem s5g_eq4_sel (a : ℕ) (ha1 : heap ≤ a) (ha2 : a < heap1) : s5g.mem a = s4.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _⟩ := hTags0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, _⟩ := H.heaps
  have hU := H.uLeHeap
  exact (H.frame5g a (by omega)
    (by have := H.tagLt (by rw [hT1 11 (by omega)]; decide); omega)).2 (by omega)
    (fun hf => by
      rcases H.treeFoot1 a hf with h0 | ⟨hlo, _⟩
      · have := H.tagLt (by rw [hT16 a h0]; decide); omega
      · omega)

/-- The foot of the tree after the second sync: the old foot, the records of Sync 1, or the
words that Sync 2 allocates. -/
theorem treeFoot2 (a : ℕ)
    (ha : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok2 a) :
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
      (heap1 ≤ a ∧ a < heapSync) ∨ (heap4 ≤ a ∧ a < nextHeap) := by
  rcases H.footEnd a ha with h1 | hhi
  · rcases H.treeFoot1 a h1 with h0 | hmid
    · exact Or.inl h0
    · exact Or.inr (Or.inl hmid)
  · exact Or.inr (Or.inr hhi)

/-- The words in `[heapSync, heap4)` are not in the foot of the tree after the second sync. -/
theorem notTr2_hi (a : ℕ) (ha1 : heapSync ≤ a) (ha2 : a < heap4) :
    ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok2 a :=
  fun hf => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _⟩ := hTags0
    obtain ⟨hH1Lo, hSyncLo, _⟩ := H.heaps
    have hU := H.uLeHeap
    rcases H.treeFoot2 a hf with h0 | ⟨_, hhi'⟩ | ⟨hlo', _⟩
    · have := H.tagLt (by rw [hT16 a h0]; decide); omega
    · omega
    · omega

/-! ### The model after the reset -/

theorem preExtG : (alg2PreResetState cfg model U gVec lVec).extG = model.extG := by
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := H.rep0
  obtain ⟨hTr1Eq, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.ref
  dsimp [alg2PreResetState]; exact hTr1Eq

theorem preE2I :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    (alg2PreResetState cfg model U gVec lVec).extToInt =
      level0E2I true ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.1 := by
  intro tr
  change level0E2I (level0Rebuilt cfg.P.d model.chain.rebuildCount
    (alg2PreResetState cfg model U gVec lVec).chain.rebuildCount) _ _ = _
  rw [H.renTrue]

theorem preI2E :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    (alg2PreResetState cfg model U gVec lVec).intToExt =
      level0I2E true ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.1 := by
  intro tr
  change level0I2E (level0Rebuilt cfg.P.d model.chain.rebuildCount
    (alg2PreResetState cfg model U gVec lVec).chain.rebuildCount) _ _ = _
  rw [H.renTrue]

theorem preNF :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    (alg2PreResetState cfg model U gVec lVec).nextFresh =
      level0NF true ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.1 := by
  intro tr
  change level0NF (level0Rebuilt cfg.P.d model.chain.rebuildCount
    (alg2PreResetState cfg model U gVec lVec).chain.rebuildCount) _ _ = _
  rw [H.renTrue]

theorem preG0 :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    (alg2PreResetState cfg model U gVec lVec).chain.G 0 =
      ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := by
  intro tr
  rw [H.chPreEq]; exact (ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P _ H.dPos _ _).2.1

theorem freshPre :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt modelPre.intToExt
      modelPre.nextFresh := by
  intro modelPre
  obtain ⟨_, _, _, _, hFreshInv0, _⟩ := H.rep0
  obtain ⟨_, hFreshTr, _⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.ref
  have hUp := Chain.Ordered.update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    gVec lVec hFreshTr
  rw [H.preExtG]; exact hUp.1

theorem preG0m :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0).m =
      ((model.chain.G 0).applyBatch tr.2.2.2.2).m := by
  intro tr
  rw [H.preG0]; simp [tr, MGraph.m, MGraph.compact]

theorem preG0Cap : ∀ e ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
    e < tok.intCap := fun e he => by
  rw [H.preG0] at he
  have hlt : e < ((model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m := by
    simpa [MGraph.compact, MGraph.m] using he
  exact lt_of_lt_of_le hlt H.g0'mLeR.2

theorem preI2EGe : ∀ j ≥ tok.intCap, (alg2PreResetState cfg model U gVec lVec).intToExt j = j :=
  fun j hj => by
    rw [H.preI2E]; unfold level0I2E compactUnrank
    have hle := H.g0'mLeR.2
    have hge : ¬ j < ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh
          U).2.2.2.2).E.card := by
      change ¬ j < ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m
      omega
    simp only [↓reduceIte, hge, ↓reduceDIte]; exact H.i2eGe j hj

/-- The edge record that `s4` holds for a live edge lies below `heap2`, and its words below
`uIntBuf` carry tag 18. -/
theorem recLoc :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    ∀ e ∈ model.extG.E, ∀ a, s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) ≤ a →
      a < s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) →
      a < heap2 ∧ (a < uIntBuf → tok.tag a = 18) := by
  intro tr G0' e he a ha1 ha2
  obtain ⟨_, _, _, _, hFreshInv0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT1718, _⟩ := hTags0
  obtain ⟨_, _, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.ref
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, _⟩ := H.heaps
  have hU := H.uLeHeap
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hInG0, hNotG0⟩ := H.canon4 e he
  by_cases hOld : tr.2.1 e ∈ (model.chain.G 0).E
  · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
    · obtain ⟨hlo, hhi, _⟩ := (hInG0 hOld).2.1 hTree
      change heap1 ≤ s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
      change s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heapSync
        at hhi
      exact ⟨by omega, fun hlt => by omega⟩
    · have hPtr : s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) =
          mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
      have heOld : model.extToInt e = tr.2.1 e := by
        by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
        · exact False.elim ((hDichRep e he hRepE).2.2.2.1 hOld)
        · exact (hDichUnch e he hRepE).2.1.symm
      have h18 : tok.tag a = 18 := by
        have := (hT1718 e he).2 (heOld.symm ▸ hTree) (a - mem0 (tok.edgeRecords + tr.2.1 e))
          (by omega)
        rwa [heOld, show mem0 (tok.edgeRecords + tr.2.1 e) +
          (a - mem0 (tok.edgeRecords + tr.2.1 e)) = a by omega] at this
      have := H.tagLt (by rw [h18]; decide)
      exact ⟨by omega, fun _ => h18⟩
  · obtain ⟨_, _, hlo, hhi⟩ := hNotG0 hOld
    change heapSync + 3 * L ≤ s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) at hlo
    change s4.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) + (2 + 4 * L) ≤ heap2 at hhi
    exact ⟨by omega, fun hlt => by omega⟩

/-! ### The memory after the off-ready rebuild

The off-ready rebuild changes only the count word `root + 11` and the two off-ready arrays
(`hFr`). So every other word keeps its value in `s5g`. -/

section ReadyFrame

variable {memK : ℕ → ℕ}
  (hFr : ∀ a, a ≠ root + 11 → (a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a) →
    (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) → memK a = s5g.mem a)
include hFr

theorem k_eq5g_geU (a : ℕ) (ha : uIntBuf ≤ a) : memK a = s5g.mem a := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, hIntCapPos, _, _⟩, _, _, _, _, _, _, _, _, _, _, _,
    hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, _, _, _, _, _, _, _, _, _, _, hT14, hT15, _⟩ := hTags0
  exact hFr a (by have := H.tagLt (by rw [hT1 11 (by omega)]; decide); omega)
    (Or.inr (by have := H.tagLt (by rw [hT14 (tok.intCap - 1) (by omega)]; decide); omega))
    (Or.inr (by have := H.tagLt (by rw [hT15 (tok.intCap - 1) (by omega)]; decide); omega))

theorem k_eq5g_tag {a v : ℕ} (ht : tok.tag a = v) (hv : v ∉ [1, 14, 15]) :
    memK a = s5g.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, _, _, _, _, _, _, _, _, _, _, hT14, hT15, _⟩ := hTags0
  have hv' : ∀ c ∈ [1, 14, 15], v ≠ c := fun c hc' h => hv (h ▸ hc')
  exact hFr a (tagSep _ _ _ _ _ ht (hT1 11 (by omega)) (hv' 1 (by simp)))
    (by
      by_contra h; push Not at h
      exact hv' 14 (by simp) (ht.symm.trans (tag_of_block tok.tag hT14 _ h.1 h.2)))
    (by
      by_contra h; push Not at h
      exact hv' 15 (by simp) (ht.symm.trans (tag_of_block tok.tag hT15 _ h.1 h.2)))

theorem k_eq4_tag {a v : ℕ} (ht : tok.tag a = v) (hv : v ∉ [0, 1, 9, 10, 11, 13, 14, 15, 16]) :
    memK a = s4.mem a :=
  (H.k_eq5g_tag hFr ht (by
    intro h; apply hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans
    (H.s5g_eq4_tag ht hv)

theorem k_eq4_root (j : ℕ) (hj : j < 16) (hne11 : j ≠ 11) :
    memK (root + j) = s4.mem (root + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, _, _, _, _, _, _, _, _, _, _, _, _, hT14, hT15, _⟩ := hTags0
  have h1 := hT1 j hj
  refine (hFr (root + j) (by omega) ?_ ?_).trans (H.s5g_eq4_root j hj hne11)
  · by_contra h; push Not at h
    have := tag_of_block tok.tag hT14 _ h.1 h.2; omega
  · by_contra h; push Not at h
    have := tag_of_block tok.tag hT15 _ h.1 h.2; omega

theorem k_eq4_hi (a : ℕ) (ha1 : heapSync ≤ a) (ha2 : a < heap4) : memK a = s4.mem a := by
  obtain ⟨hH1Lo, hSyncLo, _⟩ := H.heaps
  have hU := H.uLeHeap
  exact (H.k_eq5g_geU hFr a (by omega)).trans (H.s5g_eq4_hi a ha1 ha2)

theorem k_eq4_sel (a : ℕ) (ha1 : heap ≤ a) (ha2 : a < heap1) : memK a = s4.mem a := by
  have hU := H.uLeHeap
  exact (H.k_eq5g_geU hFr a (by omega)).trans (H.s5g_eq4_sel a ha1 ha2)

/-- The threshold word of a live edge after the off-ready rebuild: it is the word of `s4`, and
it points to the threshold of the edge. -/
theorem thrK (e : ℕ) (he : e ∈ (alg2PreResetState cfg model U gVec lVec).extG.E) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    memK (tok.edgeThresholds + modelPre.extToInt e) =
      s4.mem (tok.edgeThresholds + modelPre.extToInt e) ∧
    PathIntAt memK (memK (tok.edgeThresholds + modelPre.extToInt e)) 4 L
      (detectorThreshold P cfg.ε (modelPre.extℓ e)) := by
  intro modelPre
  obtain ⟨_, _, _, _, hFreshInv0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hT12, _, _, _, _, hT1718, _⟩ := hTags0
  obtain ⟨_, _, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 H.ref
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, _⟩ := H.heaps
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch tr.2.2.2.2
  have hPreE2I : modelPre.extToInt = level0E2I true G0' tr.2.1 := H.preE2I
  have he0 : e ∈ model.extG.E := H.preExtG ▸ he
  obtain ⟨hLt, _, hThr4, _, _, _, _, _, _, _, _, _, _, hInG0, hNotG0⟩ := H.canon4 e he0
  have hCap := lt_of_lt_of_le hLt H.g0'mLeR.2
  have hCell : memK (tok.edgeThresholds + modelPre.extToInt e) =
      s4.mem (tok.edgeThresholds + modelPre.extToInt e) := by
    rw [hPreE2I]; exact H.k_eq4_tag hFr (hT12 _ hCap) (by decide)
  refine ⟨hCell, ?_⟩
  rw [hCell, hPreE2I]
  refine hThr4.congr fun t ht => ?_
  by_cases hOld : tr.2.1 e ∈ G0.E
  · rw [(hInG0 hOld).1]
    have hOldEq : model.extToInt e = tr.2.1 e := by
      by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
      · exact False.elim ((hDichRep e he0 hRepE).2.2.2.1 hOld)
      · exact (hDichUnch e he0 hRepE).2.1.symm
    have h17 : tok.tag (mem0 (tok.edgeThresholds + tr.2.1 e) + t) = 17 := by
      rw [← hOldEq]; exact (hT1718 e he0).1 t ht
    exact H.k_eq4_tag hFr h17 (by decide)
  · obtain ⟨hlo, hhi, _, _⟩ := hNotG0 hOld
    change heapSync + 3 * L ≤ s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) at hlo
    change s4.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) + L ≤ heap2 at hhi
    exact H.k_eq4_hi hFr _ (by omega) (by omega)

/-- The record word of an edge off the new forest after the off-ready rebuild: it is the word of
`s5g`, which is the word of `s4`. -/
theorem recOffK (ei : ℕ) (hei : ei ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E)
    (hnot : ei ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E) :
    memK (tok.edgeRecords + ei) = s5g.mem (tok.edgeRecords + ei) ∧
    s5g.mem (tok.edgeRecords + ei) = s4.mem (tok.edgeRecords + ei) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.rep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT13, _⟩ := hTags0
  exact ⟨H.k_eq5g_tag hFr (hT13 ei (H.preG0Cap ei hei)) (by decide),
    (H.offRecEnd ei hei hnot).2⟩

end ReadyFrame

end WireBranchATokHypKFBL

end MinCostFlow.MinRatio
