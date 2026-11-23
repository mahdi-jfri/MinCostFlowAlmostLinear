module

public import MinCostFlow.MinRatio.WireChainCoreBranchBExitOutKFBL
public import MinCostFlow.MinRatio.WireChainCoreSyncPhaseKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecProofKFBL

/-!
# The state after the suffix of Branch B, and the post of Branch B (`WireChainCoreBranchBSufOutKFBL`)

Branch B of the chain core runs a prefix (Sync 1 and the refresh of level `0`), the front and
the loop of plain steps, one of three exits (`BranchBExitOutKFBL`), and a suffix: the change of
the root graph in the tree state, Sync 2a, the load of `firstReb` into `reg 99`, Sync 2b, the
push of the inserted names onto the off-ready list, and the return. This file states what the
whole of Branch B leaves, as one structure, and the post of Branch B as one proposition.

* `BranchBSufOutKFBL` holds the facts on the final state `out` that the post reads. They follow
  the facts that the post of Branch A reads from its own suffix (`WireBranchATokHypKFBL`): the
  tree state on the new root graph with nothing deferred (`TreeSyncPhaseAt`), where the new words
  of the tree, of the records and of the thresholds lie, the accounts of the edges, the cores and
  the last level with the places of their footprints, the level graphs and lengths, the words that
  keep their values, the finished select slots with their model facts, and the cost and the space
  of the run in their final form.
* `BranchBPostGoalKFBL` is the post: from the premises of `OrdChainCoreBranchBPostKFBL`, a run of
  the core that returns `nextHeap`, and `BranchBSufOutKFBL` at its final state, the conclusion
  `OrdChainCoreExtPost` holds. `branchBPostGoalKFBL_proved` (`WireChainCoreBranchBPostRep.lean`)
  proves it from the new token (the tree, the cores, the last level and the off-ready count of
  the structure), its tags, and the rep, as Branch A does in
  `WireChainCoreBranchATokTagKFBL.lean` and `WireChainCoreBranchATokKFBL.lean`.
* `ordChainCoreBranchBPost_of_goal` gives `OrdChainCoreBranchBPostKFBL` from the goal and a run of
  the core that ends in a state with `BranchBSufOutKFBL`.

The heap of Branch B is cut into four parts, which the structure names:
* `[heap, heap + 1 + 12 d)`: the select slots;
* `[heap + 1 + 12 d, heap2)`: the forest pointer arrays, Sync 1 and the refresh of level `0` (the
  new words of the tree, the records of the cut edges, the records and thresholds of the new
  names);
* `[heap2, hX)`: the copy of the batch of level `0`, the loop and the exit. The last level, the
  new cores and the rebuilt level blocks lie in `[hS, hT)`. The select data of the finished levels
  lies in the zone `[heap2, hS) ∪ [hT, hX)` (`BranchBSelZone`): the exit rebuilds the levels from
  `fr` on and then writes the descriptor of level `fr - 1` again, above the rebuilt blocks;
* `[hX, nextHeap)`: Sync 2a and Sync 2b (the new words of the tree and the records of the cut
  edges).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The facts on the final state `out` of Branch B, after the suffix and the return of `nextHeap`.
The run started at a state whose memory is `mem`, with the solver rep at `mem0`, the model
`model`, the token `tok` and the outer batch `U`; `gVec`, `lVec` are the new gradients and
lengths, and the model after the update is `alg2PreResetState cfg model U gVec lVec`. The first
rebuilt level is `fr` (`0 < fr ≤ d + 1`), the cores of the levels are at the handles in
`out.mem (tok.handle + 18 + j)` with tokens `tokN j`, the last level has caps `(vcL, ecL)` and
token `termTokN`, the path tree is `curTree` with token `curTreeTok`, the off-ready list has
`offCnt` entries, and `canonVal` gives the values of the edge accounts. The numbers
`heap2 ≤ hS ≤ hT ≤ hX ≤ nextHeap` cut the heap into the parts of the module docstring. `cost` is the
cost of the run of the core. -/
structure BranchBSufOutKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  coreLocal : Rcore.Local
  dPos : 0 < cfg.P.d
  heaps : uIntBuf ≤ heap ∧ heap + 1 + 12 * cfg.P.d ≤ heap2 ∧ heap2 ≤ hS ∧ hS ≤ hT ∧ hT ≤ hX ∧
    hX ≤ nextHeap ∧ nextHeap < 2 ^ w
  space : nextHeap ≤ heap + coreSpace U.length
  zero : ZeroFrom out.mem nextHeap
  -- the model
  names :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let modelPre := alg2PreResetState cfg model U gVec lVec
    modelPre.extToInt = tr.2.1 ∧ modelPre.intToExt = tr.2.2.1 ∧ modelPre.nextFresh = tr.2.2.2.1
  frPos : 0 < fr
  link : UpdateCoreLevelLink model.chain (alg2PreResetState cfg model U gVec lVec).chain fr
    levelU levelUS
  newForest : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.IsForest
  newSub : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E ⊆
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E
  -- the words that keep their values
  rootDir : ∀ j < 16, j ≠ 11 → out.mem (root + j) = mem0 (root + j)
  header : ∀ j < 18, out.mem (tok.handle + j) = mem0 (tok.handle + j)
  table : ∀ j ≤ cfg.P.d, out.mem (tok.table + j) = mem0 (tok.table + j)
  metaCells :
    out.mem (solverN0Addr tok.table cfg.P.d) = mem0 (solverN0Addr tok.table cfg.P.d) ∧
    (∀ j < cfg.P.d, out.mem (solverLvlMAddr tok.table cfg.P.d + j) =
      mem0 (solverLvlMAddr tok.table cfg.P.d + j)) ∧
    out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
      mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
    out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
      mem0 (solverSelectBlocksAddr tok.table cfg.P.d)
  fresh :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    FreshTablesAt out.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1
  sched : SolverScheduleAt out.mem tok.levelsEnd (alg2PreResetState cfg model U gVec lVec)
  frameMem : ∀ a < heap,
    ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
    out.mem a = mem a
  -- the tree and the edge accounts
  phase : TreeSyncPhaseAt L tok root uIntBuf nextHeap tok.rootGraph
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0)
    (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E canonVal B R ∅
    curTree curTreeTok offCnt out.mem
  treeFoot : ∀ a,
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a →
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
      (heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2) ∨ (hX ≤ a ∧ a < nextHeap)
  canon :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e ∈ model.extG.E,
      let ei := tr.2.1 e
      let v := canonVal ei
      PathIntAt out.mem (out.mem (tok.edgeThresholds + ei)) 4 L
        (detectorThreshold P cfg.ε (lVec e)) ∧
      (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
      (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
      (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
      ∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        v.detector = acc - detectorThreshold P cfg.ε (lVec e)
  thrLoc :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e ∈ model.extG.E, ∀ j < L,
      let a := out.mem (tok.edgeThresholds + tr.2.1 e) + j
      (a < uIntBuf → tok.tag a = 17) ∧
      (uIntBuf ≤ a → heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a
  recLoc : ∀ ei ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
    ei ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
    ∀ j < 2 + 4 * L, uIntBuf ≤ out.mem (tok.edgeRecords + ei) + j →
      (heap + 1 + 12 * cfg.P.d ≤ out.mem (tok.edgeRecords + ei) + j ∧
        out.mem (tok.edgeRecords + ei) + j < heap2) ∨
      (hX ≤ out.mem (tok.edgeRecords + ei) + j ∧ out.mem (tok.edgeRecords + ei) + j < nextHeap)
  thrRecDisj :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E,
      tr.2.1 e₂ ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
      out.mem (tok.edgeThresholds + tr.2.1 e₁) + L ≤ out.mem (tok.edgeRecords + tr.2.1 e₂) ∨
      out.mem (tok.edgeRecords + tr.2.1 e₂) + (2 + 4 * L) ≤
        out.mem (tok.edgeThresholds + tr.2.1 e₁)
  -- the cores and the last level
  bran : ∀ j < cfg.P.d, out.mem (tok.handle + 18 + (cfg.P.d + 1) + j) =
    (alg2PreResetState cfg model U gVec lVec).chain.bran j
  lastB : out.mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) =
    (alg2PreResetState cfg model U gVec lVec).chain.lastBran
  reps : ∀ j < cfg.P.d, Rcore.rep (out.mem (tok.handle + 18 + j))
    (chainLevelOrdAbs (alg2PreResetState cfg model U gVec lVec).chain j) (tokN j) out.mem
  coreFoot : ∀ j < cfg.P.d, ∀ a, Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) a →
    (a < heap → tok.tag a = 21 + j) ∧ (heap ≤ a → heap2 ≤ a ∧ a < hX)
  coreDisj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
    Rcore.foot (out.mem (tok.handle + 18 + j₁)) (tokN j₁) a →
    ¬ Rcore.foot (out.mem (tok.handle + 18 + j₂)) (tokN j₂) a
  coreHandleLoc : ∀ j < cfg.P.d,
    out.mem (tok.handle + 18 + j) = mem0 (tok.handle + 18 + j) ∨
    (hS ≤ out.mem (tok.handle + 18 + j) ∧ out.mem (tok.handle + 18 + j) < hT)
  lastRep : (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).rep
    (out.mem (tok.handle + 18 + cfg.P.d))
    ((alg2PreResetState cfg model U gVec lVec).chain.lastK,
      (alg2PreResetState cfg model U gVec lVec).chain.lastLSFs) termTokN out.mem
  lastFoot : ∀ a, (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).foot
      (out.mem (tok.handle + 18 + cfg.P.d)) termTokN a →
    (a < heap → tok.tag a = 19) ∧ (heap ≤ a → hS ≤ a ∧ a < hT) ∧
    ∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) a
  -- the level graphs and lengths
  graphs : ∀ j < cfg.P.d,
    DynGraphAt out.mem (out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)) vCap eCap
      ((alg2PreResetState cfg model U gVec lVec).chain.G j)
  lens : ∀ j < cfg.P.d,
    EdgeValuesAt out.mem (out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)) 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G j).E
      ((alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainLen
        (alg2PreResetState cfg model U gVec lVec).chain.ℓ j)
  metaKeep : ∀ j < min (fr + 1) cfg.P.d,
    out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
    out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + j)
  metaNew : ∀ j, fr + 1 ≤ j → j < cfg.P.d →
    let gp := out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
    let lp := out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)
    hS ≤ gp ∧ gp + dynGraphSize vCap eCap ≤ hT ∧ hS ≤ lp ∧ lp + eCap * L ≤ hT ∧
    ∀ a, ((gp ≤ a ∧ a < gp + dynGraphSize vCap eCap) ∨ (lp ≤ a ∧ a < lp + eCap * L)) →
      (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + r)) (tokN r) a) ∧
      ¬ (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
        ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).foot
        (out.mem (tok.handle + 18 + cfg.P.d)) termTokN a
  -- the select slots of the levels that are not rebuilt
  sel : out.mem heap = fr
  slots : ∀ j < min fr cfg.P.d,
    SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun x => BranchBSelZone heap2 hS hT hX x ∧
        ∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + r)) (tokN r) x)
      (fun x => Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) x ∨ (heap2 ≤ x ∧ x < hX))
      heap2 hX out.mem (heap + 1 + 12 * j) (D j) (model.chain.G j) (levelU j)
      ((alg2PreResetState cfg model U gVec lVec).chain.G j).E
      (cfg.T.lsfs ((alg2PreResetState cfg model U gVec lVec).chain.scState j)
        ((alg2PreResetState cfg model U gVec lVec).chain.bran j)).wstr
  slotModel : ∀ j < min fr cfg.P.d,
    (D j).uG = coreBatchTouchedEdges (levelU j) ∧
    (D j).uS = coreBatchTouchedEdges (levelUS j) ∧
    (D j).fDel.Nodup ∧
    (D j).fDel.toFinset = (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E \
      (cfg.T.lsfs ((alg2PreResetState cfg model U gVec lVec).chain.scState j)
        ((alg2PreResetState cfg model U gVec lVec).chain.bran j)).F.F.E ∧
    (D j).reemb = reembFn (model.chain.scState j) (levelU j)
      ((alg2PreResetState cfg model U gVec lVec).chain.levelOrd j) (model.chain.bran j) ∧
    BatchWithinCaps vCap eCap (levelU j)
  -- the cost of the run against the potentials
  costLe : cost +
      ((LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap curTreeTok
          out.mem +
        (Finset.range cfg.P.d).sum
          (fun j => Rcore.phi (out.mem (tok.handle + 18 + j)) (tokN j) out.mem) +
        offCnt * drainUnit) ≤
    coreFixed U.length +
      toolMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalRuntime -
        model.chain.totalRuntime) +
      treeMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalTreeUpdates -
        model.chain.totalTreeUpdates) +
      40 * (Finset.range (min fr cfg.P.d)).sum (fun j => (D j).reemb.length) +
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem0

/-- The memory clauses of `UpdateCoreSelectOutAt` at a finished level from the field `slots` of
`BranchBSufOutKFBL`, for a final footprint `F` that contains the footprint of core `j` and no word
of the zone `BranchBSelZone` that lies off all cores, and for a select base `lo' ≤ heap2`. This is
`BranchBDoneSlots.level` with the zone in place of one interval. -/
theorem branchBSufSlots_level {w P Lmax heap2 hS hT hX lo' d slot j : ℕ}
    {foot : ℕ → ℕ → Prop} {F : ℕ → Prop} {mem : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph}
    {U : List Update} {E : Finset ℕ} {vals : ℕ → ℝ}
    (h : SelOutLevelMemAt w P Lmax
      (fun x => BranchBSelZone heap2 hS hT hX x ∧ ∀ r < d, ¬ foot r x)
      (fun x => foot j x ∨ (heap2 ≤ x ∧ x < hX)) heap2 hX mem slot D G U E vals)
    (hlo' : lo' ≤ heap2)
    (hF : ∀ a, BranchBSelZone heap2 hS hT hX a → (∀ r < d, ¬ foot r a) → ¬ F a)
    (hFoot : ∀ a, foot j a → F a) :
    LevelDiffListsAt mem slot D ∧
    SelOutWordsAt F lo' hX (mem (slot + 0)) D.uG.length ∧
    SelOutWordsAt F lo' hX (mem (slot + 2)) D.fDel.length ∧
    SelOutWordsAt F lo' hX (mem (slot + 4)) D.uS.length ∧
    SelOutWordsAt F lo' hX (mem (slot + 6)) D.reemb.length ∧
    SmallBatchAt mem (mem (slot + 10)) G U (mem (slot + 11)) ∧
    (∀ t < mem (slot + 11), mem (mem (slot + 10) + t) < 2 ^ w) ∧
    SelOutWordsAt F lo' hX (mem (slot + 10)) (mem (slot + 11)) ∧
    SelOutWordsAt F lo' hX (mem (slot + 8)) 2 ∧
    mem (slot + 9) ≤ Lmax ∧
    StretchValuesAt mem (mem (slot + 8)) 4 (mem (slot + 9)) P E vals ∧
    SelOutTableAt w F lo' hX mem (mem (slot + 8)) (mem (slot + 9)) E ∧
    SelOutTableAt w F lo' hX mem (mem (slot + 8) + 1) (mem (slot + 9)) E := by
  have h1 := h.transfer
    (Good' := fun x => BranchBSelZone heap2 hS hT hX x ∧ ∀ r < d, ¬ foot r x)
    (InTab' := fun x => foot j x ∨ (lo' ≤ x ∧ x < hX)) (mem' := mem)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ hg => hg)
    (fun a ha => ha.imp id fun h' => ⟨by omega, h'.2⟩) hlo' le_rfl
  exact h1.toSelectOut (fun a _ _ hg => hF a hg.1 hg.2) (fun a ha => ha.imp (hFoot a) id)

/-- **The post of Branch B.** For every start state that meets the premises of
`OrdChainCoreBranchBPostKFBL` (the premises of `OrdChainUpdateCoreSpecWExtKFBL` and the failed
rebuild test at level `0`), every run of the core `body` from it that returns `nextHeap` and ends
in a state `out` with `BranchBSufOutKFBL` gives the conclusion `OrdChainCoreExtPost`. -/
@[expose] def BranchBPostGoalKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (G : MGraph) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ) (B_bound R_bound : ℤ)
    (body : Stmt) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
    (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (U : List Update) (B R : ℤ),
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let modelPre := alg2PreResetState cfg model U gVec lVec
    Rrep.rep root model tok mem0 →
    SolverLevelMetaAt P V model tok mem0 →
    SolverLevelCapsAt vCap eCap model tok mem0 →
    tok.intCap = initTargetCap cfg G →
    model.extG.m = m →
    PathTreeNumericInv tok.tree tok.trees B R →
    OffTreeRecInv model L mem0 tok.edgeRecords B →
    OffTreeRecBound model L mem0 tok.edgeRecords B →
    B ≤ B_bound → R ≤ R_bound →
    Chain.Ordered.ShiftLoopChainInv cfg model.chain →
    WireCapFacts capExp limbMul L capLimit model →
    (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
    UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
    UpdateCoreModelInvKFBL model U gVec lVec →
    tok.intCap ≤ intCapMax →
    graphListEdgeSum (chainSuffixForests model.chain 0) +
      graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
    Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
    2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
    (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
    FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 →
    tr.2.2.2.1 ≤ tok.intCap →
    BatchAt mem uIntBuf tr.2.2.2.2 →
    SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
    OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
    (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
    editsPtr + editWords = heap →
    RefreshBatch model.extG U →
    (∀ a, Rrep.foot root tok a → a < uIntBuf) →
    g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
    uIntBuf + cfg.P.d ≤ editsPtr →
    ZeroFrom mem heap →
    heap + coreSpace U.length < 2 ^ w →
    ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
    ∀ (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
      (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
      (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
      (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ),
    Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
      (.returned nextHeap) out cost →
    BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
      curTree curTreeTok offCnt canonVal out nextHeap cost →
    OrdChainCoreExtPost w L P m V psi k epsExp drainUnit capExp vCap eCap cfg reembFn Rcore p
      coreSpace coreFixed toolMul treeMul B_bound R_bound body root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U

/-- `OrdChainCoreBranchBPostKFBL` from the post goal `BranchBPostGoalKFBL` and the run of the core
(`hRun`): for every start state that meets the premises, the core runs from it, returns some
`nextHeap`, and ends in a state with `BranchBSufOutKFBL`, at the bounds `B` and `R` of the start
state. -/
theorem ordChainCoreBranchBPost_of_goal
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ}
    {cfg : Alg2Config} {G : MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ} {B_bound R_bound : ℤ} {body : Stmt}
    (hGoal : BranchBPostGoalKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p coreSpace coreFixed
      toolMul treeMul B_bound R_bound body)
    (hRun : ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
      (U : List Update) (B R : ℤ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      tok.intCap = initTargetCap cfg G →
      model.extG.m = m →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      B ≤ B_bound → R ≤ R_bound →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
      UpdateCoreModelInvKFBL model U gVec lVec →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
      OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
      (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
      editsPtr + editWords = heap →
      RefreshBatch model.extG U →
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
      ∃ (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
        (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
        (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
        (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ),
      Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
        (.returned nextHeap) out cost ∧
      BranchBSufOutKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
        (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
        (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
        mem0 mem model tok U gVec lVec B R heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN
        curTree curTreeTok offCnt canonVal out nextHeap cost) :
    OrdChainCoreBranchBPostKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p coreSpace
      coreFixed toolMul treeMul B_bound R_bound body := by
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R tr gVec lVec
    modelPre h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35
  obtain ⟨heap2, hS, hT, hX, fr, levelU, levelUS, D, tokN, vcL, ecL, termTokN, curTree, curTreeTok,
    offCnt, canonVal, out, nextHeap, cost, hR, hS'⟩ :=
    hRun root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R h1 h2 h3 h4 h5
      h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28
      h29 h30 h31 h32 h33 h34 h35
  exact hGoal root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R h1 h2 h3 h4
    h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    h30 h31 h32 h33 h34 h35 heap2 hS hT hX fr levelU levelUS D tokN vcL ecL termTokN curTree
    curTreeTok offCnt canonVal out nextHeap cost hR hS'

end MinCostFlow.MinRatio
