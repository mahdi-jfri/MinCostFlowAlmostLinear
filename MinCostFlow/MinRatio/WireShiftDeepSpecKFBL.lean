module

public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.SolverLevelLayout
public import MinCostFlow.MinRatio.WireCoreForestCapKFBL
public import MinCostFlow.MinRatio.OrdShiftLoopLevels
public import MinCostFlow.MinRatio.WireInitReadoutKFBL
public import MinCostFlow.MinRatio.WireTreeSync

/-!
# The hypotheses of the deep shift under the layout contract (`WireShiftDeepSpecKFBL`)

The deep shift (`shiftDeepChainBody`) restarts level `i`, rebuilds the levels `i + 1, …, d - 1`
and the last level, and syncs the tree. Under the layout contract
`sparseCoreOrdMachineContractKFBL` every level graph has the caps `(vCap, eCap)` of the module,
and the module says where its readouts lie (`SparseCoreReadoutFootAt`). So the deep shift needs
no placement facts of its own. This file states what it needs instead.

* `DeepShiftCoreKFBL`: the core hypothesis. At every level `j < d` and every graph `G` with
  `G.n ≤ G.m + 1`, the module meets `sparseCoreOrdMachineContractKFBL` at
  `(G, levelM cfg.TP cfg.P j, cfg.N₀, vCap, eCap)` and `SparseCoreReadoutFootAt`. The depth is
  the one in the solver header (`SolverChainHeaderAt`).
* `DeepShiftForestCapKFBL`: the forest that op `2` returns has caps of size at most `fcap`
  (`SparseCoreForestCapAt`). Phase 1 copies the active forest of level `i`, and nothing else
  bounds the size of that copy.
* `SolverLevelCapsAt`: the stored level graphs have the caps `(vCap, eCap)`.
  `SolverLevelMetaAt.atCaps` turns `SolverLevelMetaAt` into the per-level facts at these caps.
* `ShiftDeepModelInvKFBL`: `ShiftLoopLevelFacts` before and after the shift, and the bound on the
  words of the order that each rebuilt level hands to the next one.
* `DeepShiftOpsHypKFBL`: the space and cost budgets. It is `DeepShiftOpsHyp` without the
  placement fields `op2Placement`, `op3Placement` and `op5Placement`, with the level space and
  cost of the layout contract (`ordLevelSpace`, `ordLevelFixedCost`).
* `ShiftDeepChainSyncSpecWExtKFBL`: the spec of the deep shift procedure. It is
  `ShiftDeepChainSyncSpecWExt` (in `WireChainSpecs.lean`) with `SolverLevelCapsAt` and
  `ShiftDeepModelInvKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- **The core hypothesis of the deep shift.** At every level `j < d` and every graph `G` with
`G.n ≤ G.m + 1`, the sparse-core module meets the layout contract at
`(G, levelM cfg.TP cfg.P j, cfg.N₀, vCap, eCap)`, with the depth of the solver header, and
`SparseCoreReadoutFootAt`. -/
@[expose] def DeepShiftCoreKFBL {w : ℕ} (fmt : Num.Format w) (L m vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 → G.m ≤ m →
    Rcore.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation) ∧
    SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation Rcore p op

/-- The forest that op `2` returns at a level of the deep shift has caps of size at most
`fcap` (`SparseCoreForestCapAt`), at every level `j < d` and every graph `G` with
`G.n ≤ G.m + 1`. -/
@[expose] def DeepShiftForestCapKFBL {w : ℕ} (fmt : Num.Format w) (L vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (fcap : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 →
    SparseCoreForestCapAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation fcap Rcore p op

/-- The level graphs stored in `levelMeta` have the caps `(vCap, eCap)`. -/
@[expose] def SolverLevelCapsAt {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (vCap eCap : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) :
    Prop :=
  let d := cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table d
  ∀ j < d, DynGraphAt mem (mem (levelMeta + d + j)) vCap eCap (model.chain.G j)

/-- Two graphs stored at the same address have the same caps, since `DynGraphAt` stores the caps
in the first two words. -/
theorem dynGraphAt_caps_eq {mem : ℕ → ℕ} {a vc ec vc' ec' : ℕ} {G G' : MGraph}
    (h : DynGraphAt mem a vc ec G) (h' : DynGraphAt mem a vc' ec' G') : vc = vc' ∧ ec = ec' :=
  ⟨h.2.2.2.1.symm.trans h'.2.2.2.1, h.2.2.2.2.1.symm.trans h'.2.2.2.2.1⟩

/-- The per-level facts of `SolverLevelMetaAt` at the caps `(vCap, eCap)` of
`SolverLevelCapsAt`. -/
theorem SolverLevelMetaAt.atCaps {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hM : SolverLevelMetaAt P V model tok mem) (hC : SolverLevelCapsAt vCap eCap model tok mem)
    (j : ℕ) (hj : j < cfg.P.d) :
    let d := cfg.P.d
    let levelMeta := solverLevelMetaAddr tok.table d
    DynGraphAt mem (mem (levelMeta + d + j)) vCap eCap (model.chain.G j) ∧
    EdgeValuesAt mem (mem (levelMeta + j)) 4 L P (model.chain.G j).E
      (model.chain.toTreeChain.chainLen model.chain.ℓ j) ∧
    tok.owned (mem (levelMeta + j)) ∧
    (∀ a, mem (levelMeta + j) ≤ a → a < mem (levelMeta + j) + eCap * L → tok.tag a = 23 + d) ∧
    (∀ a, mem (levelMeta + d + j) ≤ a → a < mem (levelMeta + d + j) + dynGraphSize vCap eCap →
      tok.tag a = if j = 0 then 20 else 23 + d) := by
  obtain ⟨vc, ec, hDG, hLen, hOwn, hT1, hT2⟩ := hM.2.2.2.2.2 j hj
  obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG (hC j hj)
  subst hvc hec
  exact ⟨hDG, hLen, hOwn, hT1, hT2⟩

/-- `SolverLevelMetaAt` with the caps `(vCap, eCap)` at every level. It is the form in which the
deep shift proves both `SolverLevelMetaAt` and `SolverLevelCapsAt` at the end
(`SolverLevelMetaCapsAt.meta_caps`). -/
@[expose] def SolverLevelMetaCapsAt {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P _V vCap eCap : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) :
    Prop :=
  let d := cfg.P.d
  let n0Cell := solverN0Addr tok.table d
  let lvlMTable := solverLvlMAddr tok.table d
  let levelMeta := solverLevelMetaAddr tok.table d
  (mem n0Cell = model.chain.N₀ ∧ tok.tag n0Cell = 21 + d ∧
    tok.tag (solverSelectHeapAddr tok.table d) = 21 + d ∧
    tok.tag (solverSelectBlocksAddr tok.table d) = 21 + d) ∧
  (∀ j < d, tok.owned (tok.coreHandle j)) ∧
  (∀ j < d, mem (lvlMTable + j) = model.chain.lvlM j) ∧
  (∀ j < d, tok.tag (lvlMTable + j) = 21 + d) ∧
  (∀ j < 2 * d, tok.tag (levelMeta + j) = 22 + d) ∧
  (∀ j < d,
    DynGraphAt mem (mem (levelMeta + d + j)) vCap eCap (model.chain.G j) ∧
    EdgeValuesAt mem (mem (levelMeta + j)) 4 L P (model.chain.G j).E
      (model.chain.toTreeChain.chainLen model.chain.ℓ j) ∧
    tok.owned (mem (levelMeta + j)) ∧
    (∀ a, mem (levelMeta + j) ≤ a → a < mem (levelMeta + j) + eCap * L → tok.tag a = 23 + d) ∧
    (∀ a, mem (levelMeta + d + j) ≤ a → a < mem (levelMeta + d + j) + dynGraphSize vCap eCap →
      tok.tag a = if j = 0 then 20 else 23 + d))

/-- `SolverLevelMetaCapsAt` gives `SolverLevelMetaAt` (with the caps `(vCap, eCap)` as witnesses)
and `SolverLevelCapsAt`. -/
theorem SolverLevelMetaCapsAt.meta_caps {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (h : SolverLevelMetaCapsAt P V vCap eCap model tok mem) :
    SolverLevelMetaAt P V model tok mem ∧ SolverLevelCapsAt vCap eCap model tok mem :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun j hj => ⟨vCap, eCap, h.2.2.2.2.2 j hj⟩⟩,
    fun j hj => (h.2.2.2.2.2 j hj).1⟩

/-- The model facts that the deep shift at level `i` needs under the layout contract:
`ShiftLoopLevelFacts` of the chain before and after the shift, the level-size bound on the
rotation-order words that each rebuilt level hands to the next one, vertex bounds for the next
chain, and subgraph inclusions of the suffix forests and level graphs. -/
@[expose] def ShiftDeepModelInvKFBL {cfg : Alg2Config} (model : Alg2State cfg)
    (i : Fin (cfg.P.d + 1)) : Prop :=
  let next := (alg2LoopShiftStep cfg model i).chain
  ShiftLoopLevelFacts cfg model.chain ∧ ShiftLoopLevelFacts cfg next ∧
  (∀ j, i.val ≤ j → j < cfg.P.d →
    ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m) ∧
  (∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀) ∧
  (∀ j, i.val ≤ j → j < cfg.P.d →
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.V ⊆ (model.chain.G j).V ∧
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ (model.chain.G j).E ∧
    (model.chain.G (j + 1)).E ⊆ (model.chain.G j).E ∧
    (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E ⊆ (next.G j).E ∧
    (next.G (j + 1)).E ⊆ (next.G j).E) ∧
  (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ (model.chain.G cfg.P.d).E ∧
  (next.lastLSFs next.lastBran).F.F.E ⊆ (next.G cfg.P.d).E ∧
  (∀ j ≤ cfg.P.d, (next.G j).IsValid) ∧
  (∀ j ≤ cfg.P.d, (next.G j).m ≤ levelM cfg.TP cfg.P j) ∧
  (∀ u ∈ (next.G cfg.P.d).V, ∀ v ∈ (next.G cfg.P.d).V, (next.G cfg.P.d).Connected u v) ∧
  (next.G cfg.P.d).m ≤ (model.chain.G 0).m

/-- The space and cost budgets of a deep shift `i < d` under the layout contract. Every level
rebuild and graph copy pays according to the actual live size of its level (`copyGraphLiveCost`,
`ordLevelLiveCost`), and suffix edit packing pays according to the actual edge count of the old
and new suffix forests (`graphListEdgeSum`). -/
structure DeepShiftOpsHypKFBL
    {w L capExp capLimit fcap lastMul intCapMax forestEdgeCap deepSpace deepFixed toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    (restartSpace : ℕ) (levelSpace : ℕ → ℕ)
    (levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ) (lastSpace : ℕ) : Prop where
  /-- The space of the restart of level `i` and of the readout of level `i + 1`. -/
  restartSpaceDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (coreH h : ℕ),
    i.val < cfg.P.d →
    model.chain.N₀ = cfg.N₀ →
    (∀ j < cfg.P.d, model.chain.lvlM j = levelM cfg.TP cfg.P j) →
    ShiftDeepModelInvKFBL model i →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    ordLevelSpace L capExp capLimit (allocation 1 [coreH, newBran, h])
      (model.chain.lvlM i.val) model.chain.N₀ (next.G (i.val + 1)).m ≤ restartSpace
  /-- The space of the rebuild of level `j ∈ [i + 1, d)`. -/
  levelSpaceDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j g l gr o h : ℕ),
    i.val < cfg.P.d → i.val + 1 ≤ j → j < cfg.P.d →
    model.chain.N₀ = cfg.N₀ →
    (∀ r < cfg.P.d, model.chain.lvlM r = levelM cfg.TP cfg.P r) →
    ShiftDeepModelInvKFBL model i →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    ordLevelSpace L capExp capLimit
      (allocation 6 [g, l, gr, o, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h])
      (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j
  /-- The space of the rebuild of the last level. -/
  lastSpaceDom : ∀ (gB lB h : ℕ), lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace
  /-- The total space. -/
  spaceTotal :
    2 * (cfg.P.d + 1) + (5 + fcap + 5 * cfg.P.d) + restartSpace +
      (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d +
      3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ deepSpace
  /-- The live cost of the rebuild of level `j ∈ [i + 1, d)`. -/
  levelCostDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j : ℕ),
    i.val < cfg.P.d → i.val + 1 ≤ j → j < cfg.P.d →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    Psc.mul * cfg.T.cost (next.scState j) +
      ordLevelLiveCost L capExp Psc (next.lvlM j) next.N₀
        (next.G j).n (next.G j).m (next.G (j + 1)).n (next.G (j + 1)).m
        (2 * (next.G j).n + 2 * (next.G j).m + 1)
        (2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m + 1) + 26 ≤
      levelCost model i j
  /-- The total cost without the tree updates, against `deepFixed + toolMul · Δ totalRuntime`. -/
  costTotal : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)),
    i.val < cfg.P.d →
    (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
    SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM i.val) model.chain.N₀
      (model.chain.scState i.val) (model.chain.G i.val) (model.chain.levelOrd i.val)
      (model.chain.updCount i.val) →
    ShiftDeepModelInvKFBL model i →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let Fi0 := (cfg.T.lsfs (model.chain.scState i.val) (model.chain.bran i.val)).F.F
    let H1 := next.G (i.val + 1)
    let LwMax := ordLevelLwMax L capExp (model.chain.lvlM i.val) model.chain.N₀
    copyGraphLiveCost Fi0.n Fi0.m +
      Psc.mul * (cfg.T.cost (next.scState i.val) - cfg.T.cost (model.chain.scState i.val) + 1) +
      Psc.mul * (2 * H1.n + 2 * H1.m + 2) *
        SparseCore.bundleLogFactor (model.chain.lvlM i.val) model.chain.N₀ +
      2 * Psc.readout + copyGraphLiveCost H1.n H1.m +
      H1.m * (wireCoreLenEdgeCost LwMax + 30) +
      (Finset.Ico (i.val + 1) cfg.P.d).sum (fun j => levelCost model i j + 9) +
      lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
      2 * cfg.P.d * (Psc.readout + 48) + 210 * (cfg.P.d + 1) +
      85 * (graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests next i.val)) + 1100 ≤
      deepFixed + toolMul * (next.totalRuntime - model.chain.totalRuntime)

/-- **The deep shift sync under the layout contract.** It is `ShiftDeepChainSyncSpecWExt` with
two more premises, `SolverLevelCapsAt vCap eCap` and `ShiftDeepModelInvKFBL`, and one more
conclusion, `SolverLevelCapsAt vCap eCap` after the shift. So the level graphs keep the caps of
the module from one shift to the next. -/
@[expose] def ShiftDeepChainSyncSpecWExtKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftDeepChainProc : ℕ) (deepSpace deepFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftDeepChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      ShiftDeepModelInv w L P wordExp stretchPrec model i →
      ShiftDeepModelInvKFBL model i →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + deepSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
          mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
        out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
          mem0 (solverSelectBlocksAddr tok.table cfg.P.d) ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        (SolverLevelLayoutAt vCap eCap tok mem0 → SolverLevelLayoutAt vCap eCap tok' out.mem) ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

end MinCostFlow.MinRatio
