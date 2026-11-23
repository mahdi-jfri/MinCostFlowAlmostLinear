module

public import MinCostFlow.MinRatio.InitConcreteWired
public import MinCostFlow.MinRatio.DetectForestAccounts
public import MinCostFlow.MinRatio.OrdSparseCoreHelpers
public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.IPM.Machine.MinRatioContract
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.TreeEditPayloadSave

/-!
# Solver-wide `DSRep` for Algorithm 2 (`SolverStateRep`)

Defines the concrete Word-RAM representation `solverStateRep` of `Alg2State cfg`
rooted at the 16-word `SolverRootDirAt` directory. Every live external edge
`e ∈ model.extG.E` (internal ID `e_int = model.extToInt e`) has its flow and
detection residual maintained either:
- inside the Section 6 link-cut path tree (`slots[e_int] ≠ 0`, `names[slot] = e_int`,
  `slotThresholds[slot] = edgeThresholds[e_int]`) when
  `e_int ∈ model.chain.toTreeChain.chainTree.E`, or
- in its explicit `PathEdgeAt` block `edgeRecords[e_int]` (`slots[e_int] = 0`) with
  membership in `offReadyList[0..offReadyCount)` whenever `0 ≤ detector`, when
  `e_int ∉ model.chain.toTreeChain.chainTree.E`.

Pairwise disjointness of all memory regions (directory, headers, tables, edge blocks,
path tree, sparse cores, and terminal level) is witnessed cleanly by a single ghost
region-tag map `tok.tag : ℕ → ℕ` (`SolverTagsAt`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program IPM.Machine SparseCore.Program

/-- Zero-initialized and dynamically updated Algorithm 2 schedule block at `levelsEnd`
(`4 * (d + 1) + 1` words): `passes[0..d]`, `shiftCount[0..d]`, `rebuildCount[0..d]`,
`updCount[0..d]`, and `branD`. -/
@[expose] def SolverScheduleAt {cfg : Alg2Config} (mem : ℕ → ℕ) (levelsEnd : ℕ)
    (model : Alg2State cfg) : Prop :=
  let d := cfg.P.d
  (∀ i : Fin (d + 1), mem (levelsEnd + i.val) = model.passes i) ∧
  (∀ i ≤ d, mem (levelsEnd + (d + 1) + i) = model.chain.shiftCount i) ∧
  (∀ i ≤ d, mem (levelsEnd + 2 * (d + 1) + i) = model.chain.rebuildCount i) ∧
  (∀ i ≤ d, mem (levelsEnd + 3 * (d + 1) + i) = model.chain.updCount i) ∧
  mem (levelsEnd + 4 * (d + 1)) = model.branD

/-- Deduplicated pending off-tree edge list `offReadyList[0..offReadyCount)` synchronized
with the membership bit array `inOffReady[0..intCap)`. -/
@[expose] def OffReadyInv (mem : ℕ → ℕ) (offReadyCount offReadyList inOffReady intCap : ℕ) : Prop :=
  offReadyCount ≤ intCap ∧
  (∀ j < offReadyCount, mem (offReadyList + j) < intCap ∧
    mem (inOffReady + mem (offReadyList + j)) = 1) ∧
  (∀ j₁ < offReadyCount, ∀ j₂ < offReadyCount, j₁ ≠ j₂ →
    mem (offReadyList + j₁) ≠ mem (offReadyList + j₂)) ∧
  (∀ e < intCap, mem (inOffReady + e) = 0 ∨ mem (inOffReady + e) = 1) ∧
  (∀ e < intCap, mem (inOffReady + e) = 1 →
    ∃ j < offReadyCount, mem (offReadyList + j) = e)

/-- Unified flow, detection residual, and threshold invariant for all live edges
`e ∈ model.extG.E`, partitioned cleanly between tree edges (in `tree`) and off-tree
edges (in `edgeRecords`). -/
@[expose] def SolverEdgeAccountsAt {cfg : Alg2Config} (model : Alg2State cfg) (L P : ℕ)
    (mem : ℕ → ℕ) (slots names slotThresholds edgeThresholds edgeRecords inOffReady : ℕ)
    (intCap : ℕ) (tree : PathTreeState) (trees : List AuxTree) : Prop :=
  (∀ e ∈ model.extG.E,
    let ei := model.extToInt e
    ei < intCap ∧
    PathIntAt mem (mem (edgeThresholds + ei)) 4 L (detectorThreshold P cfg.ε (model.extℓ e)) ∧
    (if ei ∈ model.chain.toTreeChain.chainTree.E then
      let slot := mem (slots + ei)
      slot ≠ 0 ∧ isEdgeSlot tree.n slot ∧
      mem (names + slot) = ei ∧
      mem (slotThresholds + slot) = mem (edgeThresholds + ei) ∧
      ∃ val : PathEdgeValue, ∃ account : ℤ,
        (slot, some val) ∈ forestPairs pathPayload tree.splay trees ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (account : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        val.detector = account - detectorThreshold P cfg.ε (model.extℓ e)
    else
      mem (slots + ei) = 0 ∧
      ∃ val : PathEdgeValue, ∃ account : ℤ,
        PathEdgeAt mem (mem (edgeRecords + ei)) 4 L (some val) ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (account : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        val.detector = account - detectorThreshold P cfg.ε (model.extℓ e) ∧
        (0 ≤ val.detector → mem (inOffReady + ei) = 1))) ∧
  (∀ slot val, isEdgeSlot tree.n slot →
    (slot, some val) ∈ forestPairs pathPayload tree.splay trees →
    let ei := mem (names + slot)
    let e := model.intToExt ei
    ei < intCap ∧ ei ∈ model.chain.toTreeChain.chainTree.E ∧
    mem (slots + ei) = slot ∧ e ∈ model.extG.E ∧ model.extToInt e = ei)

/-- Concrete memory token carried by `solverStateRep` across `Init`, `Update`, `Query`,
and `Detect`. `owned` tracks owned addresses and `tag` assigns distinct nonzero region
tags (`1 .. 19` and `20 + i`) to every disjoint memory region. -/
structure SolverToken (cfg : Alg2Config) (L : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) where
  handle : ℕ
  table : ℕ
  levelsEnd : ℕ
  forward : ℕ
  inverse : ℕ
  freshCounter : ℕ
  slots : ℕ
  names : ℕ
  slotThresholds : ℕ
  edgeThresholds : ℕ
  edgeRecords : ℕ
  offReadyCount : ℕ
  offReadyList : ℕ
  inOffReady : ℕ
  rootGraph : ℕ
  rootECap : ℕ
  intCap : ℕ
  treeHeap : ℕ
  searchSpace : ℕ
  readSpace : ℕ
  alphaPtr : ℕ
  tree : PathTreeState
  trees : List AuxTree
  free : List ℕ
  depth : ℕ → ℕ
  treeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ
  coreHandle : ℕ → ℕ
  coreTok : ℕ → Rcore.τ
  termHandle : ℕ
  vcLast : ℕ
  ecLast : ℕ
  termTok : ℕ
  owned : ℕ → Prop
  tag : ℕ → ℕ

/-- Helper: `LastLevelProgram.lastLevelRepresentation` footprint is independent of the
precision parameter `P` (it depends only on `vCap`, `eCap`, `h`, `L`, and `E`). -/
theorem lastLevelRepresentation_foot_indep_P (vc ec h L P₁ P₂ : ℕ) (E : Finset ℕ)
    (handle tok a : ℕ) :
    (LastLevelProgram.lastLevelRepresentation vc ec h L P₁ E).foot handle tok a ↔
      (LastLevelProgram.lastLevelRepresentation vc ec h L P₂ E).foot handle tok a := by
  rfl

/-- Ghost region-tag assignment guaranteeing both ownership (`tag a ≠ 0 → owned a`)
and pairwise disjointness of all 19 solver regions plus every core level `20 + i`.
Region tags:
- `1`: `SolverRootDirAt` `[root, root + 16)`
- `2`: `DetectHeaderAt`/`MinRatioNumericHeaderAt`/`SolverChainHeaderAt` `[handle, handle + 18)`
- `3`: rebuild threshold table `[table, table + d + 1)`
- `4`: `levelTable` `[handle + 18, handle + 18 + 2 * (d + 1))`
- `5`: schedule block `[levelsEnd, levelsEnd + 4 * (d + 1) + 1)`
- `6`: `freshCounter`
- `7`: `forward[0..m)`
- `8`: `inverse[0..intCap)`
- `9`: `slots[0..intCap)`
- `10`: `names[0..2*tree.n)`
- `11`: `slotThresholds[0..2*tree.n)`
- `12`: `edgeThresholds[0..intCap)`
- `13`: `edgeRecords[0..intCap)`
- `14`: `offReadyList[0..intCap)`
- `15`: `inOffReady[0..intCap)`
- `16`: `Rtree.foot tok.treeHeap tok.treeTok`
- `17`: live `edgeThresholds[ei]` `L`-limb blocks
- `18`: live off-tree `edgeRecords[ei]` `(2 + 4 * L)`-word blocks
- `19`: terminal level `Rterm.foot`
- `20`: root dynamic graph `[rootGraph, rootGraph + dynGraphSize extG.n rootECap)`
- `21 + i`: sparse-core level `i < d` `Rcore.foot` -/
@[expose] def SolverTagsAt {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (root m : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (mem : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let levelTable := tok.handle + 18
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let Rterm := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L
    (0 : ℕ) (model.chain.G d).E
  (∀ a, tok.tag a ≠ 0 → tok.owned a) ∧
  (∀ j < 16, tok.tag (root + j) = 1) ∧
  (∀ j < 18, tok.tag (tok.handle + j) = 2) ∧
  (∀ j ≤ d, tok.tag (tok.table + j) = 3) ∧
  (∀ j < 2 * (d + 1), tok.tag (levelTable + j) = 4) ∧
  (∀ j < 4 * (d + 1) + 1, tok.tag (tok.levelsEnd + j) = 5) ∧
  tok.tag tok.freshCounter = 6 ∧
  (∀ j < m, tok.tag (tok.forward + j) = 7) ∧
  (∀ j < tok.intCap, tok.tag (tok.inverse + j) = 8) ∧
  (∀ j < tok.intCap, tok.tag (tok.slots + j) = 9) ∧
  (∀ j < 2 * tok.tree.n, tok.tag (tok.names + j) = 10) ∧
  (∀ j < 2 * tok.tree.n, tok.tag (tok.slotThresholds + j) = 11) ∧
  (∀ j < tok.intCap, tok.tag (tok.edgeThresholds + j) = 12) ∧
  (∀ j < tok.intCap, tok.tag (tok.edgeRecords + j) = 13) ∧
  (∀ j < tok.intCap, tok.tag (tok.offReadyList + j) = 14) ∧
  (∀ j < tok.intCap, tok.tag (tok.inOffReady + j) = 15) ∧
  (∀ a, Rtree.foot tok.treeHeap tok.treeTok a → tok.tag a = 16) ∧
  (∀ e ∈ model.extG.E,
    let ei := model.extToInt e
    (∀ j < L, tok.tag (mem (tok.edgeThresholds + ei) + j) = 17) ∧
    (ei ∉ model.chain.toTreeChain.chainTree.E →
      ∀ j < 2 + 4 * L, tok.tag (mem (tok.edgeRecords + ei) + j) = 18)) ∧
  (∀ a, Rterm.foot tok.termHandle tok.termTok a → tok.tag a = 19) ∧
  (∀ a, tok.rootGraph ≤ a → a < tok.rootGraph + dynGraphSize model.extG.n tok.rootECap →
    tok.tag a = 20) ∧
  (∀ i < d, ∀ a, Rcore.foot (tok.coreHandle i) (tok.coreTok i) a → tok.tag a = 21 + i)

/-- Original-direction gradient of a `PathEdgeValue`. -/
@[expose] def PathEdgeValue.originalGradient (v : PathEdgeValue) : ℤ :=
  if v.forward then v.gradient else -v.gradient

theorem PathEdgeValue.originalGradient_reverse (v : PathEdgeValue) :
    v.reverse.originalGradient = v.originalGradient := by
  cases h : v.forward <;> simp [PathEdgeValue.originalGradient, PathEdgeValue.reverse, h]

/-- Orientation and original-gradient/length invariant for all live edges in `model`:
- On every tree edge `ei ∈ chainTree.E`, the stored `PathEdgeValue` at `slots[ei]` matches
  `model.extg e`, `model.extℓ e`, and the induced parent orientation of `chainTree`
  (`forward = true` when `tail ei` is the parent of the edge slot and `head ei` is its child,
  `forward = false` when reversed).
- On every off-tree edge `ei ∉ chainTree.E`, the stored `PathEdgeValue` at `edgeRecords[ei]`
  has canonical orientation `forward = true` and matches `model.extg e` and `model.extℓ e`. -/
@[expose] def SolverEdgeOrientInv {cfg : Alg2Config} (L P : ℕ) (model : Alg2State cfg)
    (mem : ℕ → ℕ) (slots edgeRecords : ℕ) (tree : PathTreeState) (trees : List AuxTree) : Prop :=
  let F := model.chain.toTreeChain.chainTree
  let par := inducedSubPar pathPayload tree.splay trees
  ∀ e ∈ model.extG.E,
    let ei := model.extToInt e
    if ei ∈ F.E then
      ∀ val : PathEdgeValue,
        (mem (slots + ei), some val) ∈ forestPairs pathPayload tree.splay trees →
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        (val.forward = true →
          par (vid (F.head ei)) = mem (slots + ei) ∧ par (mem (slots + ei)) = vid (F.tail ei)) ∧
        (val.forward = false →
          par (vid (F.tail ei)) = mem (slots + ei) ∧ par (mem (slots + ei)) = vid (F.head ei))
    else
      ∀ val : PathEdgeValue,
        PathEdgeAt mem (mem (edgeRecords + ei)) 4 L (some val) →
        val.forward = true ∧
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e

/-- Additional wiring invariants carried by `solverStateRep` for `Init`, `ChainRefresh`,
`ShiftLevel`, `FindCycle`, and `GoodCycleNumericBridge`:
1. Exact integer rebuild thresholds `intRebuildThreshold cfg.P cfg.N₀ j` at `tok.table[0..d]`.
2. Root dynamic graph `DynGraphAt` for `model.chain.G 0` at `tok.rootGraph`.
3. `chainTree` is a forest whose edges lie below `tok.intCap` with distinct endpoints `< extG.n`.
4. `TreeEditNamedSlots` links `tok.tree` slots to `model.chain.toTreeChain.chainTree`.
5. `SolverEdgeOrientInv` gives orientation, gradient, and length agreement on every live edge. -/
@[expose] def SolverWireInv {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) : Prop :=
  let F := model.chain.toTreeChain.chainTree
  (∀ j ≤ cfg.P.d, mem (tok.table + j) = intRebuildThreshold cfg.P cfg.N₀ j) ∧
  DynGraphAt mem tok.rootGraph model.extG.n tok.rootECap (model.chain.G 0) ∧
  (F.IsForest ∧ ∀ ei ∈ F.E, ei < tok.intCap ∧ F.tail ei < model.extG.n ∧
    F.head ei < model.extG.n ∧ F.tail ei ≠ F.head ei) ∧
  TreeEditNamedSlots tok.tree tok.trees F
    (fun ei => mem (tok.slots + ei)) (fun slot => mem (tok.names + slot)) ∧
  SolverEdgeOrientInv L P model mem tok.slots tok.edgeRecords tok.tree tok.trees

/-- Concrete representation of `Alg2State cfg` rooted at `SolverRootDirAt root`.
Parameter `drainUnit` is the per-entry potential unit paid on push into `offReadyList`
so `Detect` drains stale off-tree entries in `O(1)` amortized time. The name tables have
room for every name handed out so far (`model.nextFresh ≤ tok.intCap`), and every internal name
at or above the table size maps to itself. So a later table growth may fill the new entries with
the identity. A level-`0` rebuild renames the live internal edges (`Chain.Ordered.level0I2E`), so
the names between the new `nextFresh` and the table size need not map to themselves. -/
@[expose] noncomputable def solverStateRep (cfg : Alg2Config) (L P m V psi k epsExp drainUnit : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) : DSRep (Alg2State cfg) where
  τ := SolverToken cfg L Rcore
  rep root model tok mem :=
    let d := cfg.P.d
    let levelTable := tok.handle + 18
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let Rterm := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G d).E
    SolverRootDirAt mem root tok.handle tok.table tok.levelsEnd tok.forward tok.inverse
      tok.freshCounter tok.slots tok.names tok.slotThresholds tok.edgeThresholds tok.edgeRecords
      tok.offReadyCount tok.offReadyList tok.inOffReady tok.rootGraph tok.intCap ∧
    DetectHeaderAt mem tok.handle tok.treeHeap tok.names tok.inverse tok.slotThresholds
      m L tok.searchSpace tok.readSpace ∧
    MinRatioNumericHeaderAt mem tok.handle L P tok.searchSpace tok.readSpace ∧
    SolverChainHeaderAt mem tok.handle m V d cfg.P.k psi tok.alphaPtr k epsExp
      (Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
    FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh ∧
    FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      model.extToInt model.intToExt model.nextFresh ∧
    (∀ e ∈ model.extG.E, e < m) ∧
    ((∀ e ∈ (model.chain.G 0).E, e < tok.intCap) ∧ 0 < tok.intCap ∧
      model.nextFresh ≤ tok.intCap ∧ ∀ j ≥ tok.intCap, model.intToExt j = j) ∧
    SolverScheduleAt mem tok.levelsEnd model ∧
    OffReadyInv mem tok.offReadyCount tok.offReadyList tok.inOffReady tok.intCap ∧
    tok.tree.n = model.extG.n ∧
    LctInvWith pathPayload tok.tree tok.trees tok.free tok.depth ∧
    Rtree.rep tok.treeHeap tok.tree tok.treeTok mem ∧
    SolverEdgeAccountsAt model L P mem tok.slots tok.names tok.slotThresholds
      tok.edgeThresholds tok.edgeRecords tok.inOffReady tok.intCap tok.tree tok.trees ∧
    (∀ i < d, mem (levelTable + i) = tok.coreHandle i ∧
      mem (levelTable + (d + 1) + i) = model.chain.bran i ∧
      Rcore.rep (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok.coreTok i) mem) ∧
    mem (levelTable + d) = tok.termHandle ∧
    mem (levelTable + (d + 1) + d) = model.chain.lastBran ∧
    Rterm.rep tok.termHandle (model.chain.lastK, model.chain.lastLSFs) tok.termTok mem ∧
    SolverWireInv P model tok mem ∧
    SolverTagsAt root m model tok mem
  foot _ tok a :=
    tok.owned a ∨
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
    ∃ i < cfg.P.d, Rcore.foot (tok.coreHandle i) (tok.coreTok i) a
  phi _ tok mem :=
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) +
      tok.offReadyCount * drainUnit

private theorem listAt_congr {mem mem' : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) :
    ListAt mem' base xs := fun j hj => (hag j hj).trans (h j hj)

/-- Helper: one direction of `rep` agreement for `solverStateRep_local`. -/
private theorem solverStateRep_rep_imp {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem₁ mem₂ : ℕ → ℕ}
    (hag : ∀ a, tok.owned a → mem₂ a = mem₁ a)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₁) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₂ := by
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, hlctInv, htreeRep, hedgeAcc, hcores, htermH, htermBr,
    htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : mem₂ a = mem₁ a :=
    hag a (hOwn a (ht ▸ hv))
  have hmem_et (e : ℕ) (he : e ∈ model.extG.E) :
      mem₂ (tok.edgeThresholds + model.extToInt e) =
        mem₁ (tok.edgeThresholds + model.extToInt e) :=
    hagT (t12 _ (hedgeAcc.1 e he).1) (by decide)
  have hmem_er (e : ℕ) (he : e ∈ model.extG.E) :
      mem₂ (tok.edgeRecords + model.extToInt e) =
        mem₁ (tok.edgeRecords + model.extToInt e) :=
    hagT (t13 _ (hedgeAcc.1 e he).1) (by decide)
  have htreeRep₂ : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep
      tok.treeHeap tok.tree tok.treeTok mem₂ :=
    (htreeLocal tok.treeHeap tok.tree tok.treeTok mem₁ mem₂
      (fun a ha => (hagT (t16 a ha) (by decide)).symm)).1 htreeRep
  have htermRep₂ : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E).rep tok.termHandle (model.chain.lastK, model.chain.lastLSFs)
      tok.termTok mem₂ :=
    (htermLocal tok.termHandle _ tok.termTok mem₁ mem₂
      (fun a ha => (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
        (by decide)).symm)).1 htermRep
  refine ⟨listAt_congr hrootDir (fun j hj => hagT (t1 j (by simpa [List.length] using hj)) (by decide)),
    listAt_congr hdetect (fun j hj => hagT (t2 j (by simp [List.length] at hj; omega)) (by decide)),
    listAt_congr hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hagT (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide)),
    listAt_congr hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact hagT (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide)),
    hfreshInv,
    ⟨(hagT t6 (by decide)).trans hfreshTab.1,
      fun e he => (hagT (t7 e he) (by decide)).trans (hfreshTab.2.1 e he),
      fun e he => (hagT (t8 e he) (by decide)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hagT (t5 i.val (by omega)) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide)).trans hsched.2.2.2.2⟩,
    ?_, htn, hlctInv, htreeRep₂, ?_, ?_,
    (hagT (t4 cfg.P.d (by omega)) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide)).trans htermBr,
    htermRep₂,
    ?_,
    ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16,
      fun e he => by dsimp only; rw [hmem_et e he, hmem_er e he]; exact t1718 e he, t19, t20, t21⟩⟩
  · obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hoffReady
    refine ⟨hcnt, fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_, fun e he => ?_, fun e he h1 => ?_⟩
    · rw [hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide)]
      exact ⟨(hmemL j hj).1, (hagT (t15 _ (hmemL j hj).1) (by decide)).trans (hmemL j hj).2⟩
    · rw [hagT (t14 j₁ (lt_of_lt_of_le hj₁ hcnt)) (by decide),
          hagT (t14 j₂ (lt_of_lt_of_le hj₂ hcnt)) (by decide)]
      exact hdist j₁ hj₁ j₂ hj₂ hne
    · rw [hagT (t15 e he) (by decide)]; exact hbits e he
    · rw [hagT (t15 e he) (by decide)] at h1
      obtain ⟨j, hj, hje⟩ := hrev e he h1
      exact ⟨j, hj, (hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide)).trans hje⟩
  · refine ⟨fun e he => ?_, fun slot val hslot hpair => ?_⟩
    · obtain ⟨heiCap, hthr, hbranch⟩ := hedgeAcc.1 e he
      refine ⟨heiCap, ?_, ?_⟩
      · rw [hmem_et e he]
        exact hthr.congr (fun j hj => hagT ((t1718 e he).1 j hj) (by decide))
      · split_ifs at hbranch ⊢ with hin
        · obtain ⟨hsnz, his, hnm, hst, hval⟩ := hbranch
          have hslotLt : mem₁ (tok.slots + model.extToInt e) < 2 * tok.tree.n := by
            unfold isEdgeSlot at his; omega
          rw [hagT (t9 _ heiCap) (by decide), hmem_et e he]
          exact ⟨hsnz, his,
            (hagT (t10 _ hslotLt) (by decide)).trans hnm,
            (hagT (t11 _ hslotLt) (by decide)).trans hst, hval⟩
        · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet, hpush⟩ := hbranch
          rw [hmem_er e he]
          refine ⟨(hagT (t9 _ heiCap) (by decide)).trans hs0, val, acc,
            hrec.congr (fun x hxlo hxhi => by
              have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
                  (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
              rw [hx]; exact hagT ((t1718 e he).2 hin _ (by omega)) (by decide)),
            hfl, hac, hdet, fun hnn => (hagT (t15 _ heiCap) (by decide)).trans (hpush hnn)⟩
    · have hslotLt : slot < 2 * tok.tree.n := by unfold isEdgeSlot at hslot; omega
      obtain ⟨heiCap, hin, hsl, heE, he2i⟩ := hedgeAcc.2 slot val hslot hpair
      rw [hagT (t10 slot hslotLt) (by decide)]
      exact ⟨heiCap, hin, (hagT (t9 _ heiCap) (by decide)).trans hsl, heE, he2i⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hagT (t4 i (by omega)) (by decide)).trans hh,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide)).trans hbr,
      (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem₁ mem₂
        (fun a ha => (hagT (t21 i hi a ha) (by omega)).symm)).1 hcr⟩
  · obtain ⟨htabW, hrgW, hsubCap, hnsW, hglW⟩ := hwire
    refine ⟨fun j hj => (hagT (t3 j hj) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide)), hsubCap,
      ⟨fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide)]
          have hfwd := hnsW.forward ei hei
          have hslotLt : mem₁ (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1, (hagT (t10 _ hslotLt) (by decide)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tok.tree.n := by unfold isEdgeSlot at hks; omega
          rw [hagT (t10 k hkLt) (by decide)]
          obtain ⟨hmem, hslot⟩ := hnsW.inverse k hk hks
          exact ⟨hmem, (hagT (t9 _ (hsubCap.2 _ hmem).1) (by decide)).trans hslot⟩,
        fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide)]; exact hnsW.endpoints ei hei⟩,
      fun e he => by
        dsimp only
        have hgl := hglW e he
        dsimp only at hgl
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs at hgl ⊢ with hin
        · rw [hagT (t9 _ heiCap) (by decide)]; exact hgl
        · intro val hpa
          rw [hmem_er e he] at hpa
          exact hgl val (hpa.congr fun x hlo hhi => by
            have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
                (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hagT ((t1718 e he).2 hin _ (by omega)) (by decide)).symm)⟩

/-- `solverStateRep` is local whenever `Rcore` is local: every word read by `rep` and `phi`
lies inside `foot`. -/
theorem solverStateRep_local (cfg : Alg2Config) (L P m V psi k epsExp drainUnit : ℕ)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).Local := by
  intro root model tok mem₁ mem₂ hag
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  constructor
  · exact solverStateRep_rep_imp hlocalCore (fun a ha => (hag a (Or.inl ha)).symm)
  · have hphiTree : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem₁ =
        (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem₂ :=
      (htreeLocal tok.treeHeap tok.tree tok.treeTok mem₁ mem₂
        (fun a ha => hag a (Or.inr (Or.inl ha)))).2
    have hphiCores : (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem₁) =
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem₂) :=
      Finset.sum_congr rfl fun i _ =>
        (hlocalCore (tok.coreHandle i.val) (chainLevelOrdAbs model.chain i.val) (tok.coreTok i.val) mem₁ mem₂
          (fun a ha => hag a (Or.inr (Or.inr ⟨i.val, i.isLt, ha⟩)))).2
    dsimp only [solverStateRep]
    rw [hphiTree, hphiCores]

/-- `Chain.Ordered.algorithm2_init` always has zero initial flow on every edge, so `MinRatioStateFits`
holds unconditionally for every `h, L`. -/
theorem algorithm2_init_stateFits {cfg : Alg2Config} {G : MGraph} {g₀ ℓ₀ : ℕ → ℝ} {κ : ℝ}
    {h L P : ℕ} :
    MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G h L P
      (Chain.Ordered.algorithm2_init cfg G g₀ ℓ₀) := by
  intro e _
  refine ⟨0, ?_, by simp [Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith,
    algorithm2_query, Chain.Ordered.algorithm2_init]⟩
  have hcap : (0 : ℤ) < (Num.capacity h L : ℤ) := by
    unfold Num.capacity Num.base; exact_mod_cast Nat.pow_pos (Nat.two_pow_pos h)
  exact ⟨by omega, by omega⟩

/-- Helper: given any live `model : Alg2State cfg` represented by `solverStateRep` at `root`,
extract the exact `Query` flow representation on edge `e ∈ model.extG.E` in both the tree
branch (`mem (slots + ei) ≠ 0`) and the off-tree branch (`mem (slots + ei) = 0`). -/
theorem solverStateRep_query_edge {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root e : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (he : e ∈ model.extG.E) :
    let ei := model.extToInt e
    mem (tok.forward + e) = ei ∧ ei < tok.intCap ∧
    (if mem (tok.slots + ei) ≠ 0 then
      let slot := mem (tok.slots + ei)
      isEdgeSlot tok.tree.n slot ∧
      ∃ val : PathEdgeValue,
        ((lctExpose pathPayload tok.tree slot).splay.nodes slot).val = some val ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = algorithm2_query cfg model e
    else
      ∃ val : PathEdgeValue,
        PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some val) ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = algorithm2_query cfg model e) := by
  obtain ⟨_, _, _, _, _, hfreshTab, hextM, _, _, _, _, hlctInv, _, hedgeAcc, _⟩ := hrep
  obtain ⟨heiCap, _, hbranch⟩ := hedgeAcc.1 e he
  refine ⟨hfreshTab.2.1 e (hextM e he), heiCap, ?_⟩
  by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
  · rw [ite_eq_left hin] at hbranch
    obtain ⟨hsnz, his, _, _, val, _, hpair, hflow, _, _⟩ := hbranch
    rw [ite_eq_left hsnz]
    exact ⟨his, val, pathTreeExpose_value_of_forestPair hlctInv hpair, hflow⟩
  · rw [ite_eq_right hin] at hbranch
    obtain ⟨hs0, val, _, hrec, hflow, _, _, _⟩ := hbranch
    rw [ite_eq_right (not_not.mpr hs0)]
    exact ⟨val, hrec, hflow⟩

/-- Helper: under `solverStateRep`, every live edge `e ∈ model.extG.E` satisfies the exact
`algorithm2_detect` membership test via either `pathTreeReady tok.tree (mem (tok.slots + ei))`
(for tree edges) or `0 ≤ val.detector` on `edgeRecords[ei]` (for off-tree edges). -/
theorem solverStateRep_detect_iff {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root e : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (he : e ∈ model.extG.E) (heps : 0 < cfg.ε) (hlen : 0 < model.extℓ e) :
    let ei := model.extToInt e
    if ei ∈ model.chain.toTreeChain.chainTree.E then
      pathTreeReady tok.tree (mem (tok.slots + ei)) ↔ e ∈ (algorithm2_detect cfg model).1
    else
      ∃ val : PathEdgeValue,
        PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some val) ∧
        (0 ≤ val.detector ↔ e ∈ (algorithm2_detect cfg model).1) ∧
        (0 ≤ val.detector → mem (tok.inOffReady + ei) = 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlctInv, _, hedgeAcc, _⟩ := hrep
  obtain ⟨_, _, hbranch⟩ := hedgeAcc.1 e he
  have hmem_det (acc : ℤ) (val : PathEdgeValue)
      (hac : (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e)
      (hd : val.detector = acc - detectorThreshold P cfg.ε (model.extℓ e)) :
      0 ≤ val.detector ↔ e ∈ (algorithm2_detect cfg model).1 := by
    have hres := detect_residual_pending model (reported := ∅) he heps hlen
      (by simpa [resetReported] using hac) hd
    simpa using hres
  by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
  · rw [ite_eq_left hin] at hbranch ⊢
    obtain ⟨_, his, _, _, val, acc, hpair, _, hac, hd⟩ := hbranch
    have hv := pathTreeExpose_value_of_forestPair hlctInv hpair
    have hr : pathTreeReady tok.tree (mem (tok.slots + model.extToInt e)) ↔ 0 ≤ val.detector := by
      constructor
      · rintro ⟨_, _, v, hv', hn⟩
        exact Option.some.inj (hv'.symm.trans hv) ▸ hn
      · intro hn
        exact (pathTreeReady_iff_forestPairs hlctInv _).2 ⟨his, val, hpair, hn⟩
    exact hr.trans (hmem_det acc val hac hd)
  · rw [ite_eq_right hin] at hbranch ⊢
    obtain ⟨_, val, acc, hrec, _, hac, hd, hpush⟩ := hbranch
    exact ⟨val, hrec, hmem_det acc val hac hd, hpush⟩

/-- Uniqueness of evaluated `PathEdgeValue` per active slot in `forestPairs`. -/
theorem forestPairs_val_unique {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ} {v₁ v₂ : PathEdgeValue}
    (hW : LctInvWith pathPayload s trees free depth)
    (h1 : (slot, some v₁) ∈ forestPairs pathPayload s.splay trees)
    (h2 : (slot, some v₂) ∈ forestPairs pathPayload s.splay trees) : v₁ = v₂ := by
  have he1 := pathTreeExpose_value_of_forestPair hW h1
  have he2 := pathTreeExpose_value_of_forestPair hW h2
  exact Option.some.inj (he1.symm.trans he2)

/-- Two `PathEdgeAt` decodings at the same memory block agree on `forward`, `originalGradient`,
and `length`. -/
theorem pathEdgeAt_fwd_grad_len_eq {mem : ℕ → ℕ} {a h L : ℕ} {v₁ v₂ : PathEdgeValue}
    (h1 : PathEdgeAt mem a h L (some v₁)) (h2 : PathEdgeAt mem a h L (some v₂)) :
    v₁.forward = v₂.forward ∧ v₁.originalGradient = v₂.originalGradient ∧ v₁.length = v₂.length := by
  have hdir : (if v₁.forward then 1 else 0) = (if v₂.forward then 1 else 0) :=
    h1.2.1.symm.trans h2.2.1
  have hfwd : v₁.forward = v₂.forward := by cases hd1 : v₁.forward <;> cases hd2 : v₂.forward <;> simp_all
  have hg : v₁.gradient = v₂.gradient := h1.2.2.1.2.symm.trans h2.2.2.1.2
  have hl : v₁.length = v₂.length := h1.2.2.2.1.2.symm.trans h2.2.2.2.1.2
  refine ⟨hfwd, ?_, hl⟩
  unfold PathEdgeValue.originalGradient
  rw [hfwd, hg]

/-- Two `PathEdgeAt` decodings at the same memory block agree on `originalGradient` and `length`. -/
theorem pathEdgeAt_grad_len_eq {mem : ℕ → ℕ} {a h L : ℕ} {v₁ v₂ : PathEdgeValue}
    (h1 : PathEdgeAt mem a h L (some v₁)) (h2 : PathEdgeAt mem a h L (some v₂)) :
    v₁.originalGradient = v₂.originalGradient ∧ v₁.length = v₂.length :=
  (pathEdgeAt_fwd_grad_len_eq h1 h2).2

/-- `inducedSubPar` is preserved across any `LctInvWith` witness of `lctExpose`. -/
theorem inducedSubPar_expose_witness {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {x : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hi' : LctInvWith pathPayload (lctExpose pathPayload s x) trees' free depth) :
    inducedSubPar pathPayload (lctExpose pathPayload s x).splay trees' =
      inducedSubPar pathPayload s.splay trees := by
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
  obtain ⟨ts, _, _, hInv, _, hPar, _, _⟩ := lctExpose_spec pathPayload_laws hi ht hxt
  obtain ⟨_, hPar2⟩ := treeEdit_witness_agreement hInv hi'
  funext z
  change inducedSubPar pathPayload (lctExposeCost pathPayload s x).1.splay trees' z = _
  rw [← hPar2]; exact hPar z

/-- `inducedSubPar` is preserved across any `LctInvWith` witness of `pathTreeWrite`. -/
theorem inducedSubPar_write_witness {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {x : ℕ} {value : Option PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hi' : LctInvWith pathPayload (pathTreeWrite s x value) trees' free depth) :
    inducedSubPar pathPayload (pathTreeWrite s x value).splay trees' =
      inducedSubPar pathPayload s.splay trees := by
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
  obtain ⟨tsW, hInvW, _, hParW⟩ := pathTreeWrite_inducedSubPar hi ht hxt value
  obtain ⟨_, hPar2⟩ := treeEdit_witness_agreement hInvW hi'
  funext z
  rw [← hPar2]; exact hParW z

/-- Transport `TreeEditNamedSlots` across any `LctInvWith` witness of `lctExpose`. -/
theorem treeEditNamedSlots_expose_witness {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {x : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hi' : LctInvWith pathPayload (lctExpose pathPayload s x) trees' free depth) :
    TreeEditNamedSlots (lctExpose pathPayload s x) trees' G slot name := by
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
  obtain ⟨ts, _, _, hInv, hPerm, hPar, _, _⟩ := lctExpose_spec pathPayload_laws hi ht hxt
  obtain ⟨hPerm2, hPar2⟩ := treeEdit_witness_agreement hInv hi'
  have hActive : (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
    hPerm2.symm.trans hPerm
  refine ⟨fun f hf => ?_, fun k hk hs => hn.inverse k (hActive.mem_iff.mp hk) hs, fun f hf => ?_⟩
  · obtain ⟨ha, hs, hnm⟩ := hn.forward f hf
    exact ⟨hActive.mem_iff.mpr ha, hs, hnm⟩
  · have he := hn.endpoints f hf
    dsimp only at he ⊢
    have hEq : inducedSubPar pathPayload (lctExpose pathPayload s x).splay trees' =
        inducedSubPar pathPayload s.splay trees := funext fun z => by
      change inducedSubPar pathPayload (lctExposeCost pathPayload s x).1.splay trees' z = _
      rw [← hPar2]; exact hPar z
    rw [hEq]; exact he

/-- Transport `TreeEditNamedSlots` across any `LctInvWith` witness of `pathTreeWrite`. -/
theorem treeEditNamedSlots_write_witness {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {x : ℕ}
    {value : Option PathEdgeValue}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hi' : LctInvWith pathPayload (pathTreeWrite s x value) trees' free depth) :
    TreeEditNamedSlots (pathTreeWrite s x value) trees' G slot name := by
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
  obtain ⟨tsW, hInvW, hPermW, hParW⟩ := pathTreeWrite_inducedSubPar hi ht hxt value
  obtain ⟨hPerm2, hPar2⟩ := treeEdit_witness_agreement hInvW hi'
  have hActive : (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
    hPerm2.symm.trans hPermW
  refine ⟨fun f hf => ?_, fun k hk hs => hn.inverse k (hActive.mem_iff.mp hk) hs, fun f hf => ?_⟩
  · obtain ⟨ha, hs, hnm⟩ := hn.forward f hf
    exact ⟨hActive.mem_iff.mpr ha, hs, hnm⟩
  · have he := hn.endpoints f hf
    dsimp only at he ⊢
    have hEq : inducedSubPar pathPayload (pathTreeWrite s x value).splay trees' =
        inducedSubPar pathPayload s.splay trees := funext fun z => by
      rw [← hPar2]; exact hParW z
    rw [hEq]; exact he

end MinCostFlow.MinRatio
