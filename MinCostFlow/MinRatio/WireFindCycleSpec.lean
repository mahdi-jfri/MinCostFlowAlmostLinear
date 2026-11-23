module

public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.ShiftLoopLevelFacts
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve

/-!
# Corrected specs of the cycle finder

The cycle finder of Algorithm 2 (page 29, `FindCycle` of Algorithm 1, page 21) has two inner
parts in `OrdFindCycleWired.lean`: `OrdCycleRouteSelectSpec` (choose the cycle and write its
off-tree edges and its tree paths) and `OrdCycleRouteEvalSpec` (write the gradient inner product
and the weighted length of the cycle). `OrdCycleRouteEvalSpec` cannot be met as stated, for two
reasons.

1. It must write `inner` and `norm` in `L` limbs, but nothing bounds them. Each stored gradient and
   length fits in `L` limbs, but their sum over the cycle need not. `OffTreeRecInv` bounds only
   the detector of the off-tree records.
2. `CycleRouteAt` allows the same edge twice in `edges`, once in each direction. Then the edge
   counts zero times in `lnorm`, while a sum of the record lengths counts it twice.

This file states the corrected specs.

* `OrdCycleRouteSelectSpecW`: as `OrdCycleRouteSelectSpec`, and also: the edge names in `edges`
  are distinct, `OffTreeRecBound` and the cap facts `WireCapFacts` are kept (the second is
  needed since the selection reads the levels of the chain from the sparse-core module), and the
  capacity of the name tables does not change.
* `OrdCycleRouteEvalSpecW`: as `OrdCycleRouteEvalSpec`, with the hypotheses that the edge names
  are distinct, that `OffTreeRecBound` holds, that `Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L`
  (needed by the path-tree contract and budget), that edge lengths are nonnegative (needed for
  `0 ≤ norm`), and that the capacity of `L` limbs covers the sums:
  `2 ((maxEdges + maxPaths · n) B) < capacity` for the cycle sums and
  `2 (2n + 1) (B + R) < capacity` for the tree operations. It keeps `OffTreeRecBound` and the
  capacity of the name tables.
* `FindCycleStepSpecW`: `FindCycleStepSpec` with the same new hypotheses and conclusions.

The specs of the selector and of the finder also ask `ShiftLoopLevelFacts cfg model.chain`
(`ShiftLoopLevelFacts.lean`): every level graph has `n ≤ m + 1`, and the level sizes and the vertex
bound are those of the configuration. The selection reads the levels from the sparse-core module,
and the module meets its contract only at such graphs and sizes. The loop of `Update` has the fact
from `ShiftLoopChainInv` (`shiftLoopLevelFacts_of_inv`).

The wired finder `ordFindCycleWiredBody` meets `FindCycleStepSpecW` when its two parts meet the
corrected specs (`findCycleStepSpecW_wired`, `WireFindCycle.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- An explicit off-tree edge list `edges` contains no opposite-orientation pair `(e, true)` and
`(e, false)` for the same edge ID `e`. -/
@[expose] def NoOppositePairs (edges : List (ℕ × Bool)) : Prop :=
  ∀ x ∈ edges, (x.1, !x.2) ∉ edges

/-- The corrected contract of the route selector `selectRouteProc [root, descBase, workHeap]`.
It is `OrdCycleRouteSelectSpec` with three more hypotheses (`OffTreeRecBound`, `WireCapFacts`)
and four more conclusions: `edges` has no opposite-orientation pairs (`NoOppositePairs`), the
capacity `intCap` of the name tables is kept, and so is `OffTreeRecBound`. -/
@[expose] def OrdCycleRouteSelectSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (selectRouteProc selectSpace selectBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[selectRouteProc]? = some body ∧
    ∀ (root descBase workHeap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      ShiftLoopLevelFacts cfg model.chain →
      (∀ a, Rrep.foot root tok a → a < descBase) →
      descBase + 6 = workHeap →
      ZeroFrom mem descBase →
      workHeap + selectSpace < 2 ^ w →
      ∃ work1 cost out tok' edges paths,
        Runs w p ω body (startState [root, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        workHeap ≤ work1 ∧ work1 ≤ workHeap + selectSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        NoOppositePairs edges ∧
        workHeap ≤ out.mem (descBase + 2) ∧
        out.mem (descBase + 2) + 2 * edges.length ≤ work1 ∧
        out.mem (descBase + 3) = edges.length ∧
        workHeap ≤ out.mem (descBase + 4) ∧
        out.mem (descBase + 4) + 2 * paths.length ≤ work1 ∧
        out.mem (descBase + 5) = paths.length ∧
        ExplicitEdgesAt out.mem (out.mem (descBase + 2)) edges ∧
        PathEndpointsAt out.mem (out.mem (descBase + 4)) paths ∧
        CycleRouteAt model edges paths ∧
        (∀ x < 2 * edges.length, ¬ Rrep.foot root tok' (out.mem (descBase + 2) + x)) ∧
        (∀ x < 2 * paths.length, ¬ Rrep.foot root tok' (out.mem (descBase + 4) + x)) ∧
        (∀ a, tok'.tag a = 18 → a < descBase) ∧
        Rrep.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem work1 ∧
        (∀ a < descBase, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < work1)) ∧
        cost + Rrep.phi root tok' out.mem ≤ selectBudget + Rrep.phi root tok mem

/-- The corrected contract of the evaluator
`evalCycleProc [root, edgesBase, edgesLen, pathsBase, pathsLen, workHeap]`. It is
`OrdCycleRouteEvalSpec` with four more hypotheses: `edges` has no opposite-orientation pairs
(`NoOppositePairs`), the off-tree records meet `OffTreeRecBound`, and `L` limbs hold
`2 ((maxEdges + maxPaths · n) B)` and `2 (2n + 1) (B + R)`. It has two more conclusions: the
capacity `intCap` of the name tables and `OffTreeRecBound` are kept. -/
@[expose] def OrdCycleRouteEvalSpecW (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (evalCycleProc evalSpace evalBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[evalCycleProc]? = some body ∧
    ∀ (root edgesBase pathsBase workHeap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ)
      (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)),
      let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ) →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      (∀ e ∈ model.extG.E, 0 ≤ model.extℓ e) →
      edges.length ≤ maxEdges → paths.length ≤ maxPaths →
      NoOppositePairs edges →
      ExplicitEdgesAt mem edgesBase edges →
      PathEndpointsAt mem pathsBase paths →
      CycleRouteAt model edges paths →
      edgesBase + 2 * edges.length ≤ workHeap →
      pathsBase + 2 * paths.length ≤ workHeap →
      (∀ x < 2 * edges.length, ¬ Rrep.foot root tok (edgesBase + x)) →
      (∀ x < 2 * paths.length, ¬ Rrep.foot root tok (pathsBase + x)) →
      (∀ a, Rrep.foot root tok a → a < workHeap) →
      ZeroFrom mem workHeap →
      workHeap + evalSpace < 2 ^ w →
      ∃ nextHeap cost out tok' inner norm,
        Runs w p ω body
          (startState [root, edgesBase, edges.length, pathsBase, paths.length, workHeap] mem pos)
          (.returned nextHeap) out cost ∧
        workHeap + 2 * L ≤ nextHeap ∧ nextHeap ≤ workHeap + evalSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        0 ≤ norm ∧
        PathIntAt out.mem workHeap 4 L inner ∧
        PathIntAt out.mem (workHeap + L) 4 L norm ∧
        model.extG.inner model.extg Δ = (inner : ℝ) / (2 : ℝ) ^ P ∧
        model.extG.lnorm model.extℓ Δ = (norm : ℝ) / (2 : ℝ) ^ P ∧
        (∀ x < 2 * edges.length, tok'.tag (edgesBase + x) = 0) ∧
        (∀ x < 2 * paths.length, tok'.tag (pathsBase + x) = 0) ∧
        (∀ a, tok'.tag a = 18 → tok.tag a = 18) ∧
        Rrep.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < workHeap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ evalBudget + Rrep.phi root tok mem

/-- The corrected contract of the cycle finder `findCycleProc [root, heap]`. It is
`FindCycleStepSpec` with four more hypotheses (`OffTreeRecBound`, `WireCapFacts`, and the two
capacity facts of `OrdCycleRouteEvalSpecW`) and two more conclusions (the capacity `intCap` of
the name tables and `OffTreeRecBound` are kept). All the new hypotheses are about the state of
the call, so they need hold only on the states that the solver reaches. -/
@[expose] def FindCycleStepSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (findCycleProc : ℕ) (findSpace findBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[findCycleProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      ShiftLoopLevelFacts cfg model.chain →
      2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ) →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      (∀ e ∈ model.extG.E, 0 ≤ model.extℓ e) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + findSpace < 2 ^ w →
      ∃ nextHeap cost out tok' inner norm edges paths,
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap + 6 ≤ nextHeap ∧ nextHeap ≤ heap + findSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        (∀ x < 2 * edges.length, tok'.tag (out.mem (heap + 2) + x) = 0) ∧
        (∀ x < 2 * paths.length, tok'.tag (out.mem (heap + 4) + x) = 0) ∧
        (∀ a, tok'.tag a = 18 → a < heap) ∧
        CycleDescriptorAt model L P out.mem heap nextHeap inner norm edges paths ∧
        Rrep.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ findBudget + Rrep.phi root tok mem

end MinCostFlow.MinRatio
