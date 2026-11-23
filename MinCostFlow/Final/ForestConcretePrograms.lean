module

public import MinCostFlow.Final.ForestConcreteProgramBase
import Mathlib.Tactic

/-!
# Parameter packages `ForestConcretePrograms`, `DyadicForestConcretePrograms`, and `DyadicWithVConcretePrograms`

Defines the degree-free ordered-chain program packages:
- `ForestConcretePrograms` (implementing `Chain.Ordered.algorithm2_dsWithFailureOwn`),
- `DyadicForestConcretePrograms` (implementing `Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)`),
- `DyadicWithVConcretePrograms` (implementing `Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)`
  with `V = solverPenalty J.m` passed into `minRatioMachineContractWithV` and an arbitrary `LastLevelTool`),

with the dynamic forest discharged by `DynamicLctForest`, `ToolEmbedsSurvivingOrdRestart` and
`ToolNoReinsertOrdRestart` discharged unconditionally, and `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo`.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain SparseCore IPM IPM.Machine WordRAM Scaling Scaling.Machine LinkCut.Prog

/-- Parameter package for Theorem 1.1 with the dynamic forest completely discharged by
`DynamicLctForest` on the degree-free ordered bundle chain. It has no cited-result hypotheses,
no degree cap and no restart obligations. It holds only the min-ratio data structure machine
program with its bounds, and the chain witness. -/
structure ForestConcretePrograms where
  /-- The chain witness, given by the caller. Its data fields (`oracle`, `lsfInit`, `C_lsst`,
  `sparsify`, `params`) fix the tool of `cfg` in `supported`. Build it with
  `orderedConcreteChainWitnessOf`, which takes these data as arguments. -/
  witness : OrderedConcreteChainWitness
  /-- Entry addresses and deterministic procedures for the min-ratio data structure. -/
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  cycle : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M
  /-- Machine implementation of `Chain.Ordered.algorithm2_dsWithFailureOwn` in the linked solver program. -/
  supported : ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    let W := witness
    let threshold := orderedConcreteEdgeThreshold W
    let A := orderedConcreteQualityBudget W
    let Ck := concreteQualityLinearCoeff threshold A
    let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := mrdsSolverDispatch cycleInit cycleOp cycle.length
    let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
    let p := linkedCappedSolverProgram threshold A dispatch cycle forest
    let cfg := orderedConcreteCirculationCfg W J
    ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureOwn cfg).State,
        RC.Implements w p cycleInit cycleOp
          (minRatioMachineContract (ipmQualityMinRatioFormat I.m V k hw)
            (Chain.Ordered.algorithm2_dsWithFailureOwn cfg) (namedInstance I) I.m
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m)

/-- Dyadic-`κ` parameter package next to `ForestConcretePrograms`: identical in every field
except that `supported` asks for `Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)`
(testing against an exact dyadic ratio bound `1 / 2 ^ k`) rather than
`Chain.Ordered.algorithm2_dsWithFailureOwn cfg`. -/
structure DyadicForestConcretePrograms where
  /-- The chain witness, given by the caller. Its data fields (`oracle`, `lsfInit`, `C_lsst`,
  `sparsify`, `params`) fix the tool of `cfg` in `supported`. Build it with
  `orderedConcreteChainWitnessOf`, which takes these data as arguments. -/
  witness : OrderedConcreteChainWitness
  /-- Entry addresses and deterministic procedures for the min-ratio data structure. -/
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  cycle : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M
  /-- Machine implementation of `Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)` in
  the linked solver program. -/
  supported : ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    let W := witness
    let threshold := orderedConcreteEdgeThreshold W
    let A := orderedConcreteQualityBudget W
    let Ck := concreteQualityLinearCoeff threshold A
    let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := mrdsSolverDispatch cycleInit cycleOp cycle.length
    let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
    let p := linkedCappedSolverProgram threshold A dispatch cycle forest
    let cfg := orderedConcreteCirculationCfg W J
    ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit cycleOp
          (minRatioMachineContract (ipmQualityMinRatioFormat I.m V k hw)
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m)

/-- Dyadic-`κ`, `V`-passing, arbitrary-`LastLevelTool` parameter package on the degree-free
ordered bundle chain:
1. Passes `V = solverPenalty J.m` into `minRatioMachineContractWithV` at init
   (`[graph, g, l, limbs, precision, V, heap]`) via `linkedCappedSolverProgramWithV`.
2. Accepts any `lastTool : LastLevelTool` satisfying `lastTool.IsSpec (lastLevelParams lastConstant)`.
3. Has no cited-result hypotheses, no degree cap, and discharges `ToolEmbedsSurvivingOrdRestart`
   and `ToolNoReinsertOrdRestart` unconditionally. -/
structure DyadicWithVConcretePrograms where
  /-- Last-level tool implementation (`LastLevelTool`). -/
  lastTool : LastLevelTool
  /-- Parameter constant `C'` in `lastLevelParams C'` for `lastTool.IsSpec`. -/
  lastConstant : ℝ
  /-- Proof that `lastTool` satisfies `LastLevelTool.IsSpec (lastLevelParams lastConstant)`. -/
  lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)
  /-- The chain witness, given by the caller. Its data fields (`lsfInit`, `C_lsst`, `sparsify`,
  `params`) fix the tool `cfg.T` that `supported` implements. `lsfInit` is a family indexed by
  the number format, and `cfg` uses the member at the format of the instance
  (`concreteCirculationCfgWithLast_T`). Build it with `concreteChainWitnessWithLastOf`, which
  takes these data as arguments. -/
  witness : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec
  /-- Entry addresses and deterministic procedures for the min-ratio data structure. -/
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  cycle : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M
  /-- Machine implementation of `Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)` in
  the `V`-passing linked solver program against `minRatioMachineContractWithV` (`[graph, g, l,
  limbs, precision, V, heap]`, `V = solverPenalty J.m`). -/
  supported : ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    let W := witness
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let Ck := concreteQualityLinearCoeff threshold A
    let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := mrdsSolverDispatch cycleInit cycleOp cycle.length
    let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
    let p := linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := concreteCirculationCfgWithLast W J
    ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit cycleOp
          (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V k hw)
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m)

def ForestConcretePrograms.toBase (P : ForestConcretePrograms) : ForestConcreteProgramBase where
  witness := P.witness
  cycleInit := P.cycleInit
  cycleOp := P.cycleOp
  cycle := P.cycle
  cycleDeterministic := P.cycleDeterministic
  cycleRate := P.cycleRate
  cycleAllocation := P.cycleAllocation
  cycleSpace := P.cycleSpace
  allocationCoefficient := P.allocationCoefficient
  allocationDegree := P.allocationDegree
  cycleSpace_poly := P.cycleSpace_poly
  cycleRateExponent := P.cycleRateExponent
  cycleRateExponent_nonneg := P.cycleRateExponent_nonneg
  cycleRateConstant := P.cycleRateConstant
  cycleRateConstant_pos := P.cycleRateConstant_pos
  cycleRate_subpoly := P.cycleRate_subpoly

def DyadicForestConcretePrograms.toBase (P : DyadicForestConcretePrograms) : ForestConcreteProgramBase where
  witness := P.witness
  cycleInit := P.cycleInit
  cycleOp := P.cycleOp
  cycle := P.cycle
  cycleDeterministic := P.cycleDeterministic
  cycleRate := P.cycleRate
  cycleAllocation := P.cycleAllocation
  cycleSpace := P.cycleSpace
  allocationCoefficient := P.allocationCoefficient
  allocationDegree := P.allocationDegree
  cycleSpace_poly := P.cycleSpace_poly
  cycleRateExponent := P.cycleRateExponent
  cycleRateExponent_nonneg := P.cycleRateExponent_nonneg
  cycleRateConstant := P.cycleRateConstant
  cycleRateConstant_pos := P.cycleRateConstant_pos
  cycleRate_subpoly := P.cycleRate_subpoly

def ForestConcretePrograms.qualityBudget (P : ForestConcretePrograms) : ℕ := P.toBase.qualityBudget
def ForestConcretePrograms.edgeThreshold (P : ForestConcretePrograms) : ℕ := P.toBase.edgeThreshold
def ForestConcretePrograms.qualityLinearCoeff (P : ForestConcretePrograms) : ℕ := P.toBase.qualityLinearCoeff
def ForestConcretePrograms.scratchDegree (P : ForestConcretePrograms) : ℕ := P.toBase.scratchDegree
def ForestConcretePrograms.dispatch (P : ForestConcretePrograms) : SolverDispatch := P.toBase.dispatch
def ForestConcretePrograms.forest (P : ForestConcretePrograms) : List Stmt := P.toBase.forest
def ForestConcretePrograms.resources (P : ForestConcretePrograms) : SolverForestResources := P.toBase.resources
def ForestConcretePrograms.runtimeResources (P : ForestConcretePrograms) : SolverForestRuntimeResources := P.toBase.runtimeResources
def ForestConcretePrograms.solver (P : ForestConcretePrograms) : Program := P.toBase.solver

theorem ForestConcretePrograms.solver_deterministic (P : ForestConcretePrograms) :
    P.solver.IsDeterministic := P.toBase.solver_deterministic

/-- The linked solver with discharged dynamic link-cut forest meets the compressed solver contract. -/
theorem ForestConcretePrograms.solver_meetsContract (P : ForestConcretePrograms) (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (forestConnectedSolverRuntimeTime P.runtimeResources)
      (forestConnectedSolverRuntimeWorkspace P.runtimeResources)) :=
  P.toBase.solver_meetsContract_of J
    (fun J' => Chain.Ordered.algorithm2_dsWithFailureOwn (orderedConcreteCirculationCfg P.witness J'))
    (fun J' hJn hm hp =>
      orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo P.witness J' hJn hm hp)
    (P.supported J)

/-- Polynomial scratch reservation bound covering both `cycle` and dynamic link-cut forest. -/
theorem ForestConcretePrograms.workspace_le (P : ForestConcretePrograms) (n m : ℕ) :
    forestConnectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree :=
  P.toBase.workspace_le n m

def ForestConcretePrograms.program (P : ForestConcretePrograms) : Program := P.toBase.program

theorem ForestConcretePrograms.program_deterministic (P : ForestConcretePrograms) :
    P.program.IsDeterministic := P.toBase.program_deterministic

def ForestConcretePrograms.timeConstant (P : ForestConcretePrograms) : ℕ := P.toBase.timeConstant

/-- The outer scaling program runs on arbitrary valid instances and obeys the counted scaling bound. -/
theorem ForestConcretePrograms.program_runsTo (P : ForestConcretePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
        (linkedForestSolverTime P.runtimeResources (P.timeConstant * min I.n I.m) (P.timeConstant * I.m) + I.m) +
        P.timeConstant * I.n :=
  P.toBase.program_runsTo_of P.solver_meetsContract I hv ω

def DyadicForestConcretePrograms.qualityBudget (P : DyadicForestConcretePrograms) : ℕ := P.toBase.qualityBudget
def DyadicForestConcretePrograms.edgeThreshold (P : DyadicForestConcretePrograms) : ℕ := P.toBase.edgeThreshold
def DyadicForestConcretePrograms.qualityLinearCoeff (P : DyadicForestConcretePrograms) : ℕ := P.toBase.qualityLinearCoeff
def DyadicForestConcretePrograms.scratchDegree (P : DyadicForestConcretePrograms) : ℕ := P.toBase.scratchDegree
def DyadicForestConcretePrograms.dispatch (P : DyadicForestConcretePrograms) : SolverDispatch := P.toBase.dispatch
def DyadicForestConcretePrograms.forest (P : DyadicForestConcretePrograms) : List Stmt := P.toBase.forest
def DyadicForestConcretePrograms.resources (P : DyadicForestConcretePrograms) : SolverForestResources := P.toBase.resources
def DyadicForestConcretePrograms.runtimeResources (P : DyadicForestConcretePrograms) : SolverForestRuntimeResources := P.toBase.runtimeResources
def DyadicForestConcretePrograms.solver (P : DyadicForestConcretePrograms) : Program := P.toBase.solver

theorem DyadicForestConcretePrograms.solver_deterministic (P : DyadicForestConcretePrograms) :
    P.solver.IsDeterministic := P.toBase.solver_deterministic

/-- The linked solver with discharged dynamic link-cut forest and dyadic-`κ` ordered min-ratio
structure meets the compressed solver contract, proving `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo`
at `1 / 2 ^ k` via `orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo_with`. -/
theorem DyadicForestConcretePrograms.solver_meetsContract (P : DyadicForestConcretePrograms) (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (forestConnectedSolverRuntimeTime P.runtimeResources)
      (forestConnectedSolverRuntimeWorkspace P.runtimeResources)) :=
  P.toBase.solver_meetsContract_of J
    (fun J' => Chain.Ordered.algorithm2_dsWithFailureWith (orderedConcreteCirculationCfg P.witness J')
      (1 / (2 : ℝ) ^ cappedQualityExponent P.edgeThreshold P.qualityBudget (solverConnectedAugmented J').m))
    (fun J' hJn hm hp =>
      orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo_with P.witness J' hJn hm hp)
    (P.supported J)

theorem DyadicForestConcretePrograms.workspace_le (P : DyadicForestConcretePrograms) (n m : ℕ) :
    forestConnectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree :=
  P.toBase.workspace_le n m

def DyadicForestConcretePrograms.program (P : DyadicForestConcretePrograms) : Program := P.toBase.program

theorem DyadicForestConcretePrograms.program_deterministic (P : DyadicForestConcretePrograms) :
    P.program.IsDeterministic := P.toBase.program_deterministic

def DyadicForestConcretePrograms.timeConstant (P : DyadicForestConcretePrograms) : ℕ := P.toBase.timeConstant

theorem DyadicForestConcretePrograms.program_runsTo (P : DyadicForestConcretePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
        (linkedForestSolverTime P.runtimeResources (P.timeConstant * min I.n I.m) (P.timeConstant * I.m) + I.m) +
        P.timeConstant * I.n :=
  P.toBase.program_runsTo_of P.solver_meetsContract I hv ω

def DyadicWithVConcretePrograms.qualityBudget (P : DyadicWithVConcretePrograms) : ℕ :=
  concreteQualityBudgetWithLast P.witness

def DyadicWithVConcretePrograms.edgeThreshold (P : DyadicWithVConcretePrograms) : ℕ :=
  concreteEdgeThresholdWithLast P.witness

def DyadicWithVConcretePrograms.toCore (P : DyadicWithVConcretePrograms) :
    ForestConcreteProgramCore where
  useV := true
  edgeThreshold := P.edgeThreshold
  edgeThreshold_ge_two := concreteEdgeThresholdWithLast_ge_two P.witness
  qualityBudget := P.qualityBudget
  cycleInit := P.cycleInit
  cycleOp := P.cycleOp
  cycle := P.cycle
  cycleDeterministic := P.cycleDeterministic
  cycleRate := P.cycleRate
  cycleAllocation := P.cycleAllocation
  cycleSpace := P.cycleSpace
  allocationCoefficient := P.allocationCoefficient
  allocationDegree := P.allocationDegree
  cycleSpace_poly := P.cycleSpace_poly
  cycleRateExponent := P.cycleRateExponent
  cycleRateExponent_nonneg := P.cycleRateExponent_nonneg
  cycleRateConstant := P.cycleRateConstant
  cycleRateConstant_pos := P.cycleRateConstant_pos
  cycleRate_subpoly := P.cycleRate_subpoly

def DyadicWithVConcretePrograms.qualityLinearCoeff (P : DyadicWithVConcretePrograms) : ℕ := P.toCore.qualityLinearCoeff
def DyadicWithVConcretePrograms.scratchDegree (P : DyadicWithVConcretePrograms) : ℕ := P.toCore.scratchDegree
def DyadicWithVConcretePrograms.dispatch (P : DyadicWithVConcretePrograms) : SolverDispatch := P.toCore.dispatch
def DyadicWithVConcretePrograms.forest (P : DyadicWithVConcretePrograms) : List Stmt := P.toCore.forest
def DyadicWithVConcretePrograms.resources (P : DyadicWithVConcretePrograms) : SolverForestResources := P.toCore.resources
def DyadicWithVConcretePrograms.runtimeResources (P : DyadicWithVConcretePrograms) : SolverForestRuntimeResources := P.toCore.runtimeResources
def DyadicWithVConcretePrograms.solver (P : DyadicWithVConcretePrograms) : Program := P.toCore.solver

theorem DyadicWithVConcretePrograms.solver_deterministic (P : DyadicWithVConcretePrograms) :
    P.solver.IsDeterministic := P.toCore.solver_deterministic

/-- The linked `V`-passing solver with discharged dynamic link-cut forest, arbitrary `lastTool`,
and dyadic-`κ` ordered min-ratio structure meets the compressed solver contract. -/
theorem DyadicWithVConcretePrograms.solver_meetsContract (P : DyadicWithVConcretePrograms) (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (forestConnectedSolverRuntimeTime P.runtimeResources)
      (forestConnectedSolverRuntimeWorkspace P.runtimeResources)) := by
  refine P.toCore.solver_meetsContract_of J
    (fun J' => Chain.Ordered.algorithm2_dsWithFailureWith (concreteCirculationCfgWithLast P.witness J')
      (1 / (2 : ℝ) ^ cappedQualityExponent P.edgeThreshold P.qualityBudget (solverConnectedAugmented J').m)) ?_
  intro J' hJn hm hCost hCap
  have hp : ∀ e, 1 ≤ J'.capacity e := fun e => (hCap e).1
  refine ⟨concrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo_withLast P.witness J' hJn hm hp, ?_⟩
  intro hwJ
  exact P.supported J J' hJn hm hCost hCap hwJ

theorem DyadicWithVConcretePrograms.workspace_le (P : DyadicWithVConcretePrograms) (n m : ℕ) :
    forestConnectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree :=
  P.toCore.workspace_le n m

def DyadicWithVConcretePrograms.program (P : DyadicWithVConcretePrograms) : Program := P.toCore.program

theorem DyadicWithVConcretePrograms.program_deterministic (P : DyadicWithVConcretePrograms) :
    P.program.IsDeterministic := P.toCore.program_deterministic

def DyadicWithVConcretePrograms.timeConstant (P : DyadicWithVConcretePrograms) : ℕ := P.toCore.timeConstant

theorem DyadicWithVConcretePrograms.program_runsTo (P : DyadicWithVConcretePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
        (linkedForestSolverTime P.runtimeResources (P.timeConstant * min I.n I.m) (P.timeConstant * I.m) + I.m) +
        P.timeConstant * I.n :=
  P.toCore.program_runsTo_of P.solver_meetsContract I hv ω

end MinCostFlow.Final
