module

public import MinCostFlow.Final.SolverTailCycle
public import MinCostFlow.Final.AssemblyDryRunWitness
public import MinCostFlow.MinRatio.OrdSolverSupportedFull
public import MinCostFlow.MinRatio.OrdSolverRateBounds
public import MinCostFlow.SparseCore.Program.AssemblyFamily
import MinCostFlow.MinRatio.GoodCycleBridgeWired

/-!
# Base code placement and `SolverObligations` for the dry run

Provides the linked cycle code `dryCycle`, its determinism (`dryCycle_noRand`), procedure
placement and relocation lemmas (`solverOps_hasAt`, `dryTail_hasAt`, `dryLastLevel_implements`,
`drySparseCore_uniform`, `dryInner_hasAt`), and the `SolverObligations` /
`supported_of_solverObligations` wrapper for `MinCostFlow/Final/AssemblyDryRunSolver.lean`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-- The cycle code of the dry run: `solverOpsProcs` at `mrdsCycleBase`, followed by `solverTail`
at `solverTailBase` with the real packed last-level bodies and the sparse-core and
inner-level code parts given as arguments. -/
def dryCycle (threshold A : ℕ) (sc : SparseCoreCode) (inner : SolverInnerCode) : List Stmt :=
  solverCycle threshold A lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner

/-- Determinism of `dryCycle`, from determinism of the sparse-core program and inner bodies
alone (the operations, wired entries, concrete helpers, and last-level bodies are unconditionally
`NoRand`). -/
theorem dryCycle_noRand (threshold A : ℕ) {sc : SparseCoreCode} {inner : SolverInnerCode}
    (hsc : sc.prog.IsDeterministic) (hinner : inner.IsDeterministic) :
    ∀ s ∈ dryCycle threshold A sc inner, s.NoRand :=
  solverCycle_noRand threshold A lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst hsc hinner

/-- The 183 solver operation procedures sit at `mrdsCycleBase` in the linked solver program. -/
theorem solverOps_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch
        (dryCycle threshold A sc inner) forest).HasAt mrdsCycleBase
      (solverOpsProcs mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle
        solverCycleShiftLevel) :=
  solverCycle_ops_hasAt threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    sc inner forest

/-- The solver code tail sits at `solverTailBase` (`mrdsCycleBase + 183`) in the linked solver
program. -/
theorem dryTail_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch
        (dryCycle threshold A sc inner) forest).HasAt solverTailBase
      (solverTail mrdsCycleBase threshold A lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
        sc inner solverTailBase) :=
  solverCycle_tail_hasAt threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    sc inner forest

/-- The real last-level bodies embedded in `dryCycle` implement `lastLevelRuntimeMachineContract`
for `dryLastTool` inside the linked solver program at `(lay.lastInit, lay.lastOp)`. -/
theorem dryLastLevel_implements (threshold A : ℕ) (dispatch : SolverDispatch)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    let lay := solverTailLayout lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner
      solverTailBase
    let p := linkedCappedSolverProgramWithV threshold A dispatch
      (dryCycle threshold A sc inner) forest
    ∀ {w L vCap eCap : ℕ} (fmt : Num.Format w) (G : MGraph),
      fmt.limbBits = 4 →
      (∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) → G.n ≤ G.m + 1 →
      (lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
        w p lay.lastInit lay.lastOp
        (MinRatio.lastLevelRuntimeMachineContract fmt L dryLastTool G vCap eCap
          (packedLastLevelMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK G L)
          ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (G.m + 1).size)
          (packedRuntimeAllocation G lastGuest lastCanonConst lastWordConst L vCap eCap)) :=
  dryLastBodies_implements
    (solverCycle_lastLevel_hasAt threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊
      lastWordConst sc inner forest)

/-- `SparseCoreOrdProgramUniform` transfers from `sc.prog` into the linked dry-run solver program
at `(lay.scInit, lay.scOp)`. -/
theorem drySparseCore_uniform {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    (threshold A : ℕ) (dispatch : SolverDispatch)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt)
    (hU : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op) :
    let lay := solverTailLayout lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner
      solverTailBase
    SparseCoreOrdProgramUniform C_lsst lsfInit impl
      (linkedCappedSolverProgramWithV threshold A dispatch
        (dryCycle threshold A sc inner) forest)
      lay.scInit lay.scOp :=
  solverCycle_sparseCore_uniform threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊
    lastWordConst sc inner forest hU

/-- The inner-level bodies sit at `lay.innerBase` in the linked dry-run solver program. -/
theorem dryInner_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (forest : List Stmt) :
    let lay := solverTailLayout lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner
      solverTailBase
    let env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
      lastWordConst sc solverTailBase
    (linkedCappedSolverProgramWithV threshold A dispatch
        (dryCycle threshold A sc inner) forest).HasAt lay.innerBase (inner.procs env) :=
  solverCycle_inner_hasAt threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    sc inner forest

/-- The obligations of the solver for one input, against `ordSolver_supported_full` and the
installed `dryCycle`: the sparse-core representation `Rcore` (local), the word-size facts, the
four step specifications at the fixed entries of `solverTail`, and the amortized envelope
`OrdSolverContractEnvelopeFull`. `cfg.ValidOrdNoHidden`, `GoodCycleNumericBridge`,
`solverOps_hasAt`, and the allocation bound are discharged automatically in
`supported_of_solverObligations`. -/
def SolverObligations {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode)
    (cycleRate : ℕ → ℕ) (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ)
    (allocationCoefficient allocationDegree : ℕ) : Prop :=
  ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let cycle := dryCycle threshold A sc inner
    let Ck := concreteQualityLinearCoeff threshold A
    let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase) cycle.length
    let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
    let p := linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := concreteCirculationCfgWithLast W J
    ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
      let F := ipmQualityMinRatioFormat I.m V k hw
      ∃ (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (psi epsExp capExp limbMul capLimit
          wordExp stretchPrec intCapMax forestEdgeCap initSpace
          initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul
          treeMul : ℕ)
        (DeepInv : ChainState cfg.T cfg.P → Prop)
        (refreshSpace refreshBudget : ℕ → ℕ) (B_bound R_bound : ℤ),
        Rcore.Local ∧
        epsExp = k + Num.IPM.alphaExponent I.m V + 10 ∧
        5 * F.limbs + 1 < 2 ^ w ∧
        cfg.P.d + 1 < 2 ^ w ∧ epsExp < 2 ^ w ∧
        (2 * (namedInstance I).m + 2) *
          shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w ∧
        2 * (namedInstance I).n + 1 < 2 ^ w ∧
        Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs ∧
        Nat.size I.m ≤ F.rangeExponent + 8 ∧
        maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) ∧
        2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
          (Num.capacity 4 F.limbs : ℤ) ∧
        2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
          ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
            (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
          (Num.capacity 4 F.limbs : ℤ) ∧
        B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
          (Num.capacity 4 F.limbs : ℤ) ∧
        (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound ∧
        (∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
          SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap) ∧
        initTargetCap cfg (namedInstance I) ≤ intCapMax ∧
        2 * (namedInstance I).n ≤ forestEdgeCap ∧
        DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchPrec DeepInv ∧
        SolverInitStepSpecCreditKFBL F cfg (namedInstance I) I.m V psi k epsExp Rcore p
          solverCycleInit initSpace initBudget toolMul treeMul ∧
        ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
          (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit
          (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p
          solverCycleChainRefresh refreshSpace refreshBudget toolMul treeMul B_bound R_bound ∧
        FindCycleStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
          (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p solverCycleFindCycle
          findSpace findBudget maxEdges maxPaths ∧
        ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
          (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
          forestEdgeCap (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p
          solverCycleShiftLevel shiftSpace shiftBudget toolMul treeMul ∧
        OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V psi k epsExp initSpace
          initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
          refreshSpace refreshBudget Rcore cycleRate (cycleAllocation I.n I.m)

/-- **The field `supported`**, for any chain witness `W`, code parts `sc` and `inner`, and
rate bounds `B`, by `ordSolver_supported_full_credit`. -/
theorem supported_of_solverObligations {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode)
    (B : OrdSolverInnerBounds) (allocationCoefficient allocationDegree : ℕ)
    (hSolver : SolverObligations W sc inner B.cycleRate B.cycleAllocation
      allocationCoefficient allocationDegree) :
    ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      let threshold := concreteEdgeThresholdWithLast W
      let A := concreteQualityBudgetWithLast W
      let cycle := dryCycle threshold A sc inner
      let Ck := concreteQualityLinearCoeff threshold A
      let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent threshold A I.m
      let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
      let dispatch := mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase) cycle.length
      let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
      let p := linkedCappedSolverProgramWithV threshold A dispatch cycle forest
      let cfg := concreteCirculationCfgWithLast W J
      ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
        ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
          RC.Implements w p solverCycleInit (solverOpsDispatch mrdsCycleBase)
            (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V k hw)
              (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I)
              I.m V (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
              B.cycleRate (B.cycleAllocation I.n I.m)) ∧
          (∀ j < 4, ∀ args, B.cycleAllocation I.n I.m j args ≤ B.cycleSpace I.n I.m) := by
  intro source J hJn hJm hCost hCap threshold A cycle Ck deg I V k w dispatch forest p cfg hw
  obtain ⟨Rcore, psi, epsExp, capExp, limbMul, capLimit, wordExp, stretchPrec, intCapMax,
    forestEdgeCap, initSpace, initBudget, findSpace, findBudget, shiftSpace, shiftBudget, maxEdges,
    maxPaths, toolMul, treeMul, DeepInv, refreshSpace, refreshBudget, B_bound, R_bound, hlocalCore,
    hepsExp, h5L1W, hdW, hepsW, hQuotaBoundW, h2nW, hlogW, hsizeM, hmaxEP, hcapEvalB, hcapTreeB,
    hcapOffB, hthrB, hCapLevels, hIntCapMax, hFEdgeCap, hDeepInv, hInit, hRefresh, hFind, hShift,
    hEnv⟩ :=
    hSolver source J hJn hJm hCost hCap hw
  exact ordSolver_supported_full_credit lastTool lastConstant lastSpec W solverCycleInit mrdsCycleBase
    solverCycleChainRefresh solverCycleFindCycle solverCycleShiftLevel cycle B.cycleRate
    B.cycleAllocation B.cycleSpace allocationCoefficient allocationDegree source J hJn hJm hCost
    hCap hw Rcore psi epsExp capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
    initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul
    treeMul DeepInv refreshSpace refreshBudget B_bound R_bound
    hlocalCore hepsExp h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB
    hcapOffB hthrB hCapLevels hIntCapMax hFEdgeCap hDeepInv
    (solverOps_hasAt threshold A dispatch sc inner forest)
    hInit hRefresh hFind hShift
    (goodCycleNumericBridge_wired (ipmQualityMinRatioFormat I.m V k hw) cfg (namedInstance I) I.m V
      psi k epsExp (detectOffTreeDrainUnit (ipmQualityMinRatioFormat I.m V k hw).limbs) Rcore
      maxEdges maxPaths B_bound R_bound)
    hEnv (fun j hj args => B.cycleAllocation_le_cycleSpace I.n I.m j hj args)

end MinCostFlow.Final.DryRun
