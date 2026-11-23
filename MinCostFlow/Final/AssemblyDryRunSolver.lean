module

public import MinCostFlow.Final.AssemblyDryRunSolverBase
public import MinCostFlow.MinRatio.OrdSolverWiredFull

/-!
# Wired dry-run assembly (`ordSolver_implements_full_wired` + `SparseCoreOrdProgramUniform`)

Builds `supported_of_wiredSpecs` for `Final/AssemblyDryRun.lean` from `SparseCoreOrdProgramUniform`
at `capExp = 3` and `limbMul = concreteReadout2LimbMul W` (`dryCapLimit W J = 12 * M₀ + 4`),
discharging both `DrySparseCoreCapLevels` (`drySparseCoreCapLevels_proved`) and
`DrySparseCoreWordBound` (`drySparseCoreWordBound_proved` from `drySparseCoreWordExp hSC 3 ≤ 39`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## Wired dry-run assembly (`ordSolver_implements_full_wired` + `SparseCoreOrdProgramUniform`) -/

/-- The sparse-core capacity exponent (`capExp = 3`) fixed across the dry run. -/
def dryCapExp : ℕ := 3

/-- The per-input sparse-core capacity limit (`vCap + eCap + 2 ≤ 12 * M₀ + 4`). -/
def dryCapLimit {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (J : Circulation) : ℕ :=
  12 * (concreteCirculationCfgWithLast W J).P.M₀ + 4

/-- The sparse-core word exponent `wordExp` extracted from `SparseCoreOrdProgramUniform` at
`capExp` (independent of both `limbMul` and the input circulation `J`). -/
def drySparseCoreWordExp {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {sc : SparseCoreCode}
    (hSC : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op)
    (capExp : ℕ) : ℕ :=
  Classical.choose (hSC capExp)

/-- The sparse-core contract parameters `P_sc` extracted from `SparseCoreOrdProgramUniform` at
`(capExp, limbMul)` (independent of the input circulation `J`). -/
def drySparseCoreParams {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {sc : SparseCoreCode}
    (hSC : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op)
    (capExp limbMul : ℕ) : SparseCoreOrdParams :=
  Classical.choose (Classical.choose_spec (hSC capExp) limbMul)

/-- `(drySparseCoreParams hSC capExp limbMul).wordExp` equals `drySparseCoreWordExp hSC capExp`. -/
theorem drySparseCoreParams_wordExp {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {sc : SparseCoreCode}
    (hSC : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op)
    (capExp limbMul : ℕ) :
    (drySparseCoreParams hSC capExp limbMul).wordExp = drySparseCoreWordExp hSC capExp :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hSC capExp) limbMul))).1

/-- The sparse-core allocation function extracted from `SparseCoreOrdProgramUniform` at
`(capExp, limbMul)`. -/
def drySparseCoreAlloc {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {sc : SparseCoreCode}
    (hSC : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op)
    (capExp limbMul : ℕ) : ℕ → List ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (hSC capExp) limbMul))

private theorem dsRep_local_cast {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    (R : DSRep (SparseCoreOrdAbs T₂)) (hloc : R.Local) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Local := by
  subst h; exact hloc

/-- The sparse-core representation `Rcore : DSRep (SparseCoreOrdAbs cfg.T)` extracted from
`SparseCoreOrdProgramUniform` at `(capExp, limbMul)` (matching `cfg.T` via
`concreteCirculationCfgWithLast_T_eq_progTool`). -/
def drySparseCoreRep {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl)
    (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl)
    (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (forestProgramsScratchDegree allocationCoefficient allocationDegree
          (concreteQualityLinearCoeff (concreteEdgeThresholdWithLast W)
            (concreteQualityBudgetWithLast W))))
        source.solverWords) :
    DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast W J).T) :=
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let Ck := concreteQualityLinearCoeff threshold A
  let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
  let F := ipmQualityMinRatioFormat I.m V k hw
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  have hT : (concreteCirculationCfgWithLast W J).T =
      sparseCoreProgTool (W.lsfInit F.limbs F.fmt.precision) W.C_lsst depth impl :=
    concreteCirculationCfgWithLast_T_eq_progTool W impl hsp hpar hconst J hw
  hT ▸ Classical.choose ((Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (hSC capExp) limbMul))).2 depth w F.fmt F.limbs)

/-- Locality of `drySparseCoreRep`, directly from `SparseCoreOrdProgramUniform`. -/
theorem drySparseCoreRep_local {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl)
    (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl)
    (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (forestProgramsScratchDegree allocationCoefficient allocationDegree
          (concreteQualityLinearCoeff (concreteEdgeThresholdWithLast W)
            (concreteQualityBudgetWithLast W))))
        source.solverWords) :
    (drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw).Local :=
  dsRep_local_cast (concreteCirculationCfgWithLast_T_eq_progTool W impl hsp hpar hconst J hw) _
    (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (hSC capExp) limbMul))).2
      (Expander.chosenL (max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast W) ^ 2))
      (wordSize (scratchWordMultiplier 1 (forestProgramsScratchDegree allocationCoefficient
        allocationDegree (concreteQualityLinearCoeff (concreteEdgeThresholdWithLast W)
          (concreteQualityBudgetWithLast W)))) source.solverWords)
      (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
          (solverConnectedAugmented J).m) hw).fmt
      (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
          (solverConnectedAugmented J).m) hw).limbs)).1

/-- Per-input numeric sizes, budgets, and fixed-point bounds shared across the six inner `W` specs,
the fixed-point capacity bounds, and the contract envelope (`capLimit` is fixed to `dryCapLimit`). -/
structure WiredInnerSizes where
  initSpace' : ℕ
  initFixed : ℕ
  selectSpace : ℕ
  selectBudget : ℕ
  evalSpace : ℕ
  evalBudget : ℕ
  termSpace : ℕ
  termFixed : ℕ
  deepSpace : ℕ
  deepFixed : ℕ
  maxEdges : ℕ
  maxPaths : ℕ
  toolMul : ℕ
  treeMul : ℕ
  coreSpace : ℕ → ℕ
  coreFixed : ℕ → ℕ
  B_tree : ℤ
  B_bound : ℤ
  R_bound : ℤ

/-- Linked solver program of the dry run for witness `W` and code pieces `sc`, `inner`. -/
abbrev dryLinkedProgram {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) : Program :=
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let cycle := dryCycle threshold A sc inner
  let dispatch := mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase) cycle.length
  let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
  linkedCappedSolverProgramWithV threshold A dispatch cycle forest

/-- Tail layout of the dry run (`solverTailLayout` at `solverTailBase`). -/
abbrev dryTailLay (sc : SparseCoreCode) (inner : SolverInnerCode) : SolverTailLayout :=
  solverTailLayout lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner solverTailBase

/-- Solver word size `w` of the dry run for `(source, W, allocationCoefficient, allocationDegree)`. -/
abbrev dryWordSize {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (allocationCoefficient allocationDegree : ℕ) (source : Circulation) : ℕ :=
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let Ck := concreteQualityLinearCoeff threshold A
  let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
  wordSize (scratchWordMultiplier 1 deg) source.solverWords

/-- Universal quantifier over valid reduced circulations `(source, J)` with fitting word size `hw`. -/
def ForAllDryInputs {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (allocationCoefficient allocationDegree : ℕ)
    (P : (source J : Circulation) →
      ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
          (solverConnectedAugmented J).m) ≤
        dryWordSize W allocationCoefficient allocationDegree source →
      Prop) : Prop :=
  ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      dryWordSize W allocationCoefficient allocationDegree source,
      P source J hw

/-- Hypothesis 1 of the dry run: `OrdInitConcreteSpecW` at `lay.initConcrete`. -/
def DryInitSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    OrdInitConcreteSpecW (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      cfg Rcore (namedInstance I) (dryLinkedProgram W sc inner) (dryTailLay sc inner).initConcrete
      s.B_tree capExp limbMul (dryCapLimit W J)
      (drySparseCoreParams hSC capExp limbMul).wordExp s.initSpace' s.initFixed s.toolMul

/-- Hypothesis 2 of the dry run: `OrdChainUpdateCoreSpecWKFBL` at `lay.ordChainCore`. -/
def DryChainUpdateCoreSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    OrdChainUpdateCoreSpecWKFBL (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) capExp limbMul (dryCapLimit W J) G.n (initTargetCap cfg G)
      cfg Rcore (dryLinkedProgram W sc inner) (dryTailLay sc inner).ordChainCore s.coreSpace
      s.coreFixed s.toolMul s.treeMul s.B_bound s.R_bound

/-- Hypothesis 3 of the dry run: `OrdCycleRouteSelectSpecW` at `lay.selectRoute`. -/
def DryCycleRouteSelectSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    OrdCycleRouteSelectSpecW (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) capExp limbMul (dryCapLimit W J) cfg Rcore
      (dryLinkedProgram W sc inner) (dryTailLay sc inner).selectRoute s.selectSpace s.selectBudget
      s.maxEdges s.maxPaths

/-- Hypothesis 4 of the dry run: `OrdCycleRouteEvalSpecW` at `lay.evalCycle`. -/
def DryCycleRouteEvalSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    OrdCycleRouteEvalSpecW (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) cfg Rcore (dryLinkedProgram W sc inner)
      (dryTailLay sc inner).evalCycle s.evalSpace s.evalBudget s.maxEdges s.maxPaths

/-- Hypothesis 5 of the dry run: `ShiftTermChainSyncSpecWExt` at `lay.shiftTermChain` with
`lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`. -/
def DryShiftTermSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    ShiftTermChainSyncSpecWExt (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) capExp limbMul (dryCapLimit W J)
      (2 * levelM cfg.TP cfg.P cfg.P.d) cfg Rcore
      (dryLinkedProgram W sc inner) (dryTailLay sc inner).shiftTermChain s.termSpace s.termFixed
      s.toolMul s.treeMul

/-- Hypothesis 6 of the dry run: `ShiftDeepChainSyncSpecWExtKFBL` at
`lay.shiftDeepChain`. -/
def DryShiftDeepSpecW {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (inner : SolverInnerCode) (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (stretchPrec : Circulation → ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    ShiftDeepChainSyncSpecWExtKFBL (dryWordSize W allocationCoefficient allocationDegree source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) capExp limbMul (dryCapLimit W J)
      (drySparseCoreParams hSC capExp limbMul).wordExp (stretchPrec J)
      (initTargetCap cfg G) (2 * G.n) G.n (initTargetCap cfg G) cfg Rcore
      (dryLinkedProgram W sc inner) (dryTailLay sc inner).shiftDeepChain s.deepSpace s.deepFixed
      s.toolMul s.treeMul

/-- Per-input `DeepShiftChainInvHyps` obligation supplying `ShiftDeepModelInv` for
`ShiftDeepChainSyncSpecWExtKFBL` across Init, Update, and Shift. -/
def DryDeepShiftInv {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (stretchPrec : Circulation → ℕ)
    (DeepInv : ∀ J, ChainState (concreteCirculationCfgWithLast W J).T
      (concreteCirculationCfgWithLast W J).P → Prop) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    DeepShiftChainInvHyps (dryWordSize W allocationCoefficient allocationDegree source) F cfg
      (namedInstance I) k (drySparseCoreParams hSC capExp limbMul).wordExp (stretchPrec J)
      (DeepInv J)

/-- The seven per-input fixed-point capacity inequalities on `B_tree`, `B_bound`, `R_bound`,
`maxEdges`, and `maxPaths`. -/
def DryFixedPointCapBounds {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (allocationCoefficient allocationDegree : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let G := namedInstance I
    let s := sz source J
    (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ s.B_bound ∧
    (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ s.B_tree ∧
    2 * ((2 * G.n + 1 : ℕ) : ℤ) * s.B_tree < (Num.capacity 4 F.limbs : ℤ) ∧
    s.maxEdges + s.maxPaths < 2 ^ (3 * F.rangeExponent + 20) ∧
    2 * (((s.maxEdges + s.maxPaths * G.n : ℕ) : ℤ) * s.B_bound) < (Num.capacity 4 F.limbs : ℤ) ∧
    2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((s.B_bound + (s.maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (s.R_bound + (s.maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ) ∧
    s.B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ)

/-- Sparse-core level word-size bound `(levelM i + N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w`
for all levels `i < d`. -/
def DrySparseCoreWordBound {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    ∀ i < cfg.P.d,
      (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ (drySparseCoreParams hSC capExp limbMul).wordExp *
          (F.limbs + 1) <
        2 ^ dryWordSize W allocationCoefficient allocationDegree source

/-- Per-level split `SparseCoreCapHyp capExp limbMul` for all levels `i < d` and
`vCap + eCap + 2 ≤ dryCapLimit W J`. -/
def DrySparseCoreCapLevels {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun _source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ dryCapLimit W J →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap

/-- Discharges `DrySparseCoreCapLevels` at `capExp = 3` and `limbMul = concreteReadout2LimbMul W`
through `OrdSolverLevelCapBounds.concrete_sparseCoreCapHyp_uniform`. -/
theorem drySparseCoreCapLevels_proved {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (allocationCoefficient allocationDegree : ℕ) :
    DrySparseCoreCapLevels W allocationCoefficient allocationDegree
      dryCapExp (concreteReadout2LimbMul W) := by
  intro _source J hJn hJm _hCost hCap _hw
  dsimp only
  intro i hi vCap eCap hlim
  exact concrete_sparseCoreCapHyp_uniform W J hJn hJm (fun e => (hCap e).1) i hi.le vCap eCap hlim

/-- Discharges `DrySparseCoreWordBound` at `capExp = 3` and `limbMul = concreteReadout2LimbMul W`
from `drySparseCoreWordExp hSC 3 ≤ 39` (in particular `wordExp = 24`, degree `25 ≤ 40`) through
`OrdSolverWordBound.concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize`. -/
theorem drySparseCoreWordBound_proved {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (allocationCoefficient allocationDegree : ℕ)
    (hWordExp : drySparseCoreWordExp hSC dryCapExp ≤ 39)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize W) ≤
        allocationCoefficient) :
    DrySparseCoreWordBound W impl sc hSC allocationCoefficient allocationDegree
      dryCapExp (concreteReadout2LimbMul W) := by
  intro source J hJn hJm _hCost hCap hw
  dsimp only
  intro i hi
  rw [drySparseCoreParams_wordExp]
  have hL := (concrete_sparseCoreCapHyp_uniform W J hJn hJm (fun e => (hCap e).1)
    i hi.le 0 0 (by omega)).2
  exact Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize W)
    allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm (fun e => (hCap e).1) hw
    (drySparseCoreWordExp hSC dryCapExp) hWordExp i _ hL

/-- Amortized rate and space envelope `OrdSolverContractEnvelopeFullCredit` connecting the concrete
inner budgets/spaces to `B.cycleRate` and `B.cycleAllocation`. -/
def DryContractEnvelope {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl) (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl) (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (cycleRate : ℕ → ℕ) (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ)
    (allocationCoefficient allocationDegree capExp limbMul : ℕ)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop :=
  ForAllDryInputs W allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let Rcore := drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      capExp limbMul source J hw
    let s := sz source J
    OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10)
      (s.initSpace' + initWiredExtraSpace cfg (namedInstance I))
      (s.initFixed + initWiredExtraCost cfg (namedInstance I))
      (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
      (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
      s.maxEdges s.maxPaths s.toolMul s.treeMul
      (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
      (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
        62 * (cfg.P.d + 1) + 240)
      Rcore cycleRate (cycleAllocation I.n I.m)

/-- **The wired `supported` field**, through `ordSolver_supported_full_wired`
(`ordSolver_implements_full_wired`) at `capExp = 3` and `limbMul = concreteReadout2LimbMul W`.
Discharges `DrySparseCoreCapLevels` (`drySparseCoreCapLevels_proved`),
`DrySparseCoreWordBound` (`drySparseCoreWordBound_proved` from `hWordExp : wordExp ≤ 39`),
procedure placements, `Rcore.Local`, `cfg.ValidOrdNoHidden`, `ToolCostMono`,
`GoodCycleNumericBridge`, `ShiftQuotaWriterSpec`, and all concrete word-size/format bounds. -/
theorem supported_of_wiredSpecs {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (impl : SparsifyImpl)
    (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl)
    (hconst : W.spanConst = dsAmortConst impl)
    (sc : SparseCoreCode)
    (hSC : SparseCoreOrdProgramUniform W.C_lsst W.lsfInit impl sc.prog sc.init sc.op)
    (hWordExp : drySparseCoreWordExp hSC dryCapExp ≤ 39)
    (inner : SolverInnerCode)
    (B : OrdSolverInnerBounds) (allocationCoefficient allocationDegree : ℕ)
    (hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly W) ≤ allocationCoefficient)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize W) ≤
        allocationCoefficient)
    (stretchPrec : Circulation → ℕ)
    (DeepInv : ∀ J, ChainState (concreteCirculationCfgWithLast W J).T
      (concreteCirculationCfgWithLast W J).P → Prop)
    (hDeepInv : DryDeepShiftInv W impl sc hSC allocationCoefficient allocationDegree
      dryCapExp (concreteReadout2LimbMul W) stretchPrec DeepInv)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInit : DryInitSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient allocationDegree
      dryCapExp (concreteReadout2LimbMul W) sz)
    (hCore : DryChainUpdateCoreSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) sz)
    (hSelect : DryCycleRouteSelectSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) sz)
    (hEval : DryCycleRouteEvalSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) sz)
    (hTerm : DryShiftTermSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) sz)
    (hDeep : DryShiftDeepSpecW W impl hsp hpar hconst sc hSC inner allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) stretchPrec sz)
    (hCapBounds : DryFixedPointCapBounds W allocationCoefficient allocationDegree sz)
    (hEnv : DryContractEnvelope W impl hsp hpar hconst sc hSC B.cycleRate B.cycleAllocation
      allocationCoefficient allocationDegree dryCapExp (concreteReadout2LimbMul W) sz) :
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
  obtain ⟨hthrB, hthrTree, hCapTreeInit, hmaxEP, hcapEvalB, hcapTreeB, hcapOffB⟩ :=
    hCapBounds source J hJn hJm hCost hCap hw
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W) allocationCoefficient
      allocationDegree hWordCoeff source J hJn hJm (fun e => (hCap e).1) hw
  have hTail := dryTail_hasAt threshold A dispatch sc inner forest
  let lay := dryTailLay sc inner
  let s := sz source J
  exact ordSolver_supported_full_wired lastTool lastConstant lastSpec W
    solverCycleInit lay.initConcrete lay.overwrite lay.clog mrdsCycleBase
    solverCycleChainRefresh lay.ordEdits lay.ordChainCore lay.shiftQuotaWriter
    solverCycleFindCycle lay.selectRoute lay.evalCycle
    solverCycleShiftLevel lay.shiftTermChain lay.shiftDeepChain
    cycle B.cycleRate B.cycleAllocation B.cycleSpace allocationCoefficient allocationDegree
    source J hJn hJm hCost hCap hw
    (drySparseCoreRep W impl hsp hpar hconst sc hSC allocationCoefficient allocationDegree
      dryCapExp (concreteReadout2LimbMul W) source J hw)
    dryCapExp (concreteReadout2LimbMul W) (dryCapLimit W J)
    (drySparseCoreParams hSC dryCapExp (concreteReadout2LimbMul W)).wordExp
    (stretchPrec J) (initTargetCap cfg (namedInstance I)) (2 * (namedInstance I).n)
    s.initSpace' s.initFixed
    s.selectSpace s.selectBudget s.evalSpace s.evalBudget s.termSpace s.termFixed
    s.deepSpace s.deepFixed s.maxEdges s.maxPaths s.toolMul s.treeMul (DeepInv J)
    s.coreSpace s.coreFixed
    s.B_tree s.B_bound s.R_bound
    (drySparseCoreRep_local W impl hsp hpar hconst sc hSC allocationCoefficient
      allocationDegree dryCapExp (concreteReadout2LimbMul W) source J hw)
    h4M3W hQuotaBoundW hthrB hthrTree hCapTreeInit hmaxEP hcapEvalB hcapTreeB hcapOffB
    (drySparseCoreWordBound_proved W impl sc hSC allocationCoefficient allocationDegree
      hWordExp hSCWordCoeff source J hJn hJm hCost hCap hw)
    (drySparseCoreCapLevels_proved W allocationCoefficient allocationDegree
      source J hJn hJm hCost hCap hw)
    le_rfl le_rfl (hDeepInv source J hJn hJm hCost hCap hw)
    (solverOps_hasAt threshold A dispatch sc inner forest)
    (solverTail_initWired_at hTail)
    (solverTail_overwrite_at hTail)
    (solverTail_clog_meetsContract hTail)
    (solverTail_chainRefresh_at hTail)
    (solverTail_ordEdits_at hTail)
    (solverTail_shiftQuotaWriter_at hTail)
    (solverTail_findCycle_at hTail)
    (solverTail_shiftLevel_at hTail)
    (hInit source J hJn hJm hCost hCap hw)
    (hCore source J hJn hJm hCost hCap hw)
    (hSelect source J hJn hJm hCost hCap hw)
    (hEval source J hJn hJm hCost hCap hw)
    (hTerm source J hJn hJm hCost hCap hw)
    (hDeep source J hJn hJm hCost hCap hw)
    (hEnv source J hJn hJm hCost hCap hw)
    (fun j hj args => B.cycleAllocation_le_cycleSpace I.n I.m j hj args)

end MinCostFlow.Final.DryRun
