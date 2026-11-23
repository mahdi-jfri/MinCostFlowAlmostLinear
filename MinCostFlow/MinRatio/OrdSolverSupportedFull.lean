module

public import MinCostFlow.MinRatio.OrdSolverImplementsFull

/-!
# The `supported` field for the one representation

* `ordSolver_supported_full_credit`: instantiates `ordSolver_implements_full_credit` at the
  concrete configuration of `Final.DyadicWithVConcretePrograms` with dual tool-cost and
  tree-update credits (`toolMul`, `treeMul`), automatically discharging `cfg.ValidOrdNoHidden`
  (`Final.concreteCirculationCfgWithLast_validOrdNoHidden`) and `ToolCostMono cfg.T`
  (`sparseCoreBundleRestartToolMachWith_costMono`).
* `ordSolver_supported_full`: specialization at `toolMul = 0, treeMul = 0` for fixed-budget
  step specs (also discharging `cfg.ValidOrdNoHidden` internally).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- **The `supported` field of `Final.DyadicWithVConcretePrograms` for `solverStateRepFull` with
dual tool-cost and tree-update credits (`toolMul`, `treeMul`).** Automatically discharges
`cfg.ValidOrdNoHidden` (`Final.concreteCirculationCfgWithLast_validOrdNoHidden`) and
`ToolCostMono cfg.T` (`sparseCoreBundleRestartToolMachWith_costMono`). -/
theorem ordSolver_supported_full_credit
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant))
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (cycleInit base chainRefreshProc findCycleProc shiftLevelProc : ℕ)
    (cycle : List Stmt) (cycleRate : ℕ → ℕ)
    (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ) (cycleSpace : ℕ → ℕ → ℕ)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Scaling.Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (_hCost : J.CostsBounded (J.m ^ 10))
    (hCap : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (Final.concreteEdgeThresholdWithLast W)
        (Final.concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (Final.forestProgramsScratchDegree allocationCoefficient allocationDegree
          (Final.concreteQualityLinearCoeff
            (Final.concreteEdgeThresholdWithLast W)
            (Final.concreteQualityBudgetWithLast W))))
        source.solverWords) :
    let threshold := Final.concreteEdgeThresholdWithLast W
    let A := Final.concreteQualityBudgetWithLast W
    let Ck := Final.concreteQualityLinearCoeff threshold A
    let deg := Final.forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := Final.mrdsSolverDispatch cycleInit (solverOpsDispatch base) cycle.length
    let forest := Final.dynLctForestBodies 4 (Final.mrdsCycleBase + cycle.length)
    let p := Final.linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := Final.concreteCirculationCfgWithLast W J
    let F := ipmQualityMinRatioFormat I.m V k hw
    ∀ (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (psi epsExp capExp limbMul capLimit
        wordExp stretchPrec intCapMax forestEdgeCap
        initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
        toolMul treeMul : ℕ)
      (DeepInv : ChainState cfg.T cfg.P → Prop)
      (refreshSpace refreshBudget : ℕ → ℕ) (B_bound R_bound : ℤ),
      Rcore.Local →
      epsExp = k + Num.IPM.alphaExponent I.m V + 10 →
      5 * F.limbs + 1 < 2 ^ w →
      cfg.P.d + 1 < 2 ^ w → epsExp < 2 ^ w →
      (2 * (namedInstance I).m + 2) *
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w →
      2 * (namedInstance I).n + 1 < 2 ^ w →
      Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs →
      Nat.size I.m ≤ F.rangeExponent + 8 →
      maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
      2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
        (Num.capacity 4 F.limbs : ℤ) →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
        (Num.capacity 4 F.limbs : ℤ) →
      B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
        (Num.capacity 4 F.limbs : ℤ) →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound →
      (∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
        SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap) →
      initTargetCap cfg (namedInstance I) ≤ intCapMax →
      2 * (namedInstance I).n ≤ forestEdgeCap →
      DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchPrec DeepInv →
      p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc) →
      SolverInitStepSpecCreditKFBL F cfg (namedInstance I) I.m V psi k epsExp Rcore p cycleInit
        initSpace initBudget toolMul treeMul →
      ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit
        (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p chainRefreshProc
        refreshSpace refreshBudget toolMul treeMul B_bound R_bound →
      FindCycleStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace
        findBudget maxEdges maxPaths →
      ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
        forestEdgeCap (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p
        shiftLevelProc shiftSpace shiftBudget toolMul treeMul →
      GoodCycleNumericBridge F cfg (namedInstance I) I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound →
      OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V psi k epsExp initSpace
        initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
        refreshSpace refreshBudget Rcore cycleRate (cycleAllocation I.n I.m) →
      (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) →
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit (solverOpsDispatch base)
          (minRatioMachineContractWithV F
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) := by
  intro threshold A Ck deg I V k w dispatch forest p cfg F
    Rcore psi epsExp capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
    initSpace initBudget findSpace findBudget shiftSpace shiftBudget
    maxEdges maxPaths toolMul treeMul DeepInv refreshSpace refreshBudget B_bound R_bound
    hlocalCore hepsExp h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB
    hcapOffB hthrB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInit hRefresh hFind hShift hBridge
    hEnv hAllocLe
  have hVcfg : cfg.ValidOrdNoHidden :=
    Final.concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm (fun e => (hCap e).1)
  have hMonoCfg : ToolCostMono cfg.T :=
    sparseCoreBundleRestartToolMachWith_costMono (W.lsfInit F.limbs F.fmt.precision) W.C_lsst
      (Expander.chosenL (max I.m threshold ^ 2)) (fun _ => W.sparsify) W.params W.spanConst
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hImPos : 0 < I.m :=
    lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs]; omega
  have hPL : F.fmt.precision ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hαEq : cfg.α = Num.IPM.alphaPrime I.m V / 8 := rfl
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod : (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) ≤ 1 := by
      calc (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V)
          ≤ 1 * 1 := mul_le_mul hk ha (by positivity) (by norm_num)
        _ = 1 := one_mul 1
    have hE : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hpos : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (concreteEdgeThresholdWithLast_ge_two W) J hJn hJm
    (fun e => (hCap e).1)
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by
    have : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
    rw [this]; exact hIn
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  refine ⟨solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) (namedInstance I) F.limbs F.fmt.precision I.m V
      psi k epsExp (detectOffTreeDrainUnit F.limbs)
      (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget) toolMul treeMul Rcore DeepInv,
      ?_, hAllocLe⟩
  exact ordSolver_implements_full_credit (U_cap := V) hlocalCore (Or.inr hMonoCfg) hVcfg hmG hnG
    (connectedInitialInstance_connected J.toInstance (V : ℤ))
    hEΨ hw14 rfl hLpos hPL hImPos hεPos hεLe hthrB hαEq hepsExp
    (fun e he => Finset.mem_range.mpr he) h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP
    hcapEvalB hcapTreeB hcapOffB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInit hRefresh hFind
    hShift hBridge hEnv

/-- Specialization of `ordSolver_supported_full_credit` at `toolMul = 0, treeMul = 0` for
fixed-budget step specs under `KFBL`. `cfg.ValidOrdNoHidden` is discharged internally via
`Final.concreteCirculationCfgWithLast_validOrdNoHidden`. -/
theorem ordSolver_supported_full
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant))
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (cycleInit base chainRefreshProc findCycleProc shiftLevelProc : ℕ)
    (cycle : List Stmt) (cycleRate : ℕ → ℕ)
    (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ) (cycleSpace : ℕ → ℕ → ℕ)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Scaling.Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCost : J.CostsBounded (J.m ^ 10))
    (hCap : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (Final.concreteEdgeThresholdWithLast W)
        (Final.concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (Final.forestProgramsScratchDegree allocationCoefficient allocationDegree
          (Final.concreteQualityLinearCoeff
            (Final.concreteEdgeThresholdWithLast W)
            (Final.concreteQualityBudgetWithLast W))))
        source.solverWords) :
    let threshold := Final.concreteEdgeThresholdWithLast W
    let A := Final.concreteQualityBudgetWithLast W
    let Ck := Final.concreteQualityLinearCoeff threshold A
    let deg := Final.forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := Final.mrdsSolverDispatch cycleInit (solverOpsDispatch base) cycle.length
    let forest := Final.dynLctForestBodies 4 (Final.mrdsCycleBase + cycle.length)
    let p := Final.linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := Final.concreteCirculationCfgWithLast W J
    let F := ipmQualityMinRatioFormat I.m V k hw
    ∀ (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (psi epsExp capExp limbMul capLimit
        wordExp stretchPrec intCapMax forestEdgeCap
        initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths : ℕ)
      (DeepInv : ChainState cfg.T cfg.P → Prop)
      (refreshSpace refreshBudget : ℕ → ℕ) (B_bound R_bound : ℤ),
      Rcore.Local →
      epsExp = k + Num.IPM.alphaExponent I.m V + 10 →
      5 * F.limbs + 1 < 2 ^ w →
      cfg.P.d + 1 < 2 ^ w → epsExp < 2 ^ w →
      (2 * (namedInstance I).m + 2) *
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w →
      2 * (namedInstance I).n + 1 < 2 ^ w →
      Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs →
      Nat.size I.m ≤ F.rangeExponent + 8 →
      maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
      2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
        (Num.capacity 4 F.limbs : ℤ) →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
        (Num.capacity 4 F.limbs : ℤ) →
      B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
        (Num.capacity 4 F.limbs : ℤ) →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound →
      (∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
        SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap) →
      initTargetCap cfg (namedInstance I) ≤ intCapMax →
      2 * (namedInstance I).n ≤ forestEdgeCap →
      DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchPrec DeepInv →
      p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc) →
      SolverInitStepSpecCreditKFBL F cfg (namedInstance I) I.m V psi k epsExp Rcore p cycleInit
        initSpace initBudget 0 0 →
      ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit
        (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p chainRefreshProc
        refreshSpace refreshBudget 0 0 B_bound R_bound →
      FindCycleStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace
        findBudget maxEdges maxPaths →
      ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
        forestEdgeCap (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p
        shiftLevelProc shiftSpace shiftBudget 0 0 →
      GoodCycleNumericBridge F cfg (namedInstance I) I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound →
      OrdSolverContractEnvelopeFull F cfg (namedInstance I) I.m V psi k epsExp initSpace initBudget
        findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
        refreshSpace refreshBudget Rcore cycleRate (cycleAllocation I.n I.m) →
      (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) →
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit (solverOpsDispatch base)
          (minRatioMachineContractWithV F
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) := by
  intro threshold A Ck deg I V k w dispatch forest p cfg F
    Rcore psi epsExp capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
    initSpace initBudget findSpace findBudget shiftSpace shiftBudget
    maxEdges maxPaths DeepInv refreshSpace refreshBudget B_bound R_bound
    hlocalCore hepsExp h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB
    hcapOffB hthrB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInit hRefresh hFind hShift hBridge
    hEnv hAllocLe
  exact ordSolver_supported_full_credit lastTool lastConstant lastSpec W cycleInit base
    chainRefreshProc findCycleProc shiftLevelProc cycle cycleRate cycleAllocation cycleSpace
    allocationCoefficient allocationDegree source J hJn hJm hCost hCap hw Rcore psi epsExp
    capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap initSpace initBudget
    findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths 0 0 DeepInv refreshSpace
    refreshBudget B_bound R_bound hlocalCore hepsExp h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM
    hmaxEP hcapEvalB hcapTreeB hcapOffB hthrB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInit
    hRefresh hFind hShift hBridge hEnv hAllocLe

end MinCostFlow.MinRatio
