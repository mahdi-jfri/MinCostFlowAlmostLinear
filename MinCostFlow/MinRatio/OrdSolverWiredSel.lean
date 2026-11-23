module

public import MinCostFlow.MinRatio.OrdSolverImplementsSel
public import MinCostFlow.MinRatio.OrdChainRefreshWiredSel
public import MinCostFlow.MinRatio.ShiftLevelWiredSel
public import MinCostFlow.MinRatio.OrdSolverWiredFull
import MinCostFlow.MinRatio.GoodCycleBridgeWired
import MinCostFlow.IPM.ConnectedInitialConstruction
import Mathlib.Tactic

/-!
# End-to-end wired select-aware solver assembly (`OrdSolverWiredSel`)

Connects the select-aware inner specifications (`SolverInitStepSpecSel`,
`OrdChainUpdateCoreSpecWKFBLSel`, `OrdCycleRouteSelectSpecHeap`, `OrdCycleRouteEvalSpecW`,
`ShiftTermChainSyncSpecWExtKFBLSel`, `ShiftDeepChainSyncSpecWExtKFBLSel`) into
`ordSolver_implements_sel_credit` (`OrdSolverImplementsSel.lean`) via:
* `chainRefreshStepSpecWKFBLSel_wired` (`OrdChainRefreshWiredSel.lean`) + `shiftQuotaWriterSpec_proved`;
* `findCycleStepSpecHeap_wired` (`WireSelectSpec.lean`);
* `shiftLevelStepSpecWKFBLSel_wired` (`ShiftLevelWiredSel.lean`).

Also provides:
* `solverInitWiredSel_cost_to_spec`: arithmetic adapter reducing `solverInitWiredSel_runs`'s
  credit-and-runtime init cost bound to `SolverInitStepSpecSel`'s envelope bound whenever
  `initMul + K ≤ toolMul`.
* `ordSolver_implements_sel_wired`: wired `solverStateRepSelKFBL.Implements` theorem.
* `ordSolver_supported_sel_wired`: concrete circulation `supported` theorem mirroring
  `ordSolver_supported_full_wired` (`OrdSolverWiredFull.lean`) for `solverStateRepSelKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- Arithmetic adapter from `solverInitWiredSel_runs`'s amortized init cost bound
(`SelectInitWired.lean`) to `SolverInitStepSpecSel`'s envelope bound: on
`s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀`, whenever `initMul + K ≤ toolMul` and
`s0.chain.totalRuntime ≤ chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0)`, the term
`toolMul * runtimeCredit cfg s0 + (initMul + K) * s0.chain.totalRuntime` is bounded by
`toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0)`, and `treeCredit cfg s0` is
bounded by `chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0)`. -/
theorem solverInitWiredSel_cost_to_spec {cfg : Alg2Config} {G₀ : MGraph} {g₀ ℓ₀ : ℕ → ℝ}
    {cost phi initBudget fixedCost unit initQuota toolMul treeMul initMul K : ℕ}
    (hRtCap : (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain.totalRuntime ≤
      chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0))
    (hMulLe : initMul + K ≤ toolMul)
    (hFixLe : fixedCost ≤ initBudget)
    (hCost :
      let s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀
      cost + phi ≤
        fixedCost + unit * initQuota + toolMul * runtimeCredit cfg s0 +
          treeMul * treeCredit cfg s0 + (initMul + K) * s0.chain.totalRuntime) :
    cost + phi ≤
      initBudget + unit * initQuota +
        toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
        treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) := by
  set s0 := Ordered.algorithm2_init cfg G₀ g₀ ℓ₀
  obtain ⟨_, _, hrcEq, htcEq, hrcCap, htcCap⟩ := credits_init_le cfg G₀ g₀ ℓ₀
  have hRt : toolMul * runtimeCredit cfg s0 + (initMul + K) * s0.chain.totalRuntime ≤
      toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) := by
    have h1 : (initMul + K) * s0.chain.totalRuntime ≤ toolMul * s0.chain.totalRuntime :=
      Nat.mul_le_mul_right _ hMulLe
    have h2 : toolMul * runtimeCredit cfg s0 + toolMul * s0.chain.totalRuntime =
        toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) := by
      rw [← Nat.mul_add, hrcEq, hrcCap, Nat.sub_add_cancel hRtCap]
    omega
  have hTu : treeMul * treeCredit cfg s0 ≤
      treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) := by
    refine Nat.mul_le_mul_left treeMul ?_
    rw [htcEq, htcCap]
    exact Nat.sub_le _ _
  dsimp only at hCost
  change cost + phi ≤
    fixedCost + unit * initQuota + toolMul * runtimeCredit cfg s0 +
      treeMul * treeCredit cfg s0 + (initMul + K) * s0.chain.totalRuntime at hCost
  omega

/-- **End-to-end wired select-aware `DSRep.Implements` theorem.**
Wires `SolverInitStepSpecSel`, `OrdChainUpdateCoreSpecWKFBLSel`, `OrdCycleRouteSelectSpecHeap`,
`OrdCycleRouteEvalSpecW`, `ShiftTermChainSyncSpecWExtKFBLSel`, and
`ShiftDeepChainSyncSpecWExtKFBLSel` through `chainRefreshStepSpecWKFBLSel_wired`,
`shiftQuotaWriterSpec_proved`, `findCycleStepSpecHeap_wired`, `shiftLevelStepSpecWKFBLSel_wired`,
and `ordSolver_implements_sel_credit` to establish `solverStateRepSelKFBL.Implements`. -/
theorem ordSolver_implements_sel_wired
    {w base initProc threshold
      chainRefreshProc ordEditsProc ordChainCoreProc shiftQuotaWriterProc
      findCycleProc selectRouteProc evalCycleProc
      shiftLevelProc shiftTermChainProc shiftDeepChainProc
      m U_cap V psi k epsExp capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
      dMul kOff K pLast slot initSpace initBudget selectSpace selectBudget evalSpace evalBudget
      termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {p : Program} {B_bound R_bound : ℤ}
    {coreSpace coreFixed : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hM₀Eq : cfg.P.M₀ = max m threshold)
    (hpsiEq : psi = ⌈cfg.Ψ⌉₊) (hkW : cfg.P.k < 2 ^ w)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hGE : G.E = Finset.range m)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hQuotaBoundW : (2 * G.m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hMaxEdges1 : 1 ≤ maxEdges) (hMaxEP2 : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch →
      ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
        (ch.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hBudgetB : treeBudgetBase F.fmt.precision F.rangeExponent +
        2 * (G.m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤
        B_bound ∧
      2 * (G.m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤ R_bound)
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hIntCapMax : initTargetCap cfg G ≤ intCapMax)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepInv : DeepShiftChainInvHyps w F cfg G k wordExp stretchPrec DeepInv)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hRefAt : p.procs[chainRefreshProc]? =
      some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc))
    (hEditsAt : p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody)
    (hQuotaAt : p.procs[shiftQuotaWriterProc]? = some (shiftQuotaWriterBody threshold))
    (hFindAt : p.procs[findCycleProc]? =
      some (ordFindCycleWiredBody selectRouteProc evalCycleProc))
    (hShiftAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hInit : SolverInitStepSpecSel F cfg G m V psi k epsExp
      (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
        (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
      toolMul treeMul dMul kOff K pLast slot pot Rcore p initProc initSpace initBudget)
    (hCore : OrdChainUpdateCoreSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent m V psi k
      epsExp (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit intCapMax forestEdgeCap
      G.n (initTargetCap cfg G) dMul kOff K pLast slot cfg G pot DeepInv Rcore p ordChainCoreProc
      coreSpace coreFixed toolMul treeMul)
    (hSel : OrdCycleRouteSelectSpecHeap w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) dMul kOff cfg Rcore p selectRouteProc
      selectSpace selectBudget maxEdges maxPaths)
    (hEval : OrdCycleRouteEvalSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) cfg Rcore p evalCycleProc evalSpace evalBudget
      maxEdges maxPaths)
    (hTerm : ShiftTermChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit (2 * levelM cfg.TP cfg.P cfg.P.d)
      G.n (initTargetCap cfg G) dMul kOff K F.rangeExponent pLast slot cfg G pot DeepInv Rcore p
      shiftTermChainProc termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap G.n (initTargetCap cfg G) dMul kOff K F.rangeExponent pLast slot cfg G pot
      DeepInv Rcore p shiftDeepChainProc deepSpace deepFixed toolMul treeMul)
    (hBridge : ∀ Bb Rb : ℤ, GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths Bb Rb)
    (hEnv : OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp
      initSpace initBudget
      (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
      (max termSpace deepSpace)
      (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
      maxEdges maxPaths toolMul treeMul
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
        62 * (cfg.P.d + 1) + 240)
      Rcore rate alloc) :
    (solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs)
      (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
        (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
      toolMul treeMul dMul kOff F.rangeExponent pLast slot maxPaths Rcore K pot DeepInv).Implements
      w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) := by
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hQuota := shiftQuotaWriterSpec_proved (w := w) (L := F.limbs) (P := F.fmt.precision)
    (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
    (drainUnit := detectOffTreeDrainUnit F.limbs) (cfg := cfg) (Rcore := Rcore)
    hQuotaAt hM₀Eq hpsiEq
  have hRefresh := chainRefreshStepSpecWKFBLSel_wired hlocalCore hRefAt hEditsAt hCore hQuota
    (by omega) hdW
  have hFind := findCycleStepSpecHeap_wired hlocalCore hFindAt hSel hEval (by omega)
  have hShift := shiftLevelStepSpecWKFBLSel_wired hShiftAt hV hTerm hDeep hw17 hdW hkW
  exact ordSolver_implements_sel_credit (U_cap := U_cap) hlocalCore hMono hV hmG hnG hConn hEΨ
    hw hfmt4 hLpos hPL hmPos hεPos hεLe hthrB hα hepsExp
    (fun e he => hGE ▸ Finset.mem_range.mpr he) h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM
    hmaxEP hMaxEdges1 hMaxEP2 hEmbBd hcapEvalB hcapTreeB hcapOffB hBudgetB hCapLevels hIntCapMax
    hFEdgeCap hDeepInv hp hInit hRefresh hFind hShift hBridge hEnv

/-- **Concrete circulation `solverStateRepSelKFBL.Implements` theorem from the six select-aware
inner specs.** Automatically discharges `cfg.ValidOrdNoHidden`, `ToolCostMono cfg.T`,
`GoodCycleNumericBridge`, and all unconditional concrete word-size/format inequalities, mirroring
`ordSolver_supported_full_wired` (`OrdSolverWiredFull.lean`). -/
theorem ordSolver_implements_sel_concrete
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant))
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (cycleInit base
      chainRefreshProc ordEditsProc ordChainCoreProc shiftQuotaWriterProc
      findCycleProc selectRouteProc evalCycleProc
      shiftLevelProc shiftTermChainProc shiftDeepChainProc : ℕ)
    (cycle : List Stmt) (cycleRate : ℕ → ℕ)
    (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ)
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
    let psi := ⌈cfg.Ψ⌉₊
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    ∀ (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
      (pot : cfg.T.State → ℕ)
      (capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
        dMul kOff K pLast slot initSpace initBudget selectSpace selectBudget evalSpace
        evalBudget termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul : ℕ)
      (DeepInv : ChainState cfg.T cfg.P → Prop)
      (coreSpace coreFixed : ℕ → ℕ) (B_bound R_bound : ℤ),
      Rcore.Local →
      (2 * (namedInstance I).m + 2) *
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound →
      maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
      1 ≤ maxEdges →
      2 * maxEdges ≤ maxPaths →
      (∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch →
        ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
          (ch.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges) →
      2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
        (Num.capacity 4 F.limbs : ℤ) →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
        (Num.capacity 4 F.limbs : ℤ) →
      B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
        (Num.capacity 4 F.limbs : ℤ) →
      treeBudgetBase F.fmt.precision F.rangeExponent +
          2 * ((namedInstance I).m : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤ B_bound ∧
        2 * ((namedInstance I).m : ℤ) *
          ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤ R_bound →
      (∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
        SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap) →
      initTargetCap cfg (namedInstance I) ≤ intCapMax →
      2 * (namedInstance I).n ≤ forestEdgeCap →
      DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchPrec DeepInv →
      p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc) →
      p.procs[chainRefreshProc]? =
        some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc) →
      p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody →
      p.procs[shiftQuotaWriterProc]? = some (shiftQuotaWriterBody threshold) →
      p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectRouteProc evalCycleProc) →
      p.procs[shiftLevelProc]? = some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc) →
      SolverInitStepSpecSel F cfg (namedInstance I) I.m V psi k epsExp
        (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
          (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
        toolMul treeMul dMul kOff K pLast slot pot Rcore p cycleInit initSpace initBudget →
      OrdChainUpdateCoreSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit intCapMax forestEdgeCap
        (namedInstance I).n (initTargetCap cfg (namedInstance I)) dMul kOff K pLast slot cfg
        (namedInstance I) pot DeepInv Rcore p ordChainCoreProc
        coreSpace coreFixed toolMul treeMul →
      OrdCycleRouteSelectSpecHeap w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) dMul kOff cfg Rcore p selectRouteProc
        selectSpace selectBudget maxEdges maxPaths →
      OrdCycleRouteEvalSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) cfg Rcore p evalCycleProc evalSpace evalBudget
        maxEdges maxPaths →
      ShiftTermChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit (2 * levelM cfg.TP cfg.P cfg.P.d)
        (namedInstance I).n (initTargetCap cfg (namedInstance I)) dMul kOff K F.rangeExponent
        pLast slot cfg (namedInstance I) pot DeepInv Rcore p shiftTermChainProc
        termSpace termFixed toolMul treeMul →
      ShiftDeepChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
        forestEdgeCap (namedInstance I).n (initTargetCap cfg (namedInstance I)) dMul kOff K
        F.rangeExponent pLast slot cfg (namedInstance I) pot DeepInv Rcore p shiftDeepChainProc
        deepSpace deepFixed toolMul treeMul →
      OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V psi k epsExp
        initSpace initBudget
        (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
        (max termSpace deepSpace) (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
        maxEdges maxPaths toolMul treeMul
        (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
        (fun uLen => coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
          62 * (cfg.P.d + 1) + 240)
        Rcore cycleRate (cycleAllocation I.n I.m) →
      (solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) (namedInstance I) F.limbs F.fmt.precision I.m V
        psi k epsExp (detectOffTreeDrainUnit F.limbs)
        (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
          (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
        toolMul treeMul dMul kOff F.rangeExponent pLast slot maxPaths Rcore K pot DeepInv).Implements
        w p cycleInit
        (solverOpsDispatch base)
        (minRatioMachineContractWithV F
          (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
          (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
          cycleRate (cycleAllocation I.n I.m)) := by
  intro threshold A Ck deg I V k w dispatch forest p cfg F psi epsExp
    Rcore pot capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
    dMul kOff K pLast slot initSpace initBudget selectSpace selectBudget evalSpace
    evalBudget termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul DeepInv
    coreSpace coreFixed B_bound R_bound hlocalCore hQuotaBoundW hthrB hmaxEP hMaxEdges1 hMaxEP2
    hEmbBd hcapEvalB hcapTreeB hcapOffB hBudgetB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hRefAt
    hEditsAt hQuotaAt hFindAt hShiftAt hInit hCore hSel hEval hTerm hDeep hEnv
  have hVcfg : cfg.ValidOrdNoHidden :=
    Final.concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm (fun e => (hCap e).1)
  have hMonoCfg : ToolCostMono cfg.T :=
    sparseCoreBundleRestartToolMachWith_costMono (W.lsfInit F.limbs F.fmt.precision) W.C_lsst
      (Expander.chosenL (max I.m threshold ^ 2)) (fun _ => W.sparsify) W.params W.spanConst
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm hImGeJm
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs]; omega
  have hPL : F.fmt.precision ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
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
  obtain ⟨_, _, _, _, hIn⟩ := Final.concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (Final.concreteEdgeThresholdWithLast_ge_two W) J hJn hJm
    (fun e => (hCap e).1)
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have h5L1W : 5 * F.limbs + 1 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have h1 : 5 * F.limbs + 1 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k := by
      have : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
      omega
    exact lt_of_le_of_lt h1 hB14
  have hbaseGe10 : 10 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
    shiftQuotaBase_ge_ten _ _ cfg.P.hk
  have hbasePowLt : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w := by
    have h1 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * (namedInstance I).m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt h1 hQuotaBoundW
  have hkW : cfg.P.k < 2 ^ w := by
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase
      have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    exact lt_of_le_of_lt (h1.trans h2) hbasePowLt
  have hdW : cfg.P.d + 1 < 2 ^ w := by
    have h1 : cfg.P.d + 1 < 2 ^ (cfg.P.d + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (cfg.P.d + 1) ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.pow_le_pow_left (by omega) _
    exact lt_trans (lt_of_lt_of_le h1 h2) hbasePowLt
  have hepsW : epsExp < 2 ^ w := by
    have hkLe : k ≤ F.rangeExponent := by
      have h1 := qualityExponent_le_qualitySlackExponent I.m V k
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]; omega
    have haLe : Num.IPM.alphaExponent I.m V ≤ F.fmt.precision :=
      (ipm_quality_precision_margins I.m V k).2.2.2.2.2
    have hEP : F.rangeExponent + F.fmt.precision + 10 ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have h2 : ipmQualityParameterBound I.m V k < 2 ^ w := by
      have h1 : ipmQualityParameterBound I.m V k ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k :=
        Nat.le_mul_of_pos_left _ (by decide)
      exact lt_of_le_of_lt h1 hB14
    dsimp only [epsExp]; omega
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hInDef : I.n = J.n + 1 := rfl
    omega
  have h2nW : 2 * (namedInstance I).n + 1 < 2 ^ w := by
    rw [hInEq]
    have h20 : 20 * I.m < 2 ^ w := hfit.2.2.2.2.2.1
    omega
  have hlogW : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs := by
    rw [hInEq]
    have hlt : 2 * I.n + 1 < 2 ^ (I.m.size + 4) := by
      have hmSz : I.m < 2 ^ I.m.size := Nat.lt_size_self I.m
      have h16 : 2 ^ (I.m.size + 4) = 16 * 2 ^ I.m.size := by rw [pow_add]; ring
      omega
    have hlogLt : Nat.log 2 (2 * I.n + 1) < I.m.size + 4 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    have hSzP : 5 * F.rangeExponent + I.m.size + 30 ≤ F.fmt.precision :=
      (ipm_quality_precision_margins I.m V k).2.2.1
    omega
  have hsizeM : Nat.size I.m ≤ F.rangeExponent + 8 := by
    have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
      (Nat.le_add_right _ _).trans (Nat.le_self_pow (by decide) _)
    have h2 : (I.m.size + V.size) ^ 2 ≤ slackRangeExponent I.m V :=
      Nat.le_mul_of_pos_left _ (by decide)
    have h3 : slackRangeExponent I.m V ≤ qualitySlackExponent I.m V k :=
      slackRangeExponent_le_qualitySlackExponent I.m V k
    have h4 : qualitySlackExponent I.m V k ≤ F.rangeExponent := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]; omega
    omega
  exact ordSolver_implements_sel_wired (U_cap := V) hlocalCore (Or.inr hMonoCfg) hVcfg hmG hnG
    (connectedInitialInstance_connected J.toInstance (V : ℤ))
    hEΨ hw14 rfl hLpos hPL hImPos rfl rfl hkW hεPos hεLe rfl hthrB rfl rfl h5L1W hdW hepsW
    hQuotaBoundW h2nW hlogW hsizeM hmaxEP hMaxEdges1 hMaxEP2 hEmbBd hcapEvalB hcapTreeB hcapOffB
    hBudgetB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hRefAt hEditsAt hQuotaAt hFindAt hShiftAt
    hInit hCore hSel hEval hTerm hDeep
    (fun Bb Rb => goodCycleNumericBridge_wired F cfg (namedInstance I) I.m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths Bb Rb)
    hEnv

end MinCostFlow.MinRatio
