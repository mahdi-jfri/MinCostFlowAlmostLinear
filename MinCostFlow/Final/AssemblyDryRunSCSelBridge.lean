module

public import MinCostFlow.Final.AssemblyDryRunSCFixesSkeleton
public import MinCostFlow.Final.WireSelectSizes
public import MinCostFlow.MinRatio.OrdSolverWiredSel
import Mathlib.Tactic

/-!
# Dry-run select-aware solver bridge (`AssemblyDryRunSCSelBridge`)

Appends the select-init wrapper block `selInitCode` (whose entry wraps `solverCycleInit` and
initializes the select region at `(dMul, kOff) = (4, 2)`) after `dryCycle`, yielding
`dryCycleWithSelInit`, `drySelInitProc`, and `dryLinkedProgramSel` with every procedure index in
`solverOpsProcs`, `solverTail`, `lastLevel`, `sc`, and `inner` preserved.

Proves:
* `dryCycleWithSelInit_noRand`: determinism of `dryCycleWithSelInit`.
* `dryLinkedProgramSel_ops_hasAt`, `dryLinkedProgramSel_tail_hasAt`,
  `dryLinkedProgramSel_lastLevel_hasAt`, `dryLinkedProgramSel_sc_hasAt`,
  `dryLinkedProgramSel_inner_hasAt`, `dryLinkedProgramSel_selInit_hasAt`: procedure placement
  lemmas inside `dryLinkedProgramSel`.
* `dryInnerCodeSel_hasEval_sel`, `dryInnerCodeSel_hEval_proved_sel`: automatic discharge of
  `OrdCycleRouteEvalSpecW` inside `dryLinkedProgramSel`.
* `drySolver_implements_sel`: discharges `(solverStateRepSelKFBL ... (DryChainLenGridInv J)).Implements`
  inside `dryLinkedProgramSel` at `drySelInitProc` from the five select-aware specs
  (`SolverInitStepSpecSel`, `OrdChainUpdateCoreSpecWKFBLSel`, `OrdCycleRouteSelectSpecHeap`,
  `ShiftTermChainSyncSpecWExtKFBLSel`, `ShiftDeepChainSyncSpecWExtKFBLSel`), automatically
  discharging `DryFixedPointCapBounds`, `DryEnvelopeIneqs` (`dryInnerBounds_hEnv_proved`),
  `OrdCycleRouteEvalSpecW`, `DeepShiftChainInvHyps`, `DrySparseCoreCapLevels`, and the
  embedding-length bound `progTool_embLen_le_dryMaxEmbLen_of_shiftLoop`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `dryCycleWithSelInit` and `dryLinkedProgramSel` -/

/-- Environment passed to the appended select-init wrapper block `selInitCode`: identical to
`solverTailInnerEnv`, with `innerBase` positioned immediately after `dryCycle`. -/
def drySelInitEnv (threshold A : ℕ) (sc : SparseCoreCode) (inner : SolverInnerCode) :
    SolverInnerEnv :=
  { solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      sc solverTailBase with
    innerBase := mrdsCycleBase + (dryCycle threshold A sc inner).length }

/-- Cycle procedure list for the select-heap solver: `dryCycle` followed by `selInitCode`.
Every procedure index in `solverOpsProcs`, `solverTail`, `lastLevel`, `sc`, and `inner` is
unchanged. -/
def dryCycleWithSelInit (threshold A : ℕ) (sc : SparseCoreCode) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode) : List Stmt :=
  dryCycle threshold A sc inner ++ selInitCode.procs (drySelInitEnv threshold A sc inner)

/-- Entry procedure index of `selInitCode` inside `dryLinkedProgramSel`. -/
def drySelInitProc (threshold A : ℕ) (sc : SparseCoreCode) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode) : ℕ :=
  (drySelInitEnv threshold A sc inner).innerBase + selInitCode.off

/-- Linked deterministic solver program with `selInitCode` appended to `dryCycle` and dispatched as
the solver's init procedure `drySelInitProc`. -/
def dryLinkedProgramSel {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    Program :=
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let cycle := dryCycleWithSelInit threshold A sc inner selInitCode
  let initProc := drySelInitProc threshold A sc inner selInitCode
  linkedCappedSolverProgramWithV threshold A
    (mrdsSolverDispatch initProc (solverOpsDispatch mrdsCycleBase) cycle.length)
    cycle
    (dynLctForestBodies 4 (mrdsCycleBase + cycle.length))

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Determinism and placement lemmas for `dryLinkedProgramSel` -/

theorem dryCycleWithSelInit_noRand (threshold A : ℕ) {sc : SparseCoreCode}
    {inner : SolverInnerCode} (selInitCode : SolverInnerSubCode)
    (hsc : sc.prog.IsDeterministic) (hinner : inner.IsDeterministic) :
    ∀ s ∈ dryCycleWithSelInit threshold A sc inner selInitCode, s.NoRand := by
  intro s hs
  rcases List.mem_append.mp hs with h1 | h2
  · exact dryCycle_noRand threshold A hsc hinner s h1
  · exact selInitCode.hnoRand _ s h2

private theorem linked_cycle_prefix_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (cycle₁ cycle₂ forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch (cycle₁ ++ cycle₂) forest).HasAt
      mrdsCycleBase cycle₁ := by
  intro i hi
  have hlen := boundedConnectedIPMRuntimeModuleWithV_length dispatch
  simp only [linkedCappedSolverProgramWithV, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]
  exact List.getElem?_eq_getElem hi

private theorem linked_cycle_suffix_hasAt (threshold A : ℕ) (dispatch : SolverDispatch)
    (cycle₁ cycle₂ forest : List Stmt) :
    (linkedCappedSolverProgramWithV threshold A dispatch (cycle₁ ++ cycle₂) forest).HasAt
      (mrdsCycleBase + cycle₁.length) cycle₂ := by
  intro i hi
  have hlen := boundedConnectedIPMRuntimeModuleWithV_length dispatch
  simp only [linkedCappedSolverProgramWithV, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  rw [show mrdsCycleBase + cycle₁.length + i -
      (boundedConnectedIPMRuntimeModuleWithV 0 dispatch).length = cycle₁.length + i by omega]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]
  exact List.getElem?_eq_getElem hi

/-- The 183 solver operation procedures sit at `mrdsCycleBase` in `dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_ops_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    (dryLinkedProgramSel W sc inner selInitCode).HasAt mrdsCycleBase
      (solverOpsProcs mrdsCycleBase solverCycleChainRefresh solverCycleFindCycle
        solverCycleShiftLevel) := by
  have h := linked_cycle_prefix_hasAt (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W)
    (mrdsSolverDispatch
      (drySelInitProc (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode)
      (solverOpsDispatch mrdsCycleBase)
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length)
    (dryCycle (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) sc inner)
    (selInitCode.procs (drySelInitEnv (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) sc inner))
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length))
  exact Num.hasAt_append_left h

/-- The solver tail sits at `solverTailBase` in `dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_tail_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    (dryLinkedProgramSel W sc inner selInitCode).HasAt solverTailBase
      (solverTail mrdsCycleBase (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst sc inner solverTailBase) := by
  have h := linked_cycle_prefix_hasAt (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W)
    (mrdsSolverDispatch
      (drySelInitProc (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode)
      (solverOpsDispatch mrdsCycleBase)
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length)
    (dryCycle (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) sc inner)
    (selInitCode.procs (drySelInitEnv (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) sc inner))
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length))
  have hR := Num.hasAt_append_right h
  rw [solverOpsProcs_length] at hR
  exact hR

/-- The packed last-level bodies sit at `lay.lastBase` in `dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_lastLevel_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    let lay := dryTailLay sc inner
    (dryLinkedProgramSel W sc inner selInitCode).HasAt lay.lastBase
      (packedLastLevelBodies lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst lay.lastBase) :=
  solverTail_lastLevel_hasAt (dryLinkedProgramSel_tail_hasAt W sc inner selInitCode)

/-- The shifted sparse-core program sits at `lay.scBase` in `dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_sc_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    let lay := dryTailLay sc inner
    (dryLinkedProgramSel W sc inner selInitCode).HasAt lay.scBase
      (shiftProgramProcs lay.scBase sc.prog) :=
  solverTail_sparseCore_hasAt (dryLinkedProgramSel_tail_hasAt W sc inner selInitCode)

/-- The inner-level bodies sit at `lay.innerBase` in `dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_inner_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    let lay := dryTailLay sc inner
    let env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
      lastWordConst sc solverTailBase
    (dryLinkedProgramSel W sc inner selInitCode).HasAt lay.innerBase (inner.procs env) :=
  solverTail_inner_hasAt (dryLinkedProgramSel_tail_hasAt W sc inner selInitCode)

/-- The appended select-init wrapper block sits at `(drySelInitEnv ...).innerBase` in
`dryLinkedProgramSel`. -/
theorem dryLinkedProgramSel_selInit_hasAt {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (selInitCode : SolverInnerSubCode) :
    let env := drySelInitEnv (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
      sc inner
    (dryLinkedProgramSel W sc inner selInitCode).HasAt env.innerBase (selInitCode.procs env) :=
  linked_cycle_suffix_hasAt (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
    (mrdsSolverDispatch
      (drySelInitProc (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode)
      (solverOpsDispatch mrdsCycleBase)
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length)
    (dryCycle (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) sc inner)
    (selInitCode.procs (drySelInitEnv (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) sc inner))
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycleWithSelInit (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        sc inner selInitCode).length))

/-! ## 3. Automatic `OrdCycleRouteEvalSpecW` inside `dryLinkedProgramSel` -/

theorem dryInnerCodeSel_hasEval_sel (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let ops := mrdsCycleBase
    p.procs[lay.evalCycle]? =
      some (evalCycleBody (dryPathTreeOp ops 3) (ops + 2) (ops + 6)) := by
  intro inner p lay ops
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  have hEvalIdx : lay.evalCycle = lay.innerBase := by
    change lay.innerBase + 0 = lay.innerBase
    omega
  rw [hEvalIdx]
  exact hInner.head

theorem dryInnerCodeSel_hEval_proved_sel (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdCycleRouteEvalSpecW
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) cfg Rcore
        (dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode)
        (dryTailLay Psc.sc inner).evalCycle
        s.evalSpace s.evalBudget s.maxEdges s.maxPaths := by
  intro inner source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  have hw14 : 14 ≤ dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source :=
    (ipm_quality_parameter_words_fit I.m V k hw).1
  have hOps := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl
    (dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner selInitCode)
  have hEvalAt := dryInnerCodeSel_hasEval_sel Psc initCode coreCode selectCode termCode deepCode
    selInitCode
  exact evalCycleBody_meets_spec
    (w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
    (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (initTree := mrdsCycleBase + 81) (opTree := dryPathTreeOp mrdsCycleBase)
    (numAdd := mrdsCycleBase + 2) (numSub := mrdsCycleBase + 6)
    (maxEdges := (dryInnerSizesWithSelect Psc openSz selSz source J).maxEdges)
    (maxPaths := (dryInnerSizesWithSelect Psc openSz selSz source J).maxPaths)
    (fmt := F.fmt) (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    rfl (le_trans (by decide : 10 ≤ 14) hw14) hEvalAt hOps.2.2.2.2.2 hOps.2.1 hOps.2.2.2.1

/-! ## 4. Select-aware dry-run `DSRep.Implements` bridge -/

/-- **Dry-run select-aware solver `DSRep.Implements` bridge.**
Discharges `(solverStateRepSelKFBL ... (DryChainLenGridInv J)).Implements` inside
`dryLinkedProgramSel` at `drySelInitProc` from the five select-aware step specs:
1. `hInitSel : SolverInitStepSpecSel` (at `drySelInitProc`),
2. `hCoreSel : OrdChainUpdateCoreSpecWKFBLSel` (at `lay.ordChainCore`),
3. `hSelectHeap : OrdCycleRouteSelectSpecHeap` (at `lay.selectRoute`, `(dMul, kOff) = (4, 2)`),
4. `hTermSel : ShiftTermChainSyncSpecWExtKFBLSel` (at `lay.shiftTermChain`),
5. `hDeepSel : ShiftDeepChainSyncSpecWExtKFBLSel` (at `lay.shiftDeepChain`).

All envelope inequalities, fixed-point capacity bounds, `OrdCycleRouteEvalSpecW`, sparse-core
level capacity hypotheses, `DeepShiftChainInvHyps`, and embedding-length bounds are discharged
automatically. -/
theorem drySolver_implements_sel
    (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz)
    (pot : (source J : Circulation) →
      (concreteCirculationCfgWithLast dryWitnessUsed J).T.State → ℕ)
    (hInitSel :
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      let initProc := drySelInitProc (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner selInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        SolverInitStepSpecSel F cfg G I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
            (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220))
          s.toolMul s.treeMul 4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m)
          (pot source J) Rcore p initProc
          (s.initSpace' + initWiredExtraSpace cfg G) (s.initFixed + initWiredExtraCost cfg G))
    (hCoreSel :
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        OrdChainUpdateCoreSpecWKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
          dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J)
          (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
          4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m) cfg G (pot source J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul)
    (hSelectHeap :
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        OrdCycleRouteSelectSpecHeap
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) 4 2 cfg Rcore
          p (dryTailLay Psc.sc inner).selectRoute
          s.selectSpace s.selectBudget s.maxEdges s.maxPaths)
    (hTermSel :
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        ShiftTermChainSyncSpecWExtKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) (2 * levelM cfg.TP cfg.P cfg.P.d)
          G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) F.rangeExponent
          (dryLastStretchP J) (drySlot I.m) cfg G (pot source J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).shiftTermChain
          s.termSpace s.termFixed s.toolMul s.treeMul)
    (hDeepSel :
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        ShiftDeepChainSyncSpecWExtKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J)
          (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
          (dryLastStretchP J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
          G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) F.rangeExponent
          (dryLastStretchP J) (drySlot I.m) cfg G (pot source J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).shiftDeepChain
          s.deepSpace s.deepFixed s.toolMul s.treeMul) :
    let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
    let B := dryInnerBounds Psc openSz hOpen selSz hSel
    let hB := dryInnerBounds_hyp Psc openSz hOpen selSz hSel
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let initProc := drySelInitProc (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner selInitCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      let unit := cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
        (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
      let Rsel := solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision I.m V
        ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
        unit s.toolMul s.treeMul 4 2 F.rangeExponent (dryLastStretchP J) (drySlot I.m) s.maxPaths
        Rcore (selSz.keyCost source J) (pot source J) (DryChainLenGridInv J)
      Rsel.Implements
        (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
        p initProc (solverOpsDispatch mrdsCycleBase)
        (minRatioMachineContractWithV F
          (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G I.m V
          (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
          B.cycleRate (B.cycleAllocation I.n I.m)) := by
  intro openSz hOpen B hB inner p initProc source J hJn hJm hCost hCap hw
  dsimp only
  let coeff := dryAllocCoeffFull B hB
  let deg := dryAllocDeg B hB
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let s := dryInnerSizesWithSelect Psc openSz selSz source J
  let lay := dryTailLay Psc.sc inner
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤ coeff :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        coeff :=
    le_max_right _ _
  obtain ⟨hQuotaBoundW, _⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
      coeff deg hWordCoeff source J hJn hJm hCap1 hw
  have hCapB := dryFixedPointCapBounds_of_bounds B hB (dryInnerSizesWithSelect Psc openSz selSz)
    (dryInnerSizesWithSelect_capSimpleBounds Psc openSz selSz B hB
      (drySelect_hMaxEP coeff deg))
  obtain ⟨hthrB, _, _, hmaxEP, hcapEvalB, hcapTreeB, hcapOffB⟩ :=
    hCapB source J hJn hJm hCost hCap hw
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
  have hE1 : 1 ≤ F.rangeExponent := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]; omega
  -- The budget after `2 G.m` updates fits under `B_bound = R_bound = 2^(P + 80 E)`.
  have hBudgetB := treeBudget_le_pow (P := F.fmt.precision) (m := G.m) (maxPaths := s.maxPaths)
    hE1 (by rw [namedInstance_m]; exact hsizeM) (lt_of_le_of_lt (Nat.le_add_left _ _) hmaxEP)
  have hTail := dryLinkedProgramSel_tail_hasAt dryWitnessUsed Psc.sc inner selInitCode
  have hOps := dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner selInitCode
  have hEval := dryInnerCodeSel_hEval_proved_sel Psc initCode coreCode selectCode termCode
    deepCode selInitCode openSz hOpen selSz hSel source J hJn hJm hCost hCap hw
  have hEnv := dryInnerBounds_hEnv_proved Psc openSz hOpen selSz hSel
    source J hJn hJm hCost hCap hw
  have hMaxEdges1 : 1 ≤ s.maxEdges := by
    change 1 ≤ dryMaxEmbLen I.m + 1; omega
  have hMaxEP2 : 2 * s.maxEdges ≤ s.maxPaths := by
    change 2 * dryMaxEdges I.m ≤ 2 * dryMaxEdges I.m; exact le_rfl
  have hEmbBd : ∀ (ch : ChainState cfg.T cfg.P),
      Ordered.ShiftLoopChainInv cfg ch →
      ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
        (ch.toTreeChain.activeEmb i e).length + 1 ≤ s.maxEdges :=
    fun ch hSh i hi e he =>
      (progTool_embLen_le_dryMaxEmbLen_of_shiftLoop J hJn hJm hCap1 hSh i hi e
        (Finset.mem_sdiff.mp he).1).2
  have hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J →
      SparseCoreCapHyp dryCapExp (concreteReadout2LimbMul dryWitnessUsed) F.limbs
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap :=
    fun i hi vCap eCap hlim =>
      concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap1 i hi.le vCap eCap hlim
  have hDeepInv := dryChainLenGridInv_deepShiftChainInvHyps coeff deg
    (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
    (dryLastStretchP J) hSCWordCoeff source J hJn hJm hCap1 hw
    (drySCWordBound_proved Psc coeff deg hSCWordCoeff source J hJn hJm hCost hCap hw)
    (dryLastStretchP_im_le_100_E J hJn hJm hCap1)
  exact ordSolver_implements_sel_concrete dryLastTool dryLastConstant dryLastSpec dryWitnessUsed
    initProc mrdsCycleBase solverCycleChainRefresh lay.ordEdits lay.ordChainCore
    lay.shiftQuotaWriter solverCycleFindCycle lay.selectRoute lay.evalCycle
    solverCycleShiftLevel lay.shiftTermChain lay.shiftDeepChain
    (dryCycleWithSelInit (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner selInitCode)
    B.cycleRate B.cycleAllocation coeff deg source J hJn hJm hCost hCap hw
    (drySCRep Psc coeff deg source J hw) (pot source J)
    dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J)
    (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
    (dryLastStretchP J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
    4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m)
    (s.initSpace' + initWiredExtraSpace cfg G) (s.initFixed + initWiredExtraCost cfg G)
    s.selectSpace s.selectBudget s.evalSpace s.evalBudget
    s.termSpace s.termFixed s.deepSpace s.deepFixed
    s.maxEdges s.maxPaths s.toolMul s.treeMul (DryChainLenGridInv J)
    s.coreSpace s.coreFixed s.B_bound s.R_bound
    (drySCRep_local Psc coeff deg source J hw)
    hQuotaBoundW hthrB hmaxEP hMaxEdges1 hMaxEP2 hEmbBd hcapEvalB hcapTreeB hcapOffB hBudgetB
    hCapLevels (dryInitTargetCap_le_intCapMax J hJn hJm hCap1) (dryTwoMulN_le_forestEdgeCap J)
    hDeepInv hOps
    (solverTail_chainRefresh_at hTail)
    (solverTail_ordEdits_at hTail)
    (solverTail_shiftQuotaWriter_at hTail)
    (solverTail_findCycle_at hTail)
    (solverTail_shiftLevel_at hTail)
    (hInitSel source J hJn hJm hCost hCap hw)
    (hCoreSel source J hJn hJm hCost hCap hw)
    (hSelectHeap source J hJn hJm hCost hCap hw)
    hEval
    (hTermSel source J hJn hJm hCost hCap hw)
    (hDeepSel source J hJn hJm hCost hCap hw)
    hEnv

end MinCostFlow.Final.DryRun

end
