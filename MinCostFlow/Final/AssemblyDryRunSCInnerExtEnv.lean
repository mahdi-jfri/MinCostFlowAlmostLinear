module

public import MinCostFlow.Final.AssemblyDryRunSCInnerEnv
public import MinCostFlow.MinRatio.WireChainCoreBranchBTopGoalKFBL
import MinCostFlow.Final.AssemblyDryRunSCInnerExtCore
import Mathlib.Tactic

/-!
# The environment of Branch B in the dry program (`AssemblyDryRunSCInnerExtEnv`)

`BranchBEnvKFBL` collects the facts on the program that Branch B of the chain core uses on top of
`BranchAEnvKFBL`: the environment of its loop (`BranchBLoopEnvKFBL`) and the bodies of six helper
procedures. This file proves it in the dry program `dryLinkedProgramSel`, at the procedure
indices of the inner block `dryInnerCoreCodeOf` (`AssemblyDryRunSCInnerCode.lean`).

The proof only gathers facts proved elsewhere:
* the bodies of the helpers come from their places in the block (`dryInnerCoreCodeOf_hasAll`);
* the contracts of the numeric helpers, the locality of the core, the format and the word bounds
  are fields of `dryInnerCore_branchAEnvKFBL`;
* the four facts on the sparse core at each level come from `drySC_coreLoopFacts_sel`, and the
  fact that `T.updateOrd` ignores lengths and gradients from `dryTool_updateOrdEqOnE`.

The start graphs `Ginit` of the cores are any graphs with `n ≤ m + 1` and `m ≤ I.m`, since the
facts on the sparse core hold at every such graph.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **`BranchBEnvKFBL` in the dry program.** For every inner block `dryInnerCoreCodeOf mkBranchB`
and all start graphs `Ginit` with `n ≤ m + 1` and `m ≤ I.m`, the environment of Branch B holds in
`dryLinkedProgramSel` at the procedure indices of the block (`b + 10` to `b + 21`), the sparse
core (`lay.scInit`, `lay.scOp`), the depth `dryDepth J` and the re-embedding function
`dryReembFn J`. -/
theorem dryInnerCore_branchBEnvKFBL (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (allocationCoefficient allocationDegree : ℕ)
    (hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      allocationCoefficient)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (Ginit : ℕ → MGraph) (hGn : ∀ j, (Ginit j).n ≤ (Ginit j).m + 1)
    (hGm : ∀ j, (Ginit j).m ≤ (solverConnectedAugmented J).m) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    let Rcore := drySCRep Psc allocationCoefficient allocationDegree source J hw
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let w := dryWordSize W allocationCoefficient allocationDegree source
    let b := lay.ordChainCore + 1
    let ops := mrdsCycleBase
    BranchBEnvKFBL w F.limbs F.fmt.precision (dryDepth J) G.n (initTargetCap cfg G) dryCapExp
      (drySCEdMul Psc dryCapExp limbMul) lay.scInit (b + 34 + dgIdxApplyBatch) (b + 15) (b + 16)
      (b + 17) (b + 18) (b + 10) (ops + 17) (ops + 11) (ops + 22) ops (b + 12) (b + 13) (b + 14)
      (b + 19) (b + 20) (b + 21) (ops + 69) F.fmt cfg PscP (drySCAlloc Psc dryCapExp limbMul J)
      Ginit (dryReembFn J) Rcore p lay.scOp := by
  intro W I V k F cfg G limbMul PscP Rcore innerCoreCode inner p lay w b ops
  have E := dryInnerCore_branchAEnvKFBL Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand allocationCoefficient allocationDegree hWordCoeff source J hJn hJm
    hCapPos hw
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hCollP, hEmitP, hZeroP, hCopyP, hUpdLenP, hSlotP,
    hCollTP, hFilterP, hPushInsP, hPushP, _⟩ :=
    dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
      mkBranchB hBNoRand
  have hFacts := fun j (hj : j < cfg.P.d) =>
    drySC_coreLoopFacts_sel Psc inner selInitCode allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw j hj (Ginit j) (hGn j) (hGm j)
  exact
    { loop :=
        { loc := E.coreLocal
          four := E.four
          prec := E.prec
          w16 := le_trans (by norm_num : (16 : ℕ) ≤ 18) E.w18.le
          updOrdEq := dryTool_updateOrdEqOnE J
          impl := fun j hj => (hFacts j hj).1
          out := fun j hj => (hFacts j hj).2.1
          place := fun j hj => (hFacts j hj).2.2.1
          footAt := fun j hj => (hFacts j hj).2.2.2
          dgApplyC := E.dgApplyC
          copyP := hCopyP
          slotP := hSlotP
          collP := hCollTP
          updLenP := hUpdLenP
          edgeP := E.edgeP
          signC := E.signC
          mulC := E.mulC
          divC := E.intDivC
          copyC := E.copyC
          dW := E.dW
          kW := E.kW }
      collectP := hCollP
      emitP := hEmitP
      zeroP := hZeroP
      filterP := hFilterP
      pushInsP := hPushInsP
      pushP := hPushP
      depthEq := rfl }

end MinCostFlow.Final.DryRun

end
