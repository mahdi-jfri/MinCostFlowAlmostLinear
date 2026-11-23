module

public import MinCostFlow.Final.Theorem11Core
public import MinCostFlow.MinRatio.WireChainCoreBranchBTopKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBOwnKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitCasesKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBMetaDisjEndKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBCostProved
import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProof
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProof
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLocTerm
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLocInt
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLocLevel
import MinCostFlow.MinRatio.WireChainCoreBranchBOwnRestKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailProvedKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitIntKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitTermKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitEmptyKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitAllKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadPreExitProofKFBL
import MinCostFlow.Final.AssemblyDryRunSCInnerExtEnv
import MinCostFlow.Final.AssemblyDryRunSCToolStep
import MinCostFlow.Final.AssemblyDryRunSCHandle
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayInt
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayTerm
import Mathlib.Tactic

/-!
# Theorem 1.1 from the goals of Branch B (`Theorem11Goals`)

`theorem_1_1_of_branchB` (`Final/Theorem11Core.lean`) proves Theorem 1.1 from the top goal of
Branch B and one layout fact at the dry values. Both follow from the goals of Branch B:
* the top goal: `branchBTopGoalKFBL_of_goals` and `branchBOwnGoal_of_goals`;
* the layout fact: `branchB_metaDisj_end` at the dry values
  (`dryInnerCore_branchBMetaDisj_of_goals`, below), with the same facts at the dry values as
  `dryInnerCore_extParts_of_topGoal`.

`theorem_1_1_of_goals` is Theorem 1.1 from the three exit goals of the head of the run of
Branch B. The other goals (the cost, space and model goals, the place goals of the exits, the edge
accounts, the tail of the run and the run up to the exit of the loop) enter it as proved theorems.
`theorem_1_1_proved` is Theorem 1.1 with no hypothesis, from the proofs of the three exit goals.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- The empty graph, used as the start graph of the cores in `BranchBEnvKFBL`. -/
private def goalsEmptyGraph : MGraph := ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

/-- **The layout fact of Branch B at the dry values**, from the run goal, the two forest place
goals and the space goal of Branch B. -/
theorem dryInnerCore_branchBMetaDisj_of_goals (Psc : DrySparseCorePieces)
    (hRun : BranchBRunGoalKFBL)
    (hIntF : BranchBIntExitForestLocGoalKFBL) (hTermF : BranchBTermExitForestLocGoalKFBL)
    (hSpace : BranchBSpaceGoalKFBL) : DryInnerCoreBranchBMetaDisj Psc := by
  unfold DryInnerCoreBranchBMetaDisj
  intro innerCoreCode innerSz hInnerSz coreSz hCoreSz openSz hOpen selSz hSel inner
    source J hJn hJm _ hCap hw I V k F cfg G limbMul PscP Rcore p lay w b ops env0 envIn coreBody
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hE := dryInnerCore_branchAEnvKFBL Psc (dryInitCode (dryParamCode Psc))
    drySelectRouteCode dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
  have hBEnv := dryInnerCore_branchBEnvKFBL Psc (dryInitCode (dryParamCode Psc))
    drySelectRouteCode dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
    (fun _ => goalsEmptyGraph) (fun _ => by simp [goalsEmptyGraph, MGraph.n, MGraph.m])
    (fun _ => by simp [goalsEmptyGraph, MGraph.m])
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed
      (Expander.chosenL (cfg.P.M₀ ^ 2)) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hShrink : BranchBForestShrinkKFBL cfg :=
    branchBForestShrink_of_progTool hT
      (fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj)
  have hTP : cfg.TP.Valid :=
    (concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1).hTP
  exact branchB_metaDisj_end hRun hIntF hTermF hSpace hE hBEnv branchBIntExitLayGoalKFBL_proved
    branchBTermExitLayGoalKFBL_proved
    (fun ch hInv => dryTool_branchBToolStepKFBL J hJn hJm hCap1 hInv) hShrink
    (drySCRep_handle_mem_foot Psc _ _ source J hw) hTP
    (V := V) (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (limbMul := limbMul)

/-- **Theorem 1.1 from the goals of Branch B.** The hypotheses are the exit fields of the head of
the run of Branch B, one goal for each exit of the loop. The other goals enter as proved
theorems. -/
theorem theorem_1_1_of_goals (hInt : BranchBHeadExitIntGoalKFBL)
    (hTerm : BranchBHeadExitTermGoalKFBL) (hEmpty : BranchBHeadExitEmptyGoalKFBL) :
    MinCostFlowStatement :=
  have hRun : BranchBRunGoalKFBL :=
    branchBRunGoal_of_head_tail
      (branchBRunHeadGoal_of_exit (branchBHeadExitGoal_of_cases hInt hTerm hEmpty))
      branchBRunTailGoalKFBL_proved
  theorem_1_1_of_branchB
    (branchBTopGoalKFBL_of_goals hRun branchBIntExitForestLocGoalKFBL_proved
      branchBTermExitForestLocGoalKFBL_proved branchBCostGoalKFBL_proved
      branchBSpaceGoalKFBL_proved branchBModelGoalKFBL_proved
      (branchBOwnGoal_of_goals branchBLevelLocGoalKFBL_proved
        (branchBOwnRestGoal_of_sufRecCut fun H => H.sufRecCut)))
    (dryInnerCore_branchBMetaDisj_of_goals dryPscFinal hRun
      branchBIntExitForestLocGoalKFBL_proved branchBTermExitForestLocGoalKFBL_proved
      branchBSpaceGoalKFBL_proved)

/-- **Theorem 1.1** (Min-cost flow, page 2 of arXiv:2309.16629v1), with no hypothesis. The three
exit goals of the head of Branch B are proved (`branchBHeadExitIntGoalKFBL_proved`,
`branchBHeadExitTermGoalKFBL_proved`, `branchBHeadExitEmptyGoalKFBL_proved`), so
`theorem_1_1_of_goals` applies with no hypothesis. `Comparator/Challenge.lean` states the theorem as
`MinCostFlow.theorem_1_1` and proves it from this one. -/
theorem theorem_1_1_proved : MinCostFlowStatement :=
  theorem_1_1_of_goals branchBHeadExitIntGoalKFBL_proved branchBHeadExitTermGoalKFBL_proved
    branchBHeadExitEmptyGoalKFBL_proved

end MinCostFlow.Final.DryRun

end
