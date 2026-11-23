module

public import MinCostFlow.Final.ConcreteChainModelWithLast
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
public import MinCostFlow.IPM.NamedInstance
import Mathlib.Tactic

/-!
# Three facts on the parameters of the chain core at the dry values (`AssemblyDryRunSCCoreFacts`)

The top proof of the chain core (`ordChainUpdateCoreSpecWKFBLSel_of_parts` and
`ordChainUpdateCoreSpecWExtKFBL_of_branchB`) asks for three facts on the graph `G`, the edge
count `m` and the threshold `mThresh`, through the cost of Branch A:
`G.E.sup id ≤ G.m`, `G.m = m` and `cfg.P.M₀ ≤ m + mThresh`. At the dry values `G` is the named
instance of `I := solverConnectedAugmented J`, `m = I.m` and `mThresh` is the edge threshold
`concreteEdgeThresholdWithLast W` of the witness. The named instance has the edges
`0, …, I.m - 1`, and `M₀` is the larger of `I.m` and the threshold, so all three hold.
-/

public section

namespace MinCostFlow.Final.DryRun

open Chain IPM IPM.Machine Scaling SparseCore

/-- The edges of the named instance are `0, …, m - 1`, so their largest name is below `m`. -/
theorem dryCore_hGSup (I : Instance) : (namedInstance I).E.sup id ≤ (namedInstance I).m := by
  rw [namedInstance_m]
  refine Finset.sup_le fun e he => ?_
  simp only [namedInstance, Finset.mem_range] at he
  simp only [id]
  omega

/-- The named instance has `I.m` edges. -/
theorem dryCore_hGM (I : Instance) : (namedInstance I).m = I.m := namedInstance_m I

/-- At the dry configuration, `M₀` is the larger of the edge count of the instance and the edge
threshold of the witness, so it is at most their sum. -/
theorem dryCore_hM0Le {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) (J : Circulation) :
    (concreteCirculationCfgWithLast W J).P.M₀ ≤
      (solverConnectedAugmented J).m + concreteEdgeThresholdWithLast W := by
  have hM0Eq : (concreteCirculationCfgWithLast W J).P.M₀ =
      max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast W) := rfl
  rw [hM0Eq]
  omega

end MinCostFlow.Final.DryRun
