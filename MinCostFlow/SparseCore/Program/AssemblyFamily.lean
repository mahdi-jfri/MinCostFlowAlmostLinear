module

public import MinCostFlow.SparseCore.Program.AssemblyStatement
public import MinCostFlow.Final.ConcreteChainModelWithLast

/-!
# The tool of the statement is the tool of each instance

The final witness keeps a family `lsfInit : ℕ → ℕ → LSFInit` of LSF initializers, indexed by the
limb count and the precision, and the configuration of an instance `J` uses the member at the
format `F = ipmQualityMinRatioFormat I.m V k` of the solver (`concreteCirculationCfgWithLast_T`).
The statement `SparseCoreOrdProgramUniform` chooses its constants for the whole family and uses
the member at the contract's own limb count `L` and precision `fmt.precision`.

`concreteCirculationCfgWithLast_T_eq_progTool` checks that the two meet. When the witness's
sparsifier is `canonicalSparsify impl`, the tool of the configuration of `J` is
`sparseCoreProgTool` at the member `W.lsfInit F.limbs F.fmt.precision` and the depth
`chosenL (max I.m threshold ^ 2)`. So the solver can call the core contract with its own format
`F.fmt`, its own limb count `F.limbs`, and this depth, and get the tool of its configuration.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Chain MinCostFlow.IPM MinCostFlow.IPM.Machine MinCostFlow.Final
  MinCostFlow.Scaling
  MinCostFlow.DynSpanner.Program

/-- The tool of the configuration of an instance is the tool of the statement at the solver's
format, when the witness's sparsifier is `canonicalSparsify impl`. -/
theorem concreteCirculationCfgWithLast_T_eq_progTool
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) (impl : SparsifyImpl)
    (hsp : W.sparsify = canonicalSparsify impl)
    (hpar : W.params = canonicalSparsifyParams impl)
    (hconst : W.spanConst = dsAmortConst impl)
    (J : Circulation) {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast W
    let k := cappedQualityExponent threshold (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    (concreteCirculationCfgWithLast W J).T =
      sparseCoreProgTool (W.lsfInit F.limbs F.fmt.precision) W.C_lsst
        (Expander.chosenL (max I.m threshold ^ 2)) impl := by
  intro I V threshold k F
  rw [concreteCirculationCfgWithLast_T W J hw]
  simp only [sparseCoreProgTool, hsp, hpar, hconst]
  rfl

end MinCostFlow.SparseCore.Program
