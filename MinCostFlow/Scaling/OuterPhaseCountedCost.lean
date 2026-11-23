module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
public import MinCostFlow.Scaling.ResidualOptimizationContract
import MinCostFlow.Scaling.PrunedScalingCountedCost
import MinCostFlow.Scaling.OuterCallDimensions

/-!
# Charging the two complete phases to their exact inner models

Both pruned circulation solves compare their primitive time with the same
`T(8*n,72*m)` original dimensions. Their exact model calls and work remain
unchanged. The original-slot pruning overhead and all other phase
instructions add at most `7000*(m+n+1)` per phase, including empty graphs.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The complete first phase is charged to its exact counted pruned
feasibility solve and linear original-input work. -/
theorem feasibilityPhase_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hiso : FlowReduction.isolatedCheck I hv=true) (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C
        (FlowReduction.scalingCapacityBudget I U)) (FlowReduction.buildFeasibilityInstance I hv)
    (feasibilityPhaseContract w solver entry T hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+
        303000*(solver.regBound+1)*r.work+7000*(I.m+I.n+1) := by
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let r := Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P
  have h := prunedScaling_cost_counted w solver entry T hproc hmono P C B (8*I.n) (72*I.m)
    (feasibility_compacted_solver_dimensions I hv hiso) [] (fun _ => 0)
  change (prunedScalingContract w solver entry T hproc P C B).cost [] (fun _ => 0)+4000*(I.m+I.n+1)≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+303000*(solver.regBound+1)*r.work+7000*(I.m+I.n+1)
  change (prunedScalingContract w solver entry T hproc P C B).cost [] (fun _ => 0)≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+303000*(solver.regBound+1)*r.work+1000*P.m+1000 at h
  have hPm : P.m=I.m+(I.n+I.n) := rfl
  omega

/-- The complete residual optimization phase is charged to its exact
counted pruned correction and linear original-input work. -/
theorem residualOptimization_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C
        (FlowReduction.scalingCapacityBudget I U)) ((FlowReduction.shiftedGraph I hv).residual f)
    (residualOptimizationContract w solver entry T hproc I hv f C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+
        303000*(solver.regBound+1)*r.work+7000*(I.m+I.n+1) := by
  let R := (FlowReduction.shiftedGraph I hv).residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let r := Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) R
  have h := prunedScaling_cost_counted w solver entry T hproc hmono R C B (8*I.n) (72*I.m)
    (residual_compacted_solver_dimensions I hv f) [] (fun _ => 0)
  change (prunedScalingContract w solver entry T hproc R C B).cost [] (fun _ => 0)+2000*I.m+1000≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+303000*(solver.regBound+1)*r.work+7000*(I.m+I.n+1)
  change (prunedScalingContract w solver entry T hproc R C B).cost [] (fun _ => 0)≤
    r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+303000*(solver.regBound+1)*r.work+1000*R.m+1000 at h
  have hRm : R.m=I.m+I.m := rfl
  omega

end MinCostFlow.Scaling.Machine
