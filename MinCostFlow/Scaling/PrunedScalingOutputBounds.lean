module

public import MinCostFlow.Scaling.PrunedScalingContract
import MinCostFlow.Scaling.CostCapacityCorrectness

/-!
# Bounds on the restored pruned circulation flow

Optimality of the composed solver on the positive-capacity subgraph is
preserved by the model's integer scatter. Hence the exact restored output
is feasible on the original circulation. Its nonnegative coordinates can
be copied to unsigned words for the objective and residual procedures.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The exact counted pruning adapter returns an optimal circulation on
the original graph, using only the bounded solver's supplied contract. -/
theorem prunedScalingModel_optimal (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    J.Optimal (fun e => ((Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C U) J).value e : ℝ)) := by
  change J.Optimal (fun e => ((J.scatterPositive
    (costCapacityModel (canonicalSolver solver entry T hproc) J.withoutZeroEdges C U).value e : ℤ) : ℝ))
  rw [J.scatterPositive_cast]
  apply J.scatterPositive_optimal
  exact costCapacityModel_optimal (canonicalSolver solver entry T hproc)
    (fun K _ _ => canonicalSolver_optimal solver entry T hproc K) J.withoutZeroEdges C U hU
    (fun e => hC (J.positiveIndex e)) (fun e => hu (J.positiveIndex e))

/-- Every restored coordinate is nonnegative and bounded by its original
capacity, including coordinates removed by pruning. -/
theorem prunedScalingModel_output_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    ∀ e,0≤(Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C U) J).value e ∧
      (Circulation.invokePruned
        (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C U) J).value e≤(J.capacity e : ℤ) := by
  have hopt := prunedScalingModel_optimal solver entry T hproc J C U hC hu hU
  intro e
  exact ⟨Int.cast_nonneg_iff.mp (hopt.1.2 e).1,
    (Int.cast_le (R := ℝ)).mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)⟩

end MinCostFlow.Scaling.Machine
