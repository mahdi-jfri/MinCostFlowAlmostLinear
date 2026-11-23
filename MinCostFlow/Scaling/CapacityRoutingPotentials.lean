module

public import MinCostFlow.Scaling.CapacityRoutingValues

/-!
# Labels in capacity-backed measured dual extraction

Restrict the optimized source-routing labels to the original vertices.
Applied to a primal residual, this is exactly the measured cost model's
dual-extraction value when capacity scaling supplies its inner procedure.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Old-vertex labels of the actual capacity-backed optimized routing. -/
noncomputable def capacityRoutingPotentials (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) (J : Circulation) (U : ℕ) :
    Fin J.n → ℤ :=
  let labels := J.shortestRoutingGraph.propagateLabels
    (capacitySolvedRouting solver entry T hproc J U) (Fin.last J.n)
  fun v => labels.1.labels v.castSucc

/-- The named labels equal the exact measured dual-extraction value with
the capacity model as its inner procedure. -/
theorem extractDualMeasured_value_eq_capacityRoutingPotentials (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (flow : Fin J.m → ℤ) (U : ℕ) :
    (J.extractDualMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) flow).value=
      capacityRoutingPotentials solver entry T hproc (J.residual flow) U := rfl

end MinCostFlow.Scaling.Machine
