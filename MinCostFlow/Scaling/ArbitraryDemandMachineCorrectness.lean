module

public import MinCostFlow.Scaling.ArbitraryDemandContract
import MinCostFlow.Scaling.GeneralScalingCorrectness

/-!
# Correctness of the procedure's exact model answer

The deterministic solver contract supplies precisely the bounded
circulation optimality premise of Lemma C.1. Instantiate the proved
arbitrary-demand model theorem with the canonical output of that
procedure, then serialize its result using the fixed statement format.
No additional solver property is assumed.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The exact answer written by the arbitrary-demand procedure is correct
against all feasible real flows, or certifies that no such flow exists. -/
theorem arbitraryDemand_answer_correct (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hc : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    I.IsCorrectAnswer (scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
      (canonicalSolver solver entry T hproc) I hv C U).value) := by
  have h := FlowReduction.lemma_C_1 (canonicalSolver solver entry T hproc)
    (fun J _ _ => canonicalSolver_optimal solver entry T hproc J) I hv C U hc hl hu
  exact scalingAnswerWords_correct I _ h.1 h.2

end MinCostFlow.Scaling.Machine
