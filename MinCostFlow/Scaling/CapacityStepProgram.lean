module

public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.CapacityStepStoppedProgram
import MinCostFlow.Scaling.CapacityStepActiveProgram

/-!
# The complete executable capacity-scaling step

The stored early-stop flag selects either the constant return or the
proved active residual optimization. Both branches produce exactly the
model's next state with the same flow/header layout and memory frame.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every represented capacity state executes exactly one model iteration
with its explicit branch cost and complete temporary-space reserve. -/
theorem capacityStep_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityStepModule solver entry b))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityStepContract w solver entry T hproc J s C U) := by
  cases hstop : s.stopped with
  | false => exact capacityStep_active_meetsContract hproc hdet hp J s C U hc hstop
  | true => exact capacityStep_stopped_meetsContract hproc hp J s C U hstop

end MinCostFlow.Scaling.Machine
