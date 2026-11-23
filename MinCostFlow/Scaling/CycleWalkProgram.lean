module

public import MinCostFlow.Scaling.CycleWalkCode
import MinCostFlow.Scaling.CycleWalkEmptyProgram
import MinCostFlow.Scaling.CycleWalkNonemptyProgram

/-!
# The complete walk-mode cycle traversal step

Split on the current vertex's outgoing list. An exhausted walk clears its
path flag and returns to choosing. A nonempty walk pops one unused edge,
pushes it onto the stack, and starts peeling or continues to a new vertex
according to the stored path flag. Each branch is the model's exact step.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every stored walk-mode state is processed exactly as `CycleState.step`,
with the common constant cost, fresh-space, frame, and word bounds. -/
theorem cycleWalk_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleWalkModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (v : Fin J.n) : MeetsContract w p b (cycleWalkContract w J s B C v) := by
  cases hout : s.outgoing v with
  | nil => exact cycleWalk_empty_meetsContract hp J s B C v hout
  | cons e rest => exact cycleWalk_nonempty_meetsContract hp J s B C v e rest hout

end MinCostFlow.Scaling.Machine
