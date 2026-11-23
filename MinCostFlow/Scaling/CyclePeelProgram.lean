module

public import MinCostFlow.Scaling.CyclePeelCode
import MinCostFlow.Scaling.CyclePeelEmptyProgram
import MinCostFlow.Scaling.CyclePeelNonemptyProgram

/-!
# The complete peel-mode cycle traversal step

Split on the stack. An empty stack completes the scan. A nonempty stack
adds and records its first edge, clears the path flag when needed, and
finishes or continues the peeled part. Both branches are the exact model
step and preserve the common traversal frames and word bounds.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every represented peel-mode state is processed exactly as the model
step, using at most four fresh cells and cost 1000. -/
theorem cyclePeel_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cyclePeelModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (target : Fin J.n) : MeetsContract w p b (cyclePeelContract w J s B C target) := by
  cases hstack : s.stack with
  | nil => exact cyclePeel_empty_meetsContract hp J s B C target hstack
  | cons e rest => exact cyclePeel_nonempty_meetsContract hp J s B C target e rest hstack

end MinCostFlow.Scaling.Machine
