module

public import MinCostFlow.Scaling.CycleChooseCode
import MinCostFlow.Scaling.CycleChooseEmptyProgram
import MinCostFlow.Scaling.CycleChooseSkipProgram
import MinCostFlow.Scaling.CycleChooseStartProgram

/-!
# The complete choose-mode cycle traversal step

Split on the candidate list and the chosen tail's outgoing list. The
proved machine branches complete the scan, skip an exhausted tail, or
start a new marked walk, respectively. Together they compute exactly the
model's choose step with its common cost, frame, and word bounds.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every choose-mode state is processed exactly as `CycleState.step`,
with at most 1000 steps, unchanged heap, and preserved node/table frames. -/
theorem cycleChoose_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleChooseModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) : MeetsContract w p b (cycleChooseContract w J s B C) := by
  cases hcan : s.candidates with
  | nil => exact cycleChoose_empty_meetsContract hp J s B C hcan
  | cons e rest =>
    by_cases hout : s.outgoing (J.tail e)=[]
    · exact cycleChoose_skip_meetsContract hp J s B C e rest hcan hout
    · exact cycleChoose_start_meetsContract hp J s B C e rest hcan hout

end MinCostFlow.Scaling.Machine
