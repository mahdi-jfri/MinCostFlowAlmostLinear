module

public import MinCostFlow.IPM.Machine.ReportedEdges
import WordRAM.Tactic

/-!
# Starting the reported-list counter loop

The entry copies its incoming allocation endpoint into the loop's heap
register and sets its counter to zero. Both assignments preserve memory,
position and all other registers, and cost exactly five operations with
the sequencing instruction included.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual loop initialization has an exact register update and
cost, with no memory or tape change. -/
theorem reportedEdgesInit_runs {w : ℕ} (p : Program) (parent : State) (heap : ℕ)
    (ω : ℕ → Bool) (hheap : parent.regs 8=heap) (hword : heap<2^w) :
    Runs w p ω reportedEdgesInit parent .normal
      {parent with regs:=Function.update (Function.update parent.regs 21 heap) 20 0} 5 := by
  have hzero : 0<2^w := by omega
  let mid : State := {parent with regs:=Function.update parent.regs 21 heap}
  have hfirst : Runs w p ω (.assign 21 (.reg 8)) parent .normal mid 2 := by
    apply runs_assign_iff.mpr
    exact ⟨heap,by eval_expr,rfl,rfl,rfl⟩
  have hsecond : Runs w p ω (.assign 20 (.const 0)) mid .normal
      {parent with regs:=Function.update (Function.update parent.regs 21 heap) 20 0} 2 := by
    apply runs_assign_iff.mpr
    exact ⟨0,by eval_expr,rfl,rfl,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid,2,2,hfirst,hsecond,rfl⟩)

end MinCostFlow.IPM.Machine
