module

public import MinCostFlow.IPM.Machine.BudgetedIteration
import WordRAM.Tactic

/-!
# Reading the actual Detect report for the budget guard

The complete Detect/refresh result gives a stable report pointer even
when a coordinate guard rejects. Read that pointer, its actual header
count and the refresh status. These fifteen caller operations preserve
all memory and concrete DS credit before either budget branch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual three reads decode the report and status, with exact
cost fifteen and unchanged memory and tape position. -/
theorem budgetedIterationReadReport_runs {w : ℕ} (p : Program) (parent : State)
    (ω : ℕ → Bool) (endpoint report count bit : ℕ)
    (hheap : parent.regs 26=endpoint) (hp : parent.mem (endpoint-2)=report)
    (hc : parent.mem report=count) (hb : parent.mem (endpoint-1)=bit)
    (hword : endpoint<2^w) (hTwo : 2<2^w) :
    Runs w p ω budgetedIterationReadReport parent .normal
      {parent with regs:=Function.update (Function.update (Function.update parent.regs 27 report) 28 count) 29 bit} 15 := by
  have hOne : 1<2^w := by omega
  have hs0 : endpoint-2<2^w := (Nat.sub_le _ _).trans_lt hword
  have hs1 : endpoint-1<2^w := (Nat.sub_le _ _).trans_lt hword
  let pointed : State := {parent with regs:=Function.update parent.regs 27 report}
  let counted : State := {parent with regs:=Function.update (Function.update parent.regs 27 report) 28 count}
  let flagged : State := {parent with regs:=Function.update (Function.update (Function.update parent.regs 27 report) 28 count) 29 bit}
  have hptr : Runs w p ω (.assign 27 (.load (.bin .sub (.reg 26) (.const 2)))) parent .normal pointed 5 := by
    apply runs_assign_iff.mpr
    exact ⟨report,by eval_expr,rfl,rfl,rfl⟩
  have hcount : Runs w p ω (.assign 28 (.load (.reg 27))) pointed .normal counted 3 := by
    apply runs_assign_iff.mpr
    exact ⟨count,by dsimp only [pointed]; eval_expr,rfl,rfl,rfl⟩
  have hbit : Runs w p ω (.assign 29 (.load (.bin .sub (.reg 26) (.const 1)))) counted .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨bit,by dsimp only [counted]; eval_expr,rfl,rfl,rfl⟩
  unfold budgetedIterationReadReport
  apply runs_seq_iff.mpr
  refine Or.inr ⟨pointed,5,3+5+1,hptr,?_,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨counted,3,5,hcount,hbit,rfl⟩)

end MinCostFlow.IPM.Machine
