module

public import MinCostFlow.IPM.Machine.DetectChecked
public import MinCostFlow.IPM.Machine.EpochBudgetRecord
import WordRAM.Tactic

/-!
# Enforcing the report-size budget before the next Update

A target below the optimum has no hidden-stability guarantee. Its epoch
therefore caps cumulative reported names, as in the failure-aware model's
Query-budget guard. Read the remaining budget from the incoming fresh
record. After Detect/refresh, compare its actual report count before
Update. Every branch writes a new three-word budget/status record.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Read the remaining report budget from the incoming three-word record. -/
def budgetedIterationReadBudget : Stmt :=
  .assign 25 (.load (.bin .sub (.reg 8) (.const 3)))

/-- Decode the actual Detect report pointer, count and refresh status. -/
def budgetedIterationReadReport : Stmt :=
  .assign 27 (.load (.bin .sub (.reg 26) (.const 2))) ;;
  .assign 28 (.load (.reg 27)) ;;
  .assign 29 (.load (.bin .sub (.reg 26) (.const 1)))

/-- A failed refresh or over-budget report returns without Update,
retaining its old remaining budget and recording this attempted count. -/
def budgetedIterationReject (record : ℕ) : Stmt :=
  .call 33 record [.reg 25,.reg 28,.const 0,.reg 26] ;; .ret (.reg 33)

/-- The checked call uses the refreshed coefficients and actual report. -/
def budgetedIterationCheckedArgs : List Expr :=
  [.reg 0,.reg 20,.reg 27,.reg 18,.reg 17,.reg 21,.reg 7,.reg 26,.reg 22,.reg 23,.reg 24]

/-- After a fitting report count, execute the actual checked driver,
subtract the count and append its success or failure status. -/
def budgetedIterationAccepted (checked record : ℕ) : Stmt :=
  .call 30 checked budgetedIterationCheckedArgs ;;
  .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
  .assign 32 (.bin .sub (.reg 25) (.reg 28)) ;;
  .call 33 record [.reg 32,.reg 28,.reg 31,.reg 30] ;;
  .ret (.reg 33)

/-- Same twenty-five-word packet as the complete iteration. The incoming
heap minus three stores its remaining budget. The returned last three
words are `[remaining,reportCount,status]` on every branch. -/
def budgetedIterationBody (detect checked record : ℕ) : Stmt :=
  budgetedIterationReadBudget ;;
  .call 26 detect [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
    .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19] ;;
  budgetedIterationReadReport ;;
  .cond (.reg 29)
    (.cond (.bin .lt (.reg 25) (.reg 28))
      (budgetedIterationReject record) (budgetedIterationAccepted checked record))
    (budgetedIterationReject record)

/-- Budget guards, status reads and all caller instructions are deterministic. -/
theorem budgetedIterationBody_noRand (detect checked record : ℕ) :
    (budgetedIterationBody detect checked record).NoRand := by
  simp [budgetedIterationBody,budgetedIterationReadBudget,budgetedIterationReadReport,
    budgetedIterationReject,budgetedIterationAccepted,budgetedIterationCheckedArgs,Stmt.NoRand]

/-- Reading an actual incoming budget costs five operations and changes
only its caller-local register. No memory or tape position changes. -/
theorem budgetedIterationReadBudget_runs {w : ℕ} (p : Program) (parent : State)
    (ω : ℕ → Bool) (heap remaining : ℕ) (hheap : parent.regs 8=heap)
    (hread : parent.mem (heap-3)=remaining) (hword : heap<2^w) (hThree : 3<2^w) :
    Runs w p ω budgetedIterationReadBudget parent .normal
      {parent with regs:=Function.update parent.regs 25 remaining} 5 := by
  have hslot : heap-3<2^w := (Nat.sub_le _ _).trans_lt hword
  unfold budgetedIterationReadBudget
  exact runs_assign_iff.mpr ⟨remaining,by eval_expr,rfl,rfl,rfl⟩

end MinCostFlow.IPM.Machine
