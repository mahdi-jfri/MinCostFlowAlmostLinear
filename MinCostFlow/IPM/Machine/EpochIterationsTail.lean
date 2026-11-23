module

public import MinCostFlow.IPM.Machine.EpochIterations
import WordRAM.Tactic

/-!
# Reading an iteration's status inside the epoch loop

The last-word bit is read before any further min-ratio operation.
Success replaces the caller's heap register. Failure returns that same
result immediately. Both actual branches cost ten operations and leave
memory and tape position unchanged, preserving the full DS credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful actual iteration advances only the heap and status
registers, with unchanged memory and exact ten-operation cost. -/
theorem epochIterationsTail_success_runs {w : ℕ} (p : Program) (parent : State)
    (ω : ℕ → Bool) (v : ℕ) (hword : v<2^w) (hOne : 1<2^w)
    (hheap : parent.regs 27=v) (hbit : parent.mem (v-1)=1) :
    Runs w p ω epochIterationsTail parent .normal
      {parent with regs:=Function.update (Function.update parent.regs 28 1) 8 v} 10 := by
  have hslot : v-1<2^w := (Nat.sub_le _ _).trans_lt hword
  let flagged : State := {parent with regs:=Function.update parent.regs 28 1}
  let advanced : State := {parent with regs:=Function.update (Function.update parent.regs 28 1) 8 v}
  have hread : Runs w p ω (.assign 28 (.load (.bin .sub (.reg 27) (.const 1)))) parent .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨1,by eval_expr,rfl,rfl,rfl⟩
  have hsave : Runs w p ω (.assign 8 (.reg 27)) flagged .normal advanced 2 := by
    apply runs_assign_iff.mpr
    exact ⟨v,by dsimp only [flagged]; eval_expr,rfl,rfl,rfl⟩
  have hcond : Runs w p ω (.cond (.reg 28) (.assign 8 (.reg 27)) (.ret (.reg 27)))
      flagged .normal advanced 4 := by
    apply runs_cond_iff.mpr
    exact ⟨1,2,by dsimp only [flagged]; eval_expr,by simpa using hsave,rfl⟩
  unfold epochIterationsTail
  exact runs_seq_iff.mpr (Or.inr ⟨flagged,5,4,hread,hcond,rfl⟩)

/-- A rejected actual iteration exits immediately with its same result,
unchanged memory and exact ten-operation cost. -/
theorem epochIterationsTail_failure_runs {w : ℕ} (p : Program) (parent : State)
    (ω : ℕ → Bool) (v : ℕ) (hword : v<2^w) (hOne : 1<2^w)
    (hheap : parent.regs 27=v) (hbit : parent.mem (v-1)=0) :
    Runs w p ω epochIterationsTail parent (.returned v)
      {parent with regs:=Function.update parent.regs 28 0} 10 := by
  have hslot : v-1<2^w := (Nat.sub_le _ _).trans_lt hword
  let flagged : State := {parent with regs:=Function.update parent.regs 28 0}
  have hread : Runs w p ω (.assign 28 (.load (.bin .sub (.reg 27) (.const 1)))) parent .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨0,by eval_expr,rfl,rfl,rfl⟩
  have hret : Runs w p ω (.ret (.reg 27)) flagged (.returned v) flagged 2 := by
    apply runs_ret_iff.mpr
    exact ⟨v,by dsimp only [flagged]; eval_expr,rfl,rfl,rfl⟩
  have hcond : Runs w p ω (.cond (.reg 28) (.assign 8 (.reg 27)) (.ret (.reg 27)))
      flagged (.returned v) flagged 4 := by
    apply runs_cond_iff.mpr
    exact ⟨0,2,by dsimp only [flagged]; eval_expr,by simpa using hret,rfl⟩
  unfold epochIterationsTail
  exact runs_seq_iff.mpr (Or.inr ⟨flagged,5,4,hread,hcond,rfl⟩)

end MinCostFlow.IPM.Machine
