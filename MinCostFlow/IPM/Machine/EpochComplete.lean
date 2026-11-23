module

public import MinCostFlow.IPM.Machine.EpochIterations
public import MinCostFlow.IPM.Machine.ReportedEdgesProgram
import WordRAM.Tactic

/-!
# Machine control for advancing an epoch to its explicit flow

The fixed epoch packet ends with the iteration limit. The caller first
runs the finite lazy epoch. A failure returns its endpoint immediately.
After success it reads every coordinate at that same returned heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Forward all twenty-six arguments of the finite iteration entry. -/
def epochCompleteIterationArgs : List Expr :=
  (List.range 26).map Expr.reg

/-- The full-coordinate pass forwards the numerical and graph packet.
Its heap is the previous call's result. -/
def epochCompleteReadArgs : List Expr :=
  (List.range 8).map Expr.reg ++ [.reg 26] ++ ((List.range 11).map fun j => Expr.reg (9+j))

/-- The last word of either result is the actual success bit. -/
def epochCompleteTail (read : ℕ) : Stmt :=
  .assign 27 (.load (.bin .sub (.reg 26) (.const 1))) ;;
  .cond (.reg 27) (.call 28 read epochCompleteReadArgs ;; .ret (.reg 28)) (.ret (.reg 26))

/-- Complete one lazy epoch, followed by its full coordinate read. -/
def epochCompleteBody (iterations read : ℕ) : Stmt :=
  .call 26 iterations epochCompleteIterationArgs ;; epochCompleteTail read

/-- The epoch caller is deterministic. -/
theorem epochCompleteBody_noRand (iterations read : ℕ) : (epochCompleteBody iterations read).NoRand := by
  simp [epochCompleteBody,epochCompleteTail,Stmt.NoRand]

/-- A failure returns before the full pass with unchanged memory
and a fixed control cost. -/
theorem epochCompleteTail_failure_runs {w : ℕ} (p : Program) (read : ℕ) (parent : State)
    (ω : ℕ → Bool) (heap : ℕ) (hword : heap<2^w) (hOne : 1<2^w)
    (hheap : parent.regs 26=heap) (hbit : parent.mem (heap-1)=0) :
    Runs w p ω (epochCompleteTail read) parent (.returned heap)
      {parent with regs := Function.update parent.regs 27 0} 10 := by
  let flagged : State := {parent with regs := Function.update parent.regs 27 0}
  have hslot : heap-1<2^w := (Nat.sub_le _ _).trans_lt hword
  have hread : Runs w p ω (.assign 27 (.load (.bin .sub (.reg 26) (.const 1)))) parent .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨0,by eval_expr,rfl,rfl,rfl⟩
  have hout : Runs w p ω (.ret (.reg 26)) flagged (.returned heap) flagged 2 :=
    runs_ret_iff.mpr ⟨heap,by dsimp only [flagged]; eval_expr,rfl,rfl,rfl⟩
  have hbranch : Runs w p ω (.cond (.reg 27) (.call 28 read epochCompleteReadArgs ;; .ret (.reg 28))
      (.ret (.reg 26))) flagged (.returned heap) flagged 4 := by
    apply runs_cond_iff.mpr
    exact ⟨0,2,by dsimp only [flagged]; eval_expr,by simpa using hout,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨flagged,5,4,hread,hbranch,rfl⟩)

/-- Success calls the actual full pass with the returned heap.
Its operation cost is the pass's cost plus caller overhead. -/
theorem epochCompleteTail_success_runs {w read heap v cost : ℕ} {p : Program}
    (parent : State) (ω : ℕ → Bool) {body : Stmt} {args : List ℕ} {st : State}
    (hproc : p.procs[read]?=some body)
    (hword : heap<2^w) (hOne : 1<2^w)
    (hheap : parent.regs 26=heap) (hbit : parent.mem (heap-1)=1)
    (hargs : evalArgs w parent epochCompleteReadArgs=some args)
    (hrun : Runs w p ω body (startState args parent.mem parent.pos) (.returned v) st cost) :
    Runs w p ω (epochCompleteTail read) parent (.returned v)
      {st with regs := Function.update (Function.update parent.regs 27 1) 28 v}
      (cost+(argsSize epochCompleteReadArgs+12)) := by
  let flagged : State := {parent with regs := Function.update parent.regs 27 1}
  let final : State := {st with regs := Function.update flagged.regs 28 v}
  have hslot : heap-1<2^w := (Nat.sub_le _ _).trans_lt hword
  have hread : Runs w p ω (.assign 27 (.load (.bin .sub (.reg 26) (.const 1)))) parent .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨1,by eval_expr,rfl,rfl,rfl⟩
  have hargs' : evalArgs w flagged epochCompleteReadArgs=some args := by
    simpa [epochCompleteReadArgs,flagged,evalArgs,Expr.eval,List.range_succ] using hargs
  have hcall : Runs w p ω (.call 28 read epochCompleteReadArgs) flagged .normal final
      (cost+argsSize epochCompleteReadArgs+1) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,st,cost,hargs',hproc,hrun,rfl,?_,by omega⟩
    cases st
    rfl
  have hret : Runs w p ω (.ret (.reg 28)) final (.returned v) final 2 :=
    runs_ret_iff.mpr ⟨v,by dsimp only [final]; eval_expr,rfl,rfl,rfl⟩
  have hbranch : Runs w p ω (.cond (.reg 27) (.call 28 read epochCompleteReadArgs ;; .ret (.reg 28))
      (.ret (.reg 26))) flagged (.returned v) final (cost+(argsSize epochCompleteReadArgs+6)) := by
    apply runs_cond_iff.mpr
    refine ⟨1,cost+argsSize epochCompleteReadArgs+4,by dsimp only [flagged]; eval_expr,?_,by simp; omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨final,_,2,hcall,hret,by omega⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨flagged,5,_,hread,hbranch,by omega⟩)

end MinCostFlow.IPM.Machine
