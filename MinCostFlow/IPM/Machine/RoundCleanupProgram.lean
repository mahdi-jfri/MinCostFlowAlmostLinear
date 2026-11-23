module

public import MinCostFlow.IPM.Machine.RoundFlushCut
public import MinCostFlow.IPM.Machine.RoundForestPathMin
public import MinCostFlow.IPM.Machine.RoundCleanupModel
import WordRAM.Tactic

/-!
# Recursive cleanup of integral edges on a forest path

After each cut, only the two remaining path segments can contain
more zero-availability edges. The two recursive calls use the saved
cut endpoints and pass the returned heap between them.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Save the split endpoints and reduce fuel before the cut call. -/
def roundCleanupSave : Stmt :=
  .assign 9 (.load (.bin .add (.reg 5) (.const 2))) ;;
  .assign 10 (.load (.bin .add (.reg 5) (.const 3))) ;;
  .assign 11 (.bin .sub (.reg 6) (.const 1))

/-- Pass the padded hit record to the flush-and-cut helper. -/
def roundCleanupCutArgs : List Expr := [.reg 0,.reg 5,.reg 3,.reg 4,.reg 7]

/-- On [forest,from,to,flow,L,heap,fuel], clean up a path. The leaf
returns the padded heap. The cut branch saves the endpoints before
calling Cut, since that call may change the selected record's storage. -/
def roundCleanupBody (entry pathMin pathZero flushCut : ℕ) : Stmt :=
  .cond (.reg 6)
    (.call 7 pathMin [.reg 0,.reg 1,.reg 2,.reg 4,.reg 5] ;;
     .call 8 pathZero [.reg 5,.reg 4] ;;
     .cond (.reg 8)
       (roundCleanupSave ;;
        .call 7 flushCut roundCleanupCutArgs ;;
        .call 7 entry [.reg 0,.reg 1,.reg 9,.reg 3,.reg 4,.reg 7,.reg 11] ;;
        .call 7 entry [.reg 0,.reg 10,.reg 2,.reg 3,.reg 4,.reg 7,.reg 11] ;;
        .ret (.reg 7))
       (.ret (.reg 7)))
    (.ret (.reg 5))

/-- No instruction in the path cleanup body draws random bits. -/
theorem roundCleanup_noRand (entry pathMin pathZero flushCut : ℕ) :
    (roundCleanupBody entry pathMin pathZero flushCut).NoRand := by
  simp [roundCleanupBody,roundCleanupSave,Stmt.NoRand]

/-- Lift a verified returning body to a call without losing its
state, exact cost, or the caller's register frame. -/
theorem round_returning_call {w i dst res c : ℕ} {p : Program} {ω : ℕ → Bool}
    {body : Stmt} {start final : State} {exprs : List Expr} {args : List ℕ}
    (hbody : p.procs[i]?=some body) (hargs : evalArgs w start exprs=some args)
    (hrun : Runs w p ω body (startState args start.mem start.pos) (.returned res) final c) :
    Runs w p ω (.call dst i exprs) start .normal
      ⟨final.mem,Function.update start.regs dst res,final.pos⟩ (argsSize exprs+c+1) :=
  runs_call_iff.mpr ⟨args,body,.returned res,final,c,hargs,hbody,hrun,rfl,by cases final; rfl,rfl⟩

end MinCostFlow.IPM.Machine
