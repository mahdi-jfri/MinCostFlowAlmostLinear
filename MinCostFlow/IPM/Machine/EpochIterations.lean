module

public import MinCostFlow.IPM.Machine.DetectChecked
public import MinCostFlow.IPM.Machine.FlagRecord
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# The finite checked iteration loop inside an epoch

The single-flow adaptation of Algorithm 7 of Chen et al.,
arXiv:2203.00671v2 (page 69), refreshes fully after at most m Updates.
Within that epoch, execute the complete Detect/check/Update entry and
advance only its allocation endpoint. A zero status returns immediately,
before another DS operation. Normal completion appends a fresh success
record, including when the supplied iteration count is zero.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The loop forwards the fixed twenty-five-word iteration packet.
Only its heap argument, register 8, changes between calls. -/
def epochIterationsArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
    .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19,
    .reg 20,.reg 21,.reg 22,.reg 23,.reg 24]

/-- Inspect the actual returned status. Success advances the heap;
failure exits the entire epoch loop with that same failure result. -/
def epochIterationsTail : Stmt :=
  .assign 28 (.load (.bin .sub (.reg 27) (.const 1))) ;;
  .cond (.reg 28) (.assign 8 (.reg 27)) (.ret (.reg 27))

/-- One counted call to the complete iteration and its failure guard. -/
def epochIterationsStep (iteration : ℕ) : Stmt :=
  .call 27 iteration epochIterationsArgs ;; epochIterationsTail

/-- Arguments are the complete twenty-five-word iteration packet,
followed by the iteration count. Counter 26 and result registers 27--29
are caller-local. A completed loop returns a fresh last-word success. -/
def epochIterationsBody (iteration flag : ℕ) : Stmt :=
  .assign 26 (.const 0) ;;
  forUp 26 (.reg 25) (epochIterationsStep iteration) ;;
  .call 29 flag [.const 1,.reg 8] ;;
  .ret (.reg 29)

/-- All instructions of the finite epoch loop are deterministic. -/
theorem epochIterationsBody_noRand (iteration flag : ℕ) :
    (epochIterationsBody iteration flag).NoRand := by
  simp [epochIterationsBody,epochIterationsStep,epochIterationsTail,epochIterationsArgs,forUp,Stmt.NoRand]

/-- The actual zero-counter initialization costs two operations and
preserves memory, tape position and every other caller register. -/
theorem epochIterationsInit_runs {w : ℕ} (p : Program) (parent : State) (ω : ℕ → Bool) :
    Runs w p ω (.assign 26 (.const 0)) parent .normal
      {parent with regs:=Function.update parent.regs 26 0} 2 := by
  have hzero : 0<2^w := Nat.two_pow_pos w
  apply runs_assign_iff.mpr
  exact ⟨0,by eval_expr,rfl,rfl,rfl⟩

end MinCostFlow.IPM.Machine
