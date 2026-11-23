module

public import MinCostFlow.IPM.Machine.EpochComplete
public import MinCostFlow.IPM.Machine.EpochLayout
import WordRAM.Tactic

/-!
# The register interface of the complete epoch caller

The lazy loop receives the same packet as its caller. Its returned
heap is the only new argument to materialization. Both calls are
accounted for in the caller's Word RAM runs.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The fixed twenty-six arguments are forwarded as initialized. -/
theorem epochComplete_iteration_args {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (heap finish : ℕ) (mem : ℕ → ℕ) (pos : ℕ) :
    evalArgs w (startState (L.packet F I heap++[finish]) mem pos) epochCompleteIterationArgs=
      some (L.packet F I heap++[finish]) := by rfl

/-- The epoch call's return replaces precisely the heap word in the
packet forwarded to the full-coordinate pass. -/
theorem epochComplete_read_args {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (heap finish v : ℕ)
    (mem final : ℕ → ℕ) (pos nextPos : ℕ) :
    evalArgs w ⟨final,Function.update (startState (L.packet F I heap++[finish]) mem pos).regs 26 v,nextPos⟩
      epochCompleteReadArgs=some ((L.packet F I v).take 20) := by
  simp [epochCompleteReadArgs,EpochLayout.packet,evalArgs,Expr.eval,startState,List.range_succ]

/-- The already verified finite epoch runs as the actual caller's
first instruction. It leaves the caller packet intact and stores the
returned heap in register twenty-six. -/
theorem epochComplete_call_runs {w iterations v cost : ℕ} {p : Program}
    (F : MinRatioFormat w) (I : Instance) (L : EpochLayout) (heap finish : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    {st : State} {body : Stmt} (hbody : p.procs[iterations]?=some body)
    (hrun : Runs w p ω body (startState (L.packet F I heap++[finish]) mem pos) (.returned v) st cost) :
    let start := startState (L.packet F I heap++[finish]) mem pos
    Runs w p ω (.call 26 iterations epochCompleteIterationArgs) start .normal
      ⟨st.mem,Function.update start.regs 26 v,st.pos⟩ (cost+27) := by
  let start := startState (L.packet F I heap++[finish]) mem pos
  apply runs_call_iff.mpr
  refine ⟨L.packet F I heap++[finish],body,.returned v,st,cost,
    epochComplete_iteration_args F I L heap finish mem pos,hbody,hrun,rfl,?_,?_⟩
  · cases st
    rfl
  · change cost+27=26+cost+1
    omega

end MinCostFlow.IPM.Machine
