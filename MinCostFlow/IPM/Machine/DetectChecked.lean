module

public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Stopping after Detect/refresh or invoking the checked Update driver

The iteration starts with the verified combined Detect/refresh call.
Read its last-word bit. Failure returns that result immediately.
Success reads its stable report pointer and calls the complete checked
Update driver. The driver's final bit then reports either successful
Update or the first rejected coefficient/Update answer.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The checked-driver packet uses the decoded report, fixed source
graph and normalization, and the current Detect/refresh heap. -/
def detectCheckedArgs : List Expr :=
  [.reg 0,.reg 20,.reg 28,.reg 18,.reg 17,.reg 21,.reg 7,.reg 25,.reg 22,.reg 23,.reg 24]

/-- Register 25 holds the combined Detect/refresh result. -/
def detectCheckedTail (checked : ℕ) : Stmt :=
  .assign 26 (.load (.bin .sub (.reg 25) (.const 1))) ;;
  .cond (.reg 26)
    (.assign 28 (.load (.bin .sub (.reg 25) (.const 2))) ;;
      .call 27 checked detectCheckedArgs ;;
      .ret (.reg 27))
    (.ret (.reg 25))

/-- The first twenty arguments are the full Detect/refresh packet.
Append `[sourceGraph,normalization,negativeMaximum,maximum,minimum]`.
The returned heap always has the iteration status in its last word. -/
def detectCheckedBody (detect checked : ℕ) : Stmt :=
  .call 25 detect [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
    .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19] ;;
  detectCheckedTail checked

/-- The complete iteration's own instructions contain no randomness. -/
theorem detectCheckedBody_noRand (detect checked : ℕ) : (detectCheckedBody detect checked).NoRand := by
  simp [detectCheckedBody,detectCheckedTail,detectCheckedArgs,Stmt.NoRand]

/-- An actual rejected Detect/refresh bit returns immediately with no
checked-driver call. All memory and the tape position are unchanged. -/
theorem detectCheckedTail_failure_runs {w checked v : ℕ} {p : Program}
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w) (hv : v<2^w)
    (hheap : parent.regs 25=v) (hbit : parent.mem (v-1)=0) :
    ∃ o st cost,Runs w p ω (detectCheckedTail checked) parent o st cost ∧
      (o=.returned v ∧ st.mem=parent.mem ∧ st.pos=parent.pos) ∧ cost≤10 := by
  have hslot : v-1<2^w := by omega
  apply runs_start_le
  unfold detectCheckedTail
  wram_step
  refine runs_cond_le (v:=0) (by eval_expr) ?_ ?_
  · intro hn
    exact False.elim (hn rfl)
  · intro _
    refine runs_ret_le (v:=v) (by eval_expr) ⟨rfl,rfl,rfl⟩ ?_
    simp only [Expr.size_reg,Expr.size_load,Expr.size_bin,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
