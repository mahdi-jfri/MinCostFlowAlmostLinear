module

public import MinCostFlow.IPM.Machine.TargetEpochInitRun
public import MinCostFlow.IPM.Machine.TargetEpochAfterInit
import WordRAM.Tactic

/-!
# The residual branch that runs a fresh epoch

Once the residual test returns a workspace endpoint, the driver
executes startup and follows its actual flag. The arithmetic
and branch overhead is independent of the epoch length.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Compose the actual startup and its continuation on the
nonterminal residual branch. -/
theorem targetEpochBranch_continue_runs {w startup complete record heap initCost tailCost out : ℕ}
    {p : Program} {ω : ℕ → Bool} {before after final : State}
    (hheap : before.regs 30=heap) (hThree : 3<2^w) (hbig : 3≤heap)
    (hInit : Runs w p ω (targetEpochInit startup) before .normal after initCost)
    (hTail : Runs w p ω (targetEpochAfterInit complete record) after (.returned out) final tailCost) :
    Runs w p ω (targetEpochBranch startup complete record) before (.returned out) final
      (initCost+tailCost+5) := by
  apply runs_cond_iff.mpr
  have htest : (Expr.bin .lt (.reg 30) (.const 3)).eval w before=some 0 :=
    Expr.eval_lt_false (x:=heap) (y:=3) (by simp [Expr.eval,hheap]) (by eval_expr)
      hbig (by omega)
  exact ⟨0,initCost+tailCost+1,htest,
    by simpa using (runs_seq_iff.mpr (Or.inr ⟨after,initCost,tailCost,hInit,hTail,rfl⟩)),
    by change initCost+tailCost+5=3+(initCost+tailCost+1)+1; omega⟩

/-- `V`-passing variant of `targetEpochBranch_continue_runs`. -/
theorem targetEpochBranchWithV_continue_runs {w startup complete record heap initCost tailCost out : ℕ}
    {p : Program} {ω : ℕ → Bool} {before after final : State}
    (hheap : before.regs 30=heap) (hThree : 3<2^w) (hbig : 3≤heap)
    (hInit : Runs w p ω (targetEpochInitWithV startup) before .normal after initCost)
    (hTail : Runs w p ω (targetEpochAfterInit complete record) after (.returned out) final tailCost) :
    Runs w p ω (targetEpochBranchWithV startup complete record) before (.returned out) final
      (initCost+tailCost+5) := by
  apply runs_cond_iff.mpr
  have htest : (Expr.bin .lt (.reg 30) (.const 3)).eval w before=some 0 :=
    Expr.eval_lt_false (x:=heap) (y:=3) (by simp [Expr.eval,hheap]) (by eval_expr)
      hbig (by omega)
  exact ⟨0,initCost+tailCost+1,htest,
    by simpa using (runs_seq_iff.mpr (Or.inr ⟨after,initCost,tailCost,hInit,hTail,rfl⟩)),
    by change initCost+tailCost+5=3+(initCost+tailCost+1)+1; omega⟩

end MinCostFlow.IPM.Machine
