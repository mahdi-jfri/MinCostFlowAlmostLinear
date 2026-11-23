module

public import MinCostFlow.IPM.Machine.TargetEpoch
public import MinCostFlow.IPM.Machine.TargetEpochBudget

/-!
# The bounded target-test loop

Each stage begins with a residual check and can stop before Init.
Only a continuing stage updates the flow pointer and allocation
endpoint. The limit allows one final residual check after the last
possible progress epoch.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- After a continuing stage, replace the explicit flow and heap.
The finite counter is advanced by the enclosing loop. -/
def targetTestStep (epoch : ℕ) : Stmt :=
  .call 24 epoch ((List.range 23).map Expr.reg) ;;
  .assign 25 (.load (.bin .sub (.reg 24) (.const 1))) ;;
  .cond (.bin .eq (.reg 25) (.const 2))
    (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;;
      .assign 21 (.reg 24))
    (.ret (.reg 24))

/-- Take the twenty-three stage arguments and the stage limit. The test
returns its first noncontinuing stage record, or a fresh failure
record at exhaustion. A promised target cannot exhaust this limit. -/
def targetTestBody (epoch record : ℕ) : Stmt :=
  .assign 26 (.const 0) ;;
  forUp 26 (.reg 23) (targetTestStep epoch) ;;
  targetEpochReturn record (.reg 20) (.const 0) (.reg 21)

/-- The target loop contains no random instruction. -/
theorem targetTestBody_noRand (epoch record : ℕ) : (targetTestBody epoch record).NoRand := by
  simp [targetTestBody,targetTestStep,targetEpochReturn,forUp,Stmt.NoRand]

/-- One counted stage call forwarding `V` in `.reg 27`. -/
def targetTestStepWithV (epoch : ℕ) : Stmt :=
  .call 24 epoch ((List.range 23).map Expr.reg ++ [.reg 27]) ;;
  .assign 25 (.load (.bin .sub (.reg 24) (.const 1))) ;;
  .cond (.bin .eq (.reg 25) (.const 2))
    (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;;
     .assign 21 (.reg 24))
    (.ret (.reg 24))

/-- Counted outer loop for one target, saving `V` from `.reg 24` into `.reg 27`. -/
def targetTestBodyWithV (epoch record : ℕ) : Stmt :=
  .assign 27 (.reg 24) ;;
  .assign 26 (.const 0) ;;
  forUp 26 (.reg 23) (targetTestStepWithV epoch) ;;
  targetEpochReturn record (.reg 20) (.const 0) (.reg 21)

/-- The `V`-passing target-test loop executes no random operations. -/
theorem targetTestBodyWithV_noRand (epoch record : ℕ) :
    (targetTestBodyWithV epoch record).NoRand := by
  simp [targetTestBodyWithV,targetTestStepWithV,forUp,targetEpochReturn,Stmt.NoRand]

end MinCostFlow.IPM.Machine
