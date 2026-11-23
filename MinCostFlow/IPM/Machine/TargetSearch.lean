module

public import MinCostFlow.IPM.Machine.TargetTest
public import MinCostFlow.IPM.Machine.TargetGuess

/-!
# Word RAM bisection for the integral optimum

The inclusive cost interval is represented by offsets in [0,2B].
Each comparison uses the original half-slack flow and a fresh
workspace. After the interval collapses, one final test at its
sole target returns the flow.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Run one encoded target. The input is the test packet with an
offset in place of the target pointer and the radius appended. -/
def targetOffsetEncode (guess : ℕ) : Stmt :=
  .call 25 guess [.reg 6,.reg 24,.reg 15,.reg 16,.reg 21] ;;
  .assign 6 (.bin .sub (.reg 25) (.reg 15)) ;;
  .assign 21 (.reg 25)

/-- Run the target test on the newly encoded target. -/
def targetOffsetTestBody (guess test : ℕ) : Stmt :=
  targetOffsetEncode guess ;;
  .call 26 test ((List.range 24).map Expr.reg) ;;
  .ret (.reg 26)

/-- The offset test uses the current search heap and the original
source, with the same numerical constants and stage limit. -/
def targetOffsetPacket {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (offset qp source heap limit radius : ℕ) : List ℕ :=
  targetEpochPacket L F I offset qp source heap++[limit,radius]

/-- The parent forwards its current allocation endpoint and replaces
only the target operand by the requested offset. -/
def targetSearchArgs (offset : ℕ) : List Expr :=
  (List.range 25).map (fun j => if j=6 then .reg offset else .reg j)

/-- Narrow the inclusive interval only when its endpoints differ.
Register 28 is the counted loop counter, 26 and 27 bracket the target.
The saved pointer at 20 always names the original half-slack flow. -/
def targetSearchStep (offsetTest : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 26) (.reg 27))
    (.assign 29 (.bin .add (.reg 26)
      (.bin .div (.bin .sub (.reg 27) (.reg 26)) (.const 2))) ;;
      .call 30 offsetTest (targetSearchArgs 29) ;;
      .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
      .assign 21 (.reg 30) ;;
      .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
    (.assign 26 (.reg 26))

/-- Set the two initial endpoints and start the counted loop at zero. -/
def targetSearchInit : Stmt :=
  .assign 26 (.const 0) ;;
  .assign 27 (.bin .mul (.const 2) (.reg 24)) ;;
  .assign 28 (.const 0)

/-- Rerun the target at the collapsed bracket to obtain its flow. -/
def targetSearchFinish (offsetTest : ℕ) : Stmt :=
  .call 30 offsetTest (targetSearchArgs 26) ;;
  .ret (.reg 30)

/-- Run bisection and return the final successful test's flow record. -/
def targetSearchBody (offsetTest : ℕ) : Stmt :=
  targetSearchInit ;;
  forUp 28 (.reg 25) (targetSearchStep offsetTest) ;;
  targetSearchFinish offsetTest

/-- The search and both caller kernels use no random instruction. -/
theorem targetSearch_noRand (offsetTest : ℕ) : (targetSearchBody offsetTest).NoRand := by
  simp [targetSearchBody,targetSearchInit,targetSearchStep,targetSearchFinish,Stmt.NoRand,forUp]

/-- Loading and testing a target adds no random instruction. -/
theorem targetOffsetTest_noRand (guess test : ℕ) : (targetOffsetTestBody guess test).NoRand := by
  simp [targetOffsetTestBody,targetOffsetEncode,Stmt.NoRand]

/-- `V`-passing offset test packet appending `V` at index 25 (`.reg 25`). -/
def targetOffsetPacketWithV {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (offset qp source heap limit radius V : ℕ) : List ℕ :=
  targetOffsetPacket L F I offset qp source heap limit radius ++ [V]

/-- Save `V` from `.reg 25` into `.reg 27`, encode target, and invoke `targetTestBodyWithV`. -/
def targetOffsetTestBodyWithV (guess test : ℕ) : Stmt :=
  .assign 27 (.reg 25) ;;
  targetOffsetEncode guess ;;
  .call 26 test ((List.range 24).map Expr.reg ++ [.reg 27]) ;;
  .ret (.reg 26)

/-- Forward bisection args together with `V` stored in `.reg 32`. -/
def targetSearchArgsWithV (offset : ℕ) : List Expr :=
  targetSearchArgs offset ++ [.reg 32]

/-- `V`-passing variant of `targetSearchStep`. -/
def targetSearchStepWithV (offsetTest : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 26) (.reg 27))
    (.assign 29 (.bin .add (.reg 26)
      (.bin .div (.bin .sub (.reg 27) (.reg 26)) (.const 2))) ;;
      .call 30 offsetTest (targetSearchArgsWithV 29) ;;
      .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
      .assign 21 (.reg 30) ;;
      .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
    (.assign 26 (.reg 26))

/-- `V`-passing variant of `targetSearchFinish`. -/
def targetSearchFinishWithV (offsetTest : ℕ) : Stmt :=
  .call 30 offsetTest (targetSearchArgsWithV 26) ;;
  .ret (.reg 30)

/-- `V`-passing variant of `targetSearchBody`: saves `V` from `.reg 26` into `.reg 32`. -/
def targetSearchBodyWithV (offsetTest : ℕ) : Stmt :=
  .assign 32 (.reg 26) ;;
  targetSearchInit ;;
  forUp 28 (.reg 25) (targetSearchStepWithV offsetTest) ;;
  targetSearchFinishWithV offsetTest

/-- The `V`-passing search and offset-test kernels use no random instruction. -/
theorem targetSearchWithV_noRand (offsetTest : ℕ) : (targetSearchBodyWithV offsetTest).NoRand := by
  simp [targetSearchBodyWithV,targetSearchInit,targetSearchStepWithV,targetSearchFinishWithV,Stmt.NoRand,forUp]

/-- The `V`-passing offset test adds no random instruction. -/
theorem targetOffsetTestWithV_noRand (guess test : ℕ) : (targetOffsetTestBodyWithV guess test).NoRand := by
  simp [targetOffsetTestBodyWithV,targetOffsetEncode,Stmt.NoRand]

end MinCostFlow.IPM.Machine
