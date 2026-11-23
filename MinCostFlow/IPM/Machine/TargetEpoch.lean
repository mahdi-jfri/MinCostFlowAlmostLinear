module

public import MinCostFlow.IPM.Machine.EpochNextLayout
public import MinCostFlow.IPM.Machine.EpochStartupGuard
public import MinCostFlow.IPM.Machine.EpochComplete
public import MinCostFlow.IPM.Machine.EpochBase
public import MinCostFlow.IPM.Machine.ReportStatus

/-!
# One target-test stage of Algorithm 7

First test the exact residual of the current explicit flow. If it
exceeds the stopping tolerance and is in range, start a fresh lazy epoch
from that flow and read its exact ending coordinates. The outer target
loop reads the result record and stops at the first failure.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The machine arguments that remain fixed throughout a target test,
including the two graph views. The loop replaces only the explicit flow
and the current allocation endpoint. -/
def targetEpochPacket {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (target quarter source heap : ℕ) : List ℕ :=
  [I.m,L.cost,L.lower,L.upper,L.alpha,L.one,target,L.slackMin,L.slackMax,quarter,
    L.gradientMin,L.gradientMax,L.lengthMin,L.request,L.graph,F.limbs,F.fmt.precision,L.exponent,
    Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision L.exponent,
    Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision L.exponent,source,heap,L.initGraph]

/-- Return the endpoint of a fresh pointer and status record. -/
def targetEpochReturn (record : ℕ) (flow status heap : Expr) : Stmt :=
  .call 31 record [flow,status,heap] ;; .ret (.reg 31)

/-- The checked startup forwards its own new packet. Its returned endpoint
determines the actual name list, while the arrays and handle are computed
from the same coefficient heap. -/
def targetEpochCompleteArgs : List Expr :=
  [.bin .add (.reg 30) (.bin .add (.reg 18) (.reg 19)),
    .bin .sub (.bin .sub (.reg 25) (.const 3)) (.reg 0),.reg 0,.reg 20,.reg 2,.reg 3,
    .reg 23,.reg 15,.reg 25,.reg 1,.reg 24,.reg 4,.reg 5,.reg 7,.reg 8,.reg 16,
    .reg 17,.reg 30,.bin .add (.reg 30) (.reg 18),.reg 0,
    .reg 14,.reg 13,.reg 10,.reg 11,.reg 12,.reg 0]

/-- Run the exact residual and retain the end of its numerical workspace. -/
def targetEpochSetup (base : ℕ) : Stmt :=
  .call 30 base [.reg 1,.reg 20,.reg 0,.reg 6,.reg 15,.reg 21,.reg 7,.reg 8,.reg 9] ;;
  .assign 23 (.bin .add (.reg 21)
    (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 4)) (.reg 15)))

/-- Forward the new coefficient heap and all fixed startup inputs. -/
def targetEpochStartupArgs : List Expr :=
  [.reg 0,.reg 1,.reg 24,.reg 2,.reg 23,.reg 3,.reg 4,.reg 5,.reg 15,.reg 16,
    .reg 17,.reg 18,.reg 19,.reg 30,.reg 22,.reg 10,.reg 11,.reg 12]

/-- Prepare the new residual address, initialize, and read the full
coefficient scan's recorded decision. -/
def targetEpochInit (startup : ℕ) : Stmt :=
  .assign 24 (.bin .sub (.reg 23) (.reg 15)) ;;
  .call 25 startup targetEpochStartupArgs ;;
  .assign 26 (.load (.bin .sub (.reg 25) (.const 1)))

/-- Forward the actual initialized packet only when its scan succeeded. -/
def targetEpochAfterInit (complete record : ℕ) : Stmt :=
  .cond (.reg 26)
    (.call 27 complete targetEpochCompleteArgs ;;
      .assign 28 (.load (.bin .sub (.reg 27) (.const 1))) ;;
      targetEpochReturn record (.reg 23) (.bin .mul (.const 2) (.reg 28)) (.reg 27))
    (targetEpochReturn record (.reg 20) (.const 0) (.reg 25))

/-- Dispatch on the residual outcome before entering the new epoch. -/
def targetEpochBranch (startup complete record : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 30) (.const 3))
    (targetEpochReturn record (.reg 20) (.bin .eq (.reg 30) (.const 0)) (.reg 23))
    (targetEpochInit startup ;; targetEpochAfterInit complete record)

/-- One stage of Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69).
The result status is zero for failure, one for convergence, and two for
a continuing epoch with a newly materialized explicit flow. -/
def targetEpochBody (base startup complete record : ℕ) : Stmt :=
  targetEpochSetup base ;; targetEpochBranch startup complete record

/-- The outer stage contains no random statements. -/
theorem targetEpochBody_noRand (base startup complete record : ℕ) :
    (targetEpochBody base startup complete record).NoRand := by
  simp [targetEpochBody,targetEpochSetup,targetEpochBranch,targetEpochInit,targetEpochAfterInit,targetEpochReturn,Stmt.NoRand]

/-- `V`-passing stage packet: appends `V` at index 23 (`.reg 23`). -/
def targetEpochPacketWithV {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (target quarter source heap V : ℕ) : List ℕ :=
  targetEpochPacket L F I target quarter source heap ++ [V]

/-- Save `V` from `.reg 23` into unused `.reg 29` before `targetEpochSetup` overwrites `.reg 23`. -/
def targetEpochSetupWithV (base : ℕ) : Stmt :=
  .assign 29 (.reg 23) ;; targetEpochSetup base

/-- Forward the startup arguments plus `V` (saved in `.reg 29`). -/
def targetEpochStartupArgsWithV : List Expr :=
  targetEpochStartupArgs ++ [.reg 29]

/-- `V`-passing variant of `targetEpochInit`. -/
def targetEpochInitWithV (startup : ℕ) : Stmt :=
  .assign 24 (.bin .sub (.reg 23) (.reg 15)) ;;
  .call 25 startup targetEpochStartupArgsWithV ;;
  .assign 26 (.load (.bin .sub (.reg 25) (.const 1)))

/-- `V`-passing variant of `targetEpochBranch`. -/
def targetEpochBranchWithV (startup complete record : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 30) (.const 3))
    (targetEpochReturn record (.reg 20) (.bin .eq (.reg 30) (.const 0)) (.reg 23))
    (targetEpochInitWithV startup ;; targetEpochAfterInit complete record)

/-- `V`-passing variant of `targetEpochBody`. -/
def targetEpochBodyWithV (base startup complete record : ℕ) : Stmt :=
  targetEpochSetupWithV base ;; targetEpochBranchWithV startup complete record

/-- The `V`-passing outer stage contains no random statements. -/
theorem targetEpochBodyWithV_noRand (base startup complete record : ℕ) :
    (targetEpochBodyWithV base startup complete record).NoRand := by
  simp [targetEpochBodyWithV,targetEpochSetupWithV,targetEpochSetup,targetEpochBranchWithV,
    targetEpochInitWithV,targetEpochAfterInit,targetEpochReturn,Stmt.NoRand]

end MinCostFlow.IPM.Machine
