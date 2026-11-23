module

public import MinCostFlow.IPM.Machine.SolverResources
public import MinCostFlow.IPM.Machine.WorkspaceProgram
import MinCostFlow.Num.ModulePlacement

/-!
# The bounded circulation solver entry

The empty circulation needs no output words. Otherwise the driver
reserves the original output prefix, builds the augmented graph and
midpoint and dispatches the search at the selected format. Search
and the forest rounder use their supplied data-structure entries.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Construct the fixed test packet from the tables and limits in
the caller's registers. -/
def solverStartSearchArgs : List Expr :=
  let add : Expr → Expr → Expr := .bin .add
  let mul : Expr → Expr → Expr := .bin .mul
  let read (r i : ℕ) : Expr := .load (add (.reg r) (.const i))
  let arr := (.reg 20 : Expr)
  let mL := (.reg 21 : Expr)
  let guards := (.reg 22 : Expr)
  let L := (.reg 11 : Expr)
  [.reg 9,add arr mL,arr,add arr (mul (.const 5) mL),
    add (.reg 1) (.const 7),add arr (mul (.const 9) mL),.const 0,
    guards,add guards L,add guards (mul (.const 2) L),
    add guards (mul (.const 3) L),add guards L,guards,add guards (mul (.const 4) L),
    .reg 0,L,.reg 12,.reg 13,read 15 0,read 15 1,.reg 2,.reg 19,.reg 3,
    read 18 0,read 18 1,read 18 2,.reg 6,.reg 7,.reg 8]

/-- Arguments `[rowGraph,params,source,heap,V,k,augN,originalM,dest]`.
Prepares the named graph, coefficient tables and both loop limits. -/
def solverAfterInitBody (setup workspace limits finish : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 5))) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 13 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 14 (.load (.bin .add (.reg 1) (.const 6))) ;;
  .call 15 setup [.reg 0,.reg 13,.reg 11,.reg 12,.reg 5,.reg 14,.reg 3] ;;
  .call 18 workspace [.reg 9,.reg 11,.reg 12,.reg 13,.reg 15] ;;
  .call 19 limits [.reg 9,.reg 4,.reg 5,.reg 14,.reg 18] ;;
  .assign 20 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 6))
    (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 21 (.bin .mul (.reg 9) (.reg 11)) ;;
  .assign 22 (.bin .add (.bin .add (.reg 20) (.bin .mul (.const 9) (.reg 21))) (.reg 11)) ;;
  .call 23 finish solverStartSearchArgs ;;
  .ret (.reg 23)

/-- Positive-size driver. The quality statement writes register 24
after the augmented edge count has been read into register 8. -/
def solverPositiveBodyWith (choose : Stmt) (penalty initEntry proceed : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.bin .add (.reg 1) (.reg 2)) ;;
  .call 5 penalty [.reg 2] ;;
  .call 6 initEntry [.reg 0,.reg 4] ;;
  .assign 7 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 3))) ;;
  .assign 8 (.load (.bin .add (.reg 7) (.const 1))) ;;
  .assign 9 (.bin .add (.bin .add (.reg 7) (.const 2)) (.bin .mul (.const 5) (.reg 8))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 9) (.const 7))
    (.load (.bin .add (.reg 9) (.const 5)))) ;;
  choose ;;
  .call 11 proceed [.reg 7,.reg 9,.reg 10,.reg 6,.reg 5,.reg 24,
    .bin .add (.reg 3) (.const 1),.reg 2,.reg 1] ;;
  .ret (.reg 11)

/-- Positive-size driver with constant quality. -/
def solverPositiveBody (k penalty initEntry proceed : ℕ) : Stmt :=
  solverPositiveBodyWith (.assign 24 (.const k)) penalty initEntry proceed

/-- Positive-size driver that calls the quality procedure on the augmented size. -/
def solverPositiveRuntimeBody (quality penalty initEntry proceed : ℕ) : Stmt :=
  solverPositiveBodyWith (.call 24 quality [.reg 8]) penalty initEntry proceed

/-- The bounded solver of Appendix C, Lemma C.1, arguments `[input,heap]`. -/
def boundedIPMBody (positive : ℕ) : Stmt :=
  .cond (.load (.bin .add (.reg 0) (.const 1)))
    (.call 2 positive [.reg 0,.reg 1] ;; .ret (.reg 2))
    (.ret (.reg 1))

/-- These driver statements use no random instruction. -/
theorem boundedIPMBody_noRand (positive : ℕ) : (boundedIPMBody positive).NoRand := by
  simp [boundedIPMBody,Stmt.NoRand]

theorem solverPositiveBody_noRand (k penalty initEntry proceed : ℕ) :
    (solverPositiveBody k penalty initEntry proceed).NoRand := by
  simp [solverPositiveBody,solverPositiveBodyWith,Stmt.NoRand]

theorem solverPositiveRuntimeBody_noRand (quality penalty initEntry proceed : ℕ) :
    (solverPositiveRuntimeBody quality penalty initEntry proceed).NoRand := by
  simp [solverPositiveRuntimeBody,solverPositiveBodyWith,Stmt.NoRand]

theorem solverAfterInitBody_noRand (setup workspace limits finish : ℕ) :
    (solverAfterInitBody setup workspace limits finish).NoRand := by
  simp [solverAfterInitBody,Stmt.NoRand]

/-- `V`-passing search-start arguments: appends `V` from `.reg 4`. -/
def solverStartSearchArgsWithV : List Expr :=
  solverStartSearchArgs ++ [.reg 4]

/-- `V`-passing variant of `solverAfterInitBody`. -/
def solverAfterInitBodyWithV (setup workspace limits finish : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 5))) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 13 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 14 (.load (.bin .add (.reg 1) (.const 6))) ;;
  .call 15 setup [.reg 0,.reg 13,.reg 11,.reg 12,.reg 5,.reg 14,.reg 3] ;;
  .call 18 workspace [.reg 9,.reg 11,.reg 12,.reg 13,.reg 15] ;;
  .call 19 limits [.reg 9,.reg 4,.reg 5,.reg 14,.reg 18] ;;
  .assign 20 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 6))
    (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 21 (.bin .mul (.reg 9) (.reg 11)) ;;
  .assign 22 (.bin .add (.bin .add (.reg 20) (.bin .mul (.const 9) (.reg 21))) (.reg 11)) ;;
  .call 23 finish solverStartSearchArgsWithV ;;
  .ret (.reg 23)

theorem solverAfterInitBodyWithV_noRand (setup workspace limits finish : ℕ) :
    (solverAfterInitBodyWithV setup workspace limits finish).NoRand := by
  simp [solverAfterInitBodyWithV,Stmt.NoRand]

end MinCostFlow.IPM.Machine
