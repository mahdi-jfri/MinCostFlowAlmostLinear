module

public import MinCostFlow.Scaling.CostStepContract
public import MinCostFlow.Scaling.CostStepSpace

/-!
# The repeated measured cost-round machine

Recurse on the previous prefix, then execute one cost round on its returned
state. This is the order of the model's `forRounds`. The input state is the
initial zero state, so each recursive result is an actual reached prefix
and has the uniform numerical bounds. One additional round reserve covers
the next step's complete numerical and allocation premises.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,initialState,fuel,costBound,capacityBound,heap]`. -/
def costRoundsLoopBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 5))
    (.call 6 self [.reg 0,.reg 1,.bin .sub (.reg 2) (.const 1),.reg 3,.reg 4,.reg 5] ;;
     .assign 7 (.bin .sub (.reg 6) (.const 3)) ;;
     .call 8 step [.reg 0,.reg 7,.reg 3,.reg 4,.reg 6] ;;
     .ret (.reg 8))

/-- Repeated-prefix entry and the complete cost-round module. -/
def costRoundsLoopModule (solver : Program) (entry b : ℕ) : List Stmt :=
  costRoundsLoopBody b (b+1) :: costStepModule solver entry (b+1)

/-- Exact measured prefixes from the initial state, with uniform space,
actual primitive-call cost, and accumulated measured model work. -/
noncomputable def costRoundsLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U fuel : ℕ) : Contract :=
  let N := (costStepNumberBase J C U)^524
  let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
  let r := CallResult.forRounds (CostState.stepMeasured inner C) fuel (CostState.initial J)
  { pre := fun args mem => ∃ a state heap,args=[a,state,fuel,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+3=heap ∧ CostStateAt mem state heap (CostState.initial J) ∧
      J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 0<J.m ∧ J.n+1≤U ∧
      fuel≤costRounds J.n C ∧ ZeroFrom mem heap ∧ heap+(fuel+1)*N<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+fuel*N ∧
      CostStateAt mem' (ret-3) ret r.value ∧ ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      300000*(solver.regBound+1)*r.work+100 }

/-- Every repeated-round procedure is deterministic when its primitive
solver is deterministic. -/
theorem costRoundsLoopModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ costRoundsLoopModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costRoundsLoopBody,Stmt.NoRand,and_self]
  · exact costStepModule_noRand solver entry _ hdet body hb

end MinCostFlow.Scaling.Machine
