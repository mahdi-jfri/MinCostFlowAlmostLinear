module

public import MinCostFlow.Scaling.CostRoundsProgram
public import MinCostFlow.Scaling.CostInitialProgram
public import MinCostFlow.Scaling.CostRoundsLoopContract

/-!
# The complete measured cost-loop entry

Compute the exact round count, initialize the integer zero state, and
execute that many measured cost rounds. The final state is exactly
`costLoopMeasured` with the full capacity model as its inner procedure.
The shared uniform reserve covers initialization and every round.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,costBound,capacityBound,heap]`. -/
def costLoopBody (rounds initial loop : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .call 5 rounds [.reg 4,.reg 1] ;;
  .call 6 initial [.reg 0,.reg 3] ;;
  .assign 7 (.bin .sub (.reg 6) (.const 3)) ;;
  .call 8 loop [.reg 0,.reg 7,.reg 5,.reg 1,.reg 2,.reg 6] ;;
  .ret (.reg 8)

/-- Round counting, zero-state initialization, and all repeated cost rounds. -/
def costLoopModule (solver : Program) (entry b : ℕ) : List Stmt :=
  costLoopBody (b+1) (b+3) (b+5) ::
    (costRoundsModule (b+1) ++ costInitialModule (b+3) ++ costRoundsLoopModule solver entry (b+5))

/-- Exact complete measured loop, with setup charged to its model work. -/
noncomputable def costLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let N := (costStepNumberBase J C U)^524
  let fuel := costRounds J.n C
  let r := costLoopMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) J C
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ J.n+1≤U ∧ ZeroFrom mem heap ∧ heap+J.m+2*J.n+3+(fuel+1)*N<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+J.m+2*J.n+3+fuel*N ∧ CostStateAt mem' (ret-3) ret r.value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      301000*(solver.regBound+1)*r.work }

/-- Counting, initialization, and repetition are deterministic. -/
theorem costLoopModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ costLoopModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costLoopBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hr | hi
      · exact costRoundsModule_noRand _ body hr
      · exact costInitialModule_noRand _ body hi
    · exact costRoundsLoopModule_noRand solver entry _ hdet body hl

end MinCostFlow.Scaling.Machine
