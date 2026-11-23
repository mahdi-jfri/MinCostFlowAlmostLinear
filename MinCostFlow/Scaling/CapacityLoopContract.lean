module

public import MinCostFlow.Scaling.CapacityRoundsProgram
public import MinCostFlow.Scaling.CapacityInitialProgram
public import MinCostFlow.Scaling.CapacityRoundsLoopContract
import WordRAM.Logic

/-!
# The complete capacity-loop machine entry

Compute the model's prescribed round count, initialize its zero-flow
state, and execute that many capacity steps. The final state is the exact
`capacityLoop` model value. One uniform reserve covers initialization and
every possible executed round, including one extra step margin.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityLoopBody (rounds initial loop : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 rounds [.reg 3,.reg 1] ;;
  .call 5 initial [.reg 0,.reg 2] ;;
  .assign 6 (.bin .sub (.reg 5) (.const 2)) ;;
  .call 7 loop [.reg 0,.reg 6,.reg 4,.reg 5] ;;
  .ret (.reg 7)

/-- Round computation, initial state, and the complete repeated-step code. -/
def capacityLoopModule (solver : Program) (entry b : ℕ) : List Stmt :=
  capacityLoopBody (b+1) (b+3) (b+5) ::
    (capacityRoundsModule (b+1) ++ capacityInitialModule (b+3) ++ capacityRoundsLoopModule solver entry (b+5))

/-- Exact full capacity loop with all setup charged to its own model work. -/
noncomputable def capacityLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let N := (capacityStepNumberBase J C U)^256
  let fuel := capacityRounds J.m U
  let r := capacityLoop (canonicalSolver solver entry T hproc) J U
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ ZeroFrom mem heap ∧ heap+J.m+2+(fuel+1)*N<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+J.m+2+fuel*N ∧
      CapacityStateAt mem' (ret-2) ret r.value ∧ ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+1) (J.m+J.m))+
      101000*(solver.regBound+1)*r.work }

/-- Every full-loop procedure is deterministic when the primitive solver is. -/
theorem capacityLoopModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityLoopModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityLoopBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hr | hi
      · exact capacityRoundsModule_noRand _ body hr
      · exact capacityInitialModule_noRand _ body hi
    · exact capacityRoundsLoopModule_noRand solver entry _ hdet body hl

end MinCostFlow.Scaling.Machine
