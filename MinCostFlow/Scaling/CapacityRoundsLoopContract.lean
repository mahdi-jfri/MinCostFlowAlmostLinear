module

public import MinCostFlow.Scaling.CapacityStepProgram
public import MinCostFlow.Scaling.CapacityStepWords
import WordRAM.Logic

/-!
# Repeating the capacity step with a bounded fuel

Run the preceding rounds first, then one capacity step, exactly as the
model's `forRounds`. Every state header occupies the final two words of
its heap. One common polynomial reserve per remaining round covers every
possible current flow and selected magnitude.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,state,fuel,heap]`. -/
def capacityRoundsLoopBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.call 4 self [.reg 0,.reg 1,.bin .sub (.reg 2) (.const 1),.reg 3] ;;
     .assign 5 (.bin .sub (.reg 4) (.const 2)) ;;
     .call 6 step [.reg 0,.reg 5,.reg 4] ;;
     .ret (.reg 6))

/-- Recursive repetition followed by the complete capacity step. -/
def capacityRoundsLoopModule (solver : Program) (entry b : ℕ) : List Stmt :=
  capacityRoundsLoopBody b (b+1) :: capacityStepModule solver entry (b+1)

/-- Exact finite capacity iteration, with one extra step reserve to keep
the same numerical premises available at every recursive call. -/
noncomputable def capacityRoundsLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (C U fuel : ℕ) : Contract :=
  let N := (capacityStepNumberBase J C U)^256
  let r := CallResult.forRounds (CapacityState.step (canonicalSolver solver entry T hproc)) fuel s
  { pre := fun args mem => ∃ a state heap,args=[a,state,fuel,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+2=heap ∧ CapacityStateAt mem state heap s ∧
      (∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ ZeroFrom mem heap ∧ heap+(fuel+1)*N<2^w ∧ fuel<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+fuel*N ∧
      CapacityStateAt mem' (ret-2) ret r.value ∧ ZeroFrom mem' ret ∧
      ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+1) (J.m+J.m))+
      100000*(solver.regBound+1)*r.work+100 }

/-- Repetition and all step procedures are deterministic whenever the
primitive solver is deterministic. -/
theorem capacityRoundsLoopModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityRoundsLoopModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoundsLoopBody,Stmt.NoRand,and_self]
  · exact capacityStepModule_noRand solver entry _ hdet body hb

end MinCostFlow.Scaling.Machine
