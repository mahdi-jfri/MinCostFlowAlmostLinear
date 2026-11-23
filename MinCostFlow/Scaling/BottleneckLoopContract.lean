module

public import MinCostFlow.Scaling.BottleneckStepProgram

/-!
# The bounded bottleneck-search loop interface

The loop follows the model's `forRounds`: run the earlier rounds, then one
step. Each state header is the final five words before its heap. This also
represents the zero-round result without a copy. The cost records solver
calls separately from the model's other work.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,candidates,state,rounds,heap]`. -/
def bottleneckLoopBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 0)) (.ret (.reg 4))
    (.call 5 self [.reg 0,.reg 1,.reg 2,.bin .sub (.reg 3) (.const 1),.reg 4] ;;
     .assign 6 (.bin .sub (.reg 5) (.const 5)) ;;
     .call 7 step [.reg 0,.reg 1,.reg 6,.reg 5] ;;
     .ret (.reg 7))

/-- Recursive loop entry followed by the complete step module. -/
def bottleneckLoopModule (solver : Program) (f b : ℕ) : List Stmt :=
  bottleneckLoopBody b (b+1) :: bottleneckStepModule solver f (b+1)

/-- The exact finite model loop. One extra step's space is reserved to
make the same source-layout premises available even at zero rounds. -/
noncomputable def bottleneckLoopContract (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C rounds : ℕ) : Contract :=
  let G := bottleneckGuestBound J candidates
  let A := 12+15*J.m+2^G
  let result := CallResult.forRounds (BottleneckState.step (canonicalSolver solver f T hproc) candidates) rounds s
  let H := heapContract w
    (fun args mem => ∃ a vec state heap,args=[a,vec,state,rounds,heap] ∧
      (bottleneckStepContract w solver f T hproc J candidates s C).pre [a,vec,state,heap] mem ∧
      state+5=heap ∧ rounds<2^w)
    (fun _ _ _ => True)
    (fun _ _ => result.calls.length*
      ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+200*result.work+20)
    (fun _ _ => (rounds+1)*A)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      ret ≤ heapArg args+rounds*A ∧
      BottleneckStateAt mem' (ret-5) result.value ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,result.value.best=some (u,flow) → mem' (ret-5+4)+J.m ≤ ret) }

/-- Every bounded loop procedure is deterministic when its solver is. -/
theorem bottleneckLoopModule_noRand (solver : Program) (f b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ bottleneckLoopModule solver f b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckLoopBody,Stmt.NoRand,and_self]
  · exact bottleneckStepModule_noRand solver f _ hdet body hb

end MinCostFlow.Scaling.Machine
