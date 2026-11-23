module

public import MinCostFlow.Scaling.BottleneckBudget
public import MinCostFlow.Scaling.BottleneckUpdateProgram
public import MinCostFlow.Scaling.BottleneckStepBounds

/-!
# Machine interface for a bottleneck binary-search step

The stored interval determines whether to perform a threshold solve.
A nonempty interval reads its midpoint candidate, executes the exact test,
and writes the acceptance update. An empty interval copies its state
through the same update procedure without making a solver call.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,candidates,state,heap]`. -/
def bottleneckStepBody (test update : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.load (.reg 2)) ;;
  .assign 6 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .cond (.bin .lt (.reg 5) (.reg 6))
    (.assign 7 (.bin .div (.bin .add (.reg 5) (.reg 6)) (.const 2)) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .call 9 test [.reg 0,.reg 8,.reg 3] ;;
     .assign 10 (.bin .sub (.reg 9) (.bin .add (.bin .mul (.const 5) (.reg 4)) (.const 2))) ;;
     .assign 11 (.load (.bin .sub (.reg 9) (.const 2))) ;;
     .call 12 update [.reg 2,.reg 7,.reg 8,.reg 10,.reg 11,.reg 9] ;;
     .ret (.reg 12))
    (.call 12 update [.reg 2,.reg 6,.const 0,.const 0,.const 0,.reg 3] ;;
     .ret (.reg 12))

/-- Step entry followed by its exact test and fresh state update. -/
def bottleneckStepModule (solver : Program) (f b : ℕ) : List Stmt :=
  let u := b+1+(bottleneckTestModule solver f (b+1)).length
  bottleneckStepBody (b+1) u ::
    (bottleneckTestModule solver f (b+1) ++ bottleneckUpdateModule u)

/-- Exact model state update, with common candidate workspace and a solver
cost only when the interval is nonempty. Header and referenced-flow bounds
are preserved for the next iteration. -/
noncomputable def bottleneckStepContract (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C : ℕ) : Contract :=
  let G := bottleneckGuestBound J candidates
  let next := (BottleneckState.step (canonicalSolver solver f T hproc) candidates s).value
  let H := heapContract w
    (fun args mem => ∃ a vec state heap,args=[a,vec,state,heap] ∧
      ListAt mem a J.solverWords ∧ ListAt mem vec candidates ∧ BottleneckStateAt mem state s ∧
      a+J.solverWords.length ≤ heap ∧ vec+candidates.length ≤ heap ∧ state+5 ≤ heap ∧
      (∀ x ∈ J.solverWords,x<2^w) ∧ (∀ x ∈ candidates,x<2^w) ∧
      (∀ i<5,mem (state+i)<2^w) ∧
      (∀ u flow,s.best=some (u,flow) → mem (state+4)+J.m ≤ heap) ∧
      candidates.length=J.m ∧ s.lower≤s.upper ∧ s.upper≤J.m ∧
      2*J.m+2<2^w ∧ J.m*C<2^w ∧ 2^(G+1)+2 ≤ 2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => if s.lower<s.upper then
      (solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound+1500*J.m+2200 else 200)
    (fun _ _ => if s.lower<s.upper then 12+15*J.m+2^G else 5)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+5 ≤ ret ∧ BottleneckStateAt mem' (ret-5) next ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,next.best=some (u,flow) → mem' (ret-5+4)+J.m ≤ ret) }

/-- The step is deterministic whenever the supplied solver is. -/
theorem bottleneckStepModule_noRand (solver : Program) (f b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ bottleneckStepModule solver f b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckStepBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with ht | hu
    · exact bottleneckTestModule_noRand solver f _ hdet body ht
    · exact bottleneckUpdateModule_noRand _ body hu

/-- The step's machine cost charges the canonical solver overhead exactly
once per recorded model call. All remaining instructions are covered by a
constant multiple of the model's non-solver work. -/
theorem bottleneckStep_cost_model_le (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (bottleneckStepContract w solver f T hproc J candidates s C).cost args mem ≤
      (BottleneckState.step (canonicalSolver solver f T hproc) candidates s).calls.length*
        ((solver.regBound+6)*T (J.n+1) J.m+40*bottleneckGuestBound J candidates+solver.regBound)+
      200*(BottleneckState.step (canonicalSolver solver f T hproc) candidates s).work := by
  by_cases ha : s.lower<s.upper
  · simp only [bottleneckStepContract,heapContract,BottleneckState.step,ha,↓reduceIte,
      List.length_cons,List.length_nil]
    omega
  · simp only [bottleneckStepContract,heapContract,BottleneckState.step,ha,↓reduceIte,
      List.length_nil,Nat.zero_mul,Nat.mul_one,Nat.zero_add]
    exact le_rfl

end MinCostFlow.Scaling.Machine
