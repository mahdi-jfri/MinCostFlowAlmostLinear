module

public import MinCostFlow.Scaling.CapacityScalingContract
public import MinCostFlow.Scaling.PositiveInstanceProgram
public import MinCostFlow.Scaling.EraseZeroFlowProgram
public import MinCostFlow.Scaling.MeasuredCostScaling

/-!
# Invoking capacity scaling on the positive-capacity representation

The cost model retains inactive edge slots. Construct its exact
`positiveInstance`, call the full capacity-scaling procedure, and erase
the dummy-loop coordinates. The output is the value of `invokePositive`
with the capacity model as its inner procedure. No primitive solver is
substituted for that inner model call.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityPositiveBody (positive scaling erase : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 positive [.reg 0,.reg 2] ;;
  .call 5 scaling [.reg 2,.reg 1,.reg 4] ;;
  .assign 6 (.bin .sub (.reg 5) (.reg 3)) ;;
  .call 7 erase [.bin .add (.reg 0) (.const 2),.reg 6,.reg 3,.reg 5] ;;
  .ret (.reg 7)

/-- Positive graph construction, full capacity scaling, and dummy erasure. -/
def capacityPositiveModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let erase := b+5+(capacityScalingModule solver entry (b+5)).length
  capacityPositiveBody (b+1) (b+5) erase ::
    (positiveInstanceModule (b+1) ++ capacityScalingModule solver entry (b+5) ++ eraseZeroFlowModule erase)

/-- Fresh positive graph, complete capacity reserve, and final erased vector. -/
def capacityPositiveSpace (J : Circulation) (C U : ℕ) : ℕ :=
  2+5*J.m+capacityScalingSpace J.positiveInstance C U+J.m+2

/-- Exact counted inner-call value as an unsigned array at the final `m`
words. Construction and erasure add explicit linear work to the inner cost. -/
noncomputable def capacityPositiveContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := J.invokePositive (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.n+1<2^w ∧ 8<2^w ∧
      J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 1≤U ∧ ZeroFrom mem heap ∧
      heap+capacityPositiveSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+capacityPositiveSpace J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧ ZeroFrom mem' ret ∧
      ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (capacityScalingContract w solver entry T hproc J.positiveInstance C U).cost [] (fun _ => 0)+
      400*J.m+900 }

/-- Construction, capacity scaling, and erasure use no random instruction. -/
theorem capacityPositiveModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityPositiveModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityPositiveBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | he
    · rcases List.mem_append.mp hb with hp | hs
      · exact positiveInstanceModule_noRand _ body hp
      · exact capacityScalingModule_noRand solver entry _ hdet body hs
    · have heq := List.mem_singleton.mp he
      subst body
      exact eraseZeroFlowBody_noRand _

end MinCostFlow.Scaling.Machine
