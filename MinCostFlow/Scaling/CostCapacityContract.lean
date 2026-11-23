module

public import MinCostFlow.Scaling.CostCapacityModel
public import MinCostFlow.Scaling.CostScalingContract

/-!
# The exact cost-capacity model entry

The composed model supplies every capacity invocation with the budget
`max U (2*m+1)`. Read the source edge count, compute that maximum, and call
the complete measured cost-scaling procedure. This entry adds only
constant work and retains the exact model flow in the solver-array layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,costBound,capacityBound,heap]`. -/
def costCapacityBody (scaling : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .mul (.const 2) (.reg 4)) (.const 1)) ;;
  .cond (.bin .lt (.reg 2) (.reg 5))
    (.call 6 scaling [.reg 0,.reg 1,.reg 5,.reg 3] ;; .ret (.reg 6))
    (.call 6 scaling [.reg 0,.reg 1,.reg 2,.reg 3] ;; .ret (.reg 6))

/-- Budget augmentation followed by the complete cost-scaling module. -/
def costCapacityModule (solver : Program) (entry b : ℕ) : List Stmt :=
  costCapacityBody (b+1) :: costScalingModule solver entry (b+1)

/-- Exact complete cost-capacity model on arbitrary natural capacities
and bounded integer costs, with its actual primitive-call and work budget. -/
noncomputable def costCapacityContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let V := max U (2*J.m+1)
  let r := costCapacityModel (canonicalSolver solver entry T hproc) J C U
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      ZeroFrom mem heap ∧ heap+costScalingSpace J C V<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+costScalingSpace J C V ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))+
      303000*(solver.regBound+1)*r.work }

/-- Budget selection and the full nested scaling program use no random instruction. -/
theorem costCapacityModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ costCapacityModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costCapacityBody,Stmt.NoRand,and_self]
  · exact costScalingModule_noRand solver entry _ hdet body hb

end MinCostFlow.Scaling.Machine
