module

public import MinCostFlow.Scaling.CapacityRoutingOptimizeContract
public import MinCostFlow.Scaling.PropagateLabelsProgram
public import MinCostFlow.Scaling.CapacityRoutingPotentials
public import MinCostFlow.Scaling.LabelOutputLayout

/-!
# The capacity-backed routing-label interface

After optimizing the source routing with the full capacity model,
propagate integer labels and expose the original vertices' label table
through one pointer at the old heap. The table is already in the shared
signed layout and needs no copying.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityRoutingLabelsBody (optimize labels : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .call 6 optimize [.reg 0,.reg 1,.reg 2] ;;
  .assign 7 (.bin .sub (.reg 6) (.reg 5)) ;;
  .call 8 labels [.reg 2,.reg 7,.reg 3,.reg 6] ;;
  .store (.reg 2) (.bin .add (.reg 6) (.const 2)) ;;
  .ret (.reg 8)

/-- Capacity-backed routing optimization followed by exact label traversal. -/
def capacityRoutingLabelsModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let labels := b+1+(capacityRoutingOptimizeModule solver entry (b+1)).length
  capacityRoutingLabelsBody (b+1) labels ::
    (capacityRoutingOptimizeModule solver entry (b+1) ++ propagateLabelsModule labels)

/-- Optimization storage and a full traversal reserve, including a two-cell margin. -/
def capacityRoutingLabelsSpace (J : Circulation) (C U : ℕ) : ℕ :=
  capacityRoutingOptimizeSpace J C U+5+5*(J.n+1)+6*(J.m+J.n)+2

/-- The old heap holds a fitting pointer to exactly the model's old-vertex
signed label table. All original source memory is preserved. -/
noncomputable def capacityRoutingLabelsContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ (J.m+J.n+1)*C<2^w ∧ ZeroFrom mem heap ∧
      heap+capacityRoutingLabelsSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+capacityRoutingLabelsSpace J C U ∧
      (∀ x<heapArg args,mem' x=mem x) ∧ ZeroFrom mem' ret ∧
      ∃ ptr,heapArg args<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ mem' (heapArg args)=ptr ∧
        SignedTableAt mem' ptr (capacityRoutingPotentials solver entry T hproc J U)
    cost := fun _ _ => (capacityRoutingOptimizeContract w solver entry T hproc J C U).cost [] (fun _ => 0)+
      3000*(J.m+J.n)+1100 }

/-- The entire label-producing module is deterministic. -/
theorem capacityRoutingLabelsModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityRoutingLabelsModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoutingLabelsBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with ho | hl
    · exact capacityRoutingOptimizeModule_noRand solver entry _ hdet body ho
    · exact propagateLabelsModule_noRand _ body hl

end MinCostFlow.Scaling.Machine
