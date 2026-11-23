module

public import MinCostFlow.Scaling.CapacityRoutingSolveContract
public import MinCostFlow.Scaling.ResidualAugmentProgram
public import MinCostFlow.Scaling.CapacityRoutingValues

/-!
# Augmenting the capacity model's source routing

The routing residual correction is returned in two consecutive halves.
Add its forward half to the retained starting vector and subtract the
reverse half. The result is the exact routing used by measured dual
extraction with capacity scaling as its inner procedure.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityRoutingOptimizeBody (solve augment : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .call 6 solve [.reg 0,.reg 1,.reg 2] ;;
  .assign 7 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 5) (.reg 5))) ;;
  .assign 8 (.bin .add (.reg 5) (.reg 5)) ;;
  .assign 9 (.bin .sub (.reg 6) (.reg 8)) ;;
  .call 10 augment [.reg 7,.reg 9,.reg 5,.reg 6] ;;
  .ret (.reg 10)

/-- The complete capacity-backed residual solve followed by augmentation. -/
def capacityRoutingOptimizeModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let aug := b+1+(capacityRoutingSolveModule solver entry (b+1)).length
  capacityRoutingOptimizeBody (b+1) aug ::
    (capacityRoutingSolveModule solver entry (b+1) ++ residualAugmentModule aug)

/-- The capacity-backed solve reserve followed by one routing coordinate per edge. -/
def capacityRoutingOptimizeSpace (J : Circulation) (C U : ℕ) : ℕ :=
  capacityRoutingSolveSpace J C U+(J.m+J.n)

/-- Retain the source-routing graph at the original heap and return its
exact model routing in the final `m+n` words. -/
noncomputable def capacityRoutingOptimizeContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let M := J.m+J.n
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ ZeroFrom mem heap ∧ heap+capacityRoutingOptimizeSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args+4+17*M≤ret ∧
      ret≤heapArg args+capacityRoutingOptimizeSpace J C U ∧
      ListAt mem' (heapArg args) J.shortestRoutingGraph.solverWords ∧
      ListAt mem' (ret-M) (List.ofFn (fun e => (capacitySolvedRouting solver entry T hproc J U e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (capacityRoutingSolveContract w solver entry T hproc J C U).cost [] (fun _ => 0)+
      100*M+300 }

/-- Solving and augmenting the routing uses no random instruction. -/
theorem capacityRoutingOptimizeModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityRoutingOptimizeModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoutingOptimizeBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hs | ha
    · exact capacityRoutingSolveModule_noRand solver entry _ hdet body hs
    · exact residualAugmentModule_noRand _ body ha

end MinCostFlow.Scaling.Machine
