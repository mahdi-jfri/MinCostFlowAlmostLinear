module

public import MinCostFlow.Scaling.RoutingResidualProgram
public import MinCostFlow.Scaling.CapacityPositiveContract

/-!
# Routing-residual calls to the full capacity model

Dual extraction constructs a source-routing graph and its direct starting
flow. Its residual circulation is solved by the capacity model's positive
adapter. Retain the routing graph and starting array for augmentation,
and return the residual correction in the final output words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityRoutingSolveBody (prepare solve : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .call 6 prepare [.reg 0,.reg 2] ;;
  .assign 7 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 6) (.reg 5))) ;;
  .call 8 solve [.reg 7,.reg 1,.reg 6] ;;
  .ret (.reg 8)

/-- Exact routing preparation followed by a full positive capacity-model call. -/
def capacityRoutingSolveModule (solver : Program) (entry b : ℕ) : List Stmt :=
  capacityRoutingSolveBody (b+1) (b+16) ::
    (routingResidualModule (b+1) ++ capacityPositiveModule solver entry (b+16))

/-- Preparation and the full model-call reserve. -/
def capacityRoutingSolveSpace (J : Circulation) (C U : ℕ) : ℕ :=
  4+16*(J.m+J.n)+capacityPositiveSpace (J.shortestRoutingGraph.residual J.shortestRoutingStart) C U

/-- Exact correction produced by the cost model's inner capacity call.
The source bound `n+1≤U` covers every routing residual capacity. -/
noncomputable def capacityRoutingSolveContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let M := J.m+J.n
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  let r := Q.invokePositive (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ ZeroFrom mem heap ∧ heap+capacityRoutingSolveSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args+4+16*M≤ret ∧
      ret≤heapArg args+capacityRoutingSolveSpace J C U ∧
      ListAt mem' (heapArg args) J.shortestRoutingGraph.solverWords ∧
      ListAt mem' (heapArg args+2+5*M) (List.ofFn (fun e => (J.shortestRoutingStart e).toNat)) ∧
      ListAt mem' (ret-Q.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (capacityPositiveContract w solver entry T hproc Q C U).cost [] (fun _ => 0)+
      1000*M+1400 }

/-- The complete routing-residual solver is deterministic. -/
theorem capacityRoutingSolveModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityRoutingSolveModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoutingSolveBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hp | hs
    · exact routingResidualModule_noRand _ body hp
    · exact capacityPositiveModule_noRand solver entry _ hdet body hs

end MinCostFlow.Scaling.Machine
