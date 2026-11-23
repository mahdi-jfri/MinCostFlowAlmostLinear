module

public import MinCostFlow.Scaling.TwoCallReductionContract
public import MinCostFlow.Scaling.ShiftedGraphProgram
public import MinCostFlow.Scaling.IsolatedCheckProgram

/-!
# The full bounded-demand general-flow scaling entry

Capacity order is checked before constructing a shifted graph. The
isolated-demand scan then decides whether to invoke the exact two-call
procedure. Either rejected check gives the same failed model answer,
so this order preserves the checked model's result and solver calls.
The positive cost budget is `max C 1`, computed with one zero test and
addition. Eight shared phase regions cover all checks and both solves.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,C,U,heap]`; raw cost bound zero is allowed. -/
def generalScalingBody (check graph isolated solve failure : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 1) (.bin .eq (.reg 1) (.const 0))) ;;
  .call 6 check [.bin .add (.reg 0) (.const 2),.reg 4] ;;
  .cond (.bin .eq (.reg 6) (.const 0))
    (.call 7 failure [.reg 3] ;; .ret (.reg 7))
    (.call 7 graph [.reg 0,.reg 3] ;;
     .call 8 isolated [.reg 0,.reg 3,.reg 7] ;;
     .assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
     .cond (.bin .eq (.reg 9) (.const 0))
       (.call 10 failure [.reg 8] ;; .ret (.reg 10))
       (.call 10 solve [.reg 0,.reg 5,.reg 2,.reg 8] ;; .ret (.reg 10)))

/-- Capacity order, shifted graph, isolated demands, complete two-call
scaling, and failed-answer serialization. -/
def generalScalingModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let graph := b+3
  let isolated := graph+(shiftedGraphModule graph).length
  let solve := isolated+(isolatedCheckModule isolated).length
  let failure := solve+(twoCallReductionModule solver entry solve).length
  generalScalingBody (b+1) graph isolated solve failure ::
    (capacityCheckModule (b+1) ++ (shiftedGraphModule graph ++
      (isolatedCheckModule isolated ++ (twoCallReductionModule solver entry solve ++ infeasibleResultModule failure))))

/-- The exact bounded-demand general model, including isolated demands
and inconsistent capacities, with only the selected inner cost charged. -/
noncomputable def generalScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : Contract :=
  let region := 2^wordSize 16384 (I.encode++[max C 1,U])
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a I.encode ∧ a+I.encode.length≤heap ∧
      (∀ e,(I.edge e).cost.natAbs≤C) ∧ (∀ v : Fin I.n,(I.d v).natAbs≤U) ∧
      (∀ e,(I.edge e).lower.natAbs≤U) ∧ (∀ e,(I.edge e).upper.natAbs≤U) ∧
      ZeroFrom mem heap ∧ heap+8*region<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+8*region ∧
      ScalingAnswerAt mem' (ret-2) ret
        (scalingAnswerWords (FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U).value) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => 2000*(I.m+I.n+1)+
      if ∀ e,(I.edge e).lower≤(I.edge e).upper then
        (if FlowReduction.isolatedCheck I hv then
          (twoCallReductionContract w solver entry T hproc I hv (max C 1) U).cost [] (fun _ => 0)
        else 50)
      else 50 }

/-- The bounded-demand general scaling module uses no random instruction
whenever its supplied bounded circulation solver does not. -/
theorem generalScalingModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈generalScalingModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [generalScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact capacityCheckModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact shiftedGraphModule_noRand _ body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact isolatedCheckModule_noRand _ body hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact twoCallReductionModule_noRand solver entry _ hdet body hb
          · exact infeasibleResultModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
