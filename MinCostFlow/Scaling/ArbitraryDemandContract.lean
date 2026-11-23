module

public import MinCostFlow.Scaling.GeneralScalingContract
public import MinCostFlow.Scaling.DemandCheckProgram

/-!
# The arbitrary-demand scaling entry

The outermost model first scans demands against `m*U`. Rejection writes
`[0]`; success invokes bounded-demand general scaling with `(m+1)*U`.
This procedure performs exactly that scan and multiplication, retaining
the model's exact answer and charging only the selected solving branch.
Ten shared phase regions cover the complete arbitrary-demand procedure.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,C,U,heap]`; no demand bound is assumed. -/
def arbitraryDemandBody (check solve failure : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 check [.reg 0,.reg 2] ;;
  .cond (.bin .eq (.reg 5) (.const 0))
    (.call 6 failure [.reg 3] ;; .ret (.reg 6))
    (.assign 6 (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 2)) ;;
     .call 7 solve [.reg 0,.reg 1,.reg 6,.reg 3] ;;
     .ret (.reg 7))

/-- Demand check, complete bounded-demand scaling, and failed answer. -/
def arbitraryDemandModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let solve := b+3
  let failure := solve+(generalScalingModule solver entry solve).length
  arbitraryDemandBody (b+1) solve failure ::
    (demandCheckModule (b+1) ++ (generalScalingModule solver entry solve ++ infeasibleResultModule failure))

/-- Exact arbitrary-demand model answer with no demand or feasibility
hypothesis, full memory frames, and a branch-sensitive cost. -/
noncomputable def arbitraryDemandContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : Contract :=
  let U' := (I.m+1)*U
  let region := 2^wordSize 16384 (I.encode++[max C 1,U'])
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a I.encode ∧ a+I.encode.length≤heap ∧
      (∀ e,(I.edge e).cost.natAbs≤C) ∧
      (∀ e,(I.edge e).lower.natAbs≤U) ∧ (∀ e,(I.edge e).upper.natAbs≤U) ∧
      ZeroFrom mem heap ∧ heap+10*region<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+10*region ∧
      ScalingAnswerAt mem' (ret-2) ret
        (scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
          (canonicalSolver solver entry T hproc) I hv C U).value) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => 200*(I.n+1)+
      if FlowReduction.demandBoundCheck I U then
        (generalScalingContract w solver entry T hproc I hv C U').cost [] (fun _ => 0)
      else 50 }

/-- The complete arbitrary-demand module has no random instruction
whenever its supplied bounded circulation solver does not. -/
theorem arbitraryDemandModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈arbitraryDemandModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [arbitraryDemandBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact demandCheckModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact generalScalingModule_noRand solver entry _ hdet body hb
      · exact infeasibleResultModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
