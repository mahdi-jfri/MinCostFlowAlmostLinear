module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
public import MinCostFlow.Scaling.ResidualOptimizationContract
public import MinCostFlow.Scaling.CapacityCheckProgram
public import MinCostFlow.Scaling.AnswerResultProgram

/-!
# The counted two-call reduction as a machine procedure

Check capacity order before allocating the feasibility phase. A failed
check or failed feasibility objective writes `[0]`. On success, restrict
the first flow without copying, solve its residual circulation, and write
the resulting signed flow with the success tag. Each branch returns the
common answer pointer header. Four complete source-width regions cover
both solve phases and serialization together.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,C,U,heap]`, with `C>=1`. -/
def twoCallReductionBody (check first second success failure : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 check [.bin .add (.reg 0) (.const 2),.reg 4] ;;
  .cond (.bin .eq (.reg 5) (.const 0))
    (.call 6 failure [.reg 3] ;; .ret (.reg 6))
    (.call 6 first [.reg 0,.reg 1,.reg 2,.reg 3] ;;
     .assign 7 (.bin .sub (.reg 6) (.const 3)) ;;
     .assign 8 (.load (.reg 7)) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.call 9 failure [.reg 6] ;; .ret (.reg 9))
       (.assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
        .assign 10 (.load (.bin .add (.reg 7) (.const 2))) ;;
        .call 11 second [.reg 0,.reg 10,.reg 9,.reg 1,.reg 2,.reg 6] ;;
        .call 12 success [.bin .sub (.reg 11) (.bin .mul (.const 2) (.reg 4)),.reg 4,.reg 11] ;;
        .ret (.reg 12)))

/-- Capacity check, both complete phases, and both answer serializers. -/
def twoCallReductionModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let first := b+3
  let second := first+(feasibilityPhaseModule solver entry first).length
  let success := second+(residualOptimizationModule solver entry second).length
  let failure := success+(flowResultModule success).length
  twoCallReductionBody (b+1) first second success failure ::
    (capacityCheckModule (b+1) ++ (feasibilityPhaseModule solver entry first ++
      (residualOptimizationModule solver entry second ++
        (flowResultModule success ++ infeasibleResultModule failure))))

/-- The exact unguarded two-call model, including inconsistent capacities
and failed feasibility, with a branch-sensitive actual procedure budget. -/
noncomputable def twoCallReductionContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : Contract :=
  let B := FlowReduction.scalingCapacityBudget I U
  let inner := fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B
  let P := FlowReduction.buildFeasibilityInstance I hv
  let g := (Circulation.invokePruned inner P).value
  let f := fun e => g (Fin.castAdd (I.n+I.n) e)
  let good := P.integerObjective g = -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℤ)
  let region := 2^wordSize 16384 (I.encode++[C,U])
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a I.encode ∧ a+I.encode.length≤heap ∧
      1≤C ∧ (∀ e,(I.edge e).cost.natAbs≤C) ∧ (∀ v : Fin I.n,(I.d v).natAbs≤U) ∧
      (∀ e,(I.edge e).lower.natAbs≤U) ∧ (∀ e,(I.edge e).upper.natAbs≤U) ∧
      ZeroFrom mem heap ∧ heap+4*region<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+4*region ∧
      ScalingAnswerAt mem' (ret-2) ret
        (scalingAnswerWords (FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv).value) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => 200*I.m+500+
      if ∀ e,(I.edge e).lower≤(I.edge e).upper then
        (feasibilityPhaseContract w solver entry T hproc I hv C U).cost [] (fun _ => 0)+
          (if good then (residualOptimizationContract w solver entry T hproc I hv f C U).cost [] (fun _ => 0)+
            40*I.m+150 else 50)
      else 0 }

/-- The complete two-call module uses no random instruction whenever its
supplied bounded circulation solver does not. -/
theorem twoCallReductionModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈twoCallReductionModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [twoCallReductionBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact capacityCheckModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact feasibilityPhaseModule_noRand solver entry _ hdet body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact residualOptimizationModule_noRand solver entry _ hdet body hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact flowResultModule_noRand _ body hb
          · exact infeasibleResultModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
