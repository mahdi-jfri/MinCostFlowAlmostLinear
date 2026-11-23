module

public import MinCostFlow.Scaling.BuildFeasibilityProgram
public import MinCostFlow.Scaling.PrunedScalingContract
public import MinCostFlow.Scaling.MagnitudeCopyProgram
public import MinCostFlow.Scaling.FeasibilityObjectiveProgram
public import MinCostFlow.Scaling.CostHeaderProgram
public import MinCostFlow.Scaling.ReductionCapacityBounds

/-!
# The first circulation solve of the general-flow reduction

Build the shifted graph, shifted demands, and feasibility circulation.
Run the exact pruned cost-capacity solver, convert its restored signed
flow to unsigned magnitudes, and test the integer objective threshold.
A final three-word header records the branch flag, the full unsigned
feasibility flow, and the shifted graph needed by the optimization phase.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,C,U,heap]`, with a positive cost budget `C`. -/
def feasibilityPhaseBody (build solve copy test header : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 2))
      (.bin .mul (.const 11) (.reg 5))) (.bin .mul (.const 2) (.reg 4))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .mul (.const 5) (.reg 5))) ;;
  .call 8 build [.reg 0,.reg 3] ;;
  .assign 9 (.bin .add (.bin .mul (.bin .mul (.const 2)
      (.bin .add (.reg 5) (.const 1))) (.reg 2)) (.const 1)) ;;
  .call 10 solve [.reg 6,.reg 1,.reg 9,.reg 8] ;;
  .assign 11 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .call 12 copy [.bin .sub (.reg 10) (.bin .mul (.const 2) (.reg 11)),.reg 11,.reg 10] ;;
  .call 13 test [.reg 6,.reg 10,.reg 7,.reg 4,.reg 12] ;;
  .assign 14 (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 4) (.reg 11))) (.const 2)) ;;
  .call 15 header [.reg 13,.reg 10,.reg 3,.reg 14] ;;
  .ret (.reg 15)

/-- The first-solve entry and its already proved components. -/
def feasibilityPhaseModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let solve := b+1+(buildFeasibilityModule (b+1)).length
  let copy := solve+(prunedScalingModule solver entry solve).length
  let test := copy+1
  let header := test+(feasibilityObjectiveModule test).length
  feasibilityPhaseBody (b+1) solve copy test header ::
    (buildFeasibilityModule (b+1) ++ (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (feasibilityObjectiveModule test ++ costHeaderModule))))

/-- All allocations in the first-solve phase, including its result header. -/
def feasibilityPhaseSpace (I : Instance) (hv : I.IsValid) (C U : ℕ) : ℕ :=
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  4+16*I.m+12*I.n+prunedScalingSpace P C B+P.m+4*P.m+2+3

/-- Exact first-solve result. The final header is `[flag,flow,shiftedGraph]`;
the full unsigned feasibility flow and shifted graph remain available. -/
noncomputable def feasibilityPhaseContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : Contract :=
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let g := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P).value
  let flag := if P.integerObjective g = -((FlowReduction.shiftedGraph I hv).demandMass
    (FlowReduction.shiftedDemand I) : ℤ) then 1 else 0
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a I.encode ∧
      a+I.encode.length≤heap ∧ (∀ e∈I.edges,e.lower≤e.upper) ∧
      (∀ v : Fin I.n,(I.d v).natAbs≤U) ∧
      (∀ e∈I.edges,e.lower.natAbs≤U) ∧ (∀ e∈I.edges,e.upper.natAbs≤U) ∧
      (∀ x∈I.encode,x<2^w) ∧ (∀ x∈P.solverWords,x<2^w) ∧ 1≤C ∧ 8<2^w ∧
      (2*I.m+2)*U<2^w ∧ B<2^w ∧ I.n*B<2^w ∧ P.m*B<2^w ∧
      ZeroFrom mem heap ∧ heap+feasibilityPhaseSpace I hv C U<2^w
    post := fun args mem ret mem' => heapArg args+2+5*I.m≤ret ∧ ret≤heapArg args+feasibilityPhaseSpace I hv C U ∧
      ∃ flow,flow+P.m≤ret ∧ ListAt mem' flow (List.ofFn (fun e => (g e).toNat)) ∧
        ListAt mem' (ret-3) [flag,flow,heapArg args] ∧
        ListAt mem' (heapArg args) (FlowReduction.shiftedGraph I hv).solverWords ∧
        ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (prunedScalingContract w solver entry T hproc P C B).cost [] (fun _ => 0)+
      4000*(I.m+I.n+1) }

/-- The complete first-solve phase uses no random instruction when its
supplied bounded circulation solver does not. -/
theorem feasibilityPhaseModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈feasibilityPhaseModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [feasibilityPhaseBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact buildFeasibilityModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact prunedScalingModule_noRand solver entry _ hdet body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact magnitudeCopyModule_noRand _ body hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact feasibilityObjectiveModule_noRand _ body hb
          · have he : body=costHeaderBody := by simpa only [costHeaderModule,List.mem_singleton] using hb
            subst body
            exact costHeaderBody_noRand

end MinCostFlow.Scaling.Machine
