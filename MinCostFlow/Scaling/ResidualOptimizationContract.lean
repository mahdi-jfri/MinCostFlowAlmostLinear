module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
public import MinCostFlow.Scaling.ResidualProgram
public import MinCostFlow.Scaling.ResidualAugmentProgram
public import MinCostFlow.Scaling.LowerRestoreProgram

/-!
# The residual optimization phase of the outer reduction

After the feasibility phase succeeds, build the shifted flow's residual
circulation and solve it by the exact pruned scaling procedure. Convert
its nonnegative correction to unsigned words, apply forward-minus-reverse
augmentation, and restore the original lower capacities in canonical
signed pairs. All source arrays remain below the fresh output region.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[input,shiftedGraph,shiftedFlow,C,U,heap]`. -/
def residualOptimizationBody (residual solve copy augment restore : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 7 residual [.reg 1,.reg 2,.reg 5] ;;
  .assign 8 (.bin .add (.bin .mul (.bin .mul (.const 2)
      (.bin .add (.reg 6) (.const 1))) (.reg 4)) (.const 1)) ;;
  .call 9 solve [.reg 5,.reg 3,.reg 8,.reg 7] ;;
  .assign 10 (.bin .add (.reg 6) (.reg 6)) ;;
  .call 11 copy [.bin .sub (.reg 9) (.bin .mul (.const 2) (.reg 10)),.reg 10,.reg 9] ;;
  .call 12 augment [.reg 2,.reg 9,.reg 6,.reg 11] ;;
  .call 13 restore [.bin .add (.reg 0) (.const 2),.reg 11,.reg 6,.reg 12] ;;
  .ret (.reg 13)

/-- Residual construction, full pruned scaling, conversion, augmentation,
and lower-capacity restoration. -/
def residualOptimizationModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let solve := b+1+(residualModule (b+1)).length
  let copy := solve+(prunedScalingModule solver entry solve).length
  let augment := copy+1
  let restore := augment+(residualAugmentModule augment).length
  residualOptimizationBody (b+1) solve copy augment restore ::
    (residualModule (b+1) ++ (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (residualAugmentModule augment ++ lowerRestoreModule restore))))

/-- Reserve for the residual graph, exact nested solver, unsigned
correction, augmented shifted flow, and final signed output. -/
def residualOptimizationSpace (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ) : ℕ :=
  let R := (FlowReduction.shiftedGraph I hv).residual f
  2+15*I.m+prunedScalingSpace R C (FlowReduction.scalingCapacityBudget I U)

/-- Exact successful second-call output in the original edge order.
The preconditions constrain only stored input data and arithmetic bounds. -/
noncomputable def residualOptimizationContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ) : Contract :=
  let J := FlowReduction.shiftedGraph I hv
  let R := J.residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let delta := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) R).value
  { pre := fun args mem => ∃ a graph flow heap,args=[a,graph,flow,C,U,heap] ∧
      ListAt mem a I.encode ∧ ListAt mem graph J.solverWords ∧
      ListAt mem flow (List.ofFn (fun e => (f e).toNat)) ∧
      a+I.encode.length≤heap ∧ graph+J.solverWords.length≤heap ∧ flow+I.m≤heap ∧
      (∀ e,0≤f e ∧ f e≤(J.capacity e : ℤ)) ∧
      (∀ e,(I.edge e).cost.natAbs≤C) ∧
      (∀ e,(I.edge e).lower.natAbs≤U) ∧ (∀ e,(I.edge e).upper.natAbs≤U) ∧
      (∀ x∈I.encode,x<2^w) ∧ (∀ x∈J.solverWords,x<2^w) ∧ (∀ x∈R.solverWords,x<2^w) ∧
      8<2^w ∧ B<2^w ∧ 4*U<2^w ∧ ZeroFrom mem heap ∧
      heap+residualOptimizationSpace I hv f C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+residualOptimizationSpace I hv f C U ∧
      SignedTableAt mem' (ret-2*I.m) (fun e =>
        (I.edge e).lower+f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (prunedScalingContract w solver entry T hproc R C B).cost [] (fun _ => 0)+
      2000*I.m+1000 }

/-- The complete residual optimization phase contains no random
instruction when its supplied bounded solver does not. -/
theorem residualOptimizationModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈residualOptimizationModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [residualOptimizationBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact residualModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact prunedScalingModule_noRand solver entry _ hdet body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact magnitudeCopyModule_noRand _ body hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact residualAugmentModule_noRand _ body hb
          · exact lowerRestoreModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
