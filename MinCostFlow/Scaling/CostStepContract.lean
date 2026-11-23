module

public import MinCostFlow.Scaling.CostStateLayout
public import MinCostFlow.Scaling.BuildRoundedInstanceProgram
public import MinCostFlow.Scaling.CapacityPositiveContract
public import MinCostFlow.Scaling.CapacityExtractDualContract
public import MinCostFlow.Scaling.ResidualAugmentProgram
public import MinCostFlow.Scaling.PotentialUpdateProgram
public import MinCostFlow.Scaling.CostHeaderProgram

/-!
# One measured integer cost-scaling round

Construct the residual and rounded costs, invoke the full capacity model
for the primal correction and dual extraction, then update the flow,
potentials, and denominator power. Each call follows the measured model's
actual output. The numerical entry premises concern only input data and
arithmetic budgets. Feasibility of the called solver's output is proved
from the primitive solver contract rather than assumed here.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,state,costBound,capacityBound,heap]`. -/
def costStepBody (residual rounded primal dual augment potentials header : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.load (.reg 1)) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 9 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .call 10 residual [.reg 0,.reg 7,.reg 4] ;;
  .call 11 rounded [.reg 4,.reg 8,.reg 9,.bin .add (.reg 2) (.const 1),.reg 10] ;;
  .assign 12 (.bin .add (.reg 10) (.const 2)) ;;
  .call 13 primal [.reg 12,.reg 3,.reg 11] ;;
  .assign 14 (.bin .sub (.reg 13) (.bin .add (.reg 6) (.reg 6))) ;;
  .call 15 dual [.reg 12,.reg 14,.reg 3,.reg 13] ;;
  .assign 16 (.load (.reg 13)) ;;
  .call 17 augment [.reg 7,.reg 14,.reg 6,.reg 15] ;;
  .call 18 potentials [.reg 8,.reg 16,.reg 5,.reg 17] ;;
  .call 19 header [.bin .sub (.reg 17) (.reg 6),
    .bin .sub (.reg 18) (.bin .add (.reg 5) (.reg 5)),.bin .mul (.const 2) (.reg 9),.reg 18] ;;
  .ret (.reg 19)

/-- The complete round and its seven previously proved constituent modules. -/
def costStepModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let rounded := b+1+(residualModule (b+1)).length
  let primal := rounded+(buildRoundedInstanceModule rounded).length
  let dual := primal+(capacityPositiveModule solver entry primal).length
  let augment := dual+(capacityExtractDualModule solver entry dual).length
  let potentials := augment+(residualAugmentModule augment).length
  let header := potentials+(potentialUpdateScanModule potentials).length
  costStepBody (b+1) rounded primal dual augment potentials header ::
    (residualModule (b+1) ++ buildRoundedInstanceModule rounded ++
      capacityPositiveModule solver entry primal ++ capacityExtractDualModule solver entry dual ++
      residualAugmentModule augment ++ potentialUpdateScanModule potentials ++ costHeaderModule)

/-- Fresh residual and rounded graphs, the two exact inner calls, and
new flow, potential, and header storage. -/
noncomputable def costStepSpace (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    {J : Circulation} (s : CostState J) (C U : ℕ) : ℕ :=
  let K := s.roundedInstance C
  let B := J.m+J.m
  let delta := (K.invokePositive (fun L => capacityScalingModel (canonicalSolver solver entry T hproc) L U)).value
  2+10*J.m+(4+17*B)+capacityPositiveSpace K (B^10) U+
    capacityExtractDualSpace K delta (B^10) U+J.m+2*J.n+3

/-- Exact measured cost-round output in a three-word state header.
All additional entry conditions are finite data and arithmetic bounds. -/
noncomputable def costStepContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    {J : Circulation} (s : CostState J) (C U : ℕ) : Contract :=
  let K := s.roundedInstance C
  let B := J.m+J.m
  let delta := (K.invokePositive (fun L => capacityScalingModel (canonicalSolver solver entry T hproc) L U)).value
  let r := CostState.stepMeasured (fun L => capacityScalingModel (canonicalSolver solver entry T hproc) L U) C s
  { pre := fun args mem => ∃ a state heap,args=[a,state,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+3=heap ∧ CostStateAt mem state heap s ∧
      (∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ J.n+1≤U ∧ (∀ x∈J.solverWords,x<2^w) ∧
      J.n+B+U+B^10+2<2^w ∧ C+1<2^w ∧ 2*s.power<2^w ∧ 2*U<2^w ∧
      (4*J.m+J.n+1)*B^10<2^w ∧
      (∀ v,2*((s.potential v).natAbs+(4*J.m+J.n)*B^10)<2^w) ∧
      (∀ e,(roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem) ∧
      ZeroFrom mem heap ∧ heap+costStepSpace solver entry T hproc s C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+costStepSpace solver entry T hproc s C U ∧
      CostStateAt mem' (ret-3) ret r.value ∧ ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (capacityPositiveContract w solver entry T hproc K (B^10) U).cost [] (fun _ => 0)+
      (capacityExtractDualContract w solver entry T hproc K delta (B^10) U).cost [] (fun _ => 0)+
      5000*(J.m+J.n+1) }

/-- A cost round and every nested procedure are deterministic. -/
theorem costStepModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ costStepModule solver entry b,body.NoRand := by
  intro body hb
  simp only [costStepModule,List.mem_cons,List.mem_append,or_assoc] at hb
  rcases hb with rfl | hr | hb | hp | hd | ha | hu | hh
  · simp only [costStepBody,Stmt.NoRand,and_self]
  · exact residualModule_noRand _ body hr
  · exact buildRoundedInstanceModule_noRand _ body hb
  · exact capacityPositiveModule_noRand solver entry _ hdet body hp
  · exact capacityExtractDualModule_noRand solver entry _ hdet body hd
  · exact residualAugmentModule_noRand _ body ha
  · exact potentialUpdateScanModule_noRand _ body hu
  · have heq : body=costHeaderBody := List.mem_singleton.mp hh
    subst body
    exact costHeaderBody_noRand

end MinCostFlow.Scaling.Machine
