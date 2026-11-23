module

public import MinCostFlow.Scaling.CapacityStateLayout
public import MinCostFlow.Scaling.ResidualProgram
public import MinCostFlow.Scaling.PolyApproxContract
public import MinCostFlow.Scaling.CapacityRoundedSolveProgram
public import MinCostFlow.Scaling.ResidualAugmentProgram
import WordRAM.Logic

/-!
# One executable capacity-scaling iteration

A stopped state returns immediately. Otherwise construct the residual
circulation and its bottleneck approximation. Zero magnitude records the
stop flag. Positive magnitude invokes the rounded residual solve and
augments the current flow. Each active branch writes a fresh two-word
state header after its temporary data and new flow.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,state,heap]`; the state header ends at the heap. -/
def capacityStepBody (residual approx rounded augment pair : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .cond (.bin .eq (.reg 3) (.const 1)) (.ret (.reg 2))
    (.assign 4 (.load (.reg 1)) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .call 6 residual [.reg 0,.reg 4,.reg 2] ;;
     .call 7 approx [.reg 2,.reg 6] ;;
     .assign 8 (.load (.bin .sub (.reg 7) (.const 1))) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.call 13 pair [.reg 4,.const 1,.reg 7] ;; .ret (.reg 13))
       (.call 9 rounded [.reg 2,.reg 8,.reg 7] ;;
        .assign 10 (.bin .sub (.reg 9) (.bin .add (.reg 5) (.reg 5))) ;;
        .call 11 augment [.reg 4,.reg 10,.reg 5,.reg 9] ;;
        .call 13 pair [.bin .sub (.reg 11) (.reg 5),.const 0,.reg 11] ;;
        .ret (.reg 13)))

/-- Residual construction, approximation, rounded solving, augmentation,
and state-header writing follow the capacity-step entry. -/
def capacityStepModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let approx := b+1+(residualModule (b+1)).length
  let rounded := approx+(polyApproxModule solver entry approx).length
  let augment := rounded+(capacityRoundedSolveModule solver entry rounded).length
  let pair := augment+(residualAugmentModule augment).length
  capacityStepBody (b+1) approx rounded augment pair ::
    (residualModule (b+1) ++ polyApproxModule solver entry approx ++
      capacityRoundedSolveModule solver entry rounded ++ residualAugmentModule augment ++ wordPairModule)

/-- The complete approximation reserve, including its final four-cell margin. -/
def capacityApproxSpace (J : Circulation) : ℕ := bottleneckSearchSpace J+10+3*J.n+33*J.m+12

/-- Fresh-space reserve for a rounded solve at magnitude `B`. -/
def capacityRoundedSpace (J : Circulation) (B : ℕ) : ℕ :=
  if B=0 then J.m else 5+12*J.m+2^wordSize 5 (J.scaledRoundedInstance B).positiveInstance.solverWords

/-- One step's reserve includes both residual optimization phases and a
fresh flow and header, with four additional cells. -/
noncomputable def capacityStepSpace (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) : ℕ :=
  let R := J.residual s.flow
  let B := (polyApproxModel (canonicalSolver solver entry T hproc) R).value.magnitude
  2+10*J.m+capacityApproxSpace R+capacityRoundedSpace R B+J.m+2+4

/-- Numerical premises describe actual stored values and intermediate
arithmetic budgets. Feasibility of solver outputs is proved from the
primitive solver contract, rather than required as a premise. -/
noncomputable def capacityStepContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) : Contract :=
  let R := J.residual s.flow
  let B := (polyApproxModel (canonicalSolver solver entry T hproc) R).value.magnitude
  let G := bottleneckGuestBound R (sortCapacities (List.ofFn R.capacity)).1
  let g := wordSize 5 (R.scaledRoundedInstance B).positiveInstance.solverWords
  { pre := fun args mem => ∃ a state heap,args=[a,state,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+2=heap ∧ CapacityStateAt mem state heap s ∧
      (∀ x ∈ J.solverWords,x<2^w) ∧ (∀ x ∈ R.solverWords,x<2^w) ∧
      (∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ ZeroFrom mem heap ∧ heap+capacityStepSpace solver entry T hproc J s<2^w ∧
      R.m+2<2^w ∧ R.m*C<2^w ∧ 2^(G+1)+2≤2^w ∧ (6*R.m+2)*C<2^w ∧
      R.m*(C*U)<2^w ∧ B*R.m^20<2^w ∧ (B=0 ∨ 2^(g+1)+2≤2^w) ∧ 2*U<2^w ∧ 9<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+capacityStepSpace solver entry T hproc J s ∧
      CapacityStateAt mem' (ret-2) ret (s.step (canonicalSolver solver entry T hproc)).value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ mem => if s.stopped then 100 else
      600*J.m+200+(polyApproxContract w solver entry T hproc R C U).cost [] mem+
        if B=0 then 400 else (capacityRoundedSolveContract w solver entry T hproc R B).cost [] mem+100*J.m+100+400 }

/-- The step and all callees have no random instruction when the solver is deterministic. -/
theorem capacityStepModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityStepModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityStepBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hp
    · rcases List.mem_append.mp hb with hb | ha
      · rcases List.mem_append.mp hb with hb | hr
        · rcases List.mem_append.mp hb with he | hc
          · exact residualModule_noRand _ body he
          · exact polyApproxModule_noRand solver entry _ hdet body hc
        · exact capacityRoundedSolveModule_noRand solver entry _ hdet body hr
      · exact residualAugmentModule_noRand _ body ha
    · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hp
      subst body
      exact wordPairBody_noRand

end MinCostFlow.Scaling.Machine
