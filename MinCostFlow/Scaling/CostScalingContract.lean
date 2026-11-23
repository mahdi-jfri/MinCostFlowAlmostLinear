module

public import MinCostFlow.Scaling.MeasuredCostScaling
public import MinCostFlow.Scaling.CompressionProgram
public import MinCostFlow.Scaling.CostPolynomialProgram
public import MinCostFlow.Scaling.CapacityPositiveContract
public import MinCostFlow.Scaling.CostLoopContract
public import MinCostFlow.Scaling.CostFlowCopyProgram

/-!
# The complete measured cost-scaling machine interface

Handle the empty graph directly. Otherwise compress vertex names, compare
`C` with the model's threshold `m^10`, and either invoke the positive
capacity model directly or run the complete measured cost loop. The loop
branch copies its final state flow into the shared solver-output layout.
This is exactly `costScalingMeasured` with the capacity model as its inner
procedure. Its capacity bound covers the compressed routing vertices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,costBound,capacityBound,heap]`. -/
def costScalingBody (compress polynomial positive loop copy : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.reg 3))
    (.call 5 compress [.reg 0,.reg 3] ;;
     .call 6 polynomial [.reg 4] ;;
     .cond (.bin .lt (.reg 6) (.reg 1))
       (.call 7 loop [.reg 3,.reg 1,.reg 2,.reg 5] ;;
        .assign 8 (.bin .sub (.reg 7) (.const 3)) ;;
        .call 9 copy [.reg 8,.reg 4,.reg 7] ;;
        .ret (.reg 9))
       (.call 7 positive [.reg 3,.reg 2,.reg 5] ;; .ret (.reg 7)))

/-- Compression, threshold, both exact solver branches, and flow copying. -/
def costScalingModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let positive := b+8
  let loop := positive+(capacityPositiveModule solver entry positive).length
  let copy := loop+(costLoopModule solver entry loop).length
  costScalingBody (b+1) (b+7) positive loop copy ::
    (compressionModule (b+1) ++ costPolynomialModule ++ capacityPositiveModule solver entry positive ++
      costLoopModule solver entry loop ++ costFlowCopyModule copy)

/-- Original dimensions cover compression scratch, either branch, and
one final flow array, including a spare per-round numerical margin. -/
def costScalingSpace (J : Circulation) (C U : ℕ) : ℕ :=
  J.solverWords.length+J.n+2+J.m+2*J.n+3+
    (costRounds J.n C+2)*(costStepNumberBase J C U)^524+J.m+3

/-- Exact measured cost-model flow in the final `m` returned words, with
the actual primitive-call term and model work charged for all branches. -/
noncomputable def costScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := costScalingMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) J C
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 2*J.m+1≤U ∧
      ZeroFrom mem heap ∧ heap+costScalingSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+costScalingSpace J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))+
      302000*(solver.regBound+1)*r.work }

/-- Every cost-scaling branch and all nested calls are deterministic. -/
theorem costScalingModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ costScalingModule solver entry b,body.NoRand := by
  intro body hb
  simp only [costScalingModule,List.mem_cons,List.mem_append,or_assoc] at hb
  rcases hb with rfl | hc | hp | hs | hl | hf
  · simp only [costScalingBody,Stmt.NoRand,and_self]
  · exact compressionModule_noRand _ body hc
  · have heq : body=costPolynomialBody := List.mem_singleton.mp hp
    subst body
    exact costPolynomialBody_noRand
  · exact capacityPositiveModule_noRand solver entry _ hdet body hs
  · exact costLoopModule_noRand solver entry _ hdet body hl
  · exact costFlowCopyModule_noRand _ body hf

end MinCostFlow.Scaling.Machine
