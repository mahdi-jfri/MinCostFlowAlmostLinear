module

public import MinCostFlow.Scaling.CapacityScalingModel
public import MinCostFlow.Scaling.CompressionProgram
public import MinCostFlow.Scaling.CapacityLoopContract
public import MinCostFlow.Scaling.CapacityFlowCopyProgram

/-!
# The complete capacity-scaling machine interface

The counted model first removes unused vertex names, executes its capacity
loop, and returns the resulting integral flow. The machine follows these
steps and copies the state's coordinates into the final output array.
The empty graph needs no allocation. The uniform reserve uses original
dimensions, so the caller need not inspect the compressed graph.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,capacityBound,heap]`. -/
def capacityScalingBody (compression loop copy : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (.ret (.reg 2))
    (.call 4 compression [.reg 0,.reg 2] ;;
     .call 5 loop [.reg 2,.reg 1,.reg 4] ;;
     .assign 6 (.bin .sub (.reg 5) (.const 2)) ;;
     .call 7 copy [.reg 6,.reg 3,.reg 5] ;;
     .ret (.reg 7))

/-- Compression, the complete loop, and output copying at consecutive entries. -/
def capacityScalingModule (solver : Program) (entry b : ℕ) : List Stmt :=
  capacityScalingBody (b+1) (b+7) (b+7+(capacityLoopModule solver entry (b+7)).length) ::
    (compressionModule (b+1) ++ capacityLoopModule solver entry (b+7) ++
      capacityFlowCopyModule (b+7+(capacityLoopModule solver entry (b+7)).length))

/-- Original dimensions bound compression scratch, loop space, and the final array. -/
def capacityScalingSpace (J : Circulation) (C U : ℕ) : ℕ :=
  J.solverWords.length+J.n+2+J.m+2+
    (capacityRounds J.m U+1)*(capacityStepNumberBase J C U)^256+J.m

/-- Exact capacity-model output in the last `m` returned words, with the
actual primitive-call term and a linear charge to the model work. -/
noncomputable def capacityScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := capacityScalingModel (canonicalSolver solver entry T hproc) J U
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      ZeroFrom mem heap ∧ heap+capacityScalingSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+capacityScalingSpace J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+1) (J.m+J.m))+
      102000*(solver.regBound+1)*r.work }

/-- The complete capacity-scaling program is deterministic. -/
theorem capacityScalingModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ capacityScalingModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hc
    · rcases List.mem_append.mp hb with hc | hl
      · exact compressionModule_noRand _ body hc
      · exact capacityLoopModule_noRand solver entry _ hdet body hl
    · exact capacityFlowCopyModule_noRand _ body hc

end MinCostFlow.Scaling.Machine
