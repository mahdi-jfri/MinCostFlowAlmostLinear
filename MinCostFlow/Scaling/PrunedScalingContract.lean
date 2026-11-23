module

public import MinCostFlow.Scaling.CostCapacityContract
public import MinCostFlow.Scaling.PositivePruneProgram
public import MinCostFlow.Scaling.UnsignedFlowTableProgram
public import MinCostFlow.Scaling.RestoreScatterProgram
public import MinCostFlow.Scaling.MeasuredReduction

/-!
# The pruned circulation-scaling entry

The outer reduction removes zero-capacity edges before each composed
scaling call. Keep the saved indices beside the compacted graph, convert
the returned unsigned flow to signed pairs, and scatter those pairs into
a fresh zero table of the original dimension. The contract refers to the
exact counted pruning adapter used by the general-flow model.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,C,U,heap]`. -/
def prunedScalingBody (prune scaling convert restore : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 prune [.reg 0,.reg 3] ;;
  .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .call 7 scaling [.reg 3,.reg 1,.reg 2,.reg 5] ;;
  .call 8 convert [.bin .sub (.reg 7) (.reg 6),.reg 6,.reg 7] ;;
  .call 9 restore [.bin .add (.bin .add (.reg 3) (.const 2))
      (.bin .mul (.const 5) (.reg 4)),.reg 7,.reg 6,.reg 4,.reg 8] ;;
  .ret (.reg 9)

/-- Pruning, full cost-capacity scaling, conversion, and scatter. -/
def prunedScalingModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let scale := b+4
  let convert := scale+(costCapacityModule solver entry scale).length
  let restore := convert+2
  prunedScalingBody (b+1) scale convert restore ::
    (positivePruneModule (b+1) ++ (costCapacityModule solver entry scale ++
      (unsignedFlowModule convert ++ restoreScatterModule restore)))

/-- Space for compaction, the exact nested solver, conversion, and scatter. -/
def prunedScalingSpace (J : Circulation) (C U : ℕ) : ℕ :=
  2+6*J.m+costScalingSpace J.withoutZeroEdges C (max U (2*J.withoutZeroEdges.m+1))+
    2*J.withoutZeroEdges.m+2*J.m

/-- Exact pruning-adapter output in a signed table occupying the final
`2*m` returned cells. The solver receives only the compacted graph. -/
noncomputable def prunedScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract :=
  let inner := fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C U
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ 8<2^w ∧
      J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 1≤U ∧
      ZeroFrom mem heap ∧ heap+prunedScalingSpace J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+prunedScalingSpace J C U ∧
      SignedTableAt mem' (ret-2*J.m) (Circulation.invokePruned inner J).value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (costCapacityContract w solver entry T hproc J.withoutZeroEdges C U).cost [] (fun _ => 0)+
      1000*J.m+1000 }

/-- The pruned entry contains no random instruction when its solver does not. -/
theorem prunedScalingModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈prunedScalingModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [prunedScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact positivePruneModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact costCapacityModule_noRand solver entry _ hdet body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact unsignedFlowModule_noRand _ body hb
        · exact restoreScatterModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
