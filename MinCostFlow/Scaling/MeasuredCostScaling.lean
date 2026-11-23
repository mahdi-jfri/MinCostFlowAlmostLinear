module

public import MinCostFlow.Scaling.CostScalingModel
public import MinCostFlow.Scaling.CallExpansion

/-!
# Cost scaling with counted solver procedures

To compose the two reductions of Appendix C of Chen et al.,
arXiv:2203.00671v2, a cost-scaling solver call must be implemented by the
capacity-scaling procedure. The functions here invoke a counted solver once
per call and retain its returned trace and work. They compute the same integer
states as the plain cost model. The substitution lemmas therefore transfer
its trace bounds to the composed procedure without assuming a stronger solver.
-/

@[expose] public section
namespace MinCostFlow.Scaling
namespace Circulation

/-- Invoke a counted procedure on the positive-capacity representation.
Its input assembly and zero-slot erasure are charged by the enclosing routine. -/
def invokePositive
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) :
    CallResult (Fin I.m → ℤ) :=
  let r := inner I.positiveInstance
  ⟨(fun e => if I.capacity e = 0 then 0 else r.value e), r.calls, r.work⟩

/-- The counted invocation has the value of the plain one-call adapter. -/
theorem invokePositive_value
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) :
    (invokePositive inner I).value = solveWithZeroCapacities (fun J => (inner J).value) I := rfl

/-- Dual extraction invoking the counted procedure, not just its output function. -/
def extractDualMeasured
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) (f : Fin I.m → ℤ) : CallResult (Fin I.n → ℤ) :=
  let R := I.residual f
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let call := invokePositive inner Q
  let routing : Fin S.m → ℤ := fun e => start e +
    call.value (Fin.castAdd S.m e) - call.value (Fin.natAdd S.m e)
  let labels := S.propagateLabels routing (Fin.last I.n)
  ⟨(fun v => labels.1.labels v.castSucc), call.calls,
    100 * (I.m + I.n + 1) + labels.2 + call.work⟩

/-- Counted dual extraction computes exactly the plain model's potential. -/
theorem extractDualMeasured_value
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) (f : Fin I.m → ℤ) :
    (extractDualMeasured inner I f).value =
      (extractDualModel (fun J => (inner J).value) I f).value := rfl

/-- Its trace is the expansion of the plain one-call trace. -/
theorem extractDualMeasured_calls
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) (f : Fin I.m → ℤ) :
    (extractDualMeasured inner I f).calls =
      (CallResult.expand inner (extractDualModel (fun J => (inner J).value) I f)).calls := by
  simp only [extractDualMeasured, invokePositive, extractDualModel, CallResult.expand,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Circulation.solveWithZeroCapacities]

/-- Its counter adds the called procedure's counter to the plain local work. -/
theorem extractDualMeasured_work
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) (f : Fin I.m → ℤ) :
    (extractDualMeasured inner I f).work =
      (CallResult.expand inner (extractDualModel (fun J => (inner J).value) I f)).work := by
  simp only [extractDualMeasured, invokePositive, extractDualModel, CallResult.expand,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Circulation.solveWithZeroCapacities]

end Circulation
namespace CostState

/-- One integer cost round with the two procedure calls evaluated and counted. -/
def stepMeasured
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (C : ℕ)
    {I : Circulation} (s : CostState I) : CallResult (CostState I) :=
  let J := s.roundedInstance C
  let primal := J.invokePositive inner
  let dual := J.extractDualMeasured inner primal.value
  { value :=
      { flow := fun e => s.flow e + primal.value (Fin.castAdd I.m e) -
          primal.value (Fin.natAdd I.m e)
        potential := fun v => 2 * (s.potential v + dual.value v)
        power := 2 * s.power }
    calls := primal.calls ++ dual.calls
    work := 80 * (I.m + I.n + 1) + primal.work + dual.work }

/-- Replacing the output function by counted calls leaves the next state unchanged. -/
theorem stepMeasured_value
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    (stepMeasured inner C s).value = (step (fun J => (inner J).value) C s).value := rfl

/-- The two measured calls expand exactly the two plain solver inputs. -/
theorem stepMeasured_calls
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    (stepMeasured inner C s).calls =
      (CallResult.expand inner (step (fun J => (inner J).value) C s)).calls := by
  simp only [stepMeasured, step, Circulation.extractDualMeasured, Circulation.extractDualModel,
    Circulation.invokePositive, CallResult.expand, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Circulation.solveWithZeroCapacities]

/-- Local work and the two called procedures' work add exactly as in trace expansion. -/
theorem stepMeasured_work
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    (stepMeasured inner C s).work =
      (CallResult.expand inner (step (fun J => (inner J).value) C s)).work := by
  simp only [stepMeasured, step, Circulation.extractDualMeasured, Circulation.extractDualModel,
    Circulation.invokePositive, CallResult.expand, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Circulation.solveWithZeroCapacities]
  omega

end CostState

/-- The finite cost loop using a counted solver procedure at every invocation. -/
def costLoopMeasured
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    CallResult (CostState I) :=
  CallResult.forRounds (CostState.stepMeasured inner C) (costRounds I.n C) (CostState.initial I)

/-- The measured loop computes the same final integer state. -/
theorem costLoopMeasured_value
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costLoopMeasured inner I C).value =
      (costLoop (fun J => (inner J).value) I C).value :=
  CallResult.forRounds_value_eq _ _ (CostState.stepMeasured_value inner C) _ _

/-- The measured loop expands the plain trace using the called procedure's trace. -/
theorem costLoopMeasured_calls
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costLoopMeasured inner I C).calls =
      (CallResult.expand inner (costLoop (fun J => (inner J).value) I C)).calls :=
  CallResult.forRounds_calls_expand inner _ _ (CostState.stepMeasured_value inner C)
    (CostState.stepMeasured_calls inner C) _ _

/-- The measured loop expands all inner work counters as well. -/
theorem costLoopMeasured_work
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costLoopMeasured inner I C).work =
      (CallResult.expand inner (costLoop (fun J => (inner J).value) I C)).work :=
  CallResult.forRounds_work_expand inner _ _ (CostState.stepMeasured_value inner C)
    (CostState.stepMeasured_work inner C) _ _

/-- The complete cost model with actual calls to a counted inner solver. -/
def costScalingMeasured
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    CallResult (Fin I.m → ℤ) :=
  if I.m = 0 then ⟨fun _ => 0, [], 1⟩
  else
    let J := I.compress
    let prep := I.n + 20 * I.m + 1
    if C ≤ I.m ^ 10 then
      let r := J.invokePositive inner
      ⟨r.value, r.calls, prep + 10 * (I.m + 1) + r.work⟩
    else
      let r := costLoopMeasured inner J C
      ⟨r.value.flow, r.calls, prep + r.work⟩

/-- The complete measured function has the output of the plain cost model. -/
theorem costScalingMeasured_value
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costScalingMeasured inner I C).value =
      (costScalingModel (fun J => (inner J).value) I C).value := by
  unfold costScalingMeasured costScalingModel
  split
  · rfl
  · dsimp only
    split
    · rfl
    · dsimp only
      rw [costLoopMeasured_value]

/-- The full trace is exactly the expansion of the plain cost-scaling trace. -/
theorem costScalingMeasured_calls
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costScalingMeasured inner I C).calls =
      (CallResult.expand inner (costScalingModel (fun J => (inner J).value) I C)).calls := by
  unfold costScalingMeasured costScalingModel
  split
  · rfl
  · dsimp only
    split
    · simp only [Circulation.invokePositive, CallResult.expand, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Circulation.solveWithZeroCapacities]
    · exact costLoopMeasured_calls inner I.compress C

/-- The full counter adds the local cost-model work and every invoked inner counter. -/
theorem costScalingMeasured_work
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ)) (I : Circulation) (C : ℕ) :
    (costScalingMeasured inner I C).work =
      (CallResult.expand inner (costScalingModel (fun J => (inner J).value) I C)).work := by
  unfold costScalingMeasured costScalingModel
  split
  · rfl
  · dsimp only
    split
    · simp only [Circulation.invokePositive, CallResult.expand, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Circulation.solveWithZeroCapacities]
    · dsimp only
      rw [costLoopMeasured_work]
      simp only [CallResult.expand]
      omega

end MinCostFlow.Scaling
