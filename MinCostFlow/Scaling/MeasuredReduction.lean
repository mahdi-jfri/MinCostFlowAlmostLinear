module

public import MinCostFlow.Scaling.CheckedReduction
public import MinCostFlow.Scaling.CallExpansion

/-!
# General-flow reduction with counted circulation calls

The general-flow reduction used in Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, makes its feasibility call before deciding whether to
make the optimization call. These functions execute counted inner procedures
in that order. Pruning and scatter restoration use the same integer loops as
the plain reduction. The trace and work identities justify nested counts.
-/

@[expose] public section
namespace MinCostFlow.Scaling
namespace Circulation

/-- Invoke a counted circulation procedure after pruning zero-capacity edges. -/
def invokePruned (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) : CallResult (Fin I.m → ℤ) :=
  let r := inner I.withoutZeroEdges
  ⟨I.scatterPositive r.value, r.calls, r.work⟩

/-- The counted adapter returns the plain pruning adapter's output. -/
theorem invokePruned_value (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Circulation) :
    (invokePruned inner I).value = solvePruned (fun J => (inner J).value) I := rfl

end Circulation
namespace FlowReduction

/-- Execute the feasibility call and then, on success, the residual call,
retaining their traces and counters. The enclosing checked routine charges
pruning and scatter work. -/
def reduceMeasured (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) : CallResult (Option (Fin I.m → ℤ)) :=
  if ∀ e, (I.edge e).lower ≤ (I.edge e).upper then
    let J := shiftedGraph I hv
    let P := buildFeasibilityInstance I hv
    let g := inner P
    if P.integerObjective g.value = -(J.demandMass (shiftedDemand I) : ℤ) then
      let f : Fin I.m → ℤ := fun e => g.value (Fin.castAdd (I.n + I.n) e)
      let h := inner (J.residual f)
      ⟨some (fun e => (I.edge e).lower + f e +
        h.value (Fin.castAdd I.m e) - h.value (Fin.natAdd I.m e)),
        g.calls ++ h.calls, reductionWork I + g.work + h.work⟩
    else ⟨none, g.calls, reductionWork I + g.work⟩
  else ⟨none, [], I.m⟩

/-- Counted reduction preserves the plain output, including infeasibility. -/
theorem reduceMeasured_value (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (reduceMeasured inner I hv).value =
      (reduceWithTrace (fun J => (inner J).value) I hv).value := by
  unfold reduceMeasured reduceWithTrace
  split
  · dsimp only
    split <;> rfl
  · rfl

/-- The counted two-call routine expands the plain call trace. -/
theorem reduceMeasured_calls (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (reduceMeasured inner I hv).calls =
      (CallResult.expand inner (reduceWithTrace (fun J => (inner J).value) I hv)).calls := by
  unfold reduceMeasured reduceWithTrace
  split
  · dsimp only
    split <;> simp only [CallResult.expand, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · rfl

/-- The counted routine adds exactly the counters of the calls it executes. -/
theorem reduceMeasured_work (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (reduceMeasured inner I hv).work =
      (CallResult.expand inner (reduceWithTrace (fun J => (inner J).value) I hv)).work := by
  unfold reduceMeasured reduceWithTrace
  split
  · dsimp only
    split <;> simp only [CallResult.expand, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  · simp only [CallResult.expand, List.map_nil, List.sum_nil, Nat.add_zero]

/-- Check isolated demands, then run the counted reduction with pruned calls. -/
def checkedMeasured (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) : CallResult (Option (Fin I.m → ℤ)) :=
  if isolatedCheck I hv then
    let r := reduceMeasured (Circulation.invokePruned inner) I hv
    ⟨r.value, r.calls, r.work + 44 * (I.m + I.n)⟩
  else ⟨none, [], 44 * (I.m + I.n)⟩

/-- The checked counted routine returns the same answer as its plain version. -/
theorem checkedMeasured_value (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (checkedMeasured inner I hv).value =
      (checkedReduction (fun J => (inner J).value) I hv).value := by
  unfold checkedMeasured checkedReduction
  split
  · exact reduceMeasured_value _ I hv
  · rfl

/-- The checked trace expands precisely the pruned calls of the plain routine. -/
theorem checkedMeasured_calls (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (checkedMeasured inner I hv).calls =
      (CallResult.expand inner (checkedReduction (fun J => (inner J).value) I hv)).calls := by
  unfold checkedMeasured checkedReduction
  split
  · dsimp only
    rw [reduceMeasured_calls]
    simp only [CallResult.expand, Circulation.invokePruned, List.flatMap_map]
    rfl
  · rfl

/-- The checked work counter adds every invoked inner counter once. -/
theorem checkedMeasured_work (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (I : Instance) (hv : I.IsValid) :
    (checkedMeasured inner I hv).work =
      (CallResult.expand inner (checkedReduction (fun J => (inner J).value) I hv)).work := by
  unfold checkedMeasured checkedReduction
  split
  · dsimp only
    rw [reduceMeasured_work]
    simp only [CallResult.expand, Circulation.invokePruned, List.map_map, Function.comp_def ]
    ac_rfl
  · simp only [CallResult.expand, List.map_nil, List.sum_nil, Nat.add_zero]

end FlowReduction
end MinCostFlow.Scaling
