module

public import MinCostFlow.Scaling.ReductionCounts
public import MinCostFlow.Scaling.IsolatedDemands
public import MinCostFlow.Scaling.PositiveScatter

/-!
# Bounded-size calls for the general-flow reduction

For the reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2, first reject
nonzero demands at isolated vertices. Each subsequent solver call filters out
zero-capacity arcs and restores returned coordinates with the integer scatter
loop. The feasibility call has at most `3*m` edges and the residual call has at
most `2*m` edges, even when the input has many isolated vertices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- With the isolated-demand check satisfied, pruning every instance in the
reduction's trace leaves at most `3*m` edges per call. -/
theorem reduceWithTrace_pruned_edges
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Instance) (hv : I.IsValid)
    (hcheck : isolatedCheck I hv = true) :
    ∀ J ∈ (reduceWithTrace solve I hv).calls, J.withoutZeroEdges.m ≤ 3 * I.m := by
  unfold reduceWithTrace
  split
  · dsimp only
    split
    · intro J hJ
      rcases List.mem_cons.mp hJ with hJ | hJ
      · subst J
        change ((shiftedGraph I hv).demandInstance (buildShiftedDemands I hv)).positiveEdges.length ≤ _
        rw [buildShiftedDemands_eq]
        exact feasibilityInstance_positiveEdges_le_three I hv hcheck
      · have he := List.mem_singleton.mp hJ
        subst J
        apply le_trans (Circulation.positiveEdges_length_le _)
        change I.m + I.m ≤ 3 * I.m
        omega
    · intro J hJ
      have he := List.mem_singleton.mp hJ
      subst J
      change ((shiftedGraph I hv).demandInstance (buildShiftedDemands I hv)).positiveEdges.length ≤ _
      rw [buildShiftedDemands_eq]
      exact feasibilityInstance_positiveEdges_le_three I hv hcheck
  · simp

/-- Execute the isolated-demand check, then the reduction with one pruned
solver invocation for each recorded call. The extra counter reserves the
initial endpoint and isolated-demand scans plus pruning and scatter restoration. -/
def checkedReduction (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) : CallResult (Option (Fin I.m → ℤ)) :=
  if isolatedCheck I hv then
    let r := reduceWithTrace (Circulation.solvePruned solve) I hv
    ⟨r.value, r.calls.map Circulation.withoutZeroEdges, r.work + 44 * (I.m + I.n)⟩
  else ⟨none, [], 44 * (I.m + I.n)⟩

/-- The checked and pruned reduction still returns an integral exact optimum
or proves that no feasible real flow exists. -/
theorem checkedReduction_correct (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.Optimal (fun e => (solve J e : ℝ)))
    (I : Instance) (hv : I.IsValid) :
    (∀ f, (checkedReduction solve I hv).value = some f →
      I.IsMinCostFlow (fun e => (f e : ℝ))) ∧
    ((checkedReduction solve I hv).value = none → ∀ f, ¬ I.IsFeasible f) := by
  by_cases hcheck : isolatedCheck I hv = true
  · simp only [checkedReduction, hcheck, ↓reduceIte, reduceWithTrace_value]
    exact reduceToCirculation_correct (Circulation.solvePruned solve)
      (Circulation.solvePruned_correct solve hsolve) I hv
  · have hf : isolatedCheck I hv = false := Bool.eq_false_iff.mpr hcheck
    simp only [checkedReduction, hf, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro f h
      cases h
    · intro _
      exact infeasible_of_isolatedCheck I hv hf

/-- There are at most two calls to the supplied solver. -/
theorem checkedReduction_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    (checkedReduction solve I hv).calls.length ≤ 2 := by
  unfold checkedReduction
  split
  · dsimp only
    rw [List.length_map]
    exact reduceWithTrace_calls _ I hv
  · simp

/-- Every supplied-solver call has at most three times the original edge count.
This bound needs no relation between the input's vertex and edge counts. -/
theorem checkedReduction_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    ∀ J ∈ (checkedReduction solve I hv).calls, J.m ≤ 3 * I.m := by
  unfold checkedReduction
  split
  · intro J hJ
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hJ
    exact reduceWithTrace_pruned_edges _ I hv ‹_› K hK
  · simp

/-- All supplied-solver inputs have strictly positive capacities. -/
theorem checkedReduction_positive_capacities
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Instance) (hv : I.IsValid) :
    ∀ J ∈ (checkedReduction solve I hv).calls, ∀ e, 0 < J.capacity e := by
  unfold checkedReduction
  split
  · intro J hJ e
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hJ
    exact (K.mem_positiveEdges_iff _).mp (List.getElem_mem e.isLt)
  · simp

/-- The other-work counter is at most `80*(m+n)`. The machine-program round
must implement these integer/table operations and count their word costs. -/
theorem checkedReduction_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    (checkedReduction solve I hv).work ≤ 80 * (I.m + I.n) := by
  unfold checkedReduction
  split
  · dsimp only
    have h := reduceWithTrace_work (Circulation.solvePruned solve) I hv
    omega
  · dsimp only
    omega

end MinCostFlow.Scaling.FlowReduction
