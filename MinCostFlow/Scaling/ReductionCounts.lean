module

public import MinCostFlow.Scaling.ReductionAlgorithm
public import MinCostFlow.Scaling.CallLoop

/-!
# The general-flow reduction's call trace

The reduction used in Lemma C.1 of Chen et al., arXiv:2203.00671v2, first
checks capacities, then makes one feasibility call and at most one residual
optimization call. The model below executes these calls and records their
instances. The work counter reserves the edge and vertex scans separately:
capacity checks, table initialization, shifted demands, graph assembly,
artificial arcs, residual arcs, and final flow reconstruction. It counts
integer operations, rather than word-RAM steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- Static upper budget for the reduction's non-solver scans. The seven terms
reserve respectively capacity checks, initialization, lower-demand updates,
base graph assembly, demand arcs, residual arcs, and reconstruction. -/
def reductionWork (I : Instance) : ℕ :=
  I.m + 2 * I.n + 11 * I.m + 6 * I.m + 8 * I.n + 12 * I.m + 6 * I.m

/-- Execute the two-call reduction while retaining its full solver-call trace.
An infeasible input can stop after zero calls or after the feasibility call. -/
def reduceWithTrace (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) : CallResult (Option (Fin I.m → ℤ)) :=
  if ∀ e, (I.edge e).lower ≤ (I.edge e).upper then
    let J := shiftedGraph I hv
    let P := buildFeasibilityInstance I hv
    let g := solve P
    if P.integerObjective g = -(J.demandMass (shiftedDemand I) : ℤ) then
      let f : Fin I.m → ℤ := fun e => g (Fin.castAdd (I.n + I.n) e)
      let R := J.residual f
      let h := solve R
      ⟨some (fun e => (I.edge e).lower + f e +
        h (Fin.castAdd I.m e) - h (Fin.natAdd I.m e)), [P, R], reductionWork I⟩
    else ⟨none, [P], reductionWork I⟩
  else ⟨none, [], I.m⟩

/-- Recording the solver calls leaves the reduction's output unchanged. -/
theorem reduceWithTrace_value (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    (reduceWithTrace solve I hv).value = reduceToCirculation solve I hv := by
  unfold reduceWithTrace reduceToCirculation
  split
  · dsimp only
    split <;> rfl
  · rfl

/-- The reduction makes at most two solver calls. -/
theorem reduceWithTrace_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    (reduceWithTrace solve I hv).calls.length ≤ 2 := by
  unfold reduceWithTrace
  split
  · dsimp only
    split <;> simp
  · simp

/-- Every call has at most `max (m+2*n) (2*m)` edge slots. -/
theorem reduceWithTrace_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    ∀ J ∈ (reduceWithTrace solve I hv).calls, J.m ≤ max (I.m + 2 * I.n) (2 * I.m) := by
  unfold reduceWithTrace
  split
  · dsimp only
    split
    · intro J hJ
      rcases List.mem_cons.mp hJ with h | h
      · subst J
        exact le_trans (by change I.m + (I.n + I.n) ≤ I.m + 2 * I.n; omega) (le_max_left _ _)
      · have he := List.mem_singleton.mp h
        subst J
        exact le_trans (by change I.m + I.m ≤ 2 * I.m; omega) (le_max_right _ _)
    · intro J hJ
      have he := List.mem_singleton.mp hJ
      subst J
      exact le_trans (by change I.m + (I.n + I.n) ≤ I.m + 2 * I.n; omega) (le_max_left _ _)
  · simp

/-- In a graph with `n <= 2*m`, all calls have at most five times the original
edge count. This is the concrete constant used after vertex preprocessing. -/
theorem reduceWithTrace_edges_le_five (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (hn : I.n ≤ 2 * I.m) :
    ∀ J ∈ (reduceWithTrace solve I hv).calls, J.m ≤ 5 * I.m := by
  intro J hJ
  have h := reduceWithTrace_edges solve I hv J hJ
  have hleft : I.m + 2 * I.n ≤ 5 * I.m := by omega
  have hright : 2 * I.m ≤ 5 * I.m := by omega
  exact le_trans h (max_le hleft hright)

/-- The reserved other-work budget is at most `36*m+10*n`. -/
theorem reduceWithTrace_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) :
    (reduceWithTrace solve I hv).work ≤ 36 * I.m + 10 * I.n := by
  unfold reduceWithTrace
  split
  · dsimp only
    split <;> dsimp only [reductionWork] <;> omega
  · dsimp only
    omega

end MinCostFlow.Scaling.FlowReduction
