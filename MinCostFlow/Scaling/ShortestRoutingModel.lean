module

public import MinCostFlow.Scaling.LabelTraversal
public import MinCostFlow.Scaling.CallLoop
public import MinCostFlow.Scaling.SolverAdapter
public import MinCostFlow.Scaling.ResidualBounds

/-!
# Counted primal-to-dual extraction model

Lemma C.8 of Chen et al., arXiv:2203.00671v2, extracts shortest-path labels
from an optimal primal flow. Add a super-source with zero-cost arcs to all
vertices and route one unit directly to each vertex as an initial feasible
flow. One residual circulation solve optimizes this routing. Integer label
propagation then extracts the labels from its positive-flow support.

The routing capacities are `n+1`, so the model records this capacity increase
explicitly. This file gives the functions and their call/work bounds. The
shortest-path and dual correctness arguments are separate.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The uncapacitated shortest-routing instance, using capacity `n+1` as a
finite bound. Inactive original edge slots remain inactive. -/
abbrev shortestRoutingGraph (I : Circulation) : Circulation where
  n := I.n + 1
  m := I.m + I.n
  tail := Fin.addCases (fun e => (I.tail e).castSucc) (fun _ => Fin.last I.n)
  head := Fin.addCases (fun e => (I.head e).castSucc) (fun v => v.castSucc)
  capacity := Fin.addCases (fun e => if 0 < I.capacity e then I.n + 1 else 0)
    (fun _ => I.n + 1)
  cost := Fin.addCases I.cost (fun _ => 0)

/-- Route one unit directly from the super-source to each old vertex. -/
def shortestRoutingStart (I : Circulation) : Fin (I.m + I.n) → ℤ :=
  Fin.addCases (fun _ => 0) (fun _ => 1)

/-- The direct starting flow satisfies all capacity constraints. Its demands
are nonzero, which is why optimization uses a residual circulation. -/
theorem shortestRoutingStart_bounds (I : Circulation) :
    ∀ e, 0 ≤ (I.shortestRoutingStart e : ℝ) ∧
      (I.shortestRoutingStart e : ℝ) ≤ I.shortestRoutingGraph.capacity e := by
  intro e
  refine Fin.addCases (fun e => ?_) (fun v => ?_) e
  · simp only [shortestRoutingStart, Fin.addCases_left, Int.cast_zero]
    exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · simp only [shortestRoutingStart, Fin.addCases_right, Int.cast_one]
    constructor
    · exact zero_le_one
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le I.n)

/-- The finite routing capacity bound is explicit on every edge. -/
theorem shortestRoutingGraph_capacities (I : Circulation) :
    ∀ e, I.shortestRoutingGraph.capacity e ≤ I.n + 1 := by
  intro e
  refine Fin.addCases (fun e => ?_) (fun v => ?_) e
  · simp only [Fin.addCases_left]
    split
    · exact le_rfl
    · exact Nat.zero_le _
  · simp only [Fin.addCases_right]
    exact le_rfl

/-- Adding the zero-cost super-source arcs preserves every absolute cost bound. -/
theorem shortestRoutingGraph_costsBounded (I : Circulation) (C : ℕ)
    (hc : I.CostsBounded C) : I.shortestRoutingGraph.CostsBounded C := by
  intro e
  refine Fin.addCases (fun e => ?_) (fun v => ?_) e
  · simpa only [Fin.addCases_left] using hc e
  · simp only [Fin.addCases_right, Int.natAbs_zero]
    exact Nat.zero_le _

/-- Extract a potential from a supplied primal vector using one additional
circulation call, integer augmentation, and the counted traversal. -/
def extractDualModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) : CallResult (Fin I.n → ℤ) :=
  let R := I.residual f
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta := solveWithZeroCapacities solve Q
  let routing : Fin S.m → ℤ := fun e => start e +
    delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  let labels := S.propagateLabels routing (Fin.last I.n)
  ⟨(fun v => labels.1.labels v.castSucc), [Q.positiveInstance],
    100 * (I.m + I.n + 1) + labels.2⟩

/-- Dual extraction makes exactly one additional bounded-solver call. -/
theorem extractDualModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) :
    (extractDualModel solve I f).calls.length = 1 := rfl

/-- The additional solver call has exactly `4*m+2*n` edge slots. -/
theorem extractDualModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) :
    ∀ J ∈ (extractDualModel solve I f).calls, J.m = 4 * I.m + 2 * I.n := by
  intro J hJ
  have he : J = (((I.residual f).shortestRoutingGraph).residual
    ((I.residual f).shortestRoutingStart)).positiveInstance := List.mem_singleton.mp hJ
  subst J
  change (I.m + I.m + I.n) + (I.m + I.m + I.n) = _
  omega

/-- The added call has positive capacities bounded by `n+1`, including
inactive slots handled by the one-call solver adapter. -/
theorem extractDualModel_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) :
    ∀ J ∈ (extractDualModel solve I f).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ I.n + 1 := by
  intro J hJ
  have he : J = (((I.residual f).shortestRoutingGraph).residual
    ((I.residual f).shortestRoutingStart)).positiveInstance := List.mem_singleton.mp hJ
  subst J
  apply positiveInstance_capacitiesBounded
  · exact Nat.succ_le_succ (Nat.zero_le I.n)
  · apply residual_capacities_le
    · exact (I.residual f).shortestRoutingStart_bounds
    · exact (I.residual f).shortestRoutingGraph_capacities

/-- Dual extraction preserves the original absolute cost bound in its call. -/
theorem extractDualModel_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) (C : ℕ) (hc : I.CostsBounded C) :
    ∀ J ∈ (extractDualModel solve I f).calls, J.CostsBounded C := by
  intro J hJ
  have he : J = (((I.residual f).shortestRoutingGraph).residual
    ((I.residual f).shortestRoutingStart)).positiveInstance := List.mem_singleton.mp hJ
  subst J
  apply positiveInstance_costsBounded
  apply residual_costsBounded
  apply shortestRoutingGraph_costsBounded
  exact I.residual_costsBounded f C hc

/-- The extraction model reserves at most `200*(m+n+1)` other integer/table
operations, including the traversal and all graph and flow assembly scans. -/
theorem extractDualModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (f : Fin I.m → ℤ) :
    (extractDualModel solve I f).work ≤ 200 * (I.m + I.n + 1) := by
  let R := I.residual f
  let S := R.shortestRoutingGraph
  let Q := S.residual R.shortestRoutingStart
  let delta := solveWithZeroCapacities solve Q
  let routing : Fin S.m → ℤ := fun e => R.shortestRoutingStart e +
    delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  have h := S.propagateLabels_work routing (Fin.last I.n)
  change 100 * (I.m + I.n + 1) +
    (S.propagateLabels routing (Fin.last I.n)).2 ≤ _
  calc
    100 * (I.m + I.n + 1) + (S.propagateLabels routing (Fin.last I.n)).2 ≤
        100 * (I.m + I.n + 1) + (22 * S.m + 3 * S.n + 4) := Nat.add_le_add le_rfl h
    _ ≤ 200 * (I.m + I.n + 1) := by
      change 100 * (I.m + I.n + 1) +
        (22 * (I.m + I.m + I.n) + 3 * (I.n + 1) + 4) ≤ _
      omega

end MinCostFlow.Scaling.Circulation
