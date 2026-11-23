module

public import MinCostFlow.Scaling.AdjacencyMembership

/-!
# Exact edge counts in positive-flow adjacency tables

The unit-circulation extraction in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, consumes each positive-flow edge once.
This file proves exact counts for the explicit adjacency scan. Under an
integral unit flow, the stored counts reproduce that flow, including loops
and parallel edges.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

private theorem adjacencyStep_count (I : Circulation) (flow : Fin I.m → ℤ)
    (out : Fin I.n → List (Fin I.m)) (k e : Fin I.m) (v : Fin I.n) :
    (I.adjacencyStep flow out k v).count e = (out v).count e +
      (if e = k ∧ 0 < flow e ∧ v = I.tail e then 1 else 0) := by
  classical
  by_cases he : e = k
  · subst e
    by_cases hp : 0 < flow k <;> by_cases hv : v = I.tail k <;>
      simp [adjacencyStep, hp, hv]
  · by_cases hp : 0 < flow k <;> by_cases hv : v = I.tail k <;>
      simp [adjacencyStep, hp, hv, he, Ne.symm he]

/-- An arbitrary scan inserts each positive-flow edge once per occurrence. -/
theorem fold_adjacency_count (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) (v : Fin I.n) :
    (es.foldl (I.adjacencyStep flow) out v).count e = (out v).count e +
      es.count e * (if 0 < flow e ∧ v = I.tail e then 1 else 0) := by
  induction es generalizing out with
  | nil => simp
  | cons k es ih =>
    rw [List.foldl_cons, ih, adjacencyStep_count, List.count_cons]
    by_cases he : e = k
    · subst e
      by_cases hp : 0 < flow k ∧ v = I.tail k <;> simp [hp, Nat.add_assoc, Nat.add_comm]
    · by_cases hp : 0 < flow e ∧ v = I.tail e <;> simp [he, Ne.symm he, hp]

/-- Each edge occurs exactly once at its tail when its flow is positive. -/
theorem buildAdjacency_count (I : Circulation) (flow : Fin I.m → ℤ)
    (e : Fin I.m) (v : Fin I.n) :
    (I.buildAdjacency flow v).count e = if 0 < flow e ∧ v = I.tail e then 1 else 0 := by
  unfold buildAdjacency
  rw [I.fold_adjacency_count]
  simp only [List.count_nil, List.count_finRange, Nat.one_mul, Nat.zero_add]

/-- Integral unit flow is exactly the occurrence count in the computed table. -/
theorem buildAdjacency_count_unit (I : Circulation) (flow : Fin I.m → ℤ)
    (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1) (e : Fin I.m) :
    ((I.buildAdjacency flow (I.tail e)).count e : ℤ) = flow e := by
  rw [I.buildAdjacency_count]
  have hh := hflow e
  split <;> omega

end MinCostFlow.Scaling.Circulation
