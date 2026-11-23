module

public import MinCostFlow.Scaling.AdjacencyScan
import Mathlib.Tactic.Tauto

/-!
# Membership in the computed positive-flow adjacency lists

The shortest-tree extraction in Lemma C.8 of Chen et al.,
arXiv:2203.00671v2, Appendix C, traverses exactly the positive-flow arcs.
This file proves that the explicit adjacency scan stores an arc at a vertex
exactly when that vertex is its tail and its flow is positive.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

private theorem adjacencyStep_mem (I : Circulation) (flow : Fin I.m → ℤ)
    (out : Fin I.n → List (Fin I.m)) (k e : Fin I.m) (v : Fin I.n) :
    e ∈ I.adjacencyStep flow out k v ↔
      e ∈ out v ∨ e = k ∧ 0 < flow e ∧ v = I.tail e := by
  classical
  by_cases hk : 0 < flow k <;> by_cases hv : v = I.tail k
  · simp only [adjacencyStep, hk, ↓reduceIte, Function.update_apply, hv,
      List.mem_cons]
    constructor
    · rintro (he | he)
      · subst e; exact Or.inr ⟨rfl, hk, rfl⟩
      · exact Or.inl he
    · rintro (he | ⟨rfl, _, _⟩)
      · exact Or.inr he
      · exact Or.inl rfl
  · simp only [adjacencyStep, hk, ↓reduceIte, Function.update_apply, hv]
    constructor
    · exact Or.inl
    · rintro (he | ⟨rfl, _, he⟩)
      · exact he
      · exact False.elim (hv he)
  · simp only [adjacencyStep, hk, ↓reduceIte]
    constructor
    · exact Or.inl
    · rintro (he | ⟨rfl, he, _⟩)
      · exact he
      · exact False.elim (hk he)
  · simp only [adjacencyStep, hk, ↓reduceIte]
    constructor
    · exact Or.inl
    · rintro (he | ⟨rfl, he, _⟩)
      · exact he
      · exact False.elim (hk he)

/-- An arbitrary edge scan inserts precisely its positive-flow entries. -/
theorem fold_adjacency_mem (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) (v : Fin I.n) :
    e ∈ es.foldl (I.adjacencyStep flow) out v ↔
      e ∈ out v ∨ e ∈ es ∧ 0 < flow e ∧ v = I.tail e := by
  induction es generalizing out with
  | nil => simp
  | cons k es ih =>
    rw [List.foldl_cons, ih, adjacencyStep_mem]
    simp only [List.mem_cons]
    tauto

/-- The computed adjacency table contains exactly the positive-flow arcs at their tails. -/
theorem buildAdjacency_mem (I : Circulation) (flow : Fin I.m → ℤ)
    (e : Fin I.m) (v : Fin I.n) :
    e ∈ I.buildAdjacency flow v ↔ 0 < flow e ∧ v = I.tail e := by
  unfold buildAdjacency
  rw [I.fold_adjacency_mem]
  simp only [List.not_mem_nil, List.mem_finRange, false_or, true_and]

end MinCostFlow.Scaling.Circulation
