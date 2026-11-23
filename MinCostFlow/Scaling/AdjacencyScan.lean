module

public import MinCostFlow.Scaling.Circulation
public import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Building adjacency lists for positive flow

The dual-extraction reduction in Appendix C of Chen et al., arXiv:2203.00671v2,
extracts a shortest-path tree from a flow. Its traversal needs adjacency lists
of positive-flow arcs. The construction below scans edges once and prepends
each positive-flow edge to its tail's list. The total number of stored list
entries is at most the number of scanned edges.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Total number of arc entries in a vertex-indexed adjacency table. -/
def adjacencyMass (I : Circulation) (out : Fin I.n → List (Fin I.m)) : ℕ :=
  ∑ v, (out v).length

/-- Replacing one adjacency list changes the table's total length by exactly
that list's change in length. -/
theorem adjacencyMass_update (I : Circulation) (out : Fin I.n → List (Fin I.m))
    (v : Fin I.n) (entries : List (Fin I.m)) :
    I.adjacencyMass (Function.update out v entries) + (out v).length =
      I.adjacencyMass out + entries.length := by
  classical
  have he : (fun w => (Function.update out v entries w).length) =
      Function.update (fun w => (out w).length) v entries.length := by
    funext w
    by_cases h : w = v <;> simp only [Function.update_apply, h, ↓reduceIte]
  have hu : I.adjacencyMass (Function.update out v entries) =
      entries.length + ∑ w ∈ Finset.univ.erase v, (out w).length := by
    unfold adjacencyMass
    rw [he, Finset.sum_update_of_mem (Finset.mem_univ v)]
    rw [Finset.sdiff_singleton_eq_erase]
  have ho := Finset.sum_erase_add Finset.univ (fun w => (out w).length)
    (Finset.mem_univ v)
  dsimp only [adjacencyMass] at hu ⊢
  rw [hu]
  omega

/-- Insert one positive-flow arc into its tail's adjacency list. -/
def adjacencyStep (I : Circulation) (flow : Fin I.m → ℤ)
    (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) : Fin I.n → List (Fin I.m) :=
  if 0 < flow e then Function.update out (I.tail e) (e :: out (I.tail e)) else out

/-- The edge scan inserts at most one adjacency entry per processed edge. -/
theorem adjacencyStep_mass (I : Circulation) (flow : Fin I.m → ℤ)
    (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) :
    I.adjacencyMass (I.adjacencyStep flow out e) ≤ I.adjacencyMass out + 1 := by
  unfold adjacencyStep
  split
  · have h := I.adjacencyMass_update out (I.tail e) (e :: out (I.tail e))
    simp only [List.length_cons] at h
    omega
  · exact Nat.le_succ _

/-- Build positive-flow adjacency lists by a single explicit edge scan. -/
def buildAdjacency (I : Circulation) (flow : Fin I.m → ℤ) : Fin I.n → List (Fin I.m) :=
  (List.finRange I.m).foldl (I.adjacencyStep flow) (fun _ => [])

/-- The total adjacency storage after any edge scan grows by at most its length. -/
theorem fold_adjacencyMass (I : Circulation) (flow : Fin I.m → ℤ)
    (es : List (Fin I.m)) (out : Fin I.n → List (Fin I.m)) :
    I.adjacencyMass (es.foldl (I.adjacencyStep flow) out) ≤
      I.adjacencyMass out + es.length := by
  induction es generalizing out with
  | nil => exact le_rfl
  | cons e es ih =>
    have h := ih (I.adjacencyStep flow out e)
    have hs := I.adjacencyStep_mass flow out e
    change I.adjacencyMass (es.foldl (I.adjacencyStep flow) (I.adjacencyStep flow out e)) ≤ _
    rw [List.length_cons]
    omega

/-- A complete adjacency scan stores at most `m` edge entries. -/
theorem buildAdjacency_mass (I : Circulation) (flow : Fin I.m → ℤ) :
    I.adjacencyMass (I.buildAdjacency flow) ≤ I.m := by
  have h := I.fold_adjacencyMass flow (List.finRange I.m) (fun _ => [])
  simpa only [buildAdjacency, adjacencyMass, List.length_nil, Finset.sum_const_zero,
    zero_add, List.length_finRange] using h

end MinCostFlow.Scaling.Circulation
