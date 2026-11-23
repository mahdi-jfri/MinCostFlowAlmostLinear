module

public import MinCostFlow.Scaling.DirectedWalk
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith

/-!
# Removing closed parts of directed walks

To construct the potential used by strong duality in Appendix C of Chen et al.,
arXiv:2203.00671v2, shortest walks may be taken to have no repeated vertex.
This file proves that assertion directly. Split at a repeated vertex and remove
the resulting closed walk. Its cost is nonnegative, so the cost cannot increase.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- The first vertex belongs to the list of visited vertices. -/
theorem start_mem_vertices (p : I.DirectedWalk a b) : a ∈ p.vertices := by
  cases p <;> simp [vertices]

/-- The vertex list has one more entry than the number of arcs. -/
theorem length_vertices (p : I.DirectedWalk a b) : p.vertices.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons e h p ih => simp only [vertices, List.length_cons, length, ih]

/-- Split a walk at any visited vertex. The suffix visits a sublist of the
original vertex list, so it inherits absence of repetitions. -/
theorem split_at_vertex (p : I.DirectedWalk a b) (v : Fin I.n)
    (hv : v ∈ p.vertices) :
    ∃ q : I.DirectedWalk a v, ∃ r : I.DirectedWalk v b,
      p.cost = q.cost + r.cost ∧ r.vertices.Sublist p.vertices := by
  induction p with
  | nil w =>
    have he : v = w := by simpa only [vertices, List.mem_singleton] using hv
    subst v
    exact ⟨.nil w, .nil w, by simp [cost], List.Sublist.refl _⟩
  | cons e h p ih =>
    rcases List.mem_cons.mp hv with he | he
    · subst v
      exact ⟨.nil (I.tail e), .cons e h p, by simp [cost], List.Sublist.refl _⟩
    · obtain ⟨q, r, hc, hs⟩ := ih he
      refine ⟨.cons e h q, r, ?_, ?_⟩
      · simp only [cost, hc, add_assoc]
      · exact hs.trans (List.sublist_cons_self _ _)

/-- If every closed walk has nonnegative cost, any walk can be shortened to
one with no repeated vertex and no greater cost. -/
theorem exists_nodup_cost_le
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost)
    (p : I.DirectedWalk a b) :
    ∃ q : I.DirectedWalk a b, q.vertices.Nodup ∧ q.cost ≤ p.cost := by
  induction p with
  | nil v => exact ⟨.nil v, by simp [vertices], le_rfl⟩
  | cons e h p ih =>
    obtain ⟨q, hq, hc⟩ := ih
    by_cases hv : I.tail e ∈ q.vertices
    · obtain ⟨r, s, heq, hs⟩ := q.split_at_vertex (I.tail e) hv
      have hn := hclosed (I.tail e) (.cons e h r)
      refine ⟨s, hs.nodup hq, ?_⟩
      dsimp only [cost] at hn ⊢
      linarith only [hc, heq, hn]
    · refine ⟨.cons e h q, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨hv, hq⟩
      · exact add_le_add le_rfl hc

/-- A walk with no repeated vertex uses strictly fewer arcs than vertices. -/
theorem length_lt_vertices_of_nodup (p : I.DirectedWalk a b)
    (hp : p.vertices.Nodup) : p.length < I.n := by
  have hle : p.vertices.length ≤ I.n := by
    have h := hp.length_le_card
    simpa using h
  rw [p.length_vertices] at hle
  omega

end MinCostFlow.Scaling.Circulation.DirectedWalk
