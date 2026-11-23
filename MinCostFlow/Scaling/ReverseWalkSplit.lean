module

public import MinCostFlow.Scaling.WalkEdgeLists
import Mathlib.Data.List.Nodup

/-!
# Splitting a simple stack path at a repeated vertex

The cycle scan in the proof of Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, closes a cycle when a new edge reaches a
vertex already on the stack. Splitting the old path at that vertex separates
the retained prefix from the suffix to peel. The suffix's edge heads are
disjoint from the prefix vertices, and closing it gives edge counts at most
one. This supplies the geometric facts behind the scan's marker updates.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.ReverseWalk
variable {I : Circulation} {a b : Fin I.n}

/-- The edge heads in reverse traversal order, excluding the start vertex. -/
def heads (p : I.ReverseWalk a b) : List (Fin I.n) := p.edges.map I.head

/-- The visited list is the list of edge heads followed by the starting vertex. -/
theorem vertices_eq_heads (p : I.ReverseWalk a b) : p.vertices = p.heads ++ [a] := by
  induction p with
  | nil => rfl
  | snoc e he p ih => simp only [vertices, heads, edges, List.map_cons, List.cons_append, ih]

/-- A path splits at any visited vertex, with its newest suffix first in the stack. -/
theorem split_at_vertex (p : I.ReverseWalk a b) (v : Fin I.n) (hv : v ∈ p.vertices) :
    ∃ q : I.ReverseWalk a v, ∃ r : I.ReverseWalk v b,
      p.edges = r.edges ++ q.edges ∧ p.vertices = r.heads ++ q.vertices := by
  induction p with
  | nil w =>
    have he : v = w := by simpa only [vertices, List.mem_singleton] using hv
    subst v
    exact ⟨.nil w, .nil w, rfl, rfl⟩
  | snoc e he p ih =>
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      exact ⟨.snoc e he p, .nil (I.head e), rfl, rfl⟩
    · obtain ⟨q, r, hedge, hvertices⟩ := ih hv
      refine ⟨q, .snoc e he r, ?_, ?_⟩
      · simp only [edges, hedge, List.cons_append]
      · simp only [vertices, heads, edges, List.map_cons, List.cons_append, hvertices]

/-- Splitting a simple path gives simple prefix and suffix, with each suffix
edge head outside the retained prefix's vertex set. -/
theorem split_simple_at_vertex (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (v : Fin I.n) (hv : v ∈ p.vertices) :
    ∃ q : I.ReverseWalk a v, ∃ r : I.ReverseWalk v b,
      p.edges = r.edges ++ q.edges ∧ p.vertices = r.heads ++ q.vertices ∧
      q.vertices.Nodup ∧ r.vertices.Nodup ∧
      (∀ w ∈ r.heads, w ∉ q.vertices) := by
  obtain ⟨q, r, hedge, hvertices⟩ := p.split_at_vertex v hv
  have hn : (r.heads ++ q.vertices).Nodup := hvertices ▸ hp
  obtain ⟨hr, hq, hdisj⟩ := List.nodup_append.mp hn
  have hd : ∀ w ∈ r.heads, w ∉ q.vertices := by
    intro w hw hqmem
    exact hdisj w hw w hqmem rfl
  have hrvertices : r.vertices.Nodup := by
    rw [r.vertices_eq_heads]
    apply List.nodup_append.mpr
    refine ⟨hr, by simp, ?_⟩
    intro w hw z hz heq
    have hzv : z = v := by simpa only [List.mem_singleton] using hz
    subst z
    subst w
    exact hd v hw q.end_mem_vertices
  exact ⟨q, r, hedge, hvertices, hq, hrvertices, hd⟩

/-- A used edge's head cannot be the start of a simple path. -/
theorem head_ne_start_of_count_pos (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (e : Fin I.m) (he : 0 < p.count e) : I.head e ≠ a := by
  induction p with
  | nil => simp only [count] at he; omega
  | snoc k hk p ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hp
    by_cases h : e = k
    · subst e
      intro hhead
      exact hnot (hhead.symm ▸ p.start_mem_vertices)
    · simp only [count, h, ↓reduceIte, zero_add] at he
      exact ih hn he

/-- Closing a simple path by an edge back to its start uses every edge at most once. -/
theorem count_closed_snoc_le_one (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (e : Fin I.m) (he : 0 < I.capacity e) (ht : I.tail e = b) (hh : I.head e = a) :
    ∀ k, ((ReverseWalk.snoc e he (ht.symm ▸ p)).count k) ≤ 1 := by
  intro k
  have hz : p.count e = 0 := by
    by_contra hn
    exact p.head_ne_start_of_count_pos hp e (Nat.pos_of_ne_zero hn) hh
  subst b
  change (if k = e then 1 else 0) + p.count k ≤ 1
  by_cases hk : k = e
  · subst k; simp only [↓reduceIte, hz, Nat.add_zero, le_refl]
  · simp only [hk, ↓reduceIte, zero_add]
    exact p.count_le_one_of_nodup hp k

end MinCostFlow.Scaling.Circulation.ReverseWalk
