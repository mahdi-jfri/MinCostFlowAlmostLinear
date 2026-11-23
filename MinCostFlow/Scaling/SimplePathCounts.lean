module

public import MinCostFlow.Scaling.WalkShortening

/-!
# Edge counts of paths with no repeated vertex

The shortest-path routing in Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, sends a unit on one simple path per vertex. Such a path uses
an edge at most once. This proves that summing these paths fits the finite
capacity used by the integer routing model.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- The tail of any used edge occurs among the walk's visited vertices. -/
theorem tail_mem_vertices_of_count_pos (p : I.DirectedWalk a b) (e : Fin I.m)
    (he : 0 < p.count e) : I.tail e ∈ p.vertices := by
  induction p with
  | nil => simp only [count] at he; omega
  | cons k hk p ih =>
    by_cases h : e = k
    · subst e
      exact List.mem_cons_self
    · simp only [count, h, ↓reduceIte, zero_add] at he
      exact List.mem_cons_of_mem _ (ih he)

/-- A walk without repeated vertices uses each edge at most once. -/
theorem count_le_one_of_nodup (p : I.DirectedWalk a b) (hp : p.vertices.Nodup)
    (e : Fin I.m) : p.count e ≤ 1 := by
  induction p with
  | nil => exact Nat.zero_le _
  | cons k hk p ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hp
    by_cases h : e = k
    · subst e
      have hz : p.count k = 0 := by
        by_contra hn
        exact hnot (p.tail_mem_vertices_of_count_pos k (Nat.pos_of_ne_zero hn))
      simp only [count, ↓reduceIte, hz, Nat.add_zero, le_refl]
    · simp only [count, h, ↓reduceIte, zero_add]
      exact ih hnodup

end MinCostFlow.Scaling.Circulation.DirectedWalk
