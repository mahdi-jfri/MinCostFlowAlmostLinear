module

public import MinCostFlow.Scaling.ReverseWalk
public import MinCostFlow.Scaling.WalkShortening

/-!
# Counts and simple paths for stack walks

The stack invariant in the negative-cycle extraction of Lemma C.10 of
Chen et al., arXiv:2203.00671v2, Appendix C, records a simple directed path.
Its stored list has the same edge counts and cost as its walk. A closed
path with no repeated vertex is empty, and no edge of a simple path occurs
more than once. These facts justify the model's stack and marker operations.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.ReverseWalk
variable {I : Circulation} {a b : Fin I.n}

/-- Counting an edge in the concrete stack agrees with its walk count. -/
theorem count_edges (p : I.ReverseWalk a b) (e : Fin I.m) : p.edges.count e = p.count e := by
  induction p with
  | nil => rfl
  | snoc k hk p ih =>
    simp only [edges, List.count_cons, beq_iff_eq, ih, count]
    by_cases he : e = k <;> simp only [he, eq_comm, ↓reduceIte] <;> omega

/-- The cost accumulated over the stack is the walk cost. -/
theorem sum_cost_edges (p : I.ReverseWalk a b) : (p.edges.map I.cost).sum = p.cost := by
  induction p with
  | nil => rfl
  | snoc e he p ih => simp only [edges, List.map_cons, List.sum_cons, ih, cost]

/-- The head of every used edge occurs among the visited vertices. -/
theorem head_mem_vertices_of_count_pos (p : I.ReverseWalk a b) (e : Fin I.m)
    (he : 0 < p.count e) : I.head e ∈ p.vertices := by
  induction p with
  | nil => simp only [count] at he; omega
  | snoc k hk p ih =>
    by_cases h : e = k
    · subst e
      exact List.mem_cons_self
    · simp only [count, h, ↓reduceIte, zero_add] at he
      exact List.mem_cons_of_mem _ (ih he)

/-- No edge occurs more than once in a stack path without repeated vertices. -/
theorem count_le_one_of_nodup (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (e : Fin I.m) : p.count e ≤ 1 := by
  induction p with
  | nil => exact Nat.zero_le _
  | snoc k hk p ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hp
    by_cases he : e = k
    · subst e
      have hz : p.count k = 0 := by
        by_contra hn
        exact hnot (p.head_mem_vertices_of_count_pos k (Nat.pos_of_ne_zero hn))
      simp only [count, ↓reduceIte, hz, Nat.add_zero, le_refl]
    · simp only [count, he, ↓reduceIte, zero_add]
      exact ih hnodup

/-- A closed path without repeated vertices has an empty stack. -/
theorem edges_eq_nil_of_nodup_closed (p : I.ReverseWalk a a) (hp : p.vertices.Nodup) :
    p.edges = [] := by
  cases p with
  | nil => rfl
  | snoc e he q =>
    have hnot := (List.nodup_cons.mp hp).1
    exact False.elim (hnot q.start_mem_vertices)

/-- A simple path whose endpoints agree has an empty edge list. -/
theorem edges_nil_of_nodup_end_eq (p : I.ReverseWalk a b) (hp : p.vertices.Nodup)
    (he : b = a) : p.edges = [] := by
  subst b
  exact p.edges_eq_nil_of_nodup_closed hp

/-- An empty edge stack records only its starting vertex. -/
theorem vertices_of_edges_nil (p : I.ReverseWalk a b) (hp : p.edges = []) :
    p.vertices = [a] := by
  cases p with
  | nil => rfl
  | snoc e he q => simp only [edges, List.cons_ne_nil] at hp

/-- An empty edge stack has zero cost. -/
theorem cost_of_edges_nil (p : I.ReverseWalk a b) (hp : p.edges = []) : p.cost = 0 := by
  rw [← p.sum_cost_edges, hp]
  rfl

end MinCostFlow.Scaling.Circulation.ReverseWalk
