module

public import MinCostFlow.Scaling.SimplePathCounts
public import MinCostFlow.Scaling.ExpensiveArcs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A simple cycle in a nonzero circulation's support

The cycle decomposition used in the proof of Lemma C.9 through C.10 and
C.12 of Chen et al., arXiv:2203.00671v2, Appendix C, starts with a positive
edge and a return path. Removing repeated vertices gives a cycle using each
edge at most once. Its number of arcs is therefore at most `m`, regardless
of isolated vertices. Repeated subtraction yields at most `m` cycles, which
may share edges; the source's edge-disjoint assertion is unnecessary.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- The endpoint is among the visited vertices. -/
theorem end_mem_vertices (p : I.DirectedWalk a b) : b ∈ p.vertices := by
  induction p with
  | nil => exact List.mem_singleton_self _
  | cons e he p ih => exact List.mem_cons_of_mem _ ih

/-- A simple path cannot use an arc whose tail is its endpoint. -/
theorem tail_ne_end_of_count_pos (p : I.DirectedWalk a b) (hp : p.vertices.Nodup)
    (e : Fin I.m) (he : 0 < p.count e) : I.tail e ≠ b := by
  induction p with
  | nil => simp only [count] at he; omega
  | cons k hk p ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hp
    by_cases h : e = k
    · subst e
      intro heq
      exact hnot (heq.symm ▸ p.end_mem_vertices)
    · simp only [count, h, ↓reduceIte, zero_add] at he
      exact ih hnodup he

/-- Counting all edge occurrences recovers the walk length. -/
theorem sum_count (p : I.DirectedWalk a b) : (∑ e, p.count e) = p.length := by
  classical
  induction p with
  | nil => simp only [count, length, Finset.sum_const_zero]
  | cons e he p ih =>
    simp only [count, Finset.sum_add_distrib, ih, length]
    simp [Nat.add_comm]

/-- A walk using each edge at most once has at most `m` arcs. -/
theorem length_le_edges_of_count_le_one (p : I.DirectedWalk a b)
    (hp : ∀ e, p.count e ≤ 1) : p.length ≤ I.m := by
  rw [← p.sum_count]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hh

end MinCostFlow.Scaling.Circulation.DirectedWalk

namespace MinCostFlow.Scaling.Circulation

/-- Any nonzero nonnegative circulation contains a nonempty closed support
walk using each edge at most once. Its length is at most the edge count. -/
theorem exists_simple_support_cycle (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) (he : ∃ e, 0 < f e) :
    ∃ v : Fin I.n, ∃ p : (I.positiveSupport f).DirectedWalk v v,
      0 < p.length ∧ (∀ e, p.count e ≤ 1) ∧ p.length ≤ I.m := by
  classical
  obtain ⟨e, he⟩ := he
  obtain ⟨q⟩ := I.exists_support_return_walk f hf e he
  obtain ⟨r, hr⟩ := q.exists_nodup
  have ha : 0 < (I.positiveSupport f).capacity e := by
    change 0 < if 0 < f e then 1 else 0
    rw [ite_eq_left he]
    decide
  have hz : r.count e = 0 := by
    by_contra hn
    have hh := r.tail_ne_end_of_count_pos hr e (Nat.pos_of_ne_zero hn)
    exact hh rfl
  let p := DirectedWalk.cons (I := I.positiveSupport f) e ha r
  have hcount (k : Fin I.m) : p.count k ≤ 1 := by
    change (if k = e then 1 else 0) + r.count k ≤ 1
    by_cases hk : k = e
    · subst k; simp only [↓reduceIte, hz, Nat.add_zero, le_refl]
    · simp only [hk, ↓reduceIte, zero_add]
      exact r.count_le_one_of_nodup hr k
  refine ⟨I.tail e, p, ?_, hcount, p.length_le_edges_of_count_le_one hcount⟩
  change 0 < r.length + 1
  exact Nat.zero_lt_succ _

end MinCostFlow.Scaling.Circulation
