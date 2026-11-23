module

public import MinCostFlow.Scaling.WalkShortening
import Mathlib.Tactic.Linarith

/-!
# Short negative closed walks

The exactness step used by Lemma C.3 through Lemma C.5 of Chen et al.,
arXiv:2203.00671v2, Appendix C, checks simple residual cycles. Every negative
closed walk contains a negative closed walk of at most `n` arcs. We prove
this by taking one of minimum length and removing repeated vertices from
its tail. Every closed piece removed is shorter and hence nonnegative.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- Splitting at a visited vertex also splits the length exactly. -/
theorem split_at_vertex_length (p : I.DirectedWalk a b) (v : Fin I.n)
    (hv : v ∈ p.vertices) :
    ∃ q : I.DirectedWalk a v, ∃ r : I.DirectedWalk v b,
      p.cost = q.cost + r.cost ∧ p.length = q.length + r.length ∧
      r.vertices.Sublist p.vertices := by
  induction p with
  | nil w =>
    have he : v = w := by simpa only [vertices, List.mem_singleton] using hv
    subst v
    exact ⟨.nil w, .nil w, by simp [cost], rfl, List.Sublist.refl _⟩
  | cons e h p ih =>
    rcases List.mem_cons.mp hv with he | he
    · subst v
      exact ⟨.nil (I.tail e), .cons e h p, by simp [cost], by simp [length], List.Sublist.refl _⟩
    · obtain ⟨q, r, hc, hl, hs⟩ := ih he
      refine ⟨.cons e h q, r, ?_, ?_, hs.trans (List.sublist_cons_self _ _)⟩
      · simp only [cost, hc, add_assoc]
      · simp only [length, hl]; omega

/-- Only closed walks shorter than the current length bound are needed to
remove repeated vertices. The shortened walk does not gain arcs. -/
theorem exists_nodup_cost_le_of_bounded_closed (N : ℕ)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, p.length ≤ N → 0 ≤ p.cost)
    (p : I.DirectedWalk a b) (hp : p.length ≤ N) :
    ∃ q : I.DirectedWalk a b, q.vertices.Nodup ∧ q.cost ≤ p.cost ∧ q.length ≤ p.length := by
  induction p with
  | nil v => exact ⟨.nil v, by simp [vertices], le_rfl, le_rfl⟩
  | cons e h p ih =>
    have hpl : p.length ≤ N := by simp only [length] at hp; omega
    obtain ⟨q, hq, hc, hl⟩ := ih hpl
    by_cases hv : I.tail e ∈ q.vertices
    · obtain ⟨r, s, heq, hlen, hs⟩ := q.split_at_vertex_length (I.tail e) hv
      have hr : (DirectedWalk.cons e h r).length ≤ N := by
        simp only [length] at hp ⊢
        omega
      have hn := hclosed (I.tail e) (.cons e h r) hr
      refine ⟨s, hs.nodup hq, ?_, ?_⟩
      · dsimp only [cost] at hn ⊢
        linarith only [hc, heq, hn]
      · simp only [length]
        omega
    · refine ⟨.cons e h q, List.nodup_cons.mpr ⟨hv, hq⟩, add_le_add le_rfl hc, ?_⟩
      simp only [length]
      omega

/-- Any negative closed walk yields one with at most as many arcs as vertices.
This is the simple-cycle reduction used in the proof of Lemma C.5. -/
theorem exists_short_negative_closed
    (hneg : ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, p.cost < 0) :
    ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, p.cost < 0 ∧ p.length ≤ I.n := by
  classical
  let P (k : ℕ) := ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, p.cost < 0 ∧ p.length = k
  have hex : ∃ k, P k := by
    obtain ⟨v, p, hp⟩ := hneg
    exact ⟨p.length, v, p, hp, rfl⟩
  obtain ⟨v, p, hp, hlen⟩ := Nat.find_spec hex
  have hshort (w : Fin I.n) (q : I.DirectedWalk w w) (hq : q.length < p.length) :
      0 ≤ q.cost := by
    by_contra hn
    have hqneg : q.cost < 0 := by omega
    have hnot := Nat.find_min hex (show q.length < Nat.find hex by omega)
    exact hnot ⟨w, q, hqneg, rfl⟩
  cases p with
  | nil => simp only [cost] at hp; omega
  | cons e he q =>
    have hclosed : ∀ w : Fin I.n, ∀ r : I.DirectedWalk w w,
        r.length ≤ q.length → 0 ≤ r.cost := by
      intro w r hr
      apply hshort w r
      simp only [length]
      omega
    obtain ⟨r, hr, hc, _⟩ := q.exists_nodup_cost_le_of_bounded_closed q.length hclosed le_rfl
    refine ⟨I.tail e, .cons e he r, ?_, ?_⟩
    · simp only [cost] at hp ⊢
      omega
    · have hn := r.length_lt_vertices_of_nodup hr
      simp only [length]
      omega

end MinCostFlow.Scaling.Circulation.DirectedWalk
