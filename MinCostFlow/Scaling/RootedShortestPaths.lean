module

public import MinCostFlow.Scaling.ResidualPotential
import Mathlib.Data.Int.LeastGreatest

/-!
# Rooted shortest paths without negative cycles

Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, adds a source
reaching every vertex. When closed walks have nonnegative cost, the integral
costs of paths from that source attain a minimum. Removing closed parts
preserves this minimum and gives paths with no repeated vertex. Their costs
obey the usual distance inequalities on every active arc.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A least-cost rooted walk exists whenever the endpoint is reachable and
closed walks are nonnegative. -/
theorem exists_shortest_rooted (I : Circulation) (root v : Fin I.n)
    (hclosed : ∀ w : Fin I.n, ∀ p : I.DirectedWalk w w, 0 ≤ p.cost)
    (hreach : Nonempty (I.DirectedWalk root v)) :
    ∃ d : ℤ, (∃ p : I.DirectedWalk root v, p.cost = d) ∧
      ∀ p : I.DirectedWalk root v, d ≤ p.cost := by
  obtain ⟨L, hL⟩ := I.walk_cost_bounded_below hclosed
  let P : ℤ → Prop := fun d => ∃ p : I.DirectedWalk root v, p.cost = d
  have hbounded : ∃ L, ∀ d, P d → L ≤ d := by
    refine ⟨L, ?_⟩
    rintro d ⟨p, rfl⟩
    exact hL root v p
  have hex : ∃ d, P d := by
    obtain ⟨p⟩ := hreach
    exact ⟨p.cost, p, rfl⟩
  obtain ⟨d, hd, hmin⟩ := Int.exists_least_of_bdd hbounded hex
  exact ⟨d, hd, fun p => hmin p.cost ⟨p, rfl⟩⟩

/-- Rooted distances have value zero at the root, obey every active arc's
triangle inequality, and are attained by paths with no repeated vertex. -/
theorem exists_rooted_distances (I : Circulation) (root : Fin I.n)
    (hclosed : ∀ w : Fin I.n, ∀ p : I.DirectedWalk w w, 0 ≤ p.cost)
    (hreach : ∀ v, Nonempty (I.DirectedWalk root v)) :
    ∃ d : Fin I.n → ℤ, d root = 0 ∧
      (∀ e, 0 < I.capacity e → d (I.head e) ≤ d (I.tail e) + I.cost e) ∧
      ∀ v, ∃ p : I.DirectedWalk root v, p.vertices.Nodup ∧ p.cost = d v := by
  classical
  choose d hd using fun v => I.exists_shortest_rooted root v hclosed (hreach v)
  have hroot : d root = 0 := by
    obtain ⟨p, hp⟩ := (hd root).1
    have hlo := hclosed root p
    have hup := (hd root).2 (.nil root)
    simp only [DirectedWalk.cost] at hup
    omega
  refine ⟨d, hroot, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp⟩ := (hd (I.tail e)).1
    have hh := (hd (I.head e)).2 (p.append (.cons e he (.nil (I.head e))))
    rw [DirectedWalk.cost_append, hp] at hh
    simpa only [DirectedWalk.cost, add_zero] using hh
  · intro v
    obtain ⟨p, hp⟩ := (hd v).1
    obtain ⟨q, hq, hc⟩ := p.exists_nodup_cost_le hclosed
    have hm := (hd v).2 q
    exact ⟨q, hq, by omega⟩

end MinCostFlow.Scaling.Circulation
