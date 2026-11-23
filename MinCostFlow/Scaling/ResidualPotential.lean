module

public import MinCostFlow.Scaling.WalkShortening
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Existence of a residual potential

The strong-duality argument of Appendix C of Chen et al., arXiv:2203.00671v2,
uses shortest-path labels when a graph has no negative cycles. This file proves
existence of these labels. Remove closed parts of walks, bound the cost of the
remaining simple walk, and take the least integral cost of any walk starting
at a given vertex. Such walks may stop anywhere. These labels have the sign
of the incidence convention of `Instance`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
namespace DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- A per-edge lower cost bound yields the corresponding walk bound. -/
theorem cost_ge_neg_length_mul (p : I.DirectedWalk a b) (C : ℤ)
    (hc : ∀ e, -C ≤ I.cost e) : -(p.length : ℤ) * C ≤ p.cost := by
  induction p with
  | nil => simp [length, cost]
  | cons e h p ih =>
    simp only [length, Nat.cast_add, Nat.cast_one, cost]
    nlinarith only [ih, hc e]

end DirectedWalk

/-- Without negative closed walks, the costs of all walks have a common lower
bound. Shortening gives at most `n-1` arcs; the sum of absolute edge costs is a
valid bound on the absolute cost of any one arc. -/
theorem walk_cost_bounded_below (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost) :
    ∃ L : ℤ, ∀ a b : Fin I.n, ∀ p : I.DirectedWalk a b, L ≤ p.cost := by
  classical
  let C : ℤ := ∑ e, |I.cost e|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun e _ => abs_nonneg (I.cost e))
  have he : ∀ e, -C ≤ I.cost e := by
    intro e
    have hle : |I.cost e| ≤ C :=
      Finset.single_le_sum (fun k _ => abs_nonneg (I.cost k)) (Finset.mem_univ e)
    exact le_trans (neg_le_neg hle) (neg_abs_le (I.cost e))
  refine ⟨-(I.n : ℤ) * C, ?_⟩
  intro a b p
  obtain ⟨q, hq, hc⟩ := p.exists_nodup_cost_le hclosed
  have hl : (q.length : ℤ) ≤ I.n := by
    exact_mod_cast (q.length_lt_vertices_of_nodup hq).le
  have hb := q.cost_ge_neg_length_mul C he
  have hm := mul_le_mul_of_nonneg_right (neg_le_neg hl) hC
  exact le_trans hm (le_trans hb hc)

/-- Every vertex has a least-cost walk to some endpoint if there are no
negative closed walks. The empty walk makes the set of costs nonempty. -/
theorem exists_shortest_from (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost)
    (v : Fin I.n) :
    ∃ z : ℤ, (∃ b : Fin I.n, ∃ p : I.DirectedWalk v b, p.cost = z) ∧
      ∀ b : Fin I.n, ∀ p : I.DirectedWalk v b, z ≤ p.cost := by
  obtain ⟨L, hL⟩ := I.walk_cost_bounded_below hclosed
  let P : ℤ → Prop := fun z => ∃ b : Fin I.n, ∃ p : I.DirectedWalk v b, p.cost = z
  have hbounded : ∃ L : ℤ, ∀ z, P z → L ≤ z := by
    refine ⟨L, ?_⟩
    rintro z ⟨b, p, rfl⟩
    exact hL v b p
  have hnonempty : ∃ z, P z := ⟨0, v, .nil v, rfl⟩
  obtain ⟨z, hz, hmin⟩ := Int.exists_least_of_bdd hbounded hnonempty
  refine ⟨z, hz, ?_⟩
  intro b p
  exact hmin p.cost ⟨b, p, rfl⟩

/-- Integral shortest-walk labels give nonnegative reduced costs on every
positive-capacity arc. This proves existence of the potential needed for the
dual certificate in Appendix C. -/
theorem exists_potential_of_closed_nonneg (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost) :
    ∃ y : Fin I.n → ℤ, ∀ e, 0 < I.capacity e →
      y (I.tail e) - y (I.head e) ≤ I.cost e := by
  classical
  choose y hy using I.exists_shortest_from hclosed
  refine ⟨y, ?_⟩
  intro e he
  obtain ⟨b, p, hp⟩ := (hy (I.head e)).1
  have h := (hy (I.tail e)).2 b (.cons e he p)
  simp only [DirectedWalk.cost, hp] at h
  omega

end MinCostFlow.Scaling.Circulation
