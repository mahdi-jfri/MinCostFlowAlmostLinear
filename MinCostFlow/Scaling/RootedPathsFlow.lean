module

public import MinCostFlow.Scaling.SimplePathCounts
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Routing one unit along each rooted path

The witness routing in Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, is the sum of one simple shortest path per vertex. Its balance
is `N-1` at the root and minus one at every other vertex. The empty path
to the root contributes zero. Summing the edge counts gives its cost and
shows that capacity `N` on every active arc suffices.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The sum of the unit edge-count vectors of a family of rooted paths.
This is a mathematical witness for routing optimality. -/
def rootedPathsFlow (I : Circulation) (root : Fin I.n)
    (paths : (v : Fin I.n) → I.DirectedWalk root v) (e : Fin I.m) : ℝ :=
  ∑ v, ((paths v).count e : ℝ)

/-- The sum of rooted paths routes one unit to each nonroot vertex. -/
theorem rootedPathsFlow_balance (I : Circulation) (root : Fin I.n)
    (paths : (v : Fin I.n) → I.DirectedWalk root v) (w : Fin I.n) :
    I.balance (I.rootedPathsFlow root paths) w =
      (I.n : ℝ) * (if w = root then 1 else 0) - 1 := by
  classical
  unfold balance rootedPathsFlow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ v, I.balance (fun e => ((paths v).count e : ℝ)) w) = _
  simp_rw [DirectedWalk.balance_count]
  rw [Finset.sum_sub_distrib]
  simp

/-- The sum routing's cost is the sum of its path costs. -/
theorem rootedPathsFlow_objective (I : Circulation) (root : Fin I.n)
    (paths : (v : Fin I.n) → I.DirectedWalk root v) :
    I.objective (I.rootedPathsFlow root paths) = ∑ v, ((paths v).cost : ℝ) := by
  unfold objective rootedPathsFlow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun v _ => (paths v).objective_count)

/-- Summing simple paths fits capacity `N` on all active slots. -/
theorem rootedPathsFlow_bounds (I : Circulation) (root : Fin I.n)
    (paths : (v : Fin I.n) → I.DirectedWalk root v)
    (hp : ∀ v, (paths v).vertices.Nodup)
    (hc : ∀ e, I.capacity e = 0 ∨ I.n ≤ I.capacity e) :
    ∀ e, 0 ≤ I.rootedPathsFlow root paths e ∧
      I.rootedPathsFlow root paths e ≤ I.capacity e := by
  intro e
  constructor
  · exact Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  · rcases hc e with hz | hpos
    · have hzero (v : Fin I.n) : (paths v).count e = 0 := by
        by_contra hn
        have hh := (paths v).active_of_count_pos e (Nat.pos_of_ne_zero hn)
        rw [hz] at hh
        omega
      simp only [rootedPathsFlow, hzero, Nat.cast_zero, Finset.sum_const_zero, hz, Nat.cast_zero, le_refl]
    · apply le_trans _ (Nat.cast_le.mpr hpos)
      have hh : (∑ v : Fin I.n, ((paths v).count e : ℝ)) ≤ ∑ _ : Fin I.n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        exact_mod_cast (paths v).count_le_one_of_nodup (hp v) e
      simpa only [rootedPathsFlow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using hh

end MinCostFlow.Scaling.Circulation
