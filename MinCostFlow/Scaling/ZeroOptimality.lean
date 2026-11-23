module

public import MinCostFlow.Scaling.ResidualPotential
public import MinCostFlow.Scaling.ResidualOptimality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Zero optimality and negative closed walks

The unit-capacity test in the proof of Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, detects negative cycles by optimizing a
circulation. Zero is optimal exactly when every active closed walk has
nonnegative cost. One direction uses normalized walk counts. The other
constructs a feasible potential and sums nonnegative reduced costs.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- If all active closed walks are nonnegative, zero minimizes circulation cost. -/
theorem zero_optimal_of_closed_nonneg (I : Circulation)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost) :
    I.Optimal (fun _ => 0) := by
  obtain ⟨y, hy⟩ := I.exists_potential_of_closed_nonneg hclosed
  refine ⟨I.zero_feasible, ?_⟩
  intro f hf
  have hnon (e : Fin I.m) : 0 ≤ I.reducedCost (fun v => (y v : ℝ)) e * f e := by
    by_cases hz : I.capacity e = 0
    · have hfzero : f e = 0 := by
        have hh := hf.2 e
        rw [hz, Nat.cast_zero] at hh
        exact le_antisymm hh.2 hh.1
      rw [hfzero, mul_zero]
    · have hi := hy e (Nat.pos_of_ne_zero hz)
      have hr : (y (I.tail e) : ℝ) - (y (I.head e) : ℝ) ≤ (I.cost e : ℝ) := by exact_mod_cast hi
      have hc : 0 ≤ I.reducedCost (fun v => (y v : ℝ)) e := by
        dsimp only [reducedCost, potentialDifference]
        linarith only [hr]
      exact mul_nonneg hc (hf.2 e).1
  have hh := Finset.sum_nonneg (s := Finset.univ) (fun e _ => hnon e)
  rw [I.reducedCost_objective f hf.1] at hh
  simpa only [objective, mul_zero, Finset.sum_const_zero] using hh

/-- Negative closed walks exist exactly when zero is not optimal. -/
theorem not_zero_optimal_iff_negative_closed (I : Circulation) :
    ¬ I.Optimal (fun _ => 0) ↔
      ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, p.cost < 0 := by
  constructor
  · intro h
    by_contra hn
    apply h
    apply I.zero_optimal_of_closed_nonneg
    intro v p
    have hh : ¬ p.cost < 0 := fun hp => hn ⟨v, p, hp⟩
    omega
  · rintro ⟨v, p, hp⟩ hopt
    have hh := p.cost_nonneg_of_zero_optimal hopt
    omega

end MinCostFlow.Scaling.Circulation
