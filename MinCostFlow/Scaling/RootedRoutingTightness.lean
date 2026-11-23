module

public import MinCostFlow.Scaling.RootedPathsFlow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tight arcs in an optimal rooted routing

Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, extracts shortest
labels from an optimal routing. The sum of simple shortest paths is a feasible
witness. Distance inequalities lower-bound every routing's cost by the sum
of distances, and the witness attains that bound. Thus every positive-flow
arc of an optimum is tight. This justifies label propagation along its support.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Pairing with a potential splits an objective into reduced cost and balance. -/
theorem objective_eq_reduced_add_pairing (I : Circulation) (f : Fin I.m → ℝ)
    (y : Fin I.n → ℝ) :
    I.objective f = (∑ e, I.reducedCost y e * f e) + ∑ v, y v * I.balance f v := by
  rw [← I.potential_pairing]
  simp only [reducedCost, sub_mul, Finset.sum_sub_distrib, objective]
  ring

/-- Pairing negative rooted distances with the routed demands gives their sum. -/
theorem rooted_distance_pairing (I : Circulation) (root : Fin I.n)
    (d : Fin I.n → ℤ) (hd : d root = 0) (f : Fin I.m → ℝ)
    (hb : ∀ v, I.balance f v = (I.n : ℝ) * (if v = root then 1 else 0) - 1) :
    (∑ v, -(d v : ℝ) * I.balance f v) = ∑ v, (d v : ℝ) := by
  classical
  have he (v : Fin I.n) : -(d v : ℝ) * I.balance f v =
      (if v = root then -((I.n : ℝ) * (d v : ℝ)) else 0) + (d v : ℝ) := by
    rw [hb]
    split <;> ring
  simp only [he, Finset.sum_add_distrib]
  simp [hd]

/-- Every nonnegative routing satisfying the capacities has objective at least
the sum of rooted distances. -/
theorem rooted_routing_cost_lower_bound (I : Circulation) (root : Fin I.n)
    (d : Fin I.n → ℤ) (hd : d root = 0)
    (htriangle : ∀ e, 0 < I.capacity e → d (I.head e) ≤ d (I.tail e) + I.cost e)
    (f : Fin I.m → ℝ)
    (hb : ∀ v, I.balance f v = (I.n : ℝ) * (if v = root then 1 else 0) - 1)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e) :
    (∑ v, (d v : ℝ)) ≤ I.objective f ∧
      ∀ e, 0 ≤ I.reducedCost (fun v => -(d v : ℝ)) e * f e := by
  have hnon (e : Fin I.m) : 0 ≤ I.reducedCost (fun v => -(d v : ℝ)) e * f e := by
    by_cases hz : f e = 0
    · rw [hz, mul_zero]
    · have hpos : 0 < f e := lt_of_le_of_ne (hf e).1 (Ne.symm hz)
      have hcap : 0 < I.capacity e := by
        have hh := lt_of_lt_of_le hpos (hf e).2
        exact_mod_cast hh
      have hi := htriangle e hcap
      have hr : (d (I.head e) : ℝ) ≤ (d (I.tail e) : ℝ) + (I.cost e : ℝ) := by exact_mod_cast hi
      have hc : 0 ≤ I.reducedCost (fun v => -(d v : ℝ)) e := by
        dsimp only [reducedCost, potentialDifference]
        linarith only [hr]
      exact mul_nonneg hc (hf e).1
  refine ⟨?_, hnon⟩
  rw [I.objective_eq_reduced_add_pairing f (fun v => -(d v : ℝ)),
    I.rooted_distance_pairing root d hd f hb]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun e _ => hnon e))

/-- Comparing a routing to the simple shortest-path witness forces all its
positive-flow arcs to be tight for the negative-distance potential. -/
theorem rooted_routing_tight (I : Circulation) (root : Fin I.n)
    (d : Fin I.n → ℤ) (hd : d root = 0)
    (htriangle : ∀ e, 0 < I.capacity e → d (I.head e) ≤ d (I.tail e) + I.cost e)
    (paths : (v : Fin I.n) → I.DirectedWalk root v)
    (hcost : ∀ v, (paths v).cost = d v)
    (f : Fin I.m → ℝ)
    (hb : ∀ v, I.balance f v = (I.n : ℝ) * (if v = root then 1 else 0) - 1)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e)
    (hopt : I.objective f ≤ I.objective (I.rootedPathsFlow root paths)) :
    ∀ e, 0 < f e → -(d (I.head e) : ℤ) = -(d (I.tail e) : ℤ) - I.cost e := by
  have hval : I.objective (I.rootedPathsFlow root paths) = ∑ v, (d v : ℝ) := by
    rw [I.rootedPathsFlow_objective]
    simp only [hcost]
  rw [hval] at hopt
  have hl := I.rooted_routing_cost_lower_bound root d hd htriangle f hb hf
  have heq := le_antisymm hopt hl.1
  have hsplit := I.objective_eq_reduced_add_pairing f (fun v => -(d v : ℝ))
  rw [I.rooted_distance_pairing root d hd f hb, heq] at hsplit
  have hsum : (∑ e, I.reducedCost (fun v => -(d v : ℝ)) e * f e) = 0 := by linarith only [hsplit]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e (_ : e ∈ Finset.univ) => hl.2 e)).mp hsum
  intro e he
  have hzero := (mul_eq_zero.mp (hz e (Finset.mem_univ e))).resolve_right (ne_of_gt he)
  dsimp only [reducedCost, potentialDifference] at hzero
  have hr : -(d (I.head e) : ℝ) = -(d (I.tail e) : ℝ) - (I.cost e : ℝ) := by linarith only [hzero]
  exact_mod_cast hr

end MinCostFlow.Scaling.Circulation
