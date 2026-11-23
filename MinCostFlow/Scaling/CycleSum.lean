module

public import MinCostFlow.Scaling.CycleDecomposition
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Flow and objective identities for weighted cycles

The approximation estimates used in Lemma C.9 of Chen et al.,
arXiv:2203.00671v2, Appendix C, sum cycle coefficients and costs. Weighted
closed walks always conserve flow. With nonnegative coefficients their sum
is nonnegative and dominates every individual term. Their objective is the
sum of the coefficient times the integral cost of each walk.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Every weighted sum of closed walks conserves flow. -/
theorem cycleSum_conserves (I : Circulation) (terms : List (CycleTerm I)) :
    I.Conserves (I.cycleSum terms) := by
  intro v
  induction terms with
  | nil => simp only [cycleSum, List.map_nil, List.sum_nil, balance, mul_zero, Finset.sum_const_zero]
  | cons t terms ih =>
    have he : I.balance (I.cycleSum (t :: terms)) v =
        t.amount * I.balance (fun e => (t.walk.count e : ℝ)) v + I.balance (I.cycleSum terms) v := by
      simp only [cycleSum, List.map_cons, List.sum_cons, balance, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [he, t.walk.balance_count, sub_self, mul_zero, zero_add, ih]

/-- The objective of a weighted cycle sum is the sum of its weighted walk costs. -/
theorem cycleSum_objective (I : Circulation) (terms : List (CycleTerm I)) :
    I.objective (I.cycleSum terms) = (terms.map (fun t => t.amount * (t.walk.cost : ℝ))).sum := by
  induction terms with
  | nil => simp only [cycleSum, List.map_nil, List.sum_nil, objective, mul_zero, Finset.sum_const_zero]
  | cons t terms ih =>
    have he : I.objective (I.cycleSum (t :: terms)) =
        t.amount * I.objective (fun e => (t.walk.count e : ℝ)) + I.objective (I.cycleSum terms) := by
      simp only [cycleSum, List.map_cons, List.sum_cons, objective, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [he, t.walk.objective_count, ih]
    rfl

/-- Nonnegative coefficients give a nonnegative sum flow. -/
theorem cycleSum_nonneg (I : Circulation) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount) (e : Fin I.m) : 0 ≤ I.cycleSum terms e := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (ht t htmem) (Nat.cast_nonneg _)

/-- Every nonnegative term is bounded by the total flow, even if cycles overlap. -/
theorem cycleTerm_le_sum (I : Circulation) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount) (t : CycleTerm I) (hmem : t ∈ terms) (e : Fin I.m) :
    t.amount * (t.walk.count e : ℝ) ≤ I.cycleSum terms e := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (ht u hu) (Nat.cast_nonneg _)
  · exact List.mem_map.mpr ⟨t, hmem, rfl⟩

/-- Each simple cycle has cost at least minus `m*C` when each edge has cost
at least minus `C`. This is the cost estimate in C.10 and C.12. -/
theorem CycleTerm.cost_ge_neg_edges_mul {I : Circulation} (t : CycleTerm I) (C : ℤ)
    (hC : 0 ≤ C) (hc : ∀ e, -C ≤ I.cost e) (hsimple : ∀ e, t.walk.count e ≤ 1) :
    -(I.m : ℤ) * C ≤ t.walk.cost := by
  have hh := t.walk.cost_ge_neg_length_mul C hc
  have hlen : (t.walk.length : ℤ) ≤ I.m := by
    exact_mod_cast t.walk.length_le_edges_of_count_le_one hsimple
  exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg hlen) hC) hh

end MinCostFlow.Scaling.Circulation
