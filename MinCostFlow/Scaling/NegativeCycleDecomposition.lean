module

public import MinCostFlow.Scaling.CycleSum
import Mathlib.Tactic.Linarith

/-!
# Choosing an optimum with only negative cycle terms

The proofs of Lemmas C.10 and C.12 used by capacity scaling in Appendix C
of Chen et al., arXiv:2203.00671v2, discard nonnegative cycles from an
optimal circulation. Filtering its decomposition preserves nonnegativity,
conservation, and capacity bounds, and cannot increase its cost. Optimality
therefore forces equality. The resulting optimum has at most `m` negative
simple cycle terms. Its cycles need not be edge-disjoint.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

private theorem sum_filter_le {α : Type} (xs : List α) (p : α → Bool) (f : α → ℝ)
    (h : ∀ x ∈ xs, p x = false → 0 ≤ f x) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, p y = false → 0 ≤ f y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hh := ih ht
    cases hp : p x
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      exact le_trans hh (le_add_of_nonneg_left (h x List.mem_cons_self hp))
    · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.sum_cons]
      exact add_le_add le_rfl hh

/-- Removing some nonnegative cycle terms cannot increase any coordinate. -/
theorem cycleSum_filter_le (I : Circulation) (terms : List (CycleTerm I))
    (p : CycleTerm I → Bool) (ht : ∀ t ∈ terms, 0 ≤ t.amount) (e : Fin I.m) :
    I.cycleSum (terms.filter p) e ≤ I.cycleSum terms e := by
  exact sum_filter_le terms p (fun t => t.amount * (t.walk.count e : ℝ))
    (fun t hm _ => mul_nonneg (ht t hm) (Nat.cast_nonneg _))

/-- Retaining only negative-cost cycles cannot increase the objective. -/
theorem cycleSum_negative_filter_objective (I : Circulation) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount) :
    I.objective (I.cycleSum (terms.filter (fun t => decide (t.walk.cost < 0)))) ≤
      I.objective (I.cycleSum terms) := by
  rw [I.cycleSum_objective, I.cycleSum_objective]
  apply sum_filter_le
  intro t hm hp
  have hc : 0 ≤ t.walk.cost := by
    have hn : ¬ t.walk.cost < 0 := of_decide_eq_false hp
    omega
  exact mul_nonneg (ht t hm) ((Int.cast_nonneg_iff (R := ℝ)).mpr hc)

/-- Every optimum admits a no-larger optimum decomposed into at most `m`
positive multiples of negative simple cycles, as used in C.10 and C.12. -/
theorem exists_negative_cycle_decomposition (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Optimal f) :
    ∃ terms : List (CycleTerm I), terms.length ≤ I.m ∧
      (∀ t ∈ terms, 0 < t.amount ∧ 0 < t.walk.length ∧
        (∀ e, t.walk.count e ≤ 1) ∧ t.walk.cost < 0) ∧
      I.Optimal (I.cycleSum terms) ∧ (∀ e, I.cycleSum terms e ≤ f e) ∧
      I.objective (I.cycleSum terms) = I.objective f := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := I.exists_cycle_decomposition f hf.1
  let neg := terms.filter (fun t => decide (t.walk.cost < 0))
  have hnon : ∀ t ∈ terms, 0 ≤ t.amount := fun t ht => (hterms t ht).1.le
  have hnonneg : ∀ t ∈ neg, 0 ≤ t.amount :=
    fun t ht => hnon t (List.mem_of_mem_filter ht)
  have hle : ∀ e, I.cycleSum neg e ≤ f e := by
    intro e
    rw [← hsum]
    exact I.cycleSum_filter_le terms _ hnon e
  have hfeas : I.Feasible (I.cycleSum neg) :=
    ⟨I.cycleSum_conserves neg, fun e =>
      ⟨I.cycleSum_nonneg neg hnonneg e, le_trans (hle e) (hf.1.2 e).2⟩⟩
  have hcost := I.cycleSum_negative_filter_objective terms hnon
  rw [hsum] at hcost
  have heq : I.objective (I.cycleSum neg) = I.objective f := le_antisymm hcost (hf.2 _ hfeas)
  refine ⟨neg, le_trans (List.length_filter_le _ _) hlen, ?_, ?_, hle, heq⟩
  · intro t ht
    obtain ⟨hm, hp⟩ := List.mem_filter.mp ht
    have hh := hterms t hm
    exact ⟨hh.1, hh.2.1, hh.2.2, of_decide_eq_true hp⟩
  · refine ⟨hfeas, ?_⟩
    intro g hg
    rw [heq]
    exact hf.2 g hg

end MinCostFlow.Scaling.Circulation
