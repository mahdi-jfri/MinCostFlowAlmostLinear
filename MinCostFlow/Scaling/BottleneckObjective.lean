module

public import MinCostFlow.Scaling.CycleSum
public import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The bottleneck approximation estimate

In the proof of Lemma C.10 of Chen et al., arXiv:2203.00671v2, Appendix C,
each negative simple cycle has bottleneck no larger than the selected value
`u`. Each coefficient in a feasible flow's cycle decomposition is therefore
at most `u`. The cycle cost is at least `-m^11`, and there are at most `m`
cycles. This proves the objective lower bound `-m^12*u`. The argument applies
to every feasible real flow and uses the corrected overlapping decomposition.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A cycle coefficient cannot exceed the capacity of any edge it uses. -/
theorem cycleTerm_amount_le_capacity (I : Circulation) (terms : List (CycleTerm I))
    (hterms : ∀ t ∈ terms, 0 ≤ t.amount)
    (hf : I.Feasible (I.cycleSum terms)) (t : CycleTerm I) (ht : t ∈ terms)
    (hsimple : ∀ e, t.walk.count e ≤ 1) (e : Fin I.m) (he : 0 < t.walk.count e) :
    t.amount ≤ I.capacity e := by
  have hone : t.walk.count e = 1 := by have hh := hsimple e; omega
  have hh := I.cycleTerm_le_sum terms hterms t ht e
  rw [hone, Nat.cast_one, mul_one] at hh
  exact le_trans hh (hf.2 e).2

private theorem sum_map_lower_bound {α : Type} (xs : List α) (f : α → ℝ) (b : ℝ)
    (h : ∀ x ∈ xs, b ≤ f x) : (xs.length : ℝ) * b ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have hi := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    linarith only [hh, hi]

/-- The maximum-negative-bottleneck estimate in Lemma C.10, with its
bottleneck condition written as a capacity bound on one used edge per cycle. -/
theorem objective_ge_neg_pow_twelve_mul (I : Circulation) (u : ℕ)
    (hc : I.CostsBounded (I.m ^ 10))
    (hcycles : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v,
      (∀ e, p.count e ≤ 1) → p.cost < 0 →
      ∃ e, 0 < p.count e ∧ I.capacity e ≤ u)
    (f : Fin I.m → ℝ) (hf : I.Feasible f) :
    -((I.m ^ 12 : ℕ) : ℝ) * (u : ℝ) ≤ I.objective f := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := I.exists_cycle_decomposition f hf
  have hnon : ∀ t ∈ terms, 0 ≤ t.amount := fun t ht => (hterms t ht).1.le
  have hfterms : I.Feasible (I.cycleSum terms) := by rw [hsum]; exact hf
  have hedge : ∀ e, -((I.m ^ 10 : ℕ) : ℤ) ≤ I.cost e := by
    intro e
    have hh := hc e
    omega
  have hbound (t : CycleTerm I) (ht : t ∈ terms) :
      -((u : ℝ) * ((I.m ^ 11 : ℕ) : ℝ)) ≤ t.amount * (t.walk.cost : ℝ) := by
    have hdata := hterms t ht
    by_cases hneg : t.walk.cost < 0
    · obtain ⟨e, he, hcap⟩ := hcycles t.vertex t.walk hdata.2.2 hneg
      have hamount := le_trans
        (I.cycleTerm_amount_le_capacity terms hnon hfterms t ht hdata.2.2 e he)
        (Nat.cast_le.mpr hcap)
      have hl := t.cost_ge_neg_edges_mul ((I.m ^ 10 : ℕ) : ℤ)
        (Int.natCast_nonneg _) hedge hdata.2.2
      have heq : (I.m : ℤ) * ((I.m ^ 10 : ℕ) : ℤ) = ((I.m ^ 11 : ℕ) : ℤ) := by
        simp only [Nat.cast_pow]
        ring
      simp only [neg_mul] at hl
      rw [heq] at hl
      have hlreal : -((I.m ^ 11 : ℕ) : ℝ) ≤ (t.walk.cost : ℝ) := by exact_mod_cast hl
      have h1 := mul_le_mul_of_nonneg_left hlreal hdata.1.le
      have h2 := mul_le_mul_of_nonneg_right hamount (Nat.cast_nonneg (α := ℝ) (I.m ^ 11))
      linarith only [h1, h2]
    · have hcost : 0 ≤ (t.walk.cost : ℝ) := by exact_mod_cast (le_of_not_gt hneg)
      exact le_trans (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        (mul_nonneg hdata.1.le hcost)
  have hh := sum_map_lower_bound terms (fun t => t.amount * (t.walk.cost : ℝ))
    (-((u : ℝ) * ((I.m ^ 11 : ℕ) : ℝ))) hbound
  have hlenreal : (terms.length : ℝ) ≤ I.m := Nat.cast_le.mpr hlen
  have hm := mul_le_mul_of_nonneg_right hlenreal
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) u) (Nat.cast_nonneg (α := ℝ) (I.m ^ 11)))
  rw [← I.cycleSum_objective, hsum] at hh
  have heq : (I.m : ℝ) * ((u : ℝ) * ((I.m ^ 11 : ℕ) : ℝ)) =
      ((I.m ^ 12 : ℕ) : ℝ) * u := by
    simp only [Nat.cast_pow]
    ring
  rw [heq] at hm
  linarith only [hh, hm]

end MinCostFlow.Scaling.Circulation
