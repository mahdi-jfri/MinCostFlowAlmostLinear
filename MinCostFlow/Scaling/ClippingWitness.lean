module

public import MinCostFlow.Scaling.NegativeCycleDecomposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An optimal flow below the capacity clipping threshold

The proof of Lemma C.12 used by Lemma C.9 of Chen et al.,
arXiv:2203.00671v2, Appendix C, bounds the flow before clipping. Negative
integral cycle costs are at most minus one. Hence the sum of the positive
cycle coefficients is at most minus the optimum value. This also bounds
every edge flow, even when the cycles overlap. This replaces the source's
invalid inference from a large edge flow to a single large coefficient.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- On negative integral cycles, the coefficient sum is bounded by minus the cost. -/
theorem negative_cycle_amount_sum_le (I : Circulation) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ t.walk.cost < 0) :
    (terms.map CycleTerm.amount).sum ≤ -I.objective (I.cycleSum terms) := by
  rw [I.cycleSum_objective]
  induction terms with
  | nil => simp
  | cons t terms ih =>
    have hh := ht t List.mem_cons_self
    have hi := ih (fun u hu => ht u (List.mem_cons_of_mem _ hu))
    have hc : (t.walk.cost : ℝ) ≤ -1 := by
      have hci : t.walk.cost ≤ -1 := by omega
      exact_mod_cast hci
    have hm := mul_le_mul_of_nonneg_left hc hh.1
    simp only [List.map_cons, List.sum_cons]
    linarith only [hi, hm]

/-- With simple cycles and nonnegative coefficients, each edge flow is no
larger than the sum of all coefficients. -/
theorem cycleSum_le_amount_sum (I : Circulation) (terms : List (CycleTerm I))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ ∀ e, t.walk.count e ≤ 1) (e : Fin I.m) :
    I.cycleSum terms e ≤ (terms.map CycleTerm.amount).sum := by
  induction terms with
  | nil => exact le_rfl
  | cons t terms ih =>
    have hh := ht t List.mem_cons_self
    have hi := ih (fun u hu => ht u (List.mem_cons_of_mem _ hu))
    have hc : (t.walk.count e : ℝ) ≤ 1 := by exact_mod_cast hh.2 e
    have hm := mul_le_mul_of_nonneg_left hc hh.1
    change t.amount * (t.walk.count e : ℝ) + I.cycleSum terms e ≤
      t.amount + (terms.map CycleTerm.amount).sum
    linarith only [hi, hm]

/-- An optimum can be chosen below `B*m^20`, assuming the source's
`m^12` approximation bound. This clipping estimate also covers `m=1`. -/
theorem exists_optimal_below_clipping (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Optimal f) (B : ℕ) (hm : 0 < I.m)
    (happrox : -I.objective f ≤ ((I.m ^ 12 : ℕ) : ℝ) * B) :
    ∃ g : Fin I.m → ℝ, I.Optimal g ∧ I.objective g = I.objective f ∧
      ∀ e, g e ≤ ((B * I.m ^ 20 : ℕ) : ℝ) := by
  obtain ⟨terms, _, hterms, hopt, _, hcost⟩ := I.exists_negative_cycle_decomposition f hf
  have hsum := I.negative_cycle_amount_sum_le terms
    (fun t ht => ⟨(hterms t ht).1.le, (hterms t ht).2.2.2⟩)
  have hp : I.m ^ 12 ≤ I.m ^ 20 := Nat.pow_le_pow_right hm (by decide)
  have hmul := Nat.mul_le_mul_left B hp
  have hmulreal : ((I.m ^ 12 : ℕ) : ℝ) * B ≤ ((B * I.m ^ 20 : ℕ) : ℝ) := by
    exact_mod_cast (show I.m ^ 12 * B ≤ B * I.m ^ 20 by simpa only [Nat.mul_comm] using hmul)
  refine ⟨I.cycleSum terms, hopt, hcost, ?_⟩
  intro e
  have he := I.cycleSum_le_amount_sum terms
    (fun t ht => ⟨(hterms t ht).1.le, (hterms t ht).2.2.1⟩) e
  rw [hcost] at hsum
  exact le_trans he (le_trans hsum (le_trans happrox hmulreal))

end MinCostFlow.Scaling.Circulation
