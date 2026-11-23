module

public import MinCostFlow.Scaling.CapacityApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The one-edge capacity-rounding case

The numerical loss estimate in the proof of Lemma C.12 of Chen et al.,
arXiv:2203.00671v2, Appendix C, needs a separate treatment for one edge.
With costs bounded by one, a negative optimum can only be a saturated
negative loop. Its exact magnitude is the capacity, so the rounded capacity
is unchanged. This proves the source's approximation claim also at `m=1`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

private theorem sum_one_edge (I : Circulation) (hm : I.m = 1)
    (F : Fin I.m → ℝ) (e : Fin I.m) : (∑ a, F a) = F e := by
  classical
  apply Finset.sum_eq_single e
  · intro a _ hne
    have heq : a = e := by apply Fin.ext; have ha := a.isLt; have he := e.isLt; omega
    exact False.elim (hne heq)
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

/-- With one edge and costs bounded by one, any negative optimum is a
saturated cost-minus-one loop, and its magnitude equals that edge's capacity. -/
theorem one_edge_negative_optimum (I : Circulation) (hm : I.m = 1)
    (hc : I.CostsBounded 1) (f : Fin I.m → ℝ) (hf : I.Optimal f)
    (hneg : I.objective f < 0) (e : Fin I.m) :
    I.cost e = -1 ∧ I.tail e = I.head e ∧ I.objective f = -(I.capacity e : ℝ) := by
  classical
  have hobj : I.objective f = (I.cost e : ℝ) * f e := sum_one_edge I hm _ e
  have hcostneg : I.cost e < 0 := by
    by_contra hn
    have hi : 0 ≤ I.cost e := le_of_not_gt hn
    have hr : 0 ≤ (I.cost e : ℝ) := (Int.cast_nonneg_iff (R := ℝ)).mpr hi
    have hh := mul_nonneg hr (hf.1.2 e).1
    rw [← hobj] at hh
    linarith only [hneg, hh]
  have hcost : I.cost e = -1 := by have hh := hc e; omega
  have hflowpos : 0 < f e := by rw [hcost, Int.cast_neg, Int.cast_one] at hobj; linarith only [hobj, hneg]
  have hloop : I.tail e = I.head e := by
    by_contra hn
    have hb := hf.1.1 (I.tail e)
    change (∑ a, I.incidence a (I.tail e) * f a) = 0 at hb
    rw [sum_one_edge I hm _ e] at hb
    simp only [incidence, ↓reduceIte, hn, sub_zero, one_mul] at hb
    linarith only [hb, hflowpos]
  let full : Fin I.m → ℝ := fun a => (I.capacity a : ℝ)
  have hfull : I.Feasible full := by
    constructor
    · intro v
      change (∑ a, I.incidence a v * full a) = 0
      rw [sum_one_edge I hm _ e]
      simp only [incidence, hloop, sub_self, zero_mul]
    · intro a
      exact ⟨Nat.cast_nonneg _, le_rfl⟩
  have hfullobj : I.objective full = -(I.capacity e : ℝ) := by
    rw [show I.objective full = (I.cost e : ℝ) * full e from sum_one_edge I hm _ e,
      hcost, Int.cast_neg, Int.cast_one, neg_one_mul]
  have hupper := hf.2 full hfull
  rw [hfullobj] at hupper
  have hlower : -(I.capacity e : ℝ) ≤ I.objective f := by
    rw [hobj, hcost, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact neg_le_neg (hf.1.2 e).2
  exact ⟨hcost, hloop, le_antisymm hupper hlower⟩

/-- For one edge, rounding at the exact negative optimum magnitude preserves
that edge's capacity. -/
theorem roundedCapacity_one_self (u : ℕ) : roundedCapacity 1 u u = u := by
  by_cases hu : u = 0
  · subst u
    norm_num [roundedCapacity, scaledCapacity, capacityUnit]
  · have hq : capacityUnit 1 u = u := by simp only [capacityUnit, one_pow, Nat.div_one]; omega
    simp only [roundedCapacity, scaledCapacity, hq, one_pow, Nat.mul_one,
      Nat.div_self (Nat.pos_of_ne_zero hu), min_self]

end MinCostFlow.Scaling.Circulation
