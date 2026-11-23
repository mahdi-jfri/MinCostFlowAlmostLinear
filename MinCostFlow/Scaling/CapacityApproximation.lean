module

public import MinCostFlow.Scaling.RoundedCycleLoss
public import MinCostFlow.Scaling.ClippingWitness
public import MinCostFlow.Scaling.CapacityLossBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Constant approximation by capacity rounding

Lemma C.12 used by Lemma C.9 of Chen et al., arXiv:2203.00671v2,
Appendix C, compares the capacity-rounded optimum with an original optimum.
For at least two edge slots, the proved clipping and coefficient-rounding
witnesses give the claimed `1.1` factor. The unit-one case is exact. This
proof repairs the source's overlapping-cycle, clipping-multiple, and small-B
steps while retaining its argument. The one-edge case is separate.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Lemma C.12's approximation estimate for every `m >= 2`, including all
residual instances used by Algorithm CapacityScaling. The negative-cost
ratio is stated without division as `11*returned <= 10*optimum`. -/
theorem lemma_C_12_of_two_le_edges (I : Circulation) (B : ℕ) (hm : 2 ≤ I.m)
    (hc : I.CostsBounded (I.m ^ 10)) (fstar : Fin I.m → ℝ) (hfstar : I.Optimal fstar)
    (hB : (B : ℝ) ≤ -I.objective fstar)
    (happrox : -I.objective fstar ≤ ((I.m ^ 12 : ℕ) : ℝ) * B)
    (fB : Fin I.m → ℤ)
    (hfB : (I.capacityRounded B).Optimal (fun e => (fB e : ℝ))) :
    I.Feasible (fun e => (fB e : ℝ)) ∧
      11 * I.objective (fun e => (fB e : ℝ)) ≤ 10 * I.objective fstar := by
  refine ⟨I.capacityRounded_feasible B _ hfB.1, ?_⟩
  let q := capacityUnit I.m B
  have hq : 0 < q := capacityUnit_pos _ _
  by_cases hone : q = 1
  · obtain ⟨g, hg, hcost, hclip⟩ := I.exists_optimal_below_clipping fstar hfstar B (by omega) happrox
    have hfeas : (I.capacityRounded B).Feasible g := by
      refine ⟨hg.1.1, ?_⟩
      intro e
      refine ⟨(hg.1.2 e).1, ?_⟩
      have hcapa : (I.capacityRounded B).capacity e = min (I.capacity e) (B * I.m ^ 20) :=
        roundedCapacity_of_unit_one _ _ _ hone
      rw [hcapa, Nat.cast_min]
      exact le_min (hg.1.2 e).2 (hclip e)
    have hcompare := hfB.2 g hfeas
    change I.objective (fun e => (fB e : ℝ)) ≤ I.objective g at hcompare
    rw [hcost] at hcompare
    have hnon : I.objective fstar ≤ 0 := le_trans (hfstar.2 _ I.zero_feasible) (by simp [objective])
    linarith only [hcompare, hnon]
  · have hqgt : 1 < q := by omega
    obtain ⟨terms, hlen, hterms, hopt, _, hcost⟩ := I.exists_negative_cycle_decomposition fstar hfstar
    have hnon : ∀ t ∈ terms, 0 ≤ t.amount := fun t ht => (hterms t ht).1.le
    have hsum := I.negative_cycle_amount_sum_le terms
      (fun t ht => ⟨(hterms t ht).1.le, (hterms t ht).2.2.2⟩)
    have hp : I.m ^ 12 ≤ I.m ^ 20 := Nat.pow_le_pow_right (by omega) (by decide)
    have hmul : ((I.m ^ 12 : ℕ) : ℝ) * B ≤ ((B * I.m ^ 20 : ℕ) : ℝ) := by
      have hh := Nat.mul_le_mul_left B hp
      exact_mod_cast (show I.m ^ 12 * B ≤ B * I.m ^ 20 by simpa only [Nat.mul_comm] using hh)
    have hclip : ∀ e, I.cycleSum terms e ≤ ((B * I.m ^ 20 : ℕ) : ℝ) := by
      intro e
      have he := I.cycleSum_le_amount_sum terms
        (fun t ht => ⟨(hterms t ht).1.le, (hterms t ht).2.2.1⟩) e
      rw [hcost] at hsum
      exact le_trans he (le_trans hsum (le_trans happrox hmul))
    have hfeas := I.roundCycleTerms_feasible B terms hnon hopt.1 hclip
    have hcompare := hfB.2 _ hfeas
    change I.objective (fun e => (fB e : ℝ)) ≤ I.objective (I.cycleSum (roundCycleTerms q terms)) at hcompare
    have hloss := I.roundCycleTerms_objective_loss q hq hc terms hlen
      (fun t ht => ⟨(hterms t ht).1.le, (hterms t ht).2.2.2, (hterms t ht).2.2.1⟩)
    rw [hcost] at hloss
    have hnum : 11 * ((q : ℝ) * ((I.m ^ 12 : ℕ) : ℝ)) ≤ B := by
      exact_mod_cast capacityUnit_loss_bound I.m B hm hqgt
    linarith only [hcompare, hloss, hnum, hB]

end MinCostFlow.Scaling.Circulation
