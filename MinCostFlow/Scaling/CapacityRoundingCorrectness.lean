module

public import MinCostFlow.Scaling.OneEdgeCapacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness of the capacity-rounding approximation

Lemma C.12 used by Lemma C.9 of Chen et al., arXiv:2203.00671v2,
Appendix C, states that solving the capacity-rounded instance gives an
integral `1.1` approximation. The coefficient-rounding proof covers every
`m >= 2`; one edge is exact because its negative optimum saturates a
cost-minus-one loop. The theorem below joins these cases without a hidden
large-instance assumption, using the corrected Definition C.11 clipping.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Lemma C.12 (Appendix C), for all `m >= 1`: the rounded optimum is an
integral feasible `1.1` approximation. The negative-cost ratio is written
without division. Clipping is rounded to a multiple as described in C.11. -/
theorem lemma_C_12 (I : Circulation) (B : ℕ) (hm : 0 < I.m) (hBpos : 0 < B)
    (hc : I.CostsBounded (I.m ^ 10)) (fstar : Fin I.m → ℝ) (hfstar : I.Optimal fstar)
    (hB : (B : ℝ) ≤ -I.objective fstar)
    (happrox : -I.objective fstar ≤ ((I.m ^ 12 : ℕ) : ℝ) * B)
    (fB : Fin I.m → ℤ)
    (hfB : (I.capacityRounded B).Optimal (fun e => (fB e : ℝ))) :
    I.Feasible (fun e => (fB e : ℝ)) ∧
      11 * I.objective (fun e => (fB e : ℝ)) ≤ 10 * I.objective fstar := by
  by_cases hmone : I.m = 1
  · have hupper : -I.objective fstar ≤ (B : ℝ) := by
      simpa only [hmone, one_pow, Nat.cast_one, one_mul] using happrox
    have hobj : I.objective fstar = -(B : ℝ) := by linarith only [hB, hupper]
    have hneg : I.objective fstar < 0 := by
      have hb : (0 : ℝ) < B := Nat.cast_pos.mpr hBpos
      linarith only [hb, hobj]
    have hc' : I.CostsBounded 1 := by simpa only [hmone, one_pow] using hc
    have hcapacity (e : Fin I.m) : (I.capacityRounded B).capacity e = I.capacity e := by
      have hh := (I.one_edge_negative_optimum hmone hc' fstar hfstar hneg e).2.2
      have heq : I.capacity e = B := by
        have hr : (I.capacity e : ℝ) = B := by linarith only [hh, hobj]
        exact_mod_cast hr
      change roundedCapacity I.m B (I.capacity e) = I.capacity e
      rw [hmone, heq]
      exact roundedCapacity_one_self B
    have hfeas : (I.capacityRounded B).Feasible fstar := by
      refine ⟨hfstar.1.1, ?_⟩
      intro e
      rw [hcapacity e]
      exact hfstar.1.2 e
    have hcompare := hfB.2 fstar hfeas
    change I.objective (fun e => (fB e : ℝ)) ≤ I.objective fstar at hcompare
    exact ⟨I.capacityRounded_feasible B _ hfB.1, by linarith only [hcompare, hneg]⟩
  · exact I.lemma_C_12_of_two_le_edges B (by omega) hc fstar hfstar hB happrox fB hfB

end MinCostFlow.Scaling.Circulation
