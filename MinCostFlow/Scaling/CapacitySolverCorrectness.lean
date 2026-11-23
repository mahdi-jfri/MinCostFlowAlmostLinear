module

public import MinCostFlow.Scaling.CapacitySolverModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Optimality of the scaled capacity-rounded solve

The remark after Definition C.11 and the proof of Lemma C.12 in Chen et al.,
arXiv:2203.00671v2, Appendix C, divide all rounded capacities by a known
positive integer unit. Dividing a real comparison flow by that unit preserves
feasibility in the scaled graph. Thus multiplying the exact integral scaled
optimum back up gives an exact integral optimum of the rounded graph.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Scalar multiplication also scales the objective. -/
theorem objective_const_mul (I : Circulation) (q : ℝ) (f : Fin I.m → ℝ) :
    I.objective (fun e => q * f e) = q * I.objective f := by
  simp only [objective, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The one-call model returns an exact optimum for the corrected rounded
capacities, using only the source's bounded primal solver specification. -/
theorem solveCapacityRoundedModel_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (B : ℕ) (hB : 0 < B) (hc : I.CostsBounded (I.m ^ 10)) :
    (I.capacityRounded B).Optimal
      (fun e => ((I.solveCapacityRoundedModel solve B).value e : ℝ)) := by
  let J := I.scaledRoundedInstance B
  let f := solveWithZeroCapacities solve J
  let q := capacityUnit I.m B
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (capacityUnit_pos _ _)
  have hmem : J.positiveInstance ∈ (I.solveCapacityRoundedModel solve B).calls := by
    simp only [solveCapacityRoundedModel, Nat.ne_of_gt hB, ↓reduceIte]
    exact List.mem_cons_self
  have hf : J.Optimal (fun e => (f e : ℝ)) := by
    apply solveWithZeroCapacities_of_optimal
    exact hsolve J.positiveInstance
      (I.solveCapacityRoundedModel_costs solve B hc _ hmem)
      (I.solveCapacityRoundedModel_capacities solve B _ hmem)
  have hcap (e : Fin I.m) : ((I.capacityRounded B).capacity e : ℝ) =
      (q : ℝ) * (J.capacity e : ℝ) := by
    change ((capacityUnit I.m B * scaledCapacity I.m B (I.capacity e) : ℕ) : ℝ) = _
    exact Nat.cast_mul _ _
  have hcast : (fun e : Fin (I.capacityRounded B).m => ((I.solveCapacityRoundedModel solve B).value e : ℝ)) =
      fun e : Fin (I.capacityRounded B).m => (q : ℝ) * (f e : ℝ) := by
    funext e
    simp only [solveCapacityRoundedModel, Nat.ne_of_gt hB, ↓reduceIte, Int.cast_mul, Int.cast_natCast]
    rfl
  rw [hcast]
  constructor
  · constructor
    · intro v
      rw [balance_const_mul]
      change (q : ℝ) * J.balance (fun e => (f e : ℝ)) v = 0
      rw [hf.1.1 v, mul_zero]
    · intro e
      refine ⟨mul_nonneg hq.le (hf.1.2 e).1, ?_⟩
      rw [hcap e]
      exact mul_le_mul_of_nonneg_left (hf.1.2 e).2 hq.le
  · intro h hh
    have hnorm : J.Feasible (fun e => h e / (q : ℝ)) := by
      constructor
      · intro v
        simp only [balance, ← mul_div_assoc, ← Finset.sum_div]
        change (I.capacityRounded B).balance h v / (q : ℝ) = 0
        rw [hh.1 v, zero_div]
      · intro e
        refine ⟨div_nonneg (hh.2 e).1 hq.le, ?_⟩
        apply (div_le_iff₀ hq).mpr
        have hb := (hh.2 e).2
        rw [hcap e] at hb
        simpa only [mul_comm] using hb
    have hcompare := mul_le_mul_of_nonneg_left (hf.2 _ hnorm) hq.le
    have hobj : J.objective (fun e => h e / (q : ℝ)) =
        (I.capacityRounded B).objective h / (q : ℝ) := by
      simp only [objective, ← mul_div_assoc, ← Finset.sum_div]
      rfl
    rw [hobj, mul_div_cancel₀ _ (ne_of_gt hq)] at hcompare
    rw [objective_const_mul]
    exact hcompare

end MinCostFlow.Scaling.Circulation
