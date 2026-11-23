module

public import MinCostFlow.Scaling.ReductionCapacityBounds
public import MinCostFlow.Scaling.CostCapacityCorrectness
public import MinCostFlow.Scaling.DemandBoundCheck
import Mathlib.Tactic.NormNum

/-!
# The arbitrary-demand conclusion of scaling

Lemma C.1 of Chen et al., arXiv:2203.00671v2, Appendix C, uses circulation
scaling to solve minimum-cost flow. The feasibility call has bounded artificial
capacities. Only after it finds a feasible flow does the algorithm form the
residual optimization call, whose capacities satisfy the same static budget.
Both calls prune zero-capacity arcs and restore their integer coordinates.
-/

public section
namespace MinCostFlow.Scaling.FlowReduction

private theorem pruned_composition_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (J : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hc : J.CostsBounded C) (hu : ∀ e, J.capacity e ≤ U) :
    J.Optimal (fun e => (Circulation.solvePruned
      (fun K => (costCapacityModel solve K C U).value) J e : ℝ)) := by
  unfold Circulation.solvePruned
  rw [J.scatterPositive_cast]
  apply J.scatterPositive_optimal
  exact costCapacityModel_optimal solve hsolve J.withoutZeroEdges C U hU
    (fun e => hc (J.positiveIndex e)) (fun e => hu (J.positiveIndex e))

/-- Correctness of the full general-flow model under its internal demand
bound, using the bounded solver only on the two actual reductions. -/
theorem generalScalingModel_correct
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hc : ∀ e, (I.edge e).cost.natAbs ≤ C)
    (hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ U)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U) :
    (∀ f, (generalScalingModel solve I hv C U).value = some f →
      I.IsMinCostFlow (fun e => (f e : ℝ))) ∧
    ((generalScalingModel solve I hv C U).value = none → ∀ f, ¬ I.IsFeasible f) := by
  unfold generalScalingModel
  rw [checkedMeasured_value]
  by_cases hcheck : isolatedCheck I hv = true
  · simp only [checkedReduction, hcheck, ↓reduceIte, reduceWithTrace_value]
    apply reduceToCirculation_correct_of_calls
    · apply pruned_composition_optimal solve hsolve _ _ _ (by unfold scalingCapacityBudget; omega)
      · intro e
        change ((Fin.addCases (fun _ : Fin I.m => (0 : ℤ))
          (fun _ : Fin (I.n + I.n) => -1) : Fin (I.m + (I.n + I.n)) → ℤ) e).natAbs ≤ max C 1
        induction e using Fin.addCases
        · simp only [Fin.addCases_left, Int.natAbs_zero]; exact Nat.zero_le _
        · simp only [Fin.addCases_right]; exact le_max_right _ _
      · exact buildFeasibilityInstance_capacity_le I hv U hd hl hu
    · intro f hf
      apply pruned_composition_optimal solve hsolve _ _ _ (by unfold scalingCapacityBudget; omega)
      · apply Circulation.residual_costsBounded
        intro e
        exact le_trans (hc e) (le_max_left _ _)
      · have hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper := by
          intro e
          exact (Int.cast_le (R := ℝ)).mp (le_trans (hf.2 e).1 (hf.2 e).2)
        have hb := ((feasible_restore_iff I hv hcap _).mp hf).2
        apply (shiftedGraph I hv).residual_capacities_le f hb (scalingCapacityBudget I U)
        intro e
        have hh := shiftedGraph_capacity_le I hv U hl hu e
        have hp := Nat.mul_le_mul_right U (show 2 ≤ 2 * (I.m + 1) by omega)
        exact hh.trans (hp.trans (Nat.le_succ _))
  · have hfalse := Bool.eq_false_iff.mpr hcheck
    simp only [checkedReduction, hfalse, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(by intro f h; cases h), fun _ => infeasible_of_isolatedCheck I hv hfalse⟩

/-- Lemma C.1 (Chen et al., arXiv:2203.00671v2, Appendix C): arbitrary
integral demands, costs, and lower and upper capacities are reduced to the
polynomial-cost, polynomial-capacity integral circulation solver. The result
is optimal against real flows or certifies infeasibility. The explicit nested
call and work counts are proved in `GeneralScalingLogs`. -/
theorem lemma_C_1
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hc : ∀ e, (I.edge e).cost.natAbs ≤ C)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U) :
    (∀ f, (arbitraryDemandScalingModel solve I hv C U).value = some f →
      I.IsMinCostFlow (fun e => (f e : ℝ))) ∧
    ((arbitraryDemandScalingModel solve I hv C U).value = none → ∀ f, ¬ I.IsFeasible f) := by
  unfold arbitraryDemandScalingModel
  split
  · rename_i hcheck
    apply generalScalingModel_correct solve hsolve I hv C ((I.m + 1) * U) hc
    · intro v
      have hh := (demandBoundCheck_iff I U).mp hcheck v
      exact hh.trans (Nat.mul_le_mul_right U (Nat.le_succ _))
    · intro e
      exact (hl e).trans (by rw [Nat.add_mul, Nat.one_mul]; omega)
    · intro e
      exact (hu e).trans (by rw [Nat.add_mul, Nat.one_mul]; omega)
  · rename_i hcheck
    exact ⟨(by intro f h; cases h), fun _ =>
      infeasible_of_demandBoundCheck I U hl hu (Bool.eq_false_iff.mpr hcheck)⟩

end MinCostFlow.Scaling.FlowReduction
