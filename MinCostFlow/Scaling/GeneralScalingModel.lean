module

public import MinCostFlow.Scaling.CostCapacityModel
public import MinCostFlow.Scaling.MeasuredReduction
import Mathlib.Tactic.Ring

/-!
# The counted general-flow scaling procedure

The reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2, uses at most
two circulation solves. Here each is implemented by cost and capacity scaling.
The capacity budget includes the demands introduced by subtracting lower
capacities. All calls are explicit integer functions. This file proves the
primitive call count and input bounds independently of final optimality.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- The shifted demands have size at most `(m+1)*U`; the extra factor two
also covers upper-minus-lower capacities. Padding handles zero bounds. -/
def scalingCapacityBudget (I : Instance) (U : ℕ) : ℕ := 2 * (I.m + 1) * U + 1

/-- General minimum-cost flow by two pruned circulation reductions, each
implemented by the composed cost and capacity loops. -/
def generalScalingModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : CallResult (Option (Fin I.m → ℤ)) :=
  checkedMeasured
    (fun J => costCapacityModel solve J (max C 1) (scalingCapacityBudget I U)) I hv

/-- Every primitive solver input has at most `72*m` edge slots. -/
theorem generalScalingModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    ∀ J ∈ (generalScalingModel solve I hv C U).calls, J.m ≤ 72 * I.m := by
  unfold generalScalingModel
  rw [checkedMeasured_calls]
  apply CallResult.expand_instances
  intro J hJ K hK
  have hj := checkedReduction_edges
    (fun J => (costCapacityModel solve J (max C 1) (scalingCapacityBudget I U)).value)
    I hv J hJ
  have hk := costCapacityModel_edges solve J (max C 1) (scalingCapacityBudget I U) K hK
  omega

/-- At most two circulation solves, each with the three logarithmic factors.
The factors retain the explicit constant-size intermediate graphs. -/
theorem generalScalingModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    (generalScalingModel solve I hv C U).calls.length ≤
      11520 * (Nat.clog 2 (3 * I.m + 1) + 1) *
        (Nat.clog 2 (3 * I.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1) *
        Nat.clog 2 (max C 1 + 2) := by
  unfold generalScalingModel
  rw [checkedMeasured_calls]
  let inner := fun J => costCapacityModel solve J (max C 1) (scalingCapacityBudget I U)
  let r := checkedReduction (fun J => (inner J).value) I hv
  have hi : ∀ J ∈ r.calls, (inner J).calls.length ≤
      5760 * (Nat.clog 2 (3 * I.m + 1) + 1) *
        (Nat.clog 2 (3 * I.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1) *
        Nat.clog 2 (max C 1 + 2) := by
    intro J hJ
    have hj := checkedReduction_edges (fun J => (inner J).value) I hv J hJ
    have hl := Nat.clog_mono_right (b := 2) (Nat.add_le_add_right hj 1)
    exact le_trans (costCapacityModel_calls solve J _ _)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1))
        (Nat.add_le_add_right (Nat.add_le_add_right hl _) 1)))
  have hh := CallResult.expand_calls inner r _ hi
  have hr := checkedReduction_calls (fun J => (inner J).value) I hv
  have hp := Nat.mul_le_mul_right
    (5760 * (Nat.clog 2 (3 * I.m + 1) + 1) *
      (Nat.clog 2 (3 * I.m + 1) + Nat.clog 2 (scalingCapacityBudget I U + 1) + 1) *
      Nat.clog 2 (max C 1 + 2)) hr
  have he (a b c : ℕ) : 2 * (5760 * a * b * c) = 11520 * a * b * c := by ring
  rw [he] at hp
  exact le_trans hh hp

private theorem reduction_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C : ℕ) (hc : ∀ e, (I.edge e).cost.natAbs ≤ C) :
    ∀ J ∈ (reduceWithTrace solve I hv).calls, J.CostsBounded (max C 1) := by
  have hp : (buildFeasibilityInstance I hv).CostsBounded (max C 1) := by
    intro e
    change ((Fin.addCases (fun _ : Fin I.m => (0 : ℤ))
      (fun _ : Fin (I.n + I.n) => -1) : Fin (I.m + (I.n + I.n)) → ℤ) e).natAbs ≤ max C 1
    induction e using Fin.addCases
    · simp only [Fin.addCases_left, Int.natAbs_zero]
      exact Nat.zero_le _
    · simp only [Fin.addCases_right]
      exact le_max_right _ _
  have hr (f : Fin I.m → ℤ) :
      ((shiftedGraph I hv).residual f).CostsBounded (max C 1) :=
    Circulation.residual_costsBounded _ _ _ (fun e => le_trans (hc e) (le_max_left _ _))
  unfold reduceWithTrace
  split
  · dsimp only
    split
    · intro J hJ
      rcases List.mem_cons.mp hJ with h | h
      · subst J; exact hp
      · have he := List.mem_singleton.mp h
        subst J; exact hr _
    · intro J hJ
      have he := List.mem_singleton.mp hJ
      subst J; exact hp
  · simp

/-- Each actual primitive call has polynomially bounded costs and positive
polynomial capacities, assuming only the original cost bound. -/
theorem generalScalingModel_inputs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hc : ∀ e, (I.edge e).cost.natAbs ≤ C) :
    ∀ J ∈ (generalScalingModel solve I hv C U).calls,
      J.CostsBounded (J.m ^ 10) ∧ ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  unfold generalScalingModel
  rw [checkedMeasured_calls]
  apply CallResult.expand_instances
  intro J hJ K hK
  apply costCapacityModel_inputs solve J (max C 1) (scalingCapacityBudget I U) _ K hK
  unfold checkedReduction at hJ
  split at hJ
  · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hJ
    have hl := reduction_costs _ I hv C hc L hL
    exact fun e => hl (L.positiveIndex e)
  · cases hJ

end MinCostFlow.Scaling.FlowReduction
