module

public import MinCostFlow.Scaling.GeneralScalingModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Capacity budgets for the lower-capacity reduction

For the implicit reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2,
subtracting the lower-capacity flow changes each demand by a sum of at most
`m` signed lower capacities. Thus bounded demands and lower capacities give
an explicit bound for every artificial feasibility arc. The residual bound
requires feasibility of the starting flow, as the source does.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- Each integer incidence coefficient has absolute value at most one,
including a loop, whose coefficient is zero. -/
theorem coefficient_natAbs_le (I : Instance) (e : Fin I.m) (v : Fin I.n) :
    (coefficient I e v).natAbs ≤ 1 := by
  unfold coefficient
  split <;> split <;> decide

/-- Subtracting lower capacities increases the demand bound by at most `m*U`. -/
theorem shiftedDemand_natAbs_le (I : Instance) (U : ℕ)
    (hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ U)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U) (v : Fin I.n) :
    (shiftedDemand I v).natAbs ≤ (I.m + 1) * U := by
  have hs : (∑ e, coefficient I e v * (I.edge e).lower).natAbs ≤ I.m * U := by
    apply le_trans (Int.natAbs_sum_le _ _)
    calc
      ∑ e, (coefficient I e v * (I.edge e).lower).natAbs ≤ ∑ _ : Fin I.m, U := by
        apply Finset.sum_le_sum
        intro e _
        rw [Int.natAbs_mul]
        exact le_trans (Nat.mul_le_mul (coefficient_natAbs_le I e v) (hl e))
          (by rw [Nat.one_mul])
      _ = I.m * U := by simp
  have hh := Int.natAbs_add_le (I.d v) (-(∑ e, coefficient I e v * (I.edge e).lower))
  simp only [Int.natAbs_neg] at hh
  unfold shiftedDemand
  rw [sub_eq_add_neg]
  have h := le_trans hh (Nat.add_le_add (hd v) hs)
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

/-- The original nonnegative capacities are at most twice the absolute bound. -/
theorem shiftedGraph_capacity_le (I : Instance) (hv : I.IsValid) (U : ℕ)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U) (e : Fin I.m) :
    (shiftedGraph I hv).capacity e ≤ 2 * U := by
  have hlo := hl e
  have hup := hu e
  change ((I.edge e).upper - (I.edge e).lower).toNat ≤ 2 * U
  omega

/-- All feasibility capacities fit the static budget used by the full model. -/
theorem buildFeasibilityInstance_capacity_le (I : Instance) (hv : I.IsValid) (U : ℕ)
    (hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ U)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U) :
    ∀ e, (buildFeasibilityInstance I hv).capacity e ≤ scalingCapacityBudget I U := by
  intro e
  change ((Fin.addCases (shiftedGraph I hv).capacity
    (Fin.addCases (fun v => (buildShiftedDemands I hv v).toNat)
      (fun v => (-buildShiftedDemands I hv v).toNat)) : Fin (I.m + (I.n + I.n)) → ℕ) e) ≤ _
  induction e using Fin.addCases
  · rename_i e
    simp only [Fin.addCases_left]
    have hh := shiftedGraph_capacity_le I hv U hl hu e
    change ((I.edge e).upper - (I.edge e).lower).toNat ≤ 2 * U at hh
    unfold scalingCapacityBudget
    have hp := Nat.mul_le_mul_right U (show 2 ≤ 2 * (I.m + 1) by omega)
    exact le_trans hh (Nat.le_succ_of_le hp)
  · rename_i e
    induction e using Fin.addCases <;> rename_i v
    · simp only [Fin.addCases_right, Fin.addCases_left, buildShiftedDemands_eq]
      have hh := shiftedDemand_natAbs_le I U hd hl v
      unfold scalingCapacityBudget
      simp only [Nat.mul_assoc]
      omega
    · simp only [Fin.addCases_right, buildShiftedDemands_eq]
      have hh := shiftedDemand_natAbs_le I U hd hl v
      unfold scalingCapacityBudget
      simp only [Nat.mul_assoc]
      omega

end MinCostFlow.Scaling.FlowReduction
