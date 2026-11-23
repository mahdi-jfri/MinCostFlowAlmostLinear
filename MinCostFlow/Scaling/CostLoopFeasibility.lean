module

public import MinCostFlow.Scaling.CostLoopBounds
import Mathlib.Tactic.Ring

/-!
# Valid solver calls throughout cost scaling

The instance bounds in Appendix C of Chen et al., arXiv:2203.00671v2, must
hold on every loop iteration. A rounded instance keeps the residual capacities. Therefore its primal solution is a feasible residual augmentation,
regardless of whether the extracted potential is already known correct. This
file proves feasibility through the actual loop and hence proves the capacity
bound for every recorded solver call using only the bounded primal solver's
specification.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Cost rounding omits edges but never increases residual capacities. -/
theorem CostState.roundedInstance_capacity_le {I : Circulation} (C : ℕ)
    (s : CostState I) (e : Fin (I.m + I.m)) :
    (s.roundedInstance C).capacity e ≤ (I.residual s.flow).capacity e := by
  exact le_rfl

/-- The primal flow update preserves feasibility with exactly the polynomial
cost and bounded-capacity solver specification of the scaling reduction. -/
theorem CostState.step_flow_feasible
    (solve : (J : Circulation) → Fin J.m → ℤ) (C U : ℕ) (hU : 1 ≤ U)
    {I : Circulation}
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (s : CostState I) (hf : I.Feasible (fun e => (s.flow e : ℝ)))
    (hu : ∀ e, I.capacity e ≤ U) :
    I.Feasible (fun e => ((CostState.step solve C s).value.flow e : ℝ)) := by
  let J := s.roundedInstance C
  let delta := Circulation.solveWithZeroCapacities solve J
  have hcap : ∀ e, J.capacity e ≤ max U (I.n + 1) := by
    intro e
    exact le_trans (s.roundedInstance_capacity_le C e)
      (le_trans (I.residual_capacities_le s.flow hf.2 U hu e) (le_max_left _ _))
  have hdelta := Circulation.solveWithZeroCapacities_correct solve (max U (I.n + 1))
    (le_trans hU (le_max_left _ _)) hsolve J (s.roundedInstance_polynomialCosts C) hcap
  have hr : (I.residual s.flow).Feasible (fun e => (delta e : ℝ)) := by
    constructor
    · exact hdelta.1.1
    · intro e
      exact ⟨(hdelta.1.2 e).1, le_trans (hdelta.1.2 e).2
        (by exact_mod_cast s.roundedInstance_capacity_le C e)⟩
  have he : (fun e => ((CostState.step solve C s).value.flow e : ℝ)) =
      I.augment s.flow (fun e => (delta e : ℝ)) := by
    funext e
    simp only [CostState.step, Circulation.augment, Circulation.project, Int.cast_add,
      Int.cast_sub]
    ring
  rw [he]
  exact I.augment_feasible s.flow hf _ hr

/-- Every state reached by the integer cost loop has a feasible flow. -/
theorem costLoop_flow_feasible
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hu : ∀ e, I.capacity e ≤ U) :
    I.Feasible (fun e => ((costLoop solve I C).value.flow e : ℝ)) := by
  apply CallResult.forRounds_invariant (CostState.step solve C)
    (fun s : CostState I => I.Feasible (fun e => (s.flow e : ℝ)))
    (fun s hs => CostState.step_flow_feasible solve C U hU hsolve s hs hu)
  simpa only [CostState.initial, Int.cast_zero] using I.zero_feasible

/-- All actual cost-loop calls have positive capacities bounded by the explicit
budget `max U (n+1)`. No separate feasibility assumption on loop states remains. -/
theorem costLoop_capacities
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hu : ∀ e, I.capacity e ≤ U) :
    ∀ J ∈ (costLoop solve I C).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1) := by
  apply CallResult.forRounds_instances_of_invariant (CostState.step solve C)
    (fun s : CostState I => I.Feasible (fun e => (s.flow e : ℝ)))
    (fun s hs => CostState.step_flow_feasible solve C U hU hsolve s hs hu)
    (fun J => ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1))
    (fun s hs => CostState.step_capacities solve C U hU s hs.2 hu)
  simpa only [CostState.initial, Int.cast_zero] using I.zero_feasible

/-- The denominator power stored by the loop is exactly the required power of
two, so it never vanishes. -/
theorem costLoop_power (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    (costLoop solve I C).value.power = 2 ^ costRounds I.n C := by
  have h : ∀ t : ℕ, (CallResult.forRounds (CostState.step solve C) t
      (CostState.initial I)).value.power = 2 ^ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change 2 * (CallResult.forRounds (CostState.step solve C) t
        (CostState.initial I)).value.power = 2 ^ (t + 1)
      rw [ih, Nat.pow_succ, Nat.mul_comm]
  exact h _

end MinCostFlow.Scaling
