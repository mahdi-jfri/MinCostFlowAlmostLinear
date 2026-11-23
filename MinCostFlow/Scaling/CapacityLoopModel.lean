module

public import MinCostFlow.Scaling.ApproximationModel
public import MinCostFlow.Scaling.CapacitySolverModel
public import MinCostFlow.Scaling.IterationBounds
public import MinCostFlow.Scaling.ResidualBounds
import Mathlib.Tactic.Ring

/-!
# Integer capacity-scaling loop and solver-call bounds

Algorithm CapacityScaling in Appendix C of Chen et al., arXiv:2203.00671v2,
starts at zero circulation. Each iteration computes a bottleneck candidate on
the residual graph. A zero value stops the loop. Otherwise the algorithm solves
the capacity-rounded residual instance and augments the current integral flow.
This file gives those integer functions and their solver-instance bounds and
operation counters. Approximation progress and final optimality are separate.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Integral flow and the early-stop flag of the capacity loop. -/
structure CapacityState (I : Circulation) where
  flow : Fin I.m → ℤ
  stopped : Bool

namespace CapacityState

/-- The initial zero circulation, before the early-stop test. -/
def initial (I : Circulation) : CapacityState I := ⟨fun _ => 0, false⟩

/-- A uniform other-work budget for one iteration, including residual assembly,
search, cycle extraction, the rounded solve, and the flow update. -/
def workBudget (I : Circulation) : ℕ :=
  let B := I.m + I.m
  20 * (I.m + I.n + 1) +
    (120 * (Nat.clog 2 (B + 1) + 1) * (B + 1) + 400 * (B + I.n + 1)) +
    40 * (B + 1)

/-- One capacity-scaling iteration. A previously stopped state makes no calls. -/
def step (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (s : CapacityState I) : CallResult (CapacityState I) :=
  if s.stopped then ⟨s, [], 1⟩
  else
    let R := I.residual s.flow
    let candidate := polyApproxModel solve R
    if candidate.value.magnitude = 0 then
      ⟨{ s with stopped := true }, candidate.calls,
        20 * (I.m + I.n + 1) + candidate.work⟩
    else
      let delta := R.solveCapacityRoundedModel solve candidate.value.magnitude
      ⟨{ flow := fun e => s.flow e + delta.value (Fin.castAdd I.m e) -
          delta.value (Fin.natAdd I.m e), stopped := false },
        candidate.calls ++ delta.calls,
        20 * (I.m + I.n + 1) + candidate.work + delta.work⟩

/-- An iteration makes at most the binary-search budget plus one rounded call. -/
theorem step_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    {I : Circulation} (s : CapacityState I) :
    (step solve s).calls.length ≤ Nat.clog 2 (I.m + I.m + 1) + 1 := by
  unfold step
  split
  · simp
  · dsimp only
    have ha := polyApproxModel_calls solve (I.residual s.flow)
    split
    · dsimp only
      exact le_trans ha (Nat.le_succ _)
    · dsimp only
      rw [List.length_append]
      have hd := (I.residual s.flow).solveCapacityRoundedModel_calls solve
        (polyApproxModel solve (I.residual s.flow)).value.magnitude
      exact Nat.add_le_add ha hd

/-- Every iteration call uses exactly `2*m` edge slots. -/
theorem step_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    {I : Circulation} (s : CapacityState I) :
    ∀ J ∈ (step solve s).calls, J.m = 2 * I.m := by
  unfold step
  split
  · simp
  · dsimp only
    split
    · intro J hJ
      have h := polyApproxModel_edges solve (I.residual s.flow) J hJ
      exact h.trans (I.residual_edges s.flow)
    · intro J hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · have h := polyApproxModel_edges solve (I.residual s.flow) J hJ
        exact h.trans (I.residual_edges s.flow)
      · have h := (I.residual s.flow).solveCapacityRoundedModel_edges solve _ J hJ
        exact h.trans (I.residual_edges s.flow)

/-- Every actual call satisfies the polynomial cost bound of Lemma C.9. -/
theorem step_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    {I : Circulation} (s : CapacityState I) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (step solve s).calls, J.CostsBounded (J.m ^ 10) := by
  have hr := I.residual_polynomialCosts s.flow hc
  unfold step
  split
  · simp
  · dsimp only
    split
    · exact polyApproxModel_costs solve (I.residual s.flow) hr
    · intro J hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · exact polyApproxModel_costs solve (I.residual s.flow) hr J hJ
      · exact (I.residual s.flow).solveCapacityRoundedModel_costs solve _ hr J hJ

/-- Every actual call has positive capacities bounded by its own `m^40`. -/
theorem step_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    {I : Circulation} (s : CapacityState I) :
    ∀ J ∈ (step solve s).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  have ha : ∀ J ∈ (polyApproxModel solve (I.residual s.flow)).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
    intro J hJ e
    rw [polyApproxModel_capacities solve (I.residual s.flow) J hJ e]
    have hm : 0 < J.m := by have h := e.isLt; omega
    exact ⟨le_rfl, Nat.pow_pos hm⟩
  unfold step
  split
  · simp
  · dsimp only
    split
    · exact ha
    · intro J hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · exact ha J hJ
      · exact (I.residual s.flow).solveCapacityRoundedModel_capacities solve _ J hJ

/-- The reserved counter of every iteration is bounded by the same expression. -/
theorem step_work (solve : (J : Circulation) → Fin J.m → ℤ)
    {I : Circulation} (s : CapacityState I) : (step solve s).work ≤ workBudget I := by
  unfold step
  split
  · dsimp only [workBudget]
    omega
  · dsimp only
    have ha := polyApproxModel_work solve (I.residual s.flow)
    split
    · dsimp only
      apply le_trans (Nat.add_le_add_left ha _)
      change _ ≤ _ + 40 * (I.m + I.m + 1)
      exact Nat.le_add_right _ _
    · dsimp only
      have hd := (I.residual s.flow).solveCapacityRoundedModel_work solve
        (polyApproxModel solve (I.residual s.flow)).value.magnitude
      exact Nat.add_le_add (Nat.add_le_add_left ha _) hd

/-- A simpler product bound for the iteration's padded logarithmic work budget. -/
theorem workBudget_le (I : Circulation) :
    workBudget I ≤ 2000 * (Nat.clog 2 (I.m + I.m + 1) + 1) * (I.m + I.n + 1) := by
  unfold workBudget
  ring_nf
  omega

end CapacityState

/-- The explicit finite capacity loop, retaining the source's early-stop flag. -/
def capacityLoop (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) : CallResult (CapacityState I) :=
  CallResult.forRounds (CapacityState.step solve) (capacityRounds I.m U) (CapacityState.initial I)

/-- The total solver-call count is the product of search and outer-loop budgets. -/
theorem capacityLoop_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    (capacityLoop solve I U).calls.length ≤
      capacityRounds I.m U * (Nat.clog 2 (I.m + I.m + 1) + 1) :=
  CallResult.forRounds_calls _ _ (CapacityState.step_calls solve) _ _

/-- Every recorded solver input has exactly `2*m` edges. -/
theorem capacityLoop_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    ∀ J ∈ (capacityLoop solve I U).calls, J.m = 2 * I.m :=
  CallResult.forRounds_instances _ _ (CapacityState.step_edges solve) _ _

/-- The whole capacity loop uses only polynomial-cost solver instances. -/
theorem capacityLoop_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (capacityLoop solve I U).calls, J.CostsBounded (J.m ^ 10) :=
  CallResult.forRounds_instances _ _ (fun s => CapacityState.step_costs solve s hc) _ _

/-- The whole loop's calls satisfy precisely the source's capacity specification. -/
theorem capacityLoop_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    ∀ J ∈ (capacityLoop solve I U).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 :=
  CallResult.forRounds_instances _ _ (CapacityState.step_capacities solve) _ _

/-- The other-work counter is the sum of uniform iteration budgets and control. -/
theorem capacityLoop_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    (capacityLoop solve I U).work ≤ capacityRounds I.m U * (CapacityState.workBudget I + 1) :=
  CallResult.forRounds_work _ _ (CapacityState.step_work solve) _ _

end MinCostFlow.Scaling
