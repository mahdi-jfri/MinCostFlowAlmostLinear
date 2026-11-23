module

public import MinCostFlow.Scaling.CapacityRounding
public import MinCostFlow.Scaling.SolverAdapter
public import MinCostFlow.Scaling.CallLoop
import Mathlib.Tactic.Ring

/-!
# Solving a capacity-rounded instance with one bounded call

Definition C.11 and the remark following it in Chen et al.,
arXiv:2203.00671v2, divide rounded capacities by their integer rounding unit,
solve the scaled problem, and multiply the flow by that unit. This file gives
that integer function, proves the bounds on its one solver call, and proves
that its returned flow is a feasible circulation in the original graph.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The instance obtained by dividing the corrected rounded capacities by
the integer rounding unit. -/
abbrev scaledRoundedInstance (I : Circulation) (B : ℕ) : Circulation :=
  { I with capacity := fun e => scaledCapacity I.m B (I.capacity e) }

/-- Zero magnitude needs no solve. Positive magnitude uses one bounded-capacity
call and multiplies the integral result by the rounding unit. -/
def solveCapacityRoundedModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (B : ℕ) : CallResult (Fin I.m → ℤ) :=
  if B = 0 then ⟨fun _ => 0, [], 1⟩
  else
    let J := I.scaledRoundedInstance B
    let f := solveWithZeroCapacities solve J
    let unit := capacityUnit I.m B
    ⟨(fun e => (unit : ℤ) * f e), [J.positiveInstance], 40 * (I.m + 1)⟩

/-- The scaled rounded solve makes at most one supplied-solver call. -/
theorem solveCapacityRoundedModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (B : ℕ) :
    (solveCapacityRoundedModel solve I B).calls.length ≤ 1 := by
  unfold solveCapacityRoundedModel
  split <;> simp

/-- The supplied-solver instance has exactly the original number of edges. -/
theorem solveCapacityRoundedModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (B : ℕ) :
    ∀ J ∈ (solveCapacityRoundedModel solve I B).calls, J.m = I.m := by
  unfold solveCapacityRoundedModel
  split
  · simp
  · intro J hJ
    have he := List.mem_singleton.mp hJ
    subst J
    rfl

/-- Every actual call satisfies the `m^40` capacity bound, including `m=1`.
The zero-edge case has no coordinates to check. -/
theorem solveCapacityRoundedModel_capacities
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (B : ℕ) :
    ∀ J ∈ (solveCapacityRoundedModel solve I B).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  unfold solveCapacityRoundedModel
  split
  · simp
  · rename_i hB
    intro J hJ e
    have he := List.mem_singleton.mp hJ
    subst J
    have hm : 0 < I.m := by
      have hi : e.val < I.m := e.isLt
      omega
    have hpos : 1 ≤ I.m ^ 40 := Nat.pow_pos hm
    exact (I.scaledRoundedInstance B).positiveInstance_capacitiesBounded (I.m ^ 40) hpos
      (fun k => scaledCapacity_le I.m B (I.capacity k) hm (Nat.pos_of_ne_zero hB)) e

/-- The supplied solver sees the same costs and exact polynomial bound. -/
theorem solveCapacityRoundedModel_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (B : ℕ) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (solveCapacityRoundedModel solve I B).calls, J.CostsBounded (J.m ^ 10) := by
  unfold solveCapacityRoundedModel
  split
  · simp
  · intro J hJ
    have he := List.mem_singleton.mp hJ
    subst J
    exact positiveInstance_costsBounded _ _ hc

/-- Assembly, scaling, and reconstruction reserve at most `40*(m+1)` other
integer operations in the counted model. -/
theorem solveCapacityRoundedModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (B : ℕ) :
    (solveCapacityRoundedModel solve I B).work ≤ 40 * (I.m + 1) := by
  unfold solveCapacityRoundedModel
  split
  · dsimp only
    omega
  · exact le_rfl

/-- Multiplying a flow by a scalar multiplies every vertex balance by that scalar. -/
theorem balance_const_mul (I : Circulation) (q : ℝ) (f : Fin I.m → ℝ) (v : Fin I.n) :
    I.balance (fun e => q * f e) v = q * I.balance f v := by
  unfold balance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The actual rounded-solver result is a feasible circulation in the original
graph. Only the source's polynomial-cost, polynomial-capacity primal solver
specification is used. -/
theorem solveCapacityRoundedModel_feasible
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (B : ℕ) (hc : I.CostsBounded (I.m ^ 10)) :
    I.Feasible (fun e => ((solveCapacityRoundedModel solve I B).value e : ℝ)) := by
  by_cases hB : B = 0
  · simp only [solveCapacityRoundedModel, hB, ↓reduceIte, Int.cast_zero]
    exact I.zero_feasible
  · let J := I.scaledRoundedInstance B
    have hcap : ∀ e, 1 ≤ J.positiveInstance.capacity e ∧
        J.positiveInstance.capacity e ≤ I.m ^ 40 := by
      intro e
      have hm : 0 < I.m := by have hi : e.val < I.m := e.isLt; omega
      exact J.positiveInstance_capacitiesBounded (I.m ^ 40) (Nat.pow_pos hm)
        (fun k => scaledCapacity_le I.m B (I.capacity k) hm (Nat.pos_of_ne_zero hB)) e
    have hopt := solveWithZeroCapacities_of_optimal solve J
      (hsolve J.positiveInstance (J.positiveInstance_costsBounded _ hc) hcap)
    let f := solveWithZeroCapacities solve J
    let q := capacityUnit I.m B
    have hf : J.Feasible (fun e => (f e : ℝ)) := hopt.1
    have hscaled : I.Feasible (fun e => (q : ℝ) * (f e : ℝ)) := by
      constructor
      · intro v
        rw [balance_const_mul]
        change (q : ℝ) * J.balance (fun e => (f e : ℝ)) v = 0
        rw [hf.1 v, mul_zero]
      · intro e
        constructor
        · exact mul_nonneg (Nat.cast_nonneg _) (hf.2 e).1
        · have hm := mul_le_mul_of_nonneg_left (hf.2 e).2 (Nat.cast_nonneg q)
          have hcapa : (q : ℝ) * (J.capacity e : ℝ) ≤ (I.capacity e : ℝ) := by
            have h := roundedCapacity_le I.m B (I.capacity e)
            exact_mod_cast h
          exact le_trans hm hcapa
    simpa only [solveCapacityRoundedModel, hB, ↓reduceIte, Int.cast_mul,
      Int.cast_natCast] using hscaled

end MinCostFlow.Scaling.Circulation
