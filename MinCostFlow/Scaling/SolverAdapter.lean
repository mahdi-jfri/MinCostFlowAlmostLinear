module

public import MinCostFlow.Scaling.PositiveCapacities

/-!
# Calling a bounded-cost integral solver

The solver parameter in Lemma C.3 of Chen et al., arXiv:2203.00671v2, returns
an integral exact optimum when costs are `m^10`-bounded and positive capacities
are bounded by `U`. The adapter below makes one call under exactly those
conditions, after replacing zero-capacity slots with harmless loops. It returns
an integral optimum on the original graph, with the same number of edge slots.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The bound on integral edge costs used by Appendix C. -/
def CostsBounded (I : Circulation) (C : ℕ) : Prop :=
  ∀ e, (I.cost e).natAbs ≤ C

/-- Replacing zero-capacity slots does not increase any cost bound. -/
theorem positiveInstance_costsBounded (I : Circulation) (C : ℕ)
    (hc : I.CostsBounded C) : I.positiveInstance.CostsBounded C := by
  intro e
  by_cases h : I.capacity e = 0
  · simp only [h, ↓reduceIte, Int.natAbs_zero]
    exact Nat.zero_le _
  · simpa only [positiveInstance, h, ↓reduceIte] using hc e

/-- The transformed capacities lie in `1,...,U`, as required by the solver. -/
theorem positiveInstance_capacitiesBounded (I : Circulation) (U : ℕ)
    (hU : 1 ≤ U) (hu : ∀ e, I.capacity e ≤ U) :
    ∀ e, 1 ≤ I.positiveInstance.capacity e ∧ I.positiveInstance.capacity e ≤ U := by
  intro e
  refine ⟨I.positiveInstance_capacity_pos e, ?_⟩
  by_cases h : I.capacity e = 0
  · simpa only [positiveInstance, h, ↓reduceIte] using hU
  · simpa only [positiveInstance, h, ↓reduceIte] using hu e

/-- One bounded-cost solver call, followed by erasing the dummy-loop flows. -/
def solveWithZeroCapacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : Fin I.m → ℤ :=
  let f := solve I.positiveInstance
  fun e => if I.capacity e = 0 then 0 else f e

/-- Correctness of the adapter from optimality of its one actual positive-capacity
call. This form also supports capacity bounds depending on the call's edge count. -/
theorem solveWithZeroCapacities_of_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation)
    (hcall : I.positiveInstance.Optimal (fun e => (solve I.positiveInstance e : ℝ))) :
    I.Optimal (fun e => (solveWithZeroCapacities solve I e : ℝ)) := by
  have he : (fun e => (solveWithZeroCapacities solve I e : ℝ)) =
      I.eraseZeroFlow (fun e => (solve I.positiveInstance e : ℝ)) := by
    funext e
    by_cases hz : I.capacity e = 0 <;>
      simp only [solveWithZeroCapacities, eraseZeroFlow, hz, ↓reduceIte, Int.cast_zero]
  rw [he]
  exact I.eraseZeroFlow_optimal _ hcall

/-- The one-call adapter needs only the polynomial-cost, positive-capacity
specification assumed in Lemma C.3. It does not assume a dual solution. -/
theorem solveWithZeroCapacities_correct
    (solve : (J : Circulation) → Fin J.m → ℤ) (U : ℕ) (hU : 1 ≤ U)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ U) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10))
    (hu : ∀ e, I.capacity e ≤ U) :
    I.Optimal (fun e => (solveWithZeroCapacities solve I e : ℝ)) := by
  have h := I.eraseZeroFlow_optimal _
    (hsolve I.positiveInstance (I.positiveInstance_costsBounded _ hc)
      (I.positiveInstance_capacitiesBounded U hU hu))
  have he : (fun e => (solveWithZeroCapacities solve I e : ℝ)) =
      I.eraseZeroFlow (fun e => (solve I.positiveInstance e : ℝ)) := by
    funext e
    by_cases hz : I.capacity e = 0 <;>
      simp only [solveWithZeroCapacities, eraseZeroFlow, hz, ↓reduceIte, Int.cast_zero]
  rw [he]
  exact h

/-- The adapter's complete list of solver-call instances has length one. -/
def zeroCapacityCallInstances (I : Circulation) : List Circulation := [I.positiveInstance]

/-- The solver call count is exactly one. -/
theorem zeroCapacityCallInstances_length (I : Circulation) :
    I.zeroCapacityCallInstances.length = 1 := rfl

/-- Every call has exactly the original number of edges. -/
theorem zeroCapacityCallInstances_edges (I : Circulation) :
    ∀ J ∈ I.zeroCapacityCallInstances, J.m = I.m := by
  intro J hJ
  have he : J = I.positiveInstance := List.mem_singleton.mp hJ
  subst J
  rfl

end MinCostFlow.Scaling.Circulation
