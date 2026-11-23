module

public import MinCostFlow.Scaling.CapacityScalingModel
public import MinCostFlow.Scaling.CapacityLoopCorrectness
import Mathlib.Tactic.NormNum

/-!
# Capacity scaling with an exact bounded-capacity solver

Lemma C.9 of Chen et al., arXiv:2203.00671v2, Appendix C, follows from the
finite gap-halving loop. The outer function handles the empty graph directly
and compresses isolated vertices before entering that loop. Compression
preserves capacities, costs, and optimality.
-/

public section
namespace MinCostFlow.Scaling

/-- Lemma C.9 (Chen et al., arXiv:2203.00671v2, Appendix C): the actual
capacity-scaling function gives an integral exact optimum from a solver for
`m^10`-bounded costs and positive `m^40`-bounded capacities. Its explicit
call, input-size, and work bounds are in `CapacityScalingModel`. -/
theorem lemma_C_9
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (U : ℕ) (hc : I.CostsBounded (I.m ^ 10))
    (hu : ∀ e, I.capacity e ≤ U) :
    I.Optimal (fun e => ((capacityScalingModel solve I U).value e : ℝ)) := by
  unfold capacityScalingModel
  split
  · rename_i hm
    simp only [Int.cast_zero]
    refine ⟨I.zero_feasible, ?_⟩
    intro g _
    have hempty : IsEmpty (Fin I.m) := by rw [hm]; infer_instance
    simp only [Circulation.objective, Finset.sum_empty, Finset.univ_eq_empty]
    exact le_rfl
  · rename_i hm
    apply (I.compress_optimal_iff _).mp
    exact capacityLoop_optimal solve hsolve I.compress U hc (Nat.pos_of_ne_zero hm) hu

end MinCostFlow.Scaling
