module

public import MinCostFlow.Scaling.CostCapacityModel
public import MinCostFlow.Scaling.CostScalingCorrectness
public import MinCostFlow.Scaling.CapacityScalingCorrectness

/-!
# Correctness of the composed circulation solver

The circulation part of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
Appendix C, applies cost scaling and implements each call by capacity scaling.
The measured composition has the same output as this nested execution, and
all primitive invocations meet the source's polynomial input bounds.
-/

public section
namespace MinCostFlow.Scaling

/-- The circulation conclusion in Lemma C.1 (Appendix C): the actual nested
integer algorithm is an exact solver for arbitrary bounded costs and capacities. -/
theorem costCapacityModel_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hc : I.CostsBounded C) (hu : ∀ e, I.capacity e ≤ U) :
    I.Optimal (fun e => ((costCapacityModel solve I C U).value e : ℝ)) := by
  unfold costCapacityModel
  rw [costScalingMeasured_value]
  apply lemma_C_3 _ I C U hU hc hu
  intro J hj hcap
  exact lemma_C_9 solve hsolve J _ hj (fun e => (hcap e).2)

end MinCostFlow.Scaling
