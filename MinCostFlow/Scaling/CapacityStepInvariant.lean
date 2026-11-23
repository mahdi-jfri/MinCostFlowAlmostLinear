module

public import MinCostFlow.Scaling.CapacityNumericFacts
public import MinCostFlow.Scaling.CapacityLoopModel
import MinCostFlow.Scaling.CapacitySolverModel

/-!
# The capacity bounds preserved by an executed scaling step

Stopped states and zero-magnitude candidates keep the old flow. In the
remaining case the actual rounded solver returns a feasible residual
correction. The integral augmentation bounds therefore keep every new
coordinate nonnegative and within its original capacity. This supplies
the invariant required to execute the next machine iteration.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The actual canonical capacity step preserves the integer capacity
bounds needed by residual construction and unsigned flow storage. -/
theorem capacityStep_flow_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (hc : J.CostsBounded (J.m^10))
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) :
    ∀ e,0≤(s.step (canonicalSolver solver entry T hproc)).value.flow e ∧
      (s.step (canonicalSolver solver entry T hproc)).value.flow e≤J.capacity e := by
  let solve := canonicalSolver solver entry T hproc
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
  cases hs : s.stopped with
  | true => simpa only [CapacityState.step,hs,↓reduceIte] using hf
  | false =>
    let R := J.residual s.flow
    let B := (polyApproxModel solve R).value.magnitude
    by_cases hB : (polyApproxModel (canonicalSolver solver entry T hproc) (J.residual s.flow)).value.magnitude=0
    · simpa only [CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hB] using hf
    · have hdelta := R.solveCapacityRoundedModel_feasible solve hsolve B
        (J.residual_polynomialCosts s.flow hc)
      have hnext := residualAugment_integral_bounds J s.flow
        (R.solveCapacityRoundedModel solve B).value hf hdelta
      simpa only [CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hB] using hnext

end MinCostFlow.Scaling.Machine
