module

public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.PolyApproxCountedCost
import MinCostFlow.Scaling.CapacityRoundedCountedCost
import Mathlib.Tactic.Linarith

/-!
# Charging a complete capacity iteration to the model counters

The approximation and positive rounded solve have direct call-plus-work
bounds. Residual construction, augmentation, and header writing are
covered by the step's explicit linear work budget. Stopped iterations
have cost at most a fixed multiple of their one counted operation.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem zero_cost (m n reg calls base work pCost : ℕ)
    (hp : pCost≤calls*base+30000*(reg+1)*work) :
    600*m+200+pCost+400≤calls*base+100000*(reg+1)*(20*(m+n+1)+work) := by
  nlinarith only [hp,Nat.zero_le (reg*m),Nat.zero_le (reg*n),Nat.zero_le (reg*work),
    Nat.zero_le m,Nat.zero_le n,Nat.zero_le reg,Nat.zero_le work]

private theorem positive_cost (m n reg calls base work pCost qCost : ℕ)
    (hp : pCost≤calls*base+30000*(reg+1)*work)
    (hq : qCost≤base+40000*(reg+1)*(m+m+1)) :
    600*m+200+pCost+(qCost+100*m+100+400)≤
      (calls+1)*base+100000*(reg+1)*(20*(m+n+1)+work+40*(m+m+1)) := by
  nlinarith only [hp,hq,Nat.zero_le (reg*m),Nat.zero_le (reg*n),Nat.zero_le (reg*work),
    Nat.zero_le m,Nat.zero_le n,Nat.zero_le reg,Nat.zero_le work]

/-- Every capacity iteration is charged to its actual solver-call trace
and other-work counter, with one uniform explicit coefficient. -/
theorem capacityStep_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hm : 0<J.m) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    let r := s.step (canonicalSolver solver entry T hproc)
    (capacityStepContract w solver entry T hproc J s C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+1) (J.m+J.m))+
        100000*(solver.regBound+1)*r.work := by
  let solve := canonicalSolver solver entry T hproc
  let R := J.residual s.flow
  let B := (polyApproxModel solve R).value.magnitude
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have hRm : R.m=J.m+J.m := rfl
  have hnR : R.n≤2*R.m := by change J.n≤2*(J.m+J.m); omega
  have hmR : 0<R.m := by rw [hRm]; omega
  have hp := polyApprox_cost_counted w solver entry T hproc R C U [] mem hnR hpolyR
  cases hs : s.stopped with
  | true =>
    simp only [capacityStepContract,CapacityState.step,hs,↓reduceIte,List.length_nil,Nat.zero_mul,Nat.mul_one]
    omega
  | false =>
    by_cases hB : B=0
    · have hBraw : (polyApproxModel (canonicalSolver solver entry T hproc) (J.residual s.flow)).value.magnitude=0 := hB
      simp only [capacityStepContract,CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hBraw]
      exact zero_cost J.m J.n solver.regBound (polyApproxModel solve R).calls.length
        ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) (polyApproxModel solve R).work _ hp
    · have hBraw : (polyApproxModel (canonicalSolver solver entry T hproc) (J.residual s.flow)).value.magnitude≠0 := hB
      have hq := capacityRoundedSolve_cost_positive w solver entry T hproc R B [] mem hmR
        (Nat.pos_of_ne_zero hB) hnR hpolyR
      simp only [capacityStepContract,CapacityState.step,hs,Bool.false_eq_true,↓reduceIte,hBraw,
        Circulation.solveCapacityRoundedModel,List.length_append,List.length_singleton]
      exact positive_cost J.m J.n solver.regBound (polyApproxModel solve R).calls.length
        ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) (polyApproxModel solve R).work _ _ hp hq

end MinCostFlow.Scaling.Machine
