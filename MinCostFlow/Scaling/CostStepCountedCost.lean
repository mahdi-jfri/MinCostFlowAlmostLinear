module

public import MinCostFlow.Scaling.CostStepContract
import MinCostFlow.Scaling.CapacityPositiveCountedCost
import MinCostFlow.Scaling.CapacityExtractDualCountedCost
import Mathlib.Tactic.Ring

/-!
# Charging a measured cost round to its actual counters

The two inner procedures return exactly the primal and dual model traces.
Move their solver-time terms to the larger routed dimensions and add their
actual call counts. The measured round's linear work charge covers every
remaining wrapper, array-update, and header instruction.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem step_counted_padding (m n R pc dc pw dw Q : ℕ) (hR : 1≤R) :
    (pc*Q+102000*R*pw+400*(m+m)+900)+(dc*Q+200000*R*dw)+5000*(m+n+1)≤
      (pc+dc)*Q+300000*R*(80*(m+n+1)+pw+dw) := by
  have hmR : m≤R*m := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right m hR
  have hnR : n≤R*n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hR
  ring_nf at hmR hnR ⊢
  omega

/-- Each actual measured cost round costs its primitive-call term at
`(n+3,16*m+4*n)`, plus `300000*(regBound+1)` times its exact model work. -/
theorem costStep_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) {J : Circulation} (s : CostState J) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := CostState.stepMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) C s
    (costStepContract w solver entry T hproc s C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
        300000*(solver.regBound+1)*r.work := by
  let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
  let K := s.roundedInstance C
  let B := J.m+J.m
  let primal := K.invokePositive inner
  let dual := K.extractDualMeasured inner primal.value
  have hP := capacityPositive_cost_counted w solver entry T hproc hmono K (B^10) U
    (J.n+3) (16*J.m+4*J.n) (by change J.n+2≤J.n+3; omega)
    (by change (J.m+J.m)+(J.m+J.m)≤16*J.m+4*J.n; omega) [] (fun _ => 0)
  have hD := capacityExtractDual_cost_counted w solver entry T hproc hmono K primal.value (B^10) U [] (fun _ => 0)
  have hdim : 8*K.m+4*K.n=16*J.m+4*J.n := by change 8*(J.m+J.m)+4*J.n=_; omega
  rw [hdim] at hD
  change (capacityPositiveContract w solver entry T hproc K (B^10) U).cost [] (fun _ => 0)≤
    primal.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      102000*(solver.regBound+1)*primal.work+400*(J.m+J.m)+900 at hP
  change (capacityExtractDualContract w solver entry T hproc K primal.value (B^10) U).cost [] (fun _ => 0)≤
    dual.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      200000*(solver.regBound+1)*dual.work at hD
  have hpad := step_counted_padding J.m J.n (solver.regBound+1) primal.calls.length dual.calls.length
    primal.work dual.work ((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n)) (by omega)
  simp only [CostState.stepMeasured,List.length_append]
  change (capacityPositiveContract w solver entry T hproc K (B^10) U).cost [] (fun _ => 0)+
      (capacityExtractDualContract w solver entry T hproc K primal.value (B^10) U).cost [] (fun _ => 0)+5000*(J.m+J.n+1)≤
    (primal.calls.length+dual.calls.length)*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      300000*(solver.regBound+1)*(80*(J.m+J.n+1)+primal.work+dual.work)
  exact (Nat.add_le_add_right (Nat.add_le_add hP hD) (5000*(J.m+J.n+1))).trans hpad

end MinCostFlow.Scaling.Machine
