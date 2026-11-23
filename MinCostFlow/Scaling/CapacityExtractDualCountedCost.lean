module

public import MinCostFlow.Scaling.CapacityExtractDualContract
import MinCostFlow.Scaling.CapacityPositiveCountedCost
import Mathlib.Tactic.Ring

/-!
# Charging measured dual extraction to actual solver calls and work

The routed residual's positive capacity call supplies exactly the measured
model's primitive-call list. Its work is included in the dual counter,
which also charges linear residual and routing work. This absorbs every
wrapper instruction without charging for an unexecuted primitive call.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem dual_counted_padding (m n R W work : ℕ) (hR : 1≤R)
    (hw : W+100*(m+n+1)≤work) :
    102000*R*W+10400*m+4900*n+4100≤200000*R*work := by
  have hmR : m≤R*m := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right m hR
  have hnR : n≤R*n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hR
  have hlocal : 102000*R*W+10400*m+4900*n+4100≤200000*R*(W+100*(m+n+1)) := by
    ring_nf at hmR hnR ⊢
    omega
  exact hlocal.trans (Nat.mul_le_mul_left _ hw)

/-- Measured dual extraction costs its actual primitive-call term plus
`200000*(regBound+1)` times its actual measured model work. -/
theorem capacityExtractDual_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := J.extractDualMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) flow
    (capacityExtractDualContract w solver entry T hproc J flow C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+
        200000*(solver.regBound+1)*r.work := by
  let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
  let R := J.residual flow
  let M := R.m+R.n
  let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
  let call := Q.invokePositive inner
  let dual := J.extractDualMeasured inner flow
  have hPC := capacityPositive_cost_counted w solver entry T hproc hmono Q C U
    (J.n+3) (8*J.m+4*J.n) (by change J.n+1+2≤J.n+3; omega)
    (by change ((J.m+J.m+J.n)+(J.m+J.m+J.n))+((J.m+J.m+J.n)+(J.m+J.m+J.n))≤8*J.m+4*J.n; omega)
    [] (fun _ => 0)
  change (capacityPositiveContract w solver entry T hproc Q C U).cost [] (fun _ => 0)≤
    call.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+
      102000*(solver.regBound+1)*call.work+400*(M+M)+900 at hPC
  have hwork : call.work+100*(J.m+J.n+1)≤dual.work := by
    change call.work+100*(J.m+J.n+1)≤100*(J.m+J.n+1)+_+call.work
    omega
  have hpad := dual_counted_padding J.m J.n (solver.regBound+1) call.work dual.work (by omega) hwork
  change (capacityPositiveContract w solver entry T hproc Q C U).cost [] (fun _ => 0)+
      1000*M+1400+100*M+300+3000*M+1100+600*J.m+400≤
    call.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+200000*(solver.regBound+1)*dual.work
  have hM : M=J.m+J.m+J.n := rfl
  omega

end MinCostFlow.Scaling.Machine
