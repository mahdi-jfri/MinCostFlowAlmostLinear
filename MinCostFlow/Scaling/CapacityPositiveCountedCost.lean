module

public import MinCostFlow.Scaling.CapacityPositiveContract
import MinCostFlow.Scaling.VertexCompressionSize

/-!
# Charging positive capacity-model calls to their actual counters

The complete capacity wrapper already charges its actual primitive-call
list and model work. Dummy erasure leaves those counters unchanged.
Monotonicity moves its compressed solver dimensions to any supplied larger
dimensions, while construction and erasure retain their explicit linear
extra charge.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A positive capacity-model invocation has exactly its inner call and
work charge, plus linear construction and erasure, at any larger solver
dimensions. No bound on its future output is a premise. -/
theorem capacityPositive_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (J : Circulation) (C U N M : ℕ)
    (hn : J.n+2≤N) (hm : J.m+J.m≤M) (args : List ℕ) (mem : ℕ → ℕ) :
    let r := J.invokePositive (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)
    (capacityPositiveContract w solver entry T hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T N M)+102000*(solver.regBound+1)*r.work+400*J.m+900 := by
  let r := J.invokePositive (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U)
  have hcomp := J.positiveInstance.compress_vertices_le
  have htime : T (J.positiveInstance.compress.n+1) (J.m+J.m)≤T N M :=
    hmono _ _ _ _ (by change J.positiveInstance.compress.n≤J.n+1 at hcomp; omega) hm
  have hcoef := Nat.mul_le_mul_left (solver.regBound+6) htime
  have hcalls := Nat.mul_le_mul_left r.calls.length hcoef
  change r.calls.length*((solver.regBound+6)*T (J.positiveInstance.compress.n+1) (J.m+J.m))+
      102000*(solver.regBound+1)*r.work+400*J.m+900≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hcalls
    (102000*(solver.regBound+1)*r.work)) (400*J.m)) 900

end MinCostFlow.Scaling.Machine
