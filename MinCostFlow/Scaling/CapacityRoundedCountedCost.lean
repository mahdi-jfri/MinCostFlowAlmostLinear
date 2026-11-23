module

public import MinCostFlow.Scaling.CapacityRoundedSolveProgram
import MinCostFlow.Scaling.CapacityRoundedGuestBounds
import Mathlib.Tactic.Ring

/-!
# Charging a positive rounded solve to its counters

Clipped guest setup costs logarithmic work, and its encoded graph is
linear in the edge count. Both are covered by the rounded model's
`40*(m+1)` other-work counter. The remaining term is the one actual
primitive solver call at the canonical interpreter's stated coefficient.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem rounded_overhead (m reg g : ℕ) (hg : 40*g≤27000*(m+1)) :
    80*(2+5*m)+40*g+reg+680*m+1600≤40000*(reg+1)*(m+1) := by
  have hr : reg≤reg*(m+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left reg (show 1≤m+1 by omega)
  have heq : 40000*(reg+1)*(m+1)=40000*(reg*(m+1))+40000*(m+1) := by ring
  rw [heq]
  omega

/-- A positive rounded solve has one solver term and linear overhead,
including canonical guest execution and all input/output conversions. -/
theorem capacityRoundedSolve_cost_positive (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (B : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hm : 0<J.m) (hB : 0<B) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    (capacityRoundedSolveContract w solver entry T hproc J B).cost args mem≤
      (solver.regBound+6)*T (J.n+1) J.m+40000*(solver.regBound+1)*(J.m+1) := by
  let K := (J.scaledRoundedInstance B).positiveInstance
  let g := wordSize 5 K.solverWords
  have hguest : g≤225*(Nat.clog 2 (J.m+2)+1) := capacityRoundedGuest_width_le J B hm hB hn hc
  have hlog : Nat.clog 2 (J.m+2)≤J.m+2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hg : 40*g≤27000*(J.m+1) := by omega
  have hover := rounded_overhead J.m solver.regBound g hg
  have hlen : K.solverWords.length=2+5*J.m := K.solverWords_length
  simp only [capacityRoundedSolveContract,heapContract,Nat.ne_of_gt hB,↓reduceIte]
  have h := Nat.add_le_add_left hover ((solver.regBound+6)*T (J.n+1) J.m)
  simpa only [←hlen,Nat.add_assoc] using h

/-- The positive rounded execution is charged directly to its one-call
trace and exact linear model work. -/
theorem capacityRoundedSolve_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (B : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hm : 0<J.m) (hB : 0<B) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    let r := J.solveCapacityRoundedModel (canonicalSolver solver entry T hproc) B
    (capacityRoundedSolveContract w solver entry T hproc J B).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+1) J.m)+1000*(solver.regBound+1)*r.work := by
  have h := capacityRoundedSolve_cost_positive w solver entry T hproc J B args mem hm hB hn hc
  have heq : 1000*(solver.regBound+1)*(40*(J.m+1))=40000*(solver.regBound+1)*(J.m+1) := by ring
  simpa only [Circulation.solveCapacityRoundedModel,Nat.ne_of_gt hB,↓reduceIte,
    List.length_singleton,Nat.one_mul,heq] using h

end MinCostFlow.Scaling.Machine
