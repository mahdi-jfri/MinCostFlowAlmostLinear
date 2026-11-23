module

public import MinCostFlow.Final.ScratchCostStep
import MinCostFlow.Scaling.VertexCompressionSize
import Mathlib.Tactic.Ring

/-!
# Counting work in a measured cost round

The primal and dual calls are charged at a common upper bound on
their dimensions. The guest-width factor multiplies the work
charge, and the solver term counts only actual calls.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- A positive capacity-model invocation has exactly its inner call and
work charge, plus linear construction and erasure, at any larger solver
dimensions. No bound on its future output is a premise. -/
theorem scratchCapacityPositive_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (J : Circulation) (C U N M : ℕ)
    (hn : J.n+2≤N) (hm : J.m+J.m≤M) (args : List ℕ) (mem : ℕ → ℕ) :
    let r := J.invokePositive (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U)
    (scratchCapacityPositiveContract w solver entry T S c d hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T N M)+102000*(scratchWorkFactor solver c d)*r.work+400*J.m+900 := by
  let r := J.invokePositive (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U)
  have hcomp := J.positiveInstance.compress_vertices_le
  have htime : T (J.positiveInstance.compress.n+1) (J.m+J.m)≤T N M :=
    hmono _ _ _ _ (by change J.positiveInstance.compress.n≤J.n+1 at hcomp; omega) hm
  have hcoef := Nat.mul_le_mul_left (solver.regBound+6) htime
  have hcalls := Nat.mul_le_mul_left r.calls.length hcoef
  change r.calls.length*((solver.regBound+6)*T (J.positiveInstance.compress.n+1) (J.m+J.m))+
      102000*(scratchWorkFactor solver c d)*r.work+400*J.m+900≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hcalls
    (102000*(scratchWorkFactor solver c d)*r.work)) (400*J.m)) 900

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
theorem scratchCapacityExtractDual_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := J.extractDualMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) flow
    (scratchCapacityExtractDualContract w solver entry T S c d hproc J flow C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+
        200000*(scratchWorkFactor solver c d)*r.work := by
  let inner := fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U
  let R := J.residual flow
  let M := R.m+R.n
  let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
  let call := Q.invokePositive inner
  let dual := J.extractDualMeasured inner flow
  have hPC := scratchCapacityPositive_cost_counted w solver entry T S c d hproc hmono Q C U
    (J.n+3) (8*J.m+4*J.n) (by change J.n+1+2≤J.n+3; omega)
    (by change ((J.m+J.m+J.n)+(J.m+J.m+J.n))+((J.m+J.m+J.n)+(J.m+J.m+J.n))≤8*J.m+4*J.n; omega)
    [] (fun _ => 0)
  change (scratchCapacityPositiveContract w solver entry T S c d hproc Q C U).cost [] (fun _ => 0)≤
    call.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+
      102000*(scratchWorkFactor solver c d)*call.work+400*(M+M)+900 at hPC
  have hwork : call.work+100*(J.m+J.n+1)≤dual.work := by
    change call.work+100*(J.m+J.n+1)≤100*(J.m+J.n+1)+_+call.work
    omega
  have hpad := dual_counted_padding J.m J.n (scratchWorkFactor solver c d) call.work dual.work (scratchWorkFactor_pos solver c d) hwork
  change (scratchCapacityPositiveContract w solver entry T S c d hproc Q C U).cost [] (fun _ => 0)+
      1000*M+1400+100*M+300+3000*M+1100+600*J.m+400≤
    call.calls.length*((solver.regBound+6)*T (J.n+3) (8*J.m+4*J.n))+200000*(scratchWorkFactor solver c d)*dual.work
  have hM : M=J.m+J.m+J.n := rfl
  omega

private theorem step_counted_padding (m n R pc dc pw dw Q : ℕ) (hR : 1≤R) :
    (pc*Q+102000*R*pw+400*(m+m)+900)+(dc*Q+200000*R*dw)+5000*(m+n+1)≤
      (pc+dc)*Q+300000*R*(80*(m+n+1)+pw+dw) := by
  have hmR : m≤R*m := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right m hR
  have hnR : n≤R*n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hR
  ring_nf at hmR hnR ⊢
  omega

/-- Each actual measured cost round costs its primitive-call term at
`(n+3,16*m+4*n)`, plus `300000*(regBound+1)` times its exact model work. -/
theorem scratchCostStep_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) {J : Circulation} (s : CostState J) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := CostState.stepMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) C s
    (scratchCostStepContract w solver entry T S c d hproc s C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
        300000*(scratchWorkFactor solver c d)*r.work := by
  let inner := fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U
  let K := s.roundedInstance C
  let B := J.m+J.m
  let primal := K.invokePositive inner
  let dual := K.extractDualMeasured inner primal.value
  have hP := scratchCapacityPositive_cost_counted w solver entry T S c d hproc hmono K (B^10) U
    (J.n+3) (16*J.m+4*J.n) (by change J.n+2≤J.n+3; omega)
    (by change (J.m+J.m)+(J.m+J.m)≤16*J.m+4*J.n; omega) [] (fun _ => 0)
  have hD := scratchCapacityExtractDual_cost_counted w solver entry T S c d hproc hmono K primal.value (B^10) U [] (fun _ => 0)
  have hdim : 8*K.m+4*K.n=16*J.m+4*J.n := by change 8*(J.m+J.m)+4*J.n=_; omega
  rw [hdim] at hD
  change (scratchCapacityPositiveContract w solver entry T S c d hproc K (B^10) U).cost [] (fun _ => 0)≤
    primal.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      102000*(scratchWorkFactor solver c d)*primal.work+400*(J.m+J.m)+900 at hP
  change (scratchCapacityExtractDualContract w solver entry T S c d hproc K primal.value (B^10) U).cost [] (fun _ => 0)≤
    dual.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      200000*(scratchWorkFactor solver c d)*dual.work at hD
  have hpad := step_counted_padding J.m J.n (scratchWorkFactor solver c d) primal.calls.length dual.calls.length
    primal.work dual.work ((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n)) (scratchWorkFactor_pos solver c d)
  simp only [CostState.stepMeasured,List.length_append]
  change (scratchCapacityPositiveContract w solver entry T S c d hproc K (B^10) U).cost [] (fun _ => 0)+
      (scratchCapacityExtractDualContract w solver entry T S c d hproc K primal.value (B^10) U).cost [] (fun _ => 0)+5000*(J.m+J.n+1)≤
    (primal.calls.length+dual.calls.length)*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      300000*(scratchWorkFactor solver c d)*(80*(J.m+J.n+1)+primal.work+dual.work)
  exact (Nat.add_le_add_right (Nat.add_le_add hP hD) (5000*(J.m+J.n+1))).trans hpad

end MinCostFlow.Final
