module

public import MinCostFlow.Scaling.ArbitraryDemandContract
import MinCostFlow.Scaling.GeneralScalingCountedCost
import MinCostFlow.Scaling.GeneralScalingWorkLower

/-!
# Charging the full arbitrary-demand program to actual model counters

A successful demand check adds only its vertex scan to the general model.
The general model's positive work pays for constant entry overhead. A
rejected check has at least one scanned vertex and makes no primitive
call. Thus the complete program is bounded by its actual primitive-call
term and `2000000*(regBound+1)*model.work`, on every input branch.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem passing_budget (n calls Q R W : ℕ) (hR : 1≤R) (hW : 1≤W) :
    200*(n+1)+(calls*Q+1000000*R*W)≤calls*Q+2000000*R*(W+3*n) := by
  have hprod : R*W≤R*(W+3*n) := Nat.mul_le_mul_left R (by omega)
  have htotal : W+3*n≤R*(W+3*n) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (W+3*n) hR
  simp only [Nat.mul_assoc]
  omega

private theorem rejecting_budget (n R : ℕ) (hR : 1≤R) (hn : 1≤3*n) :
    200*(n+1)+50≤2000000*R*(3*n) := by
  have hprod : 3*n≤R*(3*n) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (3*n) hR
  simp only [Nat.mul_assoc]
  omega

/-- Every instruction in the complete arbitrary-demand program is charged
to the exact model's actual calls and work, with a single explicit
coefficient and original solver dimensions `T(8*n,72*m)`. -/
theorem arbitraryDemand_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
    (arbitraryDemandContract w solver entry T hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+
        2000000*(solver.regBound+1)*r.work := by
  let U' := (I.m+1)*U
  let g := FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U'
  let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
  let Q := (solver.regBound+6)*T (8*I.n) (72*I.m)
  let R := solver.regBound+1
  have hR : 1≤R := by dsimp only [R]; omega
  change 200*(I.n+1)+(if FlowReduction.demandBoundCheck I U then
      (generalScalingContract w solver entry T hproc I hv C U').cost [] (fun _ => 0) else 50)≤
    r.calls.length*Q+2000000*R*r.work
  by_cases hcheck : FlowReduction.demandBoundCheck I U=true
  · rw [ite_eq_left hcheck]
    have hc : r.calls.length=g.calls.length := by
      unfold r FlowReduction.arbitraryDemandScalingModel
      rw [ite_eq_left hcheck]
    have hw : r.work=g.work+3*I.n := by
      unfold r FlowReduction.arbitraryDemandScalingModel
      rw [ite_eq_left hcheck]
    have hG := generalScaling_cost_counted w solver entry T hproc hmono I hv C U' [] (fun _ => 0)
    change (generalScalingContract w solver entry T hproc I hv C U').cost [] (fun _ => 0)≤
      g.calls.length*Q+1000000*R*g.work at hG
    have hgpos : 1≤g.work := generalScalingModel_work_pos _ I hv C U'
    rw [hc,hw]
    exact (Nat.add_le_add_left hG (200*(I.n+1))).trans
      (passing_budget I.n g.calls.length Q R g.work hR hgpos)
  · rw [ite_eq_right hcheck]
    have hfalse := Bool.eq_false_iff.mpr hcheck
    have hc : r.calls.length=0 := by
      simp only [r,FlowReduction.arbitraryDemandScalingModel,hfalse,Bool.false_eq_true,↓reduceIte,List.length_nil]
    have hw : r.work=3*I.n := by simp only [r,FlowReduction.arbitraryDemandScalingModel,hfalse,Bool.false_eq_true,↓reduceIte]
    have hpos := arbitraryDemandScalingModel_work_pos (canonicalSolver solver entry T hproc) I hv C U
    change 1≤r.work at hpos
    rw [hw] at hpos
    rw [hc,hw]
    simpa only [Nat.zero_mul,Nat.zero_add] using rejecting_budget I.n R hR hpos

end MinCostFlow.Scaling.Machine
