module

public import MinCostFlow.Scaling.GeneralScalingContract
import MinCostFlow.Scaling.TwoCallReductionCountedCost
import MinCostFlow.Scaling.GeneralScalingWorkLower

/-!
# Charging all bounded-demand scaling to its actual counters

The checked model pays for an original edge and vertex scan in every
branch. Its work is also positive, including on an empty graph. These
facts absorb the checks, serialization, and constant entry overhead.
The selected two-call procedure contributes exactly its model calls and
work. No solver call is charged on a rejected branch.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem absorb_general_overhead (cost calls Q R W m n : ℕ) (hR : 1≤R)
    (hscan : 44*(m+n)≤W) (hpos : 1≤W)
    (hc : cost≤calls*Q+303000*R*W+22000*(m+n+1)) :
    cost≤calls*Q+1000000*R*W := by
  have hRW : W≤R*W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hR
  simp only [Nat.mul_assoc] at hc ⊢
  omega

/-- The complete bounded-demand general procedure is charged to its
actual primitive calls and at most `1000000*(regBound+1)*model.work`
additional instructions, uniformly over all rejection and empty branches. -/
theorem generalScaling_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U
    (generalScalingContract w solver entry T hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+
        1000000*(solver.regBound+1)*r.work := by
  let K := max C 1
  let inner := fun J => costCapacityModel (canonicalSolver solver entry T hproc) J K
    (FlowReduction.scalingCapacityBudget I U)
  let p := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
  let r := FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U
  let Q := (solver.regBound+6)*T (8*I.n) (72*I.m)
  let R := solver.regBound+1
  let S := (twoCallReductionContract w solver entry T hproc I hv K U).cost [] (fun _ => 0)
  have hscan : 44*(I.m+I.n)≤r.work := generalScalingModel_work_ge_scan _ I hv C U
  have hpos : 1≤r.work := generalScalingModel_work_pos _ I hv C U
  have hbase : (generalScalingContract w solver entry T hproc I hv C U).cost args mem≤
      r.calls.length*Q+303000*R*r.work+22000*(I.m+I.n+1) := by
    by_cases hiso : FlowReduction.isolatedCheck I hv=true
    · have hc : r.calls.length=p.calls.length := by
        unfold r FlowReduction.generalScalingModel FlowReduction.checkedMeasured
        rw [ite_eq_left hiso]
      have hw : p.work≤r.work := by
        unfold r FlowReduction.generalScalingModel FlowReduction.checkedMeasured
        rw [ite_eq_left hiso]
        change p.work≤p.work+44*(I.m+I.n)
        omega
      have hS := twoCallReduction_cost_counted w solver entry T hproc hmono I hv K U hiso [] (fun _ => 0)
      change S≤p.calls.length*Q+303000*R*p.work+20000*(I.m+I.n+1) at hS
      have hSpos : 50≤S := by
        change 50≤200*I.m+500+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then _ else 0)
        omega
      have hcost : (generalScalingContract w solver entry T hproc I hv C U).cost args mem≤2000*(I.m+I.n+1)+S := by
        change 2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
          (if FlowReduction.isolatedCheck I hv then S else 50) else 50)≤_
        by_cases hcap : ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper
        · rw [ite_eq_left hcap,ite_eq_left hiso]
        · rw [ite_eq_right hcap]
          omega
      have hwork := Nat.mul_le_mul_left (303000*R) hw
      rw [←hc] at hS
      omega
    · have hfalse := Bool.eq_false_iff.mpr hiso
      change 2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
        (if FlowReduction.isolatedCheck I hv then S else 50) else 50)≤_
      simp only [hfalse,Bool.false_eq_true,↓reduceIte,ite_self]
      omega
  exact absorb_general_overhead _ r.calls.length Q R r.work I.m I.n (by dsimp only [R]; omega)
    hscan hpos hbase

end MinCostFlow.Scaling.Machine
