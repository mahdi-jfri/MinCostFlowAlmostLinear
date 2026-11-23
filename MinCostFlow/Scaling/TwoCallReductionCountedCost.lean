module

public import MinCostFlow.Scaling.TwoCallReductionContract
import MinCostFlow.Scaling.OuterPhaseCountedCost

/-!
# Charging the exact two-call entry to the reduction model

Split on the same capacity-order and objective conditions as the counted
model. Each selected phase contributes its exact inner call count and
work. Concatenation adds the calls and the reduction counter includes
both inner work counters. Linear checking and serialization overhead fits
`20000*(m+n+1)` on every branch.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem successful_budget (m n Q R W0 W1 W2 c1 c2 F O : ℕ)
    (hF : F≤c1*Q+303000*R*W1+7000*(m+n+1))
    (hO : O≤c2*Q+303000*R*W2+7000*(m+n+1)) :
    200*m+500+(F+(O+40*m+150))≤
      (c1+c2)*Q+303000*R*(W0+W1+W2)+20000*(m+n+1) := by
  simp only [Nat.add_mul,Nat.mul_add] at hF hO ⊢
  omega

private theorem failed_budget (m n Q R W0 W1 calls F : ℕ)
    (hF : F≤calls*Q+303000*R*W1+7000*(m+n+1)) :
    200*m+500+(F+50)≤calls*Q+303000*R*(W0+W1)+20000*(m+n+1) := by
  simp only [Nat.mul_add] at hF ⊢
  omega

/-- The two-call machine budget is bounded by its actual model calls and
work plus linear original-input overhead, including failed capacity order. -/
theorem twoCallReduction_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hiso : FlowReduction.isolatedCheck I hv=true) (args : List ℕ) (mem : ℕ → ℕ) :
    let inner := fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C
      (FlowReduction.scalingCapacityBudget I U)
    let r := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
    (twoCallReductionContract w solver entry T hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (8*I.n) (72*I.m))+
        303000*(solver.regBound+1)*r.work+20000*(I.m+I.n+1) := by
  let B := FlowReduction.scalingCapacityBudget I U
  let inner := fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B
  let P := FlowReduction.buildFeasibilityInstance I hv
  let g := Circulation.invokePruned inner P
  let f := fun e => g.value (Fin.castAdd (I.n+I.n) e)
  let h := Circulation.invokePruned inner ((FlowReduction.shiftedGraph I hv).residual f)
  let good := P.integerObjective g.value = -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℤ)
  let r := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
  let F := (feasibilityPhaseContract w solver entry T hproc I hv C U).cost [] (fun _ => 0)
  let O := (residualOptimizationContract w solver entry T hproc I hv f C U).cost [] (fun _ => 0)
  let Q := (solver.regBound+6)*T (8*I.n) (72*I.m)
  let R := solver.regBound+1
  have hF := feasibilityPhase_cost_counted w solver entry T hproc hmono I hv C U hiso [] (fun _ => 0)
  have hO := residualOptimization_cost_counted w solver entry T hproc hmono I hv f C U [] (fun _ => 0)
  change F≤g.calls.length*Q+303000*R*g.work+7000*(I.m+I.n+1) at hF
  change O≤h.calls.length*Q+303000*R*h.work+7000*(I.m+I.n+1) at hO
  change 200*I.m+500+(if ∀ e,(I.edge e).lower≤(I.edge e).upper then F+(if good then O+40*I.m+150 else 50) else 0)≤
    r.calls.length*Q+303000*R*r.work+20000*(I.m+I.n+1)
  by_cases hcap : ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper
  · rw [ite_eq_left hcap]
    by_cases hg : good
    · rw [ite_eq_left hg]
      have hc : r.calls.length=g.calls.length+h.calls.length := by
        unfold r FlowReduction.reduceMeasured
        rw [ite_eq_left hcap]
        change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).calls.length=_
        rw [ite_eq_left hg]
        exact List.length_append
      have hw : r.work=FlowReduction.reductionWork I+g.work+h.work := by
        unfold r FlowReduction.reduceMeasured
        rw [ite_eq_left hcap]
        change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).work=_
        rw [ite_eq_left hg]
      rw [hc,hw]
      exact successful_budget I.m I.n Q R (FlowReduction.reductionWork I) g.work h.work
        g.calls.length h.calls.length F O hF hO
    · rw [ite_eq_right hg]
      have hc : r.calls.length=g.calls.length := by
        unfold r FlowReduction.reduceMeasured
        rw [ite_eq_left hcap]
        change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).calls.length=_
        rw [ite_eq_right hg]
      have hw : r.work=FlowReduction.reductionWork I+g.work := by
        unfold r FlowReduction.reduceMeasured
        rw [ite_eq_left hcap]
        change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).work=_
        rw [ite_eq_right hg]
      rw [hc,hw]
      exact failed_budget I.m I.n Q R (FlowReduction.reductionWork I) g.work g.calls.length F hF
  · rw [ite_eq_right hcap]
    have hc : r.calls.length=0 := by
      simp only [r,FlowReduction.reduceMeasured,hcap,↓reduceIte,List.length_nil]
    have hw : r.work=I.m := by simp only [r,FlowReduction.reduceMeasured,hcap,↓reduceIte]
    rw [hc,hw]
    omega

end MinCostFlow.Scaling.Machine
