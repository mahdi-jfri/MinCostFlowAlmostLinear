module

public import MinCostFlow.Final.ScratchOuterEntry
import MinCostFlow.Scaling.GeneralScalingCountedCost
import MinCostFlow.Scaling.GeneralScalingWorkLower
import MinCostFlow.Scaling.OuterCallDimensions
import MinCostFlow.Scaling.OuterPhaseCountedCost
import MinCostFlow.Scaling.PrunedScalingCountedCost
import MinCostFlow.Scaling.TwoCallReductionCountedCost

/-!
# Counting the cost of the widened scaling program

The two calls have the same model traces at the wider guest width.
Each wrapper adds linear work, and the width factor pays for its
guest setup. The solver term uses the original comparison dimensions.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The pruned solve keeps its inner trace and adds linear scatter work. -/
theorem scratchPrunedScaling_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (J : Circulation) (C U N M : ℕ)
    (hsize : 0<J.withoutZeroEdges.m →
      J.withoutZeroEdges.compress.n+3≤N ∧
      16*J.withoutZeroEdges.m+4*J.withoutZeroEdges.compress.n≤M)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C U) J
    (scratchPrunedScalingContract w solver entry T S c d hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T N M)+303000*scratchWorkFactor solver c d*r.work+1000*J.m+1000 := by
  let K := J.withoutZeroEdges
  let r := costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C U
  change r.calls.length*((solver.regBound+6)*T (K.compress.n+3) (16*K.m+4*K.compress.n))+
    303000*scratchWorkFactor solver c d*r.work+1000*J.m+1000≤
      r.calls.length*((solver.regBound+6)*T N M)+303000*scratchWorkFactor solver c d*r.work+1000*J.m+1000
  by_cases hk : K.m=0
  · have hc : r.calls.length=0 := by
      simp only [r,costCapacityModel,costScalingMeasured,hk,↓reduceIte,List.length_nil]
    simp only [hc,Nat.zero_mul]
    exact le_rfl
  · obtain ⟨hn,hm⟩ := hsize (by change 0<K.m; omega)
    have ht := hmono _ _ _ _ hn hm
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left r.calls.length (Nat.mul_le_mul_left (solver.regBound+6) ht))
      (303000*scratchWorkFactor solver c d*r.work)) (1000*J.m)) 1000

/-- The complete first phase is charged to its exact counted pruned
feasibility solve and linear original-input work. -/
theorem scratchFeasibilityPhase_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hiso : FlowReduction.isolatedCheck I hv=true) (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C
        (FlowReduction.scalingCapacityBudget I U)) (FlowReduction.buildFeasibilityInstance I hv)
    (scratchFeasibilityPhaseContract w solver entry T S c d hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+
        303000*scratchWorkFactor solver c d*r.work+7000*(I.m+I.n+1) := by
  let P := FlowReduction.buildFeasibilityInstance I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let r := Circulation.invokePruned
    (fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C B) P
  have h := scratchPrunedScaling_cost_counted w solver entry T S c d hproc hmono P C B (min (8*I.n) (9*I.m)) (72*I.m)
    (by
      intro hpos
      have h := feasibility_compacted_solver_dimensions I hv hiso hpos
      have hm : P.withoutZeroEdges.m ≤ 3*I.m := by
        change (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m ≤ _
        rw [FlowReduction.buildFeasibilityInstance_eq]
        exact FlowReduction.feasibilityInstance_positiveEdges_le_three I hv hiso
      have hn : P.withoutZeroEdges.compress.n ≤ 2*P.withoutZeroEdges.m :=
        P.withoutZeroEdges.endpointLabels_count_le
      exact ⟨le_min h.1 (by omega), h.2⟩) [] (fun _ => 0)
  change (scratchPrunedScalingContract w solver entry T S c d hproc P C B).cost [] (fun _ => 0)+4000*(I.m+I.n+1)≤
    r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+303000*scratchWorkFactor solver c d*r.work+7000*(I.m+I.n+1)
  change (scratchPrunedScalingContract w solver entry T S c d hproc P C B).cost [] (fun _ => 0)≤
    r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+303000*scratchWorkFactor solver c d*r.work+1000*P.m+1000 at h
  have hPm : P.m=I.m+(I.n+I.n) := rfl
  omega

/-- The complete residual optimization phase is charged to its exact
counted pruned correction and linear original-input work. -/
theorem scratchResidualOptimization_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C
        (FlowReduction.scalingCapacityBudget I U)) ((FlowReduction.shiftedGraph I hv).residual f)
    (scratchResidualOptimizationContract w solver entry T S c d hproc I hv f C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+
        303000*scratchWorkFactor solver c d*r.work+7000*(I.m+I.n+1) := by
  let R := (FlowReduction.shiftedGraph I hv).residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let r := Circulation.invokePruned
    (fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C B) R
  have h := scratchPrunedScaling_cost_counted w solver entry T S c d hproc hmono R C B (min (8*I.n) (9*I.m)) (72*I.m)
    (by
      intro hpos
      have h := residual_compacted_solver_dimensions I hv f hpos
      have hm : R.withoutZeroEdges.m ≤ I.m+I.m := R.positiveEdges_length_le
      have hn : R.withoutZeroEdges.compress.n ≤ 2*R.withoutZeroEdges.m :=
        R.withoutZeroEdges.endpointLabels_count_le
      exact ⟨le_min h.1 (by omega), h.2⟩) [] (fun _ => 0)
  change (scratchPrunedScalingContract w solver entry T S c d hproc R C B).cost [] (fun _ => 0)+2000*I.m+1000≤
    r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+303000*scratchWorkFactor solver c d*r.work+7000*(I.m+I.n+1)
  change (scratchPrunedScalingContract w solver entry T S c d hproc R C B).cost [] (fun _ => 0)≤
    r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+303000*scratchWorkFactor solver c d*r.work+1000*R.m+1000 at h
  have hRm : R.m=I.m+I.m := rfl
  omega

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
theorem scratchTwoCallReduction_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (hiso : FlowReduction.isolatedCheck I hv=true) (args : List ℕ) (mem : ℕ → ℕ) :
    let inner := fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C
      (FlowReduction.scalingCapacityBudget I U)
    let r := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
    (scratchTwoCallReductionContract w solver entry T S c d hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+
        303000*scratchWorkFactor solver c d*r.work+20000*(I.m+I.n+1) := by
  let B := FlowReduction.scalingCapacityBudget I U
  let inner := fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C B
  let P := FlowReduction.buildFeasibilityInstance I hv
  let g := Circulation.invokePruned inner P
  let f := fun e => g.value (Fin.castAdd (I.n+I.n) e)
  let h := Circulation.invokePruned inner ((FlowReduction.shiftedGraph I hv).residual f)
  let good := P.integerObjective g.value = -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℤ)
  let r := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
  let F := (scratchFeasibilityPhaseContract w solver entry T S c d hproc I hv C U).cost [] (fun _ => 0)
  let O := (scratchResidualOptimizationContract w solver entry T S c d hproc I hv f C U).cost [] (fun _ => 0)
  let Q := (solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m)
  let R := scratchWorkFactor solver c d
  have hRpos : 1≤R := scratchWorkFactor_pos solver c d
  have hF := scratchFeasibilityPhase_cost_counted w solver entry T S c d hproc hmono I hv C U hiso [] (fun _ => 0)
  have hO := scratchResidualOptimization_cost_counted w solver entry T S c d hproc hmono I hv f C U [] (fun _ => 0)
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
theorem scratchGeneralScaling_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := FlowReduction.generalScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
    (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+
        1000000*scratchWorkFactor solver c d*r.work := by
  let K := max C 1
  let inner := fun J => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J K
    (FlowReduction.scalingCapacityBudget I U)
  let p := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
  let r := FlowReduction.generalScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
  let Q := (solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m)
  let R := scratchWorkFactor solver c d
  have hRpos : 1≤R := scratchWorkFactor_pos solver c d
  let charge := (scratchTwoCallReductionContract w solver entry T S c d hproc I hv K U).cost [] (fun _ => 0)
  have hscan : 44*(I.m+I.n)≤r.work := generalScalingModel_work_ge_scan _ I hv C U
  have hpos : 1≤r.work := generalScalingModel_work_pos _ I hv C U
  have hbase : (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U).cost args mem≤
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
      have hS := scratchTwoCallReduction_cost_counted w solver entry T S c d hproc hmono I hv K U hiso [] (fun _ => 0)
      change charge≤p.calls.length*Q+303000*R*p.work+20000*(I.m+I.n+1) at hS
      have hSpos : 50≤charge := by
        change 50≤200*I.m+500+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then _ else 0)
        omega
      have hcost : (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U).cost args mem≤2000*(I.m+I.n+1)+charge := by
        change 2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
          (if FlowReduction.isolatedCheck I hv then charge else 50) else 50)≤_
        by_cases hcap : ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper
        · rw [ite_eq_left hcap,ite_eq_left hiso]
        · rw [ite_eq_right hcap]
          omega
      have hwork := Nat.mul_le_mul_left (303000*R) hw
      rw [←hc] at hS
      omega
    · have hfalse := Bool.eq_false_iff.mpr hiso
      change 2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
        (if FlowReduction.isolatedCheck I hv then charge else 50) else 50)≤_
      simp only [hfalse,Bool.false_eq_true,↓reduceIte,ite_self]
      omega
  exact absorb_general_overhead _ r.calls.length Q R r.work I.m I.n (by dsimp only [R]; omega)
    hscan hpos hbase

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
theorem scratchArbitraryDemand_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid) (C U : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := FlowReduction.arbitraryDemandScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
    (scratchArbitraryDemandContract w solver entry T S c d hproc I hv C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m))+
        2000000*scratchWorkFactor solver c d*r.work := by
  let U' := (I.m+1)*U
  let g := FlowReduction.generalScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U'
  let r := FlowReduction.arbitraryDemandScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
  let Q := (solver.regBound+6)*T (min (8*I.n) (9*I.m)) (72*I.m)
  let R := scratchWorkFactor solver c d
  have hRpos : 1≤R := scratchWorkFactor_pos solver c d
  have hR : 1≤R := by dsimp only [R]; omega
  change 200*(I.n+1)+(if FlowReduction.demandBoundCheck I U then
      (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U').cost [] (fun _ => 0) else 50)≤
    r.calls.length*Q+2000000*R*r.work
  by_cases hcheck : FlowReduction.demandBoundCheck I U=true
  · rw [ite_eq_left hcheck]
    have hc : r.calls.length=g.calls.length := by
      unfold r FlowReduction.arbitraryDemandScalingModel
      rw [ite_eq_left hcheck]
    have hw : r.work=g.work+3*I.n := by
      unfold r FlowReduction.arbitraryDemandScalingModel
      rw [ite_eq_left hcheck]
    have hG := scratchGeneralScaling_cost_counted w solver entry T S c d hproc hmono I hv C U' [] (fun _ => 0)
    change (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U').cost [] (fun _ => 0)≤
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
    have hpos := arbitraryDemandScalingModel_work_pos ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
    change 1≤r.work at hpos
    rw [hw] at hpos
    rw [hc,hw]
    simpa only [Nat.zero_mul,Nat.zero_add] using rejecting_budget I.n R hR hpos

end MinCostFlow.Final
