module

public import MinCostFlow.Scaling.PrunedScalingContract

/-!
# Charging pruned scaling to actual model calls and work

The complete compacted solver's contract already counts its exact calls
and measured work. Monotonicity raises its solver-time argument to any
chosen comparison dimensions covering a nonempty compacted graph. If
compaction deletes every edge, there are no primitive calls, so no
comparison dimension assumption is needed in that case.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The pruned procedure's budget is charged to the exact counted
pruning adapter, with only its explicit linear original-slot overhead. -/
theorem prunedScaling_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (J : Circulation) (C U N M : ℕ)
    (hsize : 0<J.withoutZeroEdges.m →
      J.withoutZeroEdges.compress.n+3≤N ∧
      16*J.withoutZeroEdges.m+4*J.withoutZeroEdges.compress.n≤M)
    (args : List ℕ) (mem : ℕ → ℕ) :
    let r := Circulation.invokePruned
      (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C U) J
    (prunedScalingContract w solver entry T hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T N M)+303000*(solver.regBound+1)*r.work+1000*J.m+1000 := by
  let K := J.withoutZeroEdges
  let r := costCapacityModel (canonicalSolver solver entry T hproc) K C U
  change r.calls.length*((solver.regBound+6)*T (K.compress.n+3) (16*K.m+4*K.compress.n))+
    303000*(solver.regBound+1)*r.work+1000*J.m+1000≤
      r.calls.length*((solver.regBound+6)*T N M)+303000*(solver.regBound+1)*r.work+1000*J.m+1000
  by_cases hk : K.m=0
  · have hc : r.calls.length=0 := by
      simp only [r,costCapacityModel,costScalingMeasured,hk,↓reduceIte,List.length_nil]
    simp only [hc,Nat.zero_mul]
    exact le_rfl
  · obtain ⟨hn,hm⟩ := hsize (by change 0<K.m; omega)
    have ht := hmono _ _ _ _ hn hm
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left r.calls.length (Nat.mul_le_mul_left (solver.regBound+6) ht))
      (303000*(solver.regBound+1)*r.work)) (1000*J.m)) 1000

/-- Every compacted input has comparison dimensions satisfying the full
uniform-budget side condition simultaneously. -/
theorem exists_prunedScaling_comparison_dimensions (J : Circulation) :
    ∃ N M,0<J.withoutZeroEdges.m → J.withoutZeroEdges.compress.n+3≤N ∧
      16*J.withoutZeroEdges.m+4*J.withoutZeroEdges.compress.n≤M :=
  ⟨_,_,fun _ => ⟨le_rfl,le_rfl⟩⟩

end MinCostFlow.Scaling.Machine
