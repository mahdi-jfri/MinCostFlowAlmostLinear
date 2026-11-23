module

public import MinCostFlow.Scaling.DemandBoundCheck
import MinCostFlow.Scaling.CostScalingWorkLower

/-!
# Positive work in every branch of the outer scaling model

A failed demand or isolated-vertex check must inspect a vertex. Failed
capacity order must inspect an edge. Every remaining branch executes a
circulation solve, whose measured scaling work is positive even on an
empty graph. Thus the exact outer model always pays for constant entry
and branch instructions as well as its scans and solver calls.
-/

public section
namespace MinCostFlow.Scaling.Machine
open FlowReduction

private theorem reduceMeasured_work_pos
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (hi : ∀ J,1≤(inner J).work) (I : Instance) (hv : I.IsValid) :
    1≤(reduceMeasured inner I hv).work := by
  unfold reduceMeasured
  split
  · dsimp only
    have hfirst := hi (buildFeasibilityInstance I hv)
    split <;> dsimp only <;> omega
  · rename_i hfailed
    dsimp only
    have hm : 0<I.m := by
      by_contra hn
      apply hfailed
      intro e
      have he := e.isLt
      omega
    exact hm

/-- A counted inner procedure with positive work gives positive total
checked-reduction work in every branch, including empty inputs. -/
theorem checkedMeasured_work_pos
    (inner : (J : Circulation) → CallResult (Fin J.m → ℤ))
    (hi : ∀ J,1≤(inner J).work) (I : Instance) (hv : I.IsValid) :
    1≤(checkedMeasured inner I hv).work := by
  unfold checkedMeasured
  split
  · dsimp only
    have hh := reduceMeasured_work_pos (Circulation.invokePruned inner)
      (fun J => hi J.withoutZeroEdges) I hv
    omega
  · rename_i hfailed
    dsimp only
    have hn : 0<I.n := by
      by_contra hn
      apply hfailed
      apply (isolatedCheck_iff I hv).mpr
      intro v
      have he := v.isLt
      omega
    omega

/-- The exact general-flow composition always has at least one unit of
model work, so it pays for constant machine overhead without a new call. -/
theorem generalScalingModel_work_pos (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    1≤(generalScalingModel solve I hv C U).work :=
  checkedMeasured_work_pos _ (fun J => costCapacityModel_work_pos solve J _ _) I hv

/-- Every general-model branch pays for the full original edge and vertex
scan, whether it rejects isolated demands or proceeds to the reduction. -/
theorem generalScalingModel_work_ge_scan (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    44*(I.m+I.n)≤(generalScalingModel solve I hv C U).work := by
  unfold generalScalingModel checkedMeasured
  split <;> dsimp only <;> omega

/-- The arbitrary-demand wrapper's actual work is positive even when it
rejects before invoking any circulation procedure. -/
theorem arbitraryDemandScalingModel_work_pos (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    1≤(arbitraryDemandScalingModel solve I hv C U).work := by
  unfold arbitraryDemandScalingModel
  split
  · dsimp only
    have hh := generalScalingModel_work_pos solve I hv C ((I.m+1)*U)
    omega
  · rename_i hfailed
    dsimp only
    have hn : 0<I.n := by
      by_contra hn
      apply hfailed
      apply (demandBoundCheck_iff I U).mpr
      intro v
      have he := v.isLt
      omega
    omega

end MinCostFlow.Scaling.Machine
