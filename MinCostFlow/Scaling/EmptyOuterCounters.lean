module

public import MinCostFlow.Scaling.DemandBoundCheck
import MinCostFlow.Scaling.CallExpansion

/-!
# The exact outer counters when the original graph has no edges

The checked reduction's supplied circulation inputs have at most `3*m`
positive slots. With `m=0`, every such input is empty, so its cost-capacity
model has zero primitive calls and work one. Expanding at most two checked
calls adds at most two units to the checked scan bound. The preliminary
demand scan then adds only `3*n`, including when it rejects immediately.
-/

public section
namespace MinCostFlow.Scaling.Machine
open FlowReduction

/-- Empty original edge sets give zero primitive calls and at most
`80*n+2` work in the complete bounded-demand model. -/
theorem generalScalingModel_empty_counters (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hm : I.m=0) :
    (generalScalingModel solve I hv C U).calls.length=0 ∧
      (generalScalingModel solve I hv C U).work≤80*I.n+2 := by
  let inner := fun J => costCapacityModel solve J (max C 1) (scalingCapacityBudget I U)
  let r := checkedReduction (fun J => (inner J).value) I hv
  have hzero : ∀ J∈r.calls,J.m=0 := by
    intro J hJ
    have he := checkedReduction_edges (fun J => (inner J).value) I hv J hJ
    omega
  have hc : ∀ J∈r.calls,(inner J).calls.length≤0 := by
    intro J hJ
    have hj := hzero J hJ
    simp only [inner,costCapacityModel,costScalingMeasured,hj,↓reduceIte,List.length_nil]
    exact le_rfl
  have hw : ∀ J∈r.calls,(inner J).work≤1 := by
    intro J hJ
    have hj := hzero J hJ
    simp only [inner,costCapacityModel,costScalingMeasured,hj,↓reduceIte]
    exact le_rfl
  have hcalls := CallResult.expand_calls inner r 0 hc
  have hwork := CallResult.expand_work inner r 1 hw
  have hscan := checkedReduction_work (fun J => (inner J).value) I hv
  have hcount := checkedReduction_calls (fun J => (inner J).value) I hv
  change r.work≤80*(I.m+I.n) at hscan
  change r.calls.length≤2 at hcount
  constructor
  · change (checkedMeasured inner I hv).calls.length=0
    rw [checkedMeasured_calls]
    change (CallResult.expand inner r).calls.length=0
    omega
  · change (checkedMeasured inner I hv).work≤80*I.n+2
    rw [checkedMeasured_work]
    change (CallResult.expand inner r).work≤80*I.n+2
    omega

/-- Empty original edge sets give zero primitive calls and at most
`83*n+2` work in the full arbitrary-demand model, on every branch. -/
theorem arbitraryDemandScalingModel_empty_counters (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hm : I.m=0) :
    (arbitraryDemandScalingModel solve I hv C U).calls.length=0 ∧
      (arbitraryDemandScalingModel solve I hv C U).work≤83*I.n+2 := by
  unfold arbitraryDemandScalingModel
  split
  · dsimp only
    obtain ⟨hc,hw⟩ := generalScalingModel_empty_counters solve I hv C ((I.m+1)*U) hm
    exact ⟨hc,by omega⟩
  · exact ⟨rfl,by dsimp only; omega⟩

end MinCostFlow.Scaling.Machine
