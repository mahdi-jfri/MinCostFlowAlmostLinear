module

public import MinCostFlow.IPM.Machine.EpochBaseOutput
public import MinCostFlow.IPM.Machine.ResidualPrecision

/-!
# Exact target residual inputs on either side of the optimum

A successfully read flow is feasible and fixed-point. The bounded
costs and capacities control every dot-product prefix and the integer
target subtraction. Thus the next epoch's residual test is defined
even on guesses below the optimal cost.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The selected precision and feasible materialized flow give the
guarded base procedure's full machine precondition. -/
theorem epochBase_pre_of_chosen_precision (I : Instance) (U : ℕ) (f : Fin I.m → ℝ) (target : ℤ)
    {w cp fp tp heap mn mx qp : ℕ} {mem : ℕ → ℕ}
    (hm : 0<I.m) (hU : 0<U) (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hcost : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U) 0 (I.edge e).cost)
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U) (f e))
    (htarget : ScalarAt mem tp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) target)
    (htargetBound : |(target:ℝ)|≤I.m*(U:ℝ)^2)
    (hca : cp+I.m*ipmLimbs I.m U≤heap) (hfa : fp+I.m*ipmLimbs I.m U≤heap)
    (hta : tp+ipmLimbs I.m U≤heap)
    (hmna : mn+ipmLimbs I.m U≤heap) (hmxa : mx+ipmLimbs I.m U≤heap) (hqa : qp+ipmLimbs I.m U≤heap)
    (hmn : Num.Valid mem mn 4 (ipmLimbs I.m U)) (hmx : Num.Valid mem mx 4 (ipmLimbs I.m U))
    (hq : Num.Valid mem qp 4 (ipmLimbs I.m U))
    (hz : ZeroFrom mem heap) (hword : 8<2^w)
    (hspace : epochResidualEnd I.m (ipmLimbs I.m U) heap+I.m*ipmLimbs I.m U<2^w) :
    (epochBaseContract w 4).pre [cp,fp,I.m,tp,ipmLimbs I.m U,heap,mn,mx,qp] mem := by
  let L := ipmLimbs I.m U
  have hresSpace : heap+(8*I.m+4)*L<2^w := by
    change heap+(8*I.m+4)*L+I.m*L<2^w at hspace
    omega
  have hL : 0<L := by
    unfold L ipmLimbs
    omega
  have hres := residual_pre_of_chosen_precision I U f target hm hU hnums hf hcost hflow htarget
    htargetBound hca hfa hta hz hresSpace
  exact ⟨cp,fp,I.m,tp,L,heap,mn,mx,qp,rfl,⟨cp,fp,I.m,tp,L,heap,mn,mx,qp,rfl,by omega,
    hres,hmna,hmxa,hqa,hmn,hmx,hq⟩,hL,hword,hspace⟩

/-- The residual and base procedures fit at the widened numerical dimensions. -/
theorem epochBase_pre_of_widened_precision (I : Instance) (U k : ℕ) (f : Fin I.m → ℝ) (target : ℤ)
    {w cp fp tp heap mn mx qp : ℕ} {mem : ℕ → ℕ}
    (hm : 0<I.m) (hU : 0<U) (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hcost : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k) 0 (I.edge e).cost)
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (f e))
    (htarget : ScalarAt mem tp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) target)
    (htargetBound : |(target:ℝ)|≤I.m*(U:ℝ)^2)
    (hca : cp+I.m*ipmQualityLimbs I.m U k≤heap) (hfa : fp+I.m*ipmQualityLimbs I.m U k≤heap)
    (hta : tp+ipmQualityLimbs I.m U k≤heap)
    (hmna : mn+ipmQualityLimbs I.m U k≤heap) (hmxa : mx+ipmQualityLimbs I.m U k≤heap) (hqa : qp+ipmQualityLimbs I.m U k≤heap)
    (hmn : Num.Valid mem mn 4 (ipmQualityLimbs I.m U k)) (hmx : Num.Valid mem mx 4 (ipmQualityLimbs I.m U k))
    (hq : Num.Valid mem qp 4 (ipmQualityLimbs I.m U k))
    (hz : ZeroFrom mem heap) (hword : 8<2^w)
    (hspace : epochResidualEnd I.m (ipmQualityLimbs I.m U k) heap+I.m*ipmQualityLimbs I.m U k<2^w) :
    (epochBaseContract w 4).pre [cp,fp,I.m,tp,ipmQualityLimbs I.m U k,heap,mn,mx,qp] mem := by
  let L := ipmQualityLimbs I.m U k
  have hresSpace : heap+(8*I.m+4)*L<2^w := by
    change heap+(8*I.m+4)*L+I.m*L<2^w at hspace
    omega
  have hL : 0<L := by
    unfold L ipmQualityLimbs
    omega
  have hres := residual_pre_of_widened_precision I U k f target hm hU hnums hf hcost hflow htarget
    htargetBound hca hfa hta hz hresSpace
  exact ⟨cp,fp,I.m,tp,L,heap,mn,mx,qp,rfl,⟨cp,fp,I.m,tp,L,heap,mn,mx,qp,rfl,by omega,
    hres,hmna,hmxa,hqa,hmn,hmx,hq⟩,hL,hword,hspace⟩

end MinCostFlow.IPM.Machine
