module

public import MinCostFlow.IPM.Machine.LengthArrayPrecision
public import MinCostFlow.Num.IPM.GradientArray
import Mathlib.Tactic.Linarith

/-!
# Supplying the gradient-array procedure's numeric preconditions

The length call already checks the shared edge data. The gradient call
also needs the held epoch residual and signed integer costs. Their
representations, residual range and input cost bound discharge its
remaining premises at the selected precision.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The shared length input conditions, represented held residual and
source cost bound imply every numerical premise of the gradient call.
No equality between the held residual and the mixed stored flow's
residual is used. -/
theorem gradientArray_pre_of_chosen_precision (I : Instance) (U : ℕ)
    {w cp rp lo fp up ap one heap : ℕ} {mem : ℕ → ℕ} {r : ℝ}
    (hw : ipmParameterWordBits I.m U ≤ w) (hU : 1 ≤ U)
    (hnums : NumbersBounded I U)
    (hlen : (Num.IPM.lengthArrayContract w 4 (ipmErrorBits I.m U)).pre
      [lo,fp,up,ap,one,I.m,ipmLimbs I.m U,ipmPrecision I.m U,ipmRangeExponent I.m U,heap] mem)
    (hc : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) 0 ((I.edge e).cost:ℝ))
    (hr : ScalarAt mem rp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) r)
    (hrl : 1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ r)
    (hrh : r ≤ (2:ℝ)^(ipmRangeExponent I.m U))
    (hca : cp+I.m*ipmLimbs I.m U ≤ heap) (hra : rp+ipmLimbs I.m U ≤ heap)
    (hspace : heap+Num.IPM.gradientArraySpace I.m (ipmLimbs I.m U)
      (ipmPrecision I.m U) (ipmRangeExponent I.m U) < 2^w) :
    (Num.IPM.gradientArrayContract w 4 (ipmErrorBits I.m U) (gradientCoefficientExponent I.m U)).pre
      [I.m,cp,rp,lo,fp,up,ap,one,ipmLimbs I.m U,ipmPrecision I.m U,ipmRangeExponent I.m U,heap] mem := by
  obtain ⟨⟨lo',fp',up',ap',one',m',L',P',E',heap',heq,hP,_,_,_,hla,hfa,hua,haa,hoa,hdata⟩,hz,_⟩ := hlen
  cases List.cons.inj heq with
  | intro heq0 heq1 =>
    simp only [List.cons.injEq,and_true] at heq1
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq1
    subst lo'
    change ZeroFrom mem heap at hz
    have hrv := hr.1
    have hrval := hr.2
    have hrlo : 1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ Num.fixVal mem rp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) := by
      rw [hrval]
      exact hrl
    have hrhi : Num.fixVal mem rp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) ≤ (2:ℝ)^(ipmRangeExponent I.m U) := by
      rw [hrval]
      exact hrh
    have hm := ipm_precision_margins I.m U
    have hword := ipm_parameter_words_fit I.m U hw
    simp only [Num.IPM.gradientArrayContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,heapArg,List.getLastD_cons,List.getLastD_nil]
    with_reducible refine ⟨⟨I.m,cp,rp,lo,fp,up,ap,one,ipmLimbs I.m U,ipmPrecision I.m U,
      ipmRangeExponent I.m U,heap,rfl,hm.1,hm.2.1,hm.2.2.2.1,
      hword.2.2.2.2.1,hword.2.2.2.2.2.1,gradient_count_coefficient_bound I.m U hU,
      hca,hra,hla,hfa,hua,haa,hoa,hrv,hrlo,hrhi,?_⟩,hz,hspace⟩
    intro i hi
    refine ⟨hdata i hi,(hc ⟨i,hi⟩).1,?_⟩
    have hcost := (hc ⟨i,hi⟩).2
    simp only [Num.fixVal,pow_zero,div_one] at hcost
    have he : Num.intVal mem (cp+i*ipmLimbs I.m U) 4 (ipmLimbs I.m U)=(I.edge ⟨i,hi⟩).cost := by
      exact_mod_cast hcost
    rw [he]
    exact gradient_instance_coefficient_bound I U hnums ⟨i,hi⟩

/-- The coefficient refresh fits at the quality-dependent numerical dimensions. -/
theorem gradientArray_pre_of_widened_precision (I : Instance) (U k : ℕ)
    {w cp rp lo fp up ap one heap : ℕ} {mem : ℕ → ℕ} {r : ℝ}
    (hw : ipmQualityParameterWordBits I.m U k ≤ w) (hU : 1 ≤ U)
    (hnums : NumbersBounded I U)
    (hlen : (Num.IPM.lengthArrayContract w 4 (ipmQualityErrorBits I.m U k)).pre
      [lo,fp,up,ap,one,I.m,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,ipmQualityRangeExponent I.m U k,heap] mem)
    (hc : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) 0 ((I.edge e).cost:ℝ))
    (hr : ScalarAt mem rp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) r)
    (hrl : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k) ≤ r)
    (hrh : r ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hca : cp+I.m*ipmQualityLimbs I.m U k ≤ heap) (hra : rp+ipmQualityLimbs I.m U k ≤ heap)
    (hspace : heap+Num.IPM.gradientArraySpace I.m (ipmQualityLimbs I.m U k)
      (ipmQualityPrecision I.m U k) (ipmQualityRangeExponent I.m U k) < 2^w) :
    (Num.IPM.gradientArrayContract w 4 (ipmQualityErrorBits I.m U k) (gradientCoefficientExponent I.m U)).pre
      [I.m,cp,rp,lo,fp,up,ap,one,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,ipmQualityRangeExponent I.m U k,heap] mem := by
  obtain ⟨⟨lo',fp',up',ap',one',m',L',P',E',heap',heq,hP,_,_,_,hla,hfa,hua,haa,hoa,hdata⟩,hz,_⟩ := hlen
  cases List.cons.inj heq with
  | intro heq0 heq1 =>
    simp only [List.cons.injEq,and_true] at heq1
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq1
    subst lo'
    change ZeroFrom mem heap at hz
    have hrv := hr.1
    have hrval := hr.2
    have hrlo : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k) ≤ Num.fixVal mem rp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) := by
      rw [hrval]
      exact hrl
    have hrhi : Num.fixVal mem rp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
      rw [hrval]
      exact hrh
    have hm := ipm_quality_precision_margins I.m U k
    have hword := ipm_quality_parameter_words_fit I.m U k hw
    simp only [Num.IPM.gradientArrayContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,heapArg,List.getLastD_cons,List.getLastD_nil]
    with_reducible refine ⟨⟨I.m,cp,rp,lo,fp,up,ap,one,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,
      ipmQualityRangeExponent I.m U k,heap,rfl,hm.1,hm.2.1,hm.2.2.2.1,
      hword.2.2.2.2.1,hword.2.2.2.2.2.1,gradient_count_coefficient_bound I.m U hU,
      hca,hra,hla,hfa,hua,haa,hoa,hrv,hrlo,hrhi,?_⟩,hz,hspace⟩
    intro i hi
    refine ⟨hdata i hi,(hc ⟨i,hi⟩).1,?_⟩
    have hcost := (hc ⟨i,hi⟩).2
    simp only [Num.fixVal,pow_zero,div_one] at hcost
    have he : Num.intVal mem (cp+i*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k)=(I.edge ⟨i,hi⟩).cost := by
      exact_mod_cast hcost
    rw [he]
    exact gradient_instance_coefficient_bound I U hnums ⟨i,hi⟩

end MinCostFlow.IPM.Machine
