module

public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.Num.IPM.LengthArray
import Mathlib.Tactic.Linarith

/-!
# Connecting represented edge data to the length-array procedure

The numerical procedure reads capacities, stored flows, the barrier
exponent and one from separate blocks. Exact block decoding and the
slack bounds supply its per-edge conditions. The selected precision
supplies all static arithmetic margins, leaving only real memory extents
and workspace to the caller.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Exact scalar representations turn mathematical slack ranges into
the numerical procedure's edge input conditions. -/
theorem edgeData_of_scalarAt {mem : ℕ → ℕ} {lo fp up ap one h L P E : ℕ}
    {lower flow upper a : ℝ}
    (hlo : ScalarAt mem lo h L P lower) (hf : ScalarAt mem fp h L P flow)
    (hup : ScalarAt mem up h L P upper) (ha : ScalarAt mem ap h L P a)
    (hone : ScalarAt mem one h L P 1)
    (hul : 1/(2:ℝ)^E ≤ upper-flow) (huh : upper-flow ≤ (2:ℝ)^E)
    (hdl : 1/(2:ℝ)^E ≤ flow-lower) (hdh : flow-lower ≤ (2:ℝ)^E)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Num.IPM.EdgeData mem lo fp up ap one h L P E := by
  refine ⟨hlo.1,hf.1,hup.1,ha.1,hone.1,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := hone.2
    unfold Num.fixVal at hh
    have he : (Num.intVal mem one h L:ℝ)=(2:ℝ)^P := by
      exact (div_eq_one_iff_eq (by positivity)).mp hh
    exact_mod_cast he
  all_goals simp only [hlo.2,hf.2,hup.2,ha.2]; assumption

/-- The chosen precision meets every static premise of the actual
length-array call. The slack ranges refer to the stored coordinates
whose blocks the procedure reads. -/
theorem lengthArray_pre_of_chosen_precision (I : Instance) (U : ℕ)
    (f : Fin I.m → ℝ) (a : ℝ) {w lo fp up ap one heap : ℕ} {mem : ℕ → ℕ}
    (hw : ipmParameterWordBits I.m U ≤ w)
    (hlo : ∀ e : Fin I.m,ScalarAt mem (lo+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U) ((I.edge e).lower:ℝ))
    (hf : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U) (f e))
    (hup : ∀ e : Fin I.m,ScalarAt mem (up+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U) ((I.edge e).upper:ℝ))
    (ha : ScalarAt mem ap 4 (ipmLimbs I.m U) (ipmPrecision I.m U) a)
    (hone : ScalarAt mem one 4 (ipmLimbs I.m U) (ipmPrecision I.m U) 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hslack : ∀ e : Fin I.m,
      1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ (I.edge e).upper-f e ∧
      (I.edge e).upper-f e ≤ (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ f e-(I.edge e).lower ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(ipmRangeExponent I.m U))
    (hla : lo+I.m*ipmLimbs I.m U ≤ heap) (hfa : fp+I.m*ipmLimbs I.m U ≤ heap)
    (hua : up+I.m*ipmLimbs I.m U ≤ heap) (haa : ap+ipmLimbs I.m U ≤ heap)
    (hoa : one+ipmLimbs I.m U ≤ heap) (hz : ZeroFrom mem heap)
    (hspace : heap+Num.IPM.lengthArraySpace I.m (ipmLimbs I.m U)
      (ipmPrecision I.m U) (ipmRangeExponent I.m U) < 2^w) :
    (Num.IPM.lengthArrayContract w 4 (ipmErrorBits I.m U)).pre
      [lo,fp,up,ap,one,I.m,ipmLimbs I.m U,ipmPrecision I.m U,ipmRangeExponent I.m U,heap] mem := by
  have hm := ipm_precision_margins I.m U
  have hword := ipm_parameter_words_fit I.m U hw
  refine ⟨⟨lo,fp,up,ap,one,I.m,ipmLimbs I.m U,ipmPrecision I.m U,
    ipmRangeExponent I.m U,heap,rfl,hm.1,by omega,by omega,hword.2.2.2.2.1,
    hla,hfa,hua,haa,hoa,?_⟩,hz,hspace⟩
  intro i hi
  have hs := hslack ⟨i,hi⟩
  exact edgeData_of_scalarAt (hlo ⟨i,hi⟩) (hf ⟨i,hi⟩) (hup ⟨i,hi⟩)
    ha hone hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 ha0 ha1

/-- The coefficient refresh fits at the quality-dependent numerical dimensions. -/
theorem lengthArray_pre_of_widened_precision (I : Instance) (U k : ℕ)
    (f : Fin I.m → ℝ) (a : ℝ) {w lo fp up ap one heap : ℕ} {mem : ℕ → ℕ}
    (hw : ipmQualityParameterWordBits I.m U k ≤ w)
    (hlo : ∀ e : Fin I.m,ScalarAt mem (lo+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) ((I.edge e).lower:ℝ))
    (hf : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (f e))
    (hup : ∀ e : Fin I.m,ScalarAt mem (up+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) ((I.edge e).upper:ℝ))
    (ha : ScalarAt mem ap 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) a)
    (hone : ScalarAt mem one 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hslack : ∀ e : Fin I.m,
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k) ≤ (I.edge e).upper-f e ∧
      (I.edge e).upper-f e ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k) ∧
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k) ≤ f e-(I.edge e).lower ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hla : lo+I.m*ipmQualityLimbs I.m U k ≤ heap) (hfa : fp+I.m*ipmQualityLimbs I.m U k ≤ heap)
    (hua : up+I.m*ipmQualityLimbs I.m U k ≤ heap) (haa : ap+ipmQualityLimbs I.m U k ≤ heap)
    (hoa : one+ipmQualityLimbs I.m U k ≤ heap) (hz : ZeroFrom mem heap)
    (hspace : heap+Num.IPM.lengthArraySpace I.m (ipmQualityLimbs I.m U k)
      (ipmQualityPrecision I.m U k) (ipmQualityRangeExponent I.m U k) < 2^w) :
    (Num.IPM.lengthArrayContract w 4 (ipmQualityErrorBits I.m U k)).pre
      [lo,fp,up,ap,one,I.m,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,ipmQualityRangeExponent I.m U k,heap] mem := by
  have hm := ipm_quality_precision_margins I.m U k
  have hword := ipm_quality_parameter_words_fit I.m U k hw
  refine ⟨⟨lo,fp,up,ap,one,I.m,ipmQualityLimbs I.m U k,ipmQualityPrecision I.m U k,
    ipmQualityRangeExponent I.m U k,heap,rfl,hm.1,by omega,by omega,hword.2.2.2.2.1,
    hla,hfa,hua,haa,hoa,?_⟩,hz,hspace⟩
  intro i hi
  have hs := hslack ⟨i,hi⟩
  exact edgeData_of_scalarAt (hlo ⟨i,hi⟩) (hf ⟨i,hi⟩) (hup ⟨i,hi⟩)
    ha hone hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 ha0 ha1

end MinCostFlow.IPM.Machine
