module

public import MinCostFlow.IPM.Machine.EpochCoefficientPre
public import MinCostFlow.IPM.Machine.GradientArrayPrecision

/-!
# Numeric input to Init at a freshly copied base

A successful full read certifies the slacks and the residual guard
certifies the positive held residual. The actual arrays are computed
from these scalar blocks with the selected fixed-point parameters.
The same construction applies to the initial half-slack flow.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The selected scalar encodings and checked ranges imply the
complete startup precondition for the numerical coefficient pass. -/
theorem coefficientRefresh_pre_of_chosen_precision (I : Instance) (U : ℕ)
    {w : ℕ} (hw : ipmParameterWordBits I.m U≤w)
    (f : Fin I.m → ℝ) (a r : ℝ) {cp rp lo fp up ap one heap : ℕ} {mem : ℕ → ℕ}
    (hU : 1≤U) (hnums : NumbersBounded I U)
    (hcost : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U) 0 (I.edge e).cost)
    (hlower : ∀ e : Fin I.m,ScalarAt mem (lo+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U)
      (ipmPrecision I.m U) (I.edge e).lower)
    (hupper : ∀ e : Fin I.m,ScalarAt mem (up+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U)
      (ipmPrecision I.m U) (I.edge e).upper)
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U) (ipmPrecision I.m U) (f e))
    (ha : ScalarAt mem ap 4 (ipmLimbs I.m U) (ipmPrecision I.m U) a)
    (hone : ScalarAt mem one 4 (ipmLimbs I.m U) (ipmPrecision I.m U) 1)
    (hr : ScalarAt mem rp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) r)
    (ha0 : 0≤a) (ha1 : a≤1)
    (hrl : 1/(2:ℝ)^(ipmRangeExponent I.m U)≤r) (hrh : r≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hslack : ∀ e : Fin I.m,
      1/(2:ℝ)^(ipmRangeExponent I.m U)≤(I.edge e).upper-f e ∧
      (I.edge e).upper-f e≤(2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)≤f e-(I.edge e).lower ∧
      f e-(I.edge e).lower≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hcEnd : cp+I.m*ipmLimbs I.m U≤heap) (hrEnd : rp+ipmLimbs I.m U≤heap)
    (hlEnd : lo+I.m*ipmLimbs I.m U≤heap) (hfEnd : fp+I.m*ipmLimbs I.m U≤heap)
    (huEnd : up+I.m*ipmLimbs I.m U≤heap) (haEnd : ap+ipmLimbs I.m U≤heap)
    (hoEnd : one+ipmLimbs I.m U≤heap) (hz : ZeroFrom mem heap)
    (hspace : heap+(Num.IPM.lengthArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U)
      (ipmRangeExponent I.m U)+Num.IPM.gradientArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U)
      (ipmRangeExponent I.m U))<2^w) :
    let L := ipmLimbs I.m U
    let P := ipmPrecision I.m U
    let E := ipmRangeExponent I.m U
    (coefficientRefreshContract w 4 (ipmErrorBits I.m U) (gradientCoefficientExponent I.m U)).pre
      [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.lengthArraySpace I.m L P E,
        Num.IPM.gradientArraySpace I.m L P E,heap] mem := by
  dsimp only
  let L := ipmLimbs I.m U
  let P := ipmPrecision I.m U
  let E := ipmRangeExponent I.m U
  let la := Num.IPM.lengthArraySpace I.m L P E
  let ga := Num.IPM.gradientArraySpace I.m L P E
  change heap+(la+ga)<2^w at hspace
  have hlspace : heap+la<2^w := by omega
  have hgspace : heap+ga<2^w := by omega
  have hlen := lengthArray_pre_of_chosen_precision I U f a hw hlower hflow hupper ha hone
    ha0 ha1 hslack hlEnd hfEnd huEnd haEnd hoEnd hz hlspace
  have hgrad := gradientArray_pre_of_chosen_precision I U hw hU hnums hlen hcost hr hrl hrh hcEnd hrEnd hgspace
  exact coefficientRefresh_pre_of_arrays hlen hgrad hz hspace

/-- The coefficient refresh fits at the quality-dependent numerical dimensions. -/
theorem coefficientRefresh_pre_of_widened_precision (I : Instance) (U k : ℕ)
    {w : ℕ} (hw : ipmQualityParameterWordBits I.m U k≤w)
    (f : Fin I.m → ℝ) (a r : ℝ) {cp rp lo fp up ap one heap : ℕ} {mem : ℕ → ℕ}
    (hU : 1≤U) (hnums : NumbersBounded I U)
    (hcost : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k) 0 (I.edge e).cost)
    (hlower : ∀ e : Fin I.m,ScalarAt mem (lo+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k)
      (ipmQualityPrecision I.m U k) (I.edge e).lower)
    (hupper : ∀ e : Fin I.m,ScalarAt mem (up+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k)
      (ipmQualityPrecision I.m U k) (I.edge e).upper)
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (f e))
    (ha : ScalarAt mem ap 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) a)
    (hone : ScalarAt mem one 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) 1)
    (hr : ScalarAt mem rp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) r)
    (ha0 : 0≤a) (ha1 : a≤1)
    (hrl : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤r) (hrh : r≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hslack : ∀ e : Fin I.m,
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤(I.edge e).upper-f e ∧
      (I.edge e).upper-f e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) ∧
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤f e-(I.edge e).lower ∧
      f e-(I.edge e).lower≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hcEnd : cp+I.m*ipmQualityLimbs I.m U k≤heap) (hrEnd : rp+ipmQualityLimbs I.m U k≤heap)
    (hlEnd : lo+I.m*ipmQualityLimbs I.m U k≤heap) (hfEnd : fp+I.m*ipmQualityLimbs I.m U k≤heap)
    (huEnd : up+I.m*ipmQualityLimbs I.m U k≤heap) (haEnd : ap+ipmQualityLimbs I.m U k≤heap)
    (hoEnd : one+ipmQualityLimbs I.m U k≤heap) (hz : ZeroFrom mem heap)
    (hspace : heap+(Num.IPM.lengthArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k)
      (ipmQualityRangeExponent I.m U k)+Num.IPM.gradientArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k)
      (ipmQualityRangeExponent I.m U k))<2^w) :
    let L := ipmQualityLimbs I.m U k
    let P := ipmQualityPrecision I.m U k
    let E := ipmQualityRangeExponent I.m U k
    (coefficientRefreshContract w 4 (ipmQualityErrorBits I.m U k) (gradientCoefficientExponent I.m U)).pre
      [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.lengthArraySpace I.m L P E,
        Num.IPM.gradientArraySpace I.m L P E,heap] mem := by
  dsimp only
  let L := ipmQualityLimbs I.m U k
  let P := ipmQualityPrecision I.m U k
  let E := ipmQualityRangeExponent I.m U k
  let la := Num.IPM.lengthArraySpace I.m L P E
  let ga := Num.IPM.gradientArraySpace I.m L P E
  change heap+(la+ga)<2^w at hspace
  have hlspace : heap+la<2^w := by omega
  have hgspace : heap+ga<2^w := by omega
  have hlen := lengthArray_pre_of_widened_precision I U k f a hw hlower hflow hupper ha hone
    ha0 ha1 hslack hlEnd hfEnd huEnd haEnd hoEnd hz hlspace
  have hgrad := gradientArray_pre_of_widened_precision I U k hw hU hnums hlen hcost hr hrl hrh hcEnd hrEnd hgspace
  exact coefficientRefresh_pre_of_arrays hlen hgrad hz hspace

end MinCostFlow.IPM.Machine
