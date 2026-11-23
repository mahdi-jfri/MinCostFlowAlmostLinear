module

public import MinCostFlow.IPM.Machine.TargetEpochStatic
public import MinCostFlow.IPM.Machine.TargetEpochCopy
import Mathlib.Tactic.Positivity

/-!
# Numerical precondition after the actual residual guard

All copied coordinates have certified slack ranges, even on guesses
below optimum. The residual guard and exact target subtraction
supply the remaining input bounds for both coefficient arrays.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Use the chosen precision to start the numerical coefficient pass
from the actual copied flow and guarded residual. -/
theorem targetEpoch_coefficient_pre (I : Instance) (U : ℕ)
    {w : ℕ} (hw : ipmParameterWordBits I.m U≤w) (old : EpochLayout)
    (tp qp source oldHeap : ℕ) (target normalization a r : ℝ) (mem copied : ℕ → ℕ)
    (hfixed : TargetFixedInputs (ipmMinRatioFormat I.m U hw) I old tp qp oldHeap target normalization a mem)
    (hflow : TargetStageFlow (ipmMinRatioFormat I.m U hw) I old.exponent source oldHeap mem)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hU : 1≤U) (hnums : NumbersBounded I U) (ha0 : 0≤a) (ha1 : a≤1)
    (hframe : ∀ z<oldHeap,copied z=mem z)
    (hrl : 1/(2:ℝ)^old.exponent<r) (hrh : r<(2:ℝ)^old.exponent)
    (hres : ScalarAt copied (oldHeap+(8*I.m+3)*ipmLimbs I.m U)
      4 (ipmLimbs I.m U) (ipmPrecision I.m U) r)
    (hcopy : ∀ e : Fin I.m,
      ScalarAt copied (epochResidualEnd I.m (ipmLimbs I.m U) oldHeap+e.val*ipmLimbs I.m U)
        4 (ipmLimbs I.m U) (ipmPrecision I.m U) (epochVector (ipmMinRatioFormat I.m U hw) I mem source e))
    (hz : ZeroFrom copied (epochResidualEnd I.m (ipmLimbs I.m U) oldHeap+I.m*ipmLimbs I.m U))
    (hspace : epochResidualEnd I.m (ipmLimbs I.m U) oldHeap+I.m*ipmLimbs I.m U+
      (Num.IPM.lengthArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U) old.exponent+
        Num.IPM.gradientArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U) old.exponent)<2^w) :
    let F := ipmMinRatioFormat I.m U hw
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let rp := oldHeap+(8*I.m+3)*F.limbs
    let next := old.next F I source rp fp (fp+I.m*F.limbs) 0
    (coefficientRefreshContract w F.fmt.limbBits (ipmErrorBits I.m U) (gradientCoefficientExponent I.m U)).pre
      ((next.startPacket F I).take 14) copied := by
  dsimp only
  let F := ipmMinRatioFormat I.m U hw
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let h := fp+I.m*F.limbs
  have hOld : oldHeap≤h := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hfixed' := hfixed.frozen hframe hOld
  have hResEnd : rp+ipmLimbs I.m U=fp := by
    simp [rp,fp,F,ipmMinRatioFormat,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hslack (e : Fin I.m) :
      let f := epochVector F I mem source e
      1/(2:ℝ)^(ipmRangeExponent I.m U)≤(I.edge e).upper-f ∧
      (I.edge e).upper-f≤(2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)≤f-(I.edge e).lower ∧
      f-(I.edge e).lower≤(2:ℝ)^(ipmRangeExponent I.m U) := by
    rw [← hE]
    have he := (hflow.2.2 e).2
    exact ⟨he.1.1.le,he.1.2.le,he.2.1.le,he.2.2.le⟩
  have hfit : h+(Num.IPM.lengthArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U) (ipmRangeExponent I.m U)+
    Num.IPM.gradientArraySpace I.m (ipmLimbs I.m U) (ipmPrecision I.m U) (ipmRangeExponent I.m U))<2^w := by
    rw [← hE]
    exact hspace
  have hpre := coefficientRefresh_pre_of_chosen_precision I U hw (epochVector F I mem source) a r
    hU hnums hfixed'.cost hfixed'.lower hfixed'.upper hcopy hfixed'.alpha hfixed'.one hres ha0 ha1
    (by rw [← hE]; exact hrl.le) (by rw [← hE]; exact hrh.le) hslack
    (hfixed'.arrays _ (by simp)) (hResEnd.le.trans (Nat.le_add_right _ _))
    (hfixed'.arrays _ (by simp)) (le_refl h) (hfixed'.arrays _ (by simp))
    (hfixed'.scalars _ (by simp)) (hfixed'.scalars _ (by simp)) hz hfit
  simp only [EpochLayout.next,EpochLayout.startPacket,hE]
  exact hpre

/-- The coefficient refresh fits at the quality-dependent numerical dimensions. -/
theorem targetEpoch_coefficient_pre_widened (I : Instance) (U k : ℕ)
    {w : ℕ} (hw : ipmQualityParameterWordBits I.m U k≤w) (old : EpochLayout)
    (tp qp source oldHeap : ℕ) (target normalization a r : ℝ) (mem copied : ℕ → ℕ)
    (hfixed : TargetFixedInputs (ipmQualityMinRatioFormat I.m U k hw) I old tp qp oldHeap target normalization a mem)
    (hflow : TargetStageFlow (ipmQualityMinRatioFormat I.m U k hw) I old.exponent source oldHeap mem)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hU : 1≤U) (hnums : NumbersBounded I U) (ha0 : 0≤a) (ha1 : a≤1)
    (hframe : ∀ z<oldHeap,copied z=mem z)
    (hrl : 1/(2:ℝ)^old.exponent<r) (hrh : r<(2:ℝ)^old.exponent)
    (hres : ScalarAt copied (oldHeap+(8*I.m+3)*ipmQualityLimbs I.m U k)
      4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) r)
    (hcopy : ∀ e : Fin I.m,
      ScalarAt copied (epochResidualEnd I.m (ipmQualityLimbs I.m U k) oldHeap+e.val*ipmQualityLimbs I.m U k)
        4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e))
    (hz : ZeroFrom copied (epochResidualEnd I.m (ipmQualityLimbs I.m U k) oldHeap+I.m*ipmQualityLimbs I.m U k))
    (hspace : epochResidualEnd I.m (ipmQualityLimbs I.m U k) oldHeap+I.m*ipmQualityLimbs I.m U k+
      (Num.IPM.lengthArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) old.exponent+
        Num.IPM.gradientArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) old.exponent)<2^w) :
    let F := ipmQualityMinRatioFormat I.m U k hw
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let rp := oldHeap+(8*I.m+3)*F.limbs
    let next := old.next F I source rp fp (fp+I.m*F.limbs) 0
    (coefficientRefreshContract w F.fmt.limbBits (ipmQualityErrorBits I.m U k) (gradientCoefficientExponent I.m U)).pre
      ((next.startPacket F I).take 14) copied := by
  dsimp only
  let F := ipmQualityMinRatioFormat I.m U k hw
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let h := fp+I.m*F.limbs
  have hOld : oldHeap≤h := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hfixed' := hfixed.frozen hframe hOld
  have hResEnd : rp+ipmQualityLimbs I.m U k=fp := by
    simp [rp,fp,F,ipmQualityMinRatioFormat,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hslack (e : Fin I.m) :
      let f := epochVector F I mem source e
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤(I.edge e).upper-f ∧
      (I.edge e).upper-f≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) ∧
      1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤f-(I.edge e).lower ∧
      f-(I.edge e).lower≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
    rw [← hE]
    have he := (hflow.2.2 e).2
    exact ⟨he.1.1.le,he.1.2.le,he.2.1.le,he.2.2.le⟩
  have hfit : h+(Num.IPM.lengthArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (ipmQualityRangeExponent I.m U k)+
    Num.IPM.gradientArraySpace I.m (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (ipmQualityRangeExponent I.m U k))<2^w := by
    rw [← hE]
    exact hspace
  have hpre := coefficientRefresh_pre_of_widened_precision I U k hw (epochVector F I mem source) a r
    hU hnums hfixed'.cost hfixed'.lower hfixed'.upper hcopy hfixed'.alpha hfixed'.one hres ha0 ha1
    (by rw [← hE]; exact hrl.le) (by rw [← hE]; exact hrh.le) hslack
    (hfixed'.arrays _ (by simp)) (hResEnd.le.trans (Nat.le_add_right _ _))
    (hfixed'.arrays _ (by simp)) (le_refl h) (hfixed'.arrays _ (by simp))
    (hfixed'.scalars _ (by simp)) (hfixed'.scalars _ (by simp)) hz hfit
  simp only [EpochLayout.next,EpochLayout.startPacket,hE]
  exact hpre

end MinCostFlow.IPM.Machine
