module

public import MinCostFlow.IPM.Machine.TargetTestProgram
public import MinCostFlow.IPM.Machine.IterationBudgetCost
import MinCostFlow.Num.IPM.SlackPower
import MinCostFlow.Num.IPM.CostTerm
import MinCostFlow.Num.IPM.BarrierFromSlacks
import MinCostFlow.Num.IPM.LengthFromSlacks
import MinCostFlow.Num.IPM.GradientFromSlacks
import MinCostFlow.Num.NegativePower
import MinCostFlow.Num.Logarithm
import MinCostFlow.Num.Exponential
import MinCostFlow.Num.PositiveExponential
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Cost of the bounded machine target test

Separate the target's numerical work from the data structure's
operation rate. The numerical charge is linear in the edge count
per epoch, with a polynomial in the input bit length.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Exact grouping of one stage and all of its loop control. -/
theorem targetStage_cost_split {w : ℕ} (F : MinRatioFormat w)
    (m E : ℕ) (rate : ℕ → ℕ) :
    epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59=
      m*(9*(Num.IPM.lengthCost F.limbs F.fmt.precision E+Num.IPM.gradientCost F.limbs F.fmt.precision E)+
        152*F.limbs^2+13880*F.limbs+46826)+(30*m+1)*rate m+244*F.limbs+2270 := by
  simp only [epochBaseCost,targetStageContinuationCost,Num.IPM.lengthArrayCost,Num.IPM.gradientArrayCost,
    budgetedIterationCharge,reportedEdgesCharge]
  ring

/-- The chosen limb count, precision and range exponent are bounded
by the same explicit quadratic in the input bit length. -/
theorem target_format_bit_bound (m U : ℕ) (hm : 0<m) :
    let W := 30000000*(m.size+U.size)^2
    ipmLimbs m U≤W ∧ ipmPrecision m U≤W ∧ ipmRangeExponent m U≤W := by
  let b := m.size+U.size
  have hb : 1≤b := by have hh := Nat.size_pos.mpr hm; omega
  have hS : b≤b^2 := by nlinarith only [hb]
  have hO : 1≤b^2 := le_trans hb hS
  have hmS : m.size≤b := Nat.le_add_right _ _
  change ipmLimbs m U≤30000000*b^2 ∧ ipmPrecision m U≤30000000*b^2 ∧ ipmRangeExponent m U≤30000000*b^2
  simp only [ipmLimbs,ipmPrecision,ipmErrorBits,ipmRangeExponent,gradientCoefficientExponent,
    slackRangeExponent,Num.IPM.alphaScale]
  dsimp only [b] at hb hS hO hmS ⊢
  omega

private theorem numerical_stage_factor_bound (L P E W : ℕ) (hW : 1≤W)
    (hL : L≤W) (hP : P≤W) (hE : E≤W) :
    9*(Num.IPM.lengthCost L P E+Num.IPM.gradientCost L P E)+
      152*L^2+14124*L+49096≤100000000*W^3 := by
  have hm : 9*(Num.IPM.lengthCost L P E+Num.IPM.gradientCost L P E)+
        152*L^2+14124*L+49096≤
      9*(Num.IPM.lengthCost W W W+Num.IPM.gradientCost W W W)+152*W^2+14124*W+49096 := by
    simp only [Num.IPM.lengthCost,Num.IPM.gradientCost,Num.IPM.lengthFromSlacksCost,
      Num.IPM.gradientFromSlacksCost,Num.IPM.barrierFromSlacksCost,Num.IPM.costTermCost,Num.IPM.slackPowerCost,
      Num.negativePowerCost,Num.logarithmCost,Num.exponentialCost,Num.positiveExponentialCost]
    gcongr
  apply hm.trans
  have hw2 : W≤W^2 := by nlinarith only [hW]
  have hw3 : W^2≤W^3 := by
    rw [show W^3=W^2*W from pow_succ W 2]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (W^2) hW
  have hw1 : W≤W^3 := hw2.trans hw3
  have hw0 : 1≤W^3 := hW.trans hw1
  simp only [Num.IPM.lengthCost,Num.IPM.gradientCost,Num.IPM.lengthFromSlacksCost,
    Num.IPM.gradientFromSlacksCost,Num.IPM.barrierFromSlacksCost,Num.IPM.costTermCost,Num.IPM.slackPowerCost,
    Num.negativePowerCost,Num.logarithmCost,Num.exponentialCost,Num.positiveExponentialCost]
  ring_nf
  omega

/-- One target-test stage has a cubic numerical cost per edge when
the limb count, precision, and range exponent are at most `W`. -/
theorem targetStage_cost_width_bound {w : ℕ} (F : MinRatioFormat w)
    (m E W : ℕ) (hm : 0<m) (rate : ℕ → ℕ)
    (hW : 1≤W) (hL : F.limbs≤W) (hP : F.fmt.precision≤W) (hE : E≤W) :
    epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59≤
      m*(100000000*W^3)+(30*m+1)*rate m := by
  let L := F.limbs
  let P := F.fmt.precision
  have hn := numerical_stage_factor_bound L P E W hW hL hP hE
  have hAbsorb : 244*L+2270≤m*(244*L+2270) := Nat.le_mul_of_pos_left _ hm
  have hM := Nat.mul_le_mul_left m hn
  rw [targetStage_cost_split]
  change m*(9*(Num.IPM.lengthCost L P E+Num.IPM.gradientCost L P E)+152*L^2+13880*L+46826)+
    (30*m+1)*rate m+244*L+2270≤m*(100000000*W^3)+(30*m+1)*rate m
  let lhs := m*(9*(Num.IPM.lengthCost L P E+Num.IPM.gradientCost L P E)+152*L^2+13880*L+46826)+
    (30*m+1)*rate m
  calc
    _ = lhs+(244*L+2270) := Nat.add_assoc lhs (244*L) 2270
    _ ≤ lhs+m*(244*L+2270) := Nat.add_le_add_left hAbsorb lhs
    _ = m*(9*(Num.IPM.lengthCost L P E+Num.IPM.gradientCost L P E)+152*L^2+14124*L+49096)+
        (30*m+1)*rate m := by dsimp only [lhs]; ring
    _ ≤ _ := Nat.add_le_add_right hM _

/-- One complete target-test stage costs a linear number of calls,
with explicit bit-polynomial numerical work per edge. -/
theorem targetStage_cost_bit_bound (m U : ℕ) {w : ℕ} (hw : ipmParameterWordBits m U≤w)
    (hm : 0<m) (rate : ℕ → ℕ) :
    let F := ipmMinRatioFormat m U hw
    let E := ipmRangeExponent m U
    epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59≤
      m*(100000000*(30000000*(m.size+U.size)^2)^3)+(30*m+1)*rate m := by
  dsimp only
  let F := ipmMinRatioFormat m U hw
  let E := ipmRangeExponent m U
  let W := 30000000*(m.size+U.size)^2
  obtain ⟨hL,hP,hE⟩ := target_format_bit_bound m U hm
  have hW : 1≤W := by
    have hb : 0<m.size+U.size := by have hh := Nat.size_pos.mpr hm; omega
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by decide) (pow_ne_zero _ hb.ne'))
  exact targetStage_cost_width_bound F m E W hm rate hW hL hP hE

/-- The epoch count itself is at most cubic in the input bit length
and quadratic in inverse quality. -/
theorem targetTest_limit_bit_bound (m U k : ℕ) (hsize : 2≤m*U) :
    (targetTestLimit m U k:ℝ)≤3276800000000001*(m.size+U.size:ℕ)^3*((2:ℝ)^k)^2 := by
  have hm : 0<m := by
    by_contra h
    have he : m=0 := by omega
    simp [he] at hsize
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  let B := (m.size+U.size:ℕ)
  let e := dyadicEpochLimit B k (Num.IPM.alphaExponent m U)
  have hh := dyadicIterationBudget_bit_bound m U k hsize
  rw [← dyadicEpochLimit_mul,Nat.cast_mul] at hh
  have hBound : (e:ℝ)≤3276800000000000*(B:ℝ)^3*((2:ℝ)^k)^2 := by
    apply le_of_mul_le_mul_left (a:=(m:ℝ)) _ hmR
    convert hh using 1
    ring
  have hB : (1:ℝ)≤B := by
    exact_mod_cast (show 1≤B by have hbits := Nat.size_pos.mpr hm; dsimp only [B]; omega)
  have hPow : (1:ℝ)≤(B:ℝ)^3*((2:ℝ)^k)^2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  change ((e+1:ℕ):ℝ)≤3276800000000001*(B:ℝ)^3*((2:ℝ)^k)^2
  push_cast
  linarith only [hBound,hPow]

/-- The machine cost bound has the paper's nearly linear shape in the
edge count, with the stated data structure charge paid per epoch. -/
theorem targetTest_cost_log_bound (m U k : ℕ) {w : ℕ}
    (hw : ipmParameterWordBits m U≤w) (hm : 0<m) (hsize : 2≤m*U)
    (rate : ℕ → ℕ) (cost : ℕ)
    (hc : let F := ipmMinRatioFormat m U hw
      cost≤targetTestLimit m U k*
        (epochBaseCost m F.limbs+targetStageContinuationCost F m (ipmRangeExponent m U) rate+81+59)+50) :
    let b := 5*Real.log ((m*U:ℕ):ℝ)
    (cost:ℝ)≤3276800000000001*b^3*((2:ℝ)^k)^2*
      ((m:ℝ)*(100000000*(30000000*b^2)^3)+((30*m+1:ℕ):ℝ)*rate m)+50 := by
  dsimp only at hc ⊢
  let b := 5*Real.log ((m*U:ℕ):ℝ)
  let B := (m.size+U.size:ℕ)
  have hbits : (B:ℝ)≤b := (Num.IPM.alpha_bit_length_bounds hsize).2
  have hB : (0:ℝ)≤B := Nat.cast_nonneg _
  have habs := targetStage_cost_bit_bound m U hw hm rate
  have h1 := hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (targetTestLimit m U k) habs) 50)
  have h1' : (cost:ℝ)≤(targetTestLimit m U k:ℝ)*
      ((m:ℝ)*(100000000*(30000000*(B:ℝ)^2)^3)+((30*m+1:ℕ):ℝ)*rate m)+50 := by
    dsimp only [B]
    exact_mod_cast h1
  have hlimit : (targetTestLimit m U k:ℝ)≤3276800000000001*b^3*((2:ℝ)^k)^2 :=
    (targetTest_limit_bit_bound m U k hsize).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hbits 3) (by positivity))
        (by positivity))
  apply h1'.trans
  gcongr

end MinCostFlow.IPM.Machine
