module

public import MinCostFlow.IPM.Machine.TargetSearchProgram
public import MinCostFlow.IPM.Machine.TargetTestCost
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Number and cost of the target comparisons

The span uses one sign-range bit and the bits of the edge count
and two capacity factors. This gives the extra logarithmic factor
from the integer bisection.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The bisection and final recovery run use at most the stated
number of target tests in terms of the input length. -/
theorem targetSearch_rounds_bit_bound (m U : ℕ) :
    targetSearchRounds (m*U^2)+1≤2+2*(m.size+U.size) := by
  have hx := Nat.lt_size_self m
  have hy := Nat.lt_size_self U
  have hy' : U^2<((2:ℕ)^U.size)^2 := Nat.pow_lt_pow_left hy (by decide)
  have hp : m*U^2<(2:ℕ)^m.size*((2:ℕ)^U.size)^2 := Nat.mul_lt_mul_of_lt_of_lt hx hy'
  have hh : 2*(m*U^2)<2^(1+m.size+2*U.size) := by
    rw [pow_add,pow_add,show 2*U.size=U.size*2 by omega,pow_mul,pow_one,mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left hp (by decide)
  have h := (Nat.size_le).mpr hh
  change (2*(m*U^2)).size≤1+m.size+2*U.size at h
  unfold targetSearchRounds
  omega

private theorem search_bound_reals (cost rounds test L b bound : ℝ)
    (hcost : cost≤rounds*(test+100*L+369)) (hround : rounds≤2+2*b)
    (htest : test≤bound+50) (hL : L≤30000000*b^2)
    (hb : 0≤b) (ht : 0≤test) (hl : 0≤L) :
    cost≤(2+2*b)*(bound+3000000000*b^2+419) :=
  hcost.trans (mul_le_mul hround (by linarith only [htest,hL])
    (by linarith only [ht,hl]) (by linarith only [hb]))

/-- The complete search's operation count has an explicit nearly
linear numerical term and the summed data structure charge. -/
theorem targetSearch_cost_log_bound (m U k : ℕ) {w : ℕ}
    (hw : ipmParameterWordBits m U≤w) (hm : 0<m) (hsize : 2≤m*U)
    (rate : ℕ → ℕ) (cost : ℕ)
    (hc : cost≤targetSearchCost (ipmMinRatioFormat m U hw) m U k (ipmRangeExponent m U) rate) :
    let b := 5*Real.log ((m*U:ℕ):ℝ)
    (cost:ℝ)≤(2+2*b)*
      (3276800000000001*b^3*((2:ℝ)^k)^2*
        ((m:ℝ)*(100000000*(30000000*b^2)^3)+((30*m+1:ℕ):ℝ)*rate m)+
        3000000000*b^2+419) := by
  dsimp only
  let b := 5*Real.log ((m*U:ℕ):ℝ)
  let F := ipmMinRatioFormat m U hw
  let E := ipmRangeExponent m U
  let test := targetTestLimit m U k*(epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59)+50
  have htest := targetTest_cost_log_bound m U k hw hm hsize rate test le_rfl
  have hbits : ((m.size+U.size:ℕ):ℝ)≤b := (Num.IPM.alpha_bit_length_bounds hsize).2
  have hround : ((targetSearchRounds (m*U^2)+1:ℕ):ℝ)≤2+2*b := by
    have hr : ((targetSearchRounds (m*U^2)+1:ℕ):ℝ)≤2+2*((m.size+U.size:ℕ):ℝ) := by
      exact_mod_cast targetSearch_rounds_bit_bound m U
    linarith only [hr,hbits]
  have hins : (F.limbs:ℝ)≤30000000*b^2 := by
    have hL := (target_format_bit_bound m U hm).1
    have hL' : (F.limbs:ℝ)≤30000000*((m.size+U.size:ℕ):ℝ)^2 := by
      change (↑(ipmLimbs m U):ℝ)≤_
      exact_mod_cast hL
    exact hL'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbits 2) (by positivity))
  have hcost : cost≤(targetSearchRounds (m*U^2)+1)*(test+100*F.limbs+369) := by
    change cost≤(targetSearchRounds (m*U^2)+1)*(targetOffsetCost F m U k E rate+69) at hc
    have heq : targetOffsetCost F m U k E rate+69=test+100*F.limbs+369 := by
      dsimp only [targetOffsetCost,test]
      have hh : epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59=
          epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+140 := by omega
      rw [hh]
      omega
    exact heq ▸ hc
  have hcost' : (cost:ℝ)≤((targetSearchRounds (m*U^2)+1:ℕ):ℝ)*((test:ℝ)+100*F.limbs+369) := by
    exact_mod_cast hcost
  exact search_bound_reals _ _ _ _ b _ hcost' hround htest hins ((Nat.cast_nonneg _).trans hbits)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Search work in terms of an upper bound on the numerical dimensions.
Each target test uses the paper's iteration bound, and bisection charges
each such test together with its local offset work. -/
theorem targetSearch_cost_width_bound {w : ℕ} (F : MinRatioFormat w)
    (m U k E W : ℕ) (hm : 0<m) (rate : ℕ → ℕ)
    (hW : 1≤W) (hL : F.limbs≤W) (hP : F.fmt.precision≤W) (hE : E≤W) :
    targetSearchCost F m U k E rate ≤ (2+2*(m.size+U.size))*
      (targetTestLimit m U k*(m*(100000000*W^3)+(30*m+1)*rate m)+100*W+419) := by
  have hStage := targetStage_cost_width_bound F m E W hm rate hW hL hP hE
  have hRounds := targetSearch_rounds_bit_bound m U
  unfold targetSearchCost targetOffsetCost
  apply Nat.mul_le_mul hRounds
  have hTest := Nat.mul_le_mul_left (targetTestLimit m U k) hStage
  have hOffset := Nat.mul_le_mul_left 100 hL
  have hSum : epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+81+59 =
      epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+140 := by omega
  rw [hSum] at hTest
  omega

end MinCostFlow.IPM.Machine
