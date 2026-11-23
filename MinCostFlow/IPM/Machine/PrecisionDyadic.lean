module

public import MinCostFlow.IPM.Machine.PrecisionSlacks
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A binary range for the IPM slacks

The squared-log bound from the potential is converted to a range that the
fixed-point length procedures accept. Binary input lengths determine the
exponent without computing a real logarithm.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A binary exponent covering the potential-derived lower slack bound. -/
@[expose] def slackRangeExponent (m U : ℕ) : ℕ :=
  220000*(m.size+U.size)^2

/-- The chosen dyadic threshold is below the exponential threshold.
Only binary input lengths enter its definition. -/
theorem dyadic_le_slack_threshold (m U : ℕ) (hsize : 2 ≤ m*U) :
    1/(2:ℝ)^(slackRangeExponent m U) ≤
      Real.exp (-110000*(Real.log ((m*U:ℕ):ℝ))^2) := by
  have hlog := (Num.IPM.alpha_bit_length_bounds hsize).1
  have hlognn : 0 ≤ Real.log ((m*U:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m*U by omega))
  have hsq : (Real.log ((m*U:ℕ):ℝ))^2 ≤ ((m.size+U.size:ℕ):ℝ)^2 :=
    pow_le_pow_left₀ hlognn hlog 2
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht
    exact ht
  have hmul := mul_le_mul_of_nonneg_left htwo
    (Nat.cast_nonneg (slackRangeExponent m U) : (0:ℝ) ≤ slackRangeExponent m U)
  have he : ((slackRangeExponent m U:ℕ):ℝ) = 220000*((m.size+U.size:ℕ):ℝ)^2 := by
    simp only [slackRangeExponent,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [he] at hmul
  have hbound : -((slackRangeExponent m U:ℕ):ℝ)*Real.log 2 ≤
      -110000*(Real.log ((m*U:ℕ):ℝ))^2 := by
    rw [he]
    nlinarith only [hmul,hsq]
  calc
    1/(2:ℝ)^(slackRangeExponent m U) =
        Real.exp (-((slackRangeExponent m U:ℕ):ℝ)*Real.log 2) := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      exact one_div _
    _ ≤ _ := Real.exp_le_exp.mpr hbound

/-- At the representable exponent, the potential budget implies both
lower-slack premises required by the fixed-point length procedures. -/
theorem slacks_dyadic_lower (I : Instance) (U : ℕ) (F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hf : StrictlyInside I f)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hreslog : -10*Real.log (I.m*(U:ℝ)) ≤ Real.log (residual I F f)) (e : Fin I.m) :
    1/(2:ℝ)^(slackRangeExponent I.m U) ≤ (I.edge e).upper-f e ∧
      1/(2:ℝ)^(slackRangeExponent I.m U) ≤ f e-(I.edge e).lower := by
  have hsize' : (2:ℝ) ≤ I.m*(U:ℝ) := by exact_mod_cast hsize
  have hh := slacks_exp_lower I U F (Num.IPM.alphaPrime I.m U) f hm
    (by exact_mod_cast hU) hsize' (Num.IPM.alphaPrime_bounds I U hsize).1 hf hpot hreslog e
  have hd := dyadic_le_slack_threshold I.m U hsize
  simp only [Nat.cast_mul] at hd
  exact ⟨hd.trans hh.1,hd.trans hh.2⟩

/-- The same exponent covers the elementary upper bound `2U`. -/
theorem twice_capacity_le_dyadic (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    2*(U:ℝ) ≤ (2:ℝ)^(slackRangeExponent m U) := by
  have hb : 0 < m.size := Nat.size_pos.mpr hm
  have hu : 0 < U.size := Nat.size_pos.mpr hU
  have hs : U.size+1 ≤ slackRangeExponent m U := by
    unfold slackRangeExponent
    have hsquare : m.size+U.size ≤ (m.size+U.size)^2 := by
      have hn : 1 ≤ m.size+U.size := by omega
      nlinarith only [hn]
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hs
  have hu' := Nat.lt_size_self U
  have hbound : 2*U ≤ (2:ℕ)^(slackRangeExponent m U) := by
    rw [pow_succ] at hpow
    omega
  exact_mod_cast hbound

/-- Both upper-slack premises follow from capacity bounds and interiority. -/
theorem slacks_dyadic_upper (I : Instance) (U : ℕ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hnums : NumbersBounded I U)
    (hf : StrictlyInside I f) (e : Fin I.m) :
    (I.edge e).upper-f e ≤ (2:ℝ)^(slackRangeExponent I.m U) ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(slackRangeExponent I.m U) := by
  have hl := (abs_le.mp (hnums.2 e).1).1
  have hu := (abs_le.mp (hnums.2 e).2.1).2
  have hbound := twice_capacity_le_dyadic I.m U hm hU
  constructor
  · exact (by linarith only [hl,hu,(hf e).1] :
      ((I.edge e).upper:ℝ)-f e ≤ 2*(U:ℝ)).trans hbound
  · exact (by linarith only [hl,hu,(hf e).2] :
      f e-(I.edge e).lower ≤ 2*(U:ℝ)).trans hbound

end MinCostFlow.IPM.Machine
