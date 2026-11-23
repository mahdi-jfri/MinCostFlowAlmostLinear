module

public import MinCostFlow.IPM.Machine.StrictGuardRanges
import Mathlib.Tactic.Linarith

/-!
# Guard ranges between full residual refreshes

The stopping guard is checked when an epoch forms its exact residual.
During that epoch the held residual approximates the current one. A
held residual above one quarter and approximation factor at most two
keep the current residual above one eighth. This still supplies the
logarithmic lower bound needed by the potential-to-slack argument, so
checking the residual only at full refreshes does not lose numeric safety.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A nonterminal held residual and a factor-two approximation keep the
true residual above one eighth throughout the epoch. -/
theorem current_residual_gt_eighth {stored current eps : ℝ}
    (hr : ScalarApprox (1+eps) stored current) (heps : eps ≤ 1)
    (hstop : 1/4 < stored) : 1/8 < current := by
  have hfactor := mul_le_mul_of_nonneg_right
    (show 1+eps ≤ (2:ℝ) by linarith only [heps]) hr.2.1.le
  linarith only [hr.2.2.2,hfactor,hstop]

/-- The selected source slack exponent also covers the epoch's lower
residual endpoint. -/
theorem dyadic_le_eighth (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    1/(2:ℝ)^(slackRangeExponent m U) ≤ 1/8 := by
  have hb : 0 < m.size := Nat.size_pos.mpr hm
  have hu : 0 < U.size := Nat.size_pos.mpr hU
  have hs : 1 ≤ (m.size+U.size)^2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have he : 3 ≤ slackRangeExponent m U := by unfold slackRangeExponent; omega
  have hp : (8:ℝ) ≤ (2:ℝ)^(slackRangeExponent m U) := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he using 1
    norm_num
  exact one_div_le_one_div_of_le (by norm_num) hp

/-- The one-eighth epoch lower bound implies the same logarithmic lower
bound used by the potential-to-barrier argument. -/
theorem epoch_residual_log_lower (size R : ℝ) (hsize : 2 ≤ size) (hR : 1/8 ≤ R) :
    -10*Real.log size ≤ Real.log R := by
  have hspos : 0 < size := lt_of_lt_of_le (by norm_num) hsize
  have hp : (8:ℝ) ≤ size^10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hsize 10
    exact (by norm_num : (8:ℝ) ≤ 2^10).trans hh
  have hrec := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) hp
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 1/size^10) hrec
  have he : Real.log (1/size^10)=-10*Real.log size := by
    rw [one_div,Real.log_inv,Real.log_pow]
    ring
  rw [he] at hlog
  exact hlog.trans (Real.log_le_log (by norm_num : (0:ℝ) < 1/8) hR)

/-- The preserved potential supplies safe residual and slack ranges
throughout an epoch, including after the true residual passes the
stopping threshold but before its next full refresh. -/
theorem epoch_numeric_ranges (I : Instance) (U : ℕ) (F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hF : -(I.m*(U:ℝ)^2) ≤ F) (hr : 1/8 ≤ residual I F f) :
    (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ residual I F f ∧
      residual I F f ≤ (2:ℝ)^(slackRangeExponent I.m U)) ∧
    ∀ e, (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ (I.edge e).upper-f e ∧
      (I.edge e).upper-f e ≤ (2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ f e-(I.edge e).lower ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(slackRangeExponent I.m U)) := by
  have hu : 0 < U := by omega
  have hfeas : I.IsFeasible f := ⟨hroute,fun e => ⟨(hf e).1.le,(hf e).2.le⟩⟩
  have hc := (abs_le.mp (feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums f hfeas)).2
  have hlog := epoch_residual_log_lower (I.m*(U:ℝ)) (residual I F f)
    (by exact_mod_cast hsize) hr
  refine ⟨⟨(dyadic_le_eighth I.m U hm hu).trans hr,?_⟩,?_⟩
  · apply le_trans (b:=2*(I.m:ℝ)*(U:ℝ)^2)
    · unfold residual
      linarith only [hc,hF]
    · exact twice_search_radius_le_dyadic I.m U hm hu
  · intro e
    have hl := slacks_dyadic_lower I U F f hm hU hsize hf hpot hlog e
    have hh := slacks_dyadic_upper I U f hm hu hnums hf e
    exact ⟨⟨hl.1,hh.1⟩,⟨hl.2,hh.2⟩⟩

/-- The actual strict machine range guards also accept all residuals
and slacks in the epoch-safe potential-derived range. -/
theorem epoch_strict_guard_ranges (I : Instance) (U : ℕ) (F : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hF : -(I.m*(U:ℝ)^2) ≤ F) (hr : 1/8 ≤ residual I F f) :
    (1/(2:ℝ)^(ipmRangeExponent I.m U) < residual I F f ∧
      residual I F f < (2:ℝ)^(ipmRangeExponent I.m U)) ∧
    ∀ e, (1/(2:ℝ)^(ipmRangeExponent I.m U) < (I.edge e).upper-f e ∧
      (I.edge e).upper-f e < (2:ℝ)^(ipmRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(ipmRangeExponent I.m U) < f e-(I.edge e).lower ∧
      f e-(I.edge e).lower < (2:ℝ)^(ipmRangeExponent I.m U)) := by
  have hh := epoch_numeric_ranges I U F f hm hU hsize hnums hf hroute hpot hF hr
  refine ⟨strict_guard_range_of_slack_range I.m U hh.1,?_⟩
  intro e
  exact ⟨strict_guard_range_of_slack_range I.m U (hh.2 e).1,
    strict_guard_range_of_slack_range I.m U (hh.2 e).2⟩

end MinCostFlow.IPM.Machine
