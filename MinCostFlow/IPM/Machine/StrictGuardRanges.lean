module

public import MinCostFlow.IPM.Machine.PrecisionRun
public import MinCostFlow.IPM.Machine.PrecisionParameters

/-!
# Potential-derived ranges lie strictly inside the machine guards

The potential argument bounds nonterminal slacks and the residual in
`[2^-Es,2^Es]`. The machine uses the larger exponent R for its range
guards. Since Es is strictly smaller than R, these guards accept every
number in the potential-derived range, including its endpoints.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Every value in the potential-derived dyadic range lies strictly
inside the selected machine guard interval. -/
theorem strict_guard_range_of_slack_range (m U : ℕ) {x : ℝ}
    (hx : 1/(2:ℝ)^(slackRangeExponent m U) ≤ x ∧ x ≤ (2:ℝ)^(slackRangeExponent m U)) :
    1/(2:ℝ)^(ipmRangeExponent m U) < x ∧ x < (2:ℝ)^(ipmRangeExponent m U) := by
  have hER : slackRangeExponent m U < ipmRangeExponent m U := by
    unfold ipmRangeExponent
    omega
  have hp : (2:ℝ)^(slackRangeExponent m U) < (2:ℝ)^(ipmRangeExponent m U) :=
    pow_lt_pow_right₀ (by norm_num) hER
  have hi := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < 2^(slackRangeExponent m U)) hp
  exact ⟨hi.trans_le hx.1,hx.2.trans_lt hp⟩

/-- The preserved potential at the stored barrier exponent guarantees
that every nonterminal residual and edge slack passes the strict range
guards. This follows from the proved nonterminal numerical ranges. -/
theorem nonterminal_strict_guard_ranges (I : Instance) (U : ℕ) (F : ℝ)
    (f : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hF : -(I.m*(U:ℝ)^2) ≤ F) (hr : 1/4 < residual I F f) :
    (1/(2:ℝ)^(ipmRangeExponent I.m U) < residual I F f ∧
      residual I F f < (2:ℝ)^(ipmRangeExponent I.m U)) ∧
    ∀ e, (1/(2:ℝ)^(ipmRangeExponent I.m U) < (I.edge e).upper-f e ∧
      (I.edge e).upper-f e < (2:ℝ)^(ipmRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(ipmRangeExponent I.m U) < f e-(I.edge e).lower ∧
      f e-(I.edge e).lower < (2:ℝ)^(ipmRangeExponent I.m U)) := by
  have hh := nonterminal_numeric_ranges I U F f hm hU hsize hnums hf hroute hpot hF hr
  refine ⟨strict_guard_range_of_slack_range I.m U hh.1,?_⟩
  intro e
  exact ⟨strict_guard_range_of_slack_range I.m U (hh.2 e).1,
    strict_guard_range_of_slack_range I.m U (hh.2 e).2⟩

/-- A value strictly inside the dyadic guards stays inside them when
the binary exponent increases. -/
theorem strict_guard_range_mono {E R : ℕ} {x : ℝ} (hER : E≤R)
    (hx : 1/(2:ℝ)^E<x ∧ x<(2:ℝ)^E) :
    1/(2:ℝ)^R<x ∧ x<(2:ℝ)^R := by
  have hp : (2:ℝ)^E≤(2:ℝ)^R := pow_le_pow_right₀ (by norm_num) hER
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^E) hp
  exact ⟨hi.trans_lt hx.1,hx.2.trans_le hp⟩

end MinCostFlow.IPM.Machine
