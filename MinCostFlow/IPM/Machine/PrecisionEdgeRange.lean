module

public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.Num.IPM.EdgeFacts
import MinCostFlow.Num.IPM.DivideFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Ranges of computed gradient and length entries

The slack ranges bound the two negative powers in Definition 4.2 of
Chen et al., arXiv:2203.00671v2 (page 24). The integer-cost coefficient
bound and positive residual bound control the remaining gradient term.
The numerical error tolerances then give ranges for the stored values
sent to the min-ratio data structure.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A positive slack's upper bound alone bounds its negative power
below. No lower slack bound, potential bound or target-side premise is
needed for the unconditional Query range argument. -/
theorem slack_power_lower_of_upper_bound {s a : ℝ} {E : ℕ}
    (hs : 0<s) (hu : s≤(2:ℝ)^E) (ha : 0≤a) (ha' : a≤1) :
    1/(2:ℝ)^(2*E)≤Real.rpow s (-1-a) := by
  have hp : (1:ℝ)≤(2:ℝ)^E := one_le_pow₀ (by norm_num)
  have hlo : 1/(2:ℝ)^E≤1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
  have hbound := (Num.IPM.slack_power_dyadic_bounds (hlo.trans hp) le_rfl ha ha').1
  exact hbound.trans (Real.rpow_le_rpow_of_nonpos hs hu (by linarith only [ha]))

/-- A numerically approximated length has the capacity-based lower bound
using only strict slacks and an upper bound on one slack. This also
covers accepted histories for guesses below the optimum. -/
theorem stored_length_lower_of_upper_slack {u d a ell : ℝ} {E q : ℕ}
    (hu : 0<u) (hd : 0<d) (hu' : u≤(2:ℝ)^E) (ha : 0≤a) (ha' : a≤1)
    (hell : ScalarApprox (1+1/(2:ℝ)^q) ell (Real.rpow u (-1-a)+Real.rpow d (-1-a))) :
    1/(2:ℝ)^(2*E+1)≤ell := by
  have hpower := slack_power_lower_of_upper_bound hu hu' ha ha'
  have hother : 0≤Real.rpow d (-1-a) := Real.rpow_nonneg hd.le _
  have hexact : 1/(2:ℝ)^(2*E)≤Real.rpow u (-1-a)+Real.rpow d (-1-a) :=
    hpower.trans (le_add_of_nonneg_right hother)
  have hp : (1:ℝ)≤(2:ℝ)^q := one_le_pow₀ (by norm_num)
  have hdelta : 1/(2:ℝ)^q≤1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
  have hb : 0<1+1/(2:ℝ)^q := by positivity
  have hb' : 1+1/(2:ℝ)^q≤2 := by linarith only [hdelta]
  have hi : (2:ℝ)⁻¹≤(1+1/(2:ℝ)^q)⁻¹ := (inv_le_inv₀ (by norm_num) hb).mpr hb'
  have hfirst := mul_le_mul_of_nonneg_left hexact (by norm_num : (0:ℝ)≤1/2)
  have hsecond := mul_le_mul_of_nonneg_right hi hell.2.1.le
  have heq : 1/(2:ℝ)^(2*E+1)=(1/2)*(1/(2:ℝ)^(2*E)) := by rw [pow_succ]; ring
  rw [heq]
  exact hfirst.trans (by simpa only [one_div] using hsecond.trans hell.2.2.1)

/-- Uniform bounds for the exact edge length from its slack ranges. -/
theorem length_dyadic_range {I : Instance} {a : ℝ} {f : Fin I.m → ℝ}
    {E : ℕ} (ha : 0 ≤ a) (ha' : a ≤ 1) (e : Fin I.m)
    (hu : 1/(2:ℝ)^E ≤ (I.edge e).upper-f e ∧ (I.edge e).upper-f e ≤ (2:ℝ)^E)
    (hd : 1/(2:ℝ)^E ≤ f e-(I.edge e).lower ∧ f e-(I.edge e).lower ≤ (2:ℝ)^E) :
    1/(2:ℝ)^(2*E) ≤ lengths I a f e ∧ lengths I a f e ≤ 2*(2:ℝ)^(2*E) := by
  have hp := Num.IPM.slack_power_dyadic_bounds hu.1 hu.2 ha ha'
  have hq := Num.IPM.slack_power_dyadic_bounds hd.1 hd.2 ha ha'
  have hnonneg : 0 ≤ Real.rpow (f e-(I.edge e).lower) (-1-a) :=
    Real.rpow_nonneg (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(2:ℝ)^E) hd.1).le _
  unfold lengths
  constructor
  · exact hp.1.trans (le_add_of_nonneg_right hnonneg)
  · linarith only [hp.2,hq.2]

/-- A factor-two stored length has two more bits of range than either
power. Its lower bound follows from the multiplicative tolerance. -/
theorem stored_length_dyadic_range {I : Instance} {a z : ℝ} {f : Fin I.m → ℝ}
    {E : ℕ} (ha : 0 ≤ a) (ha' : a ≤ 1) (e : Fin I.m)
    (hu : 1/(2:ℝ)^E ≤ (I.edge e).upper-f e ∧ (I.edge e).upper-f e ≤ (2:ℝ)^E)
    (hd : 1/(2:ℝ)^E ≤ f e-(I.edge e).lower ∧ f e-(I.edge e).lower ≤ (2:ℝ)^E)
    (hz : ScalarApprox 2 z (lengths I a f e)) :
    1/(2:ℝ)^(2*E+1) ≤ z ∧ z ≤ (2:ℝ)^(2*E+2) := by
  have hh := length_dyadic_range ha ha' e hu hd
  have hlo := mul_le_mul_of_nonneg_left hh.1 (by norm_num : (0:ℝ) ≤ 1/2)
  have hhi := hz.2.2.2.trans (mul_le_mul_of_nonneg_left hh.2 (by norm_num : (0:ℝ) ≤ 2))
  constructor
  · have he : 1/(2:ℝ)^(2*E+1) = (1/2)*(1/(2:ℝ)^(2*E)) := by rw [pow_succ]; ring
    rw [he]
    exact hlo.trans (by simpa using hz.2.2.1)
  · convert hhi using 1; ring

/-- A gradient approximation with error at most one exact length fits
an explicit range derived from the coefficient and slack exponents. -/
theorem stored_gradient_dyadic_bound {I : Instance} {a F z : ℝ} {f : Fin I.m → ℝ}
    {E K : ℕ} (ha : 0 ≤ a) (ha' : a ≤ 1) (e : Fin I.m)
    (hu : 1/(2:ℝ)^E ≤ (I.edge e).upper-f e ∧ (I.edge e).upper-f e ≤ (2:ℝ)^E)
    (hd : 1/(2:ℝ)^E ≤ f e-(I.edge e).lower ∧ f e-(I.edge e).lower ≤ (2:ℝ)^E)
    (hr : 1/(2:ℝ)^E ≤ residual I F f)
    (hc : |20*(I.m:ℝ)*(I.edge e).cost| ≤ (2:ℝ)^K)
    (hz : |z-gradient I a F f e| ≤ lengths I a f e) :
    |z| ≤ (2:ℝ)^(K+2*E+3) := by
  have hp := Num.IPM.slack_power_dyadic_bounds hu.1 hu.2 ha ha'
  have hq := Num.IPM.slack_power_dyadic_bounds hd.1 hd.2 ha ha'
  have hl := (length_dyadic_range ha ha' e hu hd).2
  have hquot := Num.IPM.quotient_bound hc hr
  have hcosteq : (20*(I.m:ℝ)*(I.edge e).cost)/residual I F f =
      20*I.m*(residual I F f)⁻¹*(I.edge e).cost := by ring
  rw [hcosteq] at hquot
  have hple : (2:ℝ)^(K+E) ≤ (2:ℝ)^(K+2*E) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpowle : (2:ℝ)^(2*E) ≤ (2:ℝ)^(K+2*E) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hbar : |a*Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a) -
      a*Real.rpow (f e-(I.edge e).lower) (-1-a)| ≤ lengths I a f e := by
    have hp0 : 0 ≤ Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a) :=
      (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(2:ℝ)^(2*E)) hp.1).le
    have hq0 : 0 ≤ Real.rpow (f e-(I.edge e).lower) (-1-a) :=
      (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(2:ℝ)^(2*E)) hq.1).le
    have hpa := mul_le_of_le_one_left hp0 ha'
    have hqa := mul_le_of_le_one_left hq0 ha'
    apply abs_le.mpr
    unfold lengths
    constructor <;> linarith only [hpa,hqa,mul_nonneg ha hp0,mul_nonneg ha hq0,hp0,hq0]
  have hg : |gradient I a F f e| ≤ (2:ℝ)^(K+E)+lengths I a f e := by
    have ht := abs_add_le (20*I.m*(residual I F f)⁻¹*(I.edge e).cost)
      (a*Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a)-a*Real.rpow (f e-(I.edge e).lower) (-1-a))
    have he : gradient I a F f e = 20*I.m*(residual I F f)⁻¹*(I.edge e).cost+
      (a*Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a)-a*Real.rpow (f e-(I.edge e).lower) (-1-a)) := by
      unfold gradient; ring
    rw [he]
    exact ht.trans (add_le_add hquot hbar)
  have hz' : |z| ≤ |z-gradient I a F f e|+|gradient I a F f e| :=
    by simpa only [sub_add_cancel] using abs_add_le (z-gradient I a F f e) (gradient I a F f e)
  have hfinal : (2:ℝ)^(K+2*E+3) = 8*(2:ℝ)^(K+2*E) := by rw [pow_add]; norm_num; ring
  rw [hfinal]
  have hnonneg : (0:ℝ) ≤ (2:ℝ)^(K+2*E) := by positivity
  linarith only [hz',hz,hg,hl,hple,hpowle,hnonneg]

/-- The common DS range `R` covers approximate edge coefficients
computed using the smaller slack range `Es`. -/
theorem stored_coefficients_in_chosen_range (I : Instance) (U : ℕ)
    (a F z ell : ℝ) (f : Fin I.m → ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hnums : NumbersBounded I U) (e : Fin I.m)
    (hu : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ (I.edge e).upper-f e ∧
      (I.edge e).upper-f e ≤ (2:ℝ)^(slackRangeExponent I.m U))
    (hd : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ f e-(I.edge e).lower ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(slackRangeExponent I.m U))
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U) ≤ residual I F f)
    (hell : ScalarApprox 2 ell (lengths I a f e))
    (hz : |z-gradient I a F f e| ≤ lengths I a f e) :
    |z| ≤ (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ ell ∧
      ell ≤ (2:ℝ)^(ipmRangeExponent I.m U) := by
  have hcInt := gradient_instance_coefficient_bound I U hnums e
  have hc : |20*(I.m:ℝ)*(I.edge e).cost| ≤
      (2:ℝ)^(gradientCoefficientExponent I.m U) := by exact_mod_cast hcInt
  have hg := stored_gradient_dyadic_bound ha ha' e hu hd hr hc hz
  have hl := stored_length_dyadic_range ha ha' e hu hd hell
  have hgexp : gradientCoefficientExponent I.m U+2*slackRangeExponent I.m U+3 ≤
      ipmRangeExponent I.m U := by unfold ipmRangeExponent; omega
  have hlexp : 2*slackRangeExponent I.m U+2 ≤ ipmRangeExponent I.m U := by
    unfold ipmRangeExponent; omega
  have hlowexp : 2*slackRangeExponent I.m U+1 ≤ ipmRangeExponent I.m U := by omega
  refine ⟨hg.trans (pow_le_pow_right₀ (by norm_num) hgexp), ?_,
    hl.2.trans (pow_le_pow_right₀ (by norm_num) hlexp)⟩
  exact (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hlowexp)).trans hl.1

end MinCostFlow.IPM.Machine
