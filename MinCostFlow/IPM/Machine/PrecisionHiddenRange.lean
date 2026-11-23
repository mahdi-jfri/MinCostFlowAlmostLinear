module

public import MinCostFlow.IPM.Machine.PrecisionCallRanges
public import MinCostFlow.IPM.HiddenWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit logarithmic ranges for hidden stability

Definition 4.4, item 5 (page 14 of arXiv:2309.16629v1), bounds the
logarithms of the hidden widths and supplied lengths. The machine
coefficient range and feasible flow bounds supply an explicit parameter.
The hidden widths are the source's `50+|ell*(fstar-f)|`.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Item 5's logarithmic bound obtained from the selected binary ranges. -/
@[expose] def precisionHiddenPsi (m U : ℕ) : ℝ :=
  (ipmRangeExponent m U+slackRangeExponent m U+6:ℕ)

private theorem abs_log_le_dyadic_exponent {x : ℝ} {E : ℕ}
    (hlo : 1/(2:ℝ)^E ≤ x) (hhi : x ≤ (2:ℝ)^E) :
    0 < x ∧ |Real.log x| ≤ E := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hloglo := Real.log_le_log (by positivity : (0:ℝ)<1/(2:ℝ)^E) hlo
  have hloghi := Real.log_le_log hx hhi
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by positivity),Real.log_one,Real.log_pow] at hloglo
  rw [Real.log_pow] at hloghi
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg E : (0:ℝ) ≤ E)
  refine ⟨hx,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith only [hloglo,hloghi,hh]

/-- Feasibility and the supplied length range bound the source hidden
width above by `2^(R+Es+6)`. -/
theorem hiddenWidth_dyadic_upper_at_range (I : Instance) (U R : ℕ)
    (fstar f ell : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hf : I.IsFeasible f)
    (e : Fin I.m) (hell : 0 ≤ ell e ∧ ell e ≤ (2:ℝ)^(R)) :
    hiddenWidth fstar f ell e ≤
      (2:ℝ)^(R+slackRangeExponent I.m U+6) := by
  have hstar := feasible_abs_le I U hnums fstar hs e
  have hcur := feasible_abs_le I U hnums f hf e
  have hsub : |fstar e-f e| ≤ |fstar e|+|f e| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (fstar e) (-(f e))
  have htwo := twice_capacity_le_dyadic I.m U hm hU
  have hdiff : |fstar e-f e| ≤ (2:ℝ)^(slackRangeExponent I.m U) := by
    linarith only [hstar,hcur,hsub,htwo]
  have hprod := mul_le_mul hell.2 hdiff (abs_nonneg _)
    (by positivity : (0:ℝ) ≤ (2:ℝ)^(R))
  rw [← pow_add] at hprod
  have hpow : (1:ℝ) ≤ (2:ℝ)^(R+slackRangeExponent I.m U) :=
    one_le_pow₀ (by norm_num)
  unfold hiddenWidth
  rw [abs_mul,abs_of_nonneg hell.1,pow_add]
  norm_num only [show (2:ℝ)^6=64 by norm_num]
  linarith only [hprod,hpow]

/-- Definition 4.4 item 5 (page 14), at one computed-coefficient stage,
with explicit `Psi=R+Es+6`. No hidden range conclusion is assumed. -/
theorem precision_hidden_log_ranges_at_range (I : Instance) (U R : ℕ)
    (fstar f ell : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hf : I.IsFeasible f)
    (e : Fin I.m)
    (hell : 1/(2:ℝ)^(R) ≤ ell e ∧
      ell e ≤ (2:ℝ)^(R)) :
    0 < hiddenWidth fstar f ell e ∧
      |Real.log (hiddenWidth fstar f ell e)| ≤ ((R+slackRangeExponent I.m U+6 : ℕ) : ℝ) ∧
      0 < ell e ∧ |Real.log (ell e)| ≤ ((R+slackRangeExponent I.m U+6 : ℕ) : ℝ) := by
  have hlength := abs_log_le_dyadic_exponent hell.1 hell.2
  have hw := hiddenWidth_ge fstar f ell e
  have hup := hiddenWidth_dyadic_upper_at_range I U R fstar f ell hm hU hnums hs hf e
    ⟨hlength.1.le,hell.2⟩
  have hlo : 1/(2:ℝ)^(R+slackRangeExponent I.m U+6) ≤
      hiddenWidth fstar f ell e := by
    have hh : 1/(2:ℝ)^(R+slackRangeExponent I.m U+6) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    linarith only [hh,hw]
  have hwidth := abs_log_le_dyadic_exponent hlo hup
  refine ⟨hwidth.1,hwidth.2,hlength.1,hlength.2.trans ?_⟩
  exact_mod_cast (show R ≤ R+slackRangeExponent I.m U+6 by omega)

/-- Feasibility and the supplied length range bound the source hidden
width above by `2^(R+Es+6)`. -/
theorem hiddenWidth_dyadic_upper (I : Instance) (U : ℕ)
    (fstar f ell : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hf : I.IsFeasible f)
    (e : Fin I.m) (hell : 0 ≤ ell e ∧ ell e ≤ (2:ℝ)^(ipmRangeExponent I.m U)) :
    hiddenWidth fstar f ell e ≤
      (2:ℝ)^(ipmRangeExponent I.m U+slackRangeExponent I.m U+6) :=
  hiddenWidth_dyadic_upper_at_range I U _ fstar f ell hm hU hnums hs hf e hell

/-- Definition 4.4 item 5 (page 14), at one computed-coefficient stage,
with explicit `Psi=R+Es+6`. No hidden range conclusion is assumed. -/
theorem precision_hidden_log_ranges (I : Instance) (U : ℕ)
    (fstar f ell : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hf : I.IsFeasible f)
    (e : Fin I.m)
    (hell : 1/(2:ℝ)^(ipmRangeExponent I.m U) ≤ ell e ∧
      ell e ≤ (2:ℝ)^(ipmRangeExponent I.m U)) :
    0 < hiddenWidth fstar f ell e ∧
      |Real.log (hiddenWidth fstar f ell e)| ≤ precisionHiddenPsi I.m U ∧
      0 < ell e ∧ |Real.log (ell e)| ≤ precisionHiddenPsi I.m U :=
  precision_hidden_log_ranges_at_range I U _ fstar f ell hm hU hnums hs hf e hell

end MinCostFlow.IPM.Machine
