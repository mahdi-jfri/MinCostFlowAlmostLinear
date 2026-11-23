module

public import MinCostFlow.IPM.Machine.PrecisionRoundedStep
public import MinCostFlow.IPM.Machine.PrecisionEta
public import MinCostFlow.IPM.Machine.NormalizationProgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Admissibility after all scalar normalization errors

The epoch residual estimate, storage of the requested normalization,
and the data structure's scalar rounding are combined before taking
the effective step parameter. This retains exactly the interval in the
adapted Lemma 9.3 (Chen et al., arXiv:2203.00671v2, page 71).
The same exponent is used by every gradient, length and potential.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The normalization conversion only needs a bound on the product of
scalar errors, rather than separate factor-two bounds for each one. -/
theorem rounded_step_normalization_of_product (I : Instance) (a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hq : 0 < q)
    (hslo : (1/2:ℝ) ≤ s) (hrpos : 0 < r)
    (hsrlo : (1/4:ℝ) ≤ s*r) (hsrhi : s*r ≤ 4)
    (hg : GradientTolerance (lengths I a f)
      (fun e => s*g e) (gradient I a F f) (q/16))
    (hqual : dot g d / weightedLength l d ≤ -4*q) :
    ∃ p : ℝ, q/2 ≤ p ∧ p ≤ 2*q ∧
      GradientTolerance (lengths I a f) (fun e => s*g e)
        (gradient I a F f) (p/8) ∧
      dot (fun e => s*g e) d / weightedLength l d ≤ -p ∧
      r*q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hsqrt0 := Real.sqrt_nonneg (s*r)
  have hsqrt := Real.sq_sqrt (mul_pos hspos hrpos).le
  have hlo : (1/2 : ℝ) ≤ Real.sqrt (s*r) := by nlinarith only [hsrlo, hsqrt0, hsqrt]
  have hhi : Real.sqrt (s*r) ≤ 2 := by nlinarith only [hsrhi, hsqrt0, hsqrt]
  let p := Real.sqrt (s*r)*q
  have hp : q/2 ≤ p := by
    have hh := mul_le_mul_of_nonneg_right hlo hq.le
    dsimp only [p]
    linarith only [hh]
  have hp' : p ≤ 2*q := mul_le_mul_of_nonneg_right hhi hq.le
  have hlen0 : 0 ≤ weightedLength l d := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength l d := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    rw [hz, div_zero] at hqual
    linarith only [hq, hqual]
  have hneg : dot g d < 0 := by
    have hh := (div_le_iff₀ hlen).mp hqual
    exact lt_of_le_of_lt hh (mul_neg_of_neg_of_pos (by linarith only [hq]) hlen)
  have hdot : dot (fun e => s*g e) d = s*dot g d := by
    simp only [dot, Finset.mul_sum, mul_assoc]
  have hg' : GradientTolerance (lengths I a f)
      (fun e => s*g e) (gradient I a F f) (p/8) := by
    intro e
    exact (hg e).trans (by linarith only [hp])
  have hqual' : dot (fun e => s*g e) d / weightedLength l d ≤ -p := by
    rw [hdot, mul_div_assoc]
    have hh := mul_le_mul_of_nonneg_left hqual hspos.le
    have hs := mul_le_mul_of_nonneg_right hslo hq.le
    linarith only [hh, hp', hs]
  have hp2 : p^2 = s*r*q^2 := by dsimp only [p]; rw [mul_pow, hsqrt]
  have hnorm : r*q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
    rw [hdot, abs_of_neg hneg, hp2]
    field_simp [hneg.ne]
  exact ⟨p,hp,hp',hg',hqual',hnorm⟩

/-- With the exact dyadic request and the DS's allowed scalar rounding,
the effective parameter remains in `[q/2,2q]`. No further loss is charged
for storing the normalization. -/
theorem dyadic_request_normalization (I : Instance) (a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hq : 0 < q)
    (hs : (3/4:ℝ) ≤ s ∧ s ≤ 4/3) (hr : (1/2:ℝ) ≤ r ∧ r ≤ 2)
    (hg : GradientTolerance (lengths I a f) (fun e => s*g e)
      (gradient I a F f) (q/16))
    (hqual : dot g d/weightedLength l d ≤ -4*q) :
    ∃ p : ℝ,q/2 ≤ p ∧ p ≤ 2*q ∧
      GradientTolerance (lengths I a f) (fun e => s*g e) (gradient I a F f) (p/8) ∧
      dot (fun e => s*g e) d/weightedLength l d ≤ -p ∧
      ((25/32:ℝ)*r)*q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
  have hprod := normalization_three_factor_bounds hs hr
    (by norm_num : (3/4:ℝ) ≤ 25/32 ∧ (25/32:ℝ) ≤ 5/4)
  rw [mul_comm r (25/32)] at hprod
  have hrpos : 0 < (25/32:ℝ)*r :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hr.1)
  exact rounded_step_normalization_of_product I a F q s ((25/32:ℝ)*r) f g l d hq
    (by linarith only [hs.1]) hrpos hprod.1 hprod.2 hg hqual

/-- The exactly stored request gives the same potential progress as
Lemma 9.3's effective-step interval, including all scalar errors. -/
theorem dyadic_request_step_decrease (I : Instance) (U a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hsize : 2 ≤ (I.m:ℝ)*U) (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hres : 0 < residual I F f) (hq : 0 < q) (hqUpper : q ≤ 1/2)
    (hs : (3/4:ℝ) ≤ s ∧ s ≤ 4/3) (hr : (1/2:ℝ) ≤ r ∧ r ≤ 2)
    (hg : GradientTolerance (lengths I a f) (fun e => s*g e)
      (gradient I a F f) (q/16))
    (hl : VectorApprox 2 l (lengths I a f)) (hd : IsCirculation I d)
    (hqual : dot g d/weightedLength l d ≤ -4*q) :
    let next := fun e => f e+(((25/32:ℝ)*r)*q^2/(50*|dot g d|))*d e
    I.Routes next ∧ StrictlyInside I next ∧ 0 < residual I F next ∧
      potential I a F next ≤ potential I a F f-q^2/2000 := by
  obtain ⟨p,hplo,hphi,hg',hqual',hnorm⟩ :=
    dyadic_request_normalization I a F q s r f g l d hq hs hr hg hqual
  have hp : 0 < p := (by linarith only [hq] : 0 < q/2).trans_le hplo
  have hp' : p ≤ 1 := hphi.trans (by linarith only [hqUpper])
  obtain ⟨hroute',hinside,hres',hpot⟩ := step_decrease_at_exponent I U a F p
    (((25/32:ℝ)*r)*q^2/(50*|dot g d|)) f (fun e => s*g e) l d
    hm hU hsize ha haUpper hnums hf hroute hres hp hp' hg' hl hd hqual' hnorm
  refine ⟨hroute',hinside,hres',hpot.trans ?_⟩
  have hsq := mul_self_le_mul_self (by linarith only [hq] : 0 ≤ q/2) hplo
  nlinarith only [hsq]

end MinCostFlow.IPM.Machine
