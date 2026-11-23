module

public import MinCostFlow.IPM.Machine.PrecisionStepDecrease
public import MinCostFlow.IPM.Machine.RoundedStep
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Rounded normalization at the stored exponent

The scalar-rounding argument for Chen et al., arXiv:2203.00671v2,
Lemma 9.3 (page 71), is independent of the choice of barrier exponent.
The stored-residual ratio and scalar normalization error give an
effective parameter between half and twice the requested parameter.
All gradient and length expressions below use the same exponent.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The effective normalization interval from the adapted Lemma 9.3
(page 71), with an explicit barrier exponent. -/
theorem rounded_step_normalization_at_exponent (I : Instance) (a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hq : 0 < q)
    (hslo : (1/2 : ℝ) ≤ s) (hshi : s ≤ 2)
    (hrlo : (1/2 : ℝ) ≤ r) (hrhi : r ≤ 2)
    (hg : GradientTolerance (lengths I a f)
      (fun e => s*g e) (gradient I a F f) (q/16))
    (hqual : dot g d / weightedLength l d ≤ -4*q) :
    ∃ p : ℝ, q/2 ≤ p ∧ p ≤ 2*q ∧
      GradientTolerance (lengths I a f) (fun e => s*g e)
        (gradient I a F f) (p/8) ∧
      dot (fun e => s*g e) d / weightedLength l d ≤ -p ∧
      r*q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hrlo
  have hsrlo : (1/4 : ℝ) ≤ s*r := by
    have hh := mul_le_mul hslo hrlo (by norm_num : (0 : ℝ) ≤ 1/2) hspos.le
    norm_num at hh
    exact hh
  have hsrhi : s*r ≤ 4 := by
    have hh := mul_le_mul hshi hrhi hrpos.le (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh
    exact hh
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

/-- A scalar-rounded step preserves the domain and decreases the
potential by at least `q²/2000`. This combines the adapted Lemma 9.3
normalization interval with Lemma 4.4 at the stored exponent. -/
theorem rounded_step_decrease_at_exponent (I : Instance) (U a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hsize : 2 ≤ (I.m:ℝ)*U) (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hres : 0 < residual I F f) (hq : 0 < q) (hqUpper : q ≤ 1/2)
    (hslo : (1/2:ℝ) ≤ s) (hshi : s ≤ 2)
    (hrlo : (1/2:ℝ) ≤ r) (hrhi : r ≤ 2)
    (hg : GradientTolerance (lengths I a f) (fun e => s*g e)
      (gradient I a F f) (q/16))
    (hl : VectorApprox 2 l (lengths I a f)) (hd : IsCirculation I d)
    (hqual : dot g d / weightedLength l d ≤ -4*q) :
    let next := fun e => f e+(r*q^2/(50*|dot g d|))*d e
    I.Routes next ∧ StrictlyInside I next ∧ 0 < residual I F next ∧
      potential I a F next ≤ potential I a F f-q^2/2000 := by
  obtain ⟨p,hplo,hphi,hg',hqual',hnorm⟩ :=
    rounded_step_normalization_at_exponent I a F q s r f g l d
      hq hslo hshi hrlo hrhi hg hqual
  have hp : 0 < p := (by linarith only [hq] : 0 < q/2).trans_le hplo
  have hp' : p ≤ 1 := hphi.trans (by linarith only [hqUpper])
  obtain ⟨hroute',hinside,hres',hpot⟩ := step_decrease_at_exponent
    I U a F p (r*q^2/(50*|dot g d|)) f (fun e => s*g e) l d
      hm hU hsize ha haUpper hnums hf hroute hres hp hp' hg' hl hd hqual' hnorm
  refine ⟨hroute',hinside,hres',hpot.trans ?_⟩
  have hsq := mul_self_le_mul_self (by linarith only [hq] : 0 ≤ q/2) hplo
  nlinarith only [hsq]

end MinCostFlow.IPM.Machine
