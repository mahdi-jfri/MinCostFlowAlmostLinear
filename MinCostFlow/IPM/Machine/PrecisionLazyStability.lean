module

public import MinCostFlow.IPM.Machine.PrecisionGradientStability
import MinCostFlow.IPM.Machine.PrecisionEta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Epoch tolerances at the stored exponent

This is Chen et al., arXiv:2203.00671v2, Lemma 9.1 (page 70), with
the exponent explicit. The same residual rescaling combines the length
and gradient stability bounds proved at that exponent. Numerical
coefficient error can then be added separately to this stale-flow error.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem rescale_tolerance {n : ℕ} (a ε r R : ℝ)
    (lold lnew g gnew : Fin n → ℝ)
    (ha : 0 ≤ a) (he : 0 ≤ ε) (he' : ε ≤ 1/100)
    (hr : ScalarApprox (1+ε) r R)
    (hl : VectorApprox (1+3*ε) lold lnew)
    (hg : GradientTolerance lold g (fun e => (R/r)*gnew e) (6*a*ε)) :
    GradientTolerance lnew (fun e => (r/R)*g e) gnew (8*a*ε) := by
  have hrR : 0 < r/R := div_pos hr.1 hr.2.1
  have hrRle : r/R ≤ 1+ε := (div_le_iff₀ hr.2.1).mpr hr.2.2.2
  have hfac : (1+ε)*(1+3*ε) ≤ (4/3 : ℝ) := by
    have he2 : ε^2 ≤ ε/100 := by nlinarith only [he, he']
    nlinarith only [he, he', he2]
  have hnonneg : 0 ≤ 6*a*ε := mul_nonneg (mul_nonneg (by norm_num) ha) he
  have hfactor := mul_le_mul_of_nonneg_right hfac hnonneg
  intro e
  have hold : 0 < lold e := (hl e).1
  have hnew : 0 < lnew e := (hl e).2.1
  have herr := hg e
  rw [abs_div, abs_of_pos hold] at herr
  have herr' := (div_le_iff₀ hold).mp herr
  have hid : (r/R)*g e-gnew e = (r/R)*(g e-(R/r)*gnew e) := by
    field_simp [hr.1.ne', hr.2.1.ne']
  rw [abs_div, abs_of_pos hnew]
  apply (div_le_iff₀ hnew).mpr
  rw [hid, abs_mul, abs_of_pos hrR]
  calc
    (r/R)*|g e-(R/r)*gnew e| ≤ (r/R)*(6*a*ε*lold e) :=
      mul_le_mul_of_nonneg_left herr' hrR.le
    _ ≤ (1+ε)*(6*a*ε*lold e) :=
      mul_le_mul_of_nonneg_right hrRle (mul_nonneg hnonneg hold.le)
    _ ≤ (1+ε)*(6*a*ε*((1+3*ε)*lnew e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hl e).2.2.2 hnonneg) (by linarith only [he])
    _ ≤ 8*a*ε*lnew e := by
      have hh := mul_le_mul_of_nonneg_right hfactor hnew.le
      nlinarith only [hh]

/-- Chen et al., arXiv:2203.00671v2, Lemma 9.1 (page 70), adapted
to Definition 4.5's single maintained flow. The stale-coordinate
bound is supplied by Detect, and the residual approximation by the
periodic full refresh. The resulting gradient is rescaled by `r/R`.
The explicit error bound is `8αε`. -/
theorem lemma_9_1_at_exponent (I : Instance) (U a F ε r : ℝ)
    (stored current : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hstored : StrictlyInside I stored)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) stored e*(current e-stored e)| ≤ ε)
    (hr : ScalarApprox (1+ε) r (residual I F current)) :
    VectorApprox (1+3*ε) (lengths I (a) stored) (lengths I (a) current) ∧
    GradientTolerance (lengths I (a) current)
      (fun e => (r/residual I F current)*gradientWithResidual I (a) r stored e)
      (gradient I (a) F current) (8*a*ε) := by
  have hl := lemma_4_9_at_exponent I U a ε stored current hm hU hsize haNonneg haUpper hnums hstored he he' hclose
  have hg := lemma_4_10_at_exponent I U a F ε r stored current hm hU hsize haNonneg haUpper hnums hstored he he' hclose hr
  exact ⟨hl, rescale_tolerance (a) ε r (residual I F current) _ _ _ _
    haNonneg he he' hr hl hg⟩

/-- Rounding a stored gradient adds at most four times its numerical
error budget after the epoch's residual and length rescalings. -/
theorem rescale_computed_gradient {n : ℕ} (eps delta s staleError : ℝ)
    (oldLength newLength exactStored computed current : Fin n → ℝ)
    (_heps : 0 ≤ eps) (hepsUpper : eps ≤ 1/100) (hdelta : 0 ≤ delta)
    (hs : 0 < s ∧ s ≤ 4/3)
    (hl : VectorApprox (1+3*eps) oldLength newLength)
    (htrue : GradientTolerance newLength (fun e => s*exactStored e) current staleError)
    (hnum : GradientTolerance oldLength computed exactStored delta) :
    GradientTolerance newLength (fun e => s*computed e) current (staleError+4*delta) := by
  have hb : 1+3*eps ≤ 4/3 := by linarith only [hepsUpper]
  intro e
  have hOld := (hl e).1
  have hNew := (hl e).2.1
  have herr := hnum e
  rw [abs_div,abs_of_pos hOld] at herr
  have herr' := (div_le_iff₀ hOld).mp herr
  have hold : oldLength e ≤ (4/3:ℝ)*newLength e :=
    (hl e).2.2.2.trans (mul_le_mul_of_nonneg_right hb hNew.le)
  have hfirst := mul_le_mul_of_nonneg_left herr' hs.1.le
  have hsecond := mul_le_mul_of_nonneg_left hold (mul_nonneg hs.1.le hdelta)
  have hthird := mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hdelta hNew.le)
  have hscaled : |s*(computed e-exactStored e)| ≤ 4*delta*newLength e := by
    rw [abs_mul,abs_of_pos hs.1]
    nlinarith only [hfirst,hsecond,hthird,mul_nonneg hdelta hNew.le]
  have hstale := htrue e
  rw [abs_div,abs_of_pos hNew] at hstale
  have hstale' := (div_le_iff₀ hNew).mp hstale
  rw [abs_div,abs_of_pos hNew]
  apply (div_le_iff₀ hNew).mpr
  have ht := abs_add_le (s*(computed e-exactStored e)) (s*exactStored e-current e)
  have hid : s*computed e-current e=s*(computed e-exactStored e)+(s*exactStored e-current e) := by ring
  rw [hid]
  nlinarith only [ht,hscaled,hstale']

/-- The adapted Lemma 9.1 (page 70) including numerical error in the
stored gradient. All lengths and gradients use the same exponent `a`. -/
theorem lemma_9_1_computed_gradient (I : Instance) (U a F eps r delta : ℝ)
    (stored current computed : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m:ℝ)*U)
    (ha : 0 ≤ a) (haUpper : a ≤ alpha I U) (hnums : NumbersBounded I U)
    (hstored : StrictlyInside I stored) (heps : 0 ≤ eps) (hepsUpper : eps ≤ 1/100)
    (hdelta : 0 ≤ delta)
    (hclose : ∀ e,|lengths I a stored e*(current e-stored e)| ≤ eps)
    (hr : ScalarApprox (1+eps) r (residual I F current))
    (hcomputed : GradientTolerance (lengths I a stored) computed
      (gradientWithResidual I a r stored) delta) :
    GradientTolerance (lengths I a current)
      (fun e => (r/residual I F current)*computed e)
      (gradient I a F current) (8*a*eps+4*delta) := by
  have hstability := lemma_9_1_at_exponent I U a F eps r stored current
    hm hU hsize ha haUpper hnums hstored heps hepsUpper hclose hr
  have hratio := residual_ratio_three_fourths heps
    (by linarith only [hepsUpper] : eps ≤ 1/3) hr
  exact rescale_computed_gradient eps delta (r/residual I F current) (8*a*eps)
    (lengths I a stored) (lengths I a current) (gradientWithResidual I a r stored)
    computed (gradient I a F current) heps hepsUpper hdelta
    ⟨div_pos hr.1 hr.2.1,hratio.2⟩ hstability.1 hstability.2 hcomputed

end MinCostFlow.IPM.Machine
