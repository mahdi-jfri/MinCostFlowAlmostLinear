module

public import MinCostFlow.IPM.GradientStability
public import MinCostFlow.IPM.LengthStability
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stability of the stored gradient and lengths

Lemma 9.1 of Chen et al., arXiv:2203.00671v2 (Section 9, page 70),
is adapted to the single-flow Detect interface of Definition 4.5
(page 14 of arXiv:2309.16629v1). The stored flow coordinates are close
in the old weighted norm. A separately stored residual approximates the
current residual. Lemmas 4.9 and 4.10 then bound the stored lengths and
the rescaled stored gradient. The hypotheses describe these numerical
inputs, not conclusions about a data structure.
-/

public section
namespace MinCostFlow.IPM

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
theorem lemma_9_1 (I : Instance) (U F ε r : ℝ)
    (stored current : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hstored : StrictlyInside I stored)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (alpha I U) stored e*(current e-stored e)| ≤ ε)
    (hr : ScalarApprox (1+ε) r (residual I F current)) :
    VectorApprox (1+3*ε) (lengths I (alpha I U) stored) (lengths I (alpha I U) current) ∧
    GradientTolerance (lengths I (alpha I U) current)
      (fun e => (r/residual I F current)*gradientWithResidual I (alpha I U) r stored e)
      (gradient I (alpha I U) F current) (8*alpha I U*ε) := by
  have hl := lemma_4_9 I U ε stored current hm hU hsize hnums hstored he he' hclose
  have hg := lemma_4_10 I U F ε r stored current hm hU hsize hnums hstored he he' hclose hr
  exact ⟨hl, rescale_tolerance (alpha I U) ε r (residual I F current) _ _ _ _
    (alpha_pos I U hsize).le he he' hr hl hg⟩

end MinCostFlow.IPM
