module

public import MinCostFlow.IPM.Definitions
import MinCostFlow.IPM.StepDecrease
import MinCostFlow.IPM.OptimalDirection
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The mathematical update in Theorem 4.3 (page 25)

Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, permits any approximate
lengths, gradient, and circulation with its stated tolerances and ratio.
An update contains only those choices and side conditions. Lemma 4.4 (page 25)
proves its decrease and domain preservation. Lemma 4.7 (page 28) proves such choices
exist, using the direction to an optimum, before the stopping threshold.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The choices and side conditions of one update in Theorem 4.3 (page 25).
No decrease or stability result is part of this data. The default exponent
is the paper's `alpha`; the fixed-point program supplies its stored exponent
explicitly, with its admissibility bounds proved separately. -/
structure Update (I : Instance) (U F κ : ℝ) (f : Fin I.m → ℝ)
    (a : ℝ := alpha I U) where
  /-- The approximate gradient. -/
  gApprox : Fin I.m → ℝ
  /-- The approximate positive lengths. -/
  lApprox : Fin I.m → ℝ
  /-- The chosen circulation. -/
  direction : Fin I.m → ℝ
  /-- The step size. -/
  stepSize : ℝ
  /-- The allowed gradient error. -/
  gradient_error : GradientTolerance (lengths I a f) gApprox
    (gradient I a F f) (κ/8)
  /-- The allowed length approximation. -/
  length_error : VectorApprox 2 lApprox (lengths I a f)
  /-- The routing constraint on the direction. -/
  circulation : IsCirculation I direction
  /-- The negative ratio guarantee. -/
  quality : dot gApprox direction / weightedLength lApprox direction ≤ -κ
  /-- The step normalization. -/
  normalization : stepSize*dot gApprox direction = -κ^2/50

/-- The update `f + ηΔ` in Theorem 4.3 (page 25). -/
@[expose] def Update.next {I : Instance} {U F κ a : ℝ} {f : Fin I.m → ℝ}
    (s : Update I U F κ f a) : Fin I.m → ℝ := fun e => f e+s.stepSize*s.direction e

/-- Lemma 4.4 (page 25) applied to an arbitrary permitted update. -/
theorem Update.spec {I : Instance} {U F κ : ℝ} {f : Fin I.m → ℝ}
    (s : Update I U F κ f) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hr : 0 < residual I F f) (hκ : 0 < κ) (hκ' : κ ≤ 1) :
    I.Routes s.next ∧ StrictlyInside I s.next ∧ 0 < residual I F s.next ∧
      potential I (alpha I U) F s.next ≤ potential I (alpha I U) F f-κ^2/500 :=
  lemma_4_4 I U F κ s.stepSize f s.gApprox s.lApprox s.direction hm hU hsize
    hnums hf hroute hr hκ hκ' s.gradient_error s.length_error s.circulation s.quality s.normalization

private theorem weightedLength_pos_of_dot_neg {n : ℕ} (l g x : Fin n → ℝ)
    (hl : ∀ e, 0 < l e) (hg : dot g x < 0) : 0 < weightedLength l x := by
  have hn : 0 ≤ weightedLength l x := Finset.sum_nonneg fun e _ => abs_nonneg _
  by_contra h
  have hz := le_antisymm (not_lt.mp h) hn
  have hx : ∀ e, x e = 0 := by
    intro e
    have hs : |l e*x e| ≤ weightedLength l x :=
      Finset.single_le_sum (fun j _ => abs_nonneg (l j*x j)) (Finset.mem_univ e)
    rw [hz] at hs
    have hp := abs_eq_zero.mp (le_antisymm hs (abs_nonneg _))
    exact (mul_eq_zero.mp hp).resolve_left (hl e).ne'
  have hd : dot g x = 0 := by simp only [dot, hx, mul_zero, Finset.sum_const_zero]
  rw [hd] at hg
  exact (lt_irrefl 0) hg

/-- The hidden direction in Theorem 4.3 (page 25), for arbitrary permitted
approximations. The restriction `κ ≤ α/4` implies the error condition
needed by Lemma 4.7 (page 28), and also makes that direction a permitted update. -/
theorem exists_update_with_approximations (I : Instance) (U F κ : ℝ)
    (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hroute : I.Routes f) (hs : I.IsMinCostFlow fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hg : GradientTolerance (lengths I (alpha I U) f) gApprox
      (gradient I (alpha I U) F f) (κ/8))
    (hl : VectorApprox 2 lApprox (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hres : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    ∃ s : Update I U F κ f, s.gApprox = gApprox ∧ s.lApprox = lApprox ∧
      s.direction = (fun e => fstar e-f e) := by
  have ha := (alpha_pos I U hsize).le
  have hquality := lemma_4_7 I U F (κ/8) f fstar gApprox lApprox hm hsize hf hs hr hF
    (by linarith only [hκa, ha]) hg hl hpot hres
  let Δ : Fin I.m → ℝ := fun e => fstar e-f e
  have hd0 : 0 < 100*(I.m : ℝ)+weightedLength lApprox Δ := by
    have hn : 0 ≤ weightedLength lApprox Δ := Finset.sum_nonneg fun e _ => abs_nonneg _
    have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
    linarith only [hn, hm']
  have hq := (div_le_iff₀ hd0).mp hquality
  have hdot : dot gApprox Δ < 0 := by
    have hneg : -alpha I U/4*(100*I.m+weightedLength lApprox Δ) < 0 :=
      mul_neg_of_neg_of_pos (by linarith only [alpha_pos I U hsize]) hd0
    exact lt_of_le_of_lt hq hneg
  have hlen := weightedLength_pos_of_dot_neg lApprox gApprox Δ (fun e => (hl e).1) hdot
  have hcir : IsCirculation I Δ := by
    intro v
    dsimp only [Δ]
    simp only [mul_sub, Finset.sum_sub_distrib, hs.1.1 v, hroute v, sub_self]
  have hq' : dot gApprox Δ / weightedLength lApprox Δ ≤ -κ := by
    apply (div_le_iff₀ hlen).mpr
    have hm' : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
    have hpaid := mul_nonneg ha hm'
    have hκlen := mul_le_mul_of_nonneg_right hκa hlen.le
    nlinarith only [hq, hpaid, hκlen]
  have hnorm : (κ^2/(50*|dot gApprox Δ|))*dot gApprox Δ = -κ^2/50 := by
    rw [abs_of_neg hdot]
    field_simp [hdot.ne]
  exact ⟨⟨gApprox, lApprox, Δ, κ^2/(50*|dot gApprox Δ|), hg, hl, hcir, hq', hnorm⟩,
    rfl, rfl, rfl⟩

/-- A permitted step for an upper target guess, by the direction estimate
of Lemma 4.7 (page 28). Only feasibility and a cost at most the target
are required of the comparison flow. The restriction `κ ≤ α/4` implies the error condition
needed by Lemma 4.7 (page 28), and also makes that direction a permitted update. -/
theorem exists_update_with_approximations_of_cost_le (I : Instance) (U F κ : ℝ)
    (f fstar gApprox lApprox : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hroute : I.Routes f) (hs : I.IsFeasible fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hg : GradientTolerance (lengths I (alpha I U) f) gApprox
      (gradient I (alpha I U) F f) (κ/8))
    (hl : VectorApprox 2 lApprox (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hres : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    ∃ s : Update I U F κ f, s.gApprox = gApprox ∧ s.lApprox = lApprox ∧
      s.direction = (fun e => fstar e-f e) := by
  have ha := (alpha_pos I U hsize).le
  have hquality := direction_of_cost_le I U F (κ/8) f fstar gApprox lApprox hm hsize hf hs hr hF
    (by linarith only [hκa, ha]) hg hl hpot hres
  let Δ : Fin I.m → ℝ := fun e => fstar e-f e
  have hd0 : 0 < 100*(I.m : ℝ)+weightedLength lApprox Δ := by
    have hn : 0 ≤ weightedLength lApprox Δ := Finset.sum_nonneg fun e _ => abs_nonneg _
    have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
    linarith only [hn, hm']
  have hq := (div_le_iff₀ hd0).mp hquality
  have hdot : dot gApprox Δ < 0 := by
    have hneg : -alpha I U/4*(100*I.m+weightedLength lApprox Δ) < 0 :=
      mul_neg_of_neg_of_pos (by linarith only [alpha_pos I U hsize]) hd0
    exact lt_of_le_of_lt hq hneg
  have hlen := weightedLength_pos_of_dot_neg lApprox gApprox Δ (fun e => (hl e).1) hdot
  have hcir : IsCirculation I Δ := by
    intro v
    dsimp only [Δ]
    simp only [mul_sub, Finset.sum_sub_distrib, hs.1 v, hroute v, sub_self]
  have hq' : dot gApprox Δ / weightedLength lApprox Δ ≤ -κ := by
    apply (div_le_iff₀ hlen).mpr
    have hm' : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
    have hpaid := mul_nonneg ha hm'
    have hκlen := mul_le_mul_of_nonneg_right hκa hlen.le
    nlinarith only [hq, hpaid, hκlen]
  have hnorm : (κ^2/(50*|dot gApprox Δ|))*dot gApprox Δ = -κ^2/50 := by
    rw [abs_of_neg hdot]
    field_simp [hdot.ne]
  exact ⟨⟨gApprox, lApprox, Δ, κ^2/(50*|dot gApprox Δ|), hg, hl, hcir, hq', hnorm⟩,
    rfl, rfl, rfl⟩

end MinCostFlow.IPM
