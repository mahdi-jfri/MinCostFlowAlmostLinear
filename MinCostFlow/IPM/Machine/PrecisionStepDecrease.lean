module

public import MinCostFlow.IPM.Machine.PrecisionStepSlacks
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.StepBounds
import MinCostFlow.IPM.StepTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Potential decrease at the stored barrier exponent

The proof is the normalized-step argument of Chen et al.,
arXiv:2203.00671v2, Lemma 4.4 (page 25). Its Taylor estimates already
allow a general exponent. The relative-slack bound proved here for
`a≤alpha` supplies the remaining link for the representable exponent.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem relative_cost_small (m κ t : ℝ) (hm : 1 ≤ m)
    (hκ : 0 ≤ κ) (hκ' : κ ≤ 1) (ht : 0 ≤ t) (hc : 20*m*t ≤ κ/25) :
    t ≤ 1/10 ∧ 20*m*t^2 ≤ κ^2/10000 := by
  have hmt : 20*t ≤ 20*m*t := by nlinarith only [hm, ht]
  have htκ : t ≤ κ/500 := by linarith only [hc, hmt]
  have hquad := mul_le_mul hc htκ ht (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 25))
  constructor
  · linarith only [htκ, hκ']
  · nlinarith only [hquad, sq_nonneg κ]

/-- Lemma 4.4 (page 25) of Chen et al., arXiv:2203.00671v2,
with any nonnegative exponent at most the analytic one. Both the
approximations and the potential use the supplied exponent. -/
theorem normalized_step_decrease_at_exponent (I : Instance) (U a F κ : ℝ)
    (f gApprox lApprox s : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hr : 0 < residual I F f) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hg : GradientTolerance (lengths I a f) gApprox
      (gradient I a F f) (κ/8))
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hquality : κ * weightedLength lApprox s ≤ -dot gApprox s)
    (hscale : dot gApprox s = -κ^2/50) :
    StrictlyInside I (fun e => f e+s e) ∧
      0 < residual I F (fun e => f e+s e) ∧
      potential I a F (fun e => f e+s e) ≤
        potential I a F f - κ^2/500 := by
  have ha := haNonneg
  have ha' := haUpper.trans (alpha_le I U hsize)
  obtain ⟨hnorm, hgrad, hcost⟩ := normalized_step_bounds I a F κ
    f gApprox lApprox s hm hf hr ha ha' hκ hκ' hg hl hquality hscale
  have hs := step_slacks_at_exponent I U a κ f s hm hU hsize haNonneg haUpper hnums hf hκ.le hnorm
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have ht0 : 0 ≤ |I.cost s| / residual I F f := div_nonneg (abs_nonneg _) hr.le
  obtain ⟨htsmall, hquad⟩ := relative_cost_small (I.m : ℝ) κ
    (|I.cost s| / residual I F f) hm' hκ.le hκ' ht0 hcost
  have hc : |I.cost s| ≤ residual I F f/10 := by
    have h := (div_le_iff₀ hr).mp htsmall
    linarith only [h]
  have hinside : StrictlyInside I (fun e => f e+s e) := by
    intro e
    have hp : 0 < ((I.edge e).upper : ℝ)-f e := sub_pos.mpr (hf e).2
    have hq : 0 < f e-((I.edge e).lower : ℝ) := sub_pos.mpr (hf e).1
    have hu := mul_le_mul_of_nonneg_right hκ' hp.le
    have hl := mul_le_mul_of_nonneg_right hκ' hq.le
    have hsu := (hs e).1
    have hsl := (hs e).2
    have habs := abs_le.mp (le_refl |s e|)
    constructor <;> dsimp only <;> linarith only [hp, hq, hu, hl, hsu, hsl, habs.1, habs.2]
  have hradd : residual I F (fun e => f e+s e) = residual I F f + I.cost s := by
    rw [residual, cost_add, residual]
    ring
  have hrnew : 0 < residual I F (fun e => f e+s e) := by
    rw [hradd]
    have hh := (abs_le.mp hc).1
    linarith only [hr, hh]
  have ht := potential_step_taylor_le I a F κ f s hf ha ha' hκ' hr hc hs
  have hqeq : (|I.cost s| / residual I F f)^2 = (I.cost s / residual I F f)^2 := by
    rw [div_pow, div_pow, sq_abs]
  rw [hqeq] at hquad
  have hbar := mul_le_mul_of_nonneg_left hnorm
    (div_nonneg (mul_nonneg ha hκ.le) (by norm_num : (0 : ℝ) ≤ 10))
  have hακ := mul_le_mul_of_nonneg_right ha' (sq_nonneg κ)
  refine ⟨hinside, hrnew, ?_⟩
  nlinarith only [ht, hgrad, hquad, hbar, hακ, sq_nonneg κ]

/-- Lemma 4.4 (page 25), at an exponent at most `alpha`, for an
explicit direction and multiplier. Routing is preserved by circulation. -/
theorem step_decrease_at_exponent (I : Instance) (U a F κ η : ℝ)
    (f gApprox lApprox Δ : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hr : 0 < residual I F f) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hg : GradientTolerance (lengths I a f) gApprox
      (gradient I a F f) (κ/8))
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hcir : IsCirculation I Δ)
    (hquality : dot gApprox Δ / weightedLength lApprox Δ ≤ -κ)
    (hscale : η * dot gApprox Δ = -κ^2/50) :
    I.Routes (fun e => f e+η*Δ e) ∧
      StrictlyInside I (fun e => f e+η*Δ e) ∧
      0 < residual I F (fun e => f e+η*Δ e) ∧
      potential I a F (fun e => f e+η*Δ e) ≤
        potential I a F f - κ^2/500 := by
  have hlen0 : 0 ≤ weightedLength lApprox Δ :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength lApprox Δ := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) hlen0
    rw [hz, div_zero] at hquality
    linarith only [hquality, hκ]
  have hratio := (div_le_iff₀ hlen).mp hquality
  have hdot : dot gApprox Δ < 0 := by
    have hm := mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) hlen
    exact lt_of_le_of_lt hratio hm
  have hη : 0 < η := by
    have hk2 : 0 < κ^2 := sq_pos_of_pos hκ
    nlinarith only [hscale, hdot, hk2]
  have hdscale : dot gApprox (fun e => η*Δ e) = η*dot gApprox Δ := by
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hlscale : weightedLength lApprox (fun e => η*Δ e) = η*weightedLength lApprox Δ := by
    unfold weightedLength
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [show lApprox e*(η*Δ e) = η*(lApprox e*Δ e) by ring,
      abs_mul, abs_of_pos hη]
  have hq : κ*weightedLength lApprox (fun e => η*Δ e) ≤
      -dot gApprox (fun e => η*Δ e) := by
    rw [hlscale, hdscale]
    have h := mul_le_mul_of_nonneg_left hratio hη.le
    nlinarith only [h]
  have hs : dot gApprox (fun e => η*Δ e) = -κ^2/50 := by
    rw [hdscale, hscale]
  obtain ⟨hinside, hres, hpot⟩ := normalized_step_decrease_at_exponent I U a F κ
    f gApprox lApprox (fun e => η*Δ e) hm hU hsize haNonneg haUpper hnums hf hr hκ hκ' hg hl hq hs
  refine ⟨?_, hinside, hres, hpot⟩
  intro v
  have hz : (∑ e, (I.edge e).b v*(η*Δ e)) = 0 := by
    calc
      _ = η*(∑ e, (I.edge e).b v*Δ e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = 0 := by rw [hcir v, mul_zero]
  simp only [mul_add, Finset.sum_add_distrib, hz, add_zero]
  exact hroute v

end MinCostFlow.IPM.Machine
