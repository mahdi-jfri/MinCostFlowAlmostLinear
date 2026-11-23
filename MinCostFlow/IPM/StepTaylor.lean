module

public import MinCostFlow.IPM.Definitions
import MinCostFlow.IPM.PowerTaylor
import MinCostFlow.IPM.LogTaylor
import MinCostFlow.IPM.StepSlacks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Summing the Taylor bounds for one IPM step

In Lemma 4.4 (page 25) of Chen et al., arXiv:2203.00671v2, the linear terms from
the logarithm and the barriers add to the gradient dot product. The
quadratic terms are bounded by the squared relative cost change and the
weighted step length. This file carries out that summation.
-/

public section
namespace MinCostFlow.IPM

/-- Cost is additive on real flows. -/
theorem cost_add (I : Instance) (f s : Fin I.m → ℝ) :
    I.cost (fun e => f e+s e) = I.cost f+I.cost s := by
  simp only [Instance.cost, mul_add, Finset.sum_add_distrib]

/-- The cost and barrier parts of the gradient dot product. -/
theorem gradient_dot_eq (I : Instance) (a F : ℝ) (f s : Fin I.m → ℝ) :
    dot (gradient I a F f) s = 20*I.m*(I.cost s / residual I F f) +
      ∑ e, a*(Real.rpow ((I.edge e).upper-f e) (-1-a) -
        Real.rpow (f e-(I.edge e).lower) (-1-a))*s e := by
  simp only [dot, gradient, Instance.cost, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The sum of the barrier Taylor estimates in Lemma 4.4 (page 25). -/
theorem barrier_step_taylor_le (I : Instance) (a κ : ℝ) (f s : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hκ : κ ≤ 1)
    (hs : ∀ e, |s e| ≤ (κ/10)*((I.edge e).upper-f e) ∧
      |s e| ≤ (κ/10)*(f e-(I.edge e).lower)) :
    (∑ e, edgeBarrier I a e (f e+s e)) ≤ (∑ e, edgeBarrier I a e (f e)) +
      (∑ e, a*(Real.rpow ((I.edge e).upper-f e) (-1-a) -
        Real.rpow (f e-(I.edge e).lower) (-1-a))*s e) +
      (a*κ/10)*weightedLength (lengths I a f) s := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e (_ : e ∈ Finset.univ) => by
    have hp : 0 < ((I.edge e).upper : ℝ)-f e := sub_pos.mpr (hf e).2
    have hq : 0 < f e-((I.edge e).lower : ℝ) := sub_pos.mpr (hf e).1
    have hd : |s e| ≤ (1/10)*min ((I.edge e).upper-f e) (f e-(I.edge e).lower) := by
      have hu : |s e| ≤ (1/10)*((I.edge e).upper-f e) := by
        have hm := mul_le_mul_of_nonneg_right hκ hp.le
        linarith only [(hs e).1, hm]
      have hl : |s e| ≤ (1/10)*(f e-(I.edge e).lower) := by
        have hm := mul_le_mul_of_nonneg_right hκ hq.le
        linarith only [(hs e).2, hm]
      rcases le_total (((I.edge e).upper : ℝ)-f e) (f e-(I.edge e).lower) with he | he
      · simpa only [min_eq_left he] using hu
      · simpa only [min_eq_right he] using hl
    have ht := lemma_4_5 I a f e hf ha ha' (s e) hd
    have hu := quadratic_slack_le _ a (s e) (κ/10) hp (hs e).1
    have hl := quadratic_slack_le _ a (s e) (κ/10) hq (hs e).2
    have hquad := mul_le_mul_of_nonneg_left (add_le_add hu hl) ha
    have hlen : |lengths I a f e*s e| =
        (Real.rpow ((I.edge e).upper-f e) (-1-a) +
          Real.rpow (f e-(I.edge e).lower) (-1-a))*|s e| := by
      rw [abs_mul, abs_of_pos (lengths_pos I a f hf e)]
      rfl
    have hfinal : edgeBarrier I a e (f e+s e) ≤ edgeBarrier I a e (f e) +
        a*(Real.rpow ((I.edge e).upper-f e) (-1-a) -
          Real.rpow (f e-(I.edge e).lower) (-1-a))*s e +
        (a*κ/10)*|lengths I a f e*s e| := by
      rw [hlen]
      nlinarith only [ht, hquad]
    exact hfinal)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, weightedLength] using hsum

/-- The combined Taylor estimate in the proof of Lemma 4.4 (page 25). -/
theorem potential_step_taylor_le (I : Instance) (a F κ : ℝ) (f s : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hκ : κ ≤ 1)
    (hr : 0 < residual I F f) (hc : |I.cost s| ≤ residual I F f/10)
    (hs : ∀ e, |s e| ≤ (κ/10)*((I.edge e).upper-f e) ∧
      |s e| ≤ (κ/10)*(f e-(I.edge e).lower)) :
    potential I a F (fun e => f e+s e) ≤ potential I a F f + dot (gradient I a F f) s +
      20*I.m*(I.cost s / residual I F f)^2 +
      (a*κ/10)*weightedLength (lengths I a f) s := by
  have hb := barrier_step_taylor_le I a κ f s hf ha ha' hκ hs
  have hlog := lemma_4_6 (residual I F f) (I.cost s) hr hc
  have hm : (0 : ℝ) ≤ 20*I.m := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlog hm
  have hradd : residual I F (fun e => f e+s e) = residual I F f + I.cost s := by
    rw [residual, cost_add, residual]
    ring
  unfold potential
  rw [hradd]
  rw [gradient_dot_eq, div_pow]
  linarith only [hb, hmul]

end MinCostFlow.IPM
