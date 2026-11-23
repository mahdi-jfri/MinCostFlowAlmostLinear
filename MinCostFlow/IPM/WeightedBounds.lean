module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted dot product bounds

The proofs of Lemmas 4.4, 4.7, and 4.8 of Chen et al., arXiv:2203.00671v2,
use the same finite-sum form of Hölder's inequality. We prove it directly
from the coordinate gradient tolerance. We also show that the permitted
approximate lengths and gradients exist by taking their exact values.
-/

public section
namespace MinCostFlow.IPM

/-- Coordinate error bounds imply the weighted Hölder bound used in Section 4. -/
theorem abs_dot_error_le {n : ℕ} (l gApprox g x : Fin n → ℝ) (ε : ℝ)
    (hl : ∀ e, 0 < l e) (ht : GradientTolerance l gApprox g ε) :
    |dot gApprox x - dot g x| ≤ ε * weightedLength l x := by
  have heq : dot gApprox x - dot g x = ∑ e, (gApprox e - g e) * x e := by
    simp only [dot, sub_mul, Finset.sum_sub_distrib]
  rw [heq, weightedLength, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  have he : |gApprox e - g e| ≤ ε * l e := by
    have h := ht e
    rw [abs_div, abs_of_pos (hl e)] at h
    exact (div_le_iff₀ (hl e)).mp h
  calc
    |(gApprox e - g e) * x e| = |gApprox e - g e| * |x e| := abs_mul _ _
    _ ≤ (ε * l e) * |x e| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ = ε * |l e * x e| := by rw [abs_mul, abs_of_pos (hl e)]; ring

/-- Factor-two approximate lengths bound the true weighted length from above. -/
theorem weightedLength_le_two (I : Instance) (a : ℝ) (f lApprox x : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (hl : VectorApprox 2 lApprox (lengths I a f)) :
    weightedLength (lengths I a f) x ≤ 2 * weightedLength lApprox x := by
  unfold weightedLength
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have ht := (hl e).2.2.1
  have hb : lengths I a f e ≤ 2 * lApprox e := by norm_num at ht; linarith only [ht]
  simp only [abs_mul, abs_of_pos (lengths_pos I a f hf e), abs_of_pos (hl e).1]
  calc
    lengths I a f e * |x e| ≤ (2 * lApprox e) * |x e| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = 2 * (lApprox e * |x e|) := by ring

/-- The reverse comparison used in Lemma 4.7 (page 28). -/
theorem weightedLength_approx_le_two {n : ℕ} (lApprox l x : Fin n → ℝ)
    (hl : VectorApprox 2 lApprox l) :
    weightedLength lApprox x ≤ 2 * weightedLength l x := by
  unfold weightedLength
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  simp only [abs_mul, abs_of_pos (hl e).1, abs_of_pos (hl e).2.1]
  calc
    lApprox e * |x e| ≤ (2 * l e) * |x e| :=
      mul_le_mul_of_nonneg_right (hl e).2.2.2 (abs_nonneg _)
    _ = 2 * (l e * |x e|) := by ring

/-- The approximation conditions of Lemma 4.4 (page 25) can hold together: exact
lengths and gradients satisfy them for every nonnegative tolerance. -/
theorem exact_approximations (I : Instance) (a F ε : ℝ) (f : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (hε : 0 ≤ ε) :
    GradientTolerance (lengths I a f) (gradient I a F f) (gradient I a F f) ε ∧
      VectorApprox 2 (lengths I a f) (lengths I a f) := by
  constructor
  · intro e
    simpa only [sub_self, zero_div, abs_zero] using hε
  · intro e
    have hp := lengths_pos I a f hf e
    refine ⟨hp, hp, ?_, ?_⟩ <;> norm_num <;> linarith only [hp]

end MinCostFlow.IPM
