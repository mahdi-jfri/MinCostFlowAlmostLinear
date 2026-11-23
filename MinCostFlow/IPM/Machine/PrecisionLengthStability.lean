module

public import MinCostFlow.IPM.Machine.PrecisionStepSlacks
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.StepBounds
import all MinCostFlow.IPM.StepSlacks
import MinCostFlow.IPM.PowerStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Length stability at the stored exponent

The proof of Chen et al., arXiv:2203.00671v2, Lemma 4.9 (page 29),
uses the exponent only through its upper bounds. We repeat that argument
with an explicit `a≤alpha` so that the stored dyadic exponent can be used
throughout a numerical epoch. Both lengths in the comparison use `a`.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem slack_rpow_at_exponent_le_five_fourths (I : Instance) (U a x : ℝ)
    (hsize : 2 ≤ (I.m:ℝ)*U) (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hx : 0 < x) (hbound : x ≤ 2*(I.m*U)) : Real.rpow x a ≤ 5/4 := by
  by_cases hx1 : 1 ≤ x
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 haUpper).trans
      (slack_rpow_alpha_le_five_fourths I U x hsize hx hbound)
  · have hh := Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1) ha
    simp only [Real.rpow_zero] at hh
    exact hh.trans (by norm_num)

private theorem relative_slack_of_power_bound (p a d ε : ℝ) (hp : 0 < p)
    (hε : 0 ≤ ε) (hpower : Real.rpow p a ≤ 5/4)
    (hstep : Real.rpow p (-1-a)*|d| ≤ ε) : |d| ≤ (5/4)*ε*p := by
  have hmul := mul_le_mul_of_nonneg_right hstep
    (mul_nonneg hp.le (Real.rpow_pos_of_pos hp a).le)
  have hcancel := inverse_slack_cancel p a hp
  simp only [Real.rpow_eq_pow] at hcancel hmul hpower
  have hid : p^(-1-a)*|d| *(p*p^a) = |d| := by
    calc
      _ = |d| *(p^(-1-a)*(p*p^a)) := by ring
      _ = |d| := by rw [hcancel, mul_one]
  rw [hid] at hmul
  have hcoef := mul_le_mul_of_nonneg_left hpower (mul_nonneg hε hp.le)
  nlinarith only [hmul, hcoef]

/-- Small change in the old weighted maximum norm gives a relative
one-tenth slack change. The sharper bound is used in Lemmas 4.9 and 4.10. -/
theorem stability_slacks_at_exponent (I : Instance) (U a ε : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hε : 0 ≤ ε)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε) (e : Fin I.m) :
    |fbar e-f e| ≤ (5/4)*ε*((I.edge e).upper-f e) ∧
      |fbar e-f e| ≤ (5/4)*ε*(f e-(I.edge e).lower) := by
  have he := hclose e
  rw [abs_mul, abs_of_pos (lengths_pos I (a) f hf e)] at he
  dsimp only [lengths] at he
  have hp := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) (-1-a)).le
  have hq := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) (-1-a)).le
  have hlower := (abs_le.mp (hnums.2 e).1).1
  have hupper := (abs_le.mp (hnums.2 e).2.1).2
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hsizeU : U ≤ I.m*U := by nlinarith only [hm', hU]
  have hpu : ((I.edge e).upper : ℝ)-f e ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).1, hsizeU]
  have hpl : f e-((I.edge e).lower : ℝ) ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).2, hsizeU]
  constructor
  · apply relative_slack_of_power_bound _ (a) _ ε (sub_pos.mpr (hf e).2) hε
      (slack_rpow_at_exponent_le_five_fourths I U a _ hsize haNonneg haUpper (sub_pos.mpr (hf e).2) hpu)
    simp only [Real.rpow_eq_pow] at he ⊢
    nlinarith only [he, mul_nonneg hq (abs_nonneg (fbar e-f e))]
  · apply relative_slack_of_power_bound _ (a) _ ε (sub_pos.mpr (hf e).1) hε
      (slack_rpow_at_exponent_le_five_fourths I U a _ hsize haNonneg haUpper (sub_pos.mpr (hf e).1) hpl)
    simp only [Real.rpow_eq_pow] at he ⊢
    nlinarith only [he, mul_nonneg hp (abs_nonneg (fbar e-f e))]

/-- An absolute relative error at most `5ε/2` implies the symmetric
multiplicative factor `1+3ε` used in Lemma 4.9 (page 29). -/
private theorem scalar_approx_of_small_error (x y ε : ℝ) (hx : 0 < x)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100) (herror : |y-x| ≤ (5/2)*ε*x) :
    ScalarApprox (1+3*ε) x y := by
  have he := abs_le.mp herror
  have hfac : 0 < 1+3*ε := by linarith only [hε]
  have hy : 0 < y := by nlinarith only [he.1, hx, hε', mul_pos hx (by norm_num : (0 : ℝ) < 1/40)]
  refine ⟨hx, hy, ?_, ?_⟩
  · rw [inv_mul_le_iff₀ hfac]
    nlinarith only [he.2, mul_nonneg hε hx.le]
  · have hmul := mul_le_mul_of_nonneg_left he.1 (by linarith only [hε] : 0 ≤ 1+3*ε)
    have hεsq : ε^2 ≤ ε/100 := by nlinarith only [hε, hε']
    have hsmall := mul_le_mul_of_nonneg_right hεsq hx.le
    nlinarith only [hmul, hsmall, mul_nonneg hε hx.le]

/-- The relative slack estimates imply the one-tenth domain condition
used in the power Taylor bounds. -/
theorem relative_slack_tenth (p d ε : ℝ) (hp : 0 < p) (hε : ε ≤ 1/100)
    (hd : |d| ≤ (5/4)*ε*p) : |d| ≤ p/10 := by
  have h := mul_le_mul_of_nonneg_right hε hp.le
  nlinarith only [hd, h, hp]

private theorem power_change_of_relative_slack (x a d ε : ℝ)
    (hx : 0 < x) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (hε : ε ≤ 1/100) (hd : |d| ≤ (5/4)*ε*x) :
    |Real.rpow (x+d) (-1-a) - Real.rpow x (-1-a)| ≤
      (5/2)*ε*Real.rpow x (-1-a) := by
  have ht := power_change_le x a d hx ha ha' (relative_slack_tenth x d ε hx hε hd)
  have hm := mul_le_mul_of_nonneg_left hd (Real.rpow_pos_of_pos hx (-2-a)).le
  have hc := power_slack_mul x a hx
  have hid : Real.rpow x (-2-a)*((5/4)*ε*x) =
      (5/4)*ε*(Real.rpow x (-2-a)*x) := by ring
  simp only [Real.rpow_eq_pow] at hm hc hid ht ⊢
  rw [hid, hc] at hm
  nlinarith only [ht, hm]

/-- The separate upper and lower power changes used in Lemmas 4.9 and 4.10. -/
theorem stability_power_changes_at_exponent (I : Instance) (U a ε : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε) (e : Fin I.m) :
    |Real.rpow ((I.edge e).upper-fbar e) (-1-a) -
      Real.rpow ((I.edge e).upper-f e) (-1-a)| ≤
      (5/2)*ε*Real.rpow ((I.edge e).upper-f e) (-1-a) ∧
    |Real.rpow (fbar e-(I.edge e).lower) (-1-a) -
      Real.rpow (f e-(I.edge e).lower) (-1-a)| ≤
      (5/2)*ε*Real.rpow (f e-(I.edge e).lower) (-1-a) := by
  have hs := stability_slacks_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hclose e
  have ha := haNonneg
  have ha' := haUpper.trans (alpha_le I U hsize)
  constructor
  · have h := power_change_of_relative_slack ((I.edge e).upper-f e) (a)
      (-(fbar e-f e)) ε (sub_pos.mpr (hf e).2) ha ha' hε'
      (by simpa only [abs_neg] using hs.1)
    rw [show ((I.edge e).upper : ℝ)-f e + -(fbar e-f e) = (I.edge e).upper-fbar e by ring] at h
    exact h
  · have h := power_change_of_relative_slack (f e-(I.edge e).lower) (a)
      (fbar e-f e) ε (sub_pos.mpr (hf e).1) ha ha' hε' hs.2
    rw [show f e-((I.edge e).lower : ℝ)+(fbar e-f e) = fbar e-(I.edge e).lower by ring] at h
    exact h

/-- The pointwise relative error bound in the proof of Lemma 4.9 (page 29). -/
private theorem lengths_change_le_at_exponent (I : Instance) (U a ε : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε) (e : Fin I.m) :
    |lengths I (a) fbar e - lengths I (a) f e| ≤
      (5/2)*ε*lengths I (a) f e := by
  obtain ⟨hu, hl⟩ := stability_power_changes_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hε' hclose e
  have hid : lengths I a fbar e - lengths I a f e =
      (Real.rpow ((I.edge e).upper-fbar e) (-1-a) -
        Real.rpow ((I.edge e).upper-f e) (-1-a)) +
      (Real.rpow (fbar e-(I.edge e).lower) (-1-a) -
        Real.rpow (f e-(I.edge e).lower) (-1-a)) := by unfold lengths; ring
  rw [hid]
  have ht := abs_add_le
    (Real.rpow ((I.edge e).upper-fbar e) (-1-a)-Real.rpow ((I.edge e).upper-f e) (-1-a))
    (Real.rpow (fbar e-(I.edge e).lower) (-1-a)-Real.rpow (f e-(I.edge e).lower) (-1-a))
  unfold lengths
  linarith only [ht, hu, hl]

/-- Lemma 4.9 (page 29) (length stability) of Chen et al., arXiv:2203.00671v2:
old weighted maximum displacement at most `ε ≤ 1/100` gives length
approximation factor `1+3ε`. The capacity and exponent domain conditions
implicit in the source are explicit here. -/
theorem lemma_4_9_at_exponent (I : Instance) (U a ε : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε) :
    VectorApprox (1+3*ε) (lengths I (a) f) (lengths I (a) fbar) := by
  intro e
  exact scalar_approx_of_small_error _ _ ε (lengths_pos I (a) f hf e) hε hε'
    (lengths_change_le_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hε' hclose e)

end MinCostFlow.IPM.Machine
