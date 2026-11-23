module

public import MinCostFlow.IPM.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First-order power stability

The two first-order bounds in Lemma 4.5 (page 26) of Chen et al.,
arXiv:2203.00671v2, follow by bounding the derivative on a relative
one-tenth interval. The derivative is at most twice its reference power.
The mean value theorem then bounds the change.
-/

public section
namespace MinCostFlow.IPM

private theorem power_derivative_bound (x a z : ℝ) (hx : 0 < x)
    (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hz : (9/10)*x ≤ z) :
    |(-1-a) * z ^ (-2-a)| ≤ 2 * x ^ (-2-a) := by
  have hzpos : 0 < z := lt_of_lt_of_le (mul_pos (by norm_num) hx) hz
  have hmono := Real.rpow_le_rpow_of_nonpos
    (mul_pos (by norm_num : (0 : ℝ) < 9/10) hx) hz
    (by linarith only [ha] : -2-a ≤ 0)
  rw [Real.mul_rpow (by norm_num) hx.le] at hmono
  have hbase := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 9/10) (by norm_num : (9/10 : ℝ) ≤ 1)
    (by linarith only [ha'] : (-3 : ℝ) ≤ -2-a)
  norm_num at hbase
  have hxp : 0 ≤ x ^ (-2-a) := (Real.rpow_pos_of_pos hx _).le
  have hb := mul_le_mul_of_nonneg_right hbase hxp
  have hcoeff : (1+a)*(1000/729 : ℝ) ≤ 2 := by linarith only [ha']
  rw [abs_mul, abs_of_nonpos (by linarith only [ha] : -1-a ≤ 0),
    abs_of_pos (Real.rpow_pos_of_pos hzpos _)]
  have hm := mul_le_mul_of_nonneg_left (hmono.trans hb)
    (by linarith only [ha] : 0 ≤ -(-1-a))
  have hc := mul_le_mul_of_nonneg_right hcoeff hxp
  nlinarith only [hm, hc]

/-- The first-order power estimate used twice in Lemma 4.5 (page 26). -/
theorem power_change_le (x a d : ℝ) (hx : 0 < x)
    (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hd : |d| ≤ x/10) :
    |Real.rpow (x+d) (-1-a) - Real.rpow x (-1-a)| ≤
      2 * |d| * Real.rpow x (-2-a) := by
  let s := Set.Icc ((9/10)*x) ((11/10)*x)
  have hxp : x ∈ s := by constructor <;> linarith only [hx]
  have hxdp : x+d ∈ s := by
    have hh := abs_le.mp hd
    constructor <;> linarith only [hh.1, hh.2]
  have hderiv : ∀ z ∈ s, HasDerivWithinAt (fun t : ℝ => t ^ (-1-a))
      ((-1-a)*z^(-2-a)) s z := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le (mul_pos (by norm_num) hx) hz.1
    have h := Real.hasDerivAt_rpow_const (p := -1-a) (Or.inl hzpos.ne')
    rw [show (-1-a)-1 = -2-a by ring] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ z ∈ s, ‖(-1-a)*z^(-2-a)‖ ≤ 2*x^(-2-a) := by
    intro z hz
    exact power_derivative_bound x a z hx ha ha' hz.1
  have h := (convex_Icc ((9/10)*x) ((11/10)*x)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hxp hxdp
  simp only [Real.norm_eq_abs, add_sub_cancel_left, Real.rpow_eq_pow] at h ⊢
  calc
    |(x+d)^(-1-a) - x^(-1-a)| ≤ 2*x^(-2-a)*|d| := h
    _ = 2*|d| *x^(-2-a) := by ring

/-- The upper-slack first-order bound in Lemma 4.5 (page 26), equation (14). -/
theorem lemma_4_5_upper (I : Instance) (a : ℝ) (f : Fin I.m → ℝ) (e : Fin I.m)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (d : ℝ) (hd : |d| ≤ ((I.edge e).upper - f e)/10) :
    |Real.rpow ((I.edge e).upper - f e - d) (-1-a) -
      Real.rpow ((I.edge e).upper - f e) (-1-a)| ≤
      2*|d| *Real.rpow ((I.edge e).upper - f e) (-2-a) := by
  simpa only [sub_eq_add_neg, abs_neg] using
    power_change_le ((I.edge e).upper - f e) a (-d) (sub_pos.mpr (hf e).2)
      ha ha' (by simpa only [abs_neg] using hd)

/-- The lower-slack first-order bound in Lemma 4.5 (page 26), equation (15). -/
theorem lemma_4_5_lower (I : Instance) (a : ℝ) (f : Fin I.m → ℝ) (e : Fin I.m)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (d : ℝ) (hd : |d| ≤ (f e - (I.edge e).lower)/10) :
    |Real.rpow (f e + d - (I.edge e).lower) (-1-a) -
      Real.rpow (f e - (I.edge e).lower) (-1-a)| ≤
      2*|d| *Real.rpow (f e - (I.edge e).lower) (-2-a) := by
  have h := power_change_le (f e - (I.edge e).lower) a d
    (sub_pos.mpr (hf e).1) ha ha' hd
  rw [show f e - (I.edge e).lower + d = f e + d - (I.edge e).lower by ring] at h
  exact h

end MinCostFlow.IPM
