module

public import MinCostFlow.IPM.Definitions
import all MinCostFlow.IPM.PowerStability
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The quadratic power bound

The quadratic part of Lemma 4.5 (page 26) of Chen et al., arXiv:2203.00671v2,
follows from Taylor's theorem with a second-derivative remainder.
The same derivative bound as in the first-order estimates controls that
remainder on the relative one-tenth interval.
-/

public section
namespace MinCostFlow.IPM

private theorem power_second_derivative (a z : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => x ^ (-a)) z =
      (-a)*(-1-a)*z^(-2-a) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_rpow_const', deriv_const_mul_field]
  rw [Real.deriv_rpow_const]
  rw [show -a-1 = -1-a by ring, show (-1-a)-1 = -2-a by ring]
  ring

/-- The scalar quadratic estimate underlying Lemma 4.5 (page 26). -/
theorem power_taylor_le (x a d : ℝ) (hx : 0 < x)
    (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hd : |d| ≤ x/10) :
    Real.rpow (x+d) (-a) ≤ Real.rpow x (-a) -
      a*Real.rpow x (-1-a)*d + a*Real.rpow x (-2-a)*d^2 := by
  simp only [Real.rpow_eq_pow]
  by_cases hd0 : d = 0
  · subst d
    simp
  have hne : x ≠ x+d := by intro h; apply hd0; linarith only [h]
  have hlow : ∀ z ∈ Set.uIcc x (x+d), (9/10)*x ≤ z := by
    intro z hz
    have hh := abs_le.mp hd
    rcases Set.mem_uIcc.mp hz with hz | hz <;> linarith only [hz.1, hz.2, hh.1, hh.2, hx]
  have hzpos : ∀ z ∈ Set.uIcc x (x+d), 0 < z := fun z hz =>
    lt_of_lt_of_le (mul_pos (by norm_num) hx) (hlow z hz)
  have hcont : ContDiffOn ℝ (1+1) (fun t : ℝ => t ^ (-a)) (Set.uIcc x (x+d)) := by
    intro z hz
    exact (Real.contDiffAt_rpow_const_of_ne (hzpos z hz).ne').contDiffWithinAt
  obtain ⟨z, hz, ht⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hcont
  have hwithin : derivWithin (fun t : ℝ => t ^ (-a)) (Set.uIcc x (x+d)) x =
      (-a)*x^(-1-a) := by
    have h := Real.hasDerivAt_rpow_const (p := -a) (Or.inl hx.ne')
    rw [show -a-1 = -1-a by ring] at h
    exact h.hasDerivWithinAt.derivWithin ((uniqueDiffOn_uIcc hne) x (Set.left_mem_uIcc))
  simp only [taylorWithinEval_succ, taylor_within_zero_eval] at ht
  norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, inv_one,
    zero_add, pow_one, smul_eq_mul] at ht
  rw [iteratedDerivWithin_one, hwithin, power_second_derivative] at ht
  have hzb : (9/10)*x ≤ z := hlow z (Set.uIoo_subset_uIcc_self hz)
  have hbd := power_derivative_bound x a z hx ha ha' hzb
  have hsign : (-1-a)*z^(-2-a) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha])
      (Real.rpow_pos_of_pos (hzpos z (Set.uIoo_subset_uIcc_self hz)) _).le
  rw [abs_of_nonpos hsign] at hbd
  have hmul := mul_le_mul_of_nonneg_left hbd ha
  have hsquare := mul_le_mul_of_nonneg_right hmul (sq_nonneg d)
  rw [show x+d-x = d by ring] at ht
  nlinarith only [ht, hsquare]

/-- Lemma 4.5 (page 26) (Taylor expansion for `x⁻α`), the quadratic estimate for
the sum of the upper and lower barriers. -/
theorem lemma_4_5 (I : Instance) (a : ℝ) (f : Fin I.m → ℝ) (e : Fin I.m)
    (hf : StrictlyInside I f) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (d : ℝ) (hd : |d| ≤ (1/10)*min ((I.edge e).upper-f e) (f e-(I.edge e).lower)) :
    edgeBarrier I a e (f e+d) ≤ edgeBarrier I a e (f e) +
      a*(Real.rpow ((I.edge e).upper-f e) (-1-a) -
        Real.rpow (f e-(I.edge e).lower) (-1-a))*d +
      a*(Real.rpow ((I.edge e).upper-f e) (-2-a) +
        Real.rpow (f e-(I.edge e).lower) (-2-a))*d^2 := by
  have hu : |d| ≤ ((I.edge e).upper-f e)/10 := by
    have hmin := min_le_left ((I.edge e).upper-f e) (f e-(I.edge e).lower)
    linarith only [hd, hmin]
  have hl : |d| ≤ (f e-(I.edge e).lower)/10 := by
    have hmin := min_le_right ((I.edge e).upper-f e) (f e-(I.edge e).lower)
    linarith only [hd, hmin]
  have hup := power_taylor_le ((I.edge e).upper-f e) a (-d)
    (sub_pos.mpr (hf e).2) ha ha' (by simpa only [abs_neg] using hu)
  have hlo := power_taylor_le (f e-(I.edge e).lower) a d
    (sub_pos.mpr (hf e).1) ha ha' hl
  dsimp only [edgeBarrier]
  rw [show ((I.edge e).upper : ℝ)-(f e+d) = (I.edge e).upper-f e + -d by ring,
    show f e+d-(I.edge e).lower = f e-(I.edge e).lower+d by ring]
  nlinarith only [hup, hlo]

end MinCostFlow.IPM
