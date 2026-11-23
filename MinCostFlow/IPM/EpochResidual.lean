module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Residual stability during a full epoch

Chen et al., arXiv:2203.00671v2, Lemma 9.1 (page 70), bounds
the accumulated residual drift between refreshes. A relative change
of at most `γ/m` per step, with `γ ≤ 1/100`, gives at most a
`1+4γ` factor change during `m` steps. The proof sums absolute changes
while maintaining the bound that the current residual is at most twice
the initial one. It keeps the small step parameter rather than replacing
it by one, so a full epoch can have `m` steps.
-/

public section
namespace MinCostFlow.IPM

private theorem drift_bound (R : ℕ → ℝ) (m n : ℕ) (γ : ℝ)
    (hm : 0 < m) (hn : n ≤ m) (hg : 0 ≤ γ) (hg' : γ ≤ 1/100)
    (hpos : ∀ t ≤ n, 0 < R t)
    (hstep : ∀ t < n, |R (t+1)-R t|/R t ≤ γ/m) :
    ∀ t ≤ n, |R t-R 0| ≤ (2*γ*t/m)*R 0 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  intro t
  induction t with
  | zero => intro _; simp only [Nat.cast_zero, mul_zero, zero_div, zero_mul, sub_self, abs_zero, le_refl]
  | succ t ih =>
    intro ht
    have ht' : t ≤ n := Nat.le_of_succ_le ht
    have hi := ih ht'
    have htR : (t : ℝ) ≤ m := by exact_mod_cast ht'.trans hn
    have hcoef : 2*γ*t/m ≤ 2*γ := by
      apply (div_le_iff₀ hmR).mpr
      exact mul_le_mul_of_nonneg_left htR (mul_nonneg (by norm_num) hg)
    have hbound : R t ≤ 2*R 0 := by
      have hupper := (abs_le.mp hi).2
      have hpaid := mul_le_mul_of_nonneg_right hcoef (hpos 0 (Nat.zero_le n)).le
      have hγ := mul_le_mul_of_nonneg_right hg' (hpos 0 (Nat.zero_le n)).le
      linarith only [hupper, hpaid, hγ, (hpos 0 (Nat.zero_le n)).le]
    have hdiff := (div_le_iff₀ (hpos t ht')).mp (hstep t (Nat.lt_of_succ_le ht))
    have hmul := mul_le_mul_of_nonneg_left hbound (div_nonneg hg hmR.le)
    have htri := abs_sub_le (R (t+1)) (R t) (R 0)
    have hnext : (γ/m)*(2*R 0)+(2*γ*t/m)*R 0 = (2*γ*(t+1)/m)*R 0 := by ring
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [htri, hdiff, hi, hmul, hnext]

/-- A stored residual remains a `1+4γ` approximation throughout an
`m`-step epoch whose relative step drift is at most `γ/m`. This is the
accumulation argument in Chen et al., Lemma 9.1 (page 70), with
explicit constants. -/
theorem epoch_residual_approx_prefix (R : ℕ → ℝ) (m n : ℕ) (γ : ℝ)
    (hm : 0 < m) (hn : n ≤ m) (hg : 0 ≤ γ) (hg' : γ ≤ 1/100)
    (hpos : ∀ t ≤ n, 0 < R t)
    (hstep : ∀ t < n, |R (t+1)-R t|/R t ≤ γ/m) (t : ℕ) (ht : t ≤ n) :
    ScalarApprox (1+4*γ) (R 0) (R t) := by
  have herr := drift_bound R m n γ hm hn hg hg' hpos hstep t ht
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have htR : (t : ℝ) ≤ m := by exact_mod_cast ht.trans hn
  have hcoef : 2*γ*t/m ≤ 2*γ := (div_le_iff₀ hmR).mpr
    (mul_le_mul_of_nonneg_left htR (mul_nonneg (by norm_num) hg))
  have hpaid := mul_le_mul_of_nonneg_right hcoef (hpos 0 (Nat.zero_le n)).le
  have hclose : |R t-R 0| ≤ 2*γ*R 0 := herr.trans hpaid
  have hb : 0 < 1+4*γ := by linarith only [hg]
  refine ⟨hpos 0 (Nat.zero_le n), hpos t ht, ?_, ?_⟩
  · apply (inv_mul_le_iff₀ hb).mpr
    have hh := (abs_le.mp hclose).2
    have hp := mul_nonneg hg (hpos 0 (Nat.zero_le n)).le
    linarith only [hh, hp]
  · have hlow : (1-2*γ)*R 0 ≤ R t := by linarith only [(abs_le.mp hclose).1]
    have hmul := mul_le_mul_of_nonneg_left hlow hb.le
    have hfactor : 1 ≤ (1+4*γ)*(1-2*γ) := by nlinarith only [hg, hg']
    have hpay := mul_le_mul_of_nonneg_right hfactor (hpos 0 (Nat.zero_le n)).le
    nlinarith only [hmul, hpay]

end MinCostFlow.IPM
