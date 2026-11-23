module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Error bounds for the exponential

On arguments of absolute value at most one half, a linear number of Taylor
terms gives a relative dyadic error. A second bound describes how perturbing
an argument changes its exponential. Both bounds concern exact real values.
-/

@[expose] public section
namespace MinCostFlow.Num
open Finset

/-- The first `n` terms of the exponential series. -/
noncomputable def expSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i∈range n,x^i/i.factorial

/-- An argument error at most one gives relative output error at most twice
that argument error. -/
theorem exp_argument_error {x y δ : ℝ} (hδ : δ≤1) (hxy : |y-x|≤δ) :
    |Real.exp y-Real.exp x|≤2*δ*Real.exp x := by
  have hh := Real.abs_exp_sub_one_le (le_trans hxy hδ)
  have he : Real.exp y-Real.exp x=Real.exp x*(Real.exp (y-x)-1) := by
    rw [mul_sub,mul_one,← Real.exp_add]
    congr 1
    ring_nf
  rw [he,abs_mul,abs_of_pos (Real.exp_pos x)]
  calc
    _ ≤ Real.exp x*(2*|y-x|) := mul_le_mul_of_nonneg_left hh (le_of_lt (Real.exp_pos x))
    _ ≤ Real.exp x*(2*δ) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hxy (by norm_num)) (le_of_lt (Real.exp_pos x))
    _ = 2*δ*Real.exp x := by ring

/-- On the reduced interval, the Taylor remainder is at most `2|x|ⁿ`. -/
theorem exp_series_remainder {x : ℝ} (hx : |x|≤1) {n : ℕ} (hn : 0<n) :
    |Real.exp x-expSeries x n|≤2*|x|^n := by
  have hb := Real.exp_bound hx hn
  have hnf : (1:ℝ)≤n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hratio : ((n+1:ℕ):ℝ)/((n.factorial:ℝ)*n)≤2 := by
    apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le (by norm_num) hnf) hnp)).mpr
    push_cast
    nlinarith only [hnf,hnp,hn1]
  exact le_trans hb (by
    calc
      _ ≤ |x|^n*2 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2*|x|^n := by ring)

/-- At most `q+2` exact-real Taylor terms give relative error `2⁻q`
for arguments of absolute value at most one half. -/
theorem exp_series_relative {x : ℝ} (hx : |x|≤1/2) (q : ℕ) :
    |expSeries x (q+2)-Real.exp x|≤(1/(2:ℝ)^q)*Real.exp x := by
  have hb := exp_series_remainder (le_trans hx (by norm_num)) (show 0<q+2 by omega)
  have hp : |x|^(q+2)≤(1/2:ℝ)^(q+2) := pow_le_pow_left₀ (abs_nonneg x) hx _
  have he : (1/2:ℝ)≤Real.exp x := by
    have hxlo := (abs_le.mp hx).1
    have hh := Real.add_one_le_exp x
    linarith
  have hq : (1/2:ℝ)^q=1/(2:ℝ)^q := by rw [div_pow,one_pow]
  have hnonneg : (0:ℝ)≤1/(2:ℝ)^q := by positivity
  rw [abs_sub_comm]
  calc
    _ ≤ 2*|x|^(q+2) := hb
    _ ≤ 2*(1/2:ℝ)^(q+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = (1/(2:ℝ)^q)*(1/2) := by rw [pow_add,hq]; ring
    _ ≤ (1/(2:ℝ)^q)*Real.exp x := mul_le_mul_of_nonneg_left he hnonneg

end MinCostFlow.Num
