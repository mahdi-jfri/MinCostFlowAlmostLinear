module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.RCLike.Basic

/-!
# Fourier analysis on the torus `ℤ_m × ℤ_m`

The expansion of the Margulis graph (`Margulis.lean`) is proved by Fourier analysis on the torus
`ℤ_m × ℤ_m`, as in Hoory, Linial and Wigderson, *Expander graphs and their applications*, Bull.
AMS 43 (2006), Section 8. This file gives the three facts that proof needs.

* `sum_star_fourier_mul`: Parseval's identity, `∑_u conj(F u) G u = m² ∑_x conj(f x) g x`, where
  `F` and `G` are the transforms of `f` and `g`. It follows from the orthogonality of the
  characters, `∑_u χ(u·z) = m²` if `z = 0` and `0` otherwise (`sum_char_dot`).
* `fourier_comp_shearA`, `fourier_comp_shearB`: the transform of `f` composed with an affine shear
  `(x, y) ↦ (x + 2y + c, y)` is the transform of `f` at a sheared point, times a character. This is
  a change of variables in the sum.
* `norm_one_add_char`: `‖1 + χ(a)‖ = 2 cos(π |a| / m)`, where `|a|` is the absolute value of the
  representative of `a` in `(-m/2, m/2]`.

The character is `χ(a) = exp(2πi a / m)` (`ZMod.stdAddChar`), and the transform of `f` is
`F(u) = ∑_x f(x) χ(-(u₁ x₁ + u₂ x₂))`.
-/

public section

namespace MinCostFlow.ExplicitExpander

open Complex Finset

variable {m : ℕ} [NeZero m]

/-- The torus `ℤ_m × ℤ_m`. -/
abbrev Torus (m : ℕ) := ZMod m × ZMod m

/-- The Fourier transform on the torus: `F(u) = ∑_x f(x) χ(-(u₁ x₁ + u₂ x₂))`. -/
@[expose] noncomputable def fourier (f : Torus m → ℂ) (u : Torus m) : ℂ :=
  ∑ x : Torus m, f x * ZMod.stdAddChar (-(u.1 * x.1 + u.2 * x.2))

/-- The size of `a : ℤ_m`: the absolute value of its representative in `(-m/2, m/2]`. -/
@[expose] def size (a : ZMod m) : ℤ := |a.valMinAbs|

/-- `cos(π |a| / m)`, which is half of `‖1 + χ(a)‖`. -/
@[expose] noncomputable def halfCos (m : ℕ) (a : ℤ) : ℝ := Real.cos (Real.pi * a / m)

private lemma sum_char_mul (a : ZMod m) :
    ∑ u : ZMod m, ZMod.stdAddChar (u * a) = if a = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  split_ifs <;> simp

/-- Orthogonality of the characters of the torus. -/
lemma sum_char_dot (a b : ZMod m) :
    ∑ u : Torus m, ZMod.stdAddChar (u.1 * a + u.2 * b) =
      if a = 0 ∧ b = 0 then ((m : ℂ) ^ 2) else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum, sum_char_mul, sum_char_mul]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, sq]

/-- Parseval's identity on the torus. -/
theorem sum_star_fourier_mul (f g : Torus m → ℂ) :
    ∑ u, (starRingEnd ℂ) (fourier f u) * fourier g u =
      (m : ℂ) ^ 2 * ∑ x, (starRingEnd ℂ) (f x) * g x := by
  have hconj : ∀ z : ZMod m,
      (starRingEnd ℂ) (ZMod.stdAddChar (-z)) = ZMod.stdAddChar z := by
    intro z
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  have hstep : ∀ u : Torus m, (starRingEnd ℂ) (fourier f u) * fourier g u =
      ∑ x, ∑ y, (starRingEnd ℂ) (f x) * g y *
        (ZMod.stdAddChar (u.1 * x.1 + u.2 * x.2) * ZMod.stdAddChar (-(u.1 * y.1 + u.2 * y.2))) := by
    intro u
    simp only [fourier, map_sum, map_mul, hconj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hcomb : ∀ u x y : Torus m,
      ZMod.stdAddChar (u.1 * x.1 + u.2 * x.2) * ZMod.stdAddChar (-(u.1 * y.1 + u.2 * y.2)) =
        ZMod.stdAddChar (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2)) := by
    intro u x y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hstep, hcomb]
  calc ∑ u : Torus m, ∑ x : Torus m, ∑ y : Torus m, (starRingEnd ℂ) (f x) * g y *
        ZMod.stdAddChar (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2))
      = ∑ x : Torus m, ∑ y : Torus m, ∑ u : Torus m, (starRingEnd ℂ) (f x) * g y *
        ZMod.stdAddChar (u.1 * (x.1 - y.1) + u.2 * (x.2 - y.2)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = (m : ℂ) ^ 2 * ∑ x, (starRingEnd ℂ) (f x) * g x := by
        simp_rw [← Finset.mul_sum, sum_char_dot, sub_eq_zero]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · simp only [and_self, ↓reduceIte]
          ring
        · intro y _ hyx
          have : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun h => hyx (Prod.ext h.1.symm h.2.symm)
          simp [this]
        · simp

/-- The shear `(x, y) ↦ (x + 2y + c, y)` of the torus. -/
@[expose] def shearA (c : ZMod m) : Torus m ≃ Torus m where
  toFun x := (x.1 + 2 * x.2 + c, x.2)
  invFun x := (x.1 - 2 * x.2 - c, x.2)
  left_inv x := by ext <;> simp; ring
  right_inv x := by ext <;> simp; ring

/-- The shear `(x, y) ↦ (x, y + 2x + c)` of the torus. -/
@[expose] def shearB (c : ZMod m) : Torus m ≃ Torus m where
  toFun x := (x.1, x.2 + 2 * x.1 + c)
  invFun x := (x.1, x.2 - 2 * x.1 - c)
  left_inv x := by ext <;> simp; ring
  right_inv x := by ext <;> simp; ring

omit [NeZero m] in
@[simp] lemma shearA_apply (c : ZMod m) (x : Torus m) :
    shearA c x = (x.1 + 2 * x.2 + c, x.2) := rfl

omit [NeZero m] in
@[simp] lemma shearB_apply (c : ZMod m) (x : Torus m) :
    shearB c x = (x.1, x.2 + 2 * x.1 + c) := rfl

/-- The transform of `f ∘ shearA c` at `u` is `χ(u₁ c) F(u₁, u₂ - 2u₁)`. -/
theorem fourier_comp_shearA (f : Torus m → ℂ) (c : ZMod m) (u : Torus m) :
    fourier (fun x => f (shearA c x)) u =
      ZMod.stdAddChar (u.1 * c) * fourier f (u.1, u.2 - 2 * u.1) := by
  unfold fourier
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (shearA c) _ _ fun x => ?_
  simp only [shearA_apply]
  have : -(u.1 * x.1 + u.2 * x.2) =
      u.1 * c + -(u.1 * (x.1 + 2 * x.2 + c) + (u.2 - 2 * u.1) * x.2) := by ring
  rw [this, AddChar.map_add_eq_mul]
  ring

/-- The transform of `f ∘ shearB c` at `u` is `χ(u₂ c) F(u₁ - 2u₂, u₂)`. -/
theorem fourier_comp_shearB (f : Torus m → ℂ) (c : ZMod m) (u : Torus m) :
    fourier (fun x => f (shearB c x)) u =
      ZMod.stdAddChar (u.2 * c) * fourier f (u.1 - 2 * u.2, u.2) := by
  unfold fourier
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (shearB c) _ _ fun x => ?_
  simp only [shearB_apply]
  have : -(u.1 * x.1 + u.2 * x.2) =
      u.2 * c + -((u.1 - 2 * u.2) * x.1 + u.2 * (x.2 + 2 * x.1 + c)) := by ring
  rw [this, AddChar.map_add_eq_mul]
  ring

/-- The transform of a sum is the sum of the transforms. -/
lemma fourier_add (f g : Torus m → ℂ) (u : Torus m) :
    fourier (fun x => f x + g x) u = fourier f u + fourier g u := by
  simp only [fourier, add_mul, Finset.sum_add_distrib]

/-- The transform at `0` is the sum of the values. -/
lemma fourier_zero (f : Torus m → ℂ) : fourier f 0 = ∑ x, f x := by
  simp [fourier]

lemma halfCos_nonneg {a : ℤ} (h0 : 0 ≤ a) (h : 2 * a ≤ m) : 0 ≤ halfCos m a := by
  unfold halfCos
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have : (0 : ℝ) ≤ Real.pi * a / m := by positivity
    linarith [Real.pi_pos]
  · rw [div_le_iff₀ hm]
    have : (2 : ℝ) * a ≤ m := by exact_mod_cast h
    nlinarith [Real.pi_pos]

omit [NeZero m] in
lemma size_nonneg (a : ZMod m) : 0 ≤ size a := abs_nonneg _

lemma two_mul_size_le (a : ZMod m) : 2 * size a ≤ m := by
  have h := ZMod.valMinAbs_mem_Ioc a
  simp only [Set.mem_Ioc] at h
  unfold size
  rcases abs_cases a.valMinAbs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega

/-- `‖1 + χ(a)‖ = 2 cos(π |a| / m)`. -/
theorem norm_one_add_char (a : ZMod m) :
    ‖1 + ZMod.stdAddChar a‖ = 2 * halfCos m (size a) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  set s := a.valMinAbs with hs
  have hchar : ZMod.stdAddChar a = Complex.exp (Complex.I * ((2 * Real.pi * s / m : ℝ))) := by
    conv_lhs => rw [← ZMod.coe_valMinAbs a]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hneg : 1 + ZMod.stdAddChar a =
      -(Complex.exp (Complex.I * ((2 * Real.pi * s / m + Real.pi : ℝ))) - 1) := by
    rw [hchar]
    push_cast
    rw [show ∀ z : ℂ, I * (z + Real.pi) = I * z + Real.pi * I from fun z => by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hneg, norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two]
  congr 1
  have h1 : (2 * Real.pi * s / m + Real.pi) / 2 = Real.pi * s / m + Real.pi / 2 := by
    field_simp
  rw [h1, Real.sin_add_pi_div_two, halfCos, size]
  have hcos : Real.cos (Real.pi * (|s| : ℤ) / m) = Real.cos (Real.pi * s / m) := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, ← Real.cos_neg]
      congr 1
      push_cast
      ring
  rw [hcos]
  apply abs_of_nonneg
  rw [← hcos]
  exact halfCos_nonneg (abs_nonneg s) (by have := two_mul_size_le a; unfold size at this; omega)

end MinCostFlow.ExplicitExpander
