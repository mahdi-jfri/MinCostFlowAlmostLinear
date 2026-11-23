module

public import MinCostFlow.ExplicitExpander.CosBound
import Mathlib.Analysis.RCLike.Basic

/-!
# The Margulis graph expands

The Margulis graph on the torus `ℤ_m × ℤ_m` (in the form of Gabber and Galil) joins each point
`x = (x₁, x₂)` to the four points `(x₁ + 2x₂, x₂)`, `(x₁ + 2x₂ + 1, x₂)`, `(x₁, x₂ + 2x₁)` and
`(x₁, x₂ + 2x₁ + 1)`, the images of `x` under `shearA 0`, `shearA 1`, `shearB 0` and
`shearB 1`. This file proves that the graph expands: for every set `A` of points, at least
`min(|A|, m² - |A|) / 4` of these `4m²` pairs have exactly one end in `A`
(`card_crossing_ge`).

The proof follows Hoory, Linial and Wigderson, *Expander graphs and their applications*, Bull. AMS
43 (2006), Section 8, with the weights `3/2` and `2/3` of `CosBound.lean`.

1. For a real function `f` with `∑ f = 0`,
   `|∑_x f(x) (f(A₀x) + f(A₁x) + f(B₀x) + f(B₁x))| ≤ (15/4) ∑ f²` (`quadratic_form_le`). By
   Parseval's identity and the shear rule of `Fourier.lean`, the left side is
   `1/m² · |∑_u conj(F u) (F(u₁, u₂ - 2u₁)(1 + χ(u₁)) + F(u₁ - 2u₂, u₂)(1 + χ(u₂)))|`, and
   `F(0) = 0`. Each product `2|F(u)| |F(v)|` is at most `W |F(u)|² + W⁻¹ |F(v)|²`, with `W` the
   weight of `v` seen from `u` (`fourier_side_le`). Collecting the terms of each `u` gives
   `coeff` of `CosBound.lean` times `|F(u)|²`, which is at most `15/4`.
2. Apply 1 to the indicator of `A` minus its mean. The pairs that cross `A` count
   `∑_x ∑_T (f(x) - f(Tx))² = 8 ∑ f² - 2 ∑_x f(x) ∑_T f(Tx) ≥ (1/2) ∑ f²`, and
   `∑ f² = |A| (m² - |A|) / m²`.
-/

public section

namespace MinCostFlow.ExplicitExpander

open Complex Finset

variable {m : ℕ} [NeZero m]

/-- The map `u ↦ (u₁, u₂ - 2u₁)`, which the shears `shearA` become under the transform. -/
@[expose] def dualA : Torus m ≃ Torus m where
  toFun u := (u.1, u.2 - 2 * u.1)
  invFun u := (u.1, u.2 + 2 * u.1)
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp

/-- The map `u ↦ (u₁ - 2u₂, u₂)`, which the shears `shearB` become under the transform. -/
@[expose] def dualB : Torus m ≃ Torus m where
  toFun u := (u.1 - 2 * u.2, u.2)
  invFun u := (u.1 + 2 * u.2, u.2)
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp

/-- The weight sum at `u`, as a function of the point. -/
private noncomputable def coeffAt (u : Torus m) : ℝ :=
  halfCos m (size u.1) * (weight (size u.2) (size (u.2 - 2 * u.1)) +
      weight (size u.2) (size (u.2 + 2 * u.1))) +
    halfCos m (size u.2) * (weight (size u.1) (size (u.1 - 2 * u.2)) +
      weight (size u.1) (size (u.1 + 2 * u.2)))

omit [NeZero m] in
private lemma size_intCast (p : ℤ) : size (p : ZMod m) = sizeI m p := rfl

omit [NeZero m] in
/-- The weights of a pair of neighbours do not change when the coordinates change sign. -/
private lemma pair_abs (c s t : ℤ) :
    weight c (sizeI m (t - 2 * s)) + weight c (sizeI m (t + 2 * s)) =
      weight c (sizeI m (|t| - 2 * |s|)) + weight c (sizeI m (|t| + 2 * |s|)) := by
  rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;>
    rw [hs, ht]
  · rw [show -t - 2 * s = -(t + 2 * s) by ring, show -t + 2 * s = -(t - 2 * s) by ring,
      sizeI_neg, sizeI_neg, add_comm]
  · rw [show t - 2 * -s = t + 2 * s by ring, show t + 2 * -s = t - 2 * s by ring, add_comm]
  · rw [show -t - 2 * -s = -(t - 2 * s) by ring, show -t + 2 * -s = -(t + 2 * s) by ring,
      sizeI_neg, sizeI_neg]

omit [NeZero m] in
private lemma coeffAt_eq (u : Torus m) :
    coeffAt u = coeff m (size u.1) (size u.2) := by
  have h1 : u.2 - 2 * u.1 = ((u.2.valMinAbs - 2 * u.1.valMinAbs : ℤ) : ZMod m) := by
    push_cast; simp
  have h2 : u.2 + 2 * u.1 = ((u.2.valMinAbs + 2 * u.1.valMinAbs : ℤ) : ZMod m) := by
    push_cast; simp
  have h3 : u.1 - 2 * u.2 = ((u.1.valMinAbs - 2 * u.2.valMinAbs : ℤ) : ZMod m) := by
    push_cast; simp
  have h4 : u.1 + 2 * u.2 = ((u.1.valMinAbs + 2 * u.2.valMinAbs : ℤ) : ZMod m) := by
    push_cast; simp
  unfold coeffAt coeff
  rw [h1, h2, h3, h4, size_intCast, size_intCast, size_intCast, size_intCast,
    pair_abs, pair_abs (t := u.1.valMinAbs)]
  rfl

private lemma coeffAt_le {u : Torus m} (hu : u ≠ 0) : coeffAt u ≤ 15 / 4 := by
  rw [coeffAt_eq]
  apply coeff_le (size_nonneg _) (size_nonneg _) (two_mul_size_le _) (two_mul_size_le _)
  by_contra h
  push Not at h
  have h1 : u.1.valMinAbs = 0 := abs_nonpos_iff.mp h.1
  have h2 : u.2.valMinAbs = 0 := abs_nonpos_iff.mp h.2
  rw [ZMod.valMinAbs_eq_zero] at h1 h2
  exact hu (Prod.ext h1 h2)

private lemma two_mul_le_weight {x y W : ℝ} (hW : 0 < W) :
    2 * x * y ≤ W * x ^ 2 + W⁻¹ * y ^ 2 := by
  have h : 0 ≤ (W * x - y) ^ 2 := sq_nonneg _
  have h' : 2 * x * y * W ≤ (W * x ^ 2 + W⁻¹ * y ^ 2) * W := by
    rw [add_mul, mul_assoc W⁻¹, mul_comm (y ^ 2) W, ← mul_assoc W⁻¹, inv_mul_cancel₀ hW.ne',
      one_mul]
    nlinarith
  exact le_of_mul_le_mul_right h' hW

/-- One pair of terms of the Fourier side, after the weighted inequality and the change of
variables `v = dualA u`. -/
private lemma sum_pairA_le (g : Torus m → ℝ) :
    ∑ u, halfCos m (size u.1) * (2 * g u * g (dualA u)) ≤
      ∑ u, halfCos m (size u.1) * (weight (size u.2) (size (u.2 - 2 * u.1)) +
        weight (size u.2) (size (u.2 + 2 * u.1))) * g u ^ 2 := by
  have hstep : ∀ u : Torus m, halfCos m (size u.1) * (2 * g u * g (dualA u)) ≤
      halfCos m (size u.1) * weight (size u.2) (size (u.2 - 2 * u.1)) * g u ^ 2 +
      halfCos m (size u.1) * (weight (size u.2) (size (u.2 - 2 * u.1)))⁻¹ * g (dualA u) ^ 2 := by
    intro u
    have hc := halfCos_nonneg (m := m) (size_nonneg u.1) (two_mul_size_le u.1)
    have := two_mul_le_weight (x := g u) (y := g (dualA u))
      (weight_pos (size u.2) (size (u.2 - 2 * u.1)))
    nlinarith
  have hre : ∑ u : Torus m, halfCos m (size u.1) *
      (weight (size u.2) (size (u.2 - 2 * u.1)))⁻¹ * g (dualA u) ^ 2 =
      ∑ v : Torus m, halfCos m (size v.1) * weight (size v.2) (size (v.2 + 2 * v.1)) *
        g v ^ 2 := by
    refine Fintype.sum_equiv dualA _ _ fun u => ?_
    have hinv : (weight (size u.2) (size (u.2 - 2 * u.1)))⁻¹ =
        weight (size (u.2 - 2 * u.1)) (size u.2) :=
      inv_eq_of_mul_eq_one_right (weight_mul_weight _ _)
    simp only [dualA, Equiv.coe_fn_mk, sub_add_cancel, hinv]
  calc _ ≤ ∑ u : Torus m, (halfCos m (size u.1) * weight (size u.2) (size (u.2 - 2 * u.1)) *
        g u ^ 2 + halfCos m (size u.1) * (weight (size u.2) (size (u.2 - 2 * u.1)))⁻¹ *
        g (dualA u) ^ 2) := Finset.sum_le_sum fun u _ => hstep u
    _ = _ := by
        rw [Finset.sum_add_distrib, hre, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring

private lemma sum_pairB_le (g : Torus m → ℝ) :
    ∑ u, halfCos m (size u.2) * (2 * g u * g (dualB u)) ≤
      ∑ u, halfCos m (size u.2) * (weight (size u.1) (size (u.1 - 2 * u.2)) +
        weight (size u.1) (size (u.1 + 2 * u.2))) * g u ^ 2 := by
  have hstep : ∀ u : Torus m, halfCos m (size u.2) * (2 * g u * g (dualB u)) ≤
      halfCos m (size u.2) * weight (size u.1) (size (u.1 - 2 * u.2)) * g u ^ 2 +
      halfCos m (size u.2) * (weight (size u.1) (size (u.1 - 2 * u.2)))⁻¹ * g (dualB u) ^ 2 := by
    intro u
    have hc := halfCos_nonneg (m := m) (size_nonneg u.2) (two_mul_size_le u.2)
    have := two_mul_le_weight (x := g u) (y := g (dualB u))
      (weight_pos (size u.1) (size (u.1 - 2 * u.2)))
    nlinarith
  have hre : ∑ u : Torus m, halfCos m (size u.2) *
      (weight (size u.1) (size (u.1 - 2 * u.2)))⁻¹ * g (dualB u) ^ 2 =
      ∑ v : Torus m, halfCos m (size v.2) * weight (size v.1) (size (v.1 + 2 * v.2)) *
        g v ^ 2 := by
    refine Fintype.sum_equiv dualB _ _ fun u => ?_
    have hinv : (weight (size u.1) (size (u.1 - 2 * u.2)))⁻¹ =
        weight (size (u.1 - 2 * u.2)) (size u.1) :=
      inv_eq_of_mul_eq_one_right (weight_mul_weight _ _)
    simp only [dualB, Equiv.coe_fn_mk, sub_add_cancel, hinv]
  calc _ ≤ ∑ u : Torus m, (halfCos m (size u.2) * weight (size u.1) (size (u.1 - 2 * u.2)) *
        g u ^ 2 + halfCos m (size u.2) * (weight (size u.1) (size (u.1 - 2 * u.2)))⁻¹ *
        g (dualB u) ^ 2) := Finset.sum_le_sum fun u _ => hstep u
    _ = _ := by
        rw [Finset.sum_add_distrib, hre, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring

/-- The bound on the Fourier side (Hoory, Linial and Wigderson, Section 8): for `F` with
`F(0) = 0`, `‖∑_u conj(F u) (F(dualA u)(1 + χ(u₁)) + F(dualB u)(1 + χ(u₂)))‖ ≤ (15/4) ∑ ‖F‖²`. -/
theorem fourier_side_le (F : Torus m → ℂ) (hF : F 0 = 0) :
    ‖∑ u, (starRingEnd ℂ) (F u) * (F (dualA u) * (1 + ZMod.stdAddChar u.1) +
      F (dualB u) * (1 + ZMod.stdAddChar u.2))‖ ≤ 15 / 4 * ∑ u, ‖F u‖ ^ 2 := by
  set g : Torus m → ℝ := fun u => ‖F u‖ with hg
  have hterm : ∀ u : Torus m, ‖(starRingEnd ℂ) (F u) * (F (dualA u) *
      (1 + ZMod.stdAddChar u.1) + F (dualB u) * (1 + ZMod.stdAddChar u.2))‖ ≤
      halfCos m (size u.1) * (2 * g u * g (dualA u)) +
        halfCos m (size u.2) * (2 * g u * g (dualB u)) := by
    intro u
    rw [norm_mul, Complex.norm_conj]
    have h1 := norm_add_le (F (dualA u) * (1 + ZMod.stdAddChar u.1))
      (F (dualB u) * (1 + ZMod.stdAddChar u.2))
    rw [norm_mul, norm_mul, norm_one_add_char, norm_one_add_char] at h1
    have h0 : 0 ≤ ‖F u‖ := norm_nonneg _
    calc _ ≤ ‖F u‖ * (‖F (dualA u)‖ * (2 * halfCos m (size u.1)) +
          ‖F (dualB u)‖ * (2 * halfCos m (size u.2))) := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by simp only [hg]; ring
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hterm u
  rw [Finset.sum_add_distrib] at hsum
  have hA := sum_pairA_le g
  have hB := sum_pairB_le g
  have hpt : ∀ u : Torus m, coeffAt u * g u ^ 2 ≤ 15 / 4 * g u ^ 2 := by
    intro u
    by_cases hu : u = 0
    · simp [hg, hu, hF]
    · exact mul_le_mul_of_nonneg_right (coeffAt_le hu) (sq_nonneg _)
  have hC : ∑ u : Torus m, coeffAt u * g u ^ 2 ≤ ∑ u : Torus m, 15 / 4 * g u ^ 2 :=
    Finset.sum_le_sum fun u _ => hpt u
  have hsplit : ∑ u : Torus m, coeffAt u * g u ^ 2 =
      (∑ u, halfCos m (size u.1) * (weight (size u.2) (size (u.2 - 2 * u.1)) +
        weight (size u.2) (size (u.2 + 2 * u.1))) * g u ^ 2) +
      ∑ u, halfCos m (size u.2) * (weight (size u.1) (size (u.1 - 2 * u.2)) +
        weight (size u.1) (size (u.1 + 2 * u.2))) * g u ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold coeffAt; ring
  rw [← Finset.mul_sum] at hC
  calc _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := hsum
    _ ≤ _ := by linarith

/-- **The quadratic form of the Margulis graph.** For a real function `f` on the torus with
`∑ f = 0`, `|∑_x f(x) (f(A₀x) + f(A₁x) + f(B₀x) + f(B₁x))| ≤ (15/4) ∑ f²`, where `A_c = shearA c`
and `B_c = shearB c`. -/
theorem quadratic_form_le (f : Torus m → ℝ) (hf : ∑ x, f x = 0) :
    |∑ x, f x * (f (shearA 0 x) + f (shearA 1 x) + f (shearB 0 x) + f (shearB 1 x))| ≤
      15 / 4 * ∑ x, f x ^ 2 := by
  set fc : Torus m → ℂ := fun x => (f x : ℂ) with hfc
  set F := fourier fc with hF
  have hF0 : F 0 = 0 := by
    rw [hF, fourier_zero]
    show ∑ x, ((f x : ℝ) : ℂ) = 0
    exact_mod_cast hf
  have hH : ∀ u : Torus m, fourier (fun x => fc (shearA 0 x) + fc (shearA 1 x) +
      fc (shearB 0 x) + fc (shearB 1 x)) u =
      F (dualA u) * (1 + ZMod.stdAddChar u.1) + F (dualB u) * (1 + ZMod.stdAddChar u.2) := by
    intro u
    rw [fourier_add, fourier_add, fourier_add, fourier_comp_shearA, fourier_comp_shearA,
      fourier_comp_shearB, fourier_comp_shearB]
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, hF]
    show _ = fourier fc (u.1, u.2 - 2 * u.1) * _ + fourier fc (u.1 - 2 * u.2, u.2) * _
    ring
  have hpars := sum_star_fourier_mul fc (fun x => fc (shearA 0 x) + fc (shearA 1 x) +
      fc (shearB 0 x) + fc (shearB 1 x))
  have hpars2 := sum_star_fourier_mul fc fc
  simp_rw [hH] at hpars
  have hm : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    positivity
  have hleft : (((∑ x, f x * (f (shearA 0 x) + f (shearA 1 x) + f (shearB 0 x) +
      f (shearB 1 x)) : ℝ)) : ℂ) = ∑ x, (starRingEnd ℂ) (fc x) * (fc (shearA 0 x) +
      fc (shearA 1 x) + fc (shearB 0 x) + fc (shearB 1 x)) := by
    simp [hfc]
  have hnormF : ∑ u, ‖F u‖ ^ 2 = (m : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
    have h : ((∑ u, ‖F u‖ ^ 2 : ℝ) : ℂ) = (((m : ℝ) ^ 2 * ∑ x, f x ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [← hF] at hpars2
      have e1 : ∀ u, ((‖F u‖ : ℝ) : ℂ) ^ 2 = (starRingEnd ℂ) (F u) * F u := fun u =>
        (Complex.conj_mul' _).symm
      simp_rw [e1]
      rw [hpars2]
      simp [hfc, sq]
    exact_mod_cast h
  have hbound := fourier_side_le F hF0
  rw [hpars, ← hleft, norm_mul, hnormF] at hbound
  have hnm : ‖((m : ℂ) ^ 2)‖ = (m : ℝ) ^ 2 := by simp
  rw [hnm, Complex.norm_real, Real.norm_eq_abs] at hbound
  nlinarith


/-- `1` if exactly one of `x` and `y` is in `A`, and `0` otherwise. -/
@[expose] def crossInd (A : Finset (Torus m)) (x y : Torus m) : ℝ :=
  if (x ∈ A ↔ y ∈ A) then 0 else 1

private lemma sum_sq_comp (f : Torus m → ℝ) (T : Torus m ≃ Torus m) :
    ∑ x, f (T x) ^ 2 = ∑ x, f x ^ 2 :=
  Fintype.sum_equiv T _ _ fun _ => rfl

private lemma sum_sq_sub (f : Torus m → ℝ) (T : Torus m ≃ Torus m) :
    ∑ x, (f x - f (T x)) ^ 2 = 2 * ∑ x, f x ^ 2 - 2 * ∑ x, f x * f (T x) := by
  have h : ∀ x, (f x - f (T x)) ^ 2 = f x ^ 2 + f (T x) ^ 2 - 2 * (f x * f (T x)) := by
    intro x; ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_sq_comp, ← Finset.mul_sum]
  ring

/-- **The Margulis graph expands.** For every set `A` of points of the torus, at least
`min(|A|, m² - |A|) / 4` of the pairs `(x, Tx)`, for `T` one of `shearA 0`, `shearA 1`,
`shearB 0`, `shearB 1`, have exactly one end in `A`. -/
theorem card_crossing_ge (A : Finset (Torus m)) :
    min (A.card : ℝ) ((m : ℝ) ^ 2 - A.card) ≤
      4 * ∑ x, (crossInd A x (shearA 0 x) + crossInd A x (shearA 1 x) +
        crossInd A x (shearB 0 x) + crossInd A x (shearB 1 x)) := by
  set N : ℝ := (m : ℝ) ^ 2 with hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    positivity
  have hcard : (Fintype.card (Torus m) : ℝ) = N := by
    simp [hN, Fintype.card_prod, ZMod.card, sq]
  set a : ℝ := (A.card : ℝ) with ha
  set μ : ℝ := a / N with hμ
  set ind : Torus m → ℝ := fun x => if x ∈ A then 1 else 0 with hind
  set f : Torus m → ℝ := fun x => ind x - μ with hf
  have hsum_ind : ∑ x, ind x = a := by
    simp [hind, ha]
  have hsum_f : ∑ x, f x = 0 := by
    simp only [hf, Finset.sum_sub_distrib, hsum_ind, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcard, hμ]
    field_simp
    ring
  have hS : ∑ x, f x ^ 2 = a * (N - a) / N := by
    have h : ∀ x, f x ^ 2 = ind x * (1 - 2 * μ) + μ ^ 2 := by
      intro x
      simp only [hf, hind]
      split_ifs <;> ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.sum_mul, hsum_ind, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcard, hμ]
    field_simp
    ring
  have hcross : ∀ x y, crossInd A x y = (f x - f y) ^ 2 := by
    intro x y
    simp only [crossInd, hf, hind]
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy]
    all_goals ring
  have hQ := quadratic_form_le f hsum_f
  have htot : ∑ x, (crossInd A x (shearA 0 x) + crossInd A x (shearA 1 x) +
      crossInd A x (shearB 0 x) + crossInd A x (shearB 1 x)) =
      8 * ∑ x, f x ^ 2 - 2 * ∑ x, f x * (f (shearA 0 x) + f (shearA 1 x) + f (shearB 0 x) +
        f (shearB 1 x)) := by
    simp_rw [hcross, Finset.sum_add_distrib, sum_sq_sub]
    simp_rw [mul_add, Finset.sum_add_distrib]
    ring
  rw [htot]
  have hQ' := (abs_le.mp hQ).2
  have hmin : min a (N - a) ≤ 2 * (a * (N - a) / N) := by
    have ha0 : 0 ≤ a := by positivity
    have haN : a ≤ N := by
      rw [← hcard, ha]
      exact_mod_cast Finset.card_le_univ A
    rw [mul_div_assoc', le_div_iff₀ hNpos]
    rcases le_total a (N - a) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  rw [hS] at hQ'
  linarith

end MinCostFlow.ExplicitExpander
