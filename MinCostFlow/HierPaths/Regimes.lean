module

public import MinCostFlow.HierPaths.ParamsExp
public import MinCostFlow.Expander.SpannerToolImplProg

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `Γ` is subpolynomial where the chain uses it

The chain calls the path data structure at two kinds of scale (`ConsumerSubpolyAtRegimes`,
`Expander/SpannerToolImplProg.lean`): at the decomposition scale `d ≤ C₁ · subpolyB1 C₀ M + 1`,
where `subpolyB1 C₀ M = exp(C₀ L^{2/3} log(L + 2))` with `L = log(M + 2)`, and at a constant
`d`. At both it needs `f d M ≤ exp(C L^{7/8})`. This file proves this for `f = Γ`
(`gammaHP_at_regimes`) and for the constant `1` (`one_at_regimes`).

The proof shows `log Γ = O(log(2 + d) + X^{2/3} log(X + 2))`, in the form
of `ParamsExp.lean`: `Γ ≤ (1 + (2 + d)^4)^2 · 2^{gammaExp a M}` with
`gammaExp a M ≤ (36 + 96 a) s^21` and `s^24 ≤ 2^24 X` for `s = ⌈X^{1/24}⌉`. Since `X ≤ 10 L`,
`s^21 = (s^24)^{7/8} ≤ 2^24 · 10 · L^{7/8}`, so `2^{gammaExp a M} ≤ exp(C L^{7/8})`
(`two_pow_gammaExp_le_exp`). At the decomposition scale `2 + d ≤ (C₁ + 3) exp(C₀ L^{2/3} log(L + 2))`,
and `L^{2/3} log(L + 2) ≤ 25 L^{7/8}`, which bounds the factor of `d`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Expander

private lemma log_le_rpow_div (u p : ℝ) (hu : 0 < u) (hp : 0 < p) :
    Real.log u ≤ u ^ p / p := by
  have h1 : Real.log (u ^ p) ≤ u ^ p - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu p)
  have h2 : Real.log (u ^ p) = p * Real.log u := Real.log_rpow hu p
  have h3 : p * Real.log u ≤ u ^ p := by linarith
  exact (le_div_iff₀ hp).mpr (by linarith)

/-- `L^{2/3} log(L + 2) ≤ 25 L^{7/8}` for `L ≥ 1/2`, from `log(L + 2) ≤ 25 L^{5/24}`. -/
lemma rpow_two_thirds_mul_log_le {L : ℝ} (hL : (1 / 2 : ℝ) ≤ L) :
    L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤ 25 * L ^ (7 / 8 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hll_le : Real.log (L + 2) ≤ 25 * L ^ (5 / 24 : ℝ) := by
    have hL2_pos : 0 < L + 2 := by linarith
    have h1 := log_le_rpow_div (L + 2) (5 / 24 : ℝ) hL2_pos (by norm_num)
    have hL2_le : L + 2 ≤ 5 * L := by linarith
    have h2 : (L + 2) ^ (5 / 24 : ℝ) ≤ (5 * L) ^ (5 / 24 : ℝ) :=
      Real.rpow_le_rpow hL2_pos.le hL2_le (by norm_num)
    have h3 : (5 * L) ^ (5 / 24 : ℝ) ≤ 5 * L ^ (5 / 24 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hLpos.le]
      have h5 : (5 : ℝ) ^ (5 / 24 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      nlinarith [Real.rpow_nonneg hLpos.le (5 / 24 : ℝ)]
    have h4 : (L + 2) ^ (5 / 24 : ℝ) / (5 / 24 : ℝ) ≤ 5 * (L + 2) ^ (5 / 24 : ℝ) := by
      have : (0 : ℝ) ≤ (L + 2) ^ (5 / 24 : ℝ) := Real.rpow_nonneg hL2_pos.le _
      linarith
    have h5 := le_trans h1 h4
    linarith [le_trans h2 h3]
  have hmul := mul_le_mul_of_nonneg_left hll_le (Real.rpow_nonneg hLpos.le (2 / 3 : ℝ))
  have hadd : L ^ (2 / 3 : ℝ) * L ^ (5 / 24 : ℝ) = L ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  linarith [show L ^ (2 / 3 : ℝ) * (25 * L ^ (5 / 24 : ℝ)) =
    25 * (L ^ (2 / 3 : ℝ) * L ^ (5 / 24 : ℝ)) by ring]

/-- `X ≤ 10 log(M + 2)`: from `2^X ≤ 16 (M + 1)`, `X log 2 ≤ log 16 + log(M + 2)`. -/
lemma bigX_le_log (M : ℕ) : (bigX M : ℝ) ≤ 10 * Real.log ((M : ℝ) + 2) := by
  have hL := half_le_log_add_two_nat M
  have hpow : ((2 : ℝ) ^ bigX M) ≤ 16 * ((M : ℝ) + 2) := by
    have := two_pow_bigX_le M
    have h : ((2 ^ bigX M : ℕ) : ℝ) ≤ ((16 * (M + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    linarith
  have hM2 : (0 : ℝ) < (M : ℝ) + 2 := by positivity
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) hM2.ne'] at hlog
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  rw [h16] at hlog
  have hX : ((bigX M : ℝ) - 4) * Real.log 2 ≤ Real.log ((M : ℝ) + 2) := by linarith
  have h15 : (bigX M : ℝ) - 4 ≤ 1.5 * Real.log ((M : ℝ) + 2) := by
    by_contra hc
    push Not at hc
    have h1 : 1.5 * Real.log ((M : ℝ) + 2) * Real.log 2 < ((bigX M : ℝ) - 4) * Real.log 2 :=
      mul_lt_mul_of_pos_right hc (by linarith)
    nlinarith
  linarith

/-- `1/2 ≤ log(M + 2)^{7/8}`. -/
lemma half_le_log_rpow78 (M : ℕ) : (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) :=
  half_le_log_rpow_nat (by norm_num) (by norm_num) M

/-- `2^{gammaExp a M} ≤ exp(C log(M + 2)^{7/8})`. -/
theorem two_pow_gammaExp_le_exp (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      ((2 : ℝ) ^ gammaExp a M) ≤ Real.exp (C * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  set c : ℝ := 36 + 96 * (a : ℝ)
  have hc : 0 < c := by positivity
  set K : ℝ := 2 ^ 24 * 10
  refine ⟨Real.log 2 * c * K, by positivity, fun M => ?_⟩
  set L := Real.log ((M : ℝ) + 2)
  have hL := half_le_log_add_two_nat M
  have hLpos : 0 < L := by linarith
  set s := ceilRoot 23 (bigX M)
  have hs24 : ((s : ℝ) ^ 24) ≤ K * L := by
    have h1 : ((s ^ 24 : ℕ) : ℝ) ≤ ((2 ^ 24 * bigX M : ℕ) : ℝ) := by exact_mod_cast root24_pow_le M
    push_cast at h1
    have h2 := bigX_le_log M
    dsimp only [K]
    nlinarith
  have hs21 : ((s : ℝ) ^ 21) ≤ K * L ^ (7 / 8 : ℝ) := by
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    have heq : ((s : ℝ) ^ 21) = ((s : ℝ) ^ 24) ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hsnn]; norm_num
    rw [heq]
    calc ((s : ℝ) ^ 24) ^ (7 / 8 : ℝ) ≤ (K * L) ^ (7 / 8 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hs24 (by norm_num)
      _ = K ^ (7 / 8 : ℝ) * L ^ (7 / 8 : ℝ) := Real.mul_rpow (by positivity) hLpos.le
      _ ≤ K * L ^ (7 / 8 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
          calc K ^ (7 / 8 : ℝ) ≤ K ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num [K]) (by norm_num)
            _ = K := Real.rpow_one K
  have hE : (gammaExp a M : ℝ) ≤ c * (s : ℝ) ^ 21 := by
    have h := gammaExp_le_root a M
    have h' : ((gammaExp a M : ℕ) : ℝ) ≤ (((36 + 96 * a) * s ^ 21 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ((2 : ℝ) ^ gammaExp a M) = Real.exp (Real.log 2 * (gammaExp a M : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log 2 * c * K * L ^ (7 / 8 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h1 : (gammaExp a M : ℝ) ≤ c * (K * L ^ (7 / 8 : ℝ)) :=
          le_trans hE (mul_le_mul_of_nonneg_left hs21 hc.le)
        calc Real.log 2 * (gammaExp a M : ℝ) ≤ Real.log 2 * (c * (K * L ^ (7 / 8 : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 hl2.le
          _ = Real.log 2 * c * K * L ^ (7 / 8 : ℝ) := by ring

/-- A constant `K ≥ 1` is at most `exp(2 log K · log(M + 2)^{7/8})`. -/
lemma const_le_exp_rpow78 {K : ℝ} (hK : 1 ≤ K) (M : ℕ) :
    K ≤ Real.exp (2 * Real.log K * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hh := half_le_log_rpow78 M
  calc K = Real.exp (Real.log K) := (Real.exp_log (by linarith)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- `Γ` is at most the factor of `d` times `exp(C log(M + 2)^{7/8})`. -/
lemma gammaHP_le_factor_mul_exp (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d M : ℕ,
      (gammaHP a d M : ℝ) ≤
        ((1 + (2 + d) ^ 4) ^ 2 : ℝ) * Real.exp (C * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := two_pow_gammaExp_le_exp a
  refine ⟨C, hC, fun d M => ?_⟩
  have h1 : (gammaHP a d M : ℝ) ≤ (((1 + (2 + d) ^ 4) ^ 2 * 2 ^ gammaExp a M : ℕ) : ℝ) := by
    exact_mod_cast gammaHP_le_two_pow a d M
  push_cast at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left (h M) (by positivity))

/-- `Γ ≤ exp(C log(M + 2)^{7/8})` at the decomposition scale `d ≤ C₁ · subpolyB1 C₀ M + 1`. -/
theorem gammaHP_at_decomposition (a : ℕ) (C₀ C₁ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M d : ℕ, (d : ℝ) ≤ C₁ * subpolyB1 C₀ M + 1 →
      (gammaHP a d M : ℝ) ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C, hC, hΓ⟩ := gammaHP_le_factor_mul_exp a
  set K : ℝ := 4 * (C₁ + 3) ^ 8
  have hK : 1 ≤ K := by
    have : (1 : ℝ) ≤ (C₁ + 3) ^ 8 := one_le_pow₀ (by linarith)
    dsimp only [K]; linarith
  refine ⟨2 * Real.log K + 200 * C₀ + C, by
    have := Real.log_nonneg hK; positivity, fun M d hd => ?_⟩
  set L := Real.log ((M : ℝ) + 2)
  have hL := half_le_log_add_two_nat M
  have hLpos : 0 < L := by linarith
  set P := L ^ (7 / 8 : ℝ)
  have hPnn : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  set S := subpolyB1 C₀ M
  have hS1 : 1 ≤ S := by
    dsimp only [S, subpolyB1]
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ L + 2 by linarith)
    have h2 := Real.rpow_nonneg hLpos.le (2 / 3 : ℝ)
    exact Real.one_le_exp (mul_nonneg (mul_nonneg hC₀.le h2) h1)
  have hS : S ≤ Real.exp (25 * C₀ * P) := by
    dsimp only [S, subpolyB1]
    apply Real.exp_le_exp.mpr
    have h := rpow_two_thirds_mul_log_le hL
    calc C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) = C₀ * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          ring
      _ ≤ C₀ * (25 * P) := mul_le_mul_of_nonneg_left h hC₀.le
      _ = 25 * C₀ * P := by ring
  have h2d : (2 + d : ℝ) ≤ (C₁ + 3) * Real.exp (25 * C₀ * P) := by
    have hE1 : 1 ≤ Real.exp (25 * C₀ * P) := Real.one_le_exp (by positivity)
    have : C₁ * S ≤ C₁ * Real.exp (25 * C₀ * P) := mul_le_mul_of_nonneg_left hS hC₁.le
    nlinarith
  have hD : ((1 + (2 + d) ^ 4) ^ 2 : ℝ) ≤ K * Real.exp (200 * C₀ * P) := by
    have h4 : (1 : ℝ) ≤ (2 + d : ℝ) ^ 4 :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    have hy : ((1 + (2 + d) ^ 4) ^ 2 : ℝ) ≤ 4 * (2 + d : ℝ) ^ 8 := by nlinarith
    have h8 : (2 + d : ℝ) ^ 8 ≤ ((C₁ + 3) * Real.exp (25 * C₀ * P)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) h2d 8
    have hexp : (Real.exp (25 * C₀ * P)) ^ 8 = Real.exp (200 * C₀ * P) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [mul_pow, hexp] at h8
    dsimp only [K]
    nlinarith
  have hKe := const_le_exp_rpow78 hK M
  calc (gammaHP a d M : ℝ) ≤ ((1 + (2 + d) ^ 4) ^ 2 : ℝ) * Real.exp (C * P) := hΓ d M
    _ ≤ (K * Real.exp (200 * C₀ * P)) * Real.exp (C * P) :=
        mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
    _ ≤ (Real.exp (2 * Real.log K * P) * Real.exp (200 * C₀ * P)) * Real.exp (C * P) := by
        gcongr
    _ = Real.exp ((2 * Real.log K + 200 * C₀ + C) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- `Γ ≤ exp(C log(M + 2)^{7/8})` for `d` at most a constant `D₀`. -/
theorem gammaHP_at_const (a D₀ : ℕ) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ d M : ℕ, d ≤ D₀ →
      (gammaHP a d M : ℝ) ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C, hC, hΓ⟩ := gammaHP_le_factor_mul_exp a
  set K : ℝ := ((1 + (2 + D₀) ^ 4) ^ 2 : ℝ)
  have hK : 1 ≤ K := by
    have : (1 : ℝ) ≤ 1 + (2 + D₀ : ℝ) ^ 4 := by have := pow_nonneg (show (0:ℝ) ≤ 2 + D₀ by positivity) 4; linarith
    exact one_le_pow₀ this
  refine ⟨2 * Real.log K + C, by have := Real.log_nonneg hK; positivity, fun d M hd => ?_⟩
  set P := Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)
  have hD : ((1 + (2 + d) ^ 4) ^ 2 : ℝ) ≤ K := by
    have hd' : (d : ℝ) ≤ D₀ := by exact_mod_cast hd
    dsimp only [K]
    gcongr
  calc (gammaHP a d M : ℝ) ≤ ((1 + (2 + d) ^ 4) ^ 2 : ℝ) * Real.exp (C * P) := hΓ d M
    _ ≤ Real.exp (2 * Real.log K * P) * Real.exp (C * P) := by
        gcongr
        exact le_trans hD (const_le_exp_rpow78 hK M)
    _ = Real.exp ((2 * Real.log K + C) * P) := by rw [← Real.exp_add]; ring_nf

/-- `Γ` meets the two regime bounds that the chain needs of a path data structure parameter. -/
theorem gammaHP_at_regimes (a : ℕ) : ConsumerSubpolyAtRegimes (gammaHP a) := by
  refine ⟨fun C₀ C₁ hC₀ hC₁ => ?_, ?_⟩
  · obtain ⟨C_p, hCp, h⟩ := gammaHP_at_decomposition a C₀ C₁ hC₀ hC₁
    exact ⟨C_p, hCp, fun M d _ hd => h M d hd⟩
  · obtain ⟨C_p, hCp, h⟩ := gammaHP_at_const a (Nat.ceil (1 / constructExpanderImpl.φ_Const))
    exact ⟨C_p, hCp, fun d M _ hd => h d M hd⟩

/-- The constant `1` (the deletion factor `gDel`) meets the two regime bounds. -/
theorem one_at_regimes : ConsumerSubpolyAtRegimes (fun _ _ => 1) := by
  have h : ∀ M : ℕ, ((1 : ℕ) : ℝ) ≤ Real.exp (1 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
    intro M
    have := half_le_log_rpow78 M
    push_cast
    exact Real.one_le_exp (by linarith)
  exact ⟨fun _ _ _ _ => ⟨1, one_pos, fun M _ _ _ => h M⟩, ⟨1, one_pos, fun _ M _ _ => h M⟩⟩

end MinCostFlow.HierPaths
