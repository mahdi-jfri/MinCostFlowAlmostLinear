module

public import MinCostFlow.Expander.Section8Static
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Asymptotic Depth Parameter `chosenL` and `exp(O(log^{23/24}))` Helpers

Defines the Theorem 8.2 depth parameter `chosenL m = ⌈(log (m + 2))^{1/24}⌉` (`δ = 1 / 24`) and
proves the modular `exp(O(log(M + 2)^{23/24}))` absorption bounds used in `Section8Bound.lean` to
absorb `3^{O(L²)}`, `(γ_ℓ γ_c)^{O(L²)}`, `nMax^{1/L}`, and polylogarithmic factors into a single
`exp(C_dyn * log(M + 2)^{23/24})` envelope.
-/

namespace MinCostFlow.Expander

noncomputable section

@[expose] public section

/-- Balancing depth parameter `L(m) = ⌈(log (m + 2))^{1/24}⌉` for Theorem 8.2 (`δ = 1 / 24`,
achieving subpolynomial exponent `a = 23 / 24 < 1` against `γ_ℓ, γ_c ≤ exp(O(log^{7/8} m))`). -/
def chosenL (m : ℕ) : ℕ :=
  Nat.ceil (Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ))

end

private lemma three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith only [h2]
  have hsq : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [sq, ← Real.exp_add]; norm_num
  linarith only [h4, hsq]

public section

lemma one_le_chosenL (m : ℕ) : 1 ≤ chosenL m := by
  have h12 : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := half_le_log_add_two_nat m
  have hpow : (0 : ℝ) < Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith only [h12]) _
  exact Nat.ceil_pos.mpr hpow

lemma chosenL_lower (m : ℕ) : Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) ≤ (chosenL m : ℝ) :=
  Nat.le_ceil _

lemma chosenL_upper (m : ℕ) :
    (chosenL m : ℝ) ≤ 3 * Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) := by
  have h12 : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := half_le_log_add_two_nat m
  have hL_nn : 0 ≤ Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) :=
    Real.rpow_nonneg (by linarith only [h12]) _
  have hlt : (chosenL m : ℝ) < Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) + 1 :=
    Nat.ceil_lt_add_one hL_nn
  have hhalf : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) + 2) ^ (1 / 24 : ℝ) :=
    half_le_log_rpow_nat (by norm_num) (by norm_num) m
  linarith only [hlt, hhalf]

lemma chosenL_le_exp (M : ℕ) :
    (chosenL M : ℝ) ≤ Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
  have h1 : (chosenL M : ℝ) ≤ 6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
    have hU := chosenL_upper M
    have hup := log_rpow_le_two_mul_rpow (a := (1 / 24 : ℝ)) (b := (23 / 24 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) M
    linarith only [hU, hup]
  exact le_trans h1 (by linarith only [Real.add_one_le_exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))])

lemma chosenL_add_one_le_exp (M : ℕ) :
    ((chosenL M : ℝ) + 1) ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ (chosenL M : ℝ) := by exact_mod_cast one_le_chosenL M
  have hL_exp := chosenL_le_exp M
  have h2 : (2 : ℝ) ≤ Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    have h1 := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num) (by norm_num) M
    have h46 : 2 * (2 : ℝ) ≤ 6 := by norm_num
    have hL23 : 0 ≤ Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) :=
      Real.rpow_nonneg (by linarith only [half_le_log_add_two_nat M]) _
    exact le_trans h1 (Real.exp_le_exp.mpr (by nlinarith only [h46, hL23]))
  calc (chosenL M : ℝ) + 1 ≤ 2 * (chosenL M : ℝ) := by linarith only [hL1]
    _ ≤ Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
          Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        mul_le_mul h2 hL_exp (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        rw [← Real.exp_add]; ring_nf

lemma chosenL_mul_log78 (M : ℕ) :
    (chosenL M : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
      6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have hU := chosenL_upper M
  have h78_nn : 0 ≤ Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have hmul : Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) =
      Real.log ((M : ℝ) + 2) ^ (22 / 24 : ℝ) := by
    rw [← Real.rpow_add hL_pos]; norm_num
  have hup := log_rpow_le_two_mul_rpow (a := (22 / 24 : ℝ)) (b := (23 / 24 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) M
  calc (chosenL M : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)
      ≤ (3 * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hU h78_nn
    _ = 3 * (Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        ring
    _ = 3 * Real.log ((M : ℝ) + 2) ^ (22 / 24 : ℝ) := by rw [hmul]
    _ ≤ 3 * (2 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by gcongr
    _ = 6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by ring

lemma chosenL_sq_mul_log78 (M : ℕ) :
    (chosenL M : ℝ) ^ 2 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
      9 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have hU := chosenL_upper M
  have hL_nn : 0 ≤ (chosenL M : ℝ) := Nat.cast_nonneg _
  have hL2 : (chosenL M : ℝ) ^ 2 ≤ 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) := by
    calc (chosenL M : ℝ) ^ 2
        ≤ (3 * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) ^ 2 := pow_le_pow_left₀ hL_nn hU 2
      _ = 9 * (Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) := by
          ring
      _ = 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) := by
          rw [← Real.rpow_add hL_pos]; norm_num
  have h78_nn : 0 ≤ Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have hmul : Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) =
      Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
    rw [← Real.rpow_add hL_pos]; norm_num
  calc (chosenL M : ℝ) ^ 2 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)
      ≤ 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hL2 h78_nn
    _ = 9 * (Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        ring
    _ = 9 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by rw [hmul]

lemma chosenL_sq_le (M : ℕ) :
    (chosenL M : ℝ) ^ 2 ≤ 18 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have hU := chosenL_upper M
  have hL_nn : 0 ≤ (chosenL M : ℝ) := Nat.cast_nonneg _
  have hL2 : (chosenL M : ℝ) ^ 2 ≤ 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) := by
    calc (chosenL M : ℝ) ^ 2
        ≤ (3 * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) ^ 2 := pow_le_pow_left₀ hL_nn hU 2
      _ = 9 * (Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) := by
          ring
      _ = 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) := by
          rw [← Real.rpow_add hL_pos]; norm_num
  have hup := log_rpow_le_two_mul_rpow (a := (2 / 24 : ℝ)) (b := (23 / 24 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) M
  calc (chosenL M : ℝ) ^ 2 ≤ 9 * Real.log ((M : ℝ) + 2) ^ (2 / 24 : ℝ) := hL2
    _ ≤ 9 * (2 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by gcongr
    _ = 18 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by ring

lemma log_div_chosenL_le (M : ℕ) :
    Real.log ((M : ℝ) + 2) / (chosenL M : ℝ) ≤ Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := by
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have h124_pos : 0 < Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have hsplit : Real.log ((M : ℝ) + 2) =
      Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hL_pos]; norm_num
  calc Real.log ((M : ℝ) + 2) / (chosenL M : ℝ)
      ≤ Real.log ((M : ℝ) + 2) / Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) :=
        div_le_div_of_nonneg_left hL_pos.le h124_pos (chosenL_lower M)
    _ = (Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ)) /
          Real.log ((M : ℝ) + 2) ^ (1 / 24 : ℝ) := by
        conv_lhs => arg 1; rw [hsplit]
    _ = Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) :=
        mul_div_cancel_right₀ _ h124_pos.ne'

lemma rpow_23_24_exp_mono {A B : ℝ} (hAB : A ≤ B) (M : ℕ) :
    Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
      Real.exp (B * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) :=
    Real.rpow_nonneg (by linarith only [half_le_log_add_two_nat M]) _
  exact mul_le_mul_of_nonneg_right hAB hL

lemma nRoot_le_exp {C_n r_n : ℝ} (hCn : 1 ≤ C_n) (hrn : 0 ≤ r_n)
    {nMax M : ℕ} (hn : (nMax : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n) :
    ((max nMax 1 : ℕ) : ℝ) ^ (1 / (chosenL M : ℝ)) ≤
      Real.exp ((2 * C_n + r_n) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
  have hM2_ge1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) M]
  have hpow_ge1 : (1 : ℝ) ≤ ((M : ℝ) + 2) ^ r_n := Real.one_le_rpow hM2_ge1 hrn
  have h1_le_rhs : (1 : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n := by nlinarith only [hCn, hpow_ge1]
  have hmax_le : ((max nMax 1 : ℕ) : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n := by
    rcases max_cases nMax 1 with ⟨h, _⟩ | ⟨h, _⟩
    · simp only [h]; exact hn
    · simp only [h]; norm_num; exact h1_le_rhs
  have hL1 : (1 : ℝ) ≤ (chosenL M : ℝ) := by exact_mod_cast one_le_chosenL M
  have hL_pos : (0 : ℝ) < (chosenL M : ℝ) := by linarith only [hL1]
  have hinv_nn : 0 ≤ 1 / (chosenL M : ℝ) := by positivity
  have hinv_le1 : 1 / (chosenL M : ℝ) ≤ 1 := div_le_one_of_le₀ hL1 hL_pos.le
  have hCn_rpow : C_n ^ (1 / (chosenL M : ℝ)) ≤ C_n := by
    calc C_n ^ (1 / (chosenL M : ℝ)) ≤ C_n ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hCn hinv_le1
      _ = C_n := Real.rpow_one C_n
  have hM2_pos : 0 < (M : ℝ) + 2 := by linarith only [hM2_ge1]
  have hrn_rpow : (((M : ℝ) + 2) ^ r_n) ^ (1 / (chosenL M : ℝ)) ≤
      Real.exp (r_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    rw [← Real.rpow_mul hM2_pos.le]
    have hlog_eq : (M : ℝ) + 2 = Real.exp (Real.log ((M : ℝ) + 2)) :=
      (Real.exp_log hM2_pos).symm
    calc ((M : ℝ) + 2) ^ (r_n * (1 / (chosenL M : ℝ)))
        = Real.exp (Real.log ((M : ℝ) + 2)) ^ (r_n * (1 / (chosenL M : ℝ))) := by
            conv_lhs => rw [hlog_eq]
      _ = Real.exp (Real.log ((M : ℝ) + 2) * (r_n * (1 / (chosenL M : ℝ)))) :=
          (Real.exp_mul _ _).symm
      _ = Real.exp (r_n * (Real.log ((M : ℝ) + 2) / (chosenL M : ℝ))) := by
          congr 1; ring
      _ ≤ Real.exp (r_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (log_div_chosenL_le M) hrn
  have hCn_exp : C_n ≤ Real.exp (2 * C_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) (by linarith only [hCn])
      (by norm_num) (by norm_num) M
  calc ((max nMax 1 : ℕ) : ℝ) ^ (1 / (chosenL M : ℝ))
      ≤ (C_n * ((M : ℝ) + 2) ^ r_n) ^ (1 / (chosenL M : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hmax_le hinv_nn
    _ = C_n ^ (1 / (chosenL M : ℝ)) * (((M : ℝ) + 2) ^ r_n) ^ (1 / (chosenL M : ℝ)) :=
        Real.mul_rpow (by linarith only [hCn]) (Real.rpow_nonneg hM2_pos.le _)
    _ ≤ C_n * Real.exp (r_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        mul_le_mul hCn_rpow hrn_rpow (Real.rpow_nonneg (Real.rpow_nonneg hM2_pos.le _) _)
          (by linarith only [hCn])
    _ ≤ Real.exp (2 * C_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
          Real.exp (r_n * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_right hCn_exp (Real.exp_pos _).le
    _ = Real.exp ((2 * C_n + r_n) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        rw [← Real.exp_add]; ring_nf

lemma one_add_log_sum_le {C_n r_n : ℝ} (hCn : 1 ≤ C_n) (hrn : 1 ≤ r_n)
    {nMax m0 M : ℕ} (hm : m0 ≤ M) (hn : (nMax : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n) :
    1 + Real.log ((nMax : ℝ) + (m0 : ℝ) + 2) ≤
      (4 * C_n + r_n + 2) * Real.log ((M : ℝ) + 2) := by
  have hL_half := half_le_log_add_two_nat M
  have h1_le_2log : (1 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) := by linarith only [hL_half]
  have hM2_ge1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) M]
  have hM2_pos : 0 < (M : ℝ) + 2 := by linarith only [hM2_ge1]
  have hm_le : (m0 : ℝ) + 2 ≤ C_n * ((M : ℝ) + 2) ^ r_n := by
    have hm1 : (m0 : ℝ) + 2 ≤ (M : ℝ) + 2 := by
      have : (m0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
      linarith only [this]
    have hpow : (M : ℝ) + 2 ≤ ((M : ℝ) + 2) ^ r_n := by
      calc (M : ℝ) + 2 = ((M : ℝ) + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((M : ℝ) + 2) ^ r_n := Real.rpow_le_rpow_of_exponent_le hM2_ge1 hrn
    have hrpow_nn : 0 ≤ ((M : ℝ) + 2) ^ r_n := Real.rpow_nonneg hM2_pos.le _
    calc (m0 : ℝ) + 2 ≤ ((M : ℝ) + 2) ^ r_n := le_trans hm1 hpow
      _ ≤ C_n * ((M : ℝ) + 2) ^ r_n := by nlinarith only [hCn, hrpow_nn]
  have hsum : (nMax : ℝ) + (m0 : ℝ) + 2 ≤ 2 * C_n * ((M : ℝ) + 2) ^ r_n := by
    linarith only [hn, hm_le]
  have hlog_pos : 0 < (nMax : ℝ) + (m0 : ℝ) + 2 := by
    linarith only [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) m0]
  have hlog1 : Real.log ((nMax : ℝ) + (m0 : ℝ) + 2) ≤
      Real.log (2 * C_n) + r_n * Real.log ((M : ℝ) + 2) := by
    calc Real.log ((nMax : ℝ) + (m0 : ℝ) + 2)
        ≤ Real.log ((2 * C_n) * ((M : ℝ) + 2) ^ r_n) := by
          apply Real.log_le_log hlog_pos
          linarith only [hsum]
      _ = Real.log (2 * C_n) + Real.log (((M : ℝ) + 2) ^ r_n) :=
          Real.log_mul (by linarith only [hCn]) (Real.rpow_pos_of_pos hM2_pos _).ne'
      _ = Real.log (2 * C_n) + r_n * Real.log ((M : ℝ) + 2) := by
          rw [Real.log_rpow hM2_pos]
  have hlog2Cn : Real.log (2 * C_n) ≤ 4 * C_n * Real.log ((M : ℝ) + 2) := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith only [hCn] : 0 < 2 * C_n)
    have h2 : Real.log (2 * C_n) ≤ 2 * C_n := by linarith only [h1]
    calc Real.log (2 * C_n) ≤ 2 * C_n := h2
      _ = 2 * C_n * 1 := by ring
      _ ≤ 2 * C_n * (2 * Real.log ((M : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_left h1_le_2log (by linarith only [hCn])
      _ = 4 * C_n * Real.log ((M : ℝ) + 2) := by ring
  linarith only [h1_le_2log, hlog1, hlog2Cn]

lemma log_linear_le_mul_log {A C_n r_n : ℝ} (hA : 0 ≤ A) (hCn : 1 ≤ C_n) (hrn : 1 ≤ r_n)
    {X : ℝ} (hX0 : 0 ≤ X) {M nMax : ℕ}
    (hXM : X ≤ Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2))
    (hn : (nMax : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n) :
    Real.log (6 * X + 10) ≤ (2 * A + 64 * C_n + r_n) * Real.log ((M : ℝ) + 2) := by
  have hL_half := half_le_log_add_two_nat M
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [hL_half]
  have h1_le_2log : (1 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) := by linarith only [hL_half]
  have hL23_nn : 0 ≤ Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have hexp_ge1 : (1 : ℝ) ≤ Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    Real.one_le_exp (mul_nonneg hA hL23_nn)
  have hn2_ge1 : (1 : ℝ) ≤ (nMax : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) nMax]
  have hprod_ge1 : (1 : ℝ) ≤ Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2) := by
    nlinarith only [hexp_ge1, hn2_ge1]
  have hM2_ge1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) M]
  have hM2_pos : 0 < (M : ℝ) + 2 := by linarith only [hM2_ge1]
  have hn2_le : (nMax : ℝ) + 2 ≤ 2 * C_n * ((M : ℝ) + 2) ^ r_n := by
    have hM2_r : (M : ℝ) + 2 ≤ ((M : ℝ) + 2) ^ r_n := by
      calc (M : ℝ) + 2 = ((M : ℝ) + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((M : ℝ) + 2) ^ r_n := Real.rpow_le_rpow_of_exponent_le hM2_ge1 hrn
    have h2 : (2 : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n := by
      have h2le : (2 : ℝ) ≤ (M : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) M]
      nlinarith only [hCn, h2le, hM2_r]
    linarith only [hn, h2]
  have h6X10 : 6 * X + 10 ≤
      (32 * C_n) * Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((M : ℝ) + 2) ^ r_n := by
    have h1 : 6 * X + 10 ≤
        16 * (Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2)) := by
      linarith only [hXM, hprod_ge1]
    have h2 : 16 * (Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2)) ≤
        16 * (Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * (2 * C_n * ((M : ℝ) + 2) ^ r_n)) := by
      gcongr
    linarith only [h1, h2]
  have hlog_pos : 0 < 6 * X + 10 := by linarith only [hX0]
  have hlog1 : Real.log (6 * X + 10) ≤
      Real.log (32 * C_n) + A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) +
        r_n * Real.log ((M : ℝ) + 2) := by
    calc Real.log (6 * X + 10)
        ≤ Real.log ((32 * C_n) * Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            ((M : ℝ) + 2) ^ r_n) := Real.log_le_log hlog_pos h6X10
      _ = Real.log ((32 * C_n) * Real.exp (A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) +
            Real.log (((M : ℝ) + 2) ^ r_n) :=
          Real.log_mul (by positivity) (Real.rpow_pos_of_pos hM2_pos _).ne'
      _ = Real.log (32 * C_n) + A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) +
            r_n * Real.log ((M : ℝ) + 2) := by
          rw [Real.log_mul (by linarith only [hCn]) (Real.exp_pos _).ne', Real.log_exp,
            Real.log_rpow hM2_pos]
  have hlog32 : Real.log (32 * C_n) ≤ 64 * C_n * Real.log ((M : ℝ) + 2) := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith only [hCn] : 0 < 32 * C_n)
    have h2 : Real.log (32 * C_n) ≤ 32 * C_n := by linarith only [h1]
    calc Real.log (32 * C_n) ≤ 32 * C_n := h2
      _ = 32 * C_n * 1 := by ring
      _ ≤ 32 * C_n * (2 * Real.log ((M : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_left h1_le_2log (by linarith only [hCn])
      _ = 64 * C_n * Real.log ((M : ℝ) + 2) := by ring
  have h23_le : Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) := by
    simpa [Real.rpow_one] using
      log_rpow_le_two_mul_rpow (a := (23 / 24 : ℝ)) (b := (1 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) M
  have hA23 : A * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) ≤ 2 * A * Real.log ((M : ℝ) + 2) := by
    have := mul_le_mul_of_nonneg_left h23_le hA
    linarith only [this]
  linarith only [hlog1, hlog32, hA23]

lemma exp_gamma_pow_L_bounds {C_γ γ_ℓ γ_c : ℝ}
    (hCγ : 0 < C_γ) (hγℓ_nn : 0 ≤ γ_ℓ) (hγc_nn : 0 ≤ γ_c) (M : ℕ)
    (hγℓ : γ_ℓ ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hγc : γ_c ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    let L := chosenL M
    (γ_ℓ ≤ Real.exp (2 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) ∧
    ((3 : ℝ) ^ L * γ_ℓ ^ (L + 1) ≤ Real.exp ((36 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) ∧
    ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2) * γ_ℓ ^ (L * (L + 1) / 2) * γ_c ^ (L + 1) ≤
      Real.exp ((108 + 21 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) ∧
    ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
        γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) ≤
      Real.exp ((216 + 57 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) := by
  intro L
  have hL1 : 1 ≤ L := one_le_chosenL M
  have hL_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have h78_23 : Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ) :=
    log_rpow_le_two_mul_rpow (a := (7 / 8 : ℝ)) (b := (23 / 24 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) M
  have hγℓ_23 : γ_ℓ ≤ Real.exp (2 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    refine le_trans hγℓ (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_left h78_23 hCγ.le
    linarith only [this]
  have hL_mul := chosenL_mul_log78 M
  have hL_sq_mul := chosenL_sq_mul_log78 M
  have hL_sq := chosenL_sq_le M
  have hpow_le_exp {x : ℝ} {k : ℕ} (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)))
      {c : ℝ} (hc : 0 ≤ c) (hk : (k : ℝ) ≤ c * (L : ℝ)) :
      x ^ k ≤ Real.exp ((6 * c * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    calc x ^ k ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ^ k :=
          pow_le_pow_left₀ hx0 hx k
      _ = Real.exp ((k : ℝ) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((6 * c * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have h1 : (k : ℝ) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
              (c * (L : ℝ)) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right hk
            exact mul_nonneg hCγ.le (Real.rpow_nonneg hL_pos.le _)
          have h2 : (c * (L : ℝ)) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) =
              c * C_γ * ((L : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by ring
          have h3 : c * C_γ * ((L : ℝ) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
              c * C_γ * (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hL_mul (mul_nonneg hc hCγ.le)
          linarith only [h1, h2, h3]
  have hpow_sq_le_exp {x : ℝ} {k : ℕ} (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)))
      {c : ℝ} (hc : 0 ≤ c) (hk : (k : ℝ) ≤ c * (L : ℝ) ^ 2) :
      x ^ k ≤ Real.exp ((9 * c * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    calc x ^ k ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ^ k :=
          pow_le_pow_left₀ hx0 hx k
      _ = Real.exp ((k : ℝ) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((9 * c * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have h1 : (k : ℝ) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
              (c * (L : ℝ) ^ 2) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right hk
            exact mul_nonneg hCγ.le (Real.rpow_nonneg hL_pos.le _)
          have h2 : (c * (L : ℝ) ^ 2) * (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) =
              c * C_γ * ((L : ℝ) ^ 2 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by ring
          have h3 : c * C_γ * ((L : ℝ) ^ 2 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
              c * C_γ * (9 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hL_sq_mul (mul_nonneg hc hCγ.le)
          linarith only [h1, h2, h3]
  have h3pow {k : ℕ} {c : ℝ} (hc : 0 ≤ c) (hk : (k : ℝ) ≤ c * (L : ℝ) ^ 2) :
      (3 : ℝ) ^ k ≤ Real.exp ((36 * c) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    calc (3 : ℝ) ^ k ≤ Real.exp 2 ^ k := pow_le_pow_left₀ (by norm_num) three_le_exp_two k
      _ = Real.exp ((k : ℝ) * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((36 * c) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have h1 : (k : ℝ) * 2 ≤ (c * (L : ℝ) ^ 2) * 2 := by nlinarith only [hk]
          have h2 : (c * (L : ℝ) ^ 2) * 2 ≤ (c * (18 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) * 2 := by
            nlinarith only [hc, hL_sq]
          linarith only [h1, h2]
  have h1r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hL_le_L2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [h1r]
  have h1_le_L2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [h1r]
  have hL_add1 : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by push_cast; linarith only [h1r]
  have hnat_div1 : L * (L + 1) / 2 ≤ L ^ 2 := by
    apply Nat.div_le_of_le_mul; nlinarith only [hL1]
  have hnat_div2 : (L + 1) * (L + 2) / 2 ≤ 3 * L ^ 2 := by
    apply Nat.div_le_of_le_mul; nlinarith only [hL1]
  have hk_div1 : ((L * (L + 1) / 2 : ℕ) : ℝ) ≤ 1 * (L : ℝ) ^ 2 := by
    have h : ((L * (L + 1) / 2 : ℕ) : ℝ) ≤ ((L ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat_div1
    push_cast at h; linarith only [h]
  have hk_div2 : (((L + 1) * (L + 2) / 2 : ℕ) : ℝ) ≤ 3 * (L : ℝ) ^ 2 := by
    have h : (((L + 1) * (L + 2) / 2 : ℕ) : ℝ) ≤ ((3 * L ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat_div2
    push_cast at h; exact h
  have hk_div2_p2 : (((L + 1) * (L + 2) / 2 + 2 : ℕ) : ℝ) ≤ 5 * (L : ℝ) ^ 2 := by
    push_cast; linarith only [hk_div2, h1_le_L2]
  have hk_div2_full : (((L + 1) * (L + 2) / 2 + L + 2 : ℕ) : ℝ) ≤ 6 * (L : ℝ) ^ 2 := by
    push_cast; linarith only [hk_div2, hL_le_L2, h1_le_L2]
  have hγℓ_L1 : γ_ℓ ^ (L + 1) ≤ Real.exp ((12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show 6 * (2 : ℝ) * C_γ = 12 * C_γ by ring] using
      hpow_le_exp hγℓ_nn hγℓ (by norm_num) hL_add1
  have hγc_L1 : γ_c ^ (L + 1) ≤ Real.exp ((12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show 6 * (2 : ℝ) * C_γ = 12 * C_γ by ring] using
      hpow_le_exp hγc_nn hγc (by norm_num) hL_add1
  have h3_L : (3 : ℝ) ^ L ≤ Real.exp (36 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa using h3pow (k := L) (c := 1) (by norm_num) (by linarith only [hL_le_L2])
  have h3_div2 : (3 : ℝ) ^ ((L + 1) * (L + 2) / 2) ≤
      Real.exp (108 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show (36 * (3 : ℝ)) = 108 by norm_num] using
      h3pow (k := (L + 1) * (L + 2) / 2) (c := 3) (by norm_num) hk_div2
  have h3_full : (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) ≤
      Real.exp (216 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show (36 * (6 : ℝ)) = 216 by norm_num] using
      h3pow (k := (L + 1) * (L + 2) / 2 + L + 2) (c := 6) (by norm_num) hk_div2_full
  have hγℓ_div1 : γ_ℓ ^ (L * (L + 1) / 2) ≤
      Real.exp ((9 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show 9 * (1 : ℝ) * C_γ = 9 * C_γ by ring] using
      hpow_sq_le_exp hγℓ_nn hγℓ (by norm_num) hk_div1
  have hγℓ_div2_p2 : γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) ≤
      Real.exp ((45 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    simpa [show 9 * (5 : ℝ) * C_γ = 45 * C_γ by ring] using
      hpow_sq_le_exp hγℓ_nn hγℓ (by norm_num) hk_div2_p2
  refine ⟨hγℓ_23, ?_, ?_, ?_⟩
  · calc (3 : ℝ) ^ L * γ_ℓ ^ (L + 1)
        ≤ Real.exp (36 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp ((12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
          mul_le_mul h3_L hγℓ_L1 (pow_nonneg hγℓ_nn _) (by positivity)
      _ = Real.exp ((36 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
  · calc (3 : ℝ) ^ ((L + 1) * (L + 2) / 2) * γ_ℓ ^ (L * (L + 1) / 2) * γ_c ^ (L + 1)
        ≤ Real.exp (108 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp ((9 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp ((12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          have h12 := mul_le_mul h3_div2 hγℓ_div1 (pow_nonneg hγℓ_nn _) (by positivity)
          exact mul_le_mul h12 hγc_L1 (pow_nonneg hγc_nn _) (by positivity)
      _ = Real.exp ((108 + 21 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  · calc (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * γ_c ^ (L + 1) *
          γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
        ≤ Real.exp (216 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp ((12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp ((45 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          have h12 := mul_le_mul h3_full hγc_L1 (pow_nonneg hγc_nn _) (by positivity)
          exact mul_le_mul h12 hγℓ_div2_p2 (pow_nonneg hγℓ_nn _) (by positivity)
      _ = Real.exp ((216 + 57 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf

end

end

end MinCostFlow.Expander
