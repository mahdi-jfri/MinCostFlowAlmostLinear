module

public import MinCostFlow.Expander.DecomposeLevelProg

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base Bounds & Multi-Level Invariants for `DecomposeImpl`

Pure analytical, word-size, arena-length, cost, address-layout, and multi-level
graph-decomposition lemmas supporting `DecomposeProgHelpers` and `DecomposeProg`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section

/-! ## 1. Pure Numerical & Subpolynomial Bounds -/

lemma natLog2_add_one_le_self' {k : ℕ} (hk : 1 ≤ k) : Nat.log 2 k + 1 ≤ k := by
  have h1 : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  have h2 : Nat.log 2 k + 1 ≤ 2 ^ Nat.log 2 k := by
    induction Nat.log 2 k with
    | zero => simp
    | succ t ih =>
      have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
      rw [Nat.pow_succ]; omega
  exact le_trans h2 h1

lemma two_pow_ell_mul_n_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    2 ^ (Nat.log 2 (m / n) + 1) * n ≤ 2 * m := by
  have hdiv_pos : 1 ≤ m / n := Nat.div_pos (le_of_lt hnm) hn
  have hpow : 2 ^ Nat.log 2 (m / n) ≤ m / n := Nat.pow_log_le_self 2 (by omega)
  have hmul : 2 ^ Nat.log 2 (m / n) * n ≤ m :=
    le_trans (Nat.mul_le_mul_right n hpow) (Nat.div_mul_le_self m n)
  calc 2 ^ (Nat.log 2 (m / n) + 1) * n
      = 2 * (2 ^ Nat.log 2 (m / n) * n) := by rw [pow_succ']; ring
    _ ≤ 2 * m := by omega

lemma half_lt_real_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have h := Real.log_lt_log (Real.exp_pos _) hexp_half
  rwa [Real.log_exp] at h

lemma real_log_two_lt_one : Real.log 2 < 1 := by
  have h2e : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h := Real.log_lt_log (by norm_num) h2e
  rwa [Real.log_exp] at h

lemma rOf_le_cr_log_of_thr {cr : ℝ} (hcr : 0 < cr) {m : ℕ} (hm : thresholdB1 cr ≤ m) :
    (rOf m : ℝ) ≤ cr * Real.log (m : ℝ) :=
  (rOf_le_cr_log hcr hm).2

lemma one_le_subpolyB1 {C : ℝ} (hC : 0 ≤ C) (m : ℕ) : 1 ≤ subpolyB1 C m := by
  unfold subpolyB1
  have hm : (1 : ℝ) < (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hL : 0 ≤ Real.log ((m : ℝ) + 2) := (Real.log_pos hm).le
  have hLL : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) :=
    (Real.log_pos (by linarith)).le
  exact Real.one_le_exp (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hL _)) hLL)

lemma subpolyB1_mono_C {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) (m : ℕ) :
    subpolyB1 C₁ m ≤ subpolyB1 C₂ m := by
  unfold subpolyB1
  apply Real.exp_le_exp.mpr
  have hm : (1 : ℝ) < (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hL : 0 ≤ Real.log ((m : ℝ) + 2) := (Real.log_pos hm).le
  have hLL : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) :=
    (Real.log_pos (by linarith)).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL _)) hLL

lemma subpolyB1_mul (C₁ C₂ : ℝ) (m : ℕ) :
    subpolyB1 C₁ m * subpolyB1 C₂ m = subpolyB1 (C₁ + C₂) m := by
  unfold subpolyB1
  rw [← Real.exp_add]
  congr 1; ring

lemma subpolyB1_sq (C : ℝ) (m : ℕ) :
    subpolyB1 C m ^ 2 = subpolyB1 (2 * C) m := by
  rw [sq, subpolyB1_mul, two_mul]

lemma real_log_add_two_le_sb (m : ℕ) :
    Real.log ((m : ℝ) + 2) ≤ 6 * subpolyB1 2 m := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hL_pos : 0 < Real.log ((m : ℝ) + 2) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (le_trans half_lt_real_log_two.le (Real.log_le_log (by norm_num) hm2))
  have hLL_gt : (1 / 2 : ℝ) < Real.log (Real.log ((m : ℝ) + 2) + 2) :=
    lt_of_lt_of_le half_lt_real_log_two
      (Real.log_le_log (by norm_num) (by linarith))
  let u := Real.log ((m : ℝ) + 2) ^ (1 / 3 : ℝ)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hL_pos _
  have hu3 : u ^ 3 = Real.log ((m : ℝ) + 2) := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
    norm_num
  have hu2 : u ^ 2 = Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
    norm_num
  by_cases hu1 : u ≤ 1
  · have h3_1 : Real.log ((m : ℝ) + 2) ≤ 1 := by
      rw [← hu3]; exact pow_le_one₀ hu_pos.le hu1
    have hsb := one_le_subpolyB1 (by norm_num : (0 : ℝ) ≤ 2) m
    linarith
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have hu_le_2 : u ≤ 2 * u ^ 2 * Real.log (Real.log ((m : ℝ) + 2) + 2) := by
      have h1 : u ≤ u ^ 2 := by nlinarith
      have h2 : u ^ 2 * 1 ≤ u ^ 2 * (2 * Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
        have : 0 ≤ u ^ 2 := sq_nonneg u
        nlinarith
      linarith
    have hfac : u ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) ≤ Real.exp u :=
      Real.pow_div_factorial_le_exp u hu_pos.le 3
    have hfac3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    rw [hfac3, hu3] at hfac
    have hexp_le : Real.exp u ≤ subpolyB1 2 m := by
      unfold subpolyB1
      apply Real.exp_le_exp.mpr
      rw [← hu2]
      linarith
    linarith

lemma log_add_two_sq_le_sb (m : ℕ) :
    Real.log ((m : ℝ) + 2) ^ 2 ≤ 36 * subpolyB1 4 m := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hL_nn : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h1 := pow_le_pow_left₀ hL_nn (real_log_add_two_le_sb m) 2
  have h2 : (6 * subpolyB1 2 m) ^ 2 = 36 * subpolyB1 4 m := by
    rw [mul_pow, subpolyB1_sq]
    norm_num
  linarith

lemma real_log_add_two_le_four_mul {m_tw m : ℕ} (h1m : 1 ≤ m) (hm_tw : m_tw ≤ 4 * m) :
    Real.log ((m_tw : ℝ) + 2) ≤ 4 * Real.log ((m : ℝ) + 2) := by
  have hm1 : (m_tw : ℝ) + 2 ≤ 4 * ((m : ℝ) + 2) := by
    have : (m_tw : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hm_tw
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hlog1 : Real.log ((m_tw : ℝ) + 2) ≤ Real.log 4 + Real.log ((m : ℝ) + 2) := by
    have h := Real.log_le_log (by positivity) hm1
    rwa [Real.log_mul (by norm_num) hm_pos.ne'] at h
  have hlog4 : Real.log 4 ≤ 2 * Real.log ((m : ℝ) + 2) := by
    have h4_le_sq : (4 : ℝ) ≤ ((m : ℝ) + 2) ^ (2 : ℕ) := by
      have hm3 : (3 : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast (by omega : 3 ≤ m + 2)
      nlinarith
    have h := Real.log_le_log (by norm_num) h4_le_sq
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hlog_nn : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  linarith

lemma log_log_add_two_le_three_mul {L₁ L₂ : ℝ} (hL1 : 0 < L₁) (hL2 : 1 / 2 ≤ L₂) (h12 : L₁ ≤ 4 * L₂) :
    Real.log (L₁ + 2) ≤ 3 * Real.log (L₂ + 2) := by
  have harg : L₁ + 2 ≤ 4 * (L₂ + 2) := by linarith
  have hlog1 : Real.log (L₁ + 2) ≤ Real.log 4 + Real.log (L₂ + 2) := by
    have h := Real.log_le_log (by positivity) harg
    rwa [Real.log_mul (by norm_num) (by linarith)] at h
  have hlog4 : Real.log 4 ≤ 2 * Real.log (L₂ + 2) := by
    have h25 : (5 / 2 : ℝ) ≤ L₂ + 2 := by linarith
    have h2_le_sq : (4 : ℝ) ≤ (L₂ + 2) ^ (2 : ℕ) :=
      le_trans (by norm_num : (4 : ℝ) ≤ (5 / 2 : ℝ) ^ (2 : ℕ)) (pow_le_pow_left₀ (by norm_num) h25 2)
    have h := Real.log_le_log (by norm_num) h2_le_sq
    rwa [Real.log_pow] at h
  linarith

lemma citedCost_le_mul_subpoly {K : ℝ} (hK : 0 < K) {K_nat m_tw m n : ℕ}
    (hK_nat : K ≤ (K_nat : ℝ)) (h1m : 1 ≤ m) (hnm : n < m)
    (hm200 : 200 ≤ m_tw) (hm_tw : m_tw ≤ 4 * m) :
    K * ((2 * (n : ℝ)) +
      ((m_tw : ℝ) + 2) ^ (1 + K / (rOf m_tw : ℝ)) *
        Real.log ((m_tw : ℝ) + 2) ^ (K * (rOf m_tw : ℝ) ^ 2) / (1 / 200 : ℝ) ^ 2) ≤
      (40000 * 5 * (K_nat : ℝ) + 2 * (K_nat : ℝ)) * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m := by
  have hLtw_pos : 0 < Real.log ((m_tw : ℝ) + 2) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < m_tw + 2)
  have hLm_half : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ≤ (m : ℝ) + 2 by
      exact_mod_cast (by omega : 2 ≤ m + 2))
    exact le_trans half_lt_real_log_two.le h
  have hLm_pos : 0 < Real.log ((m : ℝ) + 2) := by linarith
  have hlog200 : 7 ≤ Nat.log 2 m_tw := by
    have h128 : 2 ^ 7 ≤ m_tw := by omega
    exact (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr h128
  have hr_ge1 : 1 ≤ rOf m_tw := one_le_rOf (by omega)
  have hr_pos : (0 : ℝ) < (rOf m_tw : ℝ) := by exact_mod_cast hr_ge1
  let L := Real.log ((m_tw : ℝ) + 2)
  have hN_lt_pow : (m_tw : ℝ) + 2 ≤ 2 ^ (Nat.log 2 m_tw + 2) := by
    have h1 : m_tw < 2 ^ (Nat.log 2 m_tw + 1) := Nat.lt_pow_succ_log_self (by omega) m_tw
    have h2 : m_tw + 2 ≤ 2 ^ (Nat.log 2 m_tw + 1) + 2 ^ (Nat.log 2 m_tw + 1) := by
      have : 2 ≤ 2 ^ (Nat.log 2 m_tw + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (Nat.log 2 m_tw + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h3 : 2 ^ (Nat.log 2 m_tw + 1) + 2 ^ (Nat.log 2 m_tw + 1) = 2 ^ (Nat.log 2 m_tw + 2) := by
      calc 2 ^ (Nat.log 2 m_tw + 1) + 2 ^ (Nat.log 2 m_tw + 1)
          = 2 ^ (Nat.log 2 m_tw + 1) * 2 := by omega
        _ = 2 ^ (Nat.log 2 m_tw + 2) := (Nat.pow_succ 2 (Nat.log 2 m_tw + 1)).symm
    exact_mod_cast le_trans h2 h3.le
  have hL_le_2N : L ≤ 2 * (Nat.log 2 m_tw : ℝ) := by
    have h1 : L ≤ ((Nat.log 2 m_tw + 2 : ℕ) : ℝ) * Real.log 2 := by
      have h := Real.log_le_log (by positivity) hN_lt_pow
      rwa [Real.log_pow] at h
    have h2 : ((Nat.log 2 m_tw + 2 : ℕ) : ℝ) ≤ 2 * (Nat.log 2 m_tw : ℝ) := by
      have : (7 : ℝ) ≤ (Nat.log 2 m_tw : ℝ) := by exact_mod_cast hlog200
      push_cast; linarith
    have h3 := real_log_two_lt_one
    nlinarith
  have hN_lt_8r3 : (Nat.log 2 m_tw : ℝ) < 8 * (rOf m_tw : ℝ) ^ 3 := by
    have hlt : (Nat.log 2 m_tw : ℝ) < ((rOf m_tw + 1 : ℕ) : ℝ) ^ 3 := by
      exact_mod_cast lt_rOf_succ_pow m_tw
    have hr1 : (rOf m_tw : ℝ) + 1 ≤ 2 * (rOf m_tw : ℝ) := by
      have : (1 : ℝ) ≤ (rOf m_tw : ℝ) := by exact_mod_cast hr_ge1
      linarith
    have hp := pow_le_pow_left₀ (by positivity) hr1 3
    have h2 : (2 * (rOf m_tw : ℝ)) ^ 3 = 8 * (rOf m_tw : ℝ) ^ 3 := by ring
    push_cast at hlt
    linarith
  have hL_div_r : L / (rOf m_tw : ℝ) ≤ 3 * L ^ (2 / 3 : ℝ) := by
    have hL3 : L ^ 3 ≤ (3 * (rOf m_tw : ℝ) * L ^ (2 / 3 : ℝ)) ^ 3 := by
      have hL23 : (L ^ (2 / 3 : ℝ)) ^ 3 = L ^ 2 := by
        dsimp only [L]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLtw_pos.le]; norm_num
      have hrhs : (3 * (rOf m_tw : ℝ) * L ^ (2 / 3 : ℝ)) ^ 3 = 27 * (rOf m_tw : ℝ) ^ 3 * L ^ 2 := by
        rw [mul_pow, mul_pow, hL23]; ring
      rw [hrhs]
      have hL16 : L ≤ 16 * (rOf m_tw : ℝ) ^ 3 := by linarith
      have hL27 : L ≤ 27 * (rOf m_tw : ℝ) ^ 3 := by nlinarith [pow_pos hr_pos 3]
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      nlinarith
    have h1 := (pow_le_pow_iff_left₀ hLtw_pos.le (by positivity) (by omega : 3 ≠ 0)).mp hL3
    exact (div_le_iff₀ hr_pos).mpr (by linarith)
  have hr2_le : (rOf m_tw : ℝ) ^ 2 ≤ 4 * L ^ (2 / 3 : ℝ) := by
    have hr3_le : (rOf m_tw : ℝ) ^ 3 ≤ (Nat.log 2 m_tw : ℝ) := by
      exact_mod_cast rOf_pow_le m_tw
    have hpow2 : (2 ^ Nat.log 2 m_tw : ℝ) ≤ (m_tw : ℝ) + 2 := by
      have h1 : 2 ^ Nat.log 2 m_tw ≤ m_tw := Nat.pow_log_le_self 2 (by omega)
      exact_mod_cast (by omega : 2 ^ Nat.log 2 m_tw ≤ m_tw + 2)
    have hlogN : (Nat.log 2 m_tw : ℝ) * Real.log 2 ≤ L := by
      have h := Real.log_le_log (by positivity) hpow2
      rwa [Real.log_pow] at h
    have hr3_2L : (rOf m_tw : ℝ) ^ 3 ≤ 2 * L := by
      have := half_lt_real_log_two
      have hr3_pos : (0 : ℝ) ≤ (rOf m_tw : ℝ) ^ 3 := pow_nonneg hr_pos.le 3
      have hN_nn : (0 : ℝ) ≤ (Nat.log 2 m_tw : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hr_le_2L13 : (rOf m_tw : ℝ) ≤ 2 * L ^ (1 / 3 : ℝ) := by
      have hL13 : (2 * L ^ (1 / 3 : ℝ)) ^ 3 = 8 * L := by
        dsimp only [L]
        rw [mul_pow, ← Real.rpow_natCast (Real.log ((m_tw : ℝ) + 2) ^ (1 / 3 : ℝ)),
          ← Real.rpow_mul hLtw_pos.le]
        norm_num
      have hpow : (rOf m_tw : ℝ) ^ 3 ≤ (2 * L ^ (1 / 3 : ℝ)) ^ 3 := by linarith
      exact (pow_le_pow_iff_left₀ hr_pos.le (by positivity) (by omega : 3 ≠ 0)).mp hpow
    have hsq := pow_le_pow_left₀ hr_pos.le hr_le_2L13 2
    have hL23 : (L ^ (1 / 3 : ℝ)) ^ 2 = L ^ (2 / 3 : ℝ) := by
      dsimp only [L]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLtw_pos.le]; norm_num
    rw [mul_pow, hL23] at hsq
    linarith
  have hLm_le := real_log_add_two_le_four_mul h1m hm_tw
  have hLL_le : Real.log (L + 2) ≤ 3 * Real.log (Real.log ((m : ℝ) + 2) + 2) :=
    log_log_add_two_le_three_mul hLtw_pos hLm_half hLm_le
  have hL_23 : L ^ (2 / 3 : ℝ) ≤ 3 * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) := by
    have hpow := Real.rpow_le_rpow hLtw_pos.le hLm_le (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [Real.mul_rpow (by norm_num) hLm_pos.le] at hpow
    have h423 : (4 : ℝ) ^ (2 / 3 : ℝ) ≤ 3 := by
      have h1 : ((4 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 ≤ 3 ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by omega : 3 ≠ 0)).mp h1
    have hLm23_nn : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLm_pos.le _
    nlinarith
  have hLL_L : Real.log L ≤ Real.log (L + 2) := Real.log_le_log hLtw_pos (by linarith)
  have hL_ge2 : 1 ≤ Real.log (L + 2) := by
    have hL_5 : (5 : ℝ) ≤ L := by
      have h200 : Real.exp 5 ≤ (m_tw : ℝ) + 2 := by
        have he1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        have he5 : Real.exp 5 = Real.exp 1 ^ 5 := by
          rw [← Real.exp_nat_mul]; norm_num
        have hp : Real.exp 1 ^ 5 < 2.72 ^ 5 := pow_lt_pow_left₀ he1 (Real.exp_pos _).le (by omega)
        have hm202 : (202 : ℝ) ≤ (m_tw : ℝ) + 2 := by exact_mod_cast (by omega : 202 ≤ m_tw + 2)
        linarith [show (2.72 : ℝ) ^ 5 < 202 by norm_num]
      have := Real.log_le_log (Real.exp_pos _) h200
      rwa [Real.log_exp] at this
    have h3_le : Real.exp 1 ≤ L + 2 := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos _) h3_le
    rwa [Real.log_exp] at this
  have hmtw_add : (m_tw : ℝ) + 2 ≤ 5 * (m : ℝ) := by
    have h1 : (m_tw : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hm_tw
    have h50 : (50 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 50 ≤ m)
    linarith
  have hrpow1 : ((m_tw : ℝ) + 2) ^ (1 + K / (rOf m_tw : ℝ)) =
      ((m_tw : ℝ) + 2) * Real.exp (K * (L / (rOf m_tw : ℝ))) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one, Real.rpow_def_of_pos (by positivity)]
    congr 1; dsimp only [L]; ring_nf
  have hrpow2 : L ^ (K * (rOf m_tw : ℝ) ^ 2) = Real.exp (K * (rOf m_tw : ℝ) ^ 2 * Real.log L) := by
    rw [Real.rpow_def_of_pos hLtw_pos]
    congr 1; ring
  have hexp_comb : Real.exp (K * (L / (rOf m_tw : ℝ))) * Real.exp (K * (rOf m_tw : ℝ) ^ 2 * Real.log L) ≤
      subpolyB1 (64 * (K_nat : ℝ)) m := by
    rw [← Real.exp_add]
    unfold subpolyB1
    apply Real.exp_le_exp.mpr
    have h1 : K * (L / (rOf m_tw : ℝ)) ≤ 3 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
      have hL23_nn : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLtw_pos.le _
      calc K * (L / (rOf m_tw : ℝ))
          ≤ (K_nat : ℝ) * (3 * L ^ (2 / 3 : ℝ)) := mul_le_mul hK_nat hL_div_r (by positivity) (by positivity)
        _ = 3 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * 1) := by ring
        _ ≤ 3 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
            gcongr
    have h2 : K * (rOf m_tw : ℝ) ^ 2 * Real.log L ≤
        4 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
      have hK_r2 : K * (rOf m_tw : ℝ) ^ 2 ≤ (K_nat : ℝ) * (4 * L ^ (2 / 3 : ℝ)) :=
        mul_le_mul hK_nat hr2_le (by positivity) (by positivity)
      by_cases hlog_nn : 0 ≤ Real.log L
      · calc K * (rOf m_tw : ℝ) ^ 2 * Real.log L
            ≤ (K_nat : ℝ) * (4 * L ^ (2 / 3 : ℝ)) * Real.log (L + 2) :=
              mul_le_mul hK_r2 hLL_L hlog_nn (by positivity)
          _ = 4 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by ring
      · have hneg : K * (rOf m_tw : ℝ) ^ 2 * Real.log L ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hlog_nn)
        have hpos : 0 ≤ 4 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          have : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLtw_pos.le _
          positivity
        linarith
    have h3 : L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤
        9 * (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
      have h := mul_le_mul hL_23 hLL_le (by linarith) (by positivity)
      linarith
    have hsum : K * (L / (rOf m_tw : ℝ)) + K * (rOf m_tw : ℝ) ^ 2 * Real.log L ≤
        7 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by linarith
    have hK_nn : (0 : ℝ) ≤ (K_nat : ℝ) := Nat.cast_nonneg _
    have h7 : 7 * (K_nat : ℝ) * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤
        64 * (K_nat : ℝ) * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2) := by
      have hmul := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) hK_nn : 0 ≤ 7 * (K_nat : ℝ))
      have hLL_nn : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2) := by
        have : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hLm_pos.le _
        have : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
        positivity
      have h63 : 63 * ((K_nat : ℝ) * (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2))) ≤
          64 * ((K_nat : ℝ) * (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2))) := by
        nlinarith [mul_nonneg hK_nn hLL_nn]
      linarith
    exact le_trans hsum h7
  rw [hrpow1, hrpow2]
  have hmain1 : ((m_tw : ℝ) + 2) * Real.exp (K * (L / (rOf m_tw : ℝ))) *
      Real.exp (K * (rOf m_tw : ℝ) ^ 2 * Real.log L) / (1 / 200 : ℝ) ^ 2 ≤
      40000 * 5 * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m := by
    have hinv : ((1 / 200 : ℝ) ^ 2)⁻¹ = 40000 := by norm_num
    rw [div_eq_mul_inv, hinv]
    have hmul : ((m_tw : ℝ) + 2) * (Real.exp (K * (L / (rOf m_tw : ℝ))) *
        Real.exp (K * (rOf m_tw : ℝ) ^ 2 * Real.log L)) ≤
        (5 * (m : ℝ)) * subpolyB1 (64 * (K_nat : ℝ)) m :=
      mul_le_mul hmtw_add hexp_comb (by positivity) (by positivity)
    linarith
  have hn_le_m : 2 * (n : ℝ) ≤ 2 * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m := by
    have hnm_r : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hnm
    have hsb := one_le_subpolyB1 (by positivity : 0 ≤ 64 * (K_nat : ℝ)) m
    nlinarith
  have hinner := add_le_add hn_le_m hmain1
  calc K * (2 * (n : ℝ) + ((m_tw : ℝ) + 2) * Real.exp (K * (L / (rOf m_tw : ℝ))) *
        Real.exp (K * (rOf m_tw : ℝ) ^ 2 * Real.log L) / (1 / 200 : ℝ) ^ 2)
      ≤ (K_nat : ℝ) * (2 * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m +
          40000 * 5 * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m) :=
        mul_le_mul hK_nat hinner (by positivity) (by positivity)
    _ = (40000 * 5 * (K_nat : ℝ) + 2 * (K_nat : ℝ)) * (m : ℝ) * subpolyB1 (64 * (K_nat : ℝ)) m := by
        ring

/-! ## 2. Word-Size & Polynomial Space Bounds for Twin Inputs -/

lemma foldr_max_append (xs ys : List ℕ) :
    List.foldr max 0 (xs ++ ys) = max (List.foldr max 0 xs) (List.foldr max 0 ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, max_assoc]

lemma foldr_max_graphEncode {G : Cited.Graph} (hV : G.IsValid) :
    List.foldr max 0 G.encode ≤ G.n + G.m := by
  have aux : ∀ es : List (ℕ × ℕ), (∀ e ∈ es, e.1 < G.n ∧ e.2 < G.n) →
      List.foldr max 0 (es.flatMap fun e => [e.1, e.2]) ≤ G.n := by
    intro es hes
    induction es with
    | nil => simp
    | cons e es' ih =>
      have he := hes e List.mem_cons_self
      have ih' := ih fun e' he' => hes e' (List.mem_cons_of_mem _ he')
      simp only [List.flatMap_cons, foldr_max_append, List.foldr_cons, List.foldr_nil]
      omega
  simp only [Cited.Graph.encode, List.foldr_cons]
  have hflat := aux G.edges hV
  omega

lemma two_pow_wordSize_twin_le {D : ℕ} {curG : Cited.Graph} (hV : curG.IsValid)
    (c_cited n m : ℕ) (hn : curG.n = n) (hnm : n < m) (hcm : curG.m ≤ m) (hDn : D * n ≤ 2 * m) :
    2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) ≤
      2 * (416 * (n + m + 2)) ^ c_cited ∧
    wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) ≤
      5 * c_cited * (Nat.log 2 (n + m + 206) + 1) := by
  have htwV := twinGraph_isValid (D := D) hV
  have htw_n : (twinGraph D curG).n = 2 * n := by simp [twinGraph, hn]
  have htw_m : (twinGraph D curG).m ≤ 3 * m := by
    rw [twinGraph_m, hn]; omega
  set x := (twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]
  have hx_len : x.length ≤ 5 + 6 * m := by
    simp only [x, List.length_append, Cited.Graph.encode, List.length_cons, List.length_nil]
    have hfl : (List.flatMap (fun e => [e.1, e.2]) (twinGraph D curG).edges).length =
        2 * (twinGraph D curG).m := by
      have h1 : ∀ l : List (ℕ × ℕ), (l.flatMap fun e => [e.1, e.2]).length = 2 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons _ _ ih => simp [ih]; omega
      exact h1 _
    rw [hfl]
    omega
  have hr_le : rOf (curG.m + D * curG.n) ≤ 3 * m := by
    have h1 : rOf (curG.m + D * curG.n) ≤ Nat.log 2 (curG.m + D * curG.n) := by
      have hcb := rOf_pow_le (curG.m + D * curG.n)
      by_cases h0 : rOf (curG.m + D * curG.n) = 0
      · simp [h0]
      · calc rOf (curG.m + D * curG.n) ≤ rOf (curG.m + D * curG.n) ^ 3 :=
            Nat.le_self_pow (by omega) _
          _ ≤ Nat.log 2 (curG.m + D * curG.n) := hcb
    have h2 : Nat.log 2 (curG.m + D * curG.n) ≤ curG.m + D * curG.n := by
      by_cases hm0 : curG.m + D * curG.n = 0
      · simp [hm0]
      · exact le_trans (Nat.le_succ _) (natLog2_add_one_le_self' (by omega))
    rw [hn] at h1 h2 ⊢
    omega
  have hx_max : List.foldr max 0 x ≤ 200 + 2 * n + 3 * m := by
    simp only [x, foldr_max_append, List.foldr_cons, List.foldr_nil]
    have hg := foldr_max_graphEncode htwV
    rw [htw_n] at hg
    omega
  have hx_sum : x.length + List.foldr max 0 x + 2 ≤ 208 * (n + m + 2) := by omega
  have h1 : 2 ^ (wordSize c_cited x + 1) ≤ 2 * (416 * (n + m + 2)) ^ c_cited := by
    rw [pow_succ']
    have hws := two_pow_wordSize_le c_cited x
    have h2 : 2 * (x.length + List.foldr max 0 x + 2) ≤ 416 * (n + m + 2) := by omega
    have hp := Nat.pow_le_pow_left h2 c_cited
    omega
  have h2 : wordSize c_cited x ≤ 5 * c_cited * (Nat.log 2 (n + m + 206) + 1) := by
    unfold wordSize
    have hsum16 : x.length + List.foldr max 0 x + 2 ≤ 16 * (n + m + 206) := by omega
    have hpowB := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n + m + 206)
    have hlt_pow : x.length + List.foldr max 0 x + 2 < 2 ^ (Nat.log 2 (n + m + 206) + 5) := by
      have h16 : 16 * (n + m + 206) < 16 * 2 ^ (Nat.log 2 (n + m + 206) + 1) := by omega
      have h25 : 16 * 2 ^ (Nat.log 2 (n + m + 206) + 1) = 2 ^ (Nat.log 2 (n + m + 206) + 5) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; ring_nf
      omega
    have hlog_lt : Nat.log 2 (x.length + List.foldr max 0 x + 2) < Nat.log 2 (n + m + 206) + 5 :=
      (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr hlt_pow
    have hlog_le : Nat.log 2 (x.length + List.foldr max 0 x + 2) + 1 ≤
        5 * (Nat.log 2 (n + m + 206) + 1) := by omega
    calc c_cited * (Nat.log 2 (x.length + List.foldr max 0 x + 2) + 1)
        ≤ c_cited * (5 * (Nat.log 2 (n + m + 206) + 1)) := Nat.mul_le_mul_left c_cited hlog_le
      _ = 5 * c_cited * (Nat.log 2 (n + m + 206) + 1) := by ring
  exact ⟨h1, h2⟩

/-! ## 3. Arena Length Bound Across Components -/

private lemma sum_filter_fst_eq_length (R : Finset ℕ) :
    ∀ L : List (ℕ × ℕ), (∀ e ∈ L, e.1 ∈ R) →
      ∑ x ∈ R, (L.filter fun e => decide (e.1 = x)).length = L.length
  | [], _ => by simp
  | e :: L', h => by
    have he : e.1 ∈ R := h e (by simp)
    have hL' : ∀ e' ∈ L', e'.1 ∈ R := fun e' he' => h e' (by simp [he'])
    have ih := sum_filter_fst_eq_length R L' hL'
    simp only [List.filter_cons, apply_ite List.length, List.length_cons]
    have hsplit : (∑ x ∈ R, (if decide (e.1 = x) = true then
        (L'.filter fun e => decide (e.1 = x)).length + 1 else
        (L'.filter fun e => decide (e.1 = x)).length)) =
        (∑ x ∈ R, (L'.filter fun e => decide (e.1 = x)).length) +
        (∑ x ∈ R, if e.1 = x then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : e.1 = x <;> simp [hx]
    rw [hsplit, Finset.sum_ite_eq, ih]
    simp [he]

private lemma sum_filter_snd_eq_length (R : Finset ℕ) :
    ∀ L : List (ℕ × ℕ), (∀ e ∈ L, e.2 ∈ R) →
      ∑ x ∈ R, (L.filter fun e => decide (e.2 = x)).length = L.length
  | [], _ => by simp
  | e :: L', h => by
    have he : e.2 ∈ R := h e (by simp)
    have hL' : ∀ e' ∈ L', e'.2 ∈ R := fun e' he' => h e' (by simp [he'])
    have ih := sum_filter_snd_eq_length R L' hL'
    simp only [List.filter_cons, apply_ite List.length, List.length_cons]
    have hsplit : (∑ x ∈ R, (if decide (e.2 = x) = true then
        (L'.filter fun e => decide (e.2 = x)).length + 1 else
        (L'.filter fun e => decide (e.2 = x)).length)) =
        (∑ x ∈ R, (L'.filter fun e => decide (e.2 = x)).length) +
        (∑ x ∈ R, if e.2 = x then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : e.2 = x <;> simp [hx]
    rw [hsplit, Finset.sum_ite_eq, ih]
    simp [he]

lemma sum_degIn_eq_two_mul_inside (G : Cited.Graph) (R : Finset ℕ) :
    ∑ x ∈ R, G.degIn R x = 2 * (G.inside R).length := by
  have hL : ∀ e ∈ G.inside R, e.1 ∈ R ∧ e.2 ∈ R := fun e he => by
    simp only [Cited.Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2
  simp only [Cited.Graph.degIn, Finset.sum_add_distrib]
  rw [sum_filter_fst_eq_length R (G.inside R) (fun e he => (hL e he).1),
      sum_filter_snd_eq_length R (G.inside R) (fun e he => (hL e he).2)]
  omega

lemma arena_len_le_four_mul_Gi {Gi : Cited.Graph} {validRs : List (Finset ℕ)}
    {rawComps_lvl : List (ℕ × List ℕ)} {φ : ℝ} (hφ : 0 < φ) {lvl : ℕ}
    (hmap : rawComps_lvl.map (fun c => c.2.toFinset) = validRs)
    (hcomps : ∀ c ∈ rawComps_lvl, c.1 = lvl ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length)
    (hdisj : validRs.Pairwise Disjoint)
    (hR_spec : ∀ R ∈ validRs, 2 ≤ R.card ∧ ∀ x ∈ R, φ * (2 ^ lvl : ℝ) ≤ (Gi.degIn R x : ℝ)) :
    (rawComps_lvl.flatMap compRecord).length ≤ 4 * Gi.m ∧ rawComps_lvl.length ≤ Gi.m := by
  have hlen_sum : (rawComps_lvl.flatMap compRecord).length =
      (validRs.map fun R => 2 + R.card).sum := by
    rw [← hmap]
    clear hmap hdisj hR_spec
    induction rawComps_lvl with
    | nil => simp
    | cons c cs ih =>
      have hc := hcomps c (by simp)
      have hnd : c.2.Nodup := List.Pairwise.nodup (List.Pairwise.imp (fun h => Nat.ne_of_lt h) hc.2.1)
      have hcs : ∀ c' ∈ cs, c'.1 = lvl ∧ c'.2.Pairwise (· < ·) ∧ 2 ≤ c'.2.length :=
        fun c' hc' => hcomps c' (by simp [hc'])
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.length_append, compRecord,
        List.length_cons]
      rw [List.toFinset_card_of_nodup hnd, ih hcs]
      omega
  have hsum_bd : (validRs.map fun R => 2 + R.card).sum ≤
      4 * (validRs.map fun R => (Gi.inside R).length).sum := by
    clear hmap hcomps hdisj hlen_sum
    induction validRs with
    | nil => simp
    | cons R Rs ih =>
      have hR := hR_spec R (by simp)
      have hR_deg : ∀ x ∈ R, 1 ≤ Gi.degIn R x := fun x hx => by
        have h1 : φ * (2 ^ lvl : ℝ) ≤ (Gi.degIn R x : ℝ) := hR.2 x hx
        have hpos : (0 : ℝ) < (Gi.degIn R x : ℝ) := lt_of_lt_of_le (by positivity) h1
        exact_mod_cast (by
          by_contra hlt
          have h0 : Gi.degIn R x = 0 := by omega
          rw [h0] at hpos
          simp at hpos : 1 ≤ Gi.degIn R x)
      have hcard_le_sum : R.card ≤ ∑ x ∈ R, Gi.degIn R x := by
        calc R.card = ∑ _ ∈ R, 1 := by simp
          _ ≤ ∑ x ∈ R, Gi.degIn R x := Finset.sum_le_sum hR_deg
      have h2R : 2 + R.card ≤ 4 * (Gi.inside R).length := by
        rw [sum_degIn_eq_two_mul_inside] at hcard_le_sum
        omega
      have ih' := ih (fun R' hR' => hR_spec R' (by simp [hR']))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add h2R ih'
  have hinside_le : (validRs.map fun R => (Gi.inside R).length).sum ≤ Gi.m :=
    sum_filter_inside_disjoint_le validRs hdisj Gi.edges
  have hflat_le : (rawComps_lvl.flatMap compRecord).length ≤ 4 * Gi.m := by omega
  have h4len : 4 * rawComps_lvl.length ≤ (rawComps_lvl.flatMap compRecord).length := by
    clear hmap hdisj hR_spec hlen_sum hsum_bd hinside_le hflat_le
    induction rawComps_lvl with
    | nil => simp
    | cons c cs ih =>
      have hc := hcomps c (by simp)
      have hcs := ih (fun c' hc' => hcomps c' (by simp [hc']))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, compRecord]
      omega
  exact ⟨hflat_le, by omega⟩


end

end MinCostFlow.Expander
