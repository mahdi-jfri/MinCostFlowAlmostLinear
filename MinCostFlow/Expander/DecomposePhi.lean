module

public import MinCostFlow.Expander.ExpanderDecomp
public import MinCostFlow.Expander.Decompose
public import MinCostFlow.Expander.Section8Static

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conductance Denominator and Subpolynomial / Polynomial Bounds for `Decompose`

Provides the integer denominator `phiDenHalf` / `maxPhiDenOf` used by `DecomposeImpl`
(**Theorem 8.5** / **Theorem B.1**, pages 41 & 49):
1. `phiDenHalf K_nat thr m := max (thr + 1) (200 * K_nat * (Nat.log 2 (4 * m + 2) + 2) ^ (K_nat * (rOf (4 * m)) ^ 2))`,
   which is monotone in `m` and satisfies `(1 : ℝ) / phiDenHalf ≤ φ_cited` above `thr` and
   `(1 : ℝ) / phiDenHalf ≤ 1 / (m_twin + 1)` below `thr` for every `m_twin ≤ 4 * m`.
2. `maxPhiDenOf K_nat thr m := 3 * phiDenHalf K_nat thr m` is bounded both subpolynomially
   (`C₁ * subpolyB1 C₀ m`) and linearly (`C_phi * (m + 2)`).
-/

@[expose] public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ## 1. Pure Monotonicity & Conductance Domination -/

lemma cubeRoot_mono {a b : ℕ} (h : a ≤ b) : cubeRoot a ≤ cubeRoot b := by
  have h1 : (cubeRoot a) ^ 3 ≤ a := cubeRoot_pow_le a
  have h2 : b < (cubeRoot b + 1) ^ 3 := lt_cubeRoot_succ_pow b
  by_contra hgt
  have hle : cubeRoot b + 1 ≤ cubeRoot a := by omega
  have hpow : (cubeRoot b + 1) ^ 3 ≤ (cubeRoot a) ^ 3 := Nat.pow_le_pow_left hle 3
  omega

lemma rOf_mono {a b : ℕ} (h : a ≤ b) : rOf a ≤ rOf b := by
  have h1 : (rOf a) ^ 3 ≤ Nat.log 2 a := rOf_pow_le a
  have h2 : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h
  have h3 : Nat.log 2 b < (rOf b + 1) ^ 3 := lt_rOf_succ_pow b
  by_contra hgt
  have hle : rOf b + 1 ≤ rOf a := by omega
  have hpow : (rOf b + 1) ^ 3 ≤ (rOf a) ^ 3 := Nat.pow_le_pow_left hle 3
  omega

/-- Half-denominator `D_phi(m)` (before the factor-of-`3` pruning loss) for `Decompose`. -/
def phiDenHalf (K_nat thr m : ℕ) : ℕ :=
  max (thr + 1) (200 * K_nat * (Nat.log 2 (4 * m + 2) + 2) ^ (K_nat * (rOf (4 * m)) ^ 2))

/-- Exact polynomial-capped maximum denominator `3 * phiDenHalf K_nat thr m`. -/
def maxPhiDenOf (K_nat thr m : ℕ) : ℕ :=
  3 * phiDenHalf K_nat thr m

lemma le_phiDenHalf_thr (K_nat thr m : ℕ) : thr + 1 ≤ phiDenHalf K_nat thr m :=
  le_max_left _ _

lemma phiDenHalf_pos (K_nat thr m : ℕ) : 1 ≤ phiDenHalf K_nat thr m :=
  Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (le_phiDenHalf_thr K_nat thr m)

lemma maxPhiDenOf_pos (K_nat thr m : ℕ) : 1 ≤ maxPhiDenOf K_nat thr m := by
  unfold maxPhiDenOf
  have := phiDenHalf_pos K_nat thr m
  omega

lemma phiDenHalf_mono (K_nat thr : ℕ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    phiDenHalf K_nat thr m₁ ≤ phiDenHalf K_nat thr m₂ := by
  unfold phiDenHalf
  apply max_le_max (le_refl _)
  apply Nat.mul_le_mul_left
  have hbase : Nat.log 2 (4 * m₁ + 2) + 2 ≤ Nat.log 2 (4 * m₂ + 2) + 2 :=
    Nat.add_le_add_right (Nat.log_mono_right (by omega)) 2
  have hexp : K_nat * (rOf (4 * m₁)) ^ 2 ≤ K_nat * (rOf (4 * m₂)) ^ 2 :=
    Nat.mul_le_mul_left K_nat (Nat.pow_le_pow_left (rOf_mono (by omega)) 2)
  exact le_trans (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_right (by omega) hexp)

lemma maxPhiDenOf_mono (K_nat thr : ℕ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    maxPhiDenOf K_nat thr m₁ ≤ maxPhiDenOf K_nat thr m₂ :=
  Nat.mul_le_mul_left 3 (phiDenHalf_mono K_nat thr hm)

lemma real_log_add_two_le_natLog2 {m_twin m : ℕ} (hm : m_twin ≤ 4 * m) :
    Real.log ((m_twin : ℝ) + 2) ≤ ((Nat.log 2 (4 * m + 2) + 1 : ℕ) : ℝ) := by
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have h2pow : (m_twin : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log 2 (4 * m + 2) + 1) := by
    have hlt : 4 * m + 2 < 2 ^ (Nat.log 2 (4 * m + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    exact_mod_cast (by omega : m_twin + 2 ≤ 2 ^ (Nat.log 2 (4 * m + 2) + 1))
  have hexp_pow : (2 : ℝ) ^ (Nat.log 2 (4 * m + 2) + 1) ≤
      (Real.exp 1) ^ (Nat.log 2 (4 * m + 2) + 1) :=
    pow_le_pow_left₀ (by norm_num) hexp1 _
  have hle_exp : (m_twin : ℝ) + 2 ≤ Real.exp ((Nat.log 2 (4 * m + 2) + 1 : ℕ) : ℝ) := by
    refine le_trans h2pow (le_trans hexp_pow ?_)
    rw [← Real.exp_nat_mul, mul_one]
  have hlog := Real.log_le_log (by positivity) hle_exp
  simpa [Real.log_exp] using hlog

lemma phiDenHalf_ge_cited_denom {K : ℝ} (hK : 0 < K) {K_nat m_twin m : ℕ}
    (hKK : K ≤ K_nat) (hm : m_twin ≤ 4 * m) :
    K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2) ≤
      (K_nat : ℝ) * ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^ (K_nat * (rOf (4 * m)) ^ 2) := by
  have hL_pos : 0 < Real.log ((m_twin : ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m_twin])
  have hr_le : (rOf m_twin : ℝ) ≤ (rOf (4 * m) : ℝ) := by exact_mod_cast rOf_mono hm
  have hexp_le : K * (rOf m_twin : ℝ) ^ 2 ≤ ((K_nat * (rOf (4 * m)) ^ 2 : ℕ) : ℝ) := by
    have hsq : (rOf m_twin : ℝ) ^ 2 ≤ (rOf (4 * m) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
    push_cast
    exact mul_le_mul hKK hsq (by positivity) (by positivity)
  have hbase_ge1 : (1 : ℝ) ≤ ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ Nat.log 2 (4 * m + 2) + 2)
  have hrpow_le : Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2) ≤
      ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^ (K_nat * (rOf (4 * m)) ^ 2) := by
    by_cases hL1 : 1 ≤ Real.log ((m_twin : ℝ) + 2)
    · have hbase : Real.log ((m_twin : ℝ) + 2) ≤ ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) := by
        have := real_log_add_two_le_natLog2 hm
        push_cast at this ⊢
        linarith
      have h1 := Real.rpow_le_rpow hL_pos.le hbase (by positivity : 0 ≤ K * (rOf m_twin : ℝ) ^ 2)
      have h2 := Real.rpow_le_rpow_of_exponent_le hbase_ge1 hexp_le
      rw [Real.rpow_natCast] at h2
      exact le_trans h1 h2
    · have h1 : Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2) ≤ 1 :=
        Real.rpow_le_one hL_pos.le (le_of_not_ge hL1) (by positivity)
      have h2 : (1 : ℝ) ≤ ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^ (K_nat * (rOf (4 * m)) ^ 2) := by
        exact_mod_cast Nat.one_le_pow _ _ (by omega)
      exact le_trans h1 h2
  have hrpow_nn : 0 ≤ Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2) :=
    Real.rpow_nonneg hL_pos.le _
  exact mul_le_mul hKK hrpow_le hrpow_nn (by positivity)

lemma one_div_phiDenHalf_le_cited {K : ℝ} (hK : 0 < K) {K_nat thr m_twin m : ℕ}
    (hKK : K ≤ K_nat) (hm : m_twin ≤ 4 * m) :
    (1 : ℝ) / (phiDenHalf K_nat thr m : ℝ) ≤
      ((1 : ℝ) / 200) / (K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2)) := by
  have hden_ge : (200 * K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2)) ≤
      (phiDenHalf K_nat thr m : ℝ) := by
    have h1 := phiDenHalf_ge_cited_denom hK hKK hm
    have h2 : (200 * K_nat * (Nat.log 2 (4 * m + 2) + 2) ^ (K_nat * (rOf (4 * m)) ^ 2) : ℕ) ≤
        phiDenHalf K_nat thr m := le_max_right _ _
    have h2R : ((200 * K_nat * (Nat.log 2 (4 * m + 2) + 2) ^ (K_nat * (rOf (4 * m)) ^ 2) : ℕ) : ℝ) ≤
        (phiDenHalf K_nat thr m : ℝ) := by
      exact_mod_cast h2
    have h2R' : 200 * ((K_nat : ℝ) * ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^
        (K_nat * (rOf (4 * m)) ^ 2)) ≤ (phiDenHalf K_nat thr m : ℝ) := by
      refine le_trans (le_of_eq ?_) h2R
      push_cast; ring
    nlinarith
  have hL_pos : 0 < Real.log ((m_twin : ℝ) + 2) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m_twin])
  have hden_pos : 0 < 200 * K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2) := by
    positivity
  have hle := one_div_le_one_div_of_le hden_pos hden_ge
  have heq : (1 : ℝ) / (200 * K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2)) =
      ((1 : ℝ) / 200) / (K * Real.log ((m_twin : ℝ) + 2) ^ (K * (rOf m_twin : ℝ) ^ 2)) := by
    ring
  rwa [← heq]

lemma one_div_phiDenHalf_le_fallback {K_nat thr m_twin m : ℕ} (hm : m_twin < thr) :
    (1 : ℝ) / (phiDenHalf K_nat thr m : ℝ) ≤ (1 : ℝ) / ((m_twin : ℝ) + 1) := by
  apply one_div_le_one_div_of_le (by positivity)
  have := le_phiDenHalf_thr K_nat thr m
  exact_mod_cast (by omega : m_twin + 1 ≤ phiDenHalf K_nat thr m)

/-! ## 2. Subpolynomial & Polynomial Upper Bounds on `maxPhiDenOf` -/

lemma natLog2_add_two_le_log {m : ℕ} :
    ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ≤ 10 * Real.log ((m : ℝ) + 2) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by simpa using half_le_log_add_two_nat 0
  have hlog2_ne : Real.log 2 ≠ 0 := by linarith
  have hnat : (Nat.log 2 (4 * m + 2) : ℝ) ≤ Real.log ((4 * m + 2 : ℕ) : ℝ) / Real.log 2 := by
    have hm0 : 4 * m + 2 ≠ 0 := by omega
    have hpow : (2 : ℝ) ^ Nat.log 2 (4 * m + 2) ≤ ((4 * m + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hm0
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ (by linarith)).mpr (by linarith)
  have h4m_le : ((4 * m + 2 : ℕ) : ℝ) ≤ 4 * ((m : ℝ) + 2) := by push_cast; linarith
  have hlog_4m : Real.log ((4 * m + 2 : ℕ) : ℝ) ≤ Real.log (4 * ((m : ℝ) + 2)) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < 4 * m + 2)) h4m_le
  have hlog_mul : Real.log (4 * ((m : ℝ) + 2)) = 2 * Real.log 2 + Real.log ((m : ℝ) + 2) := by
    have h4eq : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [Real.log_mul (by norm_num) (by positivity), h4eq, Real.log_pow]
    push_cast; ring
  have hdiv_le : Real.log ((4 * m + 2 : ℕ) : ℝ) / Real.log 2 ≤
      2 + 2 * Real.log ((m : ℝ) + 2) := by
    have h1 : Real.log ((4 * m + 2 : ℕ) : ℝ) / Real.log 2 ≤
        (2 * Real.log 2 + Real.log ((m : ℝ) + 2)) / Real.log 2 :=
      div_le_div_of_nonneg_right (le_trans hlog_4m (le_of_eq hlog_mul)) (by linarith)
    have h2 : (2 * Real.log 2 + Real.log ((m : ℝ) + 2)) / Real.log 2 =
        2 + Real.log ((m : ℝ) + 2) / Real.log 2 := by field_simp [hlog2_ne]
    have h3 : Real.log ((m : ℝ) + 2) / Real.log 2 ≤ 2 * Real.log ((m : ℝ) + 2) := by
      have hL_nonneg : 0 ≤ Real.log ((m : ℝ) + 2) := (half_le_log_add_two_nat m).trans' (by norm_num)
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hhalf := half_le_log_add_two_nat m
  push_cast
  linarith

lemma maxPhiDenOf_le_subpoly (K_nat thr : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ m : ℕ, (maxPhiDenOf K_nat thr m : ℝ) ≤ C₁ * subpolyB1 C₀ m := by
  have h52 : (1 / 2 : ℝ) ≤ Real.log (5 / 2 : ℝ) := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
    have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h1 : Real.exp (1 / 2 : ℝ) ≤ 5 / 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h1
  let c_log10 : ℝ := 2 * max 0 (Real.log 10) + 2
  let C₀ : ℝ := max 1 (5 * (K_nat : ℝ) * c_log10)
  let C₁ : ℝ := 3 * max ((thr : ℝ) + 1) (200 * (K_nat : ℝ) + 1)
  refine ⟨C₀, C₁, by positivity, by positivity, fun m => ?_⟩
  set L : ℝ := Real.log ((m : ℝ) + 2)
  have hL_half : 1 / 2 ≤ L := half_le_log_add_two_nat m
  have hL_pos : 0 < L := by linarith
  have hr_cube : (rOf (4 * m) : ℝ) ^ 3 ≤ 10 * L := by
    have h1 : (rOf (4 * m) : ℝ) ^ 3 ≤ (Nat.log 2 (4 * m) : ℝ) := by
      exact_mod_cast rOf_pow_le (4 * m)
    have h2 : (Nat.log 2 (4 * m) : ℝ) ≤ ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.log_mono_right (by omega : 4 * m ≤ 4 * m + 2)).trans (Nat.le_add_right _ 2)
    exact le_trans h1 (le_trans h2 natLog2_add_two_le_log)
  have hr_sq : (rOf (4 * m) : ℝ) ^ 2 ≤ 5 * L ^ (2 / 3 : ℝ) := by
    have hr_le : (rOf (4 * m) : ℝ) ≤ (10 * L) ^ (1 / 3 : ℝ) := by
      have hp0 : 0 ≤ (10 * L) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
      rw [← pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hp0 (by norm_num : 3 ≠ 0)]
      have heq : ((10 * L) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 10 * L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rwa [heq]
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
    have heq : ((10 * L) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) = 10 ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hL_pos.le]
      norm_num
    have h10 : (10 : ℝ) ^ (2 / 3 : ℝ) ≤ 5 := by
      rw [← Real.rpow_le_rpow_iff (z := (3 : ℝ)) (by positivity) (by positivity) (by norm_num)]
      have : ((10 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℝ) = 100 := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]
      norm_num
    exact le_trans hsq (by rw [heq]; exact mul_le_mul_of_nonneg_right h10 (by positivity))
  have hlog10L : Real.log (10 * L) ≤ c_log10 * Real.log (L + 2) := by
    have h1 : Real.log (10 * L) = Real.log 10 + Real.log L :=
      Real.log_mul (by norm_num) hL_pos.ne'
    have h2 : Real.log L ≤ Real.log (L + 2) := Real.log_le_log hL_pos (by linarith)
    have h3 : (1 / 2 : ℝ) ≤ Real.log (L + 2) :=
      le_trans h52 (Real.log_le_log (by norm_num) (by linarith))
    have h4 : Real.log 10 ≤ (2 * max 0 (Real.log 10)) * Real.log (L + 2) := by
      calc Real.log 10 ≤ max 0 (Real.log 10) := le_max_right _ _
        _ = (2 * max 0 (Real.log 10)) * (1 / 2) := by ring
        _ ≤ (2 * max 0 (Real.log 10)) * Real.log (L + 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [h1]
    dsimp only [c_log10]
    nlinarith
  have hpow_sb : ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^ (K_nat * (rOf (4 * m)) ^ 2) ≤
      subpolyB1 C₀ m := by
    have hbase : ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ≤ 10 * L := natLog2_add_two_le_log
    have hp_pos : (0 : ℝ) < ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) := by positivity
    calc ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^ (K_nat * (rOf (4 * m)) ^ 2)
        ≤ (10 * L) ^ (K_nat * (rOf (4 * m)) ^ 2) := pow_le_pow_left₀ hp_pos.le hbase _
      _ = Real.exp (Real.log (10 * L) * ((K_nat : ℝ) * (rOf (4 * m) : ℝ) ^ 2)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
          push_cast; rfl
      _ ≤ Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          rw [Real.exp_le_exp]
          have h52' : 0 ≤ Real.log (L + 2) := by
            linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 5 / 2) (by linarith : (5 / 2 : ℝ) ≤ L + 2)]
          have hlog10L_nonneg : 0 ≤ Real.log (10 * L) := Real.log_nonneg (by nlinarith)
          calc Real.log (10 * L) * ((K_nat : ℝ) * (rOf (4 * m) : ℝ) ^ 2)
              ≤ (c_log10 * Real.log (L + 2)) * ((K_nat : ℝ) * (5 * L ^ (2 / 3 : ℝ))) := by
                apply mul_le_mul hlog10L (mul_le_mul_of_nonneg_left hr_sq (by positivity))
                  (by positivity) (by positivity)
            _ = (5 * (K_nat : ℝ) * c_log10) * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by ring
            _ ≤ C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by
                apply mul_le_mul_of_nonneg_right _ h52'
                apply mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hsb_ge1 : 1 ≤ subpolyB1 C₀ m := by
    unfold subpolyB1
    apply Real.one_le_exp
    have h0 : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
    change 0 ≤ C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)
    positivity
  have hmax : max ((thr : ℝ) + 1) (200 * (K_nat : ℝ) * ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^
      (K_nat * (rOf (4 * m)) ^ 2)) ≤ (C₁ / 3) * subpolyB1 C₀ m := by
    refine max_le ?_ ?_
    · calc (thr : ℝ) + 1 ≤ max ((thr : ℝ) + 1) (200 * (K_nat : ℝ) + 1) := le_max_left _ _
        _ = (C₁ / 3) * 1 := by dsimp only [C₁]; ring
        _ ≤ (C₁ / 3) * subpolyB1 C₀ m := mul_le_mul_of_nonneg_left hsb_ge1 (by positivity)
    · have hK_le : 200 * (K_nat : ℝ) ≤ C₁ / 3 := by
        dsimp only [C₁]
        linarith [le_max_right ((thr : ℝ) + 1) (200 * (K_nat : ℝ) + 1)]
      exact mul_le_mul hK_le hpow_sb (by positivity) (by positivity)
  have h3max : (maxPhiDenOf K_nat thr m : ℝ) ≤ C₁ * subpolyB1 C₀ m := by
    unfold maxPhiDenOf phiDenHalf
    have heq : (↑(3 * max (thr + 1) (200 * K_nat * (Nat.log 2 (4 * m + 2) + 2) ^ (K_nat * (rOf (4 * m)) ^ 2))) : ℝ) =
        3 * max ((thr : ℝ) + 1) (200 * (K_nat : ℝ) * ((Nat.log 2 (4 * m + 2) + 2 : ℕ) : ℝ) ^
          (K_nat * (rOf (4 * m)) ^ 2)) := by
      push_cast; ring
    rw [heq]
    linarith
  exact h3max

lemma subpolyB1_le_linear (C : ℝ) (hC : 0 ≤ C) :
    ∃ C_lin : ℕ, 1 ≤ C_lin ∧ ∀ m : ℕ, subpolyB1 C m ≤ (C_lin : ℝ) * ((m : ℝ) + 2) := by
  let M₀ : ℝ := max 1 (12 * C)
  let C_lin : ℕ := max 1 (Nat.ceil (Real.exp (12 * C * M₀ ^ 5)))
  refine ⟨C_lin, le_max_left _ _, fun m => ?_⟩
  set L : ℝ := Real.log ((m : ℝ) + 2)
  have hL_half : 1 / 2 ≤ L := half_le_log_add_two_nat m
  have hL_pos : 0 < L := by linarith
  have hlog_sub : Real.log (L + 2) ≤ 6 * (L + 2) ^ (1 / 6 : ℝ) := by
    have hp : 0 < (L + 2) ^ (1 / 6 : ℝ) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hp
    have h2 : Real.log ((L + 2) ^ (1 / 6 : ℝ)) = (1 / 6 : ℝ) * Real.log (L + 2) :=
      Real.log_rpow (by linarith) _
    linarith
  have hL2_le : (L + 2) ^ (1 / 6 : ℝ) ≤ 2 * L ^ (1 / 6 : ℝ) := by
    have h1 : L + 2 ≤ 5 * L := by linarith
    have h2 := Real.rpow_le_rpow (by linarith) h1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [Real.mul_rpow (by norm_num) hL_pos.le] at h2
    have h5 : (5 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
      rw [← Real.rpow_le_rpow_iff (z := (6 : ℝ)) (by positivity) (by norm_num) (by norm_num)]
      have : ((5 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℝ) = 5 := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]
      norm_num
    exact le_trans h2 (mul_le_mul_of_nonneg_right h5 (by positivity))
  have hexp_bound : C * L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤ 12 * C * L ^ (5 / 6 : ℝ) := by
    have hrpow_mul : L ^ (2 / 3 : ℝ) * L ^ (1 / 6 : ℝ) = L ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_add hL_pos]
      norm_num
    calc C * L ^ (2 / 3 : ℝ) * Real.log (L + 2)
        ≤ C * L ^ (2 / 3 : ℝ) * (6 * (2 * L ^ (1 / 6 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left (le_trans hlog_sub (by linarith)) (by positivity)
      _ = 12 * C * (L ^ (2 / 3 : ℝ) * L ^ (1 / 6 : ℝ)) := by ring
      _ = 12 * C * L ^ (5 / 6 : ℝ) := by rw [hrpow_mul]
  unfold subpolyB1
  change Real.exp (C * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤ (C_lin : ℝ) * ((m : ℝ) + 2)
  by_cases hL_le : L ^ (1 / 6 : ℝ) ≤ M₀
  · have h56 : L ^ (5 / 6 : ℝ) ≤ M₀ ^ 5 := by
      have heq : L ^ (5 / 6 : ℝ) = (L ^ (1 / 6 : ℝ)) ^ (5 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
        norm_num
      rw [heq]
      exact pow_le_pow_left₀ (by positivity) hL_le 5
    have h1 : Real.exp (C * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤ Real.exp (12 * C * M₀ ^ 5) :=
      Real.exp_le_exp.mpr (le_trans hexp_bound (mul_le_mul_of_nonneg_left h56 (by positivity)))
    have h2 : Real.exp (12 * C * M₀ ^ 5) ≤ (C_lin : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 _)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    nlinarith [le_trans h1 h2]
  · have hM_lt : 12 * C ≤ L ^ (1 / 6 : ℝ) := le_trans (le_max_right 1 (12 * C)) (le_of_not_ge hL_le)
    have hprod : 12 * C * L ^ (5 / 6 : ℝ) ≤ L := by
      have heq : L ^ (1 / 6 : ℝ) * L ^ (5 / 6 : ℝ) = L := by
        rw [← Real.rpow_add hL_pos]
        norm_num
      exact le_trans (mul_le_mul_of_nonneg_right hM_lt (by positivity)) (le_of_eq heq)
    have h1 : Real.exp (C * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤ Real.exp L :=
      Real.exp_le_exp.mpr (le_trans hexp_bound hprod)
    rw [Real.exp_log (by positivity)] at h1
    have hc1 : (1 : ℝ) ≤ (C_lin : ℝ) := by exact_mod_cast le_max_left 1 _
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) + 2 by positivity]

lemma maxPhiDenOf_le_linear (K_nat thr : ℕ) :
    ∃ C_phi : ℕ, 1 ≤ C_phi ∧ ∀ m : ℕ, maxPhiDenOf K_nat thr m ≤ C_phi * (m + 2) ^ 1 := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hsb⟩ := maxPhiDenOf_le_subpoly K_nat thr
  obtain ⟨C_lin, hClin, hlin⟩ := subpolyB1_le_linear C₀ hC₀.le
  let C_phi : ℕ := max 1 (Nat.ceil C₁ * C_lin)
  refine ⟨C_phi, le_max_left _ _, fun m => ?_⟩
  have hsb_nn : 0 ≤ subpolyB1 C₀ m := by unfold subpolyB1; positivity
  have hR : (maxPhiDenOf K_nat thr m : ℝ) ≤ (C_phi : ℝ) * ((m : ℝ) + 2) := by
    calc (maxPhiDenOf K_nat thr m : ℝ)
        ≤ C₁ * subpolyB1 C₀ m := hsb m
      _ ≤ (Nat.ceil C₁ : ℝ) * ((C_lin : ℝ) * ((m : ℝ) + 2)) :=
          mul_le_mul (Nat.le_ceil C₁) (hlin m) hsb_nn (by positivity)
      _ = ((Nat.ceil C₁ * C_lin : ℕ) : ℝ) * ((m : ℝ) + 2) := by push_cast; ring
      _ ≤ (C_phi : ℝ) * ((m : ℝ) + 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast le_max_right 1 _
  have hcast : (maxPhiDenOf K_nat thr m : ℝ) ≤ ((C_phi * (m + 2) ^ 1 : ℕ) : ℝ) := by
    simpa [pow_one, Nat.cast_mul, Nat.cast_add] using hR
  exact_mod_cast hcast

end MinCostFlow.Expander
