module

public import MinCostFlow.Expander.PathDSProg.Params

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Asymptotic Parameter Bounds and Fallback Cost Obstruction for `PathDSProg`

Proves the asymptotic parameter envelopes for `pathDSParams` (`Params.lean`):

1. `csExpFactor_le_exp_seven_eighths`: `csExpFactor Kγ K_int M ≤ exp(C_cs * log(M + 2)^{7/8})`.
2. `fbCostBound_le_exp_eight_ninths`: in the `Decompose` regime (`phi_in ≥ phiB1`),
   `fbCostBound d ≤ exp(C_fb * log(M + 2)^{8/9} * log(log(M + 2) + 2)^{4/3}) = M^{o(1)}`.
3. `gExpImpl_le_exp_seven_eighths_of_le`: for constant-conductance calls (`d ≤ D_0`, e.g. `φ_Const`),
   `gExpImpl Kγ c K_int d M ≤ exp(C_p * log(M + 2)^{7/8})`, through `lenFactor_le_exp` and
   `gExpImpl_le_exp_of_phiOut`.
4. `fallback_cost_forces_gamma_ge_n`: formal proof that if `GetPath` (`op 1`) takes `≥ G.n`
   steps on an `initPre`-valid graph (as `bfsPathProc` does via `Work[0..n-1]` zeroing),
   then `G.n - 1 ≤ K_query * γ_ExpPath (phiNum / phiDen) M` — preventing `exp(O(log^{7/8} M))`
   when `φ_in = csPhi Kγ c (3 * M)` and `G.m = M`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open MinCostFlow.Cited MinCostFlow.Spanner

private lemma half_le_log_add_two (M : ℕ) : (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) := by
  have h1 : (2 : ℝ) ≤ (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have h2 : Real.log 2 ≤ Real.log ((M : ℝ) + 2) := Real.log_le_log (by norm_num) h1
  linarith [Real.log_two_gt_d9]

private lemma two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]

private lemma three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  have hsq : (4 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith
  rw [← Real.exp_nat_mul] at hsq
  norm_num at hsq
  linarith

private lemma ten8_le_exp_30 : (2000000000 : ℝ) ≤ Real.exp 30 := by
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h30 : (2.7 : ℝ) ^ 30 ≤ (Real.exp 1) ^ 30 := pow_le_pow_left₀ (by norm_num) he1 30
  rw [← Real.exp_nat_mul, mul_one] at h30
  exact le_trans (by norm_num) h30

private lemma fbCostBound_le_poly {d : ℕ} (hd : 1 ≤ d) :
    fbCostBound d ≤ 2000000000 * (zStarImpl d + 1) * (d + 1) ^ 2 * (zStarExp d + 2) ^ 2 := by
  unfold fbCostBound pruneTimeBound
  dsimp only
  set z := zStarImpl d
  set b := zStarExp d
  set Hfb := 4 * (40 * d + 1) * (b + 2) + 2
  have h1 : 1 ≤ (d + 1) := by omega
  have h2 : 2 ≤ (b + 2) := by omega
  have hdb : 2 ≤ (d + 1) * (b + 2) := by nlinarith
  have hH_le : Hfb ≤ 200 * (d + 1) * (b + 2) := by
    dsimp [Hfb]
    have : 4 * (40 * d + 1) ≤ 160 * (d + 1) := by omega
    nlinarith
  have hp1 : 4 * Hfb + 14 ≤ 1000 * (d + 1) * (b + 2) := by nlinarith
  have hp2 : 4 * Hfb + 4 ≤ 1000 * (d + 1) * (b + 2) := by nlinarith
  have hmul : (4 * Hfb + 14) * (4 * Hfb + 4) ≤ 1000000 * (d + 1) ^ 2 * (b + 2) ^ 2 := by
    have hm := Nat.mul_le_mul hp1 hp2
    nlinarith [show (1000 * (d + 1) * (b + 2)) * (1000 * (d + 1) * (b + 2)) =
      1000000 * (d + 1) ^ 2 * (b + 2) ^ 2 by ring]
  have hz3 : 2 * z + 1 ≤ 3 * (z + 1) := by omega
  have hmul3 : (4 * Hfb + 14) * (4 * Hfb + 4) * (2 * z + 1) ≤
      (1000000 * (d + 1) ^ 2 * (b + 2) ^ 2) * (3 * (z + 1)) :=
    Nat.mul_le_mul hmul hz3
  have hbig : 360 * ((4 * Hfb + 14) * (4 * Hfb + 4) * (2 * z + 1)) ≤
      1080000000 * (z + 1) * (d + 1) ^ 2 * (b + 2) ^ 2 := by
    nlinarith
  have hrest : 170 * (2 * z) + 140 * z + 30 * (Hfb + 1) + 221 + 2000 * z + 10 * d + 1000 ≤
      100000 * (z + 1) * (d + 1) ^ 2 * (b + 2) ^ 2 := by
    have hz1 : 1 ≤ z + 1 := by omega
    have hdb2 : 1 ≤ (d + 1) ^ 2 * (b + 2) ^ 2 := by nlinarith
    have hlin : 170 * (2 * z) + 140 * z + 30 * (Hfb + 1) + 221 + 2000 * z + 10 * d + 1000 ≤
        2500 * (z + 1) + 6030 * (d + 1) * (b + 2) + 1300 := by
      nlinarith
    have ha : (z + 1) ≤ (z + 1) * (d + 1) ^ 2 * (b + 2) ^ 2 := by nlinarith
    have hb : (d + 1) * (b + 2) ≤ (z + 1) * (d + 1) ^ 2 * (b + 2) ^ 2 := by nlinarith
    have hc : 1 ≤ (z + 1) * (d + 1) ^ 2 * (b + 2) ^ 2 := by nlinarith
    nlinarith
  nlinarith

private lemma two_le_exp_twenty_E {E : ℝ} (hE : 0.1 ≤ E) : (2 : ℝ) ≤ Real.exp (20 * E) :=
  le_trans (le_trans (by norm_num) three_le_exp_two) (Real.exp_le_exp.mpr (by linarith))

private lemma three_le_exp_twenty_E {E : ℝ} (hE : 0.1 ≤ E) : (3 : ℝ) ≤ Real.exp (20 * E) :=
  le_trans three_le_exp_two (Real.exp_le_exp.mpr (by linarith))

private lemma twoe9_le_exp_300_E {E : ℝ} (hE : 0.1 ≤ E) : (2000000000 : ℝ) ≤ Real.exp (300 * E) :=
  le_trans ten8_le_exp_30 (Real.exp_le_exp.mpr (by linarith))

private lemma rpow_nat_pow_eq {x : ℝ} (hx : 0 ≤ x) {p : ℝ} {n q : ℕ}
    (hpq : p * (n : ℝ) = (q : ℝ)) : (x ^ p) ^ n = x ^ q := by
  rw [← Real.rpow_natCast (x ^ p), ← Real.rpow_mul hx, hpq, Real.rpow_natCast]

/-- `csExpFactor Kγ K_int M` grows as `exp(O(log(M + 2)^{7/8}))` for every `M`. -/
lemma csExpFactor_le_exp_seven_eighths (Kγ K_int : ℕ) :
    ∃ C_cs : ℝ, 0 < C_cs ∧
      ∀ M : ℕ, (csExpFactor Kγ K_int M : ℝ) ≤
        Real.exp (C_cs * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases csGamma_four_mul_le_exp_three_quarters Kγ with ⟨C_g, hCg, hg⟩
  set C_0 : ℝ := 6 * (K_int : ℝ) * C_g + 6 ^ 7 + 4
  refine ⟨C_0 + 4, by positivity, fun M => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two M
  have hL_pos : 0 < L := by linarith
  have hL78_pos : 0 < L ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have hL18_pos : 0 < L ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have hq_bd := (qOf_bounds M).2
  have hqr1 : ((qRoot M + 1 : ℕ) : ℝ) ≤ (qOf M : ℝ) := by
    rw [qOf_eq_qRoot_add_two]
    exact_mod_cast (by omega : qRoot M + 1 ≤ qRoot M + 2)
  have hq7 : ((qRoot M + 1 : ℕ) : ℝ) ^ 7 ≤ (6 : ℝ) ^ 7 * L ^ (7 / 8 : ℝ) := by
    have h1 : ((qRoot M + 1 : ℕ) : ℝ) ≤ 6 * L ^ (1 / 8 : ℝ) := le_trans hqr1 hq_bd
    have h2 : ((qRoot M + 1 : ℕ) : ℝ) ^ 7 ≤ (6 * L ^ (1 / 8 : ℝ)) ^ 7 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 7
    have hpow7 : (6 * L ^ (1 / 8 : ℝ)) ^ 7 = (6 : ℝ) ^ 7 * (L ^ (1 / 8 : ℝ)) ^ 7 := by ring
    have h78 : (L ^ (1 / 8 : ℝ)) ^ (7 : ℕ) = L ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; norm_num
    rw [hpow7, h78] at h2
    exact h2
  have hpart1 : ((Cited.csGamma Kγ (4 * M) : ℕ) : ℝ) ^ (K_int * qOf M) ≤
      Real.exp (6 * (K_int : ℝ) * C_g * L ^ (7 / 8 : ℝ)) := by
    have h1 : (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K_int * qOf M) ≤
        (Real.exp (C_g * L ^ (3 / 4 : ℝ))) ^ (K_int * qOf M) :=
      pow_le_pow_left₀ (by unfold Cited.csGamma; positivity) (hg M) _
    rw [← Real.exp_nat_mul] at h1
    refine le_trans h1 (Real.exp_le_exp.mpr ?_)
    have hmul_le : ((K_int * qOf M : ℕ) : ℝ) * (C_g * L ^ (3 / 4 : ℝ)) ≤
        (K_int : ℝ) * (6 * L ^ (1 / 8 : ℝ)) * (C_g * L ^ (3 / 4 : ℝ)) := by
      push_cast
      have hL34 : 0 ≤ C_g * L ^ (3 / 4 : ℝ) := by positivity
      gcongr
    have hadd_exp : L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ) = L ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hL_pos]; norm_num
    calc ((K_int * qOf M : ℕ) : ℝ) * (C_g * L ^ (3 / 4 : ℝ))
        ≤ (K_int : ℝ) * (6 * L ^ (1 / 8 : ℝ)) * (C_g * L ^ (3 / 4 : ℝ)) := hmul_le
      _ = 6 * (K_int : ℝ) * C_g * (L ^ (1 / 8 : ℝ) * L ^ (3 / 4 : ℝ)) := by ring
      _ = 6 * (K_int : ℝ) * C_g * L ^ (7 / 8 : ℝ) := by rw [hadd_exp]
  have h12 : (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
    have h7 : (1 / 2 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL_ge 7
    have hlow : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ L ^ 7 :=
      le_trans (by norm_num : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (1 / 2 : ℝ) ^ 7) h7
    have hpow8 : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) := by
      have : (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) = L ^ (7 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le, ← Real.rpow_natCast]
        congr 1; norm_num
      rw [this]
      exact hlow
    exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) hL78_pos.le hpow8
  have hpart2 : ((2 ^ qExpPow M : ℕ) : ℝ) ≤
      Real.exp (((6 : ℝ) ^ 7 + 4) * L ^ (7 / 8 : ℝ)) := by
    have h2e : ((2 ^ qExpPow M : ℕ) : ℝ) ≤ Real.exp (qExpPow M : ℝ) := by
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
      calc ((2 ^ qExpPow M : ℕ) : ℝ) = (2 : ℝ) ^ qExpPow M := by norm_cast
        _ ≤ (Real.exp 1) ^ qExpPow M := pow_le_pow_left₀ (by norm_num) h2le _
        _ = Real.exp (qExpPow M : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    refine le_trans h2e (Real.exp_le_exp.mpr ?_)
    push_cast at hq7
    unfold qExpPow
    push_cast
    linarith
  set E_cs : ℕ := csGammaExp Kγ (4 * M) * K_int * qOf M
  set E_all : ℕ := E_cs + qExpPow M
  have hprod_eq : ((2 ^ E_all : ℕ) : ℝ) =
      ((Cited.csGamma Kγ (4 * M) : ℕ) : ℝ) ^ (K_int * qOf M) * ((2 ^ qExpPow M : ℕ) : ℝ) := by
    rw [csGamma_eq_two_pow]
    have hnat : 2 ^ E_all = (2 ^ csGammaExp Kγ (4 * M)) ^ (K_int * qOf M) * 2 ^ qExpPow M := by
      dsimp [E_all, E_cs]
      rw [pow_add, mul_assoc, pow_mul]
    exact_mod_cast hnat
  have hpow_le : ((2 ^ E_all : ℕ) : ℝ) ≤ Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by
    rw [hprod_eq]
    calc ((Cited.csGamma Kγ (4 * M) : ℕ) : ℝ) ^ (K_int * qOf M) * ((2 ^ qExpPow M : ℕ) : ℝ)
        ≤ Real.exp (6 * (K_int : ℝ) * C_g * L ^ (7 / 8 : ℝ)) *
            Real.exp (((6 : ℝ) ^ 7 + 4) * L ^ (7 / 8 : ℝ)) := by gcongr
      _ = Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by
          rw [← Real.exp_add]; congr 1; dsimp [C_0]; ring
  have h1_le : (1 : ℝ) ≤ Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by
    apply Real.one_le_exp
    have hK0 : (0 : ℝ) ≤ (K_int : ℝ) := Nat.cast_nonneg _
    have hC0_nn : 0 ≤ C_0 := add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hCg.le) (by norm_num)) (by norm_num)
    exact mul_nonneg hC0_nn hL78_pos.le
  have hcs_eq : (csExpFactor Kγ K_int M : ℝ) = ((2 ^ E_all : ℕ) : ℝ) + 1 := by
    dsimp [csExpFactor, E_all, E_cs]
    rw [Nat.cast_add, Nat.cast_one]
  have hdouble : (csExpFactor Kγ K_int M : ℝ) ≤ 2 * Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by
    rw [hcs_eq]
    linarith
  have h2_le_exp : (2 : ℝ) ≤ Real.exp (4 * L ^ (7 / 8 : ℝ)) := by
    have h2e : (2 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
      exact le_trans h1 (Real.exp_le_exp.mpr (by norm_num))
    exact le_trans h2e (Real.exp_le_exp.mpr (by linarith))
  calc (csExpFactor Kγ K_int M : ℝ)
      ≤ Real.exp (4 * L ^ (7 / 8 : ℝ)) * Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by
        calc (csExpFactor Kγ K_int M : ℝ) ≤ 2 * Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := hdouble
          _ ≤ Real.exp (4 * L ^ (7 / 8 : ℝ)) * Real.exp (C_0 * L ^ (7 / 8 : ℝ)) := by gcongr
    _ = Real.exp ((C_0 + 4) * L ^ (7 / 8 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

lemma real_E_lower_and_L23 {L LL : ℝ} (hL_ge : (1 / 2 : ℝ) ≤ L) (hLL_ge : (1 / 2 : ℝ) ≤ LL) :
    (0.1 : ℝ) ≤ L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) ∧
      L ^ (2 / 3 : ℝ) * LL ≤ 4 * (L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ)) := by
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hE_ge : (0.1 : ℝ) ≤ L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by
    have hL89 : (1 / 2 : ℝ) ≤ L ^ (8 / 9 : ℝ) := by
      have hp : (1 / 2 : ℝ) ^ (9 : ℕ) ≤ (L ^ (8 / 9 : ℝ)) ^ (9 : ℕ) := by
        rw [rpow_nat_pow_eq hL_pos.le (by norm_num : (8 / 9 : ℝ) * (9 : ℕ) = (8 : ℕ))]
        have : (1 / 2 : ℝ) ^ 9 ≤ (1 / 2 : ℝ) ^ 8 := by norm_num
        linarith [pow_le_pow_left₀ (by norm_num) hL_ge 8]
      exact le_of_pow_le_pow_left₀ (by decide : 9 ≠ 0) (by positivity) hp
    have hLL43 : (0.3 : ℝ) ≤ LL ^ (4 / 3 : ℝ) := by
      have hp : (0.3 : ℝ) ^ (3 : ℕ) ≤ (LL ^ (4 / 3 : ℝ)) ^ (3 : ℕ) := by
        rw [rpow_nat_pow_eq hLL_pos.le (by norm_num : (4 / 3 : ℝ) * (3 : ℕ) = (4 : ℕ))]
        have : (0.3 : ℝ) ^ 3 ≤ (1 / 2 : ℝ) ^ 4 := by norm_num
        linarith [pow_le_pow_left₀ (by norm_num) hLL_ge 4]
      exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) hp
    nlinarith
  have hL23_le : L ^ (2 / 3 : ℝ) * LL ≤ 4 * (L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ)) := by
    have hL29 : (1 / 2 : ℝ) ≤ L ^ (2 / 9 : ℝ) := by
      have hp : (1 / 2 : ℝ) ^ (9 : ℕ) ≤ (L ^ (2 / 9 : ℝ)) ^ (9 : ℕ) := by
        rw [rpow_nat_pow_eq hL_pos.le (by norm_num : (2 / 9 : ℝ) * (9 : ℕ) = (2 : ℕ))]
        have : (1 / 2 : ℝ) ^ 9 ≤ (1 / 2 : ℝ) ^ 2 := by norm_num
        linarith [pow_le_pow_left₀ (by norm_num) hL_ge 2]
      exact le_of_pow_le_pow_left₀ (by decide : 9 ≠ 0) (by positivity) hp
    have hLL13 : (1 / 2 : ℝ) ≤ LL ^ (1 / 3 : ℝ) := by
      have hp : (1 / 2 : ℝ) ^ (3 : ℕ) ≤ (LL ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
        rw [rpow_nat_pow_eq hLL_pos.le (by norm_num : (1 / 3 : ℝ) * (3 : ℕ) = (1 : ℕ)), pow_one]
        have : (1 / 2 : ℝ) ^ (3 : ℕ) ≤ 1 / 2 := by norm_num
        linarith
      exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) hp
    have hprod : L ^ (2 / 3 : ℝ) * LL * (L ^ (2 / 9 : ℝ) * LL ^ (1 / 3 : ℝ)) =
        L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by
      have ha : L ^ (2 / 3 : ℝ) * L ^ (2 / 9 : ℝ) = L ^ (8 / 9 : ℝ) := by
        rw [← Real.rpow_add hL_pos]; norm_num
      have hb1 : LL * LL ^ (1 / 3 : ℝ) = LL ^ (4 / 3 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one LL]
        rw [← Real.rpow_add hLL_pos]; norm_num
      calc L ^ (2 / 3 : ℝ) * LL * (L ^ (2 / 9 : ℝ) * LL ^ (1 / 3 : ℝ))
          = (L ^ (2 / 3 : ℝ) * L ^ (2 / 9 : ℝ)) * (LL * LL ^ (1 / 3 : ℝ)) := by ring
        _ = L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by rw [ha, hb1]
    have hfac : (1 / 4 : ℝ) ≤ L ^ (2 / 9 : ℝ) * LL ^ (1 / 3 : ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ L ^ (2 / 3 : ℝ) * LL)]
  exact ⟨hE_ge, hL23_le⟩

private lemma fb_combine_real {fb zImpl zExp d C_z D_exp E : ℝ}
    (hE_ge : (0.1 : ℝ) ≤ E) (hCz : 0 ≤ C_z) (hD : 0 ≤ D_exp)
    (hz_nn : 0 ≤ zImpl) (hd_nn : 0 ≤ d) (hb_nn : 0 ≤ zExp)
    (hb_le : zExp ≤ C_z * E) (hz_le : zImpl ≤ Real.exp (C_z * E))
    (hd_le : d ≤ Real.exp (D_exp * E))
    (hfb_poly : fb ≤ 2000000000 * (zImpl + 1) * (d + 1) ^ 2 * (zExp + 2) ^ 2) :
    fb ≤ Real.exp ((300 + 3 * C_z + 2 * D_exp + 100) * E) := by
  have hE_nn : 0 ≤ E := by linarith
  have h2e : (2 : ℝ) ≤ Real.exp (20 * E) := two_le_exp_twenty_E hE_ge
  have h3e : (3 : ℝ) ≤ Real.exp (20 * E) := three_le_exp_twenty_E hE_ge
  have hconst_exp : (2000000000 : ℝ) ≤ Real.exp (300 * E) := twoe9_le_exp_300_E hE_ge
  have hexpC : 1 ≤ Real.exp (C_z * E) := Real.one_le_exp (mul_nonneg hCz hE_nn)
  have hexpD : 1 ≤ Real.exp (D_exp * E) := Real.one_le_exp (mul_nonneg hD hE_nn)
  have hb_lin_le : zExp + 2 ≤ Real.exp (C_z * E + 20 * E) := by
    have hle : zExp + 2 ≤ Real.exp zExp + 2 :=
      add_le_add (by linarith [Real.add_one_le_exp zExp]) le_rfl
    have hex2 : Real.exp zExp ≤ Real.exp (C_z * E) := Real.exp_le_exp.mpr hb_le
    have h3 : Real.exp zExp + 2 ≤ 3 * Real.exp (C_z * E) := by linarith
    calc zExp + 2 ≤ 3 * Real.exp (C_z * E) := le_trans hle h3
      _ ≤ Real.exp (20 * E) * Real.exp (C_z * E) :=
          mul_le_mul_of_nonneg_right h3e (Real.exp_pos _).le
      _ = Real.exp (C_z * E + 20 * E) := by rw [← Real.exp_add]; ring_nf
  have hz_add : zImpl + 1 ≤ Real.exp (C_z * E + 20 * E) := by
    calc zImpl + 1 ≤ 2 * Real.exp (C_z * E) := by linarith
      _ ≤ Real.exp (20 * E) * Real.exp (C_z * E) :=
          mul_le_mul_of_nonneg_right h2e (Real.exp_pos _).le
      _ = Real.exp (C_z * E + 20 * E) := by rw [← Real.exp_add]; ring_nf
  have hd_add : d + 1 ≤ Real.exp (D_exp * E + 20 * E) := by
    calc d + 1 ≤ 2 * Real.exp (D_exp * E) := by linarith
      _ ≤ Real.exp (20 * E) * Real.exp (D_exp * E) :=
          mul_le_mul_of_nonneg_right h2e (Real.exp_pos _).le
      _ = Real.exp (D_exp * E + 20 * E) := by rw [← Real.exp_add]; ring_nf
  calc fb
      ≤ 2000000000 * (zImpl + 1) * (d + 1) ^ 2 * (zExp + 2) ^ 2 := hfb_poly
    _ ≤ Real.exp (300 * E) * Real.exp (C_z * E + 20 * E) *
          (Real.exp (D_exp * E + 20 * E)) ^ 2 * (Real.exp (C_z * E + 20 * E)) ^ 2 := by
        gcongr
    _ = Real.exp ((300 + 3 * C_z + 2 * D_exp + 100) * E) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring

/-- Subpolynomial `exp(O(log^{8/9}(M+2) * log(log(M+2)+2)^{4/3}))` upper bound on `fbCostBound d`
whenever `1 / φ_in ≤ C₁ * exp(C₀ * log(M+2)^{2/3} * log(log(M+2)+2))` (the `Decompose` regime). -/
lemma fbCostBound_le_exp_eight_ninths (C₀ C₁ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C_fb : ℝ, 0 < C_fb ∧
      ∀ (M d : ℕ), 1 ≤ d →
        (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
        (fbCostBound d : ℝ) ≤
          Real.exp (C_fb * Real.log ((M : ℝ) + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log ((M : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) := by
  have hlog2_pos : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set K_lin : ℝ := max (8 * Real.log (20 * C₁ + 40) + 16) (2 * C₀ + 2)
  have hK_lin : 0 < K_lin := lt_max_of_lt_right (by positivity)
  set C_z : ℝ := 40 * K_lin ^ (4 / 3 : ℝ) + 8
  set C_fb : ℝ := 100 * C_z + 100 * C₀ + 200 * Real.log (C₁ + 10) + 1000
  have hlogC1_nn : 0 ≤ Real.log (C₁ + 10) := Real.log_nonneg (by linarith)
  refine ⟨C_fb, by positivity, fun M d hd hbd => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  set LL : ℝ := Real.log (L + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two M
  have hL_pos : 0 < L := by linarith
  have hLL_ge : (1 / 2 : ℝ) ≤ LL := by
    have : (2 : ℝ) ≤ L + 2 := by linarith
    exact le_trans hlog2_pos (Real.log_le_log (by norm_num) this)
  have hLL_pos : 0 < LL := by linarith
  have hL_e : (1 / 4 : ℝ) ≤ L ^ (2 / 3 : ℝ) * LL := by
    have h23 : (1 / 2 : ℝ) ≤ L ^ (2 / 3 : ℝ) := by
      have hpow : ((1 / 2 : ℝ) ^ (3 : ℕ)) ≤ (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) := by
        rw [rpow_nat_pow_eq hL_pos.le (by norm_num : (2 / 3 : ℝ) * (3 : ℕ) = (2 : ℕ))]
        nlinarith
      exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (Real.rpow_nonneg hL_pos.le _) hpow
    nlinarith
  have hd_bound : (10 * d + 2 : ℝ) ≤
      (20 * C₁ + 40) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL) := by
    have hexp1 : 1 ≤ Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL) := Real.one_le_exp (by positivity)
    linarith
  have h10d_log : Real.log (10 * (d : ℝ) + 2) ≤ K_lin * L ^ (2 / 3 : ℝ) * LL := by
    have h1 : Real.log (10 * (d : ℝ) + 2) ≤
        Real.log ((20 * C₁ + 40) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL)) :=
      Real.log_le_log (by positivity) hd_bound
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
    have h_a : Real.log (20 * C₁ + 40) ≤ (K_lin / 2) * L ^ (2 / 3 : ℝ) * LL := by
      have hk1 : 8 * Real.log (20 * C₁ + 40) + 16 ≤ K_lin := le_max_left _ _
      have hln : 0 ≤ Real.log (20 * C₁ + 40) := Real.log_nonneg (by linarith)
      have hprod_ge : 1 ≤ 4 * (L ^ (2 / 3 : ℝ) * LL) := by linarith
      have : Real.log (20 * C₁ + 40) ≤ (K_lin / 8) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hL_e (by positivity : 0 ≤ K_lin / 2)]
    have h_b : C₀ * L ^ (2 / 3 : ℝ) * LL ≤ (K_lin / 2) * L ^ (2 / 3 : ℝ) * LL := by
      have hk2 : 2 * C₀ + 2 ≤ K_lin := le_max_right _ _
      have hnn : 0 ≤ L ^ (2 / 3 : ℝ) * LL := by positivity
      nlinarith
    linarith
  have hlog2_nat : (Nat.log 2 (10 * d) : ℝ) + 1 ≤ 4 * K_lin * L ^ (2 / 3 : ℝ) * LL := by
    have hpow_d : (2 : ℝ) ^ (Nat.log 2 (10 * d)) ≤ 10 * (d : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hnlog : (Nat.log 2 (10 * d) : ℝ) * Real.log 2 ≤ Real.log (10 * (d : ℝ) + 2) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlog_nat : (Nat.log 2 (10 * d) : ℝ) ≤ 2 * K_lin * L ^ (2 / 3 : ℝ) * LL := by
      nlinarith
    have h1_le : (1 : ℝ) ≤ 2 * K_lin * L ^ (2 / 3 : ℝ) * LL := by
      have hk : (2 : ℝ) ≤ K_lin := le_trans (by linarith) (le_max_right _ _)
      nlinarith
    linarith
  have hb_exp : (zStarExp d : ℝ) ≤ (4 * K_lin * L ^ (2 / 3 : ℝ) * LL) ^ (4 / 3 : ℝ) := by
    have h3 : ((zStarExp d : ℝ) ^ 3) ≤ ((Nat.log 2 (10 * d) : ℝ) + 1) ^ 4 := by
      exact_mod_cast (natCbrtFloor_spec ((Nat.log 2 (10 * d) + 1) ^ 4)).1
    have h4 : ((Nat.log 2 (10 * d) : ℝ) + 1) ^ 4 ≤ (4 * K_lin * L ^ (2 / 3 : ℝ) * LL) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hlog2_nat 4
    have h3r : ((zStarExp d : ℝ) ^ (3 : ℕ)) ≤
        ((4 * K_lin * L ^ (2 / 3 : ℝ) * LL) ^ (4 / 3 : ℝ)) ^ (3 : ℕ) := by
      rw [rpow_nat_pow_eq (by positivity) (by norm_num : (4 / 3 : ℝ) * (3 : ℕ) = (4 : ℕ))]
      linarith
    exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) h3r
  have hb_le : (zStarExp d : ℝ) ≤ C_z * L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by
    have hsplit : (4 * K_lin * L ^ (2 / 3 : ℝ) * LL) ^ (4 / 3 : ℝ) =
        (4 * K_lin) ^ (4 / 3 : ℝ) * (L ^ (2 / 3 : ℝ)) ^ (4 / 3 : ℝ) * LL ^ (4 / 3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    have hL89 : (L ^ (2 / 3 : ℝ)) ^ (4 / 3 : ℝ) = L ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_mul hL_pos.le]; norm_num
    have h4K : (4 * K_lin) ^ (4 / 3 : ℝ) ≤ C_z := by
      have hmul : (4 * K_lin) ^ (4 / 3 : ℝ) = (4 : ℝ) ^ (4 / 3 : ℝ) * K_lin ^ (4 / 3 : ℝ) :=
        Real.mul_rpow (by norm_num) hK_lin.le
      have h4le : (4 : ℝ) ^ (4 / 3 : ℝ) ≤ 8 := by
        have hp : ((4 : ℝ) ^ (4 / 3 : ℝ)) ^ (3 : ℕ) ≤ (8 : ℝ) ^ (3 : ℕ) := by
          rw [rpow_nat_pow_eq (by norm_num) (by norm_num : (4 / 3 : ℝ) * (3 : ℕ) = (4 : ℕ))]
          norm_num
        exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) hp
      rw [hmul]
      have hk1 : K_lin ^ (4 / 3 : ℝ) ≥ 0 := by positivity
      dsimp [C_z]
      nlinarith
    calc (zStarExp d : ℝ)
        ≤ (4 * K_lin * L ^ (2 / 3 : ℝ) * LL) ^ (4 / 3 : ℝ) := hb_exp
      _ = (4 * K_lin) ^ (4 / 3 : ℝ) * L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by
          rw [hsplit, hL89]
      _ ≤ C_z * L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ) := by gcongr
  have ⟨hE_ge, hL23_le_E⟩ := real_E_lower_and_L23 hL_ge hLL_ge
  let E : ℝ := L ^ (8 / 9 : ℝ) * LL ^ (4 / 3 : ℝ)
  have hb_le' : (zStarExp d : ℝ) ≤ C_z * E := by
    simpa [E, mul_assoc] using hb_le
  have hz_le : (zStarImpl d : ℝ) ≤ Real.exp (C_z * E) := by
    have h2e : (zStarImpl d : ℝ) ≤ Real.exp (zStarExp d : ℝ) := by
      have h2le : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
      calc (zStarImpl d : ℝ) = (2 : ℝ) ^ zStarExp d := by unfold zStarImpl; norm_cast
        _ ≤ (Real.exp 1) ^ zStarExp d := pow_le_pow_left₀ (by norm_num) h2le _
        _ = Real.exp (zStarExp d : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    exact le_trans h2e (Real.exp_le_exp.mpr hb_le')
  set D_exp : ℝ := 10 * Real.log (C₁ + 10) + 4 * C₀ + 10
  have hd_le_exp : (d : ℝ) ≤ Real.exp (D_exp * E) := by
    have h1 : (d : ℝ) ≤ (C₁ + 10) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL) := by
      have := Real.one_le_exp (by positivity : 0 ≤ C₀ * L ^ (2 / 3 : ℝ) * LL)
      linarith
    have hlogC : C₁ + 10 ≤ Real.exp (10 * Real.log (C₁ + 10) * E) := by
      have : Real.log (C₁ + 10) ≤ 10 * Real.log (C₁ + 10) * E := by
        nlinarith [hE_ge, hlogC1_nn]
      calc C₁ + 10 = Real.exp (Real.log (C₁ + 10)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (10 * Real.log (C₁ + 10) * E) := Real.exp_le_exp.mpr this
    have hexp_C0 : Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL) ≤ Real.exp (4 * C₀ * E) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hL23_le_E hC₀.le
      linarith
    calc (d : ℝ) ≤ (C₁ + 10) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * LL) := h1
      _ ≤ Real.exp (10 * Real.log (C₁ + 10) * E) * Real.exp (4 * C₀ * E) :=
          mul_le_mul hlogC hexp_C0 (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ Real.exp (D_exp * E) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h10 : 10 * Real.log (C₁ + 10) * E + 4 * C₀ * E =
              (10 * Real.log (C₁ + 10) + 4 * C₀) * E := by ring
          rw [h10]
          exact mul_le_mul_of_nonneg_right (by dsimp [D_exp]; linarith) (by positivity)
  have hfb_poly : (fbCostBound d : ℝ) ≤
      2000000000 * ((zStarImpl d : ℝ) + 1) * ((d : ℝ) + 1) ^ 2 * ((zStarExp d : ℝ) + 2) ^ 2 := by
    exact_mod_cast fbCostBound_le_poly hd
  have hcomb := fb_combine_real hE_ge (by dsimp [C_z]; positivity) (by dsimp [D_exp]; positivity)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hb_le' hz_le hd_le_exp hfb_poly
  calc (fbCostBound d : ℝ)
      ≤ Real.exp ((300 + 3 * C_z + 2 * D_exp + 100) * E) := hcomb
    _ ≤ Real.exp (C_fb * E) := by
        apply Real.exp_le_exp.mpr
        have hcoeff : 300 + 3 * C_z + 2 * D_exp + 100 ≤ C_fb := by
          dsimp [C_fb, D_exp, C_z]
          have : 0 ≤ K_lin ^ (4 / 3 : ℝ) := by positivity
          linarith
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = Real.exp (C_fb * Real.log ((M : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((M : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) := by
        dsimp [E, L, LL]; ring_nf

private lemma half_le_rpow_seven_eighths {L : ℝ} (hL_ge : (1 / 2 : ℝ) ≤ L) :
    (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
  have hL_pos : 0 < L := by linarith
  have hL78_pos : 0 < L ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have h7 : (1 / 2 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL_ge 7
  have hlow : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ L ^ 7 :=
    le_trans (by norm_num : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (1 / 2 : ℝ) ^ 7) h7
  have hpow8 : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) := by
    have : (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) = L ^ (7 : ℕ) := by
      rw [← Real.rpow_natCast (L ^ (7 / 8 : ℝ)), ← Real.rpow_mul hL_pos.le, ← Real.rpow_natCast]
      congr 1; norm_num
    rw [this]
    exact hlow
  exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) hL78_pos.le hpow8

/-- The factor `lenFactor M = 120 · (log₂(6M + 2) + 1)` is at most `exp(62 · log(M + 2)^{7/8})`.
The reason: `log₂(6M + 2)` is at most `10 + 2 · log(M + 2)`, and `L ≤ exp(2 · L^{7/8})` for
`L = log(M + 2)`, since `log L ≤ L^{7/8} / (7/8)`. -/
lemma lenFactor_le_exp (M : ℕ) :
    (lenFactor M : ℝ) ≤ Real.exp (62 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two M
  have hLpos : 0 < L := by linarith
  have hP := half_le_rpow_seven_eighths hL_ge
  set k := Nat.log 2 (6 * M + 2)
  have hpow : 2 ^ k ≤ 6 * M + 2 := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ k ≤ 6 * ((M : ℝ) + 2) := by
    have : ((2 ^ k : ℕ) : ℝ) ≤ ((6 * M + 2 : ℕ) : ℝ) := by exact_mod_cast hpow
    push_cast at this
    linarith
  have hlogk : (k : ℝ) * Real.log 2 ≤ Real.log 6 + L := by
    have h1 := Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h1
    exact h1
  have hlog6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk : (k : ℝ) ≤ 10 + 2 * L := by nlinarith
  -- `L ≤ exp(2 L^{7/8})`
  have hlogL : Real.log L ≤ 2 * L ^ (7 / 8 : ℝ) := by
    have h1 : Real.log (L ^ (7 / 8 : ℝ)) ≤ L ^ (7 / 8 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLpos _)
    rw [Real.log_rpow hLpos] at h1
    have : 0 ≤ L ^ (7 / 8 : ℝ) := (Real.rpow_pos_of_pos hLpos _).le
    nlinarith
  set E := Real.exp (2 * L ^ (7 / 8 : ℝ))
  have hLE : L ≤ E := by
    calc L = Real.exp (Real.log L) := (Real.exp_log hLpos).symm
      _ ≤ E := Real.exp_le_exp.mpr hlogL
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hlen : (lenFactor M : ℝ) = 120 * ((k : ℝ) + 1) := by
    unfold lenFactor; push_cast; ring
  have h1560 : (1560 : ℝ) ≤ Real.exp (60 * L ^ (7 / 8 : ℝ)) :=
    le_trans (le_trans (by norm_num) ten8_le_exp_30) (Real.exp_le_exp.mpr (by linarith))
  calc (lenFactor M : ℝ) = 120 * ((k : ℝ) + 1) := hlen
    _ ≤ 1560 * E := by nlinarith
    _ ≤ Real.exp (60 * L ^ (7 / 8 : ℝ)) * E := by gcongr
    _ = Real.exp (62 * L ^ (7 / 8 : ℝ)) := by
        dsimp only [E]; rw [← Real.exp_add]; ring_nf

/-- A bound `phiOutDen ≤ exp(A · log(M + 2)^{7/8})` gives the bound
`gExpImpl ≤ exp((A + C_x) · log(M + 2)^{7/8})` for a constant `C_x`, since
`gExpImpl = phiOutDen · lenFactor M + csExpFactor` and both `lenFactor M`
(`lenFactor_le_exp`) and `csExpFactor` (`csExpFactor_le_exp_seven_eighths`) are of this form. -/
lemma gExpImpl_le_exp_of_phiOut (Kγ c K_int : ℕ) :
    ∃ C_x : ℝ, 0 < C_x ∧ ∀ (A : ℝ) (d M : ℕ), 0 ≤ A →
      (phiOutDenImpl Kγ c d M : ℝ) ≤ Real.exp (A * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) →
      (gExpImpl Kγ c K_int d M : ℝ) ≤
        Real.exp ((A + C_x) * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases csExpFactor_le_exp_seven_eighths Kγ K_int with ⟨C_cs, hCcs, hcs⟩
  refine ⟨C_cs + 64, by positivity, fun A d M hA hphi => ?_⟩
  set L := Real.log ((M : ℝ) + 2)
  have hP := half_le_rpow_seven_eighths (half_le_log_add_two M)
  set P := L ^ (7 / 8 : ℝ)
  have hlen := lenFactor_le_exp M
  have hE : (gExpImpl Kγ c K_int d M : ℝ) =
      (phiOutDenImpl Kγ c d M : ℝ) * (lenFactor M : ℝ) + (csExpFactor Kγ K_int M : ℝ) := by
    unfold gExpImpl; push_cast; ring
  rw [hE]
  set F := Real.exp ((A + C_cs + 62) * P)
  have h1 : (phiOutDenImpl Kγ c d M : ℝ) * (lenFactor M : ℝ) ≤ F := by
    calc (phiOutDenImpl Kγ c d M : ℝ) * (lenFactor M : ℝ)
        ≤ Real.exp (A * P) * Real.exp (62 * P) :=
          mul_le_mul hphi hlen (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((A + 62) * P) := by rw [← Real.exp_add]; ring_nf
      _ ≤ F := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (csExpFactor Kγ K_int M : ℝ) ≤ F :=
    le_trans (hcs M) (Real.exp_le_exp.mpr (by nlinarith))
  have h3 : (2 : ℝ) ≤ Real.exp (2 * P) :=
    le_trans two_le_exp_one (Real.exp_le_exp.mpr (by linarith))
  calc (phiOutDenImpl Kγ c d M : ℝ) * (lenFactor M : ℝ) + (csExpFactor Kγ K_int M : ℝ)
      ≤ 2 * F := by linarith
    _ ≤ Real.exp (2 * P) * F := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp ((A + (C_cs + 64)) * P) := by dsimp only [F]; rw [← Real.exp_add]; ring_nf

/-- When `d ≤ D_0` (e.g. `φ_in = φ_Const`), `gExpImpl` satisfies `exp(O(log(M + 2)^{7/8}))`. -/
lemma gExpImpl_le_exp_seven_eighths_of_le (Kγ c K_int D_0 : ℕ) :
    ∃ C_p : ℝ, 0 < C_p ∧
      ∀ d M : ℕ, d ≤ D_0 →
        (gExpImpl Kγ c K_int d M : ℝ) ≤
          Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases gExpImpl_le_exp_of_phiOut Kγ c K_int with ⟨C_x, hCx, hx⟩
  rcases csGamma_le_exp_three_quarters Kγ with ⟨C_g, hCg, hg⟩
  set B_d : ℝ := (D_0 : ℝ) + (c : ℝ) + 2
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hD_nn : (0 : ℝ) ≤ (D_0 : ℝ) := Nat.cast_nonneg _
  have hBd : 2 ≤ B_d := by dsimp [B_d]; linarith
  have hlogB : 0 ≤ Real.log (2 * B_d) := Real.log_nonneg (by linarith)
  set A : ℝ := 2 * Real.log (2 * B_d) + 2 * C_g
  have hA : 0 ≤ A := by dsimp [A]; linarith
  refine ⟨A + C_x, by linarith, fun d M hd => hx A d M hA ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two M
  have hL_pos : 0 < L := by linarith
  have h12 := half_le_rpow_seven_eighths hL_ge
  have hL34_le : L ^ (3 / 4 : ℝ) ≤ 2 * L ^ (7 / 8 : ℝ) := by
    have h18_ge : (1 / 2 : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
      have hpow : (1 / 2 : ℝ) ^ (8 : ℕ) ≤ (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := by
        have : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = L := by
          rw [← Real.rpow_natCast (L ^ (1 / 8 : ℝ)), ← Real.rpow_mul hL_pos.le]; norm_num
        linarith [show ((1 / 2 : ℝ)) ^ (8 : ℕ) = 1 / 256 by norm_num]
      exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) (Real.rpow_nonneg hL_pos.le _) hpow
    have hadd : L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hL_pos]; norm_num
    have hmul := mul_le_mul_of_nonneg_left h18_ge (Real.rpow_nonneg hL_pos.le (3 / 4 : ℝ))
    nlinarith [hmul, hadd]
  set G := Real.exp (2 * C_g * L ^ (7 / 8 : ℝ))
  have hg_le : (Cited.csGamma Kγ (3 * M) : ℝ) ≤ G :=
    le_trans (hg M) (Real.exp_le_exp.mpr (by nlinarith))
  have hG1 : 1 ≤ G := Real.one_le_exp (by positivity)
  have hphi_le : (phiOutDenImpl Kγ c d M : ℝ) ≤
      (2 : ℝ) + (D_0 : ℝ) + (c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) := by
    unfold phiOutDenImpl
    have h1 : max 2 (max d (c * Cited.csGamma Kγ (3 * M))) ≤
        2 + D_0 + c * Cited.csGamma Kγ (3 * M) := by omega
    have hcast : ((max 2 (max d (c * Cited.csGamma Kγ (3 * M))) : ℕ) : ℝ) ≤
        ((2 + D_0 + c * Cited.csGamma Kγ (3 * M) : ℕ) : ℝ) := Nat.cast_le.mpr h1
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
    exact hcast
  have hcg : (c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) ≤ (c : ℝ) * G :=
    mul_le_mul_of_nonneg_left hg_le hc_nn
  have hphi3 : (phiOutDenImpl Kγ c d M : ℝ) ≤ (2 * B_d) * G := by
    dsimp only [B_d]; nlinarith
  have h2B : 2 * B_d ≤ Real.exp ((2 * Real.log (2 * B_d)) * L ^ (7 / 8 : ℝ)) := by
    have hpos : 0 < 2 * B_d := by linarith
    calc 2 * B_d = Real.exp (Real.log (2 * B_d)) := (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc (phiOutDenImpl Kγ c d M : ℝ) ≤ (2 * B_d) * G := hphi3
    _ ≤ Real.exp ((2 * Real.log (2 * B_d)) * L ^ (7 / 8 : ℝ)) * G := by gcongr
    _ = Real.exp (A * L ^ (7 / 8 : ℝ)) := by
        dsimp only [G, A]; rw [← Real.exp_add]; ring_nf

/-- Lower bound from amortized `GetPath` cost: if a `PathDSImpl` runs fallback `GetPath` taking
`≥ n` Word-RAM steps per repeated query (with unchanged abstract state `s' = s`, as `bfsPathProc`
does when zeroing `Work[0..n-1]`), then `n - 1 ≤ K_query * γ_ExpPath (phiNum / phiDen) M`.
Taking `phiNum = 1, phiDen = c * csGamma Kγ (3 * M)` and `G.m = M, G.n ≥ M` forces
`M - 1 ≤ K_query * γ_ExpPath (csPhi Kγ c (3 * M)) M`, excluding `exp(O(log(M+2)^{7/8}))`
for large `M`. -/
lemma fallback_cost_forces_gamma_ge_n {p : PathDSParams} {φ_in : ℝ} {M n : ℕ}
    (hφ : 0 < φ_in)
    (hfixed_phi : ∃ phi₀ : ℕ, ∀ T : ℕ, T * n ≤ T * Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) + phi₀) :
    (n : ℝ) - 1 ≤ p.K_query * p.γ_ExpPath φ_in M := by
  rcases hfixed_phi with ⟨phi₀, hT⟩
  have hle_nat : n ≤ Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) := by
    have hT1 := hT (phi₀ + 1)
    by_contra hgt
    have hge : Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) + 1 ≤ n := by omega
    have : (phi₀ + 1) * (Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) + 1) ≤ (phi₀ + 1) * n :=
      Nat.mul_le_mul_left _ hge
    nlinarith
  have hγ_nn : 0 ≤ p.K_query * p.γ_ExpPath φ_in M := by
    have h1 := p.hγ_ExpPath_ge φ_in M hφ
    have h2 := p.hφ_out_pos φ_in M hφ
    exact mul_nonneg p.hK_query (le_trans (by positivity) h1)
  have hceil := Nat.ceil_lt_add_one hγ_nn
  have hle_real : (n : ℝ) ≤ (Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) : ℝ) := by
    exact_mod_cast hle_nat
  linarith

end MinCostFlow.Expander.PathDSProg
