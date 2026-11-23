module

public import MinCostFlow.Expander.PathDSProg.ParamsBounds

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consumer Upper Bounds and Fallback `7/8` Impossibility for `pathDSParams`

Extends `ParamsBounds.lean` with:

1. Direct upper bounds on `pathDSParams` (`gDel`, `phiOutDen`, `gExp`) for downstream Word-RAM
   consumers (Algorithm 4), including both polynomial/linear word-width bounds and the
   sharp `7/8` (constant conductance) and `8/9 · (log log)^{4/3}` (`phiB1` / `Decompose`) bounds.
2. Concrete finite witness `B(9)` (`18` vertices, `73` edges, `φ_in = 1/73`) and formal
   asymptotic obstruction theorems showing why any fallback `GetPath` program following `pathDSOfCS`
   cannot achieve `exp(O(log(M + 2)^{7/8}))` in the `Decompose` regime.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open MinCostFlow.Cited MinCostFlow.Spanner

private lemma half_le_log_add_two' (M : ℕ) : (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) := by
  have h1 : (2 : ℝ) ≤ (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have h2 : Real.log 2 ≤ Real.log ((M : ℝ) + 2) := Real.log_le_log (by norm_num) h1
  linarith [Real.log_two_gt_d9]

private lemma nat_sqrt_eq_of_bounds {n s : ℕ} (h1 : s * s ≤ n) (h2 : n < (s + 1) * (s + 1)) :
    Nat.sqrt n = s := by
  have hle : s ≤ Nat.sqrt n := Nat.le_sqrt.mpr h1
  have hlt : Nat.sqrt n < s + 1 := Nat.sqrt_lt.mpr h2
  omega

/-! ## 1. Consumer Upper Bounds on `pathDSParams` (`gDel`, `phiOutDen`, `gExp`) -/

/-- `gDel` of `pathDSParams` is constant in `(d, M)`. -/
lemma pathDSParams_gDel_eq (Kγ c K_int cw_cs d M : ℕ) :
    (pathDSParams Kγ c K_int cw_cs).gDel d M = max 190 (max K_int 7) := rfl

lemma pathDSParams_gDel_le (Kγ c K_int cw_cs d M : ℕ) :
    ((pathDSParams Kγ c K_int cw_cs).gDel d M : ℝ) ≤ ((max 190 (max K_int 7) : ℕ) : ℝ) :=
  le_rfl

private lemma csGamma_three_mul_le_exp_three_quarters (Kγ : ℕ) :
    ∃ C_g : ℝ, 0 < C_g ∧ ∀ M : ℕ,
      (Cited.csGamma Kγ (3 * M) : ℝ) ≤ Real.exp (C_g * Real.log ((M : ℝ) + 2) ^ (3 / 4 : ℝ)) := by
  rcases csGamma_four_mul_le_exp_three_quarters Kγ with ⟨C_g, hCg, hg⟩
  refine ⟨C_g, hCg, fun M => le_trans ?_ (hg M)⟩
  exact_mod_cast csGamma_mono (by omega : 3 * M ≤ 4 * M)

private lemma rpow_three_quarters_le_seven_eighths (L : ℝ) (hL : (1 / 2 : ℝ) ≤ L) :
    L ^ (3 / 4 : ℝ) ≤ 2 * L ^ (7 / 8 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have h8 : (1 / 2 : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
    have hpow : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := by
      have h1 : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
      linarith [show ((1 / 2 : ℝ) ^ (8 : ℕ)) = 1 / 256 by norm_num]
    exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) (Real.rpow_nonneg hLpos.le _) hpow
  have hmul : L ^ (3 / 4 : ℝ) * (1 / 2) ≤ L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_left h8 (Real.rpow_nonneg hLpos.le _)
  have hadd : L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  linarith

private lemma exp_three_quarters_le_linear (C : ℝ) (hC : 0 < C) :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ M : ℕ,
      Real.exp (C * Real.log ((M : ℝ) + 2) ^ (3 / 4 : ℝ)) ≤ C_w * ((M : ℝ) + 2) := by
  set a : ℝ := max C 1
  have ha1 : 1 ≤ a := le_max_right _ _
  refine ⟨Real.exp (a ^ 5), Real.exp_pos _, fun M => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
  have hLpos : 0 < L := by linarith
  have hmain : a * L ^ (3 / 4 : ℝ) ≤ L + a ^ 5 := by
    by_cases hle : a ≤ L ^ (1 / 4 : ℝ)
    · have hmul : a * L ^ (3 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hLpos.le _)
      have hadd : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
        rw [← Real.rpow_add hLpos]; norm_num
      have ha5 : 0 ≤ a ^ 5 := pow_nonneg (by positivity) 5
      linarith
    · push Not at hle
      have hpow4 : L ≤ a ^ 4 := by
        have h4 : (L ^ (1 / 4 : ℝ)) ^ (4 : ℕ) ≤ a ^ (4 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le _) hle.le 4
        have hL4 : (L ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
        linarith
      have hL34 : L ^ (3 / 4 : ℝ) ≤ a ^ 4 := by
        by_cases hL1 : L ≤ 1
        · exact le_trans (Real.rpow_le_one hLpos.le hL1 (by norm_num)) (one_le_pow₀ ha1)
        · have h1L : 1 ≤ L := le_of_not_ge hL1
          exact le_trans (Real.rpow_le_rpow_of_exponent_le h1L (by norm_num : (3 / 4 : ℝ) ≤ 1))
            (by simpa using hpow4)
      have hmul : a * L ^ (3 / 4 : ℝ) ≤ a * a ^ 4 :=
        mul_le_mul_of_nonneg_left hL34 (by positivity)
      have ha5 : a * a ^ 4 = a ^ 5 := by ring
      linarith
  have hexp_a : C * L ^ (3 / 4 : ℝ) ≤ L + a ^ 5 := by
    have : C * L ^ (3 / 4 : ℝ) ≤ a * L ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hLpos.le _)
    linarith
  calc Real.exp (C * L ^ (3 / 4 : ℝ))
      ≤ Real.exp (L + a ^ 5) := Real.exp_le_exp.mpr hexp_a
    _ = Real.exp (a ^ 5) * Real.exp L := by rw [Real.exp_add, mul_comm]
    _ = Real.exp (a ^ 5) * ((M : ℝ) + 2) := by
      congr 1; exact Real.exp_log (by positivity)

/-- General upper bound on `(pathDSParams Kγ c K_int cw_cs).phiOutDen d M`. -/
lemma pathDSParams_phiOutDen_le_exp_three_quarters (Kγ c K_int cw_cs : ℕ) :
    ∃ C_g : ℝ, 0 < C_g ∧ ∀ d M : ℕ,
      ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) ≤
        (d : ℝ) + 2 + (c : ℝ) * Real.exp (C_g * Real.log ((M : ℝ) + 2) ^ (3 / 4 : ℝ)) := by
  rcases csGamma_three_mul_le_exp_three_quarters Kγ with ⟨C_g, hCg, hg⟩
  refine ⟨C_g, hCg, fun d M => ?_⟩
  change (phiOutDenImpl Kγ c d M : ℝ) ≤ _
  unfold phiOutDenImpl
  have h1 : max 2 (max d (c * Cited.csGamma Kγ (3 * M))) ≤ 2 + d + c * Cited.csGamma Kγ (3 * M) := by
    omega
  have hcast : ((max 2 (max d (c * Cited.csGamma Kγ (3 * M))) : ℕ) : ℝ) ≤
      (2 : ℝ) + (d : ℝ) + (c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) := by
    exact_mod_cast h1
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  nlinarith [hg M]

/-- Polynomial upper bound on `(pathDSParams Kγ c K_int cw_cs).phiOutDen d M` whenever
`d ≤ C_d * (M + 2)^r_d`. -/
lemma pathDSParams_phiOutDen_le_poly (Kγ c K_int cw_cs : ℕ) (C_d : ℝ) (r_d : ℕ) (hCd : 0 < C_d) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ d M : ℕ, (d : ℝ) ≤ C_d * ((M : ℝ) + 2) ^ r_d →
      ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) ≤ C_p * ((M : ℝ) + 2) ^ (max r_d 1) := by
  rcases pathDSParams_phiOutDen_le_exp_three_quarters Kγ c K_int cw_cs with ⟨C_g, hCg, hphi⟩
  rcases exp_three_quarters_le_linear C_g hCg with ⟨C_w, hCw, hlin⟩
  refine ⟨C_d + 2 + (c : ℝ) * C_w, by positivity, fun d M hd => ?_⟩
  have hM2_1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hpow_d : ((M : ℝ) + 2) ^ r_d ≤ ((M : ℝ) + 2) ^ (max r_d 1) :=
    pow_le_pow_right₀ hM2_1 (le_max_left _ _)
  have hpow_1 : ((M : ℝ) + 2) ≤ ((M : ℝ) + 2) ^ (max r_d 1) := by
    simpa using pow_le_pow_right₀ hM2_1 (le_max_right r_d 1)
  have hbase : 1 ≤ ((M : ℝ) + 2) ^ (max r_d 1) := one_le_pow₀ hM2_1
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlinM := hlin M
  have h1 : (d : ℝ) + 2 + (c : ℝ) * Real.exp (C_g * Real.log ((M : ℝ) + 2) ^ (3 / 4 : ℝ)) ≤
      (C_d + 2 + (c : ℝ) * C_w) * ((M : ℝ) + 2) ^ (max r_d 1) := by
    calc (d : ℝ) + 2 + (c : ℝ) * Real.exp (C_g * Real.log ((M : ℝ) + 2) ^ (3 / 4 : ℝ))
        ≤ C_d * ((M : ℝ) + 2) ^ r_d + 2 + (c : ℝ) * (C_w * ((M : ℝ) + 2)) := by
          linarith [mul_le_mul_of_nonneg_left hlinM hc_nn]
      _ ≤ C_d * ((M : ℝ) + 2) ^ (max r_d 1) + 2 * ((M : ℝ) + 2) ^ (max r_d 1) +
            ((c : ℝ) * C_w) * ((M : ℝ) + 2) ^ (max r_d 1) := by
          have := mul_le_mul_of_nonneg_left hpow_d hCd.le
          have := mul_le_mul_of_nonneg_left hpow_1 (mul_nonneg hc_nn hCw.le)
          linarith
      _ = (C_d + 2 + (c : ℝ) * C_w) * ((M : ℝ) + 2) ^ (max r_d 1) := by ring
  exact le_trans (hphi d M) h1

/-- Constant-conductance `gExp` bound for `pathDSParams` (`exp(O(log(M+2)^{7/8}))`, used for
`ConstructExpander` witnesses with `d ≤ D_0`). -/
lemma pathDSParams_gExp_at_phiConst (Kγ c K_int cw_cs D_0 : ℕ) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ d M : ℕ, d ≤ D_0 →
      ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
  gExpImpl_le_exp_seven_eighths_of_le Kγ c K_int D_0

/-- Constant-conductance `gQuery` bound for `pathDSParams`: for `d ≤ D_0` the query time
`gQuery = gBase + gExp` is `exp(O(log(M+2)^{7/8}))`, since `fbCostCap d M ≤ fbCostBound D_0` is a
constant there. -/
lemma pathDSParams_gQuery_at_phiConst (Kγ c K_int cw_cs D_0 : ℕ) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ d M : ℕ, d ≤ D_0 →
      ((pathDSParams Kγ c K_int cw_cs).gQuery d M : ℝ) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases gExpImpl_le_exp_seven_eighths_of_le Kγ c K_int D_0 with ⟨C_e, hCe, he⟩
  set B : ℝ := (fbCostBound D_0 : ℝ) + 2
  have hB : 2 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) (fbCostBound D_0)]
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  refine ⟨C_e + 2 * Real.log B + 6, by positivity, fun d M hd => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
  have hLpos : 0 < L := by linarith
  have hP : (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
    by_cases hL1 : 1 ≤ L
    · have : 1 ≤ L ^ (7 / 8 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    · push Not at hL1
      have : L ≤ L ^ (7 / 8 : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_ge hLpos hL1.le (show (7 / 8 : ℝ) ≤ 1 by norm_num)
        simpa using this
      linarith
  set P := L ^ (7 / 8 : ℝ)
  have hE := he d M hd
  have hbase : gBaseImpl Kγ c K_int d M ≤
      gExpImpl Kγ c K_int d M + gExpImpl Kγ c K_int d M + fbCostBound D_0 := by
    have h1 := gBaseImpl_le_fbCostBound Kγ c K_int d M
    have h2 := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
    have h3 := csExpFactor_le_gExpImpl Kγ c K_int d M
    have h4 := fbCostBound_mono hd
    omega
  have hQ : ((pathDSParams Kγ c K_int cw_cs).gQuery d M : ℝ) ≤
      3 * (gExpImpl Kγ c K_int d M : ℝ) + (fbCostBound D_0 : ℝ) := by
    change ((gQueryImpl Kγ c K_int d M : ℕ) : ℝ) ≤ _
    have : gQueryImpl Kγ c K_int d M ≤ 3 * gExpImpl Kγ c K_int d M + fbCostBound D_0 := by
      unfold gQueryImpl; omega
    exact_mod_cast this
  have hBexp : B ≤ Real.exp (2 * Real.log B * P) := by
    calc B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 2 * Real.log B)
        linarith
  have h4 : (4 : ℝ) ≤ Real.exp (6 * P) := by
    have h3 : (3 : ℝ) + 1 ≤ Real.exp 3 := Real.add_one_le_exp 3
    exact le_trans (by linarith) (Real.exp_le_exp.mpr (by linarith))
  have hE1 : 1 ≤ Real.exp (C_e * P) := Real.one_le_exp (by positivity)
  have hsum : 3 * (gExpImpl Kγ c K_int d M : ℝ) + (fbCostBound D_0 : ℝ) ≤
      4 * (Real.exp (C_e * P) * B) := by
    have hf : (fbCostBound D_0 : ℝ) ≤ B := by dsimp [B]; linarith
    have hg : (gExpImpl Kγ c K_int d M : ℝ) ≤ Real.exp (C_e * P) := hE
    have hB1 : (1 : ℝ) ≤ B := by linarith
    have hEB : Real.exp (C_e * P) ≤ Real.exp (C_e * P) * B :=
      le_mul_of_one_le_right (Real.exp_pos _).le hB1
    have hBB : B ≤ Real.exp (C_e * P) * B := le_mul_of_one_le_left (by linarith) hE1
    linarith
  calc ((pathDSParams Kγ c K_int cw_cs).gQuery d M : ℝ)
      ≤ 4 * (Real.exp (C_e * P) * B) := le_trans hQ hsum
    _ ≤ Real.exp (6 * P) * (Real.exp (C_e * P) * Real.exp (2 * Real.log B * P)) := by
        exact mul_le_mul h4 (mul_le_mul_of_nonneg_left hBexp (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (by linarith)) (Real.exp_pos _).le
    _ = Real.exp ((C_e + 2 * Real.log B + 6) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

private lemma log_rpow_poly_helper (u p : ℝ) (hu : 0 < u) (hp : 0 < p) :
    Real.log u ≤ u ^ p / p := by
  have h1 : Real.log (u ^ p) ≤ u ^ p - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu p)
  have h2 : Real.log (u ^ p) = p * Real.log u := Real.log_rpow hu p
  have h3 : p * Real.log u ≤ u ^ p := by linarith
  exact (le_div_iff₀ hp).mpr (by linarith)

private lemma exp_eight_ninths_le_linear (C : ℝ) (hC : 0 < C) :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ M : ℕ,
      Real.exp (C * Real.log ((M : ℝ) + 2) ^ (8 / 9 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ≤ C_w * ((M : ℝ) + 2) := by
  set C' : ℝ := max (C * 1500) 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  refine ⟨Real.exp (C' ^ 28), Real.exp_pos _, fun M => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
  have hLpos : 0 < L := by linarith
  have hL2_pos : 0 < L + 2 := by linarith
  have hlog_sub : Real.log (L + 2) ≤ 36 * (L + 2) ^ (1 / 36 : ℝ) := by
    have := log_rpow_poly_helper (L + 2) (1 / 36 : ℝ) hL2_pos (by norm_num)
    linarith
  have hL2_le : L + 2 ≤ 5 * L := by linarith
  have hrp1 : (L + 2) ^ (1 / 36 : ℝ) ≤ (5 * L) ^ (1 / 36 : ℝ) :=
    Real.rpow_le_rpow hL2_pos.le hL2_le (by norm_num)
  have hrp2 : (5 * L) ^ (1 / 36 : ℝ) ≤ 5 * L ^ (1 / 36 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hLpos.le]
    have h5 : (5 : ℝ) ^ (1 / 36 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    nlinarith [Real.rpow_nonneg hLpos.le (1 / 36 : ℝ)]
  have hlog_nn : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
  have hlog43 : Real.log (L + 2) ^ (4 / 3 : ℝ) ≤ (180 : ℝ) ^ (4 / 3 : ℝ) * L ^ (1 / 27 : ℝ) := by
    have h1 : Real.log (L + 2) ≤ 180 * L ^ (1 / 36 : ℝ) := by linarith
    have h2 := Real.rpow_le_rpow hlog_nn h1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hLpos.le _),
      ← Real.rpow_mul hLpos.le, show (1 / 36 : ℝ) * (4 / 3) = 1 / 27 by norm_num] at h2
    exact h2
  have h180 : (180 : ℝ) ^ (4 / 3 : ℝ) ≤ 1500 := by
    have h1 : (180 : ℝ) ^ (4 / 3 : ℝ) ≤ ((6 : ℝ) ^ (3 : ℕ)) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    have h2 : ((6 : ℝ) ^ (3 : ℕ)) ^ (4 / 3 : ℝ) = (6 : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (6 : ℝ) 3, ← Real.rpow_natCast (6 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [show (6 : ℝ) ^ (4 : ℕ) = 1296 by norm_num]
  have hL89_nn : 0 ≤ L ^ (8 / 9 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hprod : C * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) ≤ C' * L ^ (25 / 27 : ℝ) := by
    have hmul1 : L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) ≤
        L ^ (8 / 9 : ℝ) * (1500 * L ^ (1 / 27 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (le_trans hlog43 _) hL89_nn
      exact mul_le_mul_of_nonneg_right h180 (Real.rpow_nonneg hLpos.le _)
    have hadd : L ^ (8 / 9 : ℝ) * L ^ (1 / 27 : ℝ) = L ^ (25 / 27 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    have hmul2 : C * (1500 * L ^ (25 / 27 : ℝ)) ≤ C' * L ^ (25 / 27 : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hLpos.le _)
    calc C * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)
        = C * (L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) := by ring
      _ ≤ C * (L ^ (8 / 9 : ℝ) * (1500 * L ^ (1 / 27 : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul1 hC.le
      _ = C * (1500 * L ^ (25 / 27 : ℝ)) := by rw [← hadd]; ring
      _ ≤ C' * L ^ (25 / 27 : ℝ) := hmul2
  have hmain : C' * L ^ (25 / 27 : ℝ) ≤ L + C' ^ 28 := by
    by_cases hle : C' ≤ L ^ (2 / 27 : ℝ)
    · have hmul : C' * L ^ (25 / 27 : ℝ) ≤ L ^ (2 / 27 : ℝ) * L ^ (25 / 27 : ℝ) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hLpos.le _)
      have hadd : L ^ (2 / 27 : ℝ) * L ^ (25 / 27 : ℝ) = L := by
        rw [← Real.rpow_add hLpos]; norm_num
      have hc28 : 0 ≤ C' ^ 28 := pow_nonneg (by positivity) 28
      linarith
    · push Not at hle
      have hpow27 : L ^ 2 ≤ C' ^ 27 := by
        have h1 : (L ^ (2 / 27 : ℝ)) ^ (27 : ℕ) ≤ C' ^ (27 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le _) hle.le 27
        have h2 : (L ^ (2 / 27 : ℝ)) ^ (27 : ℕ) = L ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
        linarith
      have hL25 : L ^ (25 / 27 : ℝ) ≤ C' ^ 27 := by
        by_cases hL1 : L ≤ 1
        · exact le_trans (Real.rpow_le_one hLpos.le hL1 (by norm_num)) (one_le_pow₀ hC'1)
        · have h1L : 1 ≤ L := le_of_not_ge hL1
          have h1 : L ^ (25 / 27 : ℝ) ≤ L ^ (2 : ℕ) := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le h1L (by norm_num)
          exact le_trans h1 hpow27
      have hmul : C' * L ^ (25 / 27 : ℝ) ≤ C' * C' ^ 27 :=
        mul_le_mul_of_nonneg_left hL25 (by positivity)
      have hc28 : C' * C' ^ 27 = C' ^ 28 := by ring
      linarith
  calc Real.exp (C * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ))
      ≤ Real.exp (L + C' ^ 28) := Real.exp_le_exp.mpr (le_trans hprod hmain)
    _ = Real.exp (C' ^ 28) * Real.exp L := by rw [Real.exp_add, mul_comm]
    _ = Real.exp (C' ^ 28) * ((M : ℝ) + 2) := by congr 1; exact Real.exp_log (by positivity)

private lemma rpow_one_third_ge_half {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    (1 / 2 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hpow : ((1 / 2 : ℝ) ^ (3 : ℕ)) ≤ (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
    have h1 : (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [show ((1 / 2 : ℝ) ^ (3 : ℕ)) = 1 / 8 by norm_num]
  exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (Real.rpow_nonneg hxpos.le _) hpow

lemma rpow_seven_eighths_le_eight_ninths_loglog (L : ℝ) (hL : (1 / 2 : ℝ) ≤ L) :
    L ^ (7 / 8 : ℝ) ≤ 8 * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) := by
  have hLpos : 0 < L := by linarith
  have h172 : (1 / 2 : ℝ) ≤ L ^ (1 / 72 : ℝ) := by
    have hpow : ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ (L ^ (1 / 72 : ℝ)) ^ (72 : ℕ) := by
      have h1 : (L ^ (1 / 72 : ℝ)) ^ (72 : ℕ) = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
      have h2 : ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ (1 / 2 : ℝ) := by
        calc ((1 / 2 : ℝ) ^ (72 : ℕ)) ≤ ((1 / 2 : ℝ) ^ (1 : ℕ)) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by decide)
          _ = 1 / 2 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by decide : 72 ≠ 0) (Real.rpow_nonneg hLpos.le _) hpow
  have h78_89 : L ^ (7 / 8 : ℝ) ≤ 2 * L ^ (8 / 9 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left h172 (Real.rpow_nonneg hLpos.le (7 / 8 : ℝ))
    have hadd : L ^ (7 / 8 : ℝ) * L ^ (1 / 72 : ℝ) = L ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    linarith
  have hll_ge : (1 / 2 : ℝ) ≤ Real.log (L + 2) := by
    have h2 : (2 : ℝ) ≤ L + 2 := by linarith
    exact le_trans (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
  have hllpos : 0 < Real.log (L + 2) := by linarith
  have hll43 : (1 / 4 : ℝ) ≤ Real.log (L + 2) ^ (4 / 3 : ℝ) := by
    have h1 := rpow_one_third_ge_half hll_ge
    have hmul : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) :=
      mul_le_mul hll_ge h1 (by positivity) hllpos.le
    have hadd : Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) = Real.log (L + 2) ^ (4 / 3 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (Real.log (L + 2))]
      rw [← Real.rpow_add hllpos]; norm_num
    linarith
  have hmul := mul_le_mul h78_89 hll43 (by norm_num) (by positivity)
  linarith

/-- In `Decompose`'s `phiB1` regime (`d ≤ C₁ * exp(C₀ * log^{2/3} * log(log + 2)) + 1`),
`phiOutDen` of `pathDSParams` is `≤ exp(O(log(M+2)^{7/8}))`. -/
lemma pathDSParams_phiOutDen_at_phiB1 (Kγ c K_int cw_cs : ℕ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M d : ℕ,
      (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
      ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases pathDSParams_phiOutDen_le_exp_three_quarters Kγ c K_int cw_cs with ⟨C_g, hCg, hphi⟩
  set K_d : ℝ := max (C₁ + (c : ℝ) + 3) 1
  have hKd : 1 ≤ K_d := le_max_right _ _
  have hlogKd : 0 ≤ Real.log K_d := Real.log_nonneg hKd
  set C_base : ℝ := max (25 * C₀) (2 * C_g)
  set C_p : ℝ := C_base + 2 * Real.log K_d + 4
  refine ⟨C_p, by positivity, fun M d hd => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
  have hLpos : 0 < L := by linarith
  have hL78_ge : (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
    have hpow : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) := by
      have h1 : (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) = L ^ (7 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_natCast]; norm_num
      have h2 : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ L ^ (7 : ℕ) := by
        calc ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ ((1 / 2 : ℝ) ^ (7 : ℕ)) := by norm_num
          _ ≤ L ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) hL_ge 7
      linarith
    exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) (Real.rpow_nonneg hLpos.le _) hpow
  have hll_le : Real.log (L + 2) ≤ 25 * L ^ (5 / 24 : ℝ) := by
    have hL2_pos : 0 < L + 2 := by linarith
    have h1 := log_rpow_poly_helper (L + 2) (5 / 24 : ℝ) hL2_pos (by norm_num)
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
  have hpow_le : L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤ 25 * L ^ (7 / 8 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hll_le (Real.rpow_nonneg hLpos.le (2 / 3 : ℝ))
    have hadd : L ^ (2 / 3 : ℝ) * L ^ (5 / 24 : ℝ) = L ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    linarith [show L ^ (2 / 3 : ℝ) * (25 * L ^ (5 / 24 : ℝ)) =
      25 * (L ^ (2 / 3 : ℝ) * L ^ (5 / 24 : ℝ)) by ring]
  set E : ℝ := Real.exp (C_base * L ^ (7 / 8 : ℝ))
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg (by positivity) (Real.rpow_nonneg hLpos.le _))
  have hd_exp : Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h1 : C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤ (25 * C₀) * L ^ (7 / 8 : ℝ) := by
      calc C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)
          = C₀ * (L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by ring
        _ ≤ C₀ * (25 * L ^ (7 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hC₀.le
        _ = (25 * C₀) * L ^ (7 / 8 : ℝ) := by ring
    have h2 : 25 * C₀ ≤ C_base := le_max_left _ _
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLpos.le _))
  have hg_exp : Real.exp (C_g * L ^ (3 / 4 : ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have hr := rpow_three_quarters_le_seven_eighths L hL_ge
    have h2 : 2 * C_g ≤ C_base := le_max_right _ _
    have h1 : C_g * L ^ (3 / 4 : ℝ) ≤ (2 * C_g) * L ^ (7 / 8 : ℝ) := by nlinarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLpos.le _))
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hsum : ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) ≤ K_d * E := by
    have h1 := hphi d M
    have hmulC : C₁ * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤ C₁ * E :=
      mul_le_mul_of_nonneg_left hd_exp hC₁.le
    have hmulc : (c : ℝ) * Real.exp (C_g * L ^ (3 / 4 : ℝ)) ≤ (c : ℝ) * E :=
      mul_le_mul_of_nonneg_left hg_exp hc_nn
    have hKd' : C₁ + (c : ℝ) + 3 ≤ K_d := le_max_left _ _
    nlinarith
  have hK_exp : K_d ≤ Real.exp ((2 * Real.log K_d + 4) * L ^ (7 / 8 : ℝ)) := by
    have hlog_le : Real.log K_d ≤ 2 * Real.log K_d * L ^ (7 / 8 : ℝ) := by nlinarith
    have heq : K_d = Real.exp (Real.log K_d) := (Real.exp_log (by linarith)).symm
    calc K_d = Real.exp (Real.log K_d) := heq
      _ ≤ Real.exp ((2 * Real.log K_d + 4) * L ^ (7 / 8 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ L ^ (7 / 8 : ℝ) := Real.rpow_nonneg hLpos.le _
          nlinarith
  calc ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ)
      ≤ K_d * E := hsum
    _ ≤ Real.exp ((2 * Real.log K_d + 4) * L ^ (7 / 8 : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hK_exp (Real.exp_pos _).le
    _ = Real.exp (C_p * L ^ (7 / 8 : ℝ)) := by
        dsimp [E, C_p]; rw [← Real.exp_add]; ring_nf

/-- In `Decompose`'s `phiB1` regime, the path length `gExp` of `pathDSParams` is
`exp(O(log(M + 2)^{7/8}))`. It follows from `pathDSParams_phiOutDen_at_phiB1` and
`gExpImpl_le_exp_of_phiOut`, which bounds `lenFactor` and `csExpFactor`. -/
theorem pathDSParams_gExp_at_phiB1_seven_eighths (Kγ c K_int cw_cs : ℕ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M d : ℕ,
      (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
      ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases pathDSParams_phiOutDen_at_phiB1 Kγ c K_int cw_cs C₀ C₁ hC₀ hC₁ with ⟨C_phi, hCphi, hphi⟩
  rcases gExpImpl_le_exp_of_phiOut Kγ c K_int with ⟨C_x, hCx, hx⟩
  exact ⟨C_phi + C_x, by linarith, fun M d hd => hx C_phi d M hCphi.le (hphi M d hd)⟩

/-- In `Decompose`'s `phiB1` regime, the query time `gQuery` of `pathDSParams` satisfies the
`8/9 · (log log)^{4/3}` subpolynomial envelope. The term `fbCostCap` of `gQuery` is the reason
for the exponent `8/9` (`fbCostBound_le_exp_eight_ninths`). -/
lemma pathDSParams_gQuery_at_phiB1 (Kγ c K_int cw_cs : ℕ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ M d : ℕ,
      (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
      ((pathDSParams Kγ c K_int cw_cs).gQuery d M : ℝ) ≤
        Real.exp (C * Real.log ((M : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((M : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) := by
  rcases pathDSParams_phiOutDen_at_phiB1 Kγ c K_int cw_cs C₀ C₁ hC₀ hC₁ with ⟨C_phi, hCphi, hphi⟩
  rcases csExpFactor_le_exp_seven_eighths Kγ K_int with ⟨C_cs, hCcs, hcs⟩
  rcases fbCostBound_le_exp_eight_ninths C₀ (C₁ + 1) hC₀ (by linarith) with ⟨C_fb, hCfb, hfb⟩
  rcases pathDSParams_gExp_at_phiB1_seven_eighths Kγ c K_int cw_cs C₀ C₁ hC₀ hC₁ with
    ⟨C_e, hCe, hgE⟩
  set C_top : ℝ := max (8 * C_phi) (max (8 * C_cs) (max C_fb (8 * C_e)))
  set C : ℝ := C_top + 24
  refine ⟨C, by positivity, fun M d hd => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_ge : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
  have hLpos : 0 < L := by linarith
  have hS_ge : (1 / 8 : ℝ) ≤ L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) := by
    have hL89 : (1 / 2 : ℝ) ≤ L ^ (8 / 9 : ℝ) := by
      have hpow : ((1 / 2 : ℝ) ^ (9 : ℕ)) ≤ (L ^ (8 / 9 : ℝ)) ^ (9 : ℕ) := by
        have h1 : (L ^ (8 / 9 : ℝ)) ^ (9 : ℕ) = L ^ (8 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_natCast]; norm_num
        have h2 : ((1 / 2 : ℝ) ^ (9 : ℕ)) ≤ L ^ (8 : ℕ) := by
          calc ((1 / 2 : ℝ) ^ (9 : ℕ)) ≤ ((1 / 2 : ℝ) ^ (8 : ℕ)) := by norm_num
            _ ≤ L ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) hL_ge 8
        linarith
      exact le_of_pow_le_pow_left₀ (by decide : 9 ≠ 0) (Real.rpow_nonneg hLpos.le _) hpow
    have hll_ge : (1 / 2 : ℝ) ≤ Real.log (L + 2) := by
      have h2 : (2 : ℝ) ≤ L + 2 := by linarith
      exact le_trans (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) h2)
    have hllpos : 0 < Real.log (L + 2) := by linarith
    have hll43 : (1 / 4 : ℝ) ≤ Real.log (L + 2) ^ (4 / 3 : ℝ) := by
      have h1 := rpow_one_third_ge_half hll_ge
      have hmul : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) :=
        mul_le_mul hll_ge h1 (by positivity) hllpos.le
      have hadd : Real.log (L + 2) * Real.log (L + 2) ^ (1 / 3 : ℝ) = Real.log (L + 2) ^ (4 / 3 : ℝ) := by
        conv_lhs => arg 1; rw [← Real.rpow_one (Real.log (L + 2))]
        rw [← Real.rpow_add hllpos]; norm_num
      linarith
    calc (1 / 8 : ℝ) = (1 / 2 : ℝ) * (1 / 4 : ℝ) := by norm_num
      _ ≤ L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) :=
          mul_le_mul hL89 hll43 (by norm_num) (by positivity)
  set S : ℝ := L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)
  have hS_nn : 0 ≤ S := by linarith
  have h78_S := rpow_seven_eighths_le_eight_ninths_loglog L hL_ge
  have hE_phi : ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) ≤ Real.exp (C_top * S) := by
    have h1 := hphi M d hd
    have h2 : C_phi * L ^ (7 / 8 : ℝ) ≤ C_top * S := by
      have hC1 : 8 * C_phi ≤ C_top := le_max_left _ _
      have h1' : C_phi * L ^ (7 / 8 : ℝ) ≤ (8 * C_phi) * S := by
        dsimp [S]; nlinarith
      exact le_trans h1' (mul_le_mul_of_nonneg_right hC1 hS_nn)
    exact le_trans h1 (Real.exp_le_exp.mpr h2)
  have hE_cs : (csExpFactor Kγ K_int M : ℝ) ≤ Real.exp (C_top * S) := by
    have h1 := hcs M
    have h2 : C_cs * L ^ (7 / 8 : ℝ) ≤ C_top * S := by
      have hC1 : 8 * C_cs ≤ C_top := le_trans (le_max_left _ _) (le_max_right _ _)
      have h1' : C_cs * L ^ (7 / 8 : ℝ) ≤ (8 * C_cs) * S := by
        dsimp [S]; nlinarith
      exact le_trans h1' (mul_le_mul_of_nonneg_right hC1 hS_nn)
    exact le_trans h1 (Real.exp_le_exp.mpr h2)
  have hE_fb : (fbCostBound d : ℝ) ≤ Real.exp (C_top * S) := by
    have hd_le : fbCostBound d ≤ fbCostBound (max d 1) := fbCostBound_mono (le_max_left d 1)
    have hd1 : 1 ≤ max d 1 := le_max_right d 1
    have hd_bd : ((max d 1 : ℕ) : ℝ) ≤
        (C₁ + 1) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) + 1 := by
      have hexp1 : 1 ≤ Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) :=
        Real.one_le_exp (mul_nonneg (mul_nonneg hC₀.le (Real.rpow_nonneg hLpos.le _))
          (Real.log_nonneg (by linarith)))
      by_cases h0 : d = 0
      · subst h0
        simp only [Nat.zero_max, Nat.cast_one]
        have hC1E : 0 ≤ (C₁ + 1) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          positivity
        linarith
      · have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero h0
        rw [max_eq_left hd_pos]
        linarith [show (C₁ + 1) * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) =
          C₁ * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) +
          Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) by ring]
    have h1 := hfb M (max d 1) hd1 hd_bd
    have h2 : (fbCostBound d : ℝ) ≤ (fbCostBound (max d 1) : ℝ) := by exact_mod_cast hd_le
    have hC1 : C_fb ≤ C_top :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have h3 : C_fb * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) ≤ C_top * S := by
      rw [show C_fb * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) = C_fb * S by
        dsimp [S]; ring]
      exact mul_le_mul_of_nonneg_right hC1 hS_nn
    exact le_trans (le_trans h2 h1) (Real.exp_le_exp.mpr h3)
  have hE_gexp : ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤ Real.exp (C_top * S) := by
    have h1 := hgE M d hd
    have h2 : C_e * L ^ (7 / 8 : ℝ) ≤ C_top * S := by
      have hC1 : 8 * C_e ≤ C_top :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have h1' : C_e * L ^ (7 / 8 : ℝ) ≤ (8 * C_e) * S := by
        dsimp [S]; nlinarith
      exact le_trans h1' (mul_le_mul_of_nonneg_right hC1 hS_nn)
    exact le_trans h1 (Real.exp_le_exp.mpr h2)
  have h4_exp : (4 : ℝ) ≤ Real.exp (24 * S) := by
    have h3 : (3 : ℝ) + 1 ≤ Real.exp 3 := Real.add_one_le_exp 3
    exact le_trans (by linarith) (Real.exp_le_exp.mpr (by linarith))
  have hgq_eq : ((pathDSParams Kγ c K_int cw_cs).gQuery d M : ℝ) ≤
      ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) +
        (csExpFactor Kγ K_int M : ℝ) + (fbCostBound d : ℝ) +
        ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) := by
    change (gQueryImpl Kγ c K_int d M : ℝ) ≤ (phiOutDenImpl Kγ c d M : ℝ) + _ + _ +
      (gExpImpl Kγ c K_int d M : ℝ)
    have h1 := gBaseImpl_le_fbCostBound Kγ c K_int d M
    have h2 : gQueryImpl Kγ c K_int d M ≤ phiOutDenImpl Kγ c d M + csExpFactor Kγ K_int M +
        fbCostBound d + gExpImpl Kγ c K_int d M := by unfold gQueryImpl; omega
    exact_mod_cast h2
  refine le_trans hgq_eq ?_
  calc ((pathDSParams Kγ c K_int cw_cs).phiOutDen d M : ℝ) +
        (csExpFactor Kγ K_int M : ℝ) + (fbCostBound d : ℝ) +
        ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ)
      ≤ 4 * Real.exp (C_top * S) := by linarith
    _ ≤ Real.exp (24 * S) * Real.exp (C_top * S) :=
        mul_le_mul_of_nonneg_right h4_exp (Real.exp_pos _).le
    _ = Real.exp (C * S) := by dsimp [C]; rw [← Real.exp_add]; ring_nf
    _ = Real.exp (C * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) := by
        dsimp [S]; ring_nf

/-- In `Decompose`'s `phiB1` regime, `gExp` of `pathDSParams` satisfies the `8/9 · (log log)^{4/3}`
subpolynomial envelope, since `gExp ≤ gQuery` (`pathDSParams_gQuery_at_phiB1`). -/
lemma pathDSParams_gExp_at_phiB1 (Kγ c K_int cw_cs : ℕ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ M d : ℕ,
      (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
      ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤
        Real.exp (C * Real.log ((M : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((M : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) := by
  rcases pathDSParams_gQuery_at_phiB1 Kγ c K_int cw_cs C₀ C₁ hC₀ hC₁ with ⟨C, hC, hq⟩
  refine ⟨C, hC, fun M d hd => le_trans ?_ (hq M d hd)⟩
  exact_mod_cast gExpImpl_le_gQueryImpl Kγ c K_int d M

/-- Linear polynomial upper bound `≤ C_w * (M + 2)` on `pathDSParams.gExp` in `Decompose`'s `phiB1` regime
(so `Nat.log 2 (... + gExp + 2) ≤ O(log(M + 2))` for `WordWidthOK`). -/
lemma pathDSParams_gExp_at_phiB1_le_linear (Kγ c K_int cw_cs : ℕ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ M d : ℕ,
      (d : ℝ) ≤ C₁ * Real.exp (C₀ * Real.log ((M : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((M : ℝ) + 2) + 2)) + 1 →
      ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤ C_w * ((M : ℝ) + 2) := by
  rcases pathDSParams_gExp_at_phiB1 Kγ c K_int cw_cs C₀ C₁ hC₀ hC₁ with ⟨C, hC, hg⟩
  rcases exp_eight_ninths_le_linear C hC with ⟨C_w, hCw, hlin⟩
  exact ⟨C_w, hCw, fun M d hd => le_trans (hg M d hd) (hlin M)⟩

/-- Linear polynomial upper bound `≤ C_w * (M + 2)` on `pathDSParams.gExp` at constant conductance
(`d ≤ D_0`). -/
lemma pathDSParams_gExp_at_phiConst_le_linear (Kγ c K_int cw_cs D_0 : ℕ) :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ d M : ℕ, d ≤ D_0 →
      ((pathDSParams Kγ c K_int cw_cs).gExp d M : ℝ) ≤ C_w * ((M : ℝ) + 2) := by
  rcases pathDSParams_gExp_at_phiConst Kγ c K_int cw_cs D_0 with ⟨C_p, hCp, hg⟩
  rcases exp_eight_ninths_le_linear (8 * C_p) (by positivity) with ⟨C_w, hCw, hlin⟩
  refine ⟨C_w, hCw, fun d M hd => ?_⟩
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have h78 := rpow_seven_eighths_le_eight_ninths_loglog L (half_le_log_add_two' M)
  have hexp : Real.exp (C_p * L ^ (7 / 8 : ℝ)) ≤
      Real.exp ((8 * C_p) * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact le_trans (hg d M hd) (le_trans hexp (hlin M))

/-! ## 2. Concrete Small Instance and Formal `7/8` Fallback Obstruction -/

/-- Generalization of `fallback_cost_forces_gamma_ge_n`: if `GetPath` (`op 1`) takes `≥ B` steps on any
state with unchanged abstract state `s' = s` (even without scanning all `G.n` vertices, e.g., any
BFS visiting `B` edges), repeating `GetPath` forces `B - 1 ≤ p.K_query * p.γ_ExpPath φ_in M`. -/
lemma fallback_query_cost_forces_gamma {p : PathDSParams} {φ_in : ℝ} {M B : ℕ}
    (hφ : 0 < φ_in)
    (hfixed_phi : ∃ phi₀ : ℕ, ∀ T : ℕ, T * B ≤ T * Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) + phi₀) :
    (B : ℝ) - 1 ≤ p.K_query * p.γ_ExpPath φ_in M :=
  fallback_cost_forces_gamma_ge_n hφ hfixed_phi

/-- Exact `csGamma` value on `subdivGraph B(9)` (`18` vertices, `73` edges, `3 * 73 = 219`). -/
lemma csGamma_b9 : Cited.csGamma 1 (3 * 73) = 32 := by
  unfold Cited.csGamma
  have hlog : Nat.log 2 (3 * 73) = 7 := (Nat.log_eq_iff (by decide)).mpr ⟨by decide, by decide⟩
  have hs1 : Nat.sqrt ((7 + 1) ^ 3) = 22 := nat_sqrt_eq_of_bounds (by decide) (by decide)
  have hs2 : Nat.sqrt 22 = 4 := nat_sqrt_eq_of_bounds (by decide) (by decide)
  rw [hlog, hs1, hs2]
  norm_num

/-- Concrete 18-vertex, 73-edge expander `B(9)` (two `K_9` cliques joined by 1 bridge edge,
conductance `1 / 73`): even for minimal `[CS21]` constants `Kγ = 1, c = 20`, `[CS21]`'s threshold
`10 * csPhi 1 20 (3 * 73) = 1 / 64` strictly exceeds `φ_in = 1 / 73`, forcing fallback, and
`3 * 73 < zStarImpl 73`. -/
lemma csPhi_b9 :
    (1 / 73 : ℝ) < 10 * Cited.csPhi 1 20 (3 * 73) ∧ 3 * 73 < zStarImpl 73 := by
  constructor
  · unfold Cited.csPhi
    rw [csGamma_b9]
    norm_num
  · have hlog : 9 ≤ Nat.log 2 (10 * 73) :=
      (Nat.le_log_iff_pow_le (by decide) (by decide)).mpr (by decide)
    have hpow4 : 512 ≤ (Nat.log 2 (10 * 73) + 1) ^ 4 := by
      have h10 : 10 ≤ Nat.log 2 (10 * 73) + 1 := by omega
      calc 512 ≤ 10 ^ 4 := by decide
        _ ≤ (Nat.log 2 (10 * 73) + 1) ^ 4 := Nat.pow_le_pow_left h10 4
    have hspec := (natCbrtFloor_spec ((Nat.log 2 (10 * 73) + 1) ^ 4)).2
    have h8 : 8 ≤ natCbrtFloor ((Nat.log 2 (10 * 73) + 1) ^ 4) := by
      by_contra hlt
      have hle : natCbrtFloor ((Nat.log 2 (10 * 73) + 1) ^ 4) + 1 ≤ 8 := by omega
      have hp : (natCbrtFloor ((Nat.log 2 (10 * 73) + 1) ^ 4) + 1) ^ 3 ≤ 8 ^ 3 :=
        Nat.pow_le_pow_left hle 3
      omega
    change 8 ≤ zStarExp 73 at h8
    calc 3 * 73 < 2 ^ 8 := by decide
      _ ≤ 2 ^ zStarExp 73 := Nat.pow_le_pow_right (by decide) h8

/-- For any exponent `α > 7 / 8` (for instance `α = 85 / 96` in fallback BFS on `G_M` or `α = 8 / 9`
for `zStarImpl`), `exp(log(M + 2)^α)` eventually exceeds `K_q * exp(C_γ * log(M + 2)^{7/8})`. -/
lemma exp_rpow_exceeds_seven_eighths {α : ℝ} (hα : (7 / 8 : ℝ) < α) (C_γ K_q : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      K_q * Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) <
        Real.exp (Real.log ((M : ℝ) + 2) ^ α) := by
  by_cases hKq : K_q ≤ 0
  · refine ⟨0, fun M _ => ?_⟩
    have h1 : K_q * Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hKq (Real.exp_pos _).le
    exact lt_of_le_of_lt h1 (Real.exp_pos _)
  · push Not at hKq
    set δ : ℝ := α - 7 / 8
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
    have hm1 : 1 ≤ m := by
      by_contra h0
      have : m = 0 := by omega
      subst this
      have : (0 : ℝ) < 1 / δ := by positivity
      linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hinv_le : 1 / (m : ℝ) ≤ δ := by
      rw [div_le_iff₀ hm_pos]
      have h1 := (div_lt_iff₀ hδ).mp hm
      linarith
    set A : ℝ := max C_γ 0 + 2 * max (Real.log K_q) 0 + 1
    have hA1 : 1 ≤ A := by
      have : 0 ≤ max C_γ 0 := le_max_right _ _
      have : 0 ≤ max (Real.log K_q) 0 := le_max_right _ _
      dsimp [A]; linarith
    set T : ℕ := Nat.ceil A ^ m + 1
    refine ⟨2 ^ (2 * T), fun M hM => ?_⟩
    set L : ℝ := Real.log ((M : ℝ) + 2)
    have hM_ge : (2 : ℝ) ^ (2 * T) ≤ (M : ℝ) + 2 := by
      have : 2 ^ (2 * T) ≤ M + 2 := by omega
      exact_mod_cast this
    have hL_ge : (T : ℝ) ≤ L := by
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlog : Real.log ((2 : ℝ) ^ (2 * T)) ≤ L := Real.log_le_log (by positivity) hM_ge
      rw [Real.log_pow] at hlog
      have hTnn : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      have h2t : ((2 * T : ℕ) : ℝ) = 2 * (T : ℝ) := by push_cast; ring
      rw [h2t] at hlog
      linarith [mul_le_mul_of_nonneg_left hl2 hTnn]
    have hA_le_L : A ^ m + 1 ≤ L := by
      have h1 : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
      have h2 : A ^ m ≤ (Nat.ceil A : ℝ) ^ m := pow_le_pow_left₀ (by linarith) h1 m
      have h3 : ((Nat.ceil A ^ m + 1 : ℕ) : ℝ) = (Nat.ceil A : ℝ) ^ m + 1 := by push_cast; ring
      dsimp [T] at hL_ge
      linarith
    have hL1 : 1 ≤ L := by
      have : 1 ≤ A ^ m := one_le_pow₀ hA1
      linarith
    have hL_pow_A : A ≤ L ^ δ := by
      have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
      have hA_pos : 0 < A := by linarith
      have hAm_le : A ^ m ≤ L := by linarith
      have hrp1 : (A ^ m) ^ (1 / (m : ℝ)) ≤ L ^ (1 / (m : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg hA_pos.le _) hAm_le (by positivity)
      have hleft : (A ^ m) ^ (1 / (m : ℝ)) = A := by
        rw [← Real.rpow_natCast A m, ← Real.rpow_mul hA_pos.le]
        simp [hm_ne]
      have hrp2 : L ^ (1 / (m : ℝ)) ≤ L ^ δ :=
        Real.rpow_le_rpow_of_exponent_le hL1 hinv_le
      linarith
    have hL_ge_half : (1 / 2 : ℝ) ≤ L := half_le_log_add_two' M
    have hL78_ge : (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
      have hpow : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) := by
        have h1 : (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) = L ^ (7 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L), ← Real.rpow_natCast]; norm_num
        have h2 : ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ L ^ (7 : ℕ) := by
          calc ((1 / 2 : ℝ) ^ (8 : ℕ)) ≤ ((1 / 2 : ℝ) ^ (7 : ℕ)) := by norm_num
            _ ≤ L ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) hL_ge_half 7
        linarith
      exact le_of_pow_le_pow_left₀ (by decide : 8 ≠ 0) (Real.rpow_nonneg (by linarith : 0 ≤ L) _) hpow
    have hsplit : L ^ α = L ^ δ * L ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add (by linarith : 0 < L)]
      congr 1; dsimp [δ]; ring
    have hlogK_le : Real.log K_q ≤ 2 * max (Real.log K_q) 0 * L ^ (7 / 8 : ℝ) := by
      have h1 : Real.log K_q ≤ max (Real.log K_q) 0 := le_max_left _ _
      have h2 : 0 ≤ max (Real.log K_q) 0 := le_max_right _ _
      nlinarith
    have hCγ_le : C_γ * L ^ (7 / 8 : ℝ) ≤ max C_γ 0 * L ^ (7 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    have hexp_lt : Real.log K_q + C_γ * L ^ (7 / 8 : ℝ) < L ^ α := by
      have hA_mul : A * L ^ (7 / 8 : ℝ) ≤ L ^ δ * L ^ (7 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hL_pow_A (Real.rpow_nonneg (by linarith) _)
      have hA_eq : A * L ^ (7 / 8 : ℝ) =
          (max C_γ 0 + 2 * max (Real.log K_q) 0) * L ^ (7 / 8 : ℝ) + L ^ (7 / 8 : ℝ) := by
        dsimp [A]; ring
      have hL78_pos : 0 < L ^ (7 / 8 : ℝ) := by linarith
      linarith
    calc K_q * Real.exp (C_γ * L ^ (7 / 8 : ℝ))
        = Real.exp (Real.log K_q) * Real.exp (C_γ * L ^ (7 / 8 : ℝ)) := by
          rw [Real.exp_log hKq]
      _ = Real.exp (Real.log K_q + C_γ * L ^ (7 / 8 : ℝ)) := (Real.exp_add _ _).symm
      _ < Real.exp (L ^ α) := Real.exp_lt_exp.mpr hexp_lt

/-- Formal `7/8` impossibility in the fallback regime: if for infinitely many `M` there is a graph
in the fallback regime (`φ_in > 0`) on which `GetPath` (`op 1`) explores at least `B(M) ≥ exp(log(M+2)^α)`
edges/steps with `α > 7/8` (for example `α = 85/96 < 8/9` on a bounded-degree `phiB1`-expander `G_M`
with `m_M ≈ exp(log(M)^{85/96})` where any BFS/bidirectional BFS explores `m_M^{Ω(1)}` edges), then
`p.γ_ExpPath` cannot be bounded by `exp(C_γ * log(M + 2)^{7/8})`.
The parameters charge the query cost to `gQuery`, so this lemma does not limit `gExp`. -/
lemma fallback_prevents_seven_eighths_gExp (p : PathDSParams) {α C_γ : ℝ}
    (hα : (7 / 8 : ℝ) < α)
    (hM_big : ∀ M₀ : ℕ, ∃ M ≥ M₀, ∃ (φ_in : ℝ) (B : ℕ), 0 < φ_in ∧
      Real.exp (Real.log ((M : ℝ) + 2) ^ α) ≤ (B : ℝ) ∧
      (∃ phi₀ : ℕ, ∀ T : ℕ, T * B ≤ T * Nat.ceil (p.K_query * p.γ_ExpPath φ_in M) + phi₀) ∧
      p.γ_ExpPath φ_in M ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    False := by
  rcases exp_rpow_exceeds_seven_eighths hα (max C_γ 0) (p.K_query + 1) with ⟨M₀, hdom⟩
  rcases hM_big M₀ with ⟨M, hMM₀, φ_in, B, hφ, hB_ge, hcost, h78⟩
  have hlow := fallback_query_cost_forces_gamma hφ hcost
  set L : ℝ := Real.log ((M : ℝ) + 2)
  have hL_nn : 0 ≤ L ^ (7 / 8 : ℝ) := Real.rpow_nonneg (by linarith [half_le_log_add_two' M]) _
  have hmaxC : Real.exp (C_γ * L ^ (7 / 8 : ℝ)) ≤ Real.exp (max C_γ 0 * L ^ (7 / 8 : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hL_nn)
  have hExp_ge1 : 1 ≤ Real.exp (max C_γ 0 * L ^ (7 / 8 : ℝ)) :=
    Real.one_le_exp (mul_nonneg (le_max_right _ _) hL_nn)
  have h1 : Real.exp (L ^ α) - 1 ≤ p.K_query * Real.exp (max C_γ 0 * L ^ (7 / 8 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left (le_trans h78 hmaxC) p.hK_query
    linarith
  have h2 := hdom M hMM₀
  dsimp [L] at h1 hExp_ge1
  linarith

end MinCostFlow.Expander.PathDSProg
