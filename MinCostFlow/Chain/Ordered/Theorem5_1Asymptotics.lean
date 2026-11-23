module

public import MinCostFlow.Chain.Ordered.Theorem5_1Helpers
public import MinCostFlow.Chain.Theorem5_1Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.1 Subpolynomial Asymptotics for the Ordered Chain (`jtree.tex`, pages 15 & 25–31)

Ordered-chain counterpart of `MinCostFlow/Chain/Theorem5_1Asymptotics.lean`. Reuses all numerical
asymptotic lemmas (`chosenD`, `alg2TimeFactor`, `alg2KappaLower`, `tendsto_log_alg2TimeFactor_div_log`,
`alg2TimeFactor_le_rpow`, `exp_rpow_le_half_one_add`) from `MinCostFlow.Chain`, and proves the
exponent bounds for `Ordered.alg2CollapsedFactor` (which carries `lemma511TimeFactor` with the
extra factor `3 * M₀^{1/d}`) with `theorem51RuntimeConstant C_γ C_ψ C_N = 64 + 21 C_γ + 4 C_ψ + C_N`:
* `theorem_5_1_asymptotic_exponents_at`, `theorem_5_1_asymptotic_exponents_own`,
  `theorem_5_1_asymptotic_exponents_relaxed`, `theorem_5_1_asymptotic_exponents`;
* `one_add_log_le_alg2CollapsedFactor` and `two_ceil_γℓ_succ_le_alg2TimeFactor`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

section Asymptotics

private lemma one_le_log_add_two {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ Real.log ((m : ℝ) + 2) := by
  have h3 : Real.exp 1 ≤ (m : ℝ) + 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [Real.exp_one_lt_three]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

private lemma exp_pow_nat (x : ℝ) (n : ℕ) : (Real.exp x) ^ n = Real.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Real.exp_add, Nat.cast_succ]; ring_nf

private lemma asymptotic_exponents_core
    (d : ℕ) (hd : 1 ≤ d)
    {C_γ C_ψ C_N L E B γℓ γr σtot σg cT cL Ψ_g M2d k logF_p logF_2 logN1 : ℝ}
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hL1 : 1 ≤ L) (hE1 : 1 ≤ E) (hB1 : 1 ≤ B)
    (hB_le_E : B ≤ E) (hd_mul_B : (d : ℝ) * B ≤ 2 * E) (hL_le_E : L ≤ Real.exp E)
    (hγℓ1 : 1 ≤ γℓ) (hγℓ : γℓ ≤ Real.exp (C_γ * B))
    (hγr1 : 1 ≤ γr) (hγr : γr ≤ Real.exp (C_γ * B))
    (hσtot : σtot ≤ Real.exp (C_γ * E))
    (hσg0 : 0 ≤ σg) (hσg : σg ≤ Real.exp (C_γ * B))
    (hcT0 : 0 ≤ cT) (hcT : cT ≤ Real.exp (C_γ * B))
    (hcL0 : 0 ≤ cL) (hcL : cL ≤ Real.exp (C_γ * B))
    (hΨ1 : 1 ≤ Ψ_g) (hΨ : Ψ_g ≤ Real.exp (C_ψ * B))
    (hM2d0 : 0 ≤ M2d) (hM2d : M2d ≤ Real.exp (2 * E))
    (hk0 : 0 ≤ k) (hk : k ≤ Real.exp (2 * E))
    (hd1 : (d : ℝ) + 1 ≤ Real.exp (3 * E))
    (hlogFp1 : 1 ≤ logF_p) (hlogFp : logF_p ≤ Real.exp (C_γ * E))
    (hlogF21 : 1 ≤ logF_2) (hlogF2 : logF_2 ≤ Real.exp (C_γ * E))
    (hlogN1_1 : 1 ≤ logN1) (hlogN1 : logN1 ≤ C_N * L) :
    1 / kappaBound d γℓ σtot σg ≤ Real.exp ((15 + 5 * C_γ) * E) ∧
    (3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
      2 * logN1 * (γℓ + 3)) *
      (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
      (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) +
      logN1 * (2 * (γℓ + 3) + 1) ≤
      Real.exp (theorem51RuntimeConstant C_γ C_ψ C_N * E) := by
  have hE_nn : 0 ≤ E := le_trans zero_le_one hE1
  have hL_nn : 0 ≤ L := le_trans zero_le_one hL1
  have hTwoB : ∀ m : ℕ, (2 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * B) := fun m => by
    have h2 : (2 : ℝ) ≤ Real.exp B := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
      (Real.exp_le_exp.mpr hB1)
    calc
      (2 : ℝ) ^ m ≤ (Real.exp B) ^ m := pow_le_pow_left₀ (by norm_num) h2 m
      _ = Real.exp ((m : ℝ) * B) := exp_pow_nat B m
  have hTwoE : ∀ m : ℕ, (2 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * E) := fun m =>
    le_trans (hTwoB m) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB_le_E (Nat.cast_nonneg m)))
  have hPowD : ∀ c : ℝ, 0 ≤ c → (Real.exp (c * B)) ^ d ≤ Real.exp ((2 * c) * E) :=
    fun c hc => by
    rw [exp_pow_nat]
    refine Real.exp_le_exp.mpr ?_
    calc
      (d : ℝ) * (c * B) = c * ((d : ℝ) * B) := by ring
      _ ≤ c * (2 * E) := mul_le_mul_of_nonneg_left hd_mul_B hc
      _ = (2 * c) * E := by ring
  have hBE_Cγ : Real.exp (C_γ * B) ≤ Real.exp (C_γ * E) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB_le_E hCγ)
  have hd1_sq : ((d : ℝ) + 1) ^ 2 ≤ Real.exp (6 * E) := by
    calc
      ((d : ℝ) + 1) ^ 2 ≤ (Real.exp (3 * E)) ^ 2 := pow_le_pow_left₀ (by positivity) hd1 2
      _ = Real.exp (6 * E) := by rw [exp_pow_nat]; ring_nf
  have h2d3_le : 2 * (d : ℝ) + 3 ≤ Real.exp (5 * E) := by
    have h1 : 2 * (d : ℝ) + 3 ≤ 2 ^ 2 * ((d : ℝ) + 1) := by linarith
    calc
      2 * (d : ℝ) + 3 ≤ 2 ^ 2 * ((d : ℝ) + 1) := h1
      _ ≤ Real.exp (2 * E) * Real.exp (3 * E) :=
        mul_le_mul (by simpa using hTwoE 2) hd1 (by positivity) (by positivity)
      _ = Real.exp (5 * E) := by rw [← Real.exp_add]; ring_nf
  have hσtot_le : σtot + 1 ≤ Real.exp ((1 + C_γ) * E) := by
    have h1_le : 1 ≤ Real.exp (C_γ * E) := Real.one_le_exp (mul_nonneg hCγ hE_nn)
    calc
      σtot + 1 ≤ 2 ^ 1 * Real.exp (C_γ * E) := by linarith only [hσtot, h1_le]
      _ ≤ Real.exp (1 * E) * Real.exp (C_γ * E) :=
        mul_le_mul (by simpa using hTwoE 1) le_rfl (by positivity) (by positivity)
      _ = Real.exp ((1 + C_γ) * E) := by rw [← Real.exp_add]; ring_nf
  have hγℓ_nn : 0 ≤ γℓ := le_trans zero_le_one hγℓ1
  have hγr_nn : 0 ≤ γr := le_trans zero_le_one hγr1
  have hκ_base : (2 * γℓ * (1 + 2 * σg)) ^ d ≤ Real.exp ((6 + 4 * C_γ) * E) := by
    have h1_le : 1 ≤ Real.exp (C_γ * B) := Real.one_le_exp (mul_nonneg hCγ (le_trans zero_le_one hB1))
    have hsg : 1 + 2 * σg ≤ 4 * Real.exp (C_γ * B) := by linarith only [hσg, h1_le]
    have hbase_le : 2 * γℓ * (1 + 2 * σg) ≤ Real.exp ((3 + 2 * C_γ) * B) := by
      calc
        2 * γℓ * (1 + 2 * σg) ≤ 2 * Real.exp (C_γ * B) * (4 * Real.exp (C_γ * B)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hγℓ (by norm_num)) hsg (by positivity) (by positivity)
        _ = 2 ^ 3 * (Real.exp (C_γ * B) * Real.exp (C_γ * B)) := by ring
        _ ≤ Real.exp (3 * B) * Real.exp ((2 * C_γ) * B) := by
          rw [← Real.exp_add]
          exact mul_le_mul (by simpa using hTwoB 3)
            (Real.exp_le_exp.mpr (by ring_nf; exact le_rfl)) (by positivity) (by positivity)
        _ = Real.exp ((3 + 2 * C_γ) * B) := by rw [← Real.exp_add]; ring_nf
    calc
      (2 * γℓ * (1 + 2 * σg)) ^ d ≤ (Real.exp ((3 + 2 * C_γ) * B)) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase_le d
      _ ≤ Real.exp ((2 * (3 + 2 * C_γ)) * E) := hPowD _ (by positivity)
      _ = Real.exp ((6 + 4 * C_γ) * E) := by ring_nf
  have hKappa_bound : 1 / kappaBound d γℓ σtot σg ≤ Real.exp ((15 + 5 * C_γ) * E) := by
    unfold kappaBound
    rw [one_div_one_div]
    calc
      (σtot + 1) * (((d : ℝ) + 1) * (2 * (d : ℝ) + 3) * (2 * γℓ * (1 + 2 * σg)) ^ d)
          ≤ Real.exp ((1 + C_γ) * E) *
              (Real.exp (3 * E) * Real.exp (5 * E) * Real.exp ((6 + 4 * C_γ) * E)) := by
        have h35 : ((d : ℝ) + 1) * (2 * (d : ℝ) + 3) ≤ Real.exp (3 * E) * Real.exp (5 * E) :=
          mul_le_mul hd1 h2d3_le (by positivity) (by positivity)
        have h35k : ((d : ℝ) + 1) * (2 * (d : ℝ) + 3) * (2 * γℓ * (1 + 2 * σg)) ^ d ≤
            Real.exp (3 * E) * Real.exp (5 * E) * Real.exp ((6 + 4 * C_γ) * E) :=
          mul_le_mul h35 hκ_base (by positivity) (by positivity)
        exact mul_le_mul hσtot_le h35k (by positivity) (by positivity)
      _ = Real.exp ((15 + 5 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hCfac_le : 3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p ≤
      Real.exp ((16 + 14 * C_γ) * E) := by
    have hcoeff : 3 * (8 * cT + 81 * cL + 430) ≤ Real.exp ((11 + C_γ) * E) := by
      set X := Real.exp (C_γ * E)
      have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hCγ hE_nn)
      have hcT_X : cT ≤ X := le_trans hcT hBE_Cγ
      have hcL_X : cL ≤ X := le_trans hcL hBE_Cγ
      have h211 : 3 * (8 * cT + 81 * cL + 430) ≤ 2 ^ 11 * X := by linarith only [hX1, hcT_X, hcL_X]
      calc
        3 * (8 * cT + 81 * cL + 430) ≤ 2 ^ 11 * X := h211
        _ ≤ Real.exp (11 * E) * X :=
          mul_le_mul_of_nonneg_right (by simpa using hTwoE 11) (by positivity)
        _ = Real.exp ((11 + C_γ) * E) := by simp only [X]; rw [← Real.exp_add]; ring_nf
    have hγprod : γr * γℓ ^ (3 * d + 2) ≤ Real.exp ((12 * C_γ) * E) := by
      have hE1B : 1 ≤ Real.exp (C_γ * B) := Real.one_le_exp (mul_nonneg hCγ (le_trans zero_le_one hB1))
      have h1 : γr * γℓ ^ (3 * d + 2) ≤ Real.exp (C_γ * B) * (Real.exp (C_γ * B)) ^ (3 * d + 2) :=
        mul_le_mul hγr (pow_le_pow_left₀ hγℓ_nn hγℓ _) (by positivity) (by positivity)
      have h2 : Real.exp (C_γ * B) * (Real.exp (C_γ * B)) ^ (3 * d + 2) =
          (Real.exp (C_γ * B)) ^ (3 * d + 3) := by rw [← pow_succ']
      have h3 : (Real.exp (C_γ * B)) ^ (3 * d + 3) ≤ (Real.exp (C_γ * B)) ^ (6 * d) :=
        pow_le_pow_right₀ hE1B (by omega)
      calc
        γr * γℓ ^ (3 * d + 2) ≤ (Real.exp (C_γ * B)) ^ (6 * d) := le_trans h1 (h2 ▸ h3)
        _ = ((Real.exp (C_γ * B)) ^ d) ^ 6 := by rw [mul_comm 6 d, pow_mul]
        _ ≤ (Real.exp ((2 * C_γ) * E)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) (hPowD _ hCγ) 6
        _ = Real.exp ((12 * C_γ) * E) := by rw [exp_pow_nat]; ring_nf
    have h12 := mul_le_mul hd1 hcoeff (by positivity) (by positivity)
    have h123 := mul_le_mul h12 hM2d hM2d0 (by positivity)
    have h1234 := mul_le_mul h123 hγprod (by positivity) (by positivity)
    calc
      3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p
          = ((d : ℝ) + 1) * (3 * (8 * cT + 81 * cL + 430)) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p := by ring
      _ ≤ Real.exp (3 * E) * Real.exp ((11 + C_γ) * E) * Real.exp (2 * E) *
            Real.exp ((12 * C_γ) * E) * Real.exp (C_γ * E) :=
        mul_le_mul h1234 hlogFp (le_trans zero_le_one hlogFp1) (by positivity)
      _ = Real.exp ((16 + 14 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hlogN_le : logN1 ≤ Real.exp ((C_N + 1) * E) := by
    have hCN_exp : C_N ≤ Real.exp (C_N * E) := by
      have h1 : C_N ≤ Real.exp C_N := by linarith only [Real.add_one_le_exp C_N]
      exact le_trans h1 (Real.exp_le_exp.mpr (le_mul_of_one_le_right (by linarith only [hCN]) hE1))
    calc
      logN1 ≤ C_N * L := hlogN1
      _ ≤ Real.exp (C_N * E) * Real.exp E := mul_le_mul hCN_exp hL_le_E hL_nn (by positivity)
      _ = Real.exp ((C_N + 1) * E) := by rw [← Real.exp_add]; ring_nf
  have hγℓ3 : γℓ + 3 ≤ Real.exp ((2 + C_γ) * E) := by
    set X := Real.exp (C_γ * E)
    have h1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hCγ hE_nn)
    have hγ_X : γℓ ≤ X := le_trans hγℓ hBE_Cγ
    calc
      γℓ + 3 ≤ 2 ^ 2 * X := by linarith only [h1, hγ_X]
      _ ≤ Real.exp (2 * E) * X :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 2) (by positivity)
      _ = Real.exp ((2 + C_γ) * E) := by simp only [X]; rw [← Real.exp_add]; ring_nf
  have hSfac_le : ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1 ≤
      Real.exp ((29 + 4 * C_ψ) * E) := by
    have hbase : 20 * Ψ_g ≤ Real.exp ((5 + C_ψ) * B) := by
      have h1 : (1 : ℝ) ≤ Real.exp (C_ψ * B) := Real.one_le_exp (mul_nonneg hCψ (le_trans zero_le_one hB1))
      calc
        20 * Ψ_g ≤ 2 ^ 5 * Real.exp (C_ψ * B) := by linarith only [hΨ, h1]
        _ ≤ Real.exp (5 * B) * Real.exp (C_ψ * B) :=
          mul_le_mul_of_nonneg_right (by simpa using hTwoB 5) (by positivity)
        _ = Real.exp ((5 + C_ψ) * B) := by rw [← Real.exp_add]; ring_nf
    have h20pow : (20 * Ψ_g) ^ (d + 1) ≤ Real.exp ((20 + 4 * C_ψ) * E) := by
      have h1 : (1 : ℝ) ≤ 20 * Ψ_g := by linarith only [hΨ1]
      calc
        (20 * Ψ_g) ^ (d + 1) ≤ (20 * Ψ_g) ^ (2 * d) := pow_le_pow_right₀ h1 (by omega)
        _ ≤ (Real.exp ((5 + C_ψ) * B)) ^ (2 * d) := pow_le_pow_left₀ (by positivity) hbase _
        _ = ((Real.exp ((5 + C_ψ) * B)) ^ d) ^ 2 := by rw [mul_comm 2 d, pow_mul]
        _ ≤ (Real.exp ((2 * (5 + C_ψ)) * E)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hPowD _ (by positivity)) 2
        _ = Real.exp ((20 + 4 * C_ψ) * E) := by rw [exp_pow_nat]; ring_nf
    have hprod : ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k ≤
        Real.exp (6 * E) * Real.exp ((20 + 4 * C_ψ) * E) * Real.exp (2 * E) :=
      mul_le_mul (mul_le_mul hd1_sq h20pow (by positivity) (by positivity)) hk hk0 (by positivity)
    have h28 : Real.exp (6 * E) * Real.exp ((20 + 4 * C_ψ) * E) * Real.exp (2 * E) =
        Real.exp ((28 + 4 * C_ψ) * E) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h1_le : (1 : ℝ) ≤ Real.exp ((28 + 4 * C_ψ) * E) :=
      Real.one_le_exp (mul_nonneg (by linarith only [hCψ]) hE_nn)
    calc
      ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1 ≤ 2 ^ 1 * Real.exp ((28 + 4 * C_ψ) * E) := by
        linarith only [hprod, h28, h1_le]
      _ ≤ Real.exp (1 * E) * Real.exp ((28 + 4 * C_ψ) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity)
      _ = Real.exp ((29 + 4 * C_ψ) * E) := by rw [← Real.exp_add]; ring_nf
  have hRfac_le : 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1 ≤
      Real.exp ((16 + 3 * C_γ) * E) := by
    have h2d : (2 : ℝ) ^ d ≤ Real.exp (2 * E) :=
      le_trans (hTwoB d) (Real.exp_le_exp.mpr hd_mul_B)
    have hγrd : γr ^ d ≤ Real.exp ((2 * C_γ) * E) :=
      le_trans (pow_le_pow_left₀ hγr_nn hγr _) (hPowD _ hCγ)
    have hmain : 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 ≤ Real.exp ((14 + 3 * C_γ) * E) := by
      have h1 := mul_le_mul (mul_le_mul (mul_le_mul hd1_sq h2d (by positivity) (by positivity))
        hγrd (by positivity) (by positivity)) hk hk0 (by positivity)
      have h2 := mul_le_mul h1 hlogF2 (le_trans zero_le_one hlogF21) (by positivity)
      have h16 : (16 : ℝ) ≤ Real.exp (4 * E) := by simpa [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num] using hTwoE 4
      have h3 : 16 * (((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2) ≤
          Real.exp (4 * E) * (Real.exp (6 * E) * Real.exp (2 * E) * Real.exp ((2 * C_γ) * E) *
            Real.exp (2 * E) * Real.exp (C_γ * E)) :=
        mul_le_mul h16 h2 (by positivity) (by positivity)
      have h_eq : Real.exp (4 * E) * (Real.exp (6 * E) * Real.exp (2 * E) * Real.exp ((2 * C_γ) * E) *
          Real.exp (2 * E) * Real.exp (C_γ * E)) = Real.exp ((14 + 3 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      calc 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2
          = 16 * (((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2) := by ring
        _ ≤ Real.exp ((14 + 3 * C_γ) * E) := h_eq ▸ h3
    have hd_sub : ((d : ℝ) + 1) ^ 2 ≤ Real.exp ((14 + 3 * C_γ) * E) :=
      le_trans hd1_sq (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith only [hCγ]) hE_nn))
    have h1_sub : (1 : ℝ) ≤ Real.exp ((14 + 3 * C_γ) * E) :=
      Real.one_le_exp (mul_nonneg (by linarith only [hCγ]) hE_nn)
    calc
      16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1
          ≤ 3 * Real.exp ((14 + 3 * C_γ) * E) := by linarith only [hmain, hd_sub, h1_sub]
      _ ≤ 2 ^ 2 * Real.exp ((14 + 3 * C_γ) * E) := by
        linarith only [Real.exp_pos ((14 + 3 * C_γ) * E)]
      _ ≤ Real.exp (2 * E) * Real.exp ((14 + 3 * C_γ) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 2) (by positivity)
      _ = Real.exp ((16 + 3 * C_γ) * E) := by rw [← Real.exp_add]; ring_nf
  have hColl :
      (3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
        2 * logN1 * (γℓ + 3)) *
        (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
        (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) +
        logN1 * (2 * (γℓ + 3) + 1) ≤
      Real.exp (theorem51RuntimeConstant C_γ C_ψ C_N * E) := by
    have hLctTerm : 2 * logN1 * (γℓ + 3) ≤ Real.exp ((4 + C_γ + C_N) * E) := by
      have h12 : 2 * logN1 ≤ Real.exp (1 * E) * Real.exp ((C_N + 1) * E) :=
        mul_le_mul (by simpa using hTwoE 1) hlogN_le (le_trans zero_le_one hlogN1_1) (by positivity)
      have h123 := mul_le_mul h12 hγℓ3 (by linarith only [hγℓ_nn]) (by positivity)
      have h_eq : Real.exp (1 * E) * Real.exp ((C_N + 1) * E) * Real.exp ((2 + C_γ) * E) =
          Real.exp ((4 + C_γ + C_N) * E) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      linarith only [h123, h_eq]
    have hSumPref :
        3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
          2 * logN1 * (γℓ + 3) ≤ Real.exp ((17 + 18 * C_γ + C_N) * E) := by
      have h_a : Real.exp ((16 + 14 * C_γ) * E) ≤ Real.exp ((16 + 18 * C_γ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hCγ, hCN]) hE_nn)
      have h_b : Real.exp ((4 + C_γ + C_N) * E) ≤ Real.exp ((16 + 18 * C_γ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hCγ]) hE_nn)
      have hsum :
          3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
            2 * logN1 * (γℓ + 3) ≤ 2 ^ 1 * Real.exp ((16 + 18 * C_γ + C_N) * E) := by
        linarith only [hCfac_le, hLctTerm, h_a, h_b]
      calc
        _ ≤ Real.exp (1 * E) * Real.exp ((16 + 18 * C_γ + C_N) * E) :=
          le_trans hsum (mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity))
        _ = Real.exp ((17 + 18 * C_γ + C_N) * E) := by rw [← Real.exp_add]; ring_nf
    have hBig :
        (3 * ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M2d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
          2 * logN1 * (γℓ + 3)) *
          (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
          (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) ≤
        Real.exp ((63 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
      have h12 := mul_le_mul hSumPref hSfac_le (by positivity) (by positivity)
      have h123 := mul_le_mul h12 hRfac_le (by positivity) (by positivity)
      have h_eq : Real.exp ((17 + 18 * C_γ + C_N) * E) * Real.exp ((29 + 4 * C_ψ) * E) *
          Real.exp ((16 + 3 * C_γ) * E) = Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hle63 : Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) ≤
          Real.exp ((63 + 21 * C_γ + 4 * C_ψ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hE_nn)
      exact le_trans h123 (h_eq.le.trans hle63)
    have hTail : logN1 * (2 * (γℓ + 3) + 1) ≤
        Real.exp ((63 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
      have h2γ1 : 2 * (γℓ + 3) + 1 ≤ 2 ^ 2 * (γℓ + 3) := by linarith only [hγℓ_nn]
      have h21 : 2 * (γℓ + 3) + 1 ≤ Real.exp (2 * E) * Real.exp ((2 + C_γ) * E) :=
        le_trans h2γ1 (mul_le_mul (by simpa using hTwoE 2) hγℓ3 (by linarith only [hγℓ_nn]) (by positivity))
      have h12 := mul_le_mul hlogN_le h21 (by positivity) (by positivity)
      have h_eq : Real.exp ((C_N + 1) * E) * (Real.exp (2 * E) * Real.exp ((2 + C_γ) * E)) =
          Real.exp ((5 + C_γ + C_N) * E) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      exact le_trans h12 (h_eq ▸ Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith only [hCγ, hCψ]) hE_nn))
    calc
      _ ≤ 2 ^ 1 * Real.exp ((63 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by linarith only [hBig, hTail]
      _ ≤ Real.exp (1 * E) * Real.exp ((63 + 21 * C_γ + 4 * C_ψ + C_N) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity)
      _ = Real.exp (theorem51RuntimeConstant C_γ C_ψ C_N * E) := by
        unfold theorem51RuntimeConstant
        rw [← Real.exp_add]; ring_nf
  exact ⟨hKappa_bound, hColl⟩

/-- Parameterized Theorem 5.1 asymptotic exponent lemma for the ordered chain (`jtree.tex` page 30):
for any subpolynomial sparse-core growth exponent `β ∈ (0, 1)`,
setting `d = chosenD β cfg.P.M₀` bounds both `1 / alg2KappaAt` and `Ordered.alg2CollapsedFactor`
by `exp(C * log(M₀+2)^{(1+β)/2} * log(log(M₀+2)+2))`, with `C_rt = theorem51RuntimeConstant C_γ C_ψ C_N`. -/
theorem theorem_5_1_asymptotic_exponents_at (n_last : ℕ) {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last n_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    1 / alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) := by
  let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  let LL := Real.log (L + 2)
  have hL1 : 1 ≤ L := one_le_log_add_two hM₀
  have hL_pos : 0 < L := by linarith
  have hLL1 : 1 ≤ LL := by
    have : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_three]
    simpa only [LL, Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  have hDb := chosenD_bounds hβ1 hM₀
  have hd_lo : L ^ ((1 - β) / 2) ≤ (cfg.P.d : ℝ) := by rw [hD]; exact hDb.2.1
  have hd_hi : (cfg.P.d : ℝ) ≤ 2 * L ^ ((1 - β) / 2) := by rw [hD]; exact hDb.2.2
  have ha0 : 0 ≤ (1 + β) / 2 := by linarith
  have ha_ge_β : β ≤ (1 + β) / 2 := by linarith
  have hLa1 : 1 ≤ L ^ ((1 + β) / 2) := Real.one_le_rpow hL1 ha0
  have hLβ1 : 1 ≤ L ^ β := Real.one_le_rpow hL1 hβ0.le
  set E := L ^ ((1 + β) / 2) * LL
  set B := L ^ β * LL
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hLa1 hLL1
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hLβ1 hLL1
  have hB_le_E : B ≤ E :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1 ha_ge_β) (by linarith)
  have hd_mul_B : (cfg.P.d : ℝ) * B ≤ 2 * E := by
    have hpow : L ^ ((1 - β) / 2) * L ^ β = L ^ ((1 + β) / 2) := by
      rw [← Real.rpow_add hL_pos]; congr 1; ring
    calc
      (cfg.P.d : ℝ) * B ≤ (2 * L ^ ((1 - β) / 2)) * (L ^ β * LL) :=
        mul_le_mul_of_nonneg_right hd_hi (by positivity)
      _ = 2 * (L ^ ((1 - β) / 2) * L ^ β) * LL := by ring
      _ = 2 * E := by rw [hpow]; simp only [E]; ring
  have hL_le_E : L ≤ Real.exp E := by
    have h1 : L ≤ Real.exp LL := by rw [Real.exp_log (by linarith)]; linarith
    have hLL_le_E : LL ≤ E := by
      have : 1 * LL ≤ L ^ ((1 + β) / 2) * LL := mul_le_mul_of_nonneg_right hLa1 (by linarith)
      linarith
    exact le_trans h1 (Real.exp_le_exp.mpr hLL_le_E)
  have hTwoE2 : (2 : ℝ) ^ 2 ≤ Real.exp (2 * E) := by
    have h2 : (2 : ℝ) ≤ Real.exp E := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
      (Real.exp_le_exp.mpr hE1)
    calc
      (2 : ℝ) ^ 2 ≤ (Real.exp E) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = Real.exp (2 * E) := by rw [exp_pow_nat]; simp
  have hM1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) := by exact_mod_cast hM₀
  have hM_pos : (0 : ℝ) < (cfg.P.M₀ : ℝ) := by linarith
  have hd_pos : (0 : ℝ) < (cfg.P.d : ℝ) := Nat.cast_pos.mpr cfg.P.hd
  have hM1d0 : 0 ≤ (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := by positivity
  have hM1d : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ Real.exp (1 * E) := by
    have hlogM : Real.log (cfg.P.M₀ : ℝ) ≤ L :=
      Real.log_le_log hM_pos (by linarith [hM_pos])
    have hdiv_le : Real.log (cfg.P.M₀ : ℝ) / (cfg.P.d : ℝ) ≤ L / L ^ ((1 - β) / 2) :=
      le_trans (div_le_div_of_nonneg_right hlogM hd_pos.le)
        (div_le_div_of_nonneg_left (by linarith) (by positivity) hd_lo)
    have hL_pow_div : L / L ^ ((1 - β) / 2) = L ^ ((1 + β) / 2) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_sub hL_pos]
      congr 1; ring
    have hexp_le : Real.log (cfg.P.M₀ : ℝ) / (cfg.P.d : ℝ) ≤ 1 * E := by
      rw [hL_pow_div] at hdiv_le
      have hLE : L ^ ((1 + β) / 2) ≤ E :=
        le_mul_of_one_le_right (by linarith only [hLa1]) hLL1
      linarith only [hdiv_le, hLE]
    rw [Real.rpow_def_of_pos hM_pos, mul_one_div]
    exact Real.exp_le_exp.mpr hexp_le
  have hM2d0 : 0 ≤ (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) := by positivity
  have hM2d : (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) ≤ Real.exp (2 * E) := by
    have hsq : (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ)) = ((cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM_pos.le]
      congr 1; push_cast; ring
    calc
      (cfg.P.M₀ : ℝ) ^ (2 / (cfg.P.d : ℝ))
          = ((cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ))) ^ (2 : ℕ) := hsq
      _ ≤ (Real.exp (1 * E)) ^ (2 : ℕ) := pow_le_pow_left₀ hM1d0 hM1d 2
      _ = Real.exp (2 * E) := by rw [exp_pow_nat]; ring_nf
  have hk_le : (cfg.P.k : ℝ) ≤ Real.exp (2 * E) := by
    have h21 : (2 : ℝ) ≤ Real.exp (1 * E) := by
      simpa using le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_le_exp.mpr hE1)
    calc
      (cfg.P.k : ℝ) ≤ 2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := cfg.P.hk_upper
      _ ≤ Real.exp (1 * E) * Real.exp (1 * E) :=
        mul_le_mul h21 hM1d hM1d0 (by positivity)
      _ = Real.exp (2 * E) := by rw [← Real.exp_add]; ring_nf
  have hd1_le : (cfg.P.d : ℝ) + 1 ≤ Real.exp (3 * E) := by
    have hd_L : (cfg.P.d : ℝ) + 1 ≤ 4 * L := by
      have h1 : L ^ ((1 - β) / 2) ≤ L := by
        calc
          L ^ ((1 - β) / 2) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
          _ = L := Real.rpow_one L
      linarith
    calc
      (cfg.P.d : ℝ) + 1 ≤ 2 ^ 2 * L := by linarith
      _ ≤ Real.exp (2 * E) * Real.exp E :=
        mul_le_mul hTwoE2 hL_le_E hL_pos.le (by positivity)
      _ = Real.exp (3 * E) := by rw [← Real.exp_add]; ring_nf
  have hlogF0_1 : 1 ≤ logFactor cfg.P cfg.N₀ := one_le_logFactor cfg.P cfg.N₀
  have hlogF_1 : 1 ≤ 2 * logFactor cfg.P cfg.N₀ := by linarith
  have hlogF_E : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * E) := by
    simpa only [L, LL, E, mul_assoc] using hlogF
  have hlogF_p : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1) ≤
      Real.exp (C_γ * E) :=
    le_trans (pow_le_pow_right₀ hlogF_1 (by omega :
      max cfg.TP.p_T cfg.LP.p_last + 1 ≤ max cfg.TP.p_T cfg.LP.p_last + 3)) hlogF_E
  have hlogF_2 : (logFactor cfg.P cfg.N₀) ^ 2 ≤ Real.exp (C_γ * E) := by
    have hle : (logFactor cfg.P cfg.N₀) ^ 2 ≤ (2 * logFactor cfg.P cfg.N₀) ^ 2 := by
      gcongr; linarith
    exact le_trans hle (le_trans (pow_le_pow_right₀ hlogF_1 (by omega :
      2 ≤ max cfg.TP.p_T cfg.LP.p_last + 3)) hlogF_E)
  have hlogN1 : 1 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  have hcore := asymptotic_exponents_core cfg.P.d cfg.P.hd hCγ hCψ hCN hL1 hE1 hB1
    hB_le_E hd_mul_B hL_le_E
    (hTP.2.2.1 (cfg.P.M₀ ^ 2)) (by simpa only [L, LL, B, mul_assoc] using hγℓ)
    (hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)) (by simpa only [L, LL, B, mul_assoc] using hγr)
    (max_le (by simpa only [L, LL, E, mul_assoc] using hσT)
      (by simpa only [L, LL, E, mul_assoc] using hσL))
    (le_max_left _ _) (by simpa only [L, LL, B, mul_assoc] using hσM)
    hTP.2.2.2.2.2.2.2.2.2 (by simpa only [L, LL, B, mul_assoc] using hcT)
    hLP.2.2.2.2 (by simpa only [L, LL, B, mul_assoc] using hcL)
    (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) (by simpa only [L, LL, B, mul_assoc] using hΨ)
    hM2d0 hM2d (Nat.cast_nonneg _) hk_le hd1_le
    (one_le_pow₀ hlogF_1) hlogF_p (one_le_pow₀ hlogF0_1) hlogF_2
    hlogN1 hlogN
  refine ⟨?_, ?_⟩
  · have h1 : 1 / alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last ≤
        Real.exp ((15 + 5 * C_γ) * E) := by
      simpa only [alg2KappaAt, alg2SigmaTotAt, alg2SigmaGame] using hcore.1
    simpa only [E, mul_assoc] using h1
  · have h2 : alg2CollapsedFactor cfg ≤ Real.exp (theorem51RuntimeConstant C_γ C_ψ C_N * E) := by
      unfold alg2CollapsedFactor lemma511TimeFactor
      dsimp only
      exact hcore.2
    simpa only [E, mul_assoc] using h2

/-- Parameterized Theorem 5.1 asymptotic exponent lemma (`jtree.tex` page 30),
specialized to the own-level vertex cap `n_last = levelM cfg.TP cfg.P cfg.P.d + 1`. -/
theorem theorem_5_1_asymptotic_exponents_own {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_at (levelM cfg.TP cfg.P cfg.P.d + 1) hβ0 hβ1 hM₀ hD hTP hLP
    hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN

theorem theorem_5_1_asymptotic_exponents_relaxed {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    1 / alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_at cfg.N₀ hβ0 hβ1 hM₀ hD hTP hLP hCγ hCψ hCN hγℓ hγr
    hσT hσL hσM hcT hcL hΨ hlogF hlogN

/-- Parameterized Theorem 5.1 asymptotic exponent lemma (`jtree.tex` page 30), taking `L^β` bounds
on `hσT` and `hσL` and delegating to `theorem_5_1_asymptotic_exponents_relaxed`. -/
theorem theorem_5_1_asymptotic_exponents {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    1 / alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_relaxed hβ0 hβ1 hM₀ hD hTP hLP hCγ hCψ hCN hγℓ hγr
    (exp_rpow_le_half_one_add hM₀ hβ1 hCγ hσT)
    (exp_rpow_le_half_one_add hM₀ hβ1 hCγ hσL)
    hσM hcT hcL hΨ hlogF hlogN

lemma one_add_log_le_alg2CollapsedFactor (cfg : Alg2Config) (hV : cfg.ValidOrdNoHidden) :
    1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ alg2CollapsedFactor cfg := by
  have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have h2γ : 1 ≤ 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1 := by linarith
  have hCfac_nn : 0 ≤ lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀ := by
    unfold lemma511TimeFactor
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2); have := one_le_logFactor cfg.P cfg.N₀
    positivity
  have hNonneg : 0 ≤ (lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀ +
      2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) *
      (((cfg.P.d : ℝ) + 1) ^ 2 * (20 * alg2PsiGame cfg.Ψ cfg.P.M₀) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1) *
      (16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
        (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2 + ((cfg.P.d : ℝ) + 1) ^ 2 + 1) := by
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2); have := one_le_logFactor cfg.P cfg.N₀
    have := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀; positivity
  unfold alg2CollapsedFactor
  dsimp only
  nlinarith

lemma two_ceil_γℓ_succ_le_alg2TimeFactor {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) ≤
      alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ := by
  have hBase := Chain.two_ceil_γℓ_succ_le_alg2TimeFactor (cfg := cfg) hβ0 hβ1 hM₀ hTP hCγ hCψ hCN hγℓ
  refine le_trans hBase ?_
  unfold alg2TimeFactor theorem51RuntimeConstant
  have hL1 : 1 ≤ Real.log ((cfg.P.M₀ : ℝ) + 2) := one_le_log_add_two hM₀
  have hLL_nn : 0 ≤ Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hrpow_nn : 0 ≤ (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) :=
    Real.rpow_nonneg (by linarith) _
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hrpow_nn) hLL_nn)

end Asymptotics

end MinCostFlow.Chain.Ordered
