module

public import MinCostFlow.Chain.Algorithm1UpdateProofs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collapsing Runtime and Tree-Update Bounds (Lemma 5.11 Helpers)

Split from `MinCostFlow.Chain.Lemma5_11`: `powTerm`, `logFactor` bounds,
and collapsing bounds (`totalRuntime_collapse*`, `totalTreeUpdates_collapse*`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section CollapsingBounds

/-- Level weight `M₀^{1 - i/d}` appearing in Lemma 5.11's runtime and tree-update bounds. -/
noncomputable def powTerm (P : ChainParams) (i : ℕ) : ℝ :=
  (P.M₀ : ℝ) ^ (1 - (i : ℝ) / (P.d : ℝ))

lemma powTerm_zero (P : ChainParams) : powTerm P 0 = (P.M₀ : ℝ) := by
  simp [powTerm]

lemma one_le_powTerm (P : ChainParams) {i : ℕ} (hi : i ≤ P.d) : 1 ≤ powTerm P i := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hd_pos : (0 : ℝ) < P.d := Nat.cast_pos.mpr P.hd
  have hexp : 0 ≤ 1 - (i : ℝ) / (P.d : ℝ) := by
    have hi_le : (i : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hi
    have hdiv : (i : ℝ) / (P.d : ℝ) ≤ 1 := (div_le_one hd_pos).mpr hi_le
    linarith
  exact Real.one_le_rpow hM1 hexp

lemma powTerm_antitone (P : ChainParams) {i j : ℕ} (hij : i ≤ j) :
    powTerm P j ≤ powTerm P i := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hd_pos : (0 : ℝ) < P.d := Nat.cast_pos.mpr P.hd
  have hij_real : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hdiv : (i : ℝ) / (P.d : ℝ) ≤ (j : ℝ) / (P.d : ℝ) :=
    div_le_div_of_nonneg_right hij_real hd_pos.le
  exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)

lemma div_pow_le_powTerm (P : ChainParams) {i : ℕ} (hi : i ≤ P.d) :
    (P.M₀ : ℝ) / (P.k : ℝ) ^ i ≤ powTerm P i := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hM_pos : (0 : ℝ) < (P.M₀ : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have hd_pos : (0 : ℝ) < (P.d : ℝ) := Nat.cast_pos.mpr P.hd
  have hk_pow : (P.M₀ : ℝ) ≤ (P.k : ℝ) ^ P.d := by exact_mod_cast P.hk_pow
  have hLHS : ((P.M₀ : ℝ) / (P.k : ℝ) ^ i) ^ P.d ≤ ((P.M₀ : ℝ) ^ (P.d - i)) := by
    have hpow_ki : ((P.k : ℝ) ^ i) ^ P.d = ((P.k : ℝ) ^ P.d) ^ i := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have hkd_i : (P.M₀ : ℝ) ^ i ≤ ((P.k : ℝ) ^ P.d) ^ i :=
      pow_le_pow_left₀ hM_pos.le hk_pow i
    have hdiv_eq : (P.M₀ : ℝ) ^ P.d / (P.M₀ : ℝ) ^ i = (P.M₀ : ℝ) ^ (P.d - i) := by
      rw [div_eq_iff (pow_ne_zero i hM_pos.ne'), ← pow_add, Nat.sub_add_cancel hi]
    calc
      ((P.M₀ : ℝ) / (P.k : ℝ) ^ i) ^ P.d
          = (P.M₀ : ℝ) ^ P.d / ((P.k : ℝ) ^ i) ^ P.d := div_pow _ _ _
      _ = (P.M₀ : ℝ) ^ P.d / ((P.k : ℝ) ^ P.d) ^ i := by rw [hpow_ki]
      _ ≤ (P.M₀ : ℝ) ^ P.d / (P.M₀ : ℝ) ^ i :=
        div_le_div_of_nonneg_left (pow_nonneg hM_pos.le P.d) (pow_pos hM_pos i) hkd_i
      _ = (P.M₀ : ℝ) ^ (P.d - i) := hdiv_eq
  have hRHS : (powTerm P i) ^ P.d = (P.M₀ : ℝ) ^ (P.d - i) := by
    unfold powTerm
    rw [← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 - (i : ℝ) / (P.d : ℝ))) P.d,
      ← Real.rpow_mul hM_pos.le]
    have hexp : (1 - (i : ℝ) / (P.d : ℝ)) * (P.d : ℝ) = ((P.d - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hi]
      field_simp [hd_pos.ne']
    rw [hexp, Real.rpow_natCast]
  have hPowLe : ((P.M₀ : ℝ) / (P.k : ℝ) ^ i) ^ P.d ≤ (powTerm P i) ^ P.d := by
    rw [hRHS]; exact hLHS
  exact le_of_pow_le_pow_left₀ P.hd.ne' (le_trans zero_le_one (one_le_powTerm P hi)) hPowLe

lemma gamma_div_mul_le_powTerm (TP : SparseCoreParams) (P : ChainParams)
    (hTP : TP.Valid) {i₀ j : ℕ} (hi₀ : i₀ ≤ j) (hj : j ≤ P.d) :
    (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ j ≤ (TP.γ_ℓ (P.M₀ ^ 2)) ^ P.d * powTerm P i₀ := by
  have hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.1 (P.M₀ ^ 2)
  have hγj : (TP.γ_ℓ (P.M₀ ^ 2)) ^ j ≤ (TP.γ_ℓ (P.M₀ ^ 2)) ^ P.d := pow_le_pow_right₀ hγ1 hj
  have hdiv := div_pow_le_powTerm P hj
  have hpow : powTerm P j ≤ powTerm P i₀ := powTerm_antitone P hi₀
  have hpow_nn : 0 ≤ (P.M₀ : ℝ) / (P.k : ℝ) ^ j := by positivity
  calc
    (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ j
        = (TP.γ_ℓ (P.M₀ ^ 2)) ^ j * ((P.M₀ : ℝ) / (P.k : ℝ) ^ j) := by rw [div_pow]; ring
    _ ≤ (TP.γ_ℓ (P.M₀ ^ 2)) ^ P.d * powTerm P j :=
      mul_le_mul hγj hdiv hpow_nn (pow_nonneg (le_trans zero_le_one hγ1) P.d)
    _ ≤ (TP.γ_ℓ (P.M₀ ^ 2)) ^ P.d * powTerm P i₀ :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg (le_trans zero_le_one hγ1) P.d)

lemma one_le_logFactor (P : ChainParams) (n : ℕ) : 1 ≤ logFactor P n := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hexp : Real.exp 1 ≤ (P.M₀ : ℝ) + (n : ℝ) + 2 := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((P.M₀ : ℝ) + (n : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) hexp

lemma log_ten_sq_add_two_le (TP : SparseCoreParams) (P : ChainParams)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2)) (n : ℕ) :
    Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) ≤ 3 * logFactor P n := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hM0 : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have harg : 10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2 ≤ ((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3 := by
    have h1 : 10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2 ≤ 10 * (P.M₀ : ℝ) ^ 2 + 2 := by
      have hmul : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) ≤ (P.M₀ : ℝ) * (P.M₀ : ℝ) :=
        mul_le_mul_of_nonneg_left hγM₀ hM0
      nlinarith
    have h2 : 10 * (P.M₀ : ℝ) ^ 2 + 2 ≤ ((P.M₀ : ℝ) + 2) ^ 3 := by
      have hsq : 0 ≤ (P.M₀ : ℝ) * ((P.M₀ : ℝ) - 2) ^ 2 := mul_nonneg hM0 (sq_nonneg _)
      nlinarith
    have h3 : ((P.M₀ : ℝ) + 2) ^ 3 ≤ ((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    linarith
  have hγ0 : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one hγ1
  calc
    Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
        ≤ Real.log (((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3) :=
      Real.log_le_log (by positivity) harg
    _ = 3 * logFactor P n := by
      rw [Real.log_pow]; simp [logFactor]

lemma log_five_add_two_le (P : ChainParams) (n : ℕ) :
    Real.log (5 * (P.M₀ : ℝ) + 2) ≤ 3 * logFactor P n := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have harg : 5 * (P.M₀ : ℝ) + 2 ≤ ((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3 := by
    have hM0 : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg _
    have h1 : 5 * (P.M₀ : ℝ) + 2 ≤ ((P.M₀ : ℝ) + 2) ^ 3 := by
      calc
        5 * (P.M₀ : ℝ) + 2 ≤ 12 * (P.M₀ : ℝ) + 8 := by linarith
        _ ≤ (P.M₀ : ℝ) ^ 3 + 6 * (P.M₀ : ℝ) ^ 2 + 12 * (P.M₀ : ℝ) + 8 := by
          linarith [pow_nonneg hM0 2, pow_nonneg hM0 3]
        _ = ((P.M₀ : ℝ) + 2) ^ 3 := by ring
    have h2 : ((P.M₀ : ℝ) + 2) ^ 3 ≤ ((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    linarith
  calc
    Real.log (5 * (P.M₀ : ℝ) + 2)
        ≤ Real.log (((P.M₀ : ℝ) + (n : ℝ) + 2) ^ 3) :=
      Real.log_le_log (by linarith) harg
    _ = 3 * logFactor P n := by
      rw [Real.log_pow]; simp [logFactor]

lemma log_two_add_two_le (P : ChainParams) (n : ℕ) :
    Real.log (2 * (P.M₀ : ℝ) + 2) ≤ 3 * logFactor P n := by
  have hM_nn : (0 : ℝ) ≤ (P.M₀ : ℝ) := Nat.cast_nonneg P.M₀
  have hle : Real.log (2 * (P.M₀ : ℝ) + 2) ≤ Real.log (5 * (P.M₀ : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  exact le_trans hle (log_five_add_two_le P n)

lemma opRuntimeBudget_collapse (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) {n i₀ : ℕ} (hi₀ : i₀ ≤ P.d) :
    opRuntimeBudget TP LP P n i₀ ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
        powTerm P i₀ := by
  set M := (P.M₀ : ℝ)
  set γℓ := TP.γ_ℓ (P.M₀ ^ 2)
  set γr := TP.γ_r (P.M₀ ^ 2)
  set M1d := M ^ (1 / (P.d : ℝ))
  set L0 := logFactor P n
  set L := 2 * L0
  set q := max TP.p_T LP.p_last + 1
  have hM1 : 1 ≤ M := by simp only [M]; exact_mod_cast P.hM₀
  have hγℓ1 : 1 ≤ γℓ := hTP.2.2.1 (P.M₀ ^ 2)
  have hγr1 : 1 ≤ γr := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
  have hM1d1 : 1 ≤ M1d := Real.one_le_rpow hM1 (by positivity)
  have hL01 : 1 ≤ L0 := one_le_logFactor P n
  have hL1 : 1 ≤ L := by linarith
  have hPow1 : 1 ≤ powTerm P i₀ := one_le_powTerm P hi₀
  have hγr_mul_pow : ∀ a, a ≤ 3 * P.d + 2 → γr * γℓ ^ a ≤ γr * γℓ ^ (3 * P.d + 2) := fun a ha =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hγℓ1 ha) (by positivity)
  have hL_pow : ∀ p, p ≤ q → L ^ p ≤ L ^ q := fun p hp => pow_le_pow_right₀ hL1 hp
  have hToolTerm : ∀ j ∈ Finset.Ico i₀ P.d,
      levelToolCap TP P n j ≤
        (8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    have hji₀ : i₀ ≤ j := hmem.1
    have hjd : j ≤ P.d := Nat.le_of_lt hmem.2
    have hMγ := gamma_div_mul_le_powTerm TP P hTP hji₀ hjd
    have hMγγ : M * γℓ * (γℓ / P.k) ^ j ≤ γℓ ^ (P.d + 1) * powTerm P i₀ := by
      calc
        M * γℓ * (γℓ / P.k) ^ j = γℓ * (M * (γℓ / P.k) ^ j) := by ring
        _ ≤ γℓ * (γℓ ^ P.d * powTerm P i₀) := mul_le_mul_of_nonneg_left hMγ (by positivity)
        _ = γℓ ^ (P.d + 1) * powTerm P i₀ := by rw [pow_succ']; ring
    have h1_le : 1 ≤ γℓ ^ (P.d + 1) * powTerm P i₀ :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγℓ1) hPow1
    have hMγ_plus : M * γℓ * (γℓ / P.k) ^ j + 1 ≤ 2 * γℓ ^ (P.d + 1) * powTerm P i₀ := by linarith
    have hk_le : (P.k : ℝ) ≤ 2 * M1d := P.hk_upper
    have hcT : 0 ≤ TP.c_T := hTP.2.2.2.2.2.2.2.2.2
    have hMain : 2 * TP.c_T * (M * γℓ * (γℓ / P.k) ^ j + 1) * (P.k : ℝ) * γr * L ^ TP.p_T ≤
        8 * TP.c_T * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
      have hL_le : L ^ TP.p_T ≤ L ^ q := hL_pow TP.p_T (Nat.le_succ_of_le (le_max_left _ _))
      have hd_pos := P.hd
      have hγ_le : γr * γℓ ^ (P.d + 1) ≤ γr * γℓ ^ (3 * P.d + 2) :=
        hγr_mul_pow (P.d + 1) (by omega)
      have hmul1 : 2 * TP.c_T * (M * γℓ * (γℓ / P.k) ^ j + 1) * (P.k : ℝ) ≤
          2 * TP.c_T * (2 * γℓ ^ (P.d + 1) * powTerm P i₀) * (2 * M1d) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMγ_plus (by positivity)) hk_le
          (by positivity) (by positivity)
      have hmul2 : 2 * TP.c_T * (M * γℓ * (γℓ / P.k) ^ j + 1) * (P.k : ℝ) * γr * L ^ TP.p_T ≤
          (2 * TP.c_T * (2 * γℓ ^ (P.d + 1) * powTerm P i₀) * (2 * M1d)) * γr * L ^ q :=
        mul_le_mul (mul_le_mul_of_nonneg_right hmul1 (by positivity)) hL_le
          (by positivity) (by positivity)
      calc
        2 * TP.c_T * (M * γℓ * (γℓ / P.k) ^ j + 1) * (P.k : ℝ) * γr * L ^ TP.p_T
            ≤ (2 * TP.c_T * (2 * γℓ ^ (P.d + 1) * powTerm P i₀) * (2 * M1d)) * γr * L ^ q := hmul2
        _ = 8 * TP.c_T * M1d * (γr * γℓ ^ (P.d + 1)) * L ^ q * powTerm P i₀ := by ring
        _ ≤ 8 * TP.c_T * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
          gcongr
    have hTail : (if j = 0 then 200 * M * γℓ * Real.log (10 * M * γℓ + 2)
          else 5 * γr * (M * γℓ * (γℓ / P.k) ^ (j - 1) / P.k + 1)) ≤
        310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
      by_cases h0 : j = 0
      · subst h0
        have hi0_0 : i₀ = 0 := by omega
        subst hi0_0
        have hp0 : powTerm P 0 = M := powTerm_zero P
        have hlog10 : Real.log (10 * M * γℓ + 2) ≤ 3 * L0 :=
          log_ten_sq_add_two_le TP P hγM₀ hγℓ1 n
        have hL1q : L ≤ L ^ q := by simpa using hL_pow 1 (by omega)
        have hγℓ_pow : γℓ ≤ γr * γℓ ^ (3 * P.d + 2) := by
          have h1 : γℓ ≤ γr * γℓ := le_mul_of_one_le_left (by positivity) hγr1
          have h2 : γr * γℓ ^ 1 ≤ γr * γℓ ^ (3 * P.d + 2) := hγr_mul_pow 1 (by have := P.hd; omega)
          exact le_trans h1 (by simpa using h2)
        calc
          (if (0 : ℕ) = 0 then 200 * M * γℓ * Real.log (10 * M * γℓ + 2) else _)
              = 200 * M * γℓ * Real.log (10 * M * γℓ + 2) := by simp
          _ ≤ 200 * M * γℓ * (3 * L0) := mul_le_mul_of_nonneg_left hlog10 (by positivity)
          _ = 300 * 1 * γℓ * L * powTerm P 0 := by simp only [L, hp0]; ring
          _ ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P 0 := by
            have hpow0_nn : 0 ≤ powTerm P 0 := by positivity
            have h1 : 300 * 1 * γℓ * L ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q := by
              have ha : (300 : ℝ) * 1 ≤ 310 * M1d := by nlinarith
              have hb : (300 : ℝ) * 1 * γℓ ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) :=
                mul_le_mul ha hγℓ_pow (by positivity) (by positivity)
              exact mul_le_mul hb hL1q (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right h1 hpow0_nn
      · have hjpos : 0 < j := Nat.pos_of_ne_zero h0
        have hstep_eq : M * γℓ * (γℓ / P.k) ^ (j - 1) / P.k = M * (γℓ / P.k) ^ j := by
          have hk0 : (P.k : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.hk).ne'
          conv_rhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
          field_simp [hk0]
        have h1_le' : 1 ≤ γℓ ^ P.d * powTerm P i₀ :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγℓ1) hPow1
        have hle1 : M * γℓ * (γℓ / P.k) ^ (j - 1) / P.k + 1 ≤ 2 * γℓ ^ P.d * powTerm P i₀ := by
          rw [hstep_eq]; linarith
        have hγ_le : γr * γℓ ^ P.d ≤ γr * γℓ ^ (3 * P.d + 2) := hγr_mul_pow P.d (by omega)
        have hLq1 : 1 ≤ L ^ q := one_le_pow₀ hL1
        simp only [h0, ↓reduceIte]
        calc
          5 * γr * (M * γℓ * (γℓ / P.k) ^ (j - 1) / P.k + 1)
              ≤ 5 * γr * (2 * γℓ ^ P.d * powTerm P i₀) :=
            mul_le_mul_of_nonneg_left hle1 (by positivity)
          _ = 10 * 1 * (γr * γℓ ^ P.d) * 1 * powTerm P i₀ := by ring
          _ ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
            have h1 : 10 * 1 ≤ 310 * M1d := by nlinarith
            have h2 : 10 * 1 * (γr * γℓ ^ P.d) ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) :=
              mul_le_mul h1 hγ_le (by positivity) (by positivity)
            have h3 : 10 * 1 * (γr * γℓ ^ P.d) * 1 ≤ 310 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q :=
              mul_le_mul h2 hLq1 (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_right h3 (by positivity)
    unfold levelToolCap
    linarith
  have hToolSum : (if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelToolCap TP P n) else 0) ≤
      (P.d : ℝ) * (8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
    by_cases hlt : i₀ < P.d
    · simp only [hlt, ↓reduceIte]
      have hsum : (Finset.Ico i₀ P.d).sum (levelToolCap TP P n) ≤
          (Finset.Ico i₀ P.d).sum (fun _ =>
            (8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀) :=
        Finset.sum_le_sum hToolTerm
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsum
      have hsub_le : ((P.d - i₀ : ℕ) : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast Nat.sub_le P.d i₀
      have hterm_nn : 0 ≤ (8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
        have := hTP.2.2.2.2.2.2.2.2.2
        positivity
      exact le_trans hsum (by
        calc
          ((P.d - i₀ : ℕ) : ℝ) * ((8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀)
              ≤ (P.d : ℝ) * ((8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀) :=
            mul_le_mul_of_nonneg_right hsub_le hterm_nn
          _ = (P.d : ℝ) * (8 * TP.c_T + 310) * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by ring)
    · simp only [hlt, ↓reduceIte]
      have := hTP.2.2.2.2.2.2.2.2.2
      positivity
  have hLastCost : lastCostCap TP LP P n ≤
      81 * LP.c_last * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
    have hMγd := gamma_div_mul_le_powTerm TP P hTP (le_refl P.d) (le_refl P.d)
    have hpd1 : powTerm P P.d = 1 := by
      unfold powTerm
      have hd0 : (P.d : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.hd).ne'
      simp [div_self hd0]
    rw [hpd1, mul_one] at hMγd
    have hStep1 : M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k ≤ γℓ ^ P.d := by
      have h1 : M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k = M * (γℓ / P.k) ^ P.d := by
        have hk0 : (P.k : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.hk).ne'
        have hd_eq : P.d = (P.d - 1) + 1 := by have := P.hd; omega
        conv_rhs => rw [hd_eq, pow_succ]
        field_simp [hk0]
      rw [h1]
      exact hMγd
    have hF1 : 4 * γr * M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k + 4 * γr + 1 ≤ 9 * γr * γℓ ^ P.d := by
      have hγℓd1 : 1 ≤ γℓ ^ P.d := one_le_pow₀ hγℓ1
      have hγd1 : 1 ≤ γr * γℓ ^ P.d := one_le_mul_of_one_le_of_one_le hγr1 hγℓd1
      have hγr_le : γr ≤ γr * γℓ ^ P.d := le_mul_of_one_le_right (by positivity) hγℓd1
      calc
        4 * γr * M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k + 4 * γr + 1
            = 4 * γr * (M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k) + 4 * γr + 1 := by ring
        _ ≤ 4 * γr * γℓ ^ P.d + 4 * γr + 1 := by gcongr
        _ ≤ 4 * γr * γℓ ^ P.d + 4 * (γr * γℓ ^ P.d) + γr * γℓ ^ P.d := by linarith
        _ = 9 * γr * γℓ ^ P.d := by ring
    have hLvlD : (levelM TP P P.d : ℝ) ≤ γℓ ^ (P.d + 1) + 1 := by
      have hlt := levelM_lt_add_one hTP P P.d
      have hmul : M * γℓ * (γℓ / P.k) ^ P.d ≤ γℓ ^ (P.d + 1) := by
        calc M * γℓ * (γℓ / P.k) ^ P.d = γℓ * (M * (γℓ / P.k) ^ P.d) := by ring
          _ ≤ γℓ * γℓ ^ P.d := mul_le_mul_of_nonneg_left hMγd (by positivity)
          _ = γℓ ^ (P.d + 1) := by rw [pow_succ']
      linarith
    have hF2 : ((levelM TP P P.d : ℝ) + 1) ^ 2 ≤ 9 * γℓ ^ (2 * P.d + 2) := by
      have h1 : 1 ≤ γℓ ^ (P.d + 1) := one_le_pow₀ hγℓ1
      have h2 : (levelM TP P P.d : ℝ) + 1 ≤ 3 * γℓ ^ (P.d + 1) := by linarith
      calc
        ((levelM TP P P.d : ℝ) + 1) ^ 2 ≤ (3 * γℓ ^ (P.d + 1)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
        _ = 9 * γℓ ^ (2 * P.d + 2) := by
          rw [mul_pow, ← pow_mul, show (P.d + 1) * 2 = 2 * P.d + 2 by omega]; norm_num
    have hL_le : L ^ LP.p_last ≤ L ^ q :=
      hL_pow LP.p_last (Nat.le_succ_of_le (le_max_right _ _))
    have hcL := hLP.2.2.2.2
    unfold lastCostCap
    calc
      (4 * γr * M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k + 4 * γr + 1) *
          (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 * L ^ LP.p_last)
          ≤ (9 * γr * γℓ ^ P.d) * (LP.c_last * (9 * γℓ ^ (2 * P.d + 2)) * L ^ q) := by
        apply mul_le_mul hF1 _ (by positivity) (by positivity)
        apply mul_le_mul (mul_le_mul_of_nonneg_left hF2 hcL) hL_le (by positivity) (by positivity)
      _ = 81 * LP.c_last * 1 * (γr * (γℓ ^ P.d * γℓ ^ (2 * P.d + 2))) * L ^ q * 1 := by ring
      _ = 81 * LP.c_last * 1 * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * 1 := by
        rw [← pow_add, show P.d + (2 * P.d + 2) = 3 * P.d + 2 by omega]
      _ ≤ 81 * LP.c_last * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
        have h1 : 81 * LP.c_last * 1 ≤ 81 * LP.c_last * M1d := by gcongr
        have h2 : 81 * LP.c_last * 1 * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q ≤
            81 * LP.c_last * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
        exact mul_le_mul h2 hPow1 zero_le_one (by positivity)
  have hExEnc : (if i₀ = 0 then extraEncCap P else 0) ≤
      120 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by
    by_cases h0 : i₀ = 0
    · subst h0
      simp only [↓reduceIte, extraEncCap]
      have hp0 : powTerm P 0 = M := powTerm_zero P
      have hlog2 := log_two_add_two_le P n
      have hL1q : L ≤ L ^ q := by simpa using hL_pow 1 (by omega)
      have hγbig : 1 ≤ γr * γℓ ^ (3 * P.d + 2) :=
        one_le_mul_of_one_le_of_one_le hγr1 (one_le_pow₀ hγℓ1)
      calc
        40 * M * Real.log (2 * M + 2)
            ≤ 40 * M * (3 * L0) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 60 * 1 * 1 * L * powTerm P 0 := by simp only [L, hp0]; ring
        _ ≤ 120 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P 0 := by
          have hpow0_nn : 0 ≤ powTerm P 0 := by positivity
          have ha : (60 : ℝ) * 1 ≤ 120 * M1d := by nlinarith
          have hb : (60 : ℝ) * 1 * 1 ≤ 120 * M1d * (γr * γℓ ^ (3 * P.d + 2)) := by nlinarith
          have hc : (60 : ℝ) * 1 * 1 * L ≤ 120 * M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q :=
            mul_le_mul hb hL1q (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hc hpow0_nn
    · simp only [h0, ↓reduceIte]
      positivity
  unfold opRuntimeBudget
  have hAdd := add_le_add (add_le_add hToolSum hLastCost) hExEnc
  have hd_le : (P.d : ℝ) * (8 * TP.c_T + 310) + 81 * LP.c_last + 120 ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) := by
    have hd_nn : (0 : ℝ) ≤ P.d := Nat.cast_nonneg P.d
    nlinarith [hTP.2.2.2.2.2.2.2.2.2, hLP.2.2.2.2]
  have hTail_nn : 0 ≤ M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by positivity
  calc
    (if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelToolCap TP P n) else 0) +
        lastCostCap TP LP P n + (if i₀ = 0 then extraEncCap P else 0)
        ≤ ((P.d : ℝ) * (8 * TP.c_T + 310) + 81 * LP.c_last + 120) *
            (M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀) := by linarith
    _ ≤ ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
          (M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀) :=
      mul_le_mul_of_nonneg_right hd_le hTail_nn
    _ = ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
          M1d * (γr * γℓ ^ (3 * P.d + 2)) * L ^ q * powTerm P i₀ := by ring

lemma opTreeBudget_collapse (TP : SparseCoreParams) (P : ChainParams)
    (hTP : TP.Valid) {i₀ : ℕ} (hi₀ : i₀ ≤ P.d) :
    opTreeBudget TP P i₀ ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        powTerm P i₀ := by
  set M := (P.M₀ : ℝ)
  set γℓ := TP.γ_ℓ (P.M₀ ^ 2)
  set γr := TP.γ_r (P.M₀ ^ 2)
  have hγℓ1 : 1 ≤ γℓ := hTP.2.2.1 (P.M₀ ^ 2)
  have hγr1 : 1 ≤ γr := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
  have hPow1 : 1 ≤ powTerm P i₀ := one_le_powTerm P hi₀
  have hγ_le_2d1 : ∀ a, a ≤ 2 * P.d + 1 → γr * γℓ ^ a ≤ (γℓ * γr) ^ (2 * P.d + 1) := by
    intro a ha
    have h1 : γℓ ^ a ≤ γℓ ^ (2 * P.d + 1) := pow_le_pow_right₀ hγℓ1 ha
    have h2 : γr ≤ γr ^ (2 * P.d + 1) := by
      simpa using pow_le_pow_right₀ hγr1 (show 1 ≤ 2 * P.d + 1 by omega)
    calc
      γr * γℓ ^ a ≤ γr ^ (2 * P.d + 1) * γℓ ^ (2 * P.d + 1) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = (γℓ * γr) ^ (2 * P.d + 1) := by rw [mul_pow, mul_comm]
  have hγd1' : γℓ ^ (P.d + 1) ≤ (γℓ * γr) ^ (2 * P.d + 1) := by
    have hd_pos := P.hd
    calc
      γℓ ^ (P.d + 1) ≤ γr * γℓ ^ (P.d + 1) := le_mul_of_one_le_left (by positivity) hγr1
      _ ≤ (γℓ * γr) ^ (2 * P.d + 1) := hγ_le_2d1 (P.d + 1) (by omega)
  have hDecSum : (if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelDecCap TP P) else 0) ≤
      10 * (P.d : ℝ) * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by
    by_cases hlt : i₀ < P.d
    · simp only [hlt, ↓reduceIte]
      have hterm : ∀ j ∈ Finset.Ico i₀ P.d,
          levelDecCap TP P j ≤ 10 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by
        intro j hj
        have hmem := Finset.mem_Ico.mp hj
        have hMγ := gamma_div_mul_le_powTerm TP P hTP hmem.1 (Nat.le_of_lt hmem.2)
        have hMγγ : M * γℓ * (γℓ / P.k) ^ j ≤ γℓ ^ (P.d + 1) * powTerm P i₀ := by
          calc
            M * γℓ * (γℓ / P.k) ^ j = γℓ * (M * (γℓ / P.k) ^ j) := by ring
            _ ≤ γℓ * (γℓ ^ P.d * powTerm P i₀) := mul_le_mul_of_nonneg_left hMγ (by positivity)
            _ = γℓ ^ (P.d + 1) * powTerm P i₀ := by rw [pow_succ']; ring
        have h1_le : 1 ≤ γℓ ^ (P.d + 1) * powTerm P i₀ :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγℓ1) hPow1
        have hγd1 : 1 ≤ (γℓ * γr) ^ (2 * P.d + 1) := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hγℓ1 hγr1)
        unfold levelDecCap
        calc
          5 * (M * γℓ * (γℓ / P.k) ^ j + 1) ≤ 5 * (2 * γℓ ^ (P.d + 1) * powTerm P i₀) := by linarith
          _ = 10 * γℓ ^ (P.d + 1) * powTerm P i₀ := by ring
          _ ≤ 10 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by gcongr
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsum
      have hsub_le : ((P.d - i₀ : ℕ) : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast Nat.sub_le P.d i₀
      have hnn : 0 ≤ 10 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by positivity
      calc
        (Finset.Ico i₀ P.d).sum (levelDecCap TP P)
            ≤ ((P.d - i₀ : ℕ) : ℝ) * (10 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀) := hsum
        _ ≤ (P.d : ℝ) * (10 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀) :=
          mul_le_mul_of_nonneg_right hsub_le hnn
        _ = 10 * (P.d : ℝ) * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by ring
    · simp only [hlt, ↓reduceIte]
      positivity
  have hLastT : lastTreeCap TP P ≤ 32 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by
    have hMγd := gamma_div_mul_le_powTerm TP P hTP (le_refl P.d) (le_refl P.d)
    have hpd1 : powTerm P P.d = 1 := by
      unfold powTerm
      have hd0 : (P.d : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.hd).ne'
      simp [div_self hd0]
    rw [hpd1, mul_one] at hMγd
    have hStep1 : M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k ≤ γℓ ^ P.d := by
      have h1 : M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k = M * (γℓ / P.k) ^ P.d := by
        have hk0 : (P.k : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.hk).ne'
        have hd_eq : P.d = (P.d - 1) + 1 := by have := P.hd; omega
        conv_rhs => rw [hd_eq, pow_succ]
        field_simp [hk0]
      rw [h1]
      exact hMγd
    unfold lastTreeCap
    have hγℓd1 : 1 ≤ γℓ ^ P.d := one_le_pow₀ hγℓ1
    have hF1 : 4 * γr * (M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k) + 4 * γr ≤ 8 * γr * γℓ ^ P.d := by
      have hle : 4 * γr * (M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k) ≤ 4 * γr * γℓ ^ P.d := by
        gcongr
      have hγr_le : 4 * γr ≤ 4 * γr * γℓ ^ P.d := by nlinarith
      linarith
    have hLvlD : (levelM TP P P.d : ℝ) ≤ 2 * γℓ ^ (P.d + 1) := by
      have hlt := levelM_lt_add_one hTP P P.d
      have hmul : M * γℓ * (γℓ / P.k) ^ P.d ≤ γℓ ^ (P.d + 1) := by
        calc M * γℓ * (γℓ / P.k) ^ P.d = γℓ * (M * (γℓ / P.k) ^ P.d) := by ring
          _ ≤ γℓ * γℓ ^ P.d := mul_le_mul_of_nonneg_left hMγd (by positivity)
          _ = γℓ ^ (P.d + 1) := by rw [pow_succ']
      have h1 : 1 ≤ γℓ ^ (P.d + 1) := one_le_pow₀ hγℓ1
      linarith
    have hprod := mul_le_mul hF1 hLvlD (by positivity) (by positivity)
    have hγ2d1 : γr * (γℓ ^ P.d * γℓ ^ (P.d + 1)) ≤ (γℓ * γr) ^ (2 * P.d + 1) := by
      rw [← pow_add, show P.d + (P.d + 1) = 2 * P.d + 1 by omega]
      exact hγ_le_2d1 (2 * P.d + 1) (le_refl _)
    calc
      2 * (4 * γr * (M * γℓ * (γℓ / P.k) ^ (P.d - 1) / P.k) + 4 * γr) * (levelM TP P P.d : ℝ)
          ≤ 2 * ((8 * γr * γℓ ^ P.d) * (2 * γℓ ^ (P.d + 1))) := by linarith
      _ = 32 * (γr * (γℓ ^ P.d * γℓ ^ (P.d + 1))) * 1 := by ring
      _ ≤ 32 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hγ2d1 (by norm_num)) hPow1 zero_le_one (by positivity)
  have hDiffT : diffTreeCap TP P i₀ ≤
      4 * ((P.d : ℝ) + 1) * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by
    have hterm : ∀ j ∈ Finset.Ico i₀ (P.d + 1),
        (levelM TP P j : ℝ) ≤ 2 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by
      intro j hj
      have hmem := Finset.mem_Ico.mp hj
      have hMγ := gamma_div_mul_le_powTerm TP P hTP hmem.1 (Nat.lt_succ_iff.mp hmem.2)
      have hlt := levelM_lt_add_one hTP P j
      have hMγγ : M * γℓ * (γℓ / P.k) ^ j ≤ γℓ ^ (P.d + 1) * powTerm P i₀ := by
        calc
          M * γℓ * (γℓ / P.k) ^ j = γℓ * (M * (γℓ / P.k) ^ j) := by ring
          _ ≤ γℓ * (γℓ ^ P.d * powTerm P i₀) := mul_le_mul_of_nonneg_left hMγ (by positivity)
          _ = γℓ ^ (P.d + 1) * powTerm P i₀ := by rw [pow_succ']; ring
      have h1_le : 1 ≤ γℓ ^ (P.d + 1) * powTerm P i₀ :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγℓ1) hPow1
      have h2 : (levelM TP P j : ℝ) ≤ 2 * (γℓ ^ (P.d + 1) * powTerm P i₀) := by linarith
      calc
        (levelM TP P j : ℝ) ≤ 2 * (γℓ ^ (P.d + 1) * powTerm P i₀) := h2
        _ = 2 * γℓ ^ (P.d + 1) * powTerm P i₀ := by ring
        _ ≤ 2 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by gcongr
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsum
    have hsub_le : ((P.d + 1 - i₀ : ℕ) : ℝ) ≤ (P.d : ℝ) + 1 := by
      exact_mod_cast Nat.sub_le (P.d + 1) i₀
    have hnn : 0 ≤ 2 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by positivity
    unfold diffTreeCap
    calc
      2 * (Finset.Ico i₀ (P.d + 1)).sum (fun j => (levelM TP P j : ℝ))
          ≤ 2 * (((P.d + 1 - i₀ : ℕ) : ℝ) * (2 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ 2 * (((P.d : ℝ) + 1) * (2 * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub_le hnn) (by norm_num)
      _ = 4 * ((P.d : ℝ) + 1) * (γℓ * γr) ^ (2 * P.d + 1) * powTerm P i₀ := by ring
  unfold opTreeBudget
  linarith

/-- Total runtime bound (Lemma 5.11, pages 20 & 23–24) in explicit non-asymptotic form from
`ChainInv` and `ChainBudgetInv`. -/
theorem totalRuntime_collapse_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow) :
    (st.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by
  have hCost := hInv.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hActive : ((∑ i ∈ Finset.range P.d, (T.cost (st.scState i) + st.curEnc i) : ℕ) : ℝ) +
      (st.curLastCost : ℝ) ≤
        opRuntimeBudget TP LP P N₀ 0 + activeRestartCap TP P N₀ st.curRestarts := by
    have hsum : ((∑ i ∈ Finset.range P.d, (T.cost (st.scState i) + st.curEnc i) : ℕ) : ℝ) ≤
        (Finset.Ico 0 P.d).sum (levelToolCap TP P N₀) + activeRestartCap TP P N₀ st.curRestarts := by
      rw [Nat.cast_sum]
      calc
        ∑ i ∈ Finset.range P.d, ((T.cost (st.scState i) + st.curEnc i : ℕ) : ℝ)
            ≤ ∑ i ∈ Finset.range P.d,
                (levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) :=
              Finset.sum_le_sum fun i hi => by
                rw [Nat.cast_add]; exact hCost.1 i (Finset.mem_range.mp hi)
        _ = (Finset.Ico 0 P.d).sum (levelToolCap TP P N₀) + activeRestartCap TP P N₀ st.curRestarts := by
              rw [Finset.sum_add_distrib, Nat.Ico_zero_eq_range]
              rfl
    have hlast := hCost.2.2.1 P.hd
    have hex_nn : 0 ≤ extraEncCap P := by
      unfold extraEncCap
      have hlog : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
      positivity
    unfold opRuntimeBudget
    simp only [P.hd, ↓reduceIte]
    linarith
  have hTot : (st.totalRuntime : ℝ) ≤
      opRuntimeBudget TP LP P N₀ 0 +
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P N₀ i + overflow := by
    unfold ChainState.totalRuntime
    rw [Nat.cast_add, Nat.cast_add]
    have hBud1 : (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
        ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opRuntimeBudget TP LP P N₀ i +
            overflow :=
      hBudget.1
    linarith [hBud1, hActive]
  set Cfac := ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
      (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
      (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
      (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1)
  have hCfac_nn : 0 ≤ Cfac := by
    have := hTP.2.2.2.2.2.2.2.2.2
    have := hLP.2.2.2.2
    have := one_le_logFactor P N₀
    have := hTP.2.2.1 (P.M₀ ^ 2)
    have := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
    positivity
  have h0 : opRuntimeBudget TP LP P N₀ 0 ≤ Cfac * (P.M₀ : ℝ) := by
    simpa [Cfac, powTerm_zero P] using opRuntimeBudget_collapse TP LP P hTP hLP hγM₀ (Nat.zero_le P.d)
  have hSum : (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P N₀ i) ≤
      Cfac * (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hci := opRuntimeBudget_collapse TP LP P hTP hLP hγM₀ hi_le (n := N₀)
    calc
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opRuntimeBudget TP LP P N₀ i
          ≤ ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * (Cfac * powTerm P i) :=
        mul_le_mul_of_nonneg_left hci (Nat.cast_nonneg _)
      _ = Cfac * (((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring
  calc
    (st.totalRuntime : ℝ)
        ≤ Cfac * (P.M₀ : ℝ) + Cfac * (∑ i ∈ Finset.range (P.d + 1),
            ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by
      linarith
    _ = Cfac * ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by ring

theorem totalRuntime_collapse_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
  simpa using totalRuntime_collapse_with_noHidden T L TP LP P hTP hLP hT hγM₀ hγk hInv hBudget.toWith

theorem totalRuntime_collapse (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) :=
  totalRuntime_collapse_noHidden T L TP LP P hTP hLP (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT)
    hγM₀ hγk hInv hBudget

/-- Total `T^𝒢` edge-update bound (Lemma 5.11, pages 20 & 23–24) in explicit non-asymptotic form
from `ChainInv` and `ChainBudgetInvWith`. -/
theorem totalTreeUpdates_collapse_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow) :
    (st.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
  have hCost := hInv.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hActivePlusDiff : ((∑ i ∈ Finset.range P.d, st.curDecUpdates i : ℕ) : ℝ) +
      (st.curLastTreeUpdates : ℝ) + diffTreeCap TP P 0 ≤ opTreeBudget TP P 0 := by
    have hsum : ((∑ i ∈ Finset.range P.d, st.curDecUpdates i : ℕ) : ℝ) ≤
        (Finset.Ico 0 P.d).sum (levelDecCap TP P) := by
      rw [Nat.cast_sum, Nat.Ico_zero_eq_range]
      exact Finset.sum_le_sum fun i hi => hCost.2.1 i (Finset.mem_range.mp hi)
    unfold opTreeBudget
    simp only [P.hd, ↓reduceIte]
    linarith [hCost.2.2.2.1]
  have hTot : (st.totalTreeUpdates : ℝ) ≤
      opTreeBudget TP P 0 +
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i := by
    unfold ChainState.totalTreeUpdates
    rw [Nat.cast_add, Nat.cast_add]
    have hBud2 : (st.closedTreeUpdates : ℝ) ≤ diffTreeCap TP P 0 +
        ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i :=
      hBudget.2
    linarith [hBud2, hActivePlusDiff]
  set Tfac := (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1)
  have hTfac_nn : 0 ≤ Tfac := by
    have := hTP.2.2.1 (P.M₀ ^ 2)
    have := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
    positivity
  have h0 : opTreeBudget TP P 0 ≤ Tfac * (P.M₀ : ℝ) := by
    simpa [Tfac, powTerm_zero P] using opTreeBudget_collapse TP P hTP (Nat.zero_le P.d)
  have hSum : (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i) ≤
      Tfac * (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hti := opTreeBudget_collapse TP P hTP hi_le
    calc
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i
          ≤ ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * (Tfac * powTerm P i) :=
        mul_le_mul_of_nonneg_left hti (Nat.cast_nonneg _)
      _ = Tfac * (((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring
  calc
    (st.totalTreeUpdates : ℝ)
        ≤ Tfac * (P.M₀ : ℝ) + Tfac * (∑ i ∈ Finset.range (P.d + 1),
            ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by linarith
    _ = Tfac * ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring

theorem totalTreeUpdates_collapse_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) :=
  totalTreeUpdates_collapse_with_noHidden T L TP LP P hTP hLP hT hγM₀ hγk hInv hBudget.toWith

theorem totalTreeUpdates_collapse (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) :=
  totalTreeUpdates_collapse_noHidden T L TP LP P hTP hLP (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT)
    hγM₀ hγk hInv hBudget

end CollapsingBounds

end MinCostFlow.Chain
