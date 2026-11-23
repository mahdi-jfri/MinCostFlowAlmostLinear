module

public import MinCostFlow.LSF.Program.Lemma55Approx
public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.LSF.Program.UArithMul
public import MinCostFlow.Num.PositiveExponential
public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.FixedDivide
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step Denominator `ρ` and Fixed-Point Rounding Error for Lemma 5.5 (`Lemma55StepBase`)

Defines `lemma55RhoConst` and `lemma55RhoNat`, proves `lemma55Rho_bounds`, base-`2^h` limb
encoding lemmas (`lemma55_one_limbs`, `lemma55_shift_limbs`, `lemma55_trunc_pos`), and the
single-step fixed-point relative-error theorem `lemma55_step_error`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Num

@[expose] public section

/-! ## Step denominator `ρ` and bounds -/

/-- Compile-time constant factor `10 · defaultK_sigma K_AN` in `lemma55RhoNat`. -/
noncomputable def lemma55RhoConst (K_AN : ℝ) : ℕ :=
  10 * defaultK_sigma K_AN

/-- Integer MWU step denominator `ρ_nat = 10 · K_σ · k · (⌊log₂(n + 2)⌋ + 1)⁶`. -/
noncomputable def lemma55RhoNat (K_AN : ℝ) (n k_nat : ℕ) : ℕ :=
  lemma55RhoConst K_AN * k_nat * (Nat.log 2 (n + 2) + 1) ^ 6

lemma lemma55RhoNat_pos (K_AN : ℝ) (n : ℕ) {k_nat : ℕ} (hk : 1 ≤ k_nat) :
    1 ≤ lemma55RhoNat K_AN n k_nat := by
  have hc : 1 ≤ defaultC_ceil K_AN := (defaultC_ceil_ge K_AN).2
  have h1 : 1 ≤ lemma55RhoConst K_AN := by
    dsimp [lemma55RhoConst, defaultK_sigma]; omega
  have h2 : 1 ≤ (Nat.log 2 (n + 2) + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  dsimp [lemma55RhoNat]
  exact Nat.mul_pos (Nat.mul_pos h1 hk) h2

/-- `lemma55RhoNat` dominates `10 · defaultThreshNat` and brackets `10 · U` up to the universal
constant `C_ρ = 40960`. -/
lemma lemma55Rho_bounds (K_AN : ℝ) (n : ℕ) {k_nat : ℕ} (hk : 1 ≤ k_nat) :
    let K₀ := lemma54K0 (4 * max K_AN 1 + 5) (5 / 4) (defaultK_sigma K_AN : ℝ)
    10 * defaultThreshNat K_AN n k_nat ≤ lemma55RhoNat K_AN n k_nat ∧
    10 * (K₀ * (k_nat : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6) ≤ (lemma55RhoNat K_AN n k_nat : ℝ) ∧
    (lemma55RhoNat K_AN n k_nat : ℝ) ≤
      40960 * (K₀ * (k_nat : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6) := by
  intro K₀
  have hK₀_eq : K₀ = (defaultK_sigma K_AN : ℝ) := defaultK_sigma_eq_K0 K_AN
  have hC1 : 1 ≤ defaultC_ceil K_AN := (defaultC_ceil_ge K_AN).2
  set d := Nat.log 2 (n + 2)
  have hd_pos : 1 ≤ d := Nat.log_pos (by decide) (by omega)
  have hD_le : hldDepthBound n + 1 ≤ 2 * (d + 1) ^ 2 := by
    have hlogn : Nat.log 2 n ≤ d := Nat.log_mono_right (by omega)
    dsimp only [hldDepthBound]; nlinarith
  have hD_sq : (hldDepthBound n + 1) ^ 2 ≤ 4 * (d + 1) ^ 4 := by nlinarith
  have h10_thresh : 10 * defaultThreshNat K_AN n k_nat ≤ lemma55RhoNat K_AN n k_nat := by
    dsimp only [defaultThreshNat, lemma55RhoNat, lemma55RhoConst, defaultK_sigma]
    have hprod_ge : 1 ≤ 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat := by
      have h1 : 1 ≤ (hldDepthBound n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) h1) hC1) h2) hk
    rw [max_eq_right hprod_ge]
    have hstep1 : 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat ≤
        36 * defaultC_ceil K_AN * k_nat * (d + 1) ^ 6 := by
      have h1 : 9 * (hldDepthBound n + 1) ^ 2 ≤ 36 * (d + 1) ^ 4 := by omega
      have h2 := Nat.mul_le_mul_right (defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat) h1
      have hL : 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat =
          9 * (hldDepthBound n + 1) ^ 2 * (defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat) := by ring
      have hR : 36 * (d + 1) ^ 4 * (defaultC_ceil K_AN * (d + 1) ^ 2 * k_nat) =
          36 * defaultC_ceil K_AN * k_nat * (d + 1) ^ 6 := by ring
      rw [hL, ← hR]; exact h2
    have hstep2 : 10 * (36 * defaultC_ceil K_AN * k_nat * (d + 1) ^ 6) ≤
        10 * (294912 * defaultC_ceil K_AN) * k_nat * (d + 1) ^ 6 := by
      have hnn : 0 ≤ defaultC_ceil K_AN * k_nat * (d + 1) ^ 6 := Nat.zero_le _
      have : 360 * (defaultC_ceil K_AN * k_nat * (d + 1) ^ 6) ≤
          2949120 * (defaultC_ceil K_AN * k_nat * (d + 1) ^ 6) :=
        Nat.mul_le_mul_right _ (by decide)
      linarith
    exact le_trans (Nat.mul_le_mul_left 10 hstep1) hstep2
  obtain ⟨hlog_lo, hlog_hi⟩ := real_log_add_two_bounds n
  have hlog_pos : 0 < Real.log ((n : ℝ) + 2) := by
    have : (0 : ℝ) < (1 : ℝ) / 4 * ((d + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hpow_le : (Real.log ((n : ℝ) + 2)) ^ 6 ≤ ((d + 1 : ℕ) : ℝ) ^ 6 :=
    pow_le_pow_left₀ hlog_pos.le hlog_hi.le 6
  have hpow_ge : ((d + 1 : ℕ) : ℝ) ^ 6 ≤ 4096 * (Real.log ((n : ℝ) + 2)) ^ 6 := by
    have h4 : ((d + 1 : ℕ) : ℝ) ≤ 4 * Real.log ((n : ℝ) + 2) := by linarith
    have h6 := pow_le_pow_left₀ (by positivity) h4 6
    linarith [show (4 * Real.log ((n : ℝ) + 2)) ^ 6 = 4096 * (Real.log ((n : ℝ) + 2)) ^ 6 by ring]
  have hrho_cast : (lemma55RhoNat K_AN n k_nat : ℝ) =
      10 * K₀ * (k_nat : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 6 := by
    rw [hK₀_eq]
    dsimp only [lemma55RhoNat, lemma55RhoConst, d]
    push_cast; ring
  have h10K_nn : 0 ≤ 10 * K₀ * (k_nat : ℝ) := by rw [hK₀_eq]; positivity
  refine ⟨h10_thresh, ?_, ?_⟩
  · rw [hrho_cast]
    have := mul_le_mul_of_nonneg_left hpow_le h10K_nn
    linarith
  · rw [hrho_cast]
    have := mul_le_mul_of_nonneg_left hpow_ge h10K_nn
    linarith

/-! ## Limb encoding helpers -/

lemma capacity_eq_two_pow (h L : ℕ) : capacity h L = 2 ^ (h * L) := by
  dsimp only [capacity, base]
  rw [← pow_mul]

lemma valid_intVal_of_two_mul_lt {mem : ℕ → ℕ} {a h L : ℕ}
    (hlt : 2 * unsignedVal mem a h L < capacity h L) :
    intVal mem a h L = (unsignedVal mem a h L : ℤ) := by
  unfold intVal signedVal
  rw [ite_eq_right (by omega)]
  omega

/-- Single-bit `1` at limb `P_fp / h` represents `2^P_fp` (`fixVal = 1`) in `L` limbs. -/
lemma lemma55_one_limbs {mem : ℕ → ℕ} {a h L P_fp : ℕ}
    (hh : 1 ≤ h) (hdiv : h ∣ P_fp) (hfit : P_fp + 2 ≤ h * L)
    (hmem : ∀ i < L, mem (a + i) = if i = P_fp / h then 1 else 0) :
    Valid mem a h L ∧
    intVal mem a h L = (2 : ℤ) ^ P_fp ∧
    fixVal mem a h L P_fp = 1 := by
  set p := P_fp / h
  have hp_mul : h * p = P_fp := Nat.mul_div_cancel' hdiv
  have hp_lt : p < L := by
    by_contra hge
    have : h * L ≤ h * p := Nat.mul_le_mul_left h (by omega)
    omega
  have hb2 : 2 ≤ base h := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) hh
  have hv : Valid mem a h L := by
    intro i hi
    rw [hmem i hi]
    split_ifs <;> omega
  have huv : unsignedVal mem a h L = 2 ^ P_fp := by
    have hsplit := unsignedVal_split mem a h p (L - p)
    rw [show p + (L - p) = L by omega] at hsplit
    have hlow : unsignedVal mem a h p = 0 := unsignedVal_zero fun i hi => by
      rw [hmem i (by omega), ite_eq_right (by omega)]
    have hrem_pos : 1 ≤ L - p := by omega
    have hhi_eq : L - p = 1 + (L - p - 1) := by omega
    have hhi : unsignedVal mem (a + p) h (L - p) = 1 := by
      rw [hhi_eq, unsignedVal_split]
      have h1 : unsignedVal mem (a + p) h 1 = 1 := by
        simp [unsignedVal, hmem p hp_lt]
      have h0 : unsignedVal mem (a + p + 1) h (L - p - 1) = 0 :=
        unsignedVal_zero fun i hi => by
          rw [show a + p + 1 + i = a + (p + 1 + i) by omega, hmem (p + 1 + i) (by omega),
            ite_eq_right (by omega)]
      rw [h1, h0]; simp
    rw [hsplit, hlow, hhi, zero_add, mul_one, capacity_eq_two_pow, hp_mul]
  have h2lt : 2 * unsignedVal mem a h L < capacity h L := by
    rw [huv, capacity_eq_two_pow]
    calc 2 * 2 ^ P_fp = 2 ^ (P_fp + 1) := by ring
      _ < 2 ^ (h * L) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hint : intVal mem a h L = (2 : ℤ) ^ P_fp := by
    rw [valid_intVal_of_two_mul_lt h2lt, huv]; push_cast; rfl
  refine ⟨hv, hint, ?_⟩
  unfold fixVal
  rw [hint]
  push_cast
  exact div_self (by positivity)

/-- Zeroing `[a, a + pLimb)` and placing `val` in `[a + pLimb, a + L_w)` represents `val · 2^P_fp`. -/
lemma lemma55_shift_limbs {mem : ℕ → ℕ} {a h L_w P_fp val : ℕ}
    (hdiv : h ∣ P_fp) (hp_le : P_fp / h ≤ L_w)
    (hlow : ∀ i < P_fp / h, mem (a + i) = 0)
    (hhi_val : Valid mem (a + P_fp / h) h (L_w - P_fp / h))
    (hhi_u : unsignedVal mem (a + P_fp / h) h (L_w - P_fp / h) = val)
    (hfit : 2 * (val * 2 ^ P_fp) < capacity h L_w) :
    Valid mem a h L_w ∧ intVal mem a h L_w = (val : ℤ) * (2 : ℤ) ^ P_fp := by
  set p := P_fp / h
  have hp_mul : h * p = P_fp := Nat.mul_div_cancel' hdiv
  have hv : Valid mem a h L_w := by
    intro i hi
    by_cases hip : i < p
    · rw [hlow i hip]; exact base_pos h
    · have := hhi_val (i - p) (by omega)
      rwa [show a + p + (i - p) = a + i by omega] at this
  have huv : unsignedVal mem a h L_w = val * 2 ^ P_fp := by
    have hsplit := unsignedVal_split mem a h p (L_w - p)
    rw [show p + (L_w - p) = L_w by omega] at hsplit
    rw [hsplit, unsignedVal_zero hlow, zero_add, hhi_u, capacity_eq_two_pow, hp_mul, mul_comm]
  have hint : intVal mem a h L_w = (val : ℤ) * (2 : ℤ) ^ P_fp := by
    rw [valid_intVal_of_two_mul_lt (by rwa [huv]), huv]
    push_cast; rfl
  exact ⟨hv, hint⟩

/-- A nonnegative `L_w`-limb integer that fits in `L_in ≤ L_w` limbs has the same `intVal` when read
as an `L_in`-limb prefix (with no copy needed). -/
lemma lemma55_trunc_pos {mem : ℕ → ℕ} {a h L_in L_w : ℕ}
    (hv : Valid mem a h L_w) (hle : L_in ≤ L_w)
    (hnn : 0 ≤ intVal mem a h L_w)
    (hfit : 2 * intVal mem a h L_w < (capacity h L_in : ℤ)) :
    Valid mem a h L_in ∧ intVal mem a h L_in = intVal mem a h L_w := by
  have hv_in : Valid mem a h L_in := fun i hi => hv i (lt_of_lt_of_le hi hle)
  have hu_lt := unsignedVal_lt hv
  have h2u_lt_w : 2 * unsignedVal mem a h L_w < capacity h L_w := by
    unfold intVal signedVal at hnn
    by_contra hge
    rw [ite_eq_left (by omega)] at hnn
    omega
  have hint_w : intVal mem a h L_w = (unsignedVal mem a h L_w : ℤ) :=
    valid_intVal_of_two_mul_lt h2u_lt_w
  rw [hint_w] at hfit
  have h2u_lt_in : 2 * unsignedVal mem a h L_w < capacity h L_in := by exact_mod_cast hfit
  have hsplit := unsignedVal_split mem a h L_in (L_w - L_in)
  rw [show L_in + (L_w - L_in) = L_w by omega] at hsplit
  have hhi_zero : unsignedVal mem (a + L_in) h (L_w - L_in) = 0 := by
    by_contra hne
    have hge1 : 1 ≤ unsignedVal mem (a + L_in) h (L_w - L_in) := Nat.pos_of_ne_zero hne
    have : capacity h L_in ≤ unsignedVal mem a h L_w := by
      rw [hsplit]
      have : capacity h L_in * 1 ≤ capacity h L_in * unsignedVal mem (a + L_in) h (L_w - L_in) :=
        Nat.mul_le_mul_left _ hge1
      omega
    omega
  have hu_eq : unsignedVal mem a h L_in = unsignedVal mem a h L_w := by
    rw [hsplit, hhi_zero]; simp
  refine ⟨hv_in, ?_⟩
  rw [valid_intVal_of_two_mul_lt (by rw [hu_eq]; exact h2u_lt_in), hu_eq, hint_w]

/-! ## Fixed-point relative-error analysis for one MWU edge step -/

private lemma floorDiv_of_pos {x d : ℤ} (hd : 0 < d) : floorDiv x d = x / d := by
  unfold floorDiv
  rw [ite_eq_right (by omega)]

private lemma int_ediv_real_bounds {x d : ℤ} (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) - 1 < ((x / d : ℤ) : ℝ) ∧ ((x / d : ℤ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hmod_nn : 0 ≤ x % d := Int.emod_nonneg x (ne_of_gt hd)
  have hmod_lt : x % d < d := Int.emod_lt_of_pos x hd
  have heq : (x : ℝ) = (d : ℝ) * ((x / d : ℤ) : ℝ) + ((x % d : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod x d
    exact_mod_cast this.symm
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm_nn : (0 : ℝ) ≤ ((x % d : ℤ) : ℝ) := by exact_mod_cast hmod_nn
  have hm_lt : ((x % d : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod_lt
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd_r]; nlinarith
  · rw [le_div_iff₀ hd_r]; nlinarith

private lemma lemma55_step_error_combine {k_nat P_fp q : ℕ} {wstr rho v E_real v' X_real : ℝ}
    (hk : 1 ≤ k_nat) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hrho_pos : 0 < rho) (hwstr_lo : 1 ≤ wstr) (hv_lo : (1 / 2 : ℝ) ≤ v)
    (hX_le : X_real ≤ wstr / rho) (hX_lb : wstr / rho - 2 / (2 : ℝ) ^ P_fp < X_real)
    (hE_le : E_real ≤ Real.exp X_real)
    (hE_err : |E_real - Real.exp X_real| ≤ (1 / (2 : ℝ) ^ q) * Real.exp X_real)
    (hv'_le : v' ≤ v * E_real) (hv'_gt : v * E_real - 1 / (2 : ℝ) ^ P_fp < v') :
    0 < v' ∧
    (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) ≤ v' ∧
    v' ≤ (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) := by
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ P_fp := by positivity
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hexp_pos : 0 < Real.exp (wstr / rho) := Real.exp_pos _
  have hexp_ge1 : 1 ≤ Real.exp (wstr / rho) :=
    Real.one_le_exp (div_nonneg (by linarith only [hwstr_lo]) hrho_pos.le)
  have hexp_X_lb : (1 - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho) ≤ Real.exp X_real := by
    have h1 : Real.exp (wstr / rho - 2 / (2 : ℝ) ^ P_fp) ≤ Real.exp X_real :=
      Real.exp_le_exp.mpr hX_lb.le
    rw [sub_eq_add_neg, Real.exp_add] at h1
    have h2 : 1 - 2 / (2 : ℝ) ^ P_fp ≤ Real.exp (-(2 / (2 : ℝ) ^ P_fp)) := by
      linarith only [Real.add_one_le_exp (-(2 / (2 : ℝ) ^ P_fp))]
    calc (1 - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho)
        ≤ Real.exp (-(2 / (2 : ℝ) ^ P_fp)) * Real.exp (wstr / rho) :=
          mul_le_mul_of_nonneg_right h2 hexp_pos.le
      _ = Real.exp (wstr / rho) * Real.exp (-(2 / (2 : ℝ) ^ P_fp)) := mul_comm _ _
      _ ≤ Real.exp X_real := h1
  have hE_lb_X : (1 - 1 / (2 : ℝ) ^ q) * Real.exp X_real ≤ E_real := by
    linarith only [(abs_le.mp hE_err).1]
  have h1mq_nn : 0 ≤ 1 - 1 / (2 : ℝ) ^ q := by
    have h2q : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    have : 1 / (2 : ℝ) ^ q ≤ 1 := by rw [div_le_one h2q_pos]; exact h2q
    linarith only [this]
  have hE_lb : (1 - 1 / (2 : ℝ) ^ q - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho) ≤ E_real := by
    have h1 := mul_le_mul_of_nonneg_left hexp_X_lb h1mq_nn
    have hprod_ge : 1 - 1 / (2 : ℝ) ^ q - 2 / (2 : ℝ) ^ P_fp ≤
        (1 - 1 / (2 : ℝ) ^ q) * (1 - 2 / (2 : ℝ) ^ P_fp) := by
      have hnn : 0 ≤ (1 / (2 : ℝ) ^ q) * (2 / (2 : ℝ) ^ P_fp) :=
        mul_nonneg (div_nonneg zero_le_one h2q_pos.le) (div_nonneg zero_le_two h2P_pos.le)
      have heq : (1 - 1 / (2 : ℝ) ^ q) * (1 - 2 / (2 : ℝ) ^ P_fp) =
          1 - 1 / (2 : ℝ) ^ q - 2 / (2 : ℝ) ^ P_fp + (1 / (2 : ℝ) ^ q) * (2 / (2 : ℝ) ^ P_fp) := by ring
      linarith only [hnn, heq]
    have h2 := mul_le_mul_of_nonneg_right hprod_ge hexp_pos.le
    have hass : (1 - 1 / (2 : ℝ) ^ q) * (1 - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho) =
        (1 - 1 / (2 : ℝ) ^ q) * ((1 - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho)) := mul_assoc _ _ _
    linarith only [h1, h2, hass, hE_lb_X]
  have h4P_le_q : 4 / (2 : ℝ) ^ P_fp ≤ 1 / (2 : ℝ) ^ q := by
    have hpow : (2 : ℝ) ^ (q + 2) ≤ (2 : ℝ) ^ P_fp := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_le_div_iff₀ h2P_pos h2q_pos]
    have : (2 : ℝ) ^ (q + 2) = 4 * (2 : ℝ) ^ q := by ring
    linarith only [hpow, this]
  have h2q_le_delta : 2 / (2 : ℝ) ^ q ≤ 1 / (4 * (k_nat : ℝ)) := by
    have hk_r : (8 * (k_nat : ℝ)) ≤ (2 : ℝ) ^ q := by exact_mod_cast hk_q
    have hk_pos : (0 : ℝ) < (k_nat : ℝ) := by exact_mod_cast hk
    rw [div_le_div_iff₀ h2q_pos (by linarith only [hk_pos])]
    linarith only [hk_r]
  have hv_nn : (0 : ℝ) ≤ v := by linarith only [hv_lo]
  have hv'_lb : (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) ≤ v' := by
    have hvE_ge : (1 / 2 : ℝ) ≤ v * Real.exp (wstr / rho) := by
      calc (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := (mul_one _).symm
        _ ≤ v * Real.exp (wstr / rho) := mul_le_mul hv_lo hexp_ge1 zero_le_one hv_nn
    have h1 : 1 / (2 : ℝ) ^ P_fp ≤ (2 / (2 : ℝ) ^ P_fp) * (v * Real.exp (wstr / rho)) := by
      have heq : 1 / (2 : ℝ) ^ P_fp = (2 / (2 : ℝ) ^ P_fp) * (1 / 2) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hvE_ge (div_nonneg zero_le_two h2P_pos.le)
    have hm := mul_le_mul_of_nonneg_left hE_lb hv_nn
    have h3 : 1 - 1 / (4 * (k_nat : ℝ)) ≤ 1 - 1 / (2 : ℝ) ^ q - 4 / (2 : ℝ) ^ P_fp := by
      have h2eq : 2 / (2 : ℝ) ^ q = 1 / (2 : ℝ) ^ q + 1 / (2 : ℝ) ^ q := by ring
      linarith only [h4P_le_q, h2q_le_delta, h2eq]
    have hm3 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hv_nn hexp_pos.le)
    have halg1 : v * ((1 - 1 / (2 : ℝ) ^ q - 2 / (2 : ℝ) ^ P_fp) * Real.exp (wstr / rho)) -
        (2 / (2 : ℝ) ^ P_fp) * (v * Real.exp (wstr / rho)) =
        (1 - 1 / (2 : ℝ) ^ q - 4 / (2 : ℝ) ^ P_fp) * (v * Real.exp (wstr / rho)) := by ring
    have halg2 : (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) =
        (1 - 1 / (4 * (k_nat : ℝ))) * (v * Real.exp (wstr / rho)) := mul_assoc _ _ _
    linarith only [hv'_gt, h1, hm, hm3, halg1, halg2]
  have hv'_pos : 0 < v' := by
    have hk_r : (1 : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast hk
    have h1m : (1 / 2 : ℝ) ≤ 1 - 1 / (4 * (k_nat : ℝ)) := by
      have : 1 / (4 * (k_nat : ℝ)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by linarith only [hk_r]) (by norm_num)]; linarith only [hk_r]
      linarith only [this]
    have hpos_rhs : 0 < (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) :=
      mul_pos (mul_pos (by linarith only [h1m]) (by linarith only [hv_lo])) hexp_pos
    linarith only [hv'_lb, hpos_rhs]
  have hv'_ub : v' ≤ (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) := by
    have hexp_le : Real.exp X_real ≤ Real.exp (wstr / rho) := Real.exp_le_exp.mpr hX_le
    have h1 : v' ≤ v * Real.exp (wstr / rho) := by
      have := mul_le_mul_of_nonneg_left (hE_le.trans hexp_le) hv_nn
      linarith only [hv'_le, this]
    have hk_nn : (0 : ℝ) ≤ (k_nat : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ (1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) :=
      mul_nonneg (mul_nonneg (div_nonneg zero_le_one (by linarith only [hk_nn])) hv_nn) hexp_pos.le
    have halg : (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) =
        v * Real.exp (wstr / rho) + (1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / rho) := by ring
    linarith only [h1, h2, halg]
  exact ⟨hv'_pos, hv'_lb, hv'_ub⟩

/-- Core arithmetic theorem for one fixed-point MWU edge update: verifies every intermediate `Fits`
bound and proves relative error `≤ 1 / (4 k)` for `v' = ⌊v_int · E_int / 2^P⌋ / 2^P`. -/
theorem lemma55_step_error
    {h L_in L_w P_fp q k_nat m0 rho_nat : ℕ}
    {num_int den_int v_int : ℤ} {wstr v : ℝ}
    (_hh : 1 ≤ h) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (m0 + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (hrho_pos : 1 ≤ rho_nat)
    (hrho_cap : rho_nat < 2 ^ (h * (L_w - L_in)))
    (hnum_pos : 0 < num_int) (hden_pos : 0 < den_int)
    (hwstr_eq : (num_int : ℝ) / (den_int : ℝ) = wstr)
    (hwstr_lo : 1 ≤ wstr) (hwstr_hi : wstr ≤ (rho_nat : ℝ) / 10)
    (hv_eq : (v_int : ℝ) / (2 : ℝ) ^ P_fp = v)
    (hv_lo : (1 / 2 : ℝ) ≤ v) (hv_hi : v ≤ 8 * (m0 : ℝ)) :
    let Q := floorDiv (num_int * (2 : ℤ) ^ P_fp) den_int
    let X := floorDiv (Q * (2 : ℤ) ^ P_fp) ((rho_nat : ℤ) * (2 : ℤ) ^ P_fp)
    Fits h L_w Q ∧
    Fits h L_w X ∧
    0 ≤ X ∧
    ((X : ℝ) / (2 : ℝ) ^ P_fp) ≤ 1 ∧
    ∀ (E_int : ℤ),
      let E_real := (E_int : ℝ) / (2 : ℝ) ^ P_fp
      1 ≤ E_real →
      E_real ≤ Real.exp ((X : ℝ) / (2 : ℝ) ^ P_fp) →
      |E_real - Real.exp ((X : ℝ) / (2 : ℝ) ^ P_fp)| ≤
        (1 / (2 : ℝ) ^ q) * Real.exp ((X : ℝ) / (2 : ℝ) ^ P_fp) →
      let P_int := (v_int * E_int) / (2 : ℤ) ^ P_fp
      let v' := (wrap h L_in P_int : ℝ) / (2 : ℝ) ^ P_fp
      0 ≤ E_int ∧
      2 * E_int < (capacity h L_in : ℤ) ∧
      wrap h L_in P_int = P_int ∧
      0 < v' ∧
      (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) ≤ v' ∧
      v' ≤ (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) := by
  intro Q X
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ P_fp := by positivity
  have h2P_ipos : (0 : ℤ) < (2 : ℤ) ^ P_fp := by positivity
  have hrho_rpos : (0 : ℝ) < (rho_nat : ℝ) := by exact_mod_cast hrho_pos
  have hrho_ipos : (0 : ℤ) < (rho_nat : ℤ) := by exact_mod_cast hrho_pos
  have hcap_w : capacity h L_w = 2 ^ (h * L_w) := capacity_eq_two_pow h L_w
  have hcap_in : capacity h L_in = 2 ^ (h * L_in) := capacity_eq_two_pow h L_in
  have hQ_eq : Q = (num_int * (2 : ℤ) ^ P_fp) / den_int := floorDiv_of_pos hden_pos
  have hQ_nn : 0 ≤ Q := by rw [hQ_eq]; exact Int.ediv_nonneg (by positivity) hden_pos.le
  have hQ_bds := int_ediv_real_bounds (x := num_int * (2 : ℤ) ^ P_fp) hden_pos
  rw [← hQ_eq] at hQ_bds
  have hQ_real_eq : ((num_int * (2 : ℤ) ^ P_fp : ℤ) : ℝ) / (den_int : ℝ) = wstr * (2 : ℝ) ^ P_fp := by
    push_cast; rw [← hwstr_eq]; ring
  rw [hQ_real_eq] at hQ_bds
  -- `Fits h L_w Q`
  have hfit_Q : Fits h L_w Q := by
    have hQ_lt : 2 * (Q : ℝ) < (capacity h L_w : ℝ) := by
      have h1 : (Q : ℝ) ≤ ((rho_nat : ℝ) / 10) * (2 : ℝ) ^ P_fp :=
        hQ_bds.2.trans (mul_le_mul_of_nonneg_right hwstr_hi h2P_pos.le)
      have hrho_r : (rho_nat : ℝ) < (2 : ℝ) ^ (h * (L_w - L_in)) := by exact_mod_cast hrho_cap
      have hpow_le : (2 : ℝ) ^ (h * (L_w - L_in)) * (2 : ℝ) ^ P_fp ≤ (2 : ℝ) ^ (h * L_w) / 2 := by
        rw [← pow_add]
        have hexp : h * (L_w - L_in) + P_fp + 1 ≤ h * L_w := by
          have hsub : h * (L_w - L_in) + h * L_in = h * L_w := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hLin_le]
          omega
        have hle : (2 : ℝ) ^ (h * (L_w - L_in) + P_fp + 1) ≤ (2 : ℝ) ^ (h * L_w) :=
          pow_le_pow_right₀ (by norm_num) hexp
        rw [pow_succ] at hle; linarith
      rw [hcap_w]; push_cast
      nlinarith
    have hQ_lt_z : 2 * Q < (capacity h L_w : ℤ) := by exact_mod_cast hQ_lt
    exact ⟨by linarith [show (0 : ℤ) ≤ capacity h L_w by positivity], hQ_lt_z⟩
  -- `X = floorDiv (Q * 2^P) (ρ * 2^P)`
  have hdenX_pos : (0 : ℤ) < (rho_nat : ℤ) * (2 : ℤ) ^ P_fp := mul_pos hrho_ipos h2P_ipos
  have hX_eq : X = (Q * (2 : ℤ) ^ P_fp) / ((rho_nat : ℤ) * (2 : ℤ) ^ P_fp) := floorDiv_of_pos hdenX_pos
  have hX_nn : 0 ≤ X := by rw [hX_eq]; exact Int.ediv_nonneg (by positivity) hdenX_pos.le
  have hX_bds := int_ediv_real_bounds (x := Q * (2 : ℤ) ^ P_fp) hdenX_pos
  rw [← hX_eq] at hX_bds
  have hX_real_eq : ((Q * (2 : ℤ) ^ P_fp : ℤ) : ℝ) / (((rho_nat : ℤ) * (2 : ℤ) ^ P_fp : ℤ) : ℝ) =
      (Q : ℝ) / (rho_nat : ℝ) := by
    push_cast; field_simp [ne_of_gt h2P_pos, ne_of_gt hrho_rpos]
  rw [hX_real_eq] at hX_bds
  have hX_le_tenth : (X : ℝ) / (2 : ℝ) ^ P_fp ≤ 1 / 10 := by
    have h1 : (X : ℝ) ≤ (Q : ℝ) / (rho_nat : ℝ) := hX_bds.2
    have h2 : (Q : ℝ) / (rho_nat : ℝ) ≤ (wstr / (rho_nat : ℝ)) * (2 : ℝ) ^ P_fp := by
      rw [div_le_iff₀ hrho_rpos]
      have : (wstr / (rho_nat : ℝ)) * (2 : ℝ) ^ P_fp * (rho_nat : ℝ) = wstr * (2 : ℝ) ^ P_fp := by
        field_simp [ne_of_gt hrho_rpos]
      linarith [hQ_bds.2]
    have h3 : wstr / (rho_nat : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hrho_rpos]; linarith
    rw [div_le_iff₀ h2P_pos]
    nlinarith [h1, h2, h3]
  have hX_le_one : (X : ℝ) / (2 : ℝ) ^ P_fp ≤ 1 := by linarith
  have hfit_X : Fits h L_w X := by
    have hX_lt : 2 * (X : ℝ) < (capacity h L_w : ℝ) := by
      have h1 : (X : ℝ) ≤ (2 : ℝ) ^ P_fp := by
        have := (div_le_iff₀ h2P_pos).mp hX_le_one; linarith
      have hexp : P_fp + 2 ≤ h * L_w := by
        have : h * L_in ≤ h * L_w := Nat.mul_le_mul_left h hLin_le; omega
      have hpow : (2 : ℝ) ^ (P_fp + 2) ≤ (2 : ℝ) ^ (h * L_w) :=
        pow_le_pow_right₀ (by norm_num) hexp
      rw [hcap_w]; push_cast
      have h4 : (2 : ℝ) ^ (P_fp + 2) = 4 * (2 : ℝ) ^ P_fp := by ring
      linarith
    have hX_lt_z : 2 * X < (capacity h L_w : ℤ) := by exact_mod_cast hX_lt
    exact ⟨by linarith [show (0 : ℤ) ≤ capacity h L_w by positivity], hX_lt_z⟩
  refine ⟨hfit_Q, hfit_X, hX_nn, hX_le_one, ?_⟩
  intro E_int E_real hE1 hE_le hE_err P_int v'
  have hE_nn : 0 ≤ E_int := by
    have : (0 : ℝ) ≤ (E_int : ℝ) := by
      have := (le_div_iff₀ h2P_pos).mp (le_trans zero_le_one hE1); linarith
    exact_mod_cast this
  have hX_real_le_wstr : (X : ℝ) / (2 : ℝ) ^ P_fp ≤ wstr / (rho_nat : ℝ) := by
    rw [div_le_iff₀ h2P_pos]
    have h1 : (Q : ℝ) / (rho_nat : ℝ) ≤ wstr / (rho_nat : ℝ) * (2 : ℝ) ^ P_fp := by
      rw [div_le_iff₀ hrho_rpos]
      have : wstr / (rho_nat : ℝ) * (2 : ℝ) ^ P_fp * (rho_nat : ℝ) = wstr * (2 : ℝ) ^ P_fp := by
        field_simp [ne_of_gt hrho_rpos]
      linarith [hQ_bds.2]
    linarith [hX_bds.2]
  have hexp_half_lt2 : Real.exp ((X : ℝ) / (2 : ℝ) ^ P_fp) < 2 := by
    have h1 : Real.exp ((X : ℝ) / (2 : ℝ) ^ P_fp) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hq1 : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
      linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
    have hq2 : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
      rw [show (1 / 4 : ℝ) = -(-(1 / 4 : ℝ)) by ring, Real.exp_neg]
      calc (Real.exp (-(1 / 4 : ℝ)))⁻¹ ≤ (3 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq1
        _ = 4 / 3 := by norm_num
    have hsq : Real.exp (1 / 4 : ℝ) ^ 2 = Real.exp (1 / 2 : ℝ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hle := pow_le_pow_left₀ (Real.exp_pos _).le hq2 2
    rw [hsq] at hle; norm_num at hle
    linarith
  have hE_lt2 : E_real < 2 := lt_of_le_of_lt hE_le hexp_half_lt2
  have hE_fit_in : 2 * E_int < (capacity h L_in : ℤ) := by
    have hEr : 2 * (E_int : ℝ) < (2 : ℝ) ^ (h * L_in) := by
      have h1 : (E_int : ℝ) < 2 * (2 : ℝ) ^ P_fp := by
        have := (div_lt_iff₀ h2P_pos).mp hE_lt2; linarith
      have hpow : (2 : ℝ) ^ (P_fp + 2) ≤ (2 : ℝ) ^ (h * L_in) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℝ) ^ (P_fp + 2) = 4 * (2 : ℝ) ^ P_fp := by ring
      linarith
    rw [hcap_in]; exact_mod_cast hEr
  -- Product `P_int = (v_int * E_int) / 2^P_fp` fits in `L_in` limbs
  have hv_int_nn : 0 ≤ v_int := by
    have h1 : (0 : ℝ) ≤ (v_int : ℝ) / (2 : ℝ) ^ P_fp := by linarith
    have : (0 : ℝ) ≤ (v_int : ℝ) := by
      have := (le_div_iff₀ h2P_pos).mp h1; linarith
    exact_mod_cast this
  have hP_nn : 0 ≤ P_int := Int.ediv_nonneg (mul_nonneg hv_int_nn hE_nn) h2P_ipos.le
  have hP_bds := int_ediv_real_bounds (x := v_int * E_int) h2P_ipos
  have hP_real_eq : ((v_int * E_int : ℤ) : ℝ) / (((2 : ℤ) ^ P_fp : ℤ) : ℝ) =
      v * E_real * (2 : ℝ) ^ P_fp := by
    dsimp only [E_real]; push_cast; rw [← hv_eq]; field_simp [ne_of_gt h2P_pos]
  rw [hP_real_eq] at hP_bds
  have hfit_P : Fits h L_in P_int := by
    have hP_lt : 2 * (P_int : ℝ) < (capacity h L_in : ℝ) := by
      have h1 : (P_int : ℝ) ≤ 16 * (m0 : ℝ) * (2 : ℝ) ^ P_fp := by
        have hve : v * E_real ≤ 8 * (m0 : ℝ) * 2 :=
          mul_le_mul hv_hi hE_lt2.le (by positivity) (by positivity)
        nlinarith [hP_bds.2]
      have hm_r : (32 * (m0 + 1) * 2 ^ P_fp : ℝ) < (2 : ℝ) ^ (h * L_in - 1) := by
        exact_mod_cast hm_Lin
      have h2pow : 2 * (2 : ℝ) ^ (h * L_in - 1) = (2 : ℝ) ^ (h * L_in) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [hcap_in]; push_cast
      nlinarith
    have hP_lt_z : 2 * P_int < (capacity h L_in : ℤ) := by exact_mod_cast hP_lt
    exact ⟨by linarith [show (0 : ℤ) ≤ capacity h L_in by positivity], hP_lt_z⟩
  have hwrap : wrap h L_in P_int = P_int := wrap_of_fits hfit_P
  -- Upper & lower error bounds for `v'`
  have hv'_eq : v' = (P_int : ℝ) / (2 : ℝ) ^ P_fp := by dsimp only [v']; rw [hwrap]
  have hv'_le : v' ≤ v * E_real := by
    rw [hv'_eq, div_le_iff₀ h2P_pos]; exact hP_bds.2
  have hv'_gt : v * E_real - 1 / (2 : ℝ) ^ P_fp < v' := by
    rw [hv'_eq, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2P_pos]
    linarith [hP_bds.1]
  have hX_lb : wstr / (rho_nat : ℝ) - 2 / (2 : ℝ) ^ P_fp < (X : ℝ) / (2 : ℝ) ^ P_fp := by
    have hrho_ge1 : (1 : ℝ) ≤ (rho_nat : ℝ) := by exact_mod_cast hrho_pos
    have h1 : (Q : ℝ) / (rho_nat : ℝ) > (wstr * (2 : ℝ) ^ P_fp - 1) / (rho_nat : ℝ) :=
      div_lt_div_of_pos_right hQ_bds.1 hrho_rpos
    have h2 : (X : ℝ) > (wstr * (2 : ℝ) ^ P_fp - 1) / (rho_nat : ℝ) - 1 := by
      linarith only [h1, hX_bds.1]
    have hinv : 1 / (rho_nat : ℝ) ≤ 1 := by rw [div_le_one hrho_rpos]; exact hrho_ge1
    have h3 : (wstr * (2 : ℝ) ^ P_fp - 1) / (rho_nat : ℝ) - 1 ≥
        (wstr / (rho_nat : ℝ)) * (2 : ℝ) ^ P_fp - 2 := by
      have : (wstr * (2 : ℝ) ^ P_fp - 1) / (rho_nat : ℝ) =
          (wstr / (rho_nat : ℝ)) * (2 : ℝ) ^ P_fp - 1 / (rho_nat : ℝ) := by ring
      linarith only [this, hinv]
    rw [lt_div_iff₀ h2P_pos]
    have : (wstr / (rho_nat : ℝ) - 2 / (2 : ℝ) ^ P_fp) * (2 : ℝ) ^ P_fp =
        (wstr / (rho_nat : ℝ)) * (2 : ℝ) ^ P_fp - 2 := by field_simp [ne_of_gt h2P_pos]
    linarith only [h2, h3, this]
  obtain ⟨hv'_pos, hv'_lb, hv'_ub⟩ :=
    lemma55_step_error_combine hk hq_P hk_q hrho_rpos hwstr_lo hv_lo
      hX_real_le_wstr hX_lb hE_le hE_err hv'_le hv'_gt
  exact ⟨hE_nn, hE_fit_in, hwrap, hv'_pos, hv'_lb, hv'_ub⟩

end

end MinCostFlow.LSF.Program
