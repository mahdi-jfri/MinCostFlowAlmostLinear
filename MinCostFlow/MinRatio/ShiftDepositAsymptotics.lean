module

public import MinCostFlow.MinRatio.ShiftDepositBound
public import MinCostFlow.Final.TimeFactorBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The shift deposit is `m^{o(1)}`

`shiftDeposit_le` (`ShiftDepositBound.lean`) bounds the deposit per update by

  `(d + 1) (11 Ψ)^{d+1} 2^{d+2} M₀^{2/d} (clog₂ (N₀ + 2))² + 1`.

Here we show that this is at most `C · alg2TimeFactor E (47/48) M₀` for constants `C` and `E`
that do not depend on the input, when the parameters are those of the paper. Write
`L = log (M₀ + 2)` and `A = L^{47/48} log (L + 2)`. The hypotheses are
the ones that the concrete parameters meet:

* the depth is `d = ⌈L^{1/48}⌉` (`chosenD (23/24)`, the choice of the proof of Theorem 7.1), so
  `L^{1/48} ≤ d ≤ 2 L^{1/48}`;
* `Ψ ≤ exp (C_ψ L^{23/24} log (L + 2))`;
* `log (N₀ + 2) ≤ C_N L`.

Each factor is then `exp (O(A))`:

* `d + 1 ≤ e^d ≤ e^{2A}` and `2^{d+2} ≤ e^{d+2} ≤ e^{4A}`;
* `(11 Ψ)^{d+1} = exp ((d + 1) log (11 Ψ))` and `(d + 1) log (11 Ψ) ≤ 3 L^{1/48} · (3 + C_ψ)
  L^{23/24} log (L + 2) = 3 (3 + C_ψ) A`;
* `M₀^{2/d} = exp (2 log M₀ / d) ≤ exp (2 L / L^{1/48}) = exp (2 L^{47/48})`;
* `clog₂ (N₀ + 2) ≤ 1 + 2 log (N₀ + 2) ≤ (1 + 2 C_N) L`, and `L² = exp (2 log L) ≤ e^{2A}`.

The main results are `shiftDepositBound_le_exp` (the product) and `shiftDeposit_le_timeFactor`
(the deposit), and `alg2TimeFactor_max_le`, which moves the bound from `M₀ = max m T` to the edge
count `m`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- The shape `A = L^{47/48} log (L + 2)` of the time factor, with `L = log (M + 2)`. -/
@[expose] noncomputable def logShape (M : ℕ) : ℝ :=
  Real.log ((M : ℝ) + 2) ^ (47 / 48 : ℝ) * Real.log (Real.log ((M : ℝ) + 2) + 2)

theorem alg2TimeFactor_eq_exp_logShape (E : ℝ) (M : ℕ) :
    alg2TimeFactor E (47 / 48) M = Real.exp (E * logShape M) := by
  unfold alg2TimeFactor logShape
  rw [mul_assoc]

/-- The shape `A` is at least one when `M ≥ 1`. -/
theorem one_le_logShape {M : ℕ} (hM : 1 ≤ M) : 1 ≤ logShape M := by
  unfold logShape
  have hL : 1 ≤ Real.log ((M : ℝ) + 2) := by
    have h3 : Real.exp 1 ≤ (M : ℝ) + 2 := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith [Real.exp_one_lt_d9]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hLL : 1 ≤ Real.log (Real.log ((M : ℝ) + 2) + 2) := by
    have h3 : Real.exp 1 ≤ Real.log ((M : ℝ) + 2) + 2 := by linarith [Real.exp_one_lt_d9]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hp : 1 ≤ Real.log ((M : ℝ) + 2) ^ (47 / 48 : ℝ) := Real.one_le_rpow hL (by norm_num)
  nlinarith

private theorem pow_le_exp_of {y B : ℝ} (hy : 0 < y) (n : ℕ) (h : (n : ℝ) * Real.log y ≤ B) :
    y ^ n ≤ Real.exp B := by
  rw [← Real.exp_log (pow_pos hy n), Real.log_pow]
  exact Real.exp_le_exp.mpr h

private theorem clog_two_le (x : ℕ) (hx : 1 < x) :
    (Nat.clog 2 x : ℝ) ≤ 1 + 2 * Real.log x := by
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : ((Nat.clog 2 x).pred : ℝ) * Real.log 2 < Real.log x := by
    have h := Real.log_lt_log (by positivity) (show ((2 : ℝ) ^ (Nat.clog 2 x).pred) < x by
      exact_mod_cast hlt)
    rwa [Real.log_pow] at h
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpred : (Nat.clog 2 x : ℝ) ≤ (Nat.clog 2 x).pred + 1 := by
    have : Nat.clog 2 x ≤ (Nat.clog 2 x).pred + 1 := Order.le_succ_pred _
    exact_mod_cast this
  have hp0 : (0 : ℝ) ≤ (Nat.clog 2 x).pred := Nat.cast_nonneg _
  nlinarith

/-! ### The five factors

Each lemma bounds one factor in terms of real numbers `L ≥ 1`, `LL ≥ 1`, `r = L^{1/48}` and
`A = L^{47/48} LL`, with `L^{1/48} L^{23/24} = L^{47/48}` and `L^{1/48} L^{47/48} = L`. -/

private theorem factor_depth {d r A : ℝ} (hd : d ≤ 2 * r) (hrA : r ≤ A) :
    d + 1 ≤ Real.exp (2 * A) :=
  (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr (by linarith))

private theorem log_eleven_le : Real.log 11 ≤ 3 := by
  have h11 : (11 : ℝ) ≤ Real.exp 3 := by
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (11 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
  calc Real.log 11 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h11
    _ = 3 := Real.log_exp 3

/-- `(11 Ψ)^{d+1} ≤ exp (3 (3 + C_ψ) A)` when `d + 1 ≤ 3 r`, `log Ψ ≤ C_ψ L^{23/24} LL` and
`r L^{23/24} LL = A`, here with `L^{23/24}` written `L23`. -/
theorem psi_pow_le_exp {psi C_ψ r L23 LL A : ℝ} (d : ℕ) (hpsi : 1 ≤ psi)
    (hd : (d : ℝ) + 1 ≤ 3 * r) (hL23 : 1 ≤ L23) (hLL : 1 ≤ LL)
    (hψ : Real.log psi ≤ C_ψ * L23 * LL) (hA : r * L23 * LL = A) :
    (11 * psi) ^ (d + 1) ≤ Real.exp (3 * (3 + C_ψ) * A) := by
  have hlog : Real.log (11 * psi) ≤ (3 + C_ψ) * (L23 * LL) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h1 : (1 : ℝ) ≤ L23 * LL := one_le_mul_of_one_le_of_one_le hL23 hLL
    nlinarith [log_eleven_le]
  have hlog0 : 0 ≤ Real.log (11 * psi) := Real.log_nonneg (by linarith)
  apply pow_le_exp_of (by linarith)
  push_cast
  calc ((d : ℝ) + 1) * Real.log (11 * psi) ≤ 3 * r * ((3 + C_ψ) * (L23 * LL)) :=
        mul_le_mul hd hlog hlog0 (by linarith)
    _ = 3 * (3 + C_ψ) * (r * L23 * LL) := by ring
    _ = 3 * (3 + C_ψ) * A := by rw [hA]

private theorem factor_two {r A : ℝ} (d : ℕ) (hd : (d : ℝ) ≤ 2 * r) (hrA : r ≤ A) (hA : 1 ≤ A) :
    (2 : ℝ) ^ (d + 2) ≤ Real.exp (4 * A) := by
  apply pow_le_exp_of (by norm_num)
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  push_cast
  nlinarith

private theorem factor_root {M L r L47 A d : ℝ} (hM : 1 ≤ M) (hML : Real.log M ≤ L)
    (hr : 0 < r) (hrd : r ≤ d) (hsplit : r * L47 = L) (hL47 : L47 ≤ A) :
    M ^ (2 / d) ≤ Real.exp (2 * A) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM
  have h1 : Real.log M * (2 / d) ≤ L * (2 / r) :=
    mul_le_mul hML (div_le_div_of_nonneg_left (by norm_num) hr hrd)
      (div_nonneg (by norm_num) (by linarith)) (by linarith)
  have h2 : L * (2 / r) = 2 * L47 := by
    rw [← hsplit]; field_simp
  linarith

private theorem factor_clog {N₀ : ℕ} {C_N L LL A : ℝ} (hCN : 0 ≤ C_N) (hL : 1 ≤ L)
    (hN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * L) (hLL : Real.log L ≤ LL) (hLLA : LL ≤ A) :
    (Nat.clog 2 (N₀ + 2) : ℝ) ^ 2 ≤ (1 + 2 * C_N) ^ 2 * Real.exp (2 * A) := by
  have hcl := clog_two_le (N₀ + 2) (by omega)
  push_cast at hcl
  have hc1 : (Nat.clog 2 (N₀ + 2) : ℝ) ≤ (1 + 2 * C_N) * L := by nlinarith
  have hLsq : L ^ 2 ≤ Real.exp (2 * A) :=
    pow_le_exp_of (by linarith) 2 (by push_cast; linarith)
  calc (Nat.clog 2 (N₀ + 2) : ℝ) ^ 2 ≤ ((1 + 2 * C_N) * L) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hc1 2
    _ = (1 + 2 * C_N) ^ 2 * L ^ 2 := by ring
    _ ≤ (1 + 2 * C_N) ^ 2 * Real.exp (2 * A) :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)

/-- `log (M + 2) ≥ 1` for `M ≥ 1`. -/
theorem one_le_log_add_two' {M : ℕ} (hM : 1 ≤ M) : 1 ≤ Real.log ((M : ℝ) + 2) := by
  have h3 : Real.exp 1 ≤ (M : ℝ) + 2 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith [Real.exp_one_lt_d9]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

/-- `log (L + 2) ≥ 1` for `L ≥ 1`. -/
theorem one_le_log_log_add_two {L : ℝ} (hL : 1 ≤ L) : 1 ≤ Real.log (L + 2) := by
  have h3 : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_d9]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

/-- **The deposit bound is `exp (O(A))`.** For the depth `d = chosenD (23/24) M₀`, for
`1 ≤ Ψ ≤ exp (C_ψ L^{23/24} log (L + 2))` and for `log (N₀ + 2) ≤ C_N L`, the bound of
`shiftDeposit_le` without its `+ 1` is at most `(1 + 2 C_N)² exp ((19 + 3 C_ψ) A)`. -/
theorem shiftDepositBound_le_exp (P : ChainParams) (N₀ : ℕ) {psi C_ψ C_N : ℝ}
    (hpsi : 1 ≤ psi) (hCN : 0 ≤ C_N) (hd : P.d = chosenD (23 / 24) P.M₀)
    (hN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((P.M₀ : ℝ) + 2))
    (hψ : psi ≤ Real.exp (C_ψ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2))) :
    (P.d + 1) * (11 * psi) ^ (P.d + 1) * 2 ^ (P.d + 2) * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
        (Nat.clog 2 (N₀ + 2) : ℝ) ^ 2 ≤
      (1 + 2 * C_N) ^ 2 * Real.exp ((19 + 3 * C_ψ) * logShape P.M₀) := by
  have hL1 := one_le_log_add_two' P.hM₀
  have hLL1 := one_le_log_log_add_two hL1
  have hA1 := one_le_logShape P.hM₀
  have hAeq : logShape P.M₀ = Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
      Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2) := rfl
  obtain ⟨_, hdLo, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) P.hM₀
  rw [← hd, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdLo hdHi
  have hr1 : 1 ≤ Real.log ((P.M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL47 : 1 ≤ Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL23 : 1 ≤ Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hrL : Real.log ((P.M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) ≤
      Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hL47A : Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) ≤ logShape P.M₀ := by
    rw [hAeq]; exact le_mul_of_one_le_right (by linarith) hLL1
  have hLLA : Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2) ≤ logShape P.M₀ := by
    rw [hAeq]; exact le_mul_of_one_le_left (by linarith) hL47
  have hsplit : Real.log ((P.M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) *
      Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) = Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hsplit2 : Real.log ((P.M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) *
      Real.log ((P.M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) = Real.log ((P.M₀ : ℝ) + 2) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hM1 : (1 : ℝ) ≤ P.M₀ := by exact_mod_cast P.hM₀
  have ha := factor_depth hdHi (hrL.trans hL47A)
  have hb := psi_pow_le_exp (A := logShape P.M₀) (r := Real.log ((P.M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) P.d hpsi (by linarith) hL23 hLL1
    ((Real.log_le_log (by linarith) hψ).trans (le_of_eq (Real.log_exp _)))
    (by rw [hsplit, hAeq])
  have hc := factor_two P.d hdHi (hrL.trans hL47A) hA1
  have hdd := factor_root hM1 (Real.log_le_log (by linarith) (by linarith)) (by linarith) hdLo
    hsplit2 hL47A
  have he := factor_clog (N₀ := N₀) hCN hL1 hN
    (Real.log_le_log (by linarith) (by linarith)) hLLA
  calc ((P.d : ℝ) + 1) * (11 * psi) ^ (P.d + 1) * 2 ^ (P.d + 2) * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
        (Nat.clog 2 (N₀ + 2) : ℝ) ^ 2
      ≤ Real.exp (2 * logShape P.M₀) * Real.exp (3 * (3 + C_ψ) * logShape P.M₀) *
          Real.exp (4 * logShape P.M₀) * Real.exp (2 * logShape P.M₀) *
          ((1 + 2 * C_N) ^ 2 * Real.exp (2 * logShape P.M₀)) := by
        gcongr
    _ = (1 + 2 * C_N) ^ 2 * Real.exp ((19 + 3 * C_ψ) * logShape P.M₀) := by
        rw [show (19 + 3 * C_ψ) * logShape P.M₀ = 2 * logShape P.M₀ +
          3 * (3 + C_ψ) * logShape P.M₀ + 4 * logShape P.M₀ + 2 * logShape P.M₀ +
          2 * logShape P.M₀ by ring]
        simp only [Real.exp_add]
        ring

/-- **`(11 Ψ)^{d+1}` is `exp (O(A))`.** For `d = chosenD (23/24) M₀` and
`1 ≤ Ψ ≤ exp (C_ψ L^{23/24} log (L + 2))`, `(11 Ψ)^{d+1} ≤ exp (3 (3 + C_ψ) A)`. -/
theorem eleven_psi_pow_le_exp {M₀ d : ℕ} (hM : 1 ≤ M₀) {psi C_ψ : ℝ} (hpsi : 1 ≤ psi)
    (hd : d = chosenD (23 / 24) M₀)
    (hψ : psi ≤ Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    (11 * psi) ^ (d + 1) ≤ Real.exp (3 * (3 + C_ψ) * logShape M₀) := by
  have hL1 := one_le_log_add_two' hM
  have hLL1 := one_le_log_log_add_two hL1
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM
  rw [← hd, show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  have hr1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL23 : 1 ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hsplit : Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ) *
      Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) = Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  exact psi_pow_le_exp (A := logShape M₀) (r := Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) d hpsi
    (by linarith) hL23 hLL1 ((Real.log_le_log (by linarith) hψ).trans (le_of_eq (Real.log_exp _)))
    (by rw [hsplit]; rfl)

/-- **The deposit is `m^{o(1)}`.** Under the hypotheses of `shiftDepositBound_le_exp`, the
deposit per update at every level `i ≤ d` is at most
`((1 + 2 C_N)² + 1) · alg2TimeFactor (19 + 3 C_ψ) (47/48) M₀`. -/
theorem shiftDeposit_le_timeFactor (P : ChainParams) (N₀ : ℕ) {psi C_ψ C_N : ℝ}
    (hpsi : 1 ≤ psi) (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N) (hd : P.d = chosenD (23 / 24) P.M₀)
    (hN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((P.M₀ : ℝ) + 2))
    (hψ : psi ≤ Real.exp (C_ψ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2))) {i : ℕ} (hi : i ≤ P.d) :
    (shiftDeposit P N₀ psi i : ℝ) ≤
      ((1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) P.M₀ := by
  have h1 := shiftDeposit_le P N₀ hpsi hi
  have h2 := shiftDepositBound_le_exp P N₀ hpsi hCN hd hN hψ
  have hT1 : 1 ≤ alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) P.M₀ :=
    Final.scalingTimeFactor_one_le (by linarith) _
  rw [alg2TimeFactor_eq_exp_logShape] at hT1 ⊢
  nlinarith

/-- The time factor at `max m T` is at most its value at `T` times its value at `m`, since it is
monotone in the edge count and at least one. This moves a bound in terms of `M₀ = max m T` to
one in terms of the edge count `m`. -/
theorem alg2TimeFactor_max_le {E : ℝ} (hE : 0 ≤ E) (m T : ℕ) :
    alg2TimeFactor E (47 / 48) (max m T) ≤
      alg2TimeFactor E (47 / 48) T * alg2TimeFactor E (47 / 48) m := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → alg2TimeFactor E (47 / 48) a ≤ alg2TimeFactor E (47 / 48) b := by
    intro a b hab
    rw [alg2TimeFactor_eq_exp_logShape, alg2TimeFactor_eq_exp_logShape, Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ hE
    unfold logShape
    have hab' : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hab 2
    have ha2 : (1 : ℝ) ≤ (a : ℝ) + 2 := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    have hlog : Real.log ((a : ℝ) + 2) ≤ Real.log ((b : ℝ) + 2) :=
      Real.log_le_log (by linarith) hab'
    have hla : 0 ≤ Real.log ((a : ℝ) + 2) := Real.log_nonneg ha2
    apply mul_le_mul (Real.rpow_le_rpow hla hlog (by norm_num))
      (Real.log_le_log (by linarith) (by linarith)) (Real.log_nonneg (by linarith))
      (Real.rpow_nonneg (by linarith) _)
  have h1m := Final.scalingTimeFactor_one_le hE m
  have h1T := Final.scalingTimeFactor_one_le hE T
  rcases le_total m T with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- **The deposit is `m^{o(1)}` in the edge count.** When the chain is built for `M₀ = max m T`,
with `T` a threshold that does not depend on the input, the deposit is at most
`C · alg2TimeFactor E (47/48) m` with constants `C` and `E` that depend only on `C_ψ`, `C_N` and
`T`. This is the form that `cycleRate_subpoly` asks for (`SubpolyNat`). -/
theorem shiftDeposit_le_timeFactor_edges {C_ψ C_N : ℝ} (hCψ : 0 ≤ C_ψ) (hCN : 0 ≤ C_N) (T : ℕ) :
    ∃ C E : ℝ, 0 ≤ E ∧ ∀ (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (i m : ℕ), P.M₀ = max m T →
      1 ≤ psi → P.d = chosenD (23 / 24) P.M₀ →
      Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((P.M₀ : ℝ) + 2) →
      psi ≤ Real.exp (C_ψ * Real.log ((P.M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((P.M₀ : ℝ) + 2) + 2)) → i ≤ P.d →
      (shiftDeposit P N₀ psi i : ℝ) ≤ C * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) m := by
  have hE : (0 : ℝ) ≤ 19 + 3 * C_ψ := by linarith
  refine ⟨((1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) T, 19 + 3 * C_ψ, hE,
    fun P N₀ psi i m hM hpsi hd hN hψ hi => ?_⟩
  have h1 := shiftDeposit_le_timeFactor P N₀ hpsi hCψ hCN hd hN hψ hi
  rw [hM] at h1
  have h2 := alg2TimeFactor_max_le hE m T
  have hK : (0 : ℝ) ≤ (1 + 2 * C_N) ^ 2 + 1 := by positivity
  calc (shiftDeposit P N₀ psi i : ℝ)
      ≤ ((1 + 2 * C_N) ^ 2 + 1) * alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) (max m T) := h1
    _ ≤ ((1 + 2 * C_N) ^ 2 + 1) * (alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) T *
          alg2TimeFactor (19 + 3 * C_ψ) (47 / 48) m) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

/-- For `N₀ = 4 M₀`, the hypothesis on `N₀` of `shiftDeposit_le_timeFactor` holds with
`C_N = 3`: `log (4 M₀ + 2) ≤ log 4 + log (M₀ + 2) ≤ 3 log (M₀ + 2)`. -/
theorem log_four_mul_add_two_le {M₀ : ℕ} (hM : 1 ≤ M₀) :
    Real.log (((4 * M₀ : ℕ) : ℝ) + 2) ≤ 3 * Real.log ((M₀ : ℝ) + 2) := by
  have hL1 := one_le_log_add_two' hM
  have hpos : (0 : ℝ) < (M₀ : ℝ) + 2 := by positivity
  have h1 : (((4 * M₀ : ℕ) : ℝ) + 2) ≤ 4 * ((M₀ : ℝ) + 2) := by push_cast; linarith
  have h2 : Real.log (((4 * M₀ : ℕ) : ℝ) + 2) ≤ Real.log 4 + Real.log ((M₀ : ℝ) + 2) := by
    rw [← Real.log_mul (by norm_num) hpos.ne']
    exact Real.log_le_log (by positivity) h1
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  linarith

end MinCostFlow.MinRatio
