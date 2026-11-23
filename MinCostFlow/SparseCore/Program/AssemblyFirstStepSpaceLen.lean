module

public import MinCostFlow.DynSpanner.Invariant
public import MinCostFlow.DynSpanner.Program.SparsifyContract
public import MinCostFlow.Expander.Section8Asymptotics

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear walk-length and stretch bounds under `chosenL` and subpolynomial stretch (`AssemblyFirstStepSpaceLen`)

Under the Theorem 8.2 balancing depth `depth ≤ Expander.chosenL ((M + N) ^ 2)` and a subpolynomial
static-sparsifier walk-stretch bound `impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))`:
* `ceil_gamma_le_linear_of_subpoly`: `⌈impl.γ_ℓ m⌉₊ ≤ ⌈exp (C_sp ^ 8)⌉₊ * (m + 2)`.
* `ceil_lenBound_le_linear_of_chosenL`:
  `⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ lenBoundLinearConst C_sp * (M + N + 2)` where
  `lenBoundLinearConst C_sp = ⌈exp ((24 + 12 * C_sp) ^ 12)⌉₊` depends only on `C_sp`.

Both bounds use the elementary case-split inequality `A * t ^ (p / q) ≤ A ^ q + t` for `A, t ≥ 0`
(with `p / q = 7 / 8` and `p / q = 11 / 12 = 1 / 24 + 7 / 8`).
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.Expander

@[expose] public section

/-- Constant in the linear bound `⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ lenBoundLinearConst C_sp * (M + N + 2)`
under `depth ≤ Expander.chosenL ((M + N) ^ 2)` and subpolynomial stretch with constant `C_sp`. -/
noncomputable def lenBoundLinearConst (C_sp : ℝ) : ℕ :=
  ⌈Real.exp ((24 + 12 * C_sp) ^ 12)⌉₊

/-- Constant in the linear stretch bound `⌈impl.γ_ℓ m⌉₊ ≤ gammaLinearConst C_sp * (m + 2)`
under subpolynomial stretch with constant `C_sp`. -/
noncomputable def gammaLinearConst (C_sp : ℝ) : ℕ :=
  ⌈Real.exp (C_sp ^ 8)⌉₊

end

private lemma mul_rpow_le_pow_add {A t : ℝ} {n : ℕ} (hn : 1 ≤ n) (hA : 0 ≤ A) (ht : 0 ≤ t) :
    A * t ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) ≤ A ^ n + t := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / (n : ℝ) := by positivity
  by_cases hle : t ≤ A ^ n
  · have h1 : t ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) ≤ (A ^ n) ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) :=
      Real.rpow_le_rpow ht hle hq0
    have h2 : (A ^ n) ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) = A ^ (n - 1) := by
      rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA]
      have hmul : (n : ℝ) * (((n - 1 : ℕ) : ℝ) / (n : ℝ)) = ((n - 1 : ℕ) : ℝ) := by
        field_simp
      rw [hmul, Real.rpow_natCast]
    have h3 : A * A ^ (n - 1) = A ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    calc A * t ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ))
        ≤ A * (A ^ n) ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left h1 hA
      _ = A * A ^ (n - 1) := by rw [h2]
      _ = A ^ n := h3
      _ ≤ A ^ n + t := by linarith
  · have hlt : A ^ n ≤ t := le_of_not_ge hle
    have h1 : (A ^ n) ^ ((1 : ℝ) / (n : ℝ)) ≤ t ^ ((1 : ℝ) / (n : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hlt (by positivity)
    have h2 : (A ^ n) ^ ((1 : ℝ) / (n : ℝ)) = A := by
      rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA]
      have hmul : (n : ℝ) * ((1 : ℝ) / (n : ℝ)) = 1 := by field_simp
      rw [hmul, Real.rpow_one]
    have hA_le : A ≤ t ^ ((1 : ℝ) / (n : ℝ)) := h2 ▸ h1
    have hpos_t : 0 < t := by
      rcases lt_or_eq_of_le ht with h | rfl
      · exact h
      · exfalso; exact hle (pow_nonneg hA n)
    have hsum : (1 : ℝ) / (n : ℝ) + ((n - 1 : ℕ) : ℝ) / (n : ℝ) = 1 := by
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
      rw [hcast]; field_simp; ring
    calc A * t ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ))
        ≤ t ^ ((1 : ℝ) / (n : ℝ)) * t ^ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg ht _)
      _ = t ^ ((1 : ℝ) / (n : ℝ) + ((n - 1 : ℕ) : ℝ) / (n : ℝ)) := (Real.rpow_add hpos_t _ _).symm
      _ = t ^ (1 : ℝ) := by rw [hsum]
      _ = t := Real.rpow_one t
      _ ≤ A ^ n + t := by linarith [pow_nonneg hA n]

private lemma three_le_exp_two_sc : (3 : ℝ) ≤ Real.exp 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith
  have hsq : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [sq, ← Real.exp_add]; norm_num
  linarith

public section

/-- **Linear stretch bound from subpolynomial stretch.** Any `impl` with
`impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))` (`0 < C_sp`) satisfies
`⌈impl.γ_ℓ m⌉₊ ≤ gammaLinearConst C_sp * (m + 2)` for every `m`. -/
theorem ceil_gamma_le_linear_of_subpoly {impl : SparsifyImpl} {C_sp : ℝ}
    (hC : 0 < C_sp) (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (m : ℕ) :
    ⌈impl.γ_ℓ m⌉₊ ≤ gammaLinearConst C_sp * (m + 2) := by
  set Z : ℝ := (m : ℝ) + 2
  have hZpos : 0 < Z := by positivity
  have hZ1 : (1 : ℝ) ≤ Z := by dsimp [Z]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have ht_nn : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have h78 : ((8 - 1 : ℕ) : ℝ) / (8 : ℝ) = (7 / 8 : ℝ) := by norm_num
  have harg : C_sp * Real.log Z ^ (7 / 8 : ℝ) ≤ C_sp ^ 8 + Real.log Z := by
    rw [← h78]; exact mul_rpow_le_pow_add (n := 8) (by decide) hC.le ht_nn
  have hbound : impl.γ_ℓ m ≤ ((gammaLinearConst C_sp * (m + 2) : ℕ) : ℝ) := by
    push_cast
    calc impl.γ_ℓ m
        ≤ Real.exp (C_sp * Real.log Z ^ (7 / 8 : ℝ)) := hγ m
      _ ≤ Real.exp (C_sp ^ 8 + Real.log Z) := Real.exp_le_exp.mpr harg
      _ = Real.exp (C_sp ^ 8) * Real.exp (Real.log Z) := Real.exp_add _ _
      _ = Real.exp (C_sp ^ 8) * Z := by rw [Real.exp_log hZpos]
      _ ≤ (gammaLinearConst C_sp : ℝ) * Z :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) hZpos.le
  exact Nat.ceil_le.mpr hbound

/-- **Linear walk-length bound under `chosenL` and subpolynomial stretch.** When
`depth ≤ Expander.chosenL ((M + N) ^ 2)` and `impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))`
(`0 < C_sp`), the dynamic-spanner walk-length bound satisfies
`⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ lenBoundLinearConst C_sp * (M + N + 2)`. -/
theorem ceil_lenBound_le_linear_of_chosenL {impl : SparsifyImpl} {C_sp : ℝ}
    (hC : 0 < C_sp) (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {M N depth : ℕ} (hdepth : depth ≤ Expander.chosenL ((M + N) ^ 2)) :
    ⌈lenBound (impl.γ_ℓ M) depth⌉₊ ≤ lenBoundLinearConst C_sp * (M + N + 2) := by
  set Z : ℝ := ((M + N : ℕ) : ℝ) + 2
  set t : ℝ := Real.log Z
  have hZpos : 0 < Z := by positivity
  have ht_half : (1 / 2 : ℝ) ≤ t := by
    have := half_le_log_add_two_nat (M + N)
    simpa [t, Z] using this
  have ht_pos : 0 < t := by linarith
  have hsq_le : (((M + N) ^ 2 : ℕ) : ℝ) + 2 ≤ Z ^ 2 := by
    dsimp only [Z]; push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N]
  have hlog_sq : Real.log ((((M + N) ^ 2 : ℕ) : ℝ) + 2) ≤ 2 * t := by
    calc Real.log ((((M + N) ^ 2 : ℕ) : ℝ) + 2)
        ≤ Real.log (Z ^ 2) := Real.log_le_log (by positivity) hsq_le
      _ = 2 * Real.log Z := by rw [Real.log_pow]; norm_num
      _ = 2 * t := rfl
  have hlog_sq_nn : 0 ≤ Real.log ((((M + N) ^ 2 : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ((M + N) ^ 2)])
  have h2_124 : (2 : ℝ) ^ (1 / 24 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 24 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hdepth_r : (depth : ℝ) ≤ 6 * t ^ (1 / 24 : ℝ) := by
    calc (depth : ℝ) ≤ (Expander.chosenL ((M + N) ^ 2) : ℝ) := by exact_mod_cast hdepth
      _ ≤ 3 * Real.log ((((M + N) ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) :=
          Expander.chosenL_upper ((M + N) ^ 2)
      _ ≤ 3 * (2 * t) ^ (1 / 24 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_sq_nn hlog_sq (by norm_num)) (by norm_num)
      _ = 3 * ((2 : ℝ) ^ (1 / 24 : ℝ) * t ^ (1 / 24 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) ht_pos.le]
      _ ≤ 3 * (2 * t ^ (1 / 24 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2_124 (Real.rpow_nonneg ht_pos.le _)) (by norm_num)
      _ = 6 * t ^ (1 / 24 : ℝ) := by ring
  have hd1_r : ((depth + 1 : ℕ) : ℝ) ≤ 12 * t ^ (1 / 24 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Expander.chosenL ((M + N) ^ 2) : ℝ) := by
      exact_mod_cast Expander.one_le_chosenL ((M + N) ^ 2)
    have hcl : (Expander.chosenL ((M + N) ^ 2) : ℝ) ≤ 6 * t ^ (1 / 24 : ℝ) := by
      calc (Expander.chosenL ((M + N) ^ 2) : ℝ)
          ≤ 3 * Real.log ((((M + N) ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) :=
            Expander.chosenL_upper ((M + N) ^ 2)
        _ ≤ 3 * (2 * t) ^ (1 / 24 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_sq_nn hlog_sq (by norm_num)) (by norm_num)
        _ = 3 * ((2 : ℝ) ^ (1 / 24 : ℝ) * t ^ (1 / 24 : ℝ)) := by
            rw [Real.mul_rpow (by norm_num) ht_pos.le]
        _ ≤ 3 * (2 * t ^ (1 / 24 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h2_124 (Real.rpow_nonneg ht_pos.le _)) (by norm_num)
        _ = 6 * t ^ (1 / 24 : ℝ) := by ring
    push_cast
    linarith
  have hlogM_le : Real.log ((M : ℝ) + 2) ≤ t := by
    apply Real.log_le_log (by positivity)
    dsimp only [Z]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlogM_nn : 0 ≤ Real.log ((M : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hγM_exp : impl.γ_ℓ M ≤ Real.exp (C_sp * t ^ (7 / 8 : ℝ)) := by
    refine (hγ M).trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlogM_nn hlogM_le (by norm_num)) hC.le
  have h3pow : (3 : ℝ) ^ depth ≤ Real.exp (2 * (depth : ℝ)) := by
    calc (3 : ℝ) ^ depth ≤ (Real.exp 2) ^ depth := pow_le_pow_left₀ (by norm_num) three_le_exp_two_sc _
      _ = Real.exp ((depth : ℝ) * 2) := (Real.exp_nat_mul 2 depth).symm
      _ = Real.exp (2 * (depth : ℝ)) := by ring_nf
  have hγpow : (impl.γ_ℓ M) ^ (depth + 1) ≤
      Real.exp (((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ))) := by
    have hnn : 0 ≤ impl.γ_ℓ M := le_trans (by norm_num) (impl.hγ_ℓ M)
    calc (impl.γ_ℓ M) ^ (depth + 1)
        ≤ (Real.exp (C_sp * t ^ (7 / 8 : ℝ))) ^ (depth + 1) :=
          pow_le_pow_left₀ hnn hγM_exp _
      _ = Real.exp (((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ))) :=
          (Real.exp_nat_mul _ _).symm
  have h124_1112 : t ^ (1 / 24 : ℝ) ≤ 2 * t ^ (11 / 12 : ℝ) :=
    log_rpow_le_two_mul_rpow (a := (1 / 24 : ℝ)) (b := (11 / 12 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (M + N)
  have hprod : t ^ (1 / 24 : ℝ) * t ^ (7 / 8 : ℝ) = t ^ (11 / 12 : ℝ) := by
    rw [← Real.rpow_add ht_pos]; norm_num
  have hexp_arg : 2 * (depth : ℝ) + ((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ)) ≤
      (24 + 12 * C_sp) * t ^ (11 / 12 : ℝ) := by
    have h1 : 2 * (depth : ℝ) ≤ 24 * t ^ (11 / 12 : ℝ) := by linarith
    have h2 : ((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ)) ≤
        12 * C_sp * t ^ (11 / 12 : ℝ) := by
      calc ((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ))
          ≤ (12 * t ^ (1 / 24 : ℝ)) * (C_sp * t ^ (7 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_right hd1_r (by positivity)
        _ = 12 * C_sp * (t ^ (1 / 24 : ℝ) * t ^ (7 / 8 : ℝ)) := by ring
        _ = 12 * C_sp * t ^ (11 / 12 : ℝ) := by rw [hprod]
    linarith
  have h1112 : ((12 - 1 : ℕ) : ℝ) / (12 : ℝ) = (11 / 12 : ℝ) := by norm_num
  have hyoung : (24 + 12 * C_sp) * t ^ (11 / 12 : ℝ) ≤ (24 + 12 * C_sp) ^ 12 + t := by
    rw [← h1112]; exact mul_rpow_le_pow_add (n := 12) (by decide) (by linarith) ht_pos.le
  have hbound : lenBound (impl.γ_ℓ M) depth ≤ ((lenBoundLinearConst C_sp * (M + N + 2) : ℕ) : ℝ) := by
    unfold lenBound
    push_cast
    have hγ_nn : 0 ≤ (impl.γ_ℓ M) ^ (depth + 1) :=
      pow_nonneg (le_trans (by norm_num) (impl.hγ_ℓ M)) _
    calc (3 : ℝ) ^ depth * (impl.γ_ℓ M) ^ (depth + 1)
        ≤ Real.exp (2 * (depth : ℝ)) * Real.exp (((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ))) :=
          mul_le_mul h3pow hγpow hγ_nn (Real.exp_pos _).le
      _ = Real.exp (2 * (depth : ℝ) + ((depth + 1 : ℕ) : ℝ) * (C_sp * t ^ (7 / 8 : ℝ))) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp ((24 + 12 * C_sp) ^ 12 + t) := Real.exp_le_exp.mpr (hexp_arg.trans hyoung)
      _ = Real.exp ((24 + 12 * C_sp) ^ 12) * Real.exp (Real.log Z) := Real.exp_add _ _
      _ = Real.exp ((24 + 12 * C_sp) ^ 12) * Z := by rw [Real.exp_log hZpos]
      _ ≤ (lenBoundLinearConst C_sp : ℝ) * Z :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) hZpos.le
      _ = (lenBoundLinearConst C_sp : ℝ) * ((M : ℝ) + (N : ℝ) + 2) := by
          dsimp only [Z]; push_cast; ring
  exact Nat.ceil_le.mpr hbound

end

end MinCostFlow.SparseCore.Program
