module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.SparseCore.Program.AssemblyReemb

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Polynomial stretch bound and solver-input discharge lemmas (`AssemblyDryRunSCStretch`)

Proves:
* `sparsifyPolyStretch_of_implHyp`: every sparsifier program `impl` satisfying `SparsifyImplHyp impl C_sp`
  (`impl.γ_ℓ m ≤ exp (C_sp * log^{7/8} (m + 2))`) satisfies `SparsifyPolyStretch impl`, using
  `t ^ (7 / 8) ≤ t + 1` for `t ≥ 0` so `exp (C_sp * log^{7/8} x) ≤ exp C_sp * x ^ C_sp`.
* `sparsifyPolyStretch_sparsifyImplUsed`: concrete instance for `sparsifyImplUsed`.
* Solver-input discharge lemmas for the sparse-core bridge (`chosenL_sq_le_four_mul_add_one`,
  `isValidLSFInitFor_mono`, `dryLSFInitUsed_isValidLSFInitFor`).
-/

public section

namespace MinCostFlow.Final.DryRun

open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program

private theorem rpow_le_add_one {t a : ℝ} (ht : 0 ≤ t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    t ^ a ≤ t + 1 := by
  by_cases h1 : t ≤ 1
  · calc t ^ a ≤ 1 ^ a := Real.rpow_le_rpow ht h1 ha0
      _ = 1 := Real.one_rpow a
      _ ≤ t + 1 := by linarith
  · have h1' : 1 < t := not_le.mp h1
    calc t ^ a ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1'.le ha1
      _ = t := Real.rpow_one t
      _ ≤ t + 1 := by linarith

/-- Every sparsifier program satisfying `SparsifyImplHyp impl C_sp` (Theorem 8.1, page 39,
`impl.γ_ℓ m ≤ exp (C_sp * log^{7/8} (m + 2))`) satisfies the polynomial stretch bound
`SparsifyPolyStretch impl` with `Cγ = ⌈exp C_sp⌉₊` and `cγ = ⌈C_sp⌉₊`. -/
theorem sparsifyPolyStretch_of_implHyp {impl : SparsifyImpl} {C_sp : ℝ}
    (h : SparsifyImplHyp impl C_sp) : SparsifyPolyStretch impl := by
  refine ⟨Nat.ceil (Real.exp C_sp), Nat.ceil C_sp, fun m => ?_⟩
  have hCpos : 0 < C_sp := h.1
  have hγm : impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    (h.2.2.2.2 m).1
  set x : ℝ := (m : ℝ) + 2
  have hx1 : (1 : ℝ) ≤ x := by dsimp only [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrpow : Real.log x ^ (7 / 8 : ℝ) ≤ Real.log x + 1 :=
    rpow_le_add_one hlog_nn (by norm_num) (by norm_num)
  have hcγ_ge : C_sp ≤ (Nat.ceil C_sp : ℝ) := Nat.le_ceil C_sp
  have hCγ_ge : Real.exp C_sp ≤ (Nat.ceil (Real.exp C_sp) : ℝ) := Nat.le_ceil (Real.exp C_sp)
  have hexp_arg : C_sp * Real.log x ^ (7 / 8 : ℝ) ≤ C_sp + (Nat.ceil C_sp : ℝ) * Real.log x := by
    have h1 : C_sp * Real.log x ^ (7 / 8 : ℝ) ≤ C_sp * (Real.log x + 1) :=
      mul_le_mul_of_nonneg_left hrpow hCpos.le
    have h2 : C_sp * Real.log x ≤ (Nat.ceil C_sp : ℝ) * Real.log x :=
      mul_le_mul_of_nonneg_right hcγ_ge hlog_nn
    linarith
  have hbound : impl.γ_ℓ m ≤ ((Nat.ceil (Real.exp C_sp) * (m + 2) ^ Nat.ceil C_sp : ℕ) : ℝ) := by
    push_cast
    calc impl.γ_ℓ m
        ≤ Real.exp (C_sp * Real.log x ^ (7 / 8 : ℝ)) := hγm
      _ ≤ Real.exp (C_sp + (Nat.ceil C_sp : ℝ) * Real.log x) := Real.exp_le_exp.mpr hexp_arg
      _ = Real.exp C_sp * Real.exp (Real.log x * (Nat.ceil C_sp : ℝ)) := by
          rw [Real.exp_add, mul_comm (Nat.ceil C_sp : ℝ) (Real.log x)]
      _ = Real.exp C_sp * x ^ (Nat.ceil C_sp : ℝ) := by rw [← Real.rpow_def_of_pos hxpos]
      _ = Real.exp C_sp * x ^ Nat.ceil C_sp := by rw [Real.rpow_natCast]
      _ ≤ (Nat.ceil (Real.exp C_sp) : ℝ) * x ^ Nat.ceil C_sp :=
          mul_le_mul_of_nonneg_right hCγ_ge (by positivity)
  exact Nat.ceil_le.mpr hbound

/-- The library's concrete sparsifier program `sparsifyImplUsed` satisfies `SparsifyPolyStretch`. -/
theorem sparsifyPolyStretch_sparsifyImplUsed : SparsifyPolyStretch sparsifyImplUsed :=
  sparsifyPolyStretch_of_implHyp dryImplHyp

/-- The balancing depth `chosenL (M₀ ^ 2)` is at most `4 * M₀ + 1` for every `1 ≤ M₀`
(hence at most `M + N + k + L` whenever `4 * M₀ ≤ N` and `1 ≤ k`). -/
theorem chosenL_sq_le_four_mul_add_one {M₀ : ℕ} (hM : 1 ≤ M₀) :
    Expander.chosenL (M₀ ^ 2) ≤ 4 * M₀ + 1 := by
  unfold Expander.chosenL
  apply Nat.ceil_le.mpr
  have hM1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM
  have hsq : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by
    push_cast; nlinarith
  have hlog_nn : 0 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (M₀ ^ 2)])
  have hlog_le : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ 2 * ((M₀ : ℝ) + 1) := by
    calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2)
        ≤ Real.log (((M₀ : ℝ) + 2) ^ 2) := Real.log_le_log (by positivity) hsq
      _ = 2 * Real.log ((M₀ : ℝ) + 2) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * (((M₀ : ℝ) + 2) - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) (by norm_num)
      _ = 2 * ((M₀ : ℝ) + 1) := by ring
  have hrpow := rpow_le_add_one hlog_nn (a := (1 / 24 : ℝ)) (by norm_num) (by norm_num)
  push_cast at hlog_le hrpow ⊢
  linarith

/-- The balancing depth `chosenL (M₀ ^ 2)` is at most `bundleLogFactor M N` whenever `1 ≤ M₀`
and `4 * M₀ ≤ N`. -/
theorem chosenL_sq_le_bundleLogFactor {M₀ M N : ℕ} (hM : 1 ≤ M₀) (hN : 4 * M₀ ≤ N) :
    Expander.chosenL (M₀ ^ 2) ≤ bundleLogFactor M N := by
  unfold Expander.chosenL bundleLogFactor
  apply Nat.ceil_le.mpr
  set b : ℕ := Nat.log 2 (M + N + 2) + 1
  have hb3 : 3 ≤ b := by
    have h6 : 2 ^ 2 ≤ M + N + 2 := by omega
    have hlog2 : 2 ≤ Nat.log 2 (M + N + 2) := Nat.le_log_of_pow_le (by norm_num) h6
    omega
  have hlt_pow : M + N + 2 < 2 ^ b := Nat.lt_pow_succ_log_self (by norm_num) (M + N + 2)
  have hsq_nat : M₀ ^ 2 + 2 ≤ (M + N + 2) ^ 2 := by nlinarith
  have hsq_pow : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ (2 * b) := by
    have hnat : M₀ ^ 2 + 2 ≤ 2 ^ (2 * b) :=
      hsq_nat.trans <| (Nat.pow_le_pow_left hlt_pow.le 2).trans_eq (by rw [← pow_mul, mul_comm])
    exact_mod_cast hnat
  have hlog_nn : 0 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (M₀ ^ 2)])
  have hlog_le : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ 2 * (b : ℝ) := by
    have h2b : Real.log ((2 : ℝ) ^ (2 * b)) = (2 * b : ℕ) * Real.log 2 := by
      rw [Real.log_pow]
    have hlog2_le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2)
        ≤ Real.log ((2 : ℝ) ^ (2 * b)) := Real.log_le_log (by positivity) hsq_pow
      _ = (2 * b : ℕ) * Real.log 2 := h2b
      _ ≤ (2 * b : ℕ) * 1 := mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg _)
      _ = 2 * (b : ℝ) := by push_cast; ring
  have hrpow := rpow_le_add_one hlog_nn (a := (1 / 24 : ℝ)) (by norm_num) (by norm_num)
  have hquad : 2 * b + 1 ≤ b ^ 2 := by nlinarith
  have hquadR : 2 * (b : ℝ) + 1 ≤ ((b ^ 2 : ℕ) : ℝ) := by exact_mod_cast hquad
  linarith

/-- `IsValidLSFInitFor` is monotone in the stretch constant `C_lsst`. -/
theorem isValidLSFInitFor_mono {lsfInit : LSFInit} {C₁ C₂ : ℝ} {k j : ℕ}
    (h : IsValidLSFInitFor lsfInit C₁ k j) (hle : C₁ ≤ C₂) :
    IsValidLSFInitFor lsfInit C₂ k j := by
  intro G₀ ℓ₀ hG₀ hV₀ hℓ₀ hk
  have h1 := h G₀ ℓ₀ hG₀ hV₀ hℓ₀ hk
  have hK : mwuK0 C₁ ≤ mwuK0 C₂ := by
    unfold mwuK0
    exact mul_le_mul_of_nonneg_left (max_le_max_left 1 hle) (by norm_num)
  exact ⟨lsfInvAny_of_with (lsfInvWith_mono_K h1.1 hK), h1.2⟩

/-- Every format member of `dryLSFInitUsed` satisfies `IsValidLSFInitFor` at `dryCLsstUsed` for
every branch `j < k`. -/
theorem dryLSFInitUsed_isValidLSFInitFor (L_in P_fp k j : ℕ) (hj : j < k) :
    IsValidLSFInitFor (dryLSFInitUsed L_in P_fp) dryCLsstUsed k j := by
  obtain ⟨hKρ, hApprox⟩ := dryKρ_spec SparseCore.Program.canonicalLSFInit
    SparseCore.Program.canonicalLSFInit_spec
  have hval := (hApprox L_in P_fp).toValidLSFInitFor hj
  refine isValidLSFInitFor_mono hval ?_
  unfold dryCLsstUsed dryCLsst
  have hKσ_nn : (0 : ℝ) ≤ (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ) :=
    Nat.cast_nonneg _
  have hC₀_le : 4 * max anK 1 + 5 ≤
      3 * dryKρ SparseCore.Program.canonicalLSFInit SparseCore.Program.canonicalLSFInit_spec *
        max (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ)
          (max (112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5)) 2240) := by
    have h1 : 4 * max anK 1 + 5 ≤ max 1 (4 * max anK 1 + 5) := le_max_right _ _
    have h2 : max 1 (4 * max anK 1 + 5) ≤ 112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5) := by
      have : (0 : ℝ) ≤ max 1 (4 * max anK 1 + 5) := by positivity
      nlinarith
    have h3 : 112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5) ≤
        max (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ)
          (max (112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5)) 2240) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have h4 : (0 : ℝ) ≤ max (MinCostFlow.LSF.Program.defaultK_sigma anK : ℝ)
        (max (112 * (1 + 5 / 4) * max 1 (4 * max anK 1 + 5)) 2240) := by positivity
    nlinarith
  exact max_le (le_trans hC₀_le (le_max_right _ _))
    (le_trans (by linarith) (le_max_left _ _))

end MinCostFlow.Final.DryRun
