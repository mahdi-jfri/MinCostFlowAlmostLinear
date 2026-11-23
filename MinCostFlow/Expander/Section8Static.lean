module

public import MinCostFlow.Spanner.MGraphSpec
public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.ExpanderDecomp.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import MinCostFlow.Expander.PathDS
import MinCostFlow.Expander.SpannerTools
import MinCostFlow.ExpanderDecomp.SwapBridge
import MinCostFlow.Expander.PathDSProg.ParamsConsumerBounds
import MinCostFlow.Spanner.Runtime
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Static Sparsifier Parameters for Theorem 8.1

Instantiates Algorithm 4 (`Spanner.sparsifyMG`, `Theorem 8.1`) on `MGraph` from the case of the
expander decomposition that the paper uses (`ExpanderDecomp.ExpanderDecompositionUsed`), the cited
`Cited.DecrementalExpanderPaths` and the explicit expander
`MinCostFlow.ExplicitExpander.explicitExpander : Cited.ExplicitExpander`, via
`ExpanderDecomp.exists_spannerTools_of_used`, `theorem_8_1` (inside
`theorem_8_1_at_cap_of_dec_le`), and `sparsifyMG_spec_of_dec_le`. The wrappers
`theorem_8_1_concrete` and `theorem_8_1_concrete_with_time` take the cited
`Cited.ExpanderDecomposition` and pass its used case
(`ExpanderDecomp.ExpanderDecompositionUsed.of_cited`).

* `Section8Static.lean` constructs `sparsify := sparsifyMG tools costs` and
  `params mMax := sparsifyMGParamsOfDec tools costs (φ mMax) _ mMax C_dec _` satisfying
  `DynSpanner.SparsifySpec mMax (params mMax) sparsify` for every `mMax : ℕ`, with explicit
  exponent `7 / 8` (`γ_ℓ, γ_c ≤ exp(C_γ * log(mMax + 2) ^ (7 / 8))`) and mMax-independent
  constants `K_s = 1 + 36 / Real.log 2`, `p_s = 1`, explicit `K_t`, and `p_t = 1`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.DynSpanner

public section

/-- Lower bound `1 / 2 ≤ log((M : ℝ) + 2)` for every `M : ℕ`. -/
lemma half_le_log_add_two_nat (M : ℕ) : (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hpow : Real.exp (1 / 2 : ℝ) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [hsq]
      linarith
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hM : (2 : ℝ) ≤ (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have h1 : Real.exp (1 / 2 : ℝ) ≤ (M : ℝ) + 2 := le_trans hexp_half hM
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at h2

/-- Uniform lower bound `1 / 2 ≤ (log((M : ℝ) + 2)) ^ a` for `0 ≤ a ≤ 1`. -/
lemma half_le_log_rpow_nat {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (M : ℕ) :
    (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) ^ a := by
  have hL := half_le_log_add_two_nat M
  by_cases h1 : 1 ≤ Real.log ((M : ℝ) + 2)
  · have := Real.one_le_rpow h1 ha0
    linarith
  · have hlt : Real.log ((M : ℝ) + 2) ≤ 1 := le_of_not_ge h1
    have hpow1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ a :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha1
    have hpow2 : (1 / 2 : ℝ) ^ a ≤ Real.log ((M : ℝ) + 2) ^ a :=
      Real.rpow_le_rpow (by norm_num) hL ha0
    simpa using le_trans hpow1 hpow2

/-- Absorb any nonnegative constant `K` into `exp(2 * K * log((M : ℝ) + 2) ^ a)` for `0 ≤ a ≤ 1`. -/
lemma nonneg_const_le_exp_rpow {K a : ℝ} (hK : 0 ≤ K) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (M : ℕ) :
    K ≤ Real.exp (2 * K * Real.log ((M : ℝ) + 2) ^ a) := by
  have hK_exp : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hhalf := half_le_log_rpow_nat ha0 ha1 M
  have harg : K ≤ 2 * K * Real.log ((M : ℝ) + 2) ^ a := by
    calc K = K * 1 := by ring
      _ ≤ K * (2 * Real.log ((M : ℝ) + 2) ^ a) := by gcongr; linarith
      _ = 2 * K * Real.log ((M : ℝ) + 2) ^ a := by ring
  exact le_trans hK_exp (Real.exp_le_exp.mpr harg)

/-- Subexponential comparison `x ≤ 2 * exp(x ^ a)` for all `x ≥ 0` and `1 / 2 ≤ a`. -/
lemma self_le_two_mul_exp_rpow {x a : ℝ} (hx : 0 ≤ x) (ha : 1 / 2 ≤ a) :
    x ≤ 2 * Real.exp (x ^ a) := by
  by_cases hx1 : x ≤ 1
  · have hexp1 : (1 : ℝ) ≤ Real.exp (x ^ a) := Real.one_le_exp (Real.rpow_nonneg hx a)
    linarith
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have h1_le_2a : (1 : ℝ) ≤ 2 * a := by linarith
    have hx_le : x ≤ x ^ (2 * a) := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (2 * a) := Real.rpow_le_rpow_of_exponent_le hx1' h1_le_2a
    have hpow2 : x ^ (2 * a) = (x ^ a) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hx]
      norm_num
    have htaylor : (x ^ a) ^ 2 / ((Nat.factorial 2 : ℕ) : ℝ) ≤ Real.exp (x ^ a) :=
      Real.pow_div_factorial_le_exp (x ^ a) (Real.rpow_nonneg hx a) 2
    have hfac2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hfac2] at htaylor
    have hsq : (x ^ a) ^ 2 ≤ 2 * Real.exp (x ^ a) := by linarith
    linarith

/-- Absorb `log((M : ℝ) + 2)` into `exp(3 * log((M : ℝ) + 2) ^ a)` when `1 / 2 ≤ a ≤ 1`. -/
lemma log_add_two_le_exp_rpow {a : ℝ} (ha0 : 1 / 2 ≤ a) (ha1 : a ≤ 1) (M : ℕ) :
    Real.log ((M : ℝ) + 2) ≤ Real.exp (3 * Real.log ((M : ℝ) + 2) ^ a) := by
  have hL := half_le_log_add_two_nat M
  have hself := self_le_two_mul_exp_rpow (by linarith) ha0
  have hhalf := half_le_log_rpow_nat (by linarith) ha1 M
  have h2_exp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1_arg : (1 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) ^ a := by linarith
  have h2_le : (2 : ℝ) ≤ Real.exp (2 * Real.log ((M : ℝ) + 2) ^ a) :=
    le_trans h2_exp (Real.exp_le_exp.mpr h1_arg)
  calc Real.log ((M : ℝ) + 2)
      ≤ 2 * Real.exp (Real.log ((M : ℝ) + 2) ^ a) := hself
    _ ≤ Real.exp (2 * Real.log ((M : ℝ) + 2) ^ a) * Real.exp (Real.log ((M : ℝ) + 2) ^ a) := by
        gcongr
    _ = Real.exp (3 * Real.log ((M : ℝ) + 2) ^ a) := by
        rw [← Real.exp_add]
        ring_nf

/-- Compare powers of `log((M : ℝ) + 2)`: `L ^ a ≤ 2 * L ^ b` for `0 ≤ a ≤ b ≤ 1`. -/
lemma log_rpow_le_two_mul_rpow {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (M : ℕ) :
    Real.log ((M : ℝ) + 2) ^ a ≤ 2 * Real.log ((M : ℝ) + 2) ^ b := by
  have hL := half_le_log_add_two_nat M
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have hhalf := half_le_log_rpow_nat hb0 hb1 M
  by_cases h1 : 1 ≤ Real.log ((M : ℝ) + 2)
  · have hle := Real.rpow_le_rpow_of_exponent_le h1 hab
    have hnn : 0 ≤ Real.log ((M : ℝ) + 2) ^ b := Real.rpow_nonneg (by linarith) b
    linarith
  · have hlt : Real.log ((M : ℝ) + 2) ≤ 1 := le_of_not_ge h1
    have hle1 : Real.log ((M : ℝ) + 2) ^ a ≤ 1 := Real.rpow_le_one (by linarith) hlt ha0
    linarith

end

section Helpers

private lemma natLog2_le_two_log_add_two (k : ℕ) :
    (Nat.log 2 k : ℝ) ≤ 2 * Real.log ((k : ℝ) + 2) := by
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.log_zero_right, CharP.cast_eq_zero, zero_add]
    have hL := half_le_log_add_two_nat 0
    simp only [Nat.cast_zero, zero_add] at hL
    linarith
  · have hpow : (2 : ℝ) ^ (Nat.log 2 k) ≤ (k : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hk2 : (k : ℝ) ≤ (k : ℝ) + 2 := by linarith
    have hlog : (Nat.log 2 k : ℝ) * Real.log 2 ≤ Real.log ((k : ℝ) + 2) := by
      calc (Nat.log 2 k : ℝ) * Real.log 2
          = Real.log ((2 : ℝ) ^ (Nat.log 2 k)) := (Real.log_pow 2 (Nat.log 2 k)).symm
        _ ≤ Real.log (k : ℝ) := Real.log_le_log (by positivity) hpow
        _ ≤ Real.log ((k : ℝ) + 2) := Real.log_le_log hk_pos hk2
    have hl2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      simpa using half_le_log_add_two_nat 0
    have hl2_pos : 0 < Real.log 2 := by linarith
    have h1 : (Nat.log 2 k : ℝ) ≤ Real.log ((k : ℝ) + 2) / Real.log 2 :=
      (le_div_iff₀ hl2_pos).mpr hlog
    have hL_nn : 0 ≤ Real.log ((k : ℝ) + 2) := by linarith [half_le_log_add_two_nat k]
    have h2 : Real.log ((k : ℝ) + 2) / Real.log 2 ≤ Real.log ((k : ℝ) + 2) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left hL_nn (by norm_num) hl2_half
    linarith

private lemma decFactor_ge_one {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (m : ℕ) :
    1 ≤ Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
  have h1 : 0 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h2 : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) :=
    Real.log_nonneg (by linarith)
  have harg : 0 ≤ C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m : ℝ) + 2) + 2) := by positivity
  exact Real.one_le_exp harg

private lemma decFactor_mono {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    Real.exp (C₀ * Real.log ((m₁ : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m₁ : ℝ) + 2) + 2)) ≤
    Real.exp (C₀ * Real.log ((m₂ : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m₂ : ℝ) + 2) + 2)) := by
  apply Real.exp_le_exp.mpr
  have hm_r : (m₁ : ℝ) + 2 ≤ (m₂ : ℝ) + 2 := by
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm1_pos : (0 : ℝ) < (m₁ : ℝ) + 2 := by positivity
  have hlog_le : Real.log ((m₁ : ℝ) + 2) ≤ Real.log ((m₂ : ℝ) + 2) :=
    Real.log_le_log hm1_pos hm_r
  have hlog1_nn : 0 ≤ Real.log ((m₁ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m₁])
  have hrpow : Real.log ((m₁ : ℝ) + 2) ^ (2 / 3 : ℝ) ≤ Real.log ((m₂ : ℝ) + 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlog1_nn hlog_le (by positivity)
  have hloglog : Real.log (Real.log ((m₁ : ℝ) + 2) + 2) ≤ Real.log (Real.log ((m₂ : ℝ) + 2) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hll1_nn : 0 ≤ Real.log (Real.log ((m₁ : ℝ) + 2) + 2) :=
    Real.log_nonneg (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hrpow hC₀) hloglog hll1_nn
    (mul_nonneg hC₀ (Real.rpow_nonneg (le_trans hlog1_nn hlog_le) _))

private lemma pathDS_gamma_mono_from_exp_tools {pds : Spanner.PathDSTool}
    (hφ_mono : ∀ φ₁ φ₂ M, φ₁ ≤ φ₂ → pds.φ_out φ₁ M ≤ pds.φ_out φ₂ M)
    (hφ_antiM : ∀ φ_in M₁ M₂, M₁ ≤ M₂ → pds.φ_out φ_in M₂ ≤ pds.φ_out φ_in M₁)
    (hγ_anti : ∀ φ₁ φ₂ M, 0 < φ₁ → φ₁ ≤ φ₂ → pds.γ_ExpPath φ₂ M ≤ pds.γ_ExpPath φ₁ M)
    (hγ_monoM : ∀ φ_in M₁ M₂, 0 < φ_in → M₁ ≤ M₂ → pds.γ_ExpPath φ_in M₁ ≤ pds.γ_ExpPath φ_in M₂)
    (hq_anti : ∀ φ₁ φ₂ M, 0 < φ₁ → φ₁ ≤ φ₂ → pds.γ_query φ₂ M ≤ pds.γ_query φ₁ M)
    (hq_monoM : ∀ φ_in M₁ M₂, 0 < φ_in → M₁ ≤ M₂ → pds.γ_query φ_in M₁ ≤ pds.γ_query φ_in M₂)
    {C_del : ℝ} (hγ_del_eq : ∀ φ_in M, pds.γ_del φ_in M = C_del) :
    Spanner.PathDSMonotone pds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ₁ φ₂ M₁ M₂ _ hφ _ hM
    exact le_trans (hφ_antiM φ₁ M₁ M₂ hM) (hφ_mono φ₁ φ₂ M₁ hφ)
  · intro φ₁ φ₂ M₁ M₂ hφ₁ hφ _ hM
    exact le_trans (hγ_monoM φ₂ M₁ M₂ (lt_of_lt_of_le hφ₁ hφ) hM) (hγ_anti φ₁ φ₂ M₂ hφ₁ hφ)
  · intro φ₁ φ₂ M₁ M₂ hφ₁ hφ _ hM
    exact le_trans (hq_monoM φ₂ M₁ M₂ (lt_of_lt_of_le hφ₁ hφ) hM) (hq_anti φ₁ φ₂ M₂ hφ₁ hφ)
  · intro φ₁ φ₂ M₁ M₂ _ _ _ _
    rw [hγ_del_eq, hγ_del_eq]

/-- The time factor `capGammaQuery` of a path data structure whose query bound is
`γ_ExpPath + fbCostBound ⌈1 / φ⌉` is at most `exp(C_q · log^{8/9}(M + 2) · log(log(M + 2) + 2)^{4/3})`
on the clusters of `Decompose`, once `capGammaExpPath ≤ exp(C_W · log^{7/8}(M + 2))`. -/
private lemma capGammaQuery_le_exp_eight_ninths {pds : Spanner.PathDSTool} {c_deg φ_C C₀ C₁ C_W : ℝ}
    {φ : ℕ → ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCW_nn : 0 ≤ C_W) (hφC_pos : 0 < φ_C)
    (hγq : ∀ φ_in M, pds.γ_query φ_in M = pds.γ_ExpPath φ_in M +
      (PathDSProg.fbCostBound (Nat.ceil (1 / φ_in)) : ℝ))
    (hφ_pos : ∀ m, 0 < φ m)
    (hφ_bd : ∀ m : ℕ, 1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m : ℝ) + 2) + 2))) :
    ∃ C_q : ℝ, 0 < C_q ∧ ∀ mMax : ℕ,
      Spanner.capGammaExpPath c_deg φ_C pds (φ mMax) mMax ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) →
      Spanner.capGammaQuery c_deg φ_C pds (φ mMax) mMax ≤
        Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) := by
  let C₁' : ℝ := C₁ + (Nat.ceil (1 / φ_C) : ℝ)
  have hC₁' : 0 < C₁' := by positivity
  obtain ⟨C_fb, hCfb, hfb⟩ := PathDSProg.fbCostBound_le_exp_eight_ninths C₀ C₁' hC₀ hC₁'
  refine ⟨8 * C_W + C_fb + 10, by positivity, fun mMax hE_bd => ?_⟩
  set L : ℝ := Real.log ((mMax : ℝ) + 2) with hL_def
  set S : ℝ := L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) with hS_def
  have hL_half : (1 / 2 : ℝ) ≤ L := half_le_log_add_two_nat mMax
  have hLL_half : (1 / 2 : ℝ) ≤ Real.log (L + 2) := by
    have h2 : Real.log 2 ≤ Real.log (L + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hS_ge := (PathDSProg.real_E_lower_and_L23 hL_half hLL_half).1
  have hS_nn : 0 ≤ S := by linarith
  have h78 := PathDSProg.rpow_seven_eighths_le_eight_ninths_loglog L hL_half
  have hExp_S : Real.exp (C_W * L ^ (7 / 8 : ℝ)) ≤ Real.exp ((8 * C_W + C_fb) * S) := by
    apply Real.exp_le_exp.mpr
    have : C_W * L ^ (7 / 8 : ℝ) ≤ C_W * (8 * S) := by
      apply mul_le_mul_of_nonneg_left _ hCW_nn
      rw [hS_def]; linarith
    nlinarith
  have hFb_S : Real.exp (C_fb * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ)) ≤
      Real.exp ((8 * C_W + C_fb) * S) := by
    apply Real.exp_le_exp.mpr
    rw [hS_def, mul_assoc]
    nlinarith
  have hexp_pos : 0 ≤ C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by
    have : 0 ≤ Real.log (L + 2) := by linarith
    have : 0 ≤ L ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hexp1 : (1 : ℝ) ≤ Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) :=
    Real.one_le_exp hexp_pos
  have hd_fb : ∀ φ' : ℝ, 0 < φ' → (Nat.ceil (1 / φ') : ℝ) ≤
      C₁' * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) + 1 →
      (PathDSProg.fbCostBound (Nat.ceil (1 / φ')) : ℝ) ≤ Real.exp ((8 * C_W + C_fb) * S) := by
    intro φ' hφ' hd
    have h1 : 1 ≤ Nat.ceil (1 / φ') := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ')
    exact le_trans (hfb mMax _ h1 hd) hFb_S
  have hφm_pos : 0 < φ mMax := hφ_pos mMax
  have hb : 1 / φ mMax ≤ C₁ * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) :=
    hφ_bd mMax
  have hc : (Nat.ceil (1 / φ mMax) : ℝ) < 1 / φ mMax + 1 :=
    Nat.ceil_lt_add_one (div_pos one_pos hφm_pos).le
  have hC1le : C₁ * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) ≤
      C₁' * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hd1 : (Nat.ceil (1 / φ mMax) : ℝ) ≤
      C₁' * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) + 1 := by
    linarith
  have hfb1 := hd_fb (φ mMax) hφm_pos hd1
  have hle2 : (Nat.ceil (1 / φ_C) : ℝ) ≤ C₁' :=
    le_add_of_nonneg_left hC₁.le
  have hC1'exp : C₁' ≤ C₁' * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) :=
    le_mul_of_one_le_right hC₁'.le hexp1
  have hd2 : (Nat.ceil (1 / φ_C) : ℝ) ≤
      C₁' * Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) + 1 := by
    linarith
  have hfb2 := hd_fb φ_C hφC_pos hd2
  have hE1 : pds.γ_ExpPath (φ mMax) mMax ≤ Real.exp ((8 * C_W + C_fb) * S) :=
    le_trans (le_trans (le_max_left _ _) hE_bd) hExp_S
  have hE2 : pds.γ_ExpPath φ_C
        (Spanner.capM_W c_deg (φ mMax) mMax) ≤
      Real.exp ((8 * C_W + C_fb) * S) :=
    le_trans (le_trans (le_max_right _ _) hE_bd) hExp_S
  have h2 : (2 : ℝ) ≤ Real.exp (10 * S) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    exact le_trans h1 (Real.exp_le_exp.mpr (by linarith))
  have hsum : ∀ x y : ℝ, x ≤ Real.exp ((8 * C_W + C_fb) * S) →
      y ≤ Real.exp ((8 * C_W + C_fb) * S) → x + y ≤ Real.exp ((8 * C_W + C_fb + 10) * S) := by
    intro x y hx hy
    have hq : Real.exp ((8 * C_W + C_fb + 10) * S) = Real.exp (10 * S) * Real.exp ((8 * C_W + C_fb) * S) := by
      rw [← Real.exp_add]; ring_nf
    rw [hq]
    nlinarith [Real.exp_pos ((8 * C_W + C_fb) * S)]
  have hgoal_eq : (8 * C_W + C_fb + 10) * L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) = (8 * C_W + C_fb + 10) * S := by
    rw [hS_def]; ring
  rw [hgoal_eq]
  unfold Spanner.capGammaQuery
  rw [hγq, hγq]
  exact max_le (hsum _ _ hE1 hfb1) (hsum _ _ hE2 hfb2)

end Helpers

public section

/-- **Concrete Static Sparsifier (Theorem 8.1, page 39)**:
From the case of the expander decomposition that the paper uses (`ExpanderDecompositionUsed`,
proved as `ExpanderDecomp.expanderDecompositionUsed_holds`), the cited `DecrementalExpanderPaths`
and the explicit expander `MinCostFlow.ExplicitExpander.explicitExpander`, constructs
`sparsify := sparsifyMG tools costs` and `params : ℕ → DynSpanner.SparsifyParams` via `exists_spannerTools_of_used`, `theorem_8_1`
(`theorem_8_1_at_cap_of_dec_le`), and `sparsifyMG_spec_of_dec_le`, proving for every `mMax : ℕ`:
* `DynSpanner.SparsifySpec mMax (params mMax) sparsify`,
* `γ_ℓ, γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))` for an explicit `C_γ > 0`, and
* `mMax`-independent explicit constants `K_s = 1 + 36 / Real.log 2`, `p_s = 1`, `K_t ≥ 0`, `p_t = 1`. -/
theorem theorem_8_1_concrete_both
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify sparsify_t : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params params_t : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      (∀ mMax : ℕ,
        (params_t mMax).K_s = K_s ∧
        (params_t mMax).p_s = 1 ∧
        (params_t mMax).K_t = K_t ∧
        (params_t mMax).p_t = 1 ∧
        (params_t mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params_t mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params_t mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params_t mMax) sparsify_t) := by
  classical
  rcases ExpanderDecomp.exists_spannerTools_of_used hDec hPaths with
    ⟨tools, φ, C₀, C₁, C_cost, K_run, C_p, C_tot, C_lin, C_q, C_k,
      Kγ, c, cw, K_cs, mk, R,
      hc_deg, hφC_pos, _, hc_ℓ, hC₀, hC₁, hCc, hKr,
      hKγ, hc20, hCp, hCtot, hClin, hCq, hCk,
      hφ_spec, hφ_anti, hφ_dec_eq, _,
      hφ_mono, hφ_antiM, hγ_anti, hγ_monoM, hγ_del_eq, hγ_del_ge,
      _, hdom_dec, hdom_phi, hreg_phi, hreg_const, _, _, _, hγq⟩
  let decFactor : ℕ → ℝ := fun m =>
    Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m : ℝ) + 2) + 2))
  let costs : Spanner.SpannerToolCosts :=
    { constructExpander := ⟨2 * K_run, by linarith⟩
      decompose := ⟨C_cost, decFactor, hCc.le,
        fun m => decFactor_ge_one hC₀.le m, fun _ _ hm => decFactor_mono hC₀.le hm⟩
      pathDS := ⟨max C_lin 1, max C_k 1, by positivity, by positivity⟩ }
  let hdec_mono : Spanner.DecomposeMonotone tools.decompose :=
    { φ_lb := φ
      hφ_lb_pos := fun m => (hφ_spec m).1
      hφ_lb_le := fun m => (hφ_spec m).2.1
      hφ_lb_anti := fun _ _ hm => hφ_anti _ _ hm
      hφ_dec_ge := fun G _ _ => by rw [hφ_dec_eq G] }
  have hq_anti : ∀ φ₁ φ₂ M, 0 < φ₁ → φ₁ ≤ φ₂ →
      tools.pathDS.γ_query φ₂ M ≤ tools.pathDS.γ_query φ₁ M := by
    intro φ₁ φ₂ M h1 h12
    rw [hγq, hγq]
    have hfb : PathDSProg.fbCostBound (Nat.ceil (1 / φ₂)) ≤ PathDSProg.fbCostBound (Nat.ceil (1 / φ₁)) :=
      PathDSProg.fbCostBound_mono (Nat.ceil_mono (one_div_le_one_div_of_le h1 h12))
    have hfbR : (PathDSProg.fbCostBound (Nat.ceil (1 / φ₂)) : ℝ) ≤
        (PathDSProg.fbCostBound (Nat.ceil (1 / φ₁)) : ℝ) := by exact_mod_cast hfb
    linarith [hγ_anti φ₁ φ₂ M h1 h12]
  have hq_monoM : ∀ φ_in M₁ M₂, 0 < φ_in → M₁ ≤ M₂ →
      tools.pathDS.γ_query φ_in M₁ ≤ tools.pathDS.γ_query φ_in M₂ := by
    intro φ_in M₁ M₂ hφ hM
    rw [hγq, hγq]
    linarith [hγ_monoM φ_in M₁ M₂ hφ hM]
  have hpds_mono : Spanner.PathDSMonotone tools.pathDS :=
    pathDS_gamma_mono_from_exp_tools hφ_mono hφ_antiM hγ_anti hγ_monoM hq_anti hq_monoM hγ_del_eq
  let pdsE : Spanner.PathDSTool :=
    { tools.pathDS with γ_query := tools.pathDS.γ_ExpPath, hγ_query_ge := fun _ _ _ => le_rfl }
  let toolsE : Spanner.SpannerTools := { tools with pathDS := pdsE }
  have hpdsE_mono : Spanner.PathDSMonotone toolsE.pathDS :=
    pathDS_gamma_mono_from_exp_tools (pds := pdsE) hφ_mono hφ_antiM hγ_anti hγ_monoM hγ_anti
      hγ_monoM hγ_del_eq
  let C_dec : ℝ := 1 / (10 * C₁)
  have hCdec_nn : 0 ≤ C_dec := by positivity
  let sparsify := Spanner.sparsifyMG toolsE costs
  let sparsify_t := Spanner.sparsifyMG tools costs
  let params : ℕ → DynSpanner.SparsifyParams := fun mMax =>
    Spanner.sparsifyMGParamsOfDec tools costs (φ mMax) (hφ_spec mMax).1 mMax C_dec hCdec_nn
  let C_W : ℝ := C_p * (81 + 2 * C_p) ^ (7 / 8 : ℝ)
  have hCW_ge : C_p ≤ C_W := by
    have hbase : (1 : ℝ) ≤ 81 + 2 * C_p := by linarith
    have hr : (1 : ℝ) ≤ (81 + 2 * C_p) ^ (7 / 8 : ℝ) := Real.one_le_rpow hbase (by norm_num)
    calc C_p = C_p * 1 := by ring
      _ ≤ C_p * (81 + 2 * C_p) ^ (7 / 8 : ℝ) := by gcongr
  let C_del : ℝ := csGammaDel K_cs
  let C_poly : ℝ := 2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2 + 1
  have hCpoly_nn : 0 ≤ C_poly := by positivity
  let C_γ : ℝ := 4 * C_W + 6 + 2 * C_poly
  have hCγ_pos : 0 < C_γ := by positivity
  have hCW_le_Cγ : C_W ≤ C_γ := by
    have hW_nn : 0 ≤ C_W := by positivity
    dsimp only [C_γ]; linarith
  have hMW_caps : ∀ mMax : ℕ,
      let M_W := Spanner.capM_W 36 (φ mMax) mMax
      1 / φ mMax ≤ Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      Real.log ((M_W : ℝ) + 2) ≤ (81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2) ∧
      Spanner.capGammaExpPath tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      1 / Spanner.capPhiDS tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
    intro mMax M_W
    have hregM := hreg_phi mMax mMax le_rfl
    have hc1 : 1 ≤ c := by omega
    have hcsPhi_pos : 0 < Cited.csPhi Kγ c (3 * mMax) := by
      unfold Cited.csPhi Cited.csGamma
      have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
      positivity
    have h10 := hdom_phi mMax
    have hcsPhi_le_phi : Cited.csPhi Kγ c (3 * mMax) ≤ φ mMax := by linarith
    have hinv_phi : 1 / φ mMax ≤ Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      have h1 : 1 / φ mMax ≤ 1 / Cited.csPhi Kγ c (3 * mMax) :=
        one_div_le_one_div_of_le hcsPhi_pos hcsPhi_le_phi
      rw [← hregM.1] at h1
      exact le_trans h1 hregM.2.2
    have hL_half := half_le_log_add_two_nat mMax
    have hL_pos : 0 < Real.log ((mMax : ℝ) + 2) := by linarith
    have hlog_MW : Real.log ((M_W : ℝ) + 2) ≤ (81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2) := by
      have hm_nn : 0 ≤ 36 * (mMax : ℝ) / φ mMax := div_nonneg (by positivity) (hφ_spec mMax).1.le
      have hceil : (Nat.ceil (36 * (mMax : ℝ) / φ mMax) : ℝ) < 36 * (mMax : ℝ) / φ mMax + 1 :=
        Nat.ceil_lt_add_one hm_nn
      have hm_exp : 1 ≤ Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
        Real.one_le_exp (mul_nonneg hCp.le (Real.rpow_nonneg hL_pos.le _))
      have hMW_le1 : (M_W : ℝ) + 2 ≤
          40 * ((mMax : ℝ) + 2) * Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        have hM_def : (M_W : ℝ) = (Nat.ceil (36 * (mMax : ℝ) / φ mMax) : ℝ) + 1 := by
          dsimp only [M_W, Spanner.capM_W]; push_cast; rfl
        have hdiv : 36 * (mMax : ℝ) / φ mMax ≤
            36 * ((mMax : ℝ) + 2) * Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
          rw [div_eq_mul_one_div]
          have h36 : 36 * (mMax : ℝ) ≤ 36 * ((mMax : ℝ) + 2) := by linarith
          exact mul_le_mul h36 hinv_phi (div_nonneg zero_le_one (hφ_spec mMax).1.le) (by positivity)
        have h4 : (4 : ℝ) ≤ 4 * ((mMax : ℝ) + 2) * Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
          have h2le : (2 : ℝ) ≤ (mMax : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) mMax]
          calc (4 : ℝ) ≤ 4 * 2 * 1 := by norm_num
            _ ≤ 4 * ((mMax : ℝ) + 2) * Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
                gcongr
        linarith
      have hlog1 : Real.log ((M_W : ℝ) + 2) ≤
          Real.log 40 + Real.log ((mMax : ℝ) + 2) +
            C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) := by
        have h1 : Real.log ((M_W : ℝ) + 2) ≤
            Real.log (40 * ((mMax : ℝ) + 2) *
              Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) :=
          Real.log_le_log (by positivity) hMW_le1
        have h2 : Real.log (40 * ((mMax : ℝ) + 2) *
              Real.exp (C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) =
            Real.log 40 + Real.log ((mMax : ℝ) + 2) +
              C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
              Real.log_mul (by norm_num) (by positivity), Real.log_exp]
        linarith
      have hl40 : Real.log 40 ≤ 80 * Real.log ((mMax : ℝ) + 2) := by
        have h1 : Real.log 40 ≤ 40 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40)]
        linarith
      have hL78 : Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) ≤ 2 * Real.log ((mMax : ℝ) + 2) := by
        simpa using log_rpow_le_two_mul_rpow (a := 7 / 8) (b := 1) (by norm_num) (by norm_num)
          (by norm_num) mMax
      have hCpL : C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
          2 * C_p * Real.log ((mMax : ℝ) + 2) := by
        calc C_p * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)
            ≤ C_p * (2 * Real.log ((mMax : ℝ) + 2)) := mul_le_mul_of_nonneg_left hL78 hCp.le
          _ = 2 * C_p * Real.log ((mMax : ℝ) + 2) := by ring
      have heq81 : (81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2) =
          81 * Real.log ((mMax : ℝ) + 2) + 2 * C_p * Real.log ((mMax : ℝ) + 2) := by ring
      linarith
    have hlog_MW_rpow :
        C_p * Real.log ((M_W : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
          C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) := by
      have hpow : Real.log ((M_W : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
          ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2)) ^ (7 / 8 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M_W]))
          hlog_MW (by norm_num)
      rw [Real.mul_rpow (by linarith) hL_pos.le] at hpow
      have hmul := mul_le_mul_of_nonneg_left hpow hCp.le
      dsimp only [C_W]
      linarith
    have hreg_const_MW := hreg_const M_W
    have hMW_eq : Spanner.capM_W tools.constructExpander.c_deg (φ mMax) mMax = M_W := by
      rw [hc_deg]
    have hexp_M : tools.pathDS.γ_ExpPath (φ mMax) mMax ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
      le_trans hregM.2.1 (Real.exp_le_exp.mpr (by gcongr))
    have hexp_W : tools.pathDS.γ_ExpPath tools.constructExpander.φ_Const
          (Spanner.capM_W tools.constructExpander.c_deg (φ mMax) mMax) ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      rw [hMW_eq]
      exact le_trans hreg_const_MW.2.1 (Real.exp_le_exp.mpr hlog_MW_rpow)
    have hphi_M : 1 / tools.pathDS.φ_out (φ mMax) mMax ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
      le_trans hregM.2.2 (Real.exp_le_exp.mpr (by gcongr))
    have hphi_W : 1 / tools.pathDS.φ_out tools.constructExpander.φ_Const
          (Spanner.capM_W tools.constructExpander.c_deg (φ mMax) mMax) ≤
        Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      rw [hMW_eq]
      exact le_trans hreg_const_MW.2.2 (Real.exp_le_exp.mpr hlog_MW_rpow)
    have hcapPhi_inv : 1 / Spanner.capPhiDS tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (φ mMax) mMax ≤ Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      unfold Spanner.capPhiDS
      rcases le_total (tools.pathDS.φ_out (φ mMax) mMax)
          (tools.pathDS.φ_out tools.constructExpander.φ_Const
            (Spanner.capM_W tools.constructExpander.c_deg (φ mMax) mMax)) with hmin | hmin
      · rw [min_eq_left hmin]; exact hphi_M
      · rw [min_eq_right hmin]; exact hphi_W
    exact ⟨hinv_phi, hlog_MW, max_le hexp_M hexp_W, hcapPhi_inv⟩
  have hdec_le_all : ∀ mMax : ℕ,
      costs.decompose.decFactor mMax ≤
        C_dec * (Spanner.capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (hdec_mono.φ_lb mMax) mMax) ^ 2 := by
    intro mMax
    have hdom := hdom_dec mMax
    have hc1 : 1 ≤ c := by omega
    have hcsPhi_pos : 0 < Cited.csPhi Kγ c (3 * mMax) := by
      unfold Cited.csPhi Cited.csGamma
      have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
      positivity
    have hdec_pos : 0 < decFactor mMax := Real.exp_pos _
    have h1_phi : decFactor mMax ≤ C_dec * (1 / Cited.csPhi Kγ c (3 * mMax)) := by
      have hmul : 10 * C₁ * Cited.csPhi Kγ c (3 * mMax) * decFactor mMax ≤ 1 := by
        have hdom' : 10 * Cited.csPhi Kγ c (3 * mMax) ≤ 1 / (C₁ * decFactor mMax) := hdom
        have hden : 0 < C₁ * decFactor mMax := mul_pos hC₁ hdec_pos
        have hm := (le_div_iff₀ hden).mp hdom'
        linarith
      have hden2 : 0 < 10 * C₁ := by linarith
      rw [show C_dec * (1 / Cited.csPhi Kγ c (3 * mMax)) =
          1 / (10 * C₁ * Cited.csPhi Kγ c (3 * mMax)) by dsimp only [C_dec]; ring]
      rw [le_div_iff₀ (mul_pos hden2 hcsPhi_pos)]
      linarith
    have hinv_eq : 1 / Cited.csPhi Kγ c (3 * mMax) = 1 / tools.pathDS.φ_out (φ mMax) mMax := by
      rw [(hreg_phi mMax mMax le_rfl).1]
    have hinv_le_ge : 1 / tools.pathDS.φ_out (φ mMax) mMax ≤
        Spanner.capGammaExpPath tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax :=
      le_trans (tools.pathDS.hγ_ExpPath_ge (φ mMax) mMax (hφ_spec mMax).1) (le_max_left _ _)
    have hE_ge2 : 2 ≤ Spanner.capGammaExpPath tools.constructExpander.c_deg
        tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax :=
      Spanner.two_le_capGammaExpPath hφC_pos (hφ_spec mMax).1 mMax
    have hE_le_L2 : Spanner.capGammaExpPath tools.constructExpander.c_deg
          tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax ≤
        (Spanner.capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax) ^ 2 := by
      unfold Spanner.capGammaL
      have hE_le_E4 : Spanner.capGammaExpPath tools.constructExpander.c_deg
            tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax ≤
          (Spanner.capGammaExpPath tools.constructExpander.c_deg
            tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 4 := by
        have h1 : (1 : ℝ) ≤ (Spanner.capGammaExpPath tools.constructExpander.c_deg
            tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 3 :=
          one_le_pow₀ (by linarith)
        nlinarith
      exact le_trans hE_le_E4 (le_of_eq (by ring))
    have hdf_eq : costs.decompose.decFactor mMax = decFactor mMax := rfl
    have hphi_eq : hdec_mono.φ_lb mMax = φ mMax := rfl
    rw [hdf_eq, hphi_eq]
    exact le_trans h1_phi (mul_le_mul_of_nonneg_left (le_trans (hinv_eq ▸ hinv_le_ge) hE_le_L2) hCdec_nn)
  have hγ_bds : ∀ mMax : ℕ,
      (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
    intro mMax
    have hcaps := hMW_caps mMax
    rcases hcaps with ⟨_, hlog_MW, hE_bd, hPhi_bd⟩
    have hL_half := half_le_log_add_two_nat mMax
    have hL_pos : 0 < Real.log ((mMax : ℝ) + 2) := by linarith
    have hL78_nn : 0 ≤ Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) := Real.rpow_nonneg hL_pos.le _
    have hγℓ_bd : (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      change Spanner.capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax ≤ _
      unfold Spanner.capGammaL
      calc (Spanner.capGammaExpPath tools.constructExpander.c_deg tools.constructExpander.φ_Const
              tools.pathDS (φ mMax) mMax) ^ 2
          ≤ (Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) ^ 2 := by
            have hE_nn : 0 ≤ Spanner.capGammaExpPath tools.constructExpander.c_deg
                tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax :=
              le_trans (by norm_num) (Spanner.two_le_capGammaExpPath hφC_pos (hφ_spec mMax).1 mMax)
            nlinarith
        _ = Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            rw [sq, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            apply Real.exp_le_exp.mpr
            have hW_nn : 0 ≤ C_W := by positivity
            have h1 : 2 * C_W ≤ C_γ := by dsimp only [C_γ]; linarith
            nlinarith
    have heta1_bd : (Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2 ≤
        (144 * (81 + 2 * C_p) + 200) * Real.log ((mMax : ℝ) + 2) := by
      unfold Spanner.capEta1
      rw [hc_deg]
      have hceil_72 : (Nat.ceil (2 * (36 : ℝ)) : ℝ) ≤ 72 := by norm_num
      set a1 := Nat.ceil ((36 : ℝ) * (mMax : ℝ) / (2 * φ mMax)) + 1
      have ha1_le : a1 ≤ Spanner.capM_W 36 (φ mMax) mMax := by
        unfold Spanner.capM_W
        have hdiv : (36 : ℝ) * (mMax : ℝ) / (2 * φ mMax) ≤ (36 : ℝ) * (mMax : ℝ) / φ mMax :=
          div_le_div_of_nonneg_left (by positivity) (hφ_spec mMax).1 (by linarith [(hφ_spec mMax).1])
        exact Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
      have hlog_a1 : (Nat.log 2 a1 : ℝ) ≤ 2 * Real.log ((Spanner.capM_W 36 (φ mMax) mMax : ℝ) + 2) := by
        have h1 : (Nat.log 2 a1 : ℝ) ≤ (Nat.log 2 (Spanner.capM_W 36 (φ mMax) mMax) : ℝ) :=
          Nat.cast_le.mpr (Nat.log_mono_right ha1_le)
        exact le_trans h1 (natLog2_le_two_log_add_two _)
      have hlog_MW' : Real.log ((Spanner.capM_W 36 (φ mMax) mMax : ℝ) + 2) ≤
          (81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2) := by
        simpa [hc_deg] using hlog_MW
      have hcast : ((1 + Nat.ceil (2 * (36 : ℝ)) * (Nat.log 2 a1 + 1) : ℕ) : ℝ) + 1 / 2 =
          (3 / 2 : ℝ) + (Nat.ceil (2 * (36 : ℝ)) : ℝ) * ((Nat.log 2 a1 : ℝ) + 1) := by
        push_cast; ring
      rw [hcast]
      have h72_mul : (Nat.ceil (2 * (36 : ℝ)) : ℝ) * ((Nat.log 2 a1 : ℝ) + 1) ≤
          72 * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2)) + 1) := by
        have hlog1 : (Nat.log 2 a1 : ℝ) + 1 ≤ 2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2)) + 1 := by
          linarith
        exact mul_le_mul hceil_72 hlog1 (by positivity) (by norm_num)
      have hconst : (3 / 2 : ℝ) + 72 ≤ 200 * Real.log ((mMax : ℝ) + 2) := by linarith only [hL_half]
      have hexp_lhs : (72 : ℝ) * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2)) + 1) =
          72 * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2))) + 72 := by ring
      have h1 : (3 / 2 : ℝ) + (Nat.ceil (2 * (36 : ℝ)) : ℝ) * ((Nat.log 2 a1 : ℝ) + 1) ≤
          72 * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2))) + (3 / 2 + 72) := by
        have hadd := add_le_add (le_refl (3 / 2 : ℝ)) (le_trans h72_mul (le_of_eq hexp_lhs))
        exact le_trans hadd (le_of_eq (by ring))
      calc (3 / 2 : ℝ) + (Nat.ceil (2 * (36 : ℝ)) : ℝ) * ((Nat.log 2 a1 : ℝ) + 1)
          ≤ 72 * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2))) + (3 / 2 + 72) := h1
        _ ≤ 72 * (2 * ((81 + 2 * C_p) * Real.log ((mMax : ℝ) + 2))) +
              200 * Real.log ((mMax : ℝ) + 2) := add_le_add (le_refl _) hconst
        _ = (144 * (81 + 2 * C_p) + 200) * Real.log ((mMax : ℝ) + 2) := by ring
    have heta2_bd : (Spanner.capEta2 mMax : ℝ) + 1 / 2 ≤ 16 * Real.log ((mMax : ℝ) + 2) := by
      unfold Spanner.capEta2
      have hcast : ((1 + 2 * (Nat.log 2 (mMax + 1) + 1) : ℕ) : ℝ) + 1 / 2 =
          (7 / 2 : ℝ) + 2 * (Nat.log 2 (mMax + 1) : ℝ) := by
        push_cast; ring
      rw [hcast]
      have hlog_a : (Nat.log 2 (mMax + 1) : ℝ) ≤ 2 * Real.log (((mMax + 1 : ℕ) : ℝ) + 2) :=
        natLog2_le_two_log_add_two (mMax + 1)
      have h2m : Real.log (((mMax + 1 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((mMax : ℝ) + 2) := by
        have hM : (((mMax + 1 : ℕ) : ℝ) + 2) ≤ 2 * ((mMax : ℝ) + 2) := by
          push_cast; linarith only [Nat.cast_nonneg (α := ℝ) mMax]
        have h1' : Real.log (((mMax + 1 : ℕ) : ℝ) + 2) ≤ Real.log (2 * ((mMax : ℝ) + 2)) :=
          Real.log_le_log (by positivity) hM
        rw [Real.log_mul (by norm_num) (by positivity)] at h1'
        have hlog2_le : Real.log 2 ≤ Real.log ((mMax : ℝ) + 2) :=
          Real.log_le_log (by norm_num) (by linarith only [Nat.cast_nonneg (α := ℝ) mMax])
        linarith only [h1', hlog2_le]
      have hlog4 : (Nat.log 2 (mMax + 1) : ℝ) ≤ 4 * Real.log ((mMax : ℝ) + 2) := by
        linarith only [hlog_a, h2m]
      linarith only [hL_half, hlog4]
    have hγc_bd : (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      change Spanner.capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (φ mMax) mMax + 1 ≤ _
      unfold Spanner.capGammaC
      have hcapDel_eq : Spanner.capGammaDel tools.constructExpander.c_deg
          tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax = C_del := by
        unfold Spanner.capGammaDel
        rw [hγ_del_eq, hγ_del_eq, max_self]
      rw [hcapDel_eq]
      have hdiv_eq : 2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
            ((Spanner.capEta2 mMax : ℝ) + 1 / 2) *
            (Spanner.capGammaExpPath tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 *
            C_del ^ 2 /
            (Spanner.capPhiDS tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 =
          2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
            ((Spanner.capEta2 mMax : ℝ) + 1 / 2) * C_del ^ 2 *
            (Spanner.capGammaExpPath tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 *
            (1 / Spanner.capPhiDS tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 := by
        ring
      rw [hdiv_eq]
      have hE_nn : 0 ≤ Spanner.capGammaExpPath tools.constructExpander.c_deg
          tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax :=
        le_trans (by norm_num) (Spanner.two_le_capGammaExpPath hφC_pos (hφ_spec mMax).1 mMax)
      have hPhi_pos : 0 < Spanner.capPhiDS tools.constructExpander.c_deg
          tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax :=
        Spanner.capPhiDS_pos hφC_pos (hφ_spec mMax).1 mMax
      have hE2 : (Spanner.capGammaExpPath tools.constructExpander.c_deg
            tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 ≤
          Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        calc _ ≤ (Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ hE_nn hE_bd 2
          _ = Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
              rw [sq, ← Real.exp_add]; ring_nf
      have hPhi2 : (1 / Spanner.capPhiDS tools.constructExpander.c_deg
            tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 ≤
          Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        calc _ ≤ (Real.exp (C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hPhi_bd 2
          _ = Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
              rw [sq, ← Real.exp_add]; ring_nf
      have hlog_exp : Real.log ((mMax : ℝ) + 2) ≤
          Real.exp (3 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
        log_add_two_le_exp_rpow (by norm_num) (by norm_num) mMax
      have hlog_sq : Real.log ((mMax : ℝ) + 2) ^ 2 ≤
          Real.exp (6 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        calc Real.log ((mMax : ℝ) + 2) ^ 2
            ≤ (Real.exp (3 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ hL_pos.le hlog_exp 2
          _ = Real.exp (6 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
              rw [sq, ← Real.exp_add]; ring_nf
      have hpre : 2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
            ((Spanner.capEta2 mMax : ℝ) + 1 / 2) * C_del ^ 2 ≤
          (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
            Real.log ((mMax : ℝ) + 2) ^ 2 := by
        have hm1 := mul_le_mul heta1_bd heta2_bd (by positivity) (by positivity)
        have hm2 := mul_le_mul_of_nonneg_left hm1 (by norm_num : (0 : ℝ) ≤ 2)
        have hm3 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg C_del)
        have hlhs : 2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
              ((Spanner.capEta2 mMax : ℝ) + 1 / 2) * C_del ^ 2 =
            2 * (((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
              ((Spanner.capEta2 mMax : ℝ) + 1 / 2)) * C_del ^ 2 := by ring
        rw [hlhs]
        exact le_trans hm3 (le_of_eq (by ring))
      have h1_le_exp : (1 : ℝ) ≤ Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
        Real.one_le_exp (by positivity)
      have hprod_bd : 2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
            ((Spanner.capEta2 mMax : ℝ) + 1 / 2) * C_del ^ 2 *
            (Spanner.capGammaExpPath tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 *
            (1 / Spanner.capPhiDS tools.constructExpander.c_deg
              tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 + 1 ≤
          C_poly * Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
        have h4 : (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
              Real.log ((mMax : ℝ) + 2) ^ 2 *
              Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
              Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
            (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
              Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
          have hexp_eq : Real.exp (6 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                (Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) =
              Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          have hA := mul_le_mul_of_nonneg_left hlog_sq
            (by positivity : 0 ≤ 2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2)
          have hB := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤
            Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
            Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)))
          calc (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
                Real.log ((mMax : ℝ) + 2) ^ 2 *
                Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))
              = (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
                  Real.log ((mMax : ℝ) + 2) ^ 2 *
                  (Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                  Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) := by ring
            _ ≤ (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
                  Real.exp (6 * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                  (Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
                  Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ))) := hB
            _ = (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
                  Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
                rw [mul_assoc _ (Real.exp (6 * _)) _, hexp_eq]
        have hmain : 2 * ((Spanner.capEta1 tools.constructExpander.c_deg (φ mMax) mMax : ℝ) + 1 / 2) *
              ((Spanner.capEta2 mMax : ℝ) + 1 / 2) * C_del ^ 2 *
              (Spanner.capGammaExpPath tools.constructExpander.c_deg
                tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 *
              (1 / Spanner.capPhiDS tools.constructExpander.c_deg
                tools.constructExpander.φ_Const tools.pathDS (φ mMax) mMax) ^ 2 ≤
            (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
              Real.log ((mMax : ℝ) + 2) ^ 2 *
              Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
              Real.exp (2 * C_W * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
          have hm12 := mul_le_mul hpre hE2 (by positivity) (by positivity)
          exact mul_le_mul hm12 hPhi2 (by positivity) (by positivity)
        have hsum := add_le_add (le_trans hmain h4) h1_le_exp
        have hrhs : (2 * (144 * (81 + 2 * C_p) + 200) * 16 * C_del ^ 2) *
              Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) +
              Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) =
            C_poly * Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
          dsimp only [C_poly]; ring
        exact le_trans hsum (le_of_eq hrhs)
      have hCpoly_exp := nonneg_const_le_exp_rpow (a := (7 / 8 : ℝ)) hCpoly_nn (by norm_num) (by norm_num) mMax
      calc _ ≤ C_poly * Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := hprod_bd
        _ ≤ Real.exp (2 * C_poly * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) *
              Real.exp ((4 * C_W + 6) * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCpoly_exp (Real.exp_pos _).le
        _ = Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            rw [← Real.exp_add]; dsimp only [C_γ]; ring_nf
    exact ⟨hγℓ_bd, hγc_bd⟩
  have hCW_nn : 0 ≤ C_W := le_trans hCp.le hCW_ge
  obtain ⟨C_q, hCq_pos, hγt_all⟩ := capGammaQuery_le_exp_eight_ninths hC₀ hC₁ hCW_nn hφC_pos hγq
    (fun m => (hφ_spec m).1) (fun m => (hφ_spec m).2.2) (c_deg := tools.constructExpander.c_deg)
  have hγt_bd := fun mMax => hγt_all mMax (hMW_caps mMax).2.2.1
  let params_t : ℕ → DynSpanner.SparsifyParams := fun mMax =>
    Spanner.sparsifyMGParamsOfDecWithTime tools costs (φ mMax) (hφ_spec mMax).1 mMax C_dec hCdec_nn
  refine ⟨sparsify, sparsify_t, params, params_t, C_γ, (params 0).K_s, (params 0).K_t, C_q,
    hCγ_pos, ?_, ?_, ?_, hCq_pos, ?_, ?_⟩
  · dsimp only [params, Spanner.sparsifyMGParamsOfDec]
    rw [hc_deg, hc_ℓ]; ring
  · have := (params 0).hK_s; exact this
  · have := (params 0).hK_t; exact this
  · intro mMax
    refine ⟨rfl, rfl, rfl, rfl, (hγ_bds mMax).1, (hγ_bds mMax).2, ?_⟩
    exact Spanner.sparsifyMG_spec_of_dec_le toolsE costs hdec_mono hpdsE_mono mMax hCdec_nn
      (hdec_le_all mMax) (fun _ _ _ => rfl)
  · intro mMax
    refine ⟨rfl, rfl, rfl, rfl, (hγ_bds mMax).1, (hγ_bds mMax).2, hγt_bd mMax, ?_⟩
    exact Spanner.sparsifyMG_spec_of_dec_le_with_time tools costs hdec_mono hpds_mono mMax
      hCdec_nn (hdec_le_all mMax)

/-- **Concrete Static Sparsifier (Theorem 8.1, page 39), with each `GetPath` charged
`γ_ExpPath`**: the first part of `theorem_8_1_concrete_both`. It charges every query of the path
data structure only `O(γ_ExpPath)`, which holds on clusters where [CS21] applies. Below the
conductance of [CS21] a query costs up to `γ_query` (`theorem_8_1_concrete_with_time`). -/
theorem theorem_8_1_concrete
    (hDec : Cited.ExpanderDecomposition) (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) := by
  obtain ⟨sparsify, _, params, _, C_γ, K_s, K_t, _, h1, h2, h3, h4, _, h6, _⟩ :=
    theorem_8_1_concrete_both (.of_cited hDec) hPaths
  exact ⟨sparsify, params, C_γ, K_s, K_t, h1, h2, h3, h4, h6⟩

/-- **Concrete Static Sparsifier (Theorem 8.1, page 39), with the query time of Theorem 8.6**:
the second part of `theorem_8_1_concrete_both`. Each `GetPath` of the path data structure is
charged `γ_query`, which covers the fallback search on clusters below the conductance of [CS21].
The runtime of the sparsifier carries the factor `γ_t ≤ exp(C_q · log^{8/9}(mMax + 2) ·
log(log(mMax + 2) + 2)^{4/3})`; the bounds on `γ_ℓ` and `γ_c` are those of
`theorem_8_1_concrete`. -/
theorem theorem_8_1_concrete_with_time
    (hDec : Cited.ExpanderDecomposition) (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) := by
  obtain ⟨_, sparsify, _, params, C_γ, K_s, K_t, C_q, h1, h2, h3, h4, h5, _, h7⟩ :=
    theorem_8_1_concrete_both (.of_cited hDec) hPaths
  exact ⟨sparsify, params, C_γ, K_s, K_t, C_q, h1, h2, h3, h4, h5, h7⟩

end

end MinCostFlow.Expander
