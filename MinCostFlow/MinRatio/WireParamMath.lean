module

public import MinCostFlow.Final.ConcreteChainModelWithLast
public import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Exact integer formulas for the solver's chain parameters

Expresses the scalar parameters of `concreteCirculationCfgOfDims` and `levelM` (when `γ_ℓ` is
integral) in exact natural-number form:
1. `paramM0`, `paramN0`, `paramQuality`, `paramEpsExp`, `paramPsi`, `paramDepth`, `paramBranch`:
   exact formulas as functions of `(m, V)` and the witness constants `(threshold, A)`.
2. `nat_ceil_rpow_inv_eq_nthRoot`: proves that `⌈M ^ (1 / d)⌉₊ = if M ≤ 1 then 1 else
   Nat.nthRoot d (M - 1) + 1` for every `1 ≤ M` and `0 < d`.
3. `chosenD_le_size_add_two`: proves `Chain.chosenD (23 / 24) M ≤ (M + 2).size` for `1 ≤ M`,
   giving an explicit upper bound on `d` computable in `O(log M)` before `d` is known.
4. `levelM_eq_nat_div`: proves that whenever `TP.γ_ℓ (P.M₀ ^ 2) = (γ : ℝ)` for a natural number
   `1 ≤ γ`, `Chain.levelM TP P i = (P.M₀ * γ ^ (i + 1) + P.k ^ i - 1) / P.k ^ i`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain IPM.Machine Final

/-- Padded edge cap `M₀ = max m threshold`. -/
@[expose] def paramM0 (threshold m : ℕ) : ℕ := max m threshold

/-- Vertex cap `N₀ = 4 * max m threshold`. -/
@[expose] def paramN0 (threshold m : ℕ) : ℕ := 4 * max m threshold

/-- Capped dyadic quality exponent `k = cappedQualityExponent threshold A m`. -/
@[expose] def paramQuality (threshold A m : ℕ) : ℕ := cappedQualityExponent threshold A m

/-- Detector epsilon exponent `k + alphaExponent m V + 10`. -/
@[expose] def paramEpsExp (threshold A m V : ℕ) : ℕ :=
  paramQuality threshold A m + Num.IPM.alphaExponent m V + 10

/-- Stability range parameter `⌈cfg.Ψ⌉₊` in exact natural-number form. -/
@[expose] def paramPsi (threshold A m V : ℕ) : ℕ :=
  ipmQualityRangeExponent m V (paramQuality threshold A m) + slackRangeExponent m V + 6

/-- Chain depth `d = chosenD (23 / 24) (max m threshold)`. -/
@[expose] noncomputable def paramDepth (threshold m : ℕ) : ℕ :=
  Chain.chosenD (23 / 24) (max m threshold)

/-- Exact integer branching factor `⌈M₀^{1/d}⌉₊` via `Nat.nthRoot`. -/
@[expose] noncomputable def paramBranch (threshold m : ℕ) : ℕ :=
  let M₀ := max m threshold
  if M₀ ≤ 1 then 1 else Nat.nthRoot (paramDepth threshold m) (M₀ - 1) + 1

/-- Exact natural-number ceiling of `M ^ (1 / d)` for `1 ≤ M` and `0 < d`. -/
theorem nat_ceil_rpow_inv_eq_nthRoot {M d : ℕ} (hM : 1 ≤ M) (hd : 0 < d) :
    Nat.ceil ((M : ℝ) ^ (1 / (d : ℝ))) =
      if M ≤ 1 then 1 else Nat.nthRoot d (M - 1) + 1 := by
  have hd_ne : d ≠ 0 := hd.ne'
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  by_cases hM1 : M ≤ 1
  · have hMeq : M = 1 := by omega
    subst hMeq
    simp [Real.one_rpow]
  · rw [ite_eq_right hM1]
    have hM2 : 2 ≤ M := by omega
    set r := Nat.nthRoot d (M - 1)
    have hr_pow : r ^ d ≤ M - 1 := (Nat.le_nthRoot_iff hd_ne).mp le_rfl
    have hr_lt : M - 1 < (r + 1) ^ d := Nat.lt_pow_nthRoot_add_one hd_ne (M - 1)
    have hr_lt_M : (r : ℝ) ^ d < (M : ℝ) := by exact_mod_cast (show r ^ d < M by omega)
    have hM_le_r1 : (M : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ d := by
      exact_mod_cast (show M ≤ (r + 1) ^ d by omega)
    have hrpow : ((M : ℝ) ^ (1 / (d : ℝ))) ^ d = (M : ℝ) := by
      rw [← Real.rpow_natCast ((M : ℝ) ^ (1 / (d : ℝ))) d,
        ← Real.rpow_mul hM_nn, one_div_mul_cancel hd_pos.ne', Real.rpow_one]
    have hlo : (r : ℝ) < (M : ℝ) ^ (1 / (d : ℝ)) := by
      by_contra hnot
      push Not at hnot
      have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hM_nn _) hnot d
      rw [hrpow] at hpow
      linarith
    have hhi : (M : ℝ) ^ (1 / (d : ℝ)) ≤ ((r + 1 : ℕ) : ℝ) := by
      by_contra hnot
      push Not at hnot
      have hpow := pow_lt_pow_left₀ hnot (Nat.cast_nonneg _) hd_ne
      rw [hrpow] at hpow
      linarith
    exact (Nat.ceil_eq_iff (Nat.succ_ne_zero r)).mpr ⟨by simpa using hlo, by simpa using hhi⟩

/-- `chosenD (23 / 24) M` is bounded above by the binary length `(M + 2).size` for `1 ≤ M`. -/
theorem chosenD_le_size_add_two {M : ℕ} (hM : 1 ≤ M) :
    Chain.chosenD (23 / 24) M ≤ (M + 2).size := by
  have hM3 : 3 ≤ M + 2 := by omega
  have hlog_ge1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
    have h3 : Real.exp 1 ≤ (M : ℝ) + 2 := by
      have : (3 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast hM3
      linarith [Real.exp_one_lt_three]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hpow_le_log : Real.log ((M : ℝ) + 2) ^ ((1 - (23 : ℝ) / 24) / 2) ≤ Real.log ((M : ℝ) + 2) := by
    calc Real.log ((M : ℝ) + 2) ^ ((1 - (23 : ℝ) / 24) / 2)
        ≤ Real.log ((M : ℝ) + 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog_ge1 (by norm_num)
      _ = Real.log ((M : ℝ) + 2) := Real.rpow_one _
  have hlt_pow : ((M : ℝ) + 2) < (2 : ℝ) ^ (M + 2).size := by
    exact_mod_cast Nat.lt_size_self (M + 2)
  have hlog_le_sz : Real.log ((M : ℝ) + 2) ≤ ((M + 2).size : ℝ) := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h1 := Real.log_le_log (by positivity) hlt_pow.le
    rw [Real.log_pow] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) (M + 2).size]
  exact Nat.ceil_le.mpr (hpow_le_log.trans hlog_le_sz)

/-- Exact formulas for all six scalar parameters of `concreteCirculationCfgOfDims W m V`. -/
theorem concreteCfg_scalars_eq
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (SparseCore.lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) (m V : ℕ) :
    let threshold := concreteEdgeThresholdWithLast W
    let A := concreteQualityBudgetWithLast W
    let cfg := concreteCirculationCfgOfDims W m V
    cfg.P.M₀ = paramM0 threshold m ∧
    cfg.N₀ = paramN0 threshold m ∧
    ⌈cfg.Ψ⌉₊ = paramPsi threshold A m V ∧
    cfg.P.d = paramDepth threshold m ∧
    cfg.P.k = paramBranch threshold m := by
  dsimp only [concreteCirculationCfgOfDims, Chain.Ordered.concreteAlg2CfgWithLast,
    Chain.concreteChainParams, Chain.mkChainParams, paramM0, paramN0, paramPsi,
    paramQuality, paramDepth, paramBranch]
  refine ⟨rfl, rfl, Nat.ceil_natCast _, rfl, ?_⟩
  have hM₀ : 1 ≤ max m (concreteEdgeThresholdWithLast W) :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
  have hd : 0 < Chain.chosenD (23 / 24) (max m (concreteEdgeThresholdWithLast W)) :=
    (Chain.chosenD_bounds (by norm_num) hM₀).1
  exact nat_ceil_rpow_inv_eq_nthRoot hM₀ hd

/-- When `TP.γ_ℓ (P.M₀ ^ 2)` is a positive integer `γ`, `levelM TP P i` equals the exact
natural-number ceiling division `(P.M₀ * γ ^ (i + 1) + P.k ^ i - 1) / P.k ^ i`. -/
theorem levelM_eq_nat_div {TP : SparseCoreParams} {P : ChainParams} {γ : ℕ}
    (hγ1 : 1 ≤ γ) (hγ : TP.γ_ℓ (P.M₀ ^ 2) = (γ : ℝ)) (i : ℕ) :
    Chain.levelM TP P i = (P.M₀ * γ ^ (i + 1) + P.k ^ i - 1) / P.k ^ i := by
  unfold Chain.levelM
  rw [hγ]
  have hki_pos : 0 < P.k ^ i := Nat.pow_pos P.hk
  have hki_rpos : (0 : ℝ) < ((P.k ^ i : ℕ) : ℝ) := Nat.cast_pos.mpr hki_pos
  have hnum_pos : 0 < P.M₀ * γ ^ (i + 1) := Nat.mul_pos P.hM₀ (Nat.pow_pos hγ1)
  have hreal : (P.M₀ : ℝ) * (γ : ℝ) * ((γ : ℝ) / (P.k : ℝ)) ^ i =
      ((P.M₀ * γ ^ (i + 1) : ℕ) : ℝ) / ((P.k ^ i : ℕ) : ℝ) := by
    rw [div_pow]
    push_cast
    rw [pow_succ']
    ring
  rw [hreal]
  set N := P.M₀ * γ ^ (i + 1)
  set D := P.k ^ i
  set q := (N + D - 1) / D
  have hq_pos : 1 ≤ q := Nat.div_pos (by omega) hki_pos
  have hdiv_mod := Nat.mod_add_div (N + D - 1) D
  have hmod_lt := Nat.mod_lt (N + D - 1) hki_pos
  have hN_le : N ≤ q * D := by
    have : (N + D - 1) % D + D * q = N + D - 1 := hdiv_mod
    have : D * q = q * D := Nat.mul_comm D q
    omega
  have hlt_N : (q - 1) * D < N := by
    have hmul : q * D = (q - 1) * D + D := by
      calc q * D = (q - 1 + 1) * D := by rw [Nat.sub_add_cancel hq_pos]
        _ = (q - 1) * D + D := by ring
    have : (N + D - 1) % D + D * q = N + D - 1 := hdiv_mod
    have : D * q = q * D := Nat.mul_comm D q
    omega
  refine (Nat.ceil_eq_iff (by omega : q ≠ 0)).mpr ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hki_rpos]
    exact_mod_cast hlt_N
  · rw [div_le_iff₀ hki_rpos]
    exact_mod_cast hN_le

end MinCostFlow.MinRatio

end
