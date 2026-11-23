module

public import MinCostFlow.Chain.ConcreteDefs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modular Asymptotics for `ConcreteInstantiation`

Proves modular asymptotic bounds showing every Section 8 expander term, bucket capacity,
`gammaLEnv`, `recEnv`, `encEnv`, and `costMult` stays within
`exp (O(log^{23/24} (M₀ + 2) * log (log (M₀ + 2) + 2)))`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander

section ModularAsymp

lemma asymp_sec8_bounds {C_sp K_s K_t C_poly : ℝ}
    (hCsp : 0 < C_sp) (_hKs : 0 ≤ K_s)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {M₀ : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_69 : 69 ≤ C_poly) :
    let M₂ := M₀ ^ 2
    let Pb := params M₂
    let L_E := chosenL M₂
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    coreE82Len L_E Pb ≤ Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    coreE_L L_E Pb ≤ Real.exp ((432 + 114 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    Pb.γ_ℓ ≤ Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) ∧
    (L_E : ℝ) + 1 ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) ∧
    coreNRoot L_E M₂ ≤ Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) ∧
    coreLambdaS Pb M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
  intro M₂ Pb L_E L LL
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hL_nn : 0 ≤ L := by linarith
  have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_nn _
  have hPb_spec := hp_spec M₂
  have hPb_γℓ_nn : 0 ≤ Pb.γ_ℓ := by linarith [Pb.hγ_ℓ]
  have hPb_γc_nn : 0 ≤ Pb.γ_c := by linarith [Pb.hγ_c]
  have hS8 := exp_gamma_pow_L_bounds hCsp hPb_γℓ_nn hPb_γc_nn M₂ hPb_spec.2.2.2.2.1 hPb_spec.2.2.2.2.2
  have hExp_M2_mono : ∀ c : ℝ, 0 ≤ c →
      Real.exp (c * Real.log ((M₂ : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
        Real.exp (2 * c * L ^ (23 / 24 : ℝ)) := fun c hc => by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left (rpow_sq_23_24_le M₀) hc]
  have hExp_to_LL : ∀ {x c : ℝ}, 0 ≤ c → x ≤ Real.exp (c * L ^ (23 / 24 : ℝ)) →
      x ≤ Real.exp (c * L ^ (23 / 24 : ℝ) * LL) := fun hc hx =>
    le_trans hx (rpow_exp_le_LL hc hM₀1)
  have hNMax_le : (coreNMax M₂ : ℝ) ≤ 63 * ((M₂ : ℝ) + 2) ^ 2 := by
    unfold coreNMax coreSplitMax; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) M₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hExp_to_LL (by positivity) ?_
    change (3 : ℝ) ^ L_E * Pb.γ_ℓ ^ (L_E + 1) ≤ _
    rw [show (72 + 24 * C_sp : ℝ) = 2 * (36 + 12 * C_sp) by ring]
    exact le_trans hS8.2.1 (hExp_M2_mono (36 + 12 * C_sp) (by positivity))
  · refine hExp_to_LL (by positivity) ?_
    change (3 : ℝ) ^ ((L_E + 1) * (L_E + 2) / 2 + L_E + 2) *
        Pb.γ_c ^ (L_E + 1) * Pb.γ_ℓ ^ ((L_E + 1) * (L_E + 2) / 2 + 2) ≤ _
    rw [show (432 + 114 * C_sp : ℝ) = 2 * (216 + 57 * C_sp) by ring]
    exact le_trans hS8.2.2.2 (hExp_M2_mono (216 + 57 * C_sp) (by positivity))
  · exact hExp_to_LL (by positivity) (by
      rw [show (4 : ℝ) * C_sp = 2 * (2 * C_sp) by ring]
      exact le_trans hS8.1 (hExp_M2_mono (2 * C_sp) (by positivity)))
  · exact hExp_to_LL (by norm_num) (by
      have h24 : (24 : ℝ) * L ^ (23 / 24 : ℝ) = 2 * 12 * L ^ (23 / 24 : ℝ) := by ring
      rw [h24]
      exact le_trans (chosenL_add_one_le_exp M₂) (hExp_M2_mono 12 (by norm_num)))
  · refine hExp_to_LL (by norm_num) ?_
    have hNMax_le' : (coreNMax M₂ : ℝ) ≤ 63 * ((M₂ : ℝ) + 2) ^ (2 : ℝ) := by
      simpa [Real.rpow_natCast] using hNMax_le
    have hnr := nRoot_le_exp (C_n := 63) (r_n := 2) (by norm_num) (by norm_num) hNMax_le'
    have h256 : Real.exp (2 * (2 * 63 + 2 : ℝ) * L ^ (23 / 24 : ℝ)) ≤
        Real.exp (260 * L ^ (23 / 24 : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by norm_num) hLa23_nn)
    unfold coreNRoot
    exact le_trans hnr (le_trans (hExp_M2_mono (2 * 63 + 2) (by norm_num)) h256)
  · unfold coreLambdaS
    rw [hPb_spec.2.1, pow_one]
    have hM2_eq : ((M₂ : ℝ)) = (M₀ : ℝ) ^ 2 := by push_cast [M₂]; rfl
    have hm2 : (M₂ : ℝ) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by rw [hM2_eq]; nlinarith only [hM0_nn]
    have harg : (coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2 ≤ 64 * ((M₀ : ℝ) + 2) ^ 4 := by
      have hsq : ((M₂ : ℝ) + 2) ^ 2 ≤ (((M₀ : ℝ) + 2) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hm2 2
      have h2_4 : ((M₀ : ℝ) + 2) ^ 2 ≤ ((M₀ : ℝ) + 2) ^ 4 :=
        pow_le_pow_right₀ (by linarith [hM0_nn]) (by norm_num)
      calc (coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2
          ≤ 63 * ((M₂ : ℝ) + 2) ^ 2 + ((M₀ : ℝ) + 2) ^ 2 := by linarith only [hNMax_le, hm2]
        _ ≤ 63 * (((M₀ : ℝ) + 2) ^ 2) ^ 2 + ((M₀ : ℝ) + 2) ^ 4 := by linarith only [hsq, h2_4]
        _ = 64 * ((M₀ : ℝ) + 2) ^ 4 := by ring
    have hlog_arg : 1 + Real.log ((coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤ 69 * L := by
      have hpos : 0 < (coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2 := by positivity
      have hlog_le : Real.log ((coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤ Real.log (64 * ((M₀ : ℝ) + 2) ^ 4) :=
        Real.log_le_log hpos harg
      rw [Real.log_mul (by norm_num) (pow_ne_zero 4 (by positivity)), Real.log_pow] at hlog_le
      have hlog64 : Real.log 64 ≤ 64 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 64)]
      have hlog_le' : Real.log ((coreNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤ 64 + 4 * L := by
        have h4 : ((4 : ℕ) : ℝ) * Real.log ((M₀ : ℝ) + 2) = 4 * L := by norm_num [L]
        linarith only [hlog_le, hlog64, h4]
      linarith only [hlog_le', hL1]
    have h69 := hPoly 69 1 (by norm_num) hCpoly_69 (by norm_num)
    rw [pow_one] at h69
    exact le_trans hlog_arg h69

private lemma asymp_bcap_bound_strong (C_lsst C_ψ C_N C_poly : ℝ) (_hCψ : 0 ≤ C_ψ) (_hCN : 1 ≤ C_N)
    {M₀ N₀ : ℕ} (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    (hlogN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2))
    (hΨ : alg2PsiGame Ψ M₀ ≤
      Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hExpPoly : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤ Real.exp (Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ)))
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_bcap : 2 * mwuK0 C_lsst * C_N ^ 6 + 2 ≤ C_poly ∧ 11 ≤ C_poly) :
    (concreteBCap C_lsst Ψ M₀ N₀ hM₀1 : ℝ) ≤
      Real.exp ((2 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  let L := Real.log ((M₀ : ℝ) + 2)
  let LL := Real.log (L + 2)
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
  have hL_nn : 0 ≤ L := by linarith
  have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_nn _
  have hlogN2_nn : 0 ≤ Real.log ((N₀ : ℝ) + 2) := by linarith [half_lt_log_add_two N₀]
  let P := concreteChainParams M₀ hM₀1
  have hPd_bounds := chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM₀1
  have hPd_le_2L : (P.d : ℝ) ≤ 2 * L := by
    have h1 : L ^ ((1 - (23 : ℝ) / 24) / 2) ≤ L := by
      calc L ^ ((1 - (23 : ℝ) / 24) / 2) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    change (chosenD (23 / 24) M₀ : ℝ) ≤ 2 * L
    linarith [hPd_bounds.2.2]
  have hPk_le_2M0 : (P.k : ℝ) ≤ 2 * ((M₀ : ℝ) + 2) := by
    have hk_up : (P.k : ℝ) ≤ 2 * (M₀ : ℝ) ^ (1 / (P.d : ℝ)) := P.hk_upper
    have hd1 : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast P.hd
    have hM0_r : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
    have hinv : 1 / (P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd1 (by linarith)
    have hrpow : (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (M₀ : ℝ) := by
      calc (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (M₀ : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hM0_r hinv
        _ = (M₀ : ℝ) := Real.rpow_one _
    linarith
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  have hσ_cap_ge2 : 2 ≤ σ_cap := le_max_left _ _
  have hσ_cap_pos : 0 < σ_cap := by linarith
  have hK0_nn : 0 ≤ mwuK0 C_lsst := (mwuK0_pos C_lsst).le
  have hσ_cap_le : σ_cap ≤ (2 + 2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * ((M₀ : ℝ) + 2) := by
    have hpow6 : (Real.log ((N₀ : ℝ) + 2)) ^ 6 ≤ (C_N * L) ^ 6 := pow_le_pow_left₀ hlogN2_nn hlogN 6
    have hm_part : mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 ≤
        (2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * ((M₀ : ℝ) + 2) := by
      calc mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6
          ≤ mwuK0 C_lsst * (2 * ((M₀ : ℝ) + 2)) * (C_N * L) ^ 6 := by gcongr
        _ = (2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * ((M₀ : ℝ) + 2) := by ring
    have hM2_1 : (1 : ℝ) ≤ (M₀ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M₀]
    have h12 : (2 : ℝ) ≤ 2 * ((M₀ : ℝ) + 2) := by linarith
    have hrhs_nn : 0 ≤ (2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * ((M₀ : ℝ) + 2) := by positivity
    dsimp only [σ_cap]
    refine max_le (by linarith) (max_le (by linarith) (by linarith))
  have hpoly_exp_cap : 2 + 2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6 ≤ Real.exp L := by
    have hL6 := hExpPoly (2 + 2 * mwuK0 C_lsst * C_N ^ 6) 6 (by positivity) (by linarith [hCpoly_bcap.1]) (by norm_num)
    have hL16 : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ hL1
    have hsum : 2 + 2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6 ≤ (2 + 2 * mwuK0 C_lsst * C_N ^ 6) * L ^ 6 := by nlinarith
    have h23_L : L ^ (23 / 24 : ℝ) ≤ L := by
      calc L ^ (23 / 24 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    exact le_trans (le_trans hsum hL6) (Real.exp_le_exp.mpr h23_L)
  have hlog_σ_le : Real.log σ_cap ≤ 2 * L := by
    have hle_exp : σ_cap ≤ Real.exp (2 * L) := by
      have hM2_eq : (M₀ : ℝ) + 2 = Real.exp L := (Real.exp_log (by positivity)).symm
      calc σ_cap ≤ (2 + 2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * ((M₀ : ℝ) + 2) := hσ_cap_le
        _ ≤ Real.exp L * Real.exp L := by rw [hM2_eq]; exact mul_le_mul_of_nonneg_right hpoly_exp_cap (Real.exp_pos _).le
        _ = Real.exp (2 * L) := by rw [← Real.exp_add]; ring_nf
    calc Real.log σ_cap ≤ Real.log (Real.exp (2 * L)) := Real.log_le_log hσ_cap_pos hle_exp
      _ = 2 * L := Real.log_exp _
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hB_lt : (concreteBCap C_lsst Ψ M₀ N₀ hM₀1 : ℝ) <
      (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 + 3 := by
    have hnum_nn : 0 ≤ (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 := by positivity
    have hc := Nat.ceil_lt_add_one hnum_nn
    dsimp only [concreteBCap]; push_cast; linarith [hc]
  have hΨ_part : 2 * max 0 Ψ / Real.log 2 ≤ 4 * Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) := by
    have h1 : max 0 Ψ ≤ Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) := le_trans (max_zero_le_alg2PsiGame Ψ M₀) hΨ
    have h2 : 2 * max 0 Ψ / Real.log 2 ≤ 4 * max 0 Ψ :=
      (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr (by
        have : 0 ≤ max 0 Ψ := le_max_left _ _; nlinarith [hlog2_gt])
    linarith
  have hd_part : (P.d : ℝ) * Real.log σ_cap / Real.log 2 + 3 ≤
      Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
    have hmul := mul_le_mul hPd_le_2L hlog_σ_le hlogσ_nn (by positivity)
    have hdiv : (P.d : ℝ) * Real.log σ_cap / Real.log 2 ≤ 8 * L ^ 2 :=
      (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr (by nlinarith [hlog2_gt])
    have h1_L2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    exact le_trans (by linarith : (P.d : ℝ) * Real.log σ_cap / Real.log 2 + 3 ≤ 11 * L ^ 2)
      (hPoly_LL 11 2 (by norm_num) hCpoly_bcap.2 (by norm_num))
  have h4_le : 4 * Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) ≤
      Real.exp ((C_ψ + 1) * L ^ (23 / 24 : ℝ) * LL) := by
    have h4e : (4 : ℝ) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
      simpa using hPoly_LL 4 0 (by norm_num) (by linarith [hCpoly_bcap.2]) (by norm_num)
    calc 4 * Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL)
        ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) := mul_le_mul_of_nonneg_right h4e (by positivity)
      _ = Real.exp ((C_ψ + 1) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
  have h2e : (2 : ℝ) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
    simpa using hPoly_LL 2 0 (by norm_num) (by linarith [hCpoly_bcap.2]) (by norm_num)
  have hsum : 4 * Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) + ((P.d : ℝ) * Real.log σ_cap / Real.log 2 + 3) ≤
      Real.exp ((2 + C_ψ) * L ^ (23 / 24 : ℝ) * LL) := by
    let A := L ^ (23 / 24 : ℝ) * LL
    have hA : 0 ≤ A := mul_nonneg hLa23_nn (by linarith)
    have hmono : Real.exp A ≤ Real.exp ((C_ψ + 1) * A) :=
      Real.exp_le_exp.mpr (by nlinarith only [_hCψ, hA, mul_nonneg _hCψ hA])
    have hd : (P.d : ℝ) * Real.log σ_cap / Real.log 2 + 3 ≤ Real.exp A := by
      simpa [A] using hd_part
    have hx : 4 * Real.exp (C_ψ * L ^ (23 / 24 : ℝ) * LL) ≤ Real.exp ((C_ψ + 1) * A) := by
      simpa only [A, mul_assoc] using h4_le
    rw [show (2 + C_ψ) * L ^ (23 / 24 : ℝ) * LL = A + (C_ψ + 1) * A by
      dsimp [A]; ring, Real.exp_add]
    have htwo : (2 : ℝ) ≤ Real.exp A := by simpa [A] using h2e
    linarith only [hx, hd.trans hmono, mul_le_mul_of_nonneg_right htwo
      (Real.exp_pos ((C_ψ + 1) * A)).le]
  have hB_split : (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 + 3 =
      2 * max 0 Ψ / Real.log 2 + ((P.d : ℝ) * Real.log σ_cap / Real.log 2 + 3) := by ring
  change (concreteBCap C_lsst Ψ M₀ N₀ hM₀1 : ℝ) ≤ Real.exp ((2 + C_ψ) * L ^ (23 / 24 : ℝ) * LL)
  linarith only [hB_lt, hB_split, hΨ_part, hsum]

lemma asymp_bcap_bound (C_lsst C_ψ C_N C_poly : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    {M₀ N₀ : ℕ} (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    (hlogN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2))
    (hΨ : alg2PsiGame Ψ M₀ ≤
      Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hExpPoly : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤ Real.exp (Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ)))
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_bcap : 2 * mwuK0 C_lsst * C_N ^ 6 + 2 ≤ C_poly ∧ 11 ≤ C_poly) :
    (concreteBCap C_lsst Ψ M₀ N₀ hM₀1 : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  exact (asymp_bcap_bound_strong C_lsst C_ψ C_N C_poly hCψ hCN hM₀1 Ψ hlogN hΨ
    hExpPoly hPoly_LL hCpoly_bcap).trans (exp_23_24_mono_LL (by linarith) hM₀1)

/-- The integer bucket cap has the same subpolynomial scale as the real bound. -/
lemma asymp_bucketCap_bound (C_lsst C_ψ C_N C_poly : ℝ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    {M₀ N₀ : ℕ} (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    (hlogN : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2))
    (hΨ : alg2PsiGame Ψ M₀ ≤
      Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hExpPoly : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤ Real.exp (Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ)))
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_bcap : 2 * mwuK0 (8192 * max 1 C_lsst) * C_N ^ 6 + 2 ≤ C_poly ∧ 11 ≤ C_poly) :
    (concreteBucketCap ⌈C_lsst⌉₊ ⌈Ψ⌉₊ (concreteChainParams M₀ hM₀1).k
      (concreteChainParams M₀ hM₀1).d N₀ : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  let L := Real.log ((M₀ : ℝ) + 2)
  let A := L ^ (23 / 24 : ℝ) * Real.log (L + 2)
  have hA : 0 ≤ A := by
    have hL := one_le_log_add_two_of_one hM₀1
    dsimp [A, L] at *
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith))
  have hreal := asymp_bcap_bound_strong (8192 * max 1 C_lsst) C_ψ C_N C_poly
    hCψ hCN hM₀1 Ψ hlogN hΨ hExpPoly hPoly_LL hCpoly_bcap
  have hfive : (5 : ℝ) ≤ Real.exp A := by
    simpa [A, L] using hPoly_LL 5 0 (by norm_num) (by linarith [hCpoly_bcap.2]) (by norm_num)
  have hlarge : 1 ≤ Real.exp ((2 + C_ψ) * A) :=
    Real.one_le_exp (mul_nonneg (by linarith) hA)
  have hcap := concreteBucketCap_le_twice_bcap C_lsst Ψ M₀ N₀ hM₀1
  have hcast : (concreteBucketCap ⌈C_lsst⌉₊ ⌈Ψ⌉₊ (concreteChainParams M₀ hM₀1).k
      (concreteChainParams M₀ hM₀1).d N₀ : ℝ) ≤ (2 * (concreteBCap (8192 * max 1 C_lsst) Ψ M₀ N₀ hM₀1 : ℝ) + 3) := by
    exact_mod_cast hcap
  refine hcast.trans ?_
  change _ ≤ Real.exp ((3 + C_ψ) * L ^ (23 / 24 : ℝ) * Real.log (L + 2))
  rw [show (3 + C_ψ) * L ^ (23 / 24 : ℝ) * Real.log (L + 2) =
    A + (2 + C_ψ) * A by dsimp [A]; ring, Real.exp_add]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hfive (Real.exp_pos _).le)
  have hreal' : (concreteBCap (8192 * max 1 C_lsst) Ψ M₀ N₀ hM₀1 : ℝ) ≤
      Real.exp ((2 + C_ψ) * A) := by
    simpa only [A, L, mul_assoc] using hreal
  linarith

private lemma asymp_uc_uh_d_bounds
    {C_lsst C_sp K_s K_t C_D C_poly : ℝ}
    (hKs : 0 ≤ K_s) (hCD : 0 ≤ C_D)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap D_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 22 * (K_s + 1) ≤ C_poly)
    (hDcap : (D_cap : ℝ) ≤
      Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hE82Len_le : coreE82Len (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) ≤
      Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hNRoot_le : coreNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (260 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hLam_le : coreLambdaS (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    ucRatioHi E (M₀ ^ 2) ≤ Real.exp ((C_D + 2) * L ^ (23 / 24 : ℝ) * LL) ∧
    coreBucketRecUH E.L (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((288 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    coreBucketRecD E.L (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((359 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E L LL
  let M₂ := M₀ ^ 2
  let Pb := params M₂
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hPb_spec := hp_spec M₂
  have hPb_γℓ_nn : 0 ≤ Pb.γ_ℓ := by linarith [Pb.hγ_ℓ]
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
  have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hConst : ∀ A : ℝ, 0 ≤ A → A ≤ C_poly →
      A ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := fun A hA0 hAC => by
    simpa using hPoly_LL A 0 hA0 hAC (by norm_num)
  have h2e := hConst 2 (by norm_num) (by linarith [hCpoly_ge.1])
  have hAdd : ∀ {x y c₁ c₂ : ℝ}, 0 ≤ c₁ → 0 ≤ c₂ →
      x ≤ Real.exp (c₁ * L ^ (23 / 24 : ℝ) * LL) →
      y ≤ Real.exp (c₂ * L ^ (23 / 24 : ℝ) * LL) →
      x + y ≤ Real.exp ((c₁ + c₂ + 1) * L ^ (23 / 24 : ℝ) * LL) := fun hc1 hc2 hx hy =>
    add_exp_23_24_LL hc1 hc2 hLa23_nn (by linarith) h2e hx hy
  have h12Ks : 12 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    hConst (12 * K_s) (by positivity) (by linarith [hCpoly_ge.2])
  have h6Ks : 6 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    le_trans (by linarith) h12Ks
  have hUC_le : ucRatioHi E M₂ ≤ Real.exp ((C_D + 2) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold ucRatioHi
    have hd_r : (E.d_fn M₂ : ℝ) = (D_cap : ℝ) := rfl
    have hc1 : E.c_n = 1 := rfl
    have hM2_eq : (M₂ : ℝ) = (M₀ : ℝ) ^ 2 := by push_cast [M₂]; rfl
    have hlog_c : Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2) ≤ 2 * L := by
      rw [hc1, one_mul]
      have hle : ((M₂ : ℝ) + 1) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by rw [hM2_eq]; nlinarith only [hM0_nn]
      calc Real.log (((M₂ : ℝ) + 1) + 2)
          ≤ Real.log (((M₀ : ℝ) + 2) ^ 2) := Real.log_le_log (by positivity) hle
        _ = 2 * L := by rw [Real.log_pow]; norm_num [L]
    have hlog_nn : 0 ≤ Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2) :=
      Real.log_nonneg (by change 1 ≤ 1 * ((M₂ : ℝ) + 1) + 2; linarith [Nat.cast_nonneg (α := ℝ) M₂])
    have h56 : 1 + 56 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 ≤ 225 * L ^ 2 := by
      have hsq := pow_le_pow_left₀ hlog_nn hlog_c 2
      have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
      nlinarith only [hsq, this]
    have h225 := le_trans h56 (hPoly_LL 225 2 (by norm_num) (by linarith [hCpoly_ge.1]) (by norm_num))
    have hsum := hAdd hCD zero_le_one hDcap h225
    rw [show C_D + 1 + 1 = C_D + 2 by ring] at hsum
    rw [hd_r, add_assoc]
    exact hsum
  have hEL_eq : E.L = chosenL M₂ := rfl
  have hL_E_le : (E.L : ℝ) ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact le_trans (by linarith) hL_add1_le
  have hnr_le : coreNRoot E.L M₂ ≤ Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hNRoot_le
  have hE82_le : coreE82Len E.L Pb ≤ Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hE82Len_le
  have hnr_nn : 0 ≤ coreNRoot E.L M₂ := by unfold coreNRoot; positivity
  have hlam_nn : 0 ≤ coreLambdaS Pb M₂ := by linarith [coreLambdaS_ge_one Pb M₂]
  have hUH_le : coreBucketRecUH E.L Pb M₂ ≤ Real.exp ((288 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold coreBucketRecUH
    rw [hPb_spec.1]
    have hprod : 12 * (E.L : ℝ) * coreNRoot E.L M₂ * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ ≤
        Real.exp ((286 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have h1 : 12 * (E.L : ℝ) * coreNRoot E.L M₂ * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ =
          (E.L : ℝ) * coreNRoot E.L M₂ * (12 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂ := by ring
      rw [h1]
      calc (E.L : ℝ) * coreNRoot E.L M₂ * (12 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂
          ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((286 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := hAdd zero_le_one (by positivity) h2e hprod
    exact le_trans hsum (exp_23_24_mono_LL (by linarith) hM₀1)
  have hD_le : coreBucketRecD E.L Pb M₂ ≤ Real.exp ((359 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold coreBucketRecD
    rw [hPb_spec.1]
    have h1_le : (1 : ℝ) ≤ Real.exp (0 * L ^ (23 / 24 : ℝ) * LL) := by simp
    have h3g : (3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1 ≤
        Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      change coreE82Len E.L Pb + 1 ≤ _
      rw [show (73 + 24 * C_sp : ℝ) = (72 + 24 * C_sp) + 0 + 1 by ring]
      exact hAdd (by positivity) le_rfl hE82_le h1_le
    have h3g_nn : 0 ≤ (3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1 := by positivity
    have heq : 6 * (E.L : ℝ) * coreNRoot E.L M₂ * K_s * Pb.γ_ℓ *
        ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * coreLambdaS Pb M₂ =
        (E.L : ℝ) * coreNRoot E.L M₂ * (6 * K_s) * Pb.γ_ℓ *
          ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * coreLambdaS Pb M₂ := by ring
    rw [heq]
    calc (E.L : ℝ) * coreNRoot E.L M₂ * (6 * K_s) * Pb.γ_ℓ *
            ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * coreLambdaS Pb M₂
        ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((359 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact ⟨hUC_le, hUH_le, hD_le⟩

private lemma asymp_gammaL_and_recEnv
    {C_lsst C_sp K_s K_t C_D C_ψ C_poly : ℝ}
    (hKs : 0 ≤ K_s) (hCD : 0 ≤ C_D) (_hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap D_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 22 * (K_s + 1) ≤ C_poly)
    (hDcap : (D_cap : ℝ) ≤
      Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hBcap : (B_cap : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hE82Len_le : coreE82Len (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) ≤
      Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hLam_le : coreLambdaS (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp)
    (hUC_le : ucRatioHi (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap) (M₀ ^ 2) ≤
      Real.exp ((C_D + 2) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hUH_le : coreBucketRecUH (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((288 + 4 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hD_le : coreBucketRecD (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((359 + 28 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap
    let C_B := 3 + C_ψ
    let C_rec := 950 + 240 * C_sp + 2 * C_B + C_D
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    gammaLEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) ∧
    recEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec L LL
  let M₂ := M₀ ^ 2
  let Pb := params M₂
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hPb_spec := hp_spec M₂
  have hPb_γℓ_nn : 0 ≤ Pb.γ_ℓ := by linarith [Pb.hγ_ℓ]
  have hKs_pb : 0 ≤ Pb.K_s := Pb.hK_s
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
  have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hConst : ∀ A : ℝ, 0 ≤ A → A ≤ C_poly →
      A ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := fun A hA0 hAC => by
    simpa using hPoly_LL A 0 hA0 hAC (by norm_num)
  have h2e := hConst 2 (by norm_num) (by linarith [hCpoly_ge.1])
  have hAdd : ∀ {x y c₁ c₂ : ℝ}, 0 ≤ c₁ → 0 ≤ c₂ →
      x ≤ Real.exp (c₁ * L ^ (23 / 24 : ℝ) * LL) →
      y ≤ Real.exp (c₂ * L ^ (23 / 24 : ℝ) * LL) →
      x + y ≤ Real.exp ((c₁ + c₂ + 1) * L ^ (23 / 24 : ℝ) * LL) := fun hc1 hc2 hx hy =>
    add_exp_23_24_LL hc1 hc2 hLa23_nn (by linarith) h2e hx hy
  have hBfn_le : (E.B_fn M₂ : ℝ) ≤ Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) := by
    change ((max 1 B_cap : ℕ) : ℝ) ≤ _
    by_cases h1 : 1 ≤ B_cap
    · rw [max_eq_right h1]; exact hBcap
    · rw [max_eq_left (Nat.le_of_not_ge h1)]; norm_num
      exact mul_nonneg (mul_nonneg (add_nonneg (by norm_num) _hCψ) hLa23_nn) (by linarith [hLL1])
  have hEL_eq : E.L = chosenL M₂ := rfl
  have hE82_le : coreE82Len E.L Pb ≤ Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hE82Len_le
  have hL1_E_le : (E.L : ℝ) + 1 ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hL_add1_le
  have h22Ks : 22 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    hConst (22 * K_s) (by positivity) (by linarith [hCpoly_ge.2])
  have h11Ks : 11 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    le_trans (by linarith) h22Ks
  have hlam_nn : 0 ≤ coreLambdaS Pb M₂ := by linarith [coreLambdaS_ge_one Pb M₂]
  have hGammaL_le : gammaLEnv E M₂ ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
    unfold gammaLEnv
    change max (coreE82Len E.L Pb)
      (11 * (((E.L : ℝ) + 1) * Pb.K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ *
        (E.B_fn M₂ : ℝ) * (2 * (E.d_fn M₂ : ℝ) + 190) + 115)) ≤ _
    rw [hPb_spec.1]
    have hD_rhs : 2 * (E.d_fn M₂ : ℝ) + 190 ≤ Real.exp ((C_D + 3) * L ^ (23 / 24 : ℝ) * LL) := by
      have hd_r : (E.d_fn M₂ : ℝ) = (D_cap : ℝ) := rfl
      rw [hd_r]
      have h2D : 2 * (D_cap : ℝ) ≤ Real.exp ((C_D + 1) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * (D_cap : ℝ) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp (C_D * L ^ (23 / 24 : ℝ) * LL) := mul_le_mul h2e hDcap (Nat.cast_nonneg _) (by positivity)
          _ = Real.exp ((C_D + 1) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      have h190 := hConst 190 (by norm_num) (by linarith [hCpoly_ge.1])
      rw [show C_D + 3 = (C_D + 1) + 1 + 1 by ring]
      exact hAdd (by positivity) zero_le_one h2D h190
    have hB_nn : 0 ≤ (E.B_fn M₂ : ℝ) := Nat.cast_nonneg _
    have hD_nn : 0 ≤ 2 * (E.d_fn M₂ : ℝ) + 190 := by positivity
    have hmain : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ * (E.B_fn M₂ : ℝ) *
          (2 * (E.d_fn M₂ : ℝ) + 190)) ≤
        Real.exp ((29 + 4 * C_sp + C_B + C_D) * L ^ (23 / 24 : ℝ) * LL) := by
      have heq : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ * (E.B_fn M₂ : ℝ) *
          (2 * (E.d_fn M₂ : ℝ) + 190)) =
          ((E.L : ℝ) + 1) * (11 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂ * (E.B_fn M₂ : ℝ) *
            (2 * (E.d_fn M₂ : ℝ) + 190) := by ring
      rw [heq]
      calc ((E.L : ℝ) + 1) * (11 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂ * (E.B_fn M₂ : ℝ) *
              (2 * (E.d_fn M₂ : ℝ) + 190)
          ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) * Real.exp ((C_D + 3) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((29 + 4 * C_sp + C_B + C_D) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h1265 : (11 * 115 : ℝ) ≤ Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by
      have h1k := hConst 1000 (by norm_num) hCpoly_ge.1
      calc (11 * 115 : ℝ) ≤ 2 * 1000 := by norm_num
        _ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
    have heq2 : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ *
        (E.B_fn M₂ : ℝ) * (2 * (E.d_fn M₂ : ℝ) + 190) + 115) =
        11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ *
          (E.B_fn M₂ : ℝ) * (2 * (E.d_fn M₂ : ℝ) + 190)) + 11 * 115 := by ring
    refine max_le (le_trans hE82_le (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)) ?_
    rw [heq2]
    exact le_trans (hAdd (by positivity) (by norm_num) hmain h1265)
      (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)
  have hRecEnv_le : recEnv E M₂ ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
    unfold recEnv
    change (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
        2 * coreBucketRecD E.L Pb M₂) * (2 * ucRatioHi E M₂) +
      22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * Pb.K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ +
      7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 ≤ _
    rw [hPb_spec.1]
    have hE82_nn : 0 ≤ coreE82Len E.L Pb := by
      unfold coreE82Len; exact mul_nonneg (by positivity) (pow_nonneg hPb_γℓ_nn _)
    have hnr_nn : 0 ≤ coreNRoot E.L M₂ := by unfold coreNRoot; positivity
    have hUH_nn : 0 ≤ coreBucketRecUH E.L Pb M₂ := by
      unfold coreBucketRecUH
      exact add_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hnr_nn) hKs_pb) hPb_γℓ_nn) hlam_nn)
    have hD_nn : 0 ≤ coreBucketRecD E.L Pb M₂ := by
      unfold coreBucketRecD
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hnr_nn) hKs_pb) hPb_γℓ_nn) (by positivity)) hlam_nn
    have h32 : 3 + 2 * coreE82Len E.L Pb ≤ Real.exp ((75 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have h3e := hConst 3 (by norm_num) (by linarith [hCpoly_ge.1])
      have h2l : 2 * coreE82Len E.L Pb ≤ Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * coreE82Len E.L Pb ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
          _ = Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      exact le_trans (hAdd zero_le_one (by positivity) h3e h2l) (exp_23_24_mono_LL (by linarith) hM₀1)
    have hterm1_mid : (3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
        2 * coreBucketRecD E.L Pb M₂ ≤
        Real.exp ((724 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have ha : (3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ ≤
          Real.exp ((363 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc (3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂
            ≤ Real.exp ((75 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((288 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← hEL_eq] at hUH_le; gcongr
          _ = Real.exp ((363 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      have hb : 2 * coreBucketRecD E.L Pb M₂ ≤ Real.exp ((360 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * coreBucketRecD E.L Pb M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((359 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← hEL_eq] at hD_le; gcongr
          _ = Real.exp ((360 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      exact le_trans (hAdd (by positivity) (by positivity) ha hb) (exp_23_24_mono_LL (by linarith) hM₀1)
    have hterm1 : (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
        2 * coreBucketRecD E.L Pb M₂) * (2 * ucRatioHi E M₂) ≤
        Real.exp ((C_B + 727 + 56 * C_sp + C_D) * L ^ (23 / 24 : ℝ) * LL) := by
      have huc_nn : 0 ≤ ucRatioHi E M₂ := by unfold ucRatioHi; positivity
      have h2UC : 2 * ucRatioHi E M₂ ≤ Real.exp ((C_D + 3) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * ucRatioHi E M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((C_D + 2) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
          _ = Real.exp ((C_D + 3) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      have hmid_nn : 0 ≤ (3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
          2 * coreBucketRecD E.L Pb M₂ := add_nonneg (mul_nonneg (by positivity) hUH_nn) (by positivity)
      calc (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
              2 * coreBucketRecD E.L Pb M₂) * (2 * ucRatioHi E M₂)
          ≤ Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp ((724 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp ((C_D + 3) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((C_B + 727 + 56 * C_sp + C_D) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hterm2 : 22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ ≤
        Real.exp ((C_B + 26 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have heq : 22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ =
          (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * (22 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂ := by ring
      rw [heq]
      calc (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * (22 * K_s) * Pb.γ_ℓ * coreLambdaS Pb M₂
          ≤ Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) * Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((C_B + 26 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hterm3 : 7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 ≤
        Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
      have hc1 : E.c_n = 1 := rfl
      have hM2_eq : (M₂ : ℝ) = (M₀ : ℝ) ^ 2 := by push_cast [M₂]; rfl
      rw [hc1, one_mul]
      have hle : ((M₂ : ℝ) + 1) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by rw [hM2_eq]; nlinarith only [hM0_nn]
      have hlog_c : Real.log (((M₂ : ℝ) + 1) + 2) ≤ 2 * L := by
        calc Real.log (((M₂ : ℝ) + 1) + 2)
            ≤ Real.log (((M₀ : ℝ) + 2) ^ 2) := Real.log_le_log (by positivity) hle
          _ = 2 * L := by rw [Real.log_pow]; norm_num [L]
      have hlog_nn : 0 ≤ Real.log (((M₂ : ℝ) + 1) + 2) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₂])
      have hsq := pow_le_pow_left₀ hlog_nn hlog_c 2
      have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
      have h7_le : 7 + 224 * (Real.log (((M₂ : ℝ) + 1) + 2)) ^ 2 ≤ 903 * L ^ 2 := by nlinarith only [hsq, hL2]
      exact le_trans h7_le (hPoly_LL 903 2 (by norm_num) (by linarith [hCpoly_ge.1]) (by norm_num))
    have h12 := hAdd (by positivity) (by positivity) hterm1 hterm2
    have hall := hAdd (by positivity) zero_le_one h12 hterm3
    rw [show (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
          2 * coreBucketRecD E.L Pb M₂) * (2 * ucRatioHi E M₂) +
        22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂ +
        7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 =
        ((E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * coreBucketRecUH E.L Pb M₂ +
          2 * coreBucketRecD E.L Pb M₂) * (2 * ucRatioHi E M₂) +
          22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * coreLambdaS Pb M₂) +
        (7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2) by ring]
    exact le_trans hall (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)
  exact ⟨hGammaL_le, hRecEnv_le⟩

private lemma asymp_enc_cost_bounds
    {C_lsst C_sp K_s K_t C_D C_ψ C_poly : ℝ}
    (hKt : 0 ≤ K_t) (hCD : 0 ≤ C_D) (_hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap D_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 2 * K_t + 2 ≤ C_poly)
    (hDcap : (D_cap : ℝ) ≤
      Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hEL_le : coreE_L (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) ≤
      Real.exp ((432 + 114 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hNRoot_le : coreNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (260 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp)
    (hGammaL_le : gammaLEnv (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap) (M₀ ^ 2) ≤
      Real.exp ((950 + 240 * C_sp + 2 * (3 + C_ψ) + C_D) *
        Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hRecEnv_le : recEnv (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap) (M₀ ^ 2) ≤
      Real.exp ((950 + 240 * C_sp + 2 * (3 + C_ψ) + C_D) *
        Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap
    let C_B := 3 + C_ψ
    let C_rec := 950 + 240 * C_sp + 2 * C_B + C_D
    let C_cost := 1500 + 360 * C_sp + C_D
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    recBase E (M₀ ^ 2) * costMult E (M₀ ^ 2) ≤
      Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec C_cost L LL
  let M₂ := M₀ ^ 2
  let Pb := params M₂
  have hPb_spec := hp_spec M₂
  have hPb_γℓ_nn : 0 ≤ Pb.γ_ℓ := by linarith [Pb.hγ_ℓ]
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
  have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hConst : ∀ A : ℝ, 0 ≤ A → A ≤ C_poly →
      A ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := fun A hA0 hAC => by
    simpa using hPoly_LL A 0 hA0 hAC (by norm_num)
  have h2e := hConst 2 (by norm_num) (by linarith [hCpoly_ge.1])
  have hAdd : ∀ {x y c₁ c₂ : ℝ}, 0 ≤ c₁ → 0 ≤ c₂ →
      x ≤ Real.exp (c₁ * L ^ (23 / 24 : ℝ) * LL) →
      y ≤ Real.exp (c₂ * L ^ (23 / 24 : ℝ) * LL) →
      x + y ≤ Real.exp ((c₁ + c₂ + 1) * L ^ (23 / 24 : ℝ) * LL) := fun hc1 hc2 hx hy =>
    add_exp_23_24_LL hc1 hc2 hLa23_nn (by linarith) h2e hx hy
  have hEL_eq : E.L = chosenL M₂ := rfl
  have hL_E_le : (E.L : ℝ) ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact le_trans (by linarith) hL_add1_le
  have hL1_E_le : (E.L : ℝ) + 1 ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hL_add1_le
  have hEL_len_le : coreE_L E.L Pb ≤ Real.exp ((432 + 114 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hEL_le
  have hnr_le : coreNRoot E.L M₂ ≤ Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hNRoot_le
  have hEncEnv_le : encEnv E M₂ ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold encEnv
    have hmax_r := max_le hGammaL_le hRecEnv_le
    have hlog_bd : Real.log ((M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2) ≤
        Real.exp ((C_rec + 2) * L ^ (23 / 24 : ℝ) * LL) := by
      have hrec_ge4 := recEnv_ge_four E M₂
      have hprod : (M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2 ≤ (1 + recEnv E M₂) * ((M₂ : ℝ) + 2) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) M₂]
      have hlog1 : Real.log ((M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2) ≤
          Real.log (1 + recEnv E M₂) + Real.log ((M₂ : ℝ) + 2) := by
        calc Real.log ((M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2)
            ≤ Real.log ((1 + recEnv E M₂) * ((M₂ : ℝ) + 2)) := Real.log_le_log (by positivity) hprod
          _ = Real.log (1 + recEnv E M₂) + Real.log ((M₂ : ℝ) + 2) := Real.log_mul (by linarith) (by positivity)
      have hlog_rec : Real.log (1 + recEnv E M₂) ≤ recEnv E M₂ := by
        linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + recEnv E M₂)]
      have h2L_exp : Real.log ((M₂ : ℝ) + 2) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
        have h21 := hPoly_LL 2 1 (by norm_num) (by linarith [hCpoly_ge.1]) (by norm_num)
        rw [pow_one] at h21
        exact le_trans (log_sq_add_two_le_double M₀) h21
      have hsum_rec := hAdd (by positivity) zero_le_one (le_trans hlog_rec hRecEnv_le) h2L_exp
      rw [show C_rec + 1 + 1 = C_rec + 2 by ring] at hsum_rec
      linarith only [hlog1, hsum_rec]
    have h20_le := hConst 20 (by norm_num) (by linarith [hCpoly_ge.1])
    have hmax_nn : 0 ≤ max (gammaLEnv E M₂) (recEnv E M₂) :=
      le_max_of_le_right (le_trans (by norm_num : (0 : ℝ) ≤ 4) (recEnv_ge_four E M₂))
    have hlog_nn : 0 ≤ Real.log ((M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2) := by
      have := recEnv_ge_four E M₂; exact Real.log_nonneg (by nlinarith)
    calc 20 * max (gammaLEnv E M₂) (recEnv E M₂) * Real.log ((M₂ : ℝ) + recEnv E M₂ * (M₂ : ℝ) + 2)
        ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((C_rec + 2) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hCostMult_le : costMult E M₂ ≤ Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) := by
    unfold costMult
    change max 1 (coreE_L E.L Pb * ((E.d_fn M₂ : ℝ) + 1) *
      (Pb.K_t * (2 + Pb.γ_ℓ ^ 2) + 1) * max 1 ((E.L : ℝ) * coreNRoot E.L M₂) * ((E.L : ℝ) + 1)) ≤ _
    rw [hPb_spec.2.2.1]
    have hD1_le : (E.d_fn M₂ : ℝ) + 1 ≤ Real.exp ((C_D + 1) * L ^ (23 / 24 : ℝ) * LL) := by
      have hd_r : (E.d_fn M₂ : ℝ) = (D_cap : ℝ) := rfl
      rw [hd_r, show C_D + 1 = C_D + 0 + 1 by ring]
      exact hAdd hCD le_rfl hDcap (by simp)
    have hKt_part : K_t * (2 + Pb.γ_ℓ ^ 2) + 1 ≤
        Real.exp ((8 * C_sp + 4) * L ^ (23 / 24 : ℝ) * LL) := by
      have hsq_le : Pb.γ_ℓ ^ 2 ≤ Real.exp (8 * C_sp * L ^ (23 / 24 : ℝ) * LL) := by
        calc Pb.γ_ℓ ^ 2 ≤ (Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL)) ^ 2 :=
              pow_le_pow_left₀ hPb_γℓ_nn hPb_γℓ_le 2
          _ = Real.exp (8 * C_sp * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_nat_mul]; congr 1; ring
      have h2g := hAdd zero_le_one (by positivity) h2e hsq_le
      have hKt_e := hConst K_t hKt (by linarith [hCpoly_ge.2])
      have h2g_nn : 0 ≤ 2 + Pb.γ_ℓ ^ 2 := by positivity
      have hprod : K_t * (2 + Pb.γ_ℓ ^ 2) ≤ Real.exp ((8 * C_sp + 3) * L ^ (23 / 24 : ℝ) * LL) := by
        calc K_t * (2 + Pb.γ_ℓ ^ 2) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((1 + 8 * C_sp + 1) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
          _ = Real.exp ((8 * C_sp + 3) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      rw [show (8 : ℝ) * C_sp + 4 = (8 * C_sp + 3) + 0 + 1 by ring]
      exact hAdd (by positivity) le_rfl hprod (by simp)
    have hLnr : max 1 ((E.L : ℝ) * coreNRoot E.L M₂) ≤ Real.exp (284 * L ^ (23 / 24 : ℝ) * LL) := by
      have hnr_nn : 0 ≤ coreNRoot E.L M₂ := by unfold coreNRoot; positivity
      refine max_le (Real.one_le_exp (by positivity)) ?_
      calc (E.L : ℝ) * coreNRoot E.L M₂ ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (260 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp (284 * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
    have hEL_nn : 0 ≤ coreE_L E.L Pb := by
      unfold coreE_L
      exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith [Pb.hγ_c]) _)) (pow_nonneg hPb_γℓ_nn _)
    have hD1_nn : 0 ≤ (E.d_fn M₂ : ℝ) + 1 := by positivity
    have hKt_nn : 0 ≤ K_t * (2 + Pb.γ_ℓ ^ 2) + 1 := by positivity
    have hLnr_nn : 0 ≤ max 1 ((E.L : ℝ) * coreNRoot E.L M₂) := by positivity
    refine max_le (Real.one_le_exp (by positivity)) ?_
    calc coreE_L E.L Pb * ((E.d_fn M₂ : ℝ) + 1) * (K_t * (2 + Pb.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * coreNRoot E.L M₂) * ((E.L : ℝ) + 1)
        ≤ Real.exp ((432 + 114 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((C_D + 1) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((8 * C_sp + 4) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (284 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((745 + 122 * C_sp + C_D) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) :=
          exp_23_24_mono_LL (by dsimp only [C_cost]; linarith) hM₀1
  have hrb : recBase E M₂ ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) :=
    max_le (le_trans hRecEnv_le (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1))
      hEncEnv_le
  have hrb_nn : 0 ≤ recBase E M₂ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 4) (le_trans (recEnv_ge_four E M₂) (le_max_left _ _))
  have hcm_nn : 0 ≤ costMult E M₂ := by linarith [costMult_ge_one E M₂]
  calc recBase E M₂ * costMult E M₂
      ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) *
        Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) := by gcongr
    _ = Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring

lemma asymp_gammaL_recEnv_bounds
    {C_lsst C_sp K_s K_t C_D C_ψ C_poly : ℝ}
    (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap D_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 22 * (K_s + 1) ≤ C_poly ∧ 2 * K_t + 2 ≤ C_poly)
    (hDcap : (D_cap : ℝ) ≤
      Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hBcap : (B_cap : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hSec8 :
      coreE82Len (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) ≤
        Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      coreE_L (chosenL (M₀ ^ 2)) (params (M₀ ^ 2)) ≤
        Real.exp ((432 + 114 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      (params (M₀ ^ 2)).γ_ℓ ≤
        Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
        Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      coreNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
        Real.exp (260 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      coreLambdaS (params (M₀ ^ 2)) (M₀ ^ 2) ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap D_cap
    let C_B := 3 + C_ψ
    let C_rec := 950 + 240 * C_sp + 2 * C_B + C_D
    let C_cost := 1500 + 360 * C_sp + C_D
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    gammaLEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) ∧
    recBase E (M₀ ^ 2) * costMult E (M₀ ^ 2) ≤
      Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec C_cost L LL
  rcases hSec8 with ⟨hE82Len_le, hEL_le, hPb_γℓ_le, hL_add1_le, hNRoot_le, hLam_le⟩
  have h1 := asymp_uc_uh_d_bounds (C_lsst := C_lsst) (B_cap := B_cap) hKs hCD params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.1⟩ hDcap hE82Len_le hPb_γℓ_le hL_add1_le hNRoot_le hLam_le hCsp_nn
  have h2 := asymp_gammaL_and_recEnv (C_lsst := C_lsst) hKs hCD hCψ params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.1⟩ hDcap hBcap hE82Len_le hPb_γℓ_le hL_add1_le hLam_le hCsp_nn
    h1.1 h1.2.1 h1.2.2
  have h3 := asymp_enc_cost_bounds (C_lsst := C_lsst) hKt hCD hCψ params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.2⟩ hDcap hEL_le hPb_γℓ_le hL_add1_le hNRoot_le hCsp_nn
    h2.1 h2.2
  exact ⟨h2.1, h3⟩

end ModularAsymp

end MinCostFlow.Chain