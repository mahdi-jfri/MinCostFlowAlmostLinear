module

public import MinCostFlow.Chain.Ordered.ConcreteDefs
public import MinCostFlow.Chain.ConcreteAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modular Asymptotics for the Ordered Bundle Chain

Proves modular degree-free asymptotic bounds showing every Section 8 expander term,
`bundleNRoot`, `bundleLambdaS`, `bundleGammaLEnv`, `bundleRecEnv`, `bundleEncEnv`, and
`bundleCostMult` stays within `exp (O(log^{23/24} (M₀ + 2) * log (log (M₀ + 2) + 2)))` without any
degree-cap parameter `C_D` or `D_cap`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander MinCostFlow.Bundle

section ModularAsymp

/-- Section 8 expander and bundle-population bounds at edge scale `M₂ = M₀ ^ 2`:
`coreE82Len`, `coreE_L`, `Pb.γ_ℓ`, `L_E + 1`, `bundleNRoot`, and `bundleLambdaS`. -/
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
    (hCpoly_118 : 118 ≤ C_poly) :
    let M₂ := M₀ ^ 2
    let Pb := params M₂
    let L_E := chosenL M₂
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    coreE82Len L_E Pb ≤ Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    coreE_L L_E Pb ≤ Real.exp ((432 + 114 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    Pb.γ_ℓ ≤ Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) ∧
    (L_E : ℝ) + 1 ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleNRoot L_E M₂ ≤ Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleLambdaS Pb M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
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
  have hNMax_le : (bundleNMax M₂ : ℝ) ≤ 114 * ((M₂ : ℝ) + 2) := by
    unfold bundleNMax; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M₂]
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
    have hNMax_le' : (bundleNMax M₂ : ℝ) ≤ 114 * ((M₂ : ℝ) + 2) ^ (1 : ℝ) := by
      simpa [Real.rpow_one] using hNMax_le
    have hnr := nRoot_le_exp (C_n := 114) (r_n := 1) (by norm_num) (by norm_num) hNMax_le'
    have h460 : Real.exp (2 * (2 * 114 + 1 : ℝ) * L ^ (23 / 24 : ℝ)) ≤
        Real.exp (460 * L ^ (23 / 24 : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by norm_num) hLa23_nn)
    unfold bundleNRoot
    exact le_trans hnr (le_trans (hExp_M2_mono (2 * 114 + 1) (by norm_num)) h460)
  · unfold bundleLambdaS
    rw [hPb_spec.2.1, pow_one]
    have hM2_eq : ((M₂ : ℝ)) = (M₀ : ℝ) ^ 2 := by push_cast [M₂]; rfl
    have harg : (bundleNMax M₂ : ℝ) + (M₂ : ℝ) + 2 ≤ 115 * ((M₀ : ℝ) + 2) ^ 2 := by
      have hm2 : (M₂ : ℝ) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by rw [hM2_eq]; nlinarith only [hM0_nn]
      have hbn : (bundleNMax M₂ : ℝ) = 114 * (M₂ : ℝ) + 2 := by
        unfold bundleNMax; push_cast; ring
      nlinarith only [hbn, hm2, hM0_nn]
    have hlog_arg : 1 + Real.log ((bundleNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤ 118 * L := by
      have hpos : 0 < (bundleNMax M₂ : ℝ) + (M₂ : ℝ) + 2 := by positivity
      have hlog_le : Real.log ((bundleNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤
          Real.log (115 * ((M₀ : ℝ) + 2) ^ 2) :=
        Real.log_le_log hpos harg
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (by positivity)), Real.log_pow] at hlog_le
      have hlog115 : Real.log 115 ≤ 115 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 115)]
      have hlog_le' : Real.log ((bundleNMax M₂ : ℝ) + (M₂ : ℝ) + 2) ≤ 115 + 2 * L := by
        have h2 : ((2 : ℕ) : ℝ) * Real.log ((M₀ : ℝ) + 2) = 2 * L := by norm_num [L]
        linarith only [hlog_le, hlog115, h2]
      linarith only [hlog_le', hL1]
    have h118 := hPoly 118 1 (by norm_num) hCpoly_118 (by norm_num)
    rw [pow_one] at h118
    exact le_trans hlog_arg h118

private lemma env_K_p_eq {K_s K_t : ℝ} (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    (m : ℕ) :
    (monoSparsifyParamsEnvelope params m).K_s = K_s ∧
    (monoSparsifyParamsEnvelope params m).p_s = 1 ∧
    (monoSparsifyParamsEnvelope params m).K_t = K_t ∧
    (monoSparsifyParamsEnvelope params m).p_t = 1 := by
  have hmem0 : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ m)
  have hne : (Finset.range (m + 1)).Nonempty := ⟨0, hmem0⟩
  exact ⟨le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).1.le)
      ((hp_spec 0).1.symm.le.trans (Finset.le_sup' (fun i => (params i).K_s) hmem0)),
    le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.1.le)
      ((hp_spec 0).2.1.symm.le.trans (Finset.le_sup' (fun i => (params i).p_s) hmem0)),
    le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.2.1.le)
      ((hp_spec 0).2.2.1.symm.le.trans (Finset.le_sup' (fun i => (params i).K_t) hmem0)),
    le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.2.2.le)
      ((hp_spec 0).2.2.2.symm.le.trans (Finset.le_sup' (fun i => (params i).p_t) hmem0))⟩

private lemma asymp_uc_uh_d_bounds
    {C_lsst C_sp K_s K_t C_poly : ℝ}
    (hKs : 0 ≤ K_s)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 11000 * (K_s + 1) ≤ C_poly)
    (hE82Len_le : coreE82Len (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) ≤
      Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (monoSparsifyParamsEnvelope params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hNRoot_le : bundleNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (460 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hLam_le : bundleLambdaS (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    bundleUCRatioHi E (M₀ ^ 2) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleBucketRecUH E.L (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((488 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleBucketRecD E.L (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((559 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E L LL
  let M₂ := M₀ ^ 2
  let Pb := monoSparsifyParamsEnvelope params M₂
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hPb_spec := env_K_p_eq params hp_spec M₂
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
  have hUC_le : bundleUCRatioHi E M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleUCRatioHi
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
    have h449 : 1 + 112 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 ≤ 449 * L ^ 2 := by
      have hsq := pow_le_pow_left₀ hlog_nn hlog_c 2
      have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
      nlinarith only [hsq, this]
    exact le_trans h449 (hPoly_LL 449 2 (by norm_num) (by linarith [hCpoly_ge.1]) (by norm_num))
  have hEL_eq : E.L = chosenL M₂ := rfl
  have hL_E_le : (E.L : ℝ) ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact le_trans (by linarith) hL_add1_le
  have hnr_le : bundleNRoot E.L M₂ ≤ Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hNRoot_le
  have hE82_le : coreE82Len E.L Pb ≤ Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hE82Len_le
  have hnr_nn : 0 ≤ bundleNRoot E.L M₂ := by unfold bundleNRoot; positivity
  have hlam_nn : 0 ≤ bundleLambdaS Pb M₂ := bundleParams_lambdaS_pos Pb M₂
  have hUH_le : bundleBucketRecUH E.L Pb M₂ ≤ Real.exp ((488 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleBucketRecUH
    rw [hPb_spec.1]
    have hprod : 12 * (E.L : ℝ) * bundleNRoot E.L M₂ * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ ≤
        Real.exp ((486 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have h1 : 12 * (E.L : ℝ) * bundleNRoot E.L M₂ * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ =
          (E.L : ℝ) * bundleNRoot E.L M₂ * (12 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂ := by ring
      rw [h1]
      calc (E.L : ℝ) * bundleNRoot E.L M₂ * (12 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂
          ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((486 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := hAdd zero_le_one (by positivity) h2e hprod
    exact le_trans hsum (exp_23_24_mono_LL (by linarith) hM₀1)
  have hD_le : bundleBucketRecD E.L Pb M₂ ≤ Real.exp ((559 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleBucketRecD
    rw [hPb_spec.1]
    have h1_le : (1 : ℝ) ≤ Real.exp (0 * L ^ (23 / 24 : ℝ) * LL) := by simp
    have h3g : (3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1 ≤
        Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      change coreE82Len E.L Pb + 1 ≤ _
      rw [show (73 + 24 * C_sp : ℝ) = (72 + 24 * C_sp) + 0 + 1 by ring]
      exact hAdd (by positivity) le_rfl hE82_le h1_le
    have h3g_nn : 0 ≤ (3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1 := by positivity
    have heq : 6 * (E.L : ℝ) * bundleNRoot E.L M₂ * K_s * Pb.γ_ℓ *
        ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * bundleLambdaS Pb M₂ =
        (E.L : ℝ) * bundleNRoot E.L M₂ * (6 * K_s) * Pb.γ_ℓ *
          ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * bundleLambdaS Pb M₂ := by ring
    rw [heq]
    calc (E.L : ℝ) * bundleNRoot E.L M₂ * (6 * K_s) * Pb.γ_ℓ *
            ((3 : ℝ) ^ E.L * Pb.γ_ℓ ^ (E.L + 1) + 1) * bundleLambdaS Pb M₂
        ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((559 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact ⟨hUC_le, hUH_le, hD_le⟩

private lemma asymp_gammaL_and_recEnv
    {C_lsst C_sp K_s K_t C_ψ C_poly : ℝ}
    (hKs : 0 ≤ K_s) (_hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 11000 * (K_s + 1) ≤ C_poly)
    (hBcap : (B_cap : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hE82Len_le : coreE82Len (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) ≤
      Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (monoSparsifyParamsEnvelope params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hLam_le : bundleLambdaS (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp)
    (hUC_le : bundleUCRatioHi (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap) (M₀ ^ 2) ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hUH_le : bundleBucketRecUH (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((488 + 4 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hD_le : bundleBucketRecD (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp ((559 + 28 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap
    let C_B := 3 + C_ψ
    let C_rec := 1200 + 240 * C_sp + 2 * C_B
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    bundleGammaLEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleRecEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec L LL
  let M₂ := M₀ ^ 2
  let Pb := monoSparsifyParamsEnvelope params M₂
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hPb_spec := env_K_p_eq params hp_spec M₂
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
  have h11kKs : 11000 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    hConst (11000 * K_s) (by positivity) (by linarith [hCpoly_ge.2])
  have h22Ks : 22 * K_s ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    le_trans (by linarith) h11kKs
  have hlam_nn : 0 ≤ bundleLambdaS Pb M₂ := bundleParams_lambdaS_pos Pb M₂
  have hGammaL_le : bundleGammaLEnv E M₂ ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleGammaLEnv bundleSizeFactor
    change max (coreE82Len E.L Pb)
      (11 * (((E.L : ℝ) + 1) * Pb.K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ *
        (E.B_fn M₂ : ℝ) * 1000 + 115)) ≤ _
    rw [hPb_spec.1]
    have hB_nn : 0 ≤ (E.B_fn M₂ : ℝ) := Nat.cast_nonneg _
    have hmain : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ *
          (E.B_fn M₂ : ℝ) * 1000) ≤
        Real.exp ((26 + 4 * C_sp + C_B) * L ^ (23 / 24 : ℝ) * LL) := by
      have heq : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ *
          (E.B_fn M₂ : ℝ) * 1000) =
          ((E.L : ℝ) + 1) * (11000 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂ * (E.B_fn M₂ : ℝ) := by ring
      rw [heq]
      calc ((E.L : ℝ) + 1) * (11000 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂ * (E.B_fn M₂ : ℝ)
          ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (4 * C_sp * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((26 + 4 * C_sp + C_B) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h1265 : (11 * 115 : ℝ) ≤ Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by
      have h1k := hConst 1000 (by norm_num) hCpoly_ge.1
      calc (11 * 115 : ℝ) ≤ 2 * 1000 := by norm_num
        _ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
    have heq2 : 11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ *
        (E.B_fn M₂ : ℝ) * 1000 + 115) =
        11 * (((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ *
          (E.B_fn M₂ : ℝ) * 1000) + 11 * 115 := by ring
    refine max_le (le_trans hE82_le (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)) ?_
    rw [heq2]
    exact le_trans (hAdd (by positivity) (by norm_num) hmain h1265)
      (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)
  have hRecEnv_le : bundleRecEnv E M₂ ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleRecEnv
    change (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
        2 * bundleBucketRecD E.L Pb M₂) * (2 * bundleUCRatioHi E M₂) +
      22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * Pb.K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ +
      7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 ≤ _
    rw [hPb_spec.1]
    have hE82_nn : 0 ≤ coreE82Len E.L Pb := by
      unfold coreE82Len; exact mul_nonneg (by positivity) (pow_nonneg hPb_γℓ_nn _)
    have hnr_nn : 0 ≤ bundleNRoot E.L M₂ := by unfold bundleNRoot; positivity
    have hUH_nn : 0 ≤ bundleBucketRecUH E.L Pb M₂ := (bundleParams_bucketRec_pos E.L Pb M₂).1
    have hD_nn : 0 ≤ bundleBucketRecD E.L Pb M₂ := (bundleParams_bucketRec_pos E.L Pb M₂).2.1
    have h32 : 3 + 2 * coreE82Len E.L Pb ≤ Real.exp ((75 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have h3e := hConst 3 (by norm_num) (by linarith [hCpoly_ge.1])
      have h2l : 2 * coreE82Len E.L Pb ≤ Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * coreE82Len E.L Pb ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((72 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
          _ = Real.exp ((73 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      exact le_trans (hAdd zero_le_one (by positivity) h3e h2l) (exp_23_24_mono_LL (by linarith) hM₀1)
    have hterm1_mid : (3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
        2 * bundleBucketRecD E.L Pb M₂ ≤
        Real.exp ((1124 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have ha : (3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ ≤
          Real.exp ((563 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc (3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂
            ≤ Real.exp ((75 + 24 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((488 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← hEL_eq] at hUH_le; gcongr
          _ = Real.exp ((563 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      have hb : 2 * bundleBucketRecD E.L Pb M₂ ≤ Real.exp ((560 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * bundleBucketRecD E.L Pb M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp ((559 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← hEL_eq] at hD_le; gcongr
          _ = Real.exp ((560 + 28 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      exact le_trans (hAdd (by positivity) (by positivity) ha hb) (exp_23_24_mono_LL (by linarith) hM₀1)
    have hterm1 : (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
        2 * bundleBucketRecD E.L Pb M₂) * (2 * bundleUCRatioHi E M₂) ≤
        Real.exp ((C_B + 1126 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have huc_nn : 0 ≤ bundleUCRatioHi E M₂ := by linarith [bundleUCRatioHi_ge_one E M₂]
      have h2UC : 2 * bundleUCRatioHi E M₂ ≤ Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by
        calc 2 * bundleUCRatioHi E M₂ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
              Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
          _ = Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      have hmid_nn : 0 ≤ (3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
          2 * bundleBucketRecD E.L Pb M₂ := add_nonneg (mul_nonneg (by positivity) hUH_nn) (by positivity)
      calc (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
              2 * bundleBucketRecD E.L Pb M₂) * (2 * bundleUCRatioHi E M₂)
          ≤ Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp ((1124 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (2 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp ((C_B + 1126 + 56 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hterm2 : 22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ ≤
        Real.exp ((C_B + 26 + 4 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
      have heq : 22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ =
          (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * (22 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂ := by ring
      rw [heq]
      calc (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * (22 * K_s) * Pb.γ_ℓ * bundleLambdaS Pb M₂
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
    rw [show (E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
          2 * bundleBucketRecD E.L Pb M₂) * (2 * bundleUCRatioHi E M₂) +
        22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂ +
        7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2 =
        ((E.B_fn M₂ : ℝ) * ((3 + 2 * coreE82Len E.L Pb) * bundleBucketRecUH E.L Pb M₂ +
          2 * bundleBucketRecD E.L Pb M₂) * (2 * bundleUCRatioHi E M₂) +
          22 * (E.B_fn M₂ : ℝ) * ((E.L : ℝ) + 1) * K_s * Pb.γ_ℓ * bundleLambdaS Pb M₂) +
        (7 + 224 * (Real.log (E.c_n * ((M₂ : ℝ) + 1) + 2)) ^ 2) by ring]
    exact le_trans hall (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1)
  exact ⟨hGammaL_le, hRecEnv_le⟩

private lemma asymp_enc_cost_bounds
    {C_lsst C_sp K_s K_t C_ψ C_poly : ℝ}
    (hKt : 0 ≤ K_t) (_hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 2 * K_t + 2 ≤ C_poly)
    (hEL_le : coreE_L (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) ≤
      Real.exp ((432 + 114 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hPb_γℓ_le : (monoSparsifyParamsEnvelope params (M₀ ^ 2)).γ_ℓ ≤
      Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hL_add1_le : ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
      Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hNRoot_le : bundleNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
      Real.exp (460 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp)
    (hGammaL_le : bundleGammaLEnv (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap) (M₀ ^ 2) ≤
      Real.exp ((1200 + 240 * C_sp + 2 * (3 + C_ψ)) *
        Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hRecEnv_le : bundleRecEnv (concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap) (M₀ ^ 2) ≤
      Real.exp ((1200 + 240 * C_sp + 2 * (3 + C_ψ)) *
        Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) * Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap
    let C_B := 3 + C_ψ
    let C_rec := 1200 + 240 * C_sp + 2 * C_B
    let C_cost := 1500 + 360 * C_sp
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2) ≤
      Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec C_cost L LL
  let M₂ := M₀ ^ 2
  let Pb := monoSparsifyParamsEnvelope params M₂
  have hPb_spec := env_K_p_eq params hp_spec M₂
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
  have hnr_le : bundleNRoot E.L M₂ ≤ Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) := by
    rw [hEL_eq]; exact hNRoot_le
  have hEncEnv_le : bundleEncEnv E M₂ ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleEncEnv
    have hmax_r := max_le hGammaL_le hRecEnv_le
    have hlog_bd : Real.log ((M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2) ≤
        Real.exp ((C_rec + 2) * L ^ (23 / 24 : ℝ) * LL) := by
      have hrec_ge4 := bundleRecEnv_ge_four E M₂
      have hprod : (M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2 ≤
          (1 + bundleRecEnv E M₂) * ((M₂ : ℝ) + 2) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) M₂]
      have hlog1 : Real.log ((M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2) ≤
          Real.log (1 + bundleRecEnv E M₂) + Real.log ((M₂ : ℝ) + 2) := by
        calc Real.log ((M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2)
            ≤ Real.log ((1 + bundleRecEnv E M₂) * ((M₂ : ℝ) + 2)) :=
              Real.log_le_log (by positivity) hprod
          _ = Real.log (1 + bundleRecEnv E M₂) + Real.log ((M₂ : ℝ) + 2) :=
              Real.log_mul (by linarith) (by positivity)
      have hlog_rec : Real.log (1 + bundleRecEnv E M₂) ≤ bundleRecEnv E M₂ := by
        linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + bundleRecEnv E M₂)]
      have h2L_exp : Real.log ((M₂ : ℝ) + 2) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
        have h21 := hPoly_LL 2 1 (by norm_num) (by linarith [hCpoly_ge.1]) (by norm_num)
        rw [pow_one] at h21
        exact le_trans (log_sq_add_two_le_double M₀) h21
      have hsum_rec := hAdd (by positivity) zero_le_one (le_trans hlog_rec hRecEnv_le) h2L_exp
      rw [show C_rec + 1 + 1 = C_rec + 2 by ring] at hsum_rec
      linarith only [hlog1, hsum_rec]
    have h20_le := hConst 20 (by norm_num) (by linarith [hCpoly_ge.1])
    have hmax_nn : 0 ≤ max (bundleGammaLEnv E M₂) (bundleRecEnv E M₂) :=
      le_max_of_le_right (le_trans (by norm_num : (0 : ℝ) ≤ 4) (bundleRecEnv_ge_four E M₂))
    have hlog_nn : 0 ≤ Real.log ((M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2) := by
      have := bundleRecEnv_ge_four E M₂; exact Real.log_nonneg (by nlinarith)
    calc 20 * max (bundleGammaLEnv E M₂) (bundleRecEnv E M₂) *
            Real.log ((M₂ : ℝ) + bundleRecEnv E M₂ * (M₂ : ℝ) + 2)
        ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) * Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((C_rec + 2) * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hCostMult_le : bundleCostMult E M₂ ≤ Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) := by
    unfold bundleCostMult
    change max 1 (coreE_L E.L Pb * (Pb.K_t * (2 + Pb.γ_ℓ ^ 2) + 1) *
      max 1 ((E.L : ℝ) * bundleNRoot E.L M₂) * ((E.L : ℝ) + 1)) ≤ _
    rw [hPb_spec.2.2.1]
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
    have hLnr : max 1 ((E.L : ℝ) * bundleNRoot E.L M₂) ≤ Real.exp (484 * L ^ (23 / 24 : ℝ) * LL) := by
      have hnr_nn : 0 ≤ bundleNRoot E.L M₂ := by unfold bundleNRoot; positivity
      refine max_le (Real.one_le_exp (by positivity)) ?_
      calc (E.L : ℝ) * bundleNRoot E.L M₂ ≤ Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) *
            Real.exp (460 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
        _ = Real.exp (484 * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
    have hEL_nn : 0 ≤ coreE_L E.L Pb := by
      unfold coreE_L
      exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith [Pb.hγ_c]) _)) (pow_nonneg hPb_γℓ_nn _)
    have hKt_nn : 0 ≤ K_t * (2 + Pb.γ_ℓ ^ 2) + 1 := by positivity
    have hLnr_nn : 0 ≤ max 1 ((E.L : ℝ) * bundleNRoot E.L M₂) := by positivity
    refine max_le (Real.one_le_exp (by positivity)) ?_
    calc coreE_L E.L Pb * (K_t * (2 + Pb.γ_ℓ ^ 2) + 1) *
          max 1 ((E.L : ℝ) * bundleNRoot E.L M₂) * ((E.L : ℝ) + 1)
        ≤ Real.exp ((432 + 114 * C_sp) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((8 * C_sp + 4) * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (484 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp (24 * L ^ (23 / 24 : ℝ) * LL) := by gcongr
      _ = Real.exp ((944 + 122 * C_sp) * L ^ (23 / 24 : ℝ) * LL) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) :=
          exp_23_24_mono_LL (by dsimp only [C_cost]; linarith) hM₀1
  have hrb : bundleRecBase E M₂ ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) :=
    max_le (le_trans hRecEnv_le (exp_23_24_mono_LL (by dsimp only [C_rec, C_B]; linarith) hM₀1))
      hEncEnv_le
  have hrb_nn : 0 ≤ bundleRecBase E M₂ :=
    le_trans (by norm_num : (0 : ℝ) ≤ 4) (le_trans (bundleRecEnv_ge_four E M₂) (le_max_left _ _))
  have hcm_nn : 0 ≤ bundleCostMult E M₂ := by linarith [bundleCostMult_ge_one E M₂]
  calc bundleRecBase E M₂ * bundleCostMult E M₂
      ≤ Real.exp ((2 * C_rec + 3) * L ^ (23 / 24 : ℝ) * LL) *
        Real.exp (C_cost * L ^ (23 / 24 : ℝ) * LL) := by gcongr
    _ = Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring

/-- Combined subpolynomial upper bounds on `bundleGammaLEnv` and `bundleRecBase * bundleCostMult`
at `M₀ ^ 2` for `concreteEnv`, with no degree-cap parameter. -/
lemma asymp_gammaL_recEnv_bounds
    {C_lsst C_sp K_s K_t C_ψ C_poly : ℝ}
    (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t) (hCψ : 0 ≤ C_ψ)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧ (params m).K_t = K_t ∧ (params m).p_t = 1)
    {M₀ B_cap : ℕ} (hM₀1 : 1 ≤ M₀)
    (hPoly_LL : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCpoly_ge : 1000 ≤ C_poly ∧ 11000 * (K_s + 1) ≤ C_poly ∧ 2 * K_t + 2 ≤ C_poly)
    (hBcap : (B_cap : ℝ) ≤
      Real.exp ((3 + C_ψ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hSec8 :
      coreE82Len (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) ≤
        Real.exp ((72 + 24 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      coreE_L (chosenL (M₀ ^ 2)) (monoSparsifyParamsEnvelope params (M₀ ^ 2)) ≤
        Real.exp ((432 + 114 * C_sp) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      (monoSparsifyParamsEnvelope params (M₀ ^ 2)).γ_ℓ ≤
        Real.exp (4 * C_sp * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      ((chosenL (M₀ ^ 2) : ℝ) + 1) ≤
        Real.exp (24 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      bundleNRoot (chosenL (M₀ ^ 2)) (M₀ ^ 2) ≤
        Real.exp (460 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
      bundleLambdaS (monoSparsifyParamsEnvelope params (M₀ ^ 2)) (M₀ ^ 2) ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hCsp_nn : 0 ≤ C_sp) :
    let E := concreteEnv C_lsst params (fun m => le_of_eq (hp_spec m).2.1)
      (fun m => le_of_eq (hp_spec m).2.2.2) M₀ B_cap
    let C_B := 3 + C_ψ
    let C_rec := 1200 + 240 * C_sp + 2 * C_B
    let C_cost := 1500 + 360 * C_sp
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    bundleGammaLEnv E (M₀ ^ 2) ≤ Real.exp (C_rec * L ^ (23 / 24 : ℝ) * LL) ∧
    bundleRecBase E (M₀ ^ 2) * bundleCostMult E (M₀ ^ 2) ≤
      Real.exp ((2 * C_rec + C_cost + 3) * L ^ (23 / 24 : ℝ) * LL) := by
  intro E C_B C_rec C_cost L LL
  rcases hSec8 with ⟨hE82Len_le, hEL_le, hPb_γℓ_le, hL_add1_le, hNRoot_le, hLam_le⟩
  have h1 := asymp_uc_uh_d_bounds (C_lsst := C_lsst) (B_cap := B_cap) hKs params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.1⟩ hE82Len_le hPb_γℓ_le hL_add1_le hNRoot_le hLam_le hCsp_nn
  have h2 := asymp_gammaL_and_recEnv (C_lsst := C_lsst) hKs hCψ params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.1⟩ hBcap hE82Len_le hPb_γℓ_le hL_add1_le hLam_le hCsp_nn
    h1.1 h1.2.1 h1.2.2
  have h3 := asymp_enc_cost_bounds (C_lsst := C_lsst) hKt hCψ params hp_spec
    hM₀1 hPoly_LL ⟨hCpoly_ge.1, hCpoly_ge.2.2⟩ hEL_le hPb_γℓ_le hL_add1_le hNRoot_le hCsp_nn
    h2.1 h2.2
  exact ⟨h2.1, h3⟩

end ModularAsymp

end MinCostFlow.Chain.Ordered
