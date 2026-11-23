module

public import MinCostFlow.Chain.ConcreteAsymptotics
public import MinCostFlow.Chain.LevelInvariants
public import MinCostFlow.LSF.Theorem22
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Asymptotic Parameter Bounds and `σ_last(N₀)` Obstruction

Proves `concrete_params_asymptotics`, discharging all parameter sanity, monotonicity,
asymptotic exponent (`hγℓ, hγr, hσT, hσM, hcT, hcL, hlogF, hγM₀, hγk`), and own-level
`lastLevelParams.σ_last (levelM TP P P.d + 1)` bounds for `concreteAlg2Cfg` when `M_thresh ≤ M₀`
and `1 + log(N₀ + 2) ≤ C_N * log(M₀ + 2)`.

Also proves `sigmaLast_N0_obstruction`, showing `(lastLevelParams C_lsst).σ_last N₀ ≥ 2 * N₀^2`
for `1 ≤ N₀` (preventing any subpolynomial global-`N₀` `hσL` bound when `N₀ = Ω(M₀)`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander

section ConcreteBounds

private lemma asymp_params_tail_1
    (C_lsst C_last C_N C_γ C_poly : ℝ) (M₀ N₀ B_cap D_cap : ℕ) (hM₀1 : 1 ≤ M₀)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hCγ_ge : 3 ≤ C_γ) (hCpoly_1k : 1000 ≤ C_poly)
    (hcpoly_cT : 37810 * 7 + 1 ≤ C_poly)
    (hp_2K6 : 2 * mwuK0 C_lsst * C_N ^ 6 ≤ C_poly)
    (hp_mwu : 4 * (26 * mwuK0 C_lsst + 128) * C_N ^ 7 ≤ C_poly)
    (hp_log5 : (2 * (1 + C_N)) ^ 5 ≤ C_poly)
    (hlogN2 : Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2))
    (hPoly_exp : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let P := concreteChainParams M₀ hM₀1
    let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap
    let TP := sparseCoreParams E
    let LP := lastLevelParams C_last
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    TP.σ P.k N₀ ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) ∧
    max 0 (concreteSigmaMWU C_lsst M₀ N₀) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
    TP.c_T ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
    LP.c_last ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
    (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 3) ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) := by
  intro P E TP LP L LL
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
  have hL_pos : 0 < L := by linarith
  have hLa47_nn : 0 ≤ L ^ (47 / 48 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have hConst_Cpoly : ∀ A : ℝ, 0 ≤ A → A ≤ C_poly → A ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    fun A hA0 hAC => by simpa using hPoly_exp A 0 hA0 hAC (by norm_num)
  have hExp1_47 : Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) ≤
      Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) := by
    have h23_47 : L ^ (23 / 24 : ℝ) ≤ L ^ (47 / 48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hlogN2_nn : 0 ≤ Real.log ((N₀ : ℝ) + 2) := by linarith [half_lt_log_add_two N₀]
  have hK0 := (mwuK0_pos C_lsst).le
  have hCN_nn : 0 ≤ C_N := by
    have : 0 ≤ C_N * L := le_trans hlogN2_nn hlogN2
    exact nonneg_of_mul_nonneg_left this hL_pos
  have hPd_bounds := chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM₀1
  have hσT_le : TP.σ P.k N₀ ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) := by
    change max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6) ≤ _
    refine max_le (Real.one_le_exp (by positivity)) ?_
    have hM0_pos : (0 : ℝ) < M₀ := by positivity
    have hM0_le_L : Real.log (M₀ : ℝ) ≤ L := Real.log_le_log hM0_pos (by linarith)
    have hd_pos : 0 < (P.d : ℝ) := by exact_mod_cast P.hd
    have hsplit : L = L ^ (47 / 48 : ℝ) * L ^ ((1 - (23 : ℝ) / 24) / 2) := by
      rw [← Real.rpow_add hL_pos]; norm_num
    have hdiv_le : Real.log (M₀ : ℝ) / (P.d : ℝ) ≤ L ^ (47 / 48 : ℝ) * LL := by
      have h1 : Real.log (M₀ : ℝ) / (P.d : ℝ) ≤ L / L ^ ((1 - (23 : ℝ) / 24) / 2) := by
        have hlogM0_nn : 0 ≤ Real.log (M₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hM₀1)
        have h124_pos : 0 < L ^ ((1 - (23 : ℝ) / 24) / 2) := Real.rpow_pos_of_pos hL_pos _
        gcongr
        exact hPd_bounds.2.1
      have h2 : L / L ^ ((1 - (23 : ℝ) / 24) / 2) = L ^ (47 / 48 : ℝ) := by
        conv_lhs => arg 1; rw [hsplit]
        exact mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hL_pos _).ne'
      have h3 : L ^ (47 / 48 : ℝ) ≤ L ^ (47 / 48 : ℝ) * LL :=
        le_mul_of_one_le_right hLa47_nn hLL1
      linarith
    have hdiv_le1 : Real.log (M₀ : ℝ) / (P.d : ℝ) ≤ 1 * L ^ (47 / 48 : ℝ) * LL := by linarith
    have hPk_rpow : (P.k : ℝ) ≤ 2 * Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) := by
      have hk_up : (P.k : ℝ) ≤ 2 * (M₀ : ℝ) ^ (1 / (P.d : ℝ)) := P.hk_upper
      have hrpow_le : (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) := by
        rw [Real.rpow_def_of_pos hM0_pos, mul_one_div]; exact Real.exp_le_exp.mpr hdiv_le1
      linarith
    have hpow6 : (Real.log ((N₀ : ℝ) + 2)) ^ 6 ≤ (C_N * L) ^ 6 := pow_le_pow_left₀ hlogN2_nn hlogN2 6
    have h2K6 : 2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6 ≤ Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) :=
      le_trans (hPoly_exp (2 * mwuK0 C_lsst * C_N ^ 6) 6 (by positivity) hp_2K6 (by norm_num)) hExp1_47
    calc mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6
        ≤ mwuK0 C_lsst * (2 * Real.exp (1 * L ^ (47 / 48 : ℝ) * LL)) * (C_N * L) ^ 6 := by gcongr
      _ = (2 * mwuK0 C_lsst * C_N ^ 6 * L ^ 6) * Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) := by ring
      _ ≤ Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) * Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) :=
          mul_le_mul_of_nonneg_right h2K6 (Real.exp_pos _).le
      _ = Real.exp (2 * L ^ (47 / 48 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) := exp_47_48_mono_LL (by linarith only [hCγ_ge]) hM₀1
  have hσM_le : max 0 (concreteSigmaMWU C_lsst M₀ N₀) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) := by
    rw [max_eq_right (concreteSigmaMWU_nonneg C_lsst M₀ N₀)]
    change ((Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1 : ℕ) : ℝ) *
        (26 * mwuK0 C_lsst + 128) * (Real.log ((N₀ : ℝ) + 2)) ^ 7 ≤ _
    have hlog3_gt1 : 1 ≤ Real.log 3 := by
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    have hlogm2_nn : 0 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (M₀ ^ 2)])
    have hμ_le : ((Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1 : ℕ) : ℝ) ≤ 4 * L := by
      have hdiv_le : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3 ≤ 2 * L :=
        calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3
            ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / 1 := div_le_div_of_nonneg_left hlogm2_nn zero_lt_one hlog3_gt1
          _ = Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := div_one _
          _ ≤ 2 * L := log_sq_add_two_le_double M₀
      have hc_lt : (Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) : ℝ) <
          Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3 + 1 :=
        Nat.ceil_lt_add_one (div_nonneg hlogm2_nn (by linarith [hlog3_gt1]))
      rw [Nat.cast_add_one]
      linarith only [hdiv_le, hc_lt, hL1]
    have hK_nn : 0 ≤ 26 * mwuK0 C_lsst + 128 := by linarith only [hK0]
    have hpow7 : (Real.log ((N₀ : ℝ) + 2)) ^ 7 ≤ (C_N * L) ^ 7 := pow_le_pow_left₀ hlogN2_nn hlogN2 7
    have hL8 := hPoly_exp (4 * (26 * mwuK0 C_lsst + 128) * C_N ^ 7) 8 (by positivity) hp_mwu (by norm_num)
    calc ((Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1 : ℕ) : ℝ) *
            (26 * mwuK0 C_lsst + 128) * (Real.log ((N₀ : ℝ) + 2)) ^ 7
        ≤ (4 * L) * (26 * mwuK0 C_lsst + 128) * (C_N * L) ^ 7 := by gcongr
      _ = (4 * (26 * mwuK0 C_lsst + 128) * C_N ^ 7) * L ^ 8 := by ring
      _ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := hL8
      _ ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) := exp_23_24_mono_LL (by linarith only [hCγ_ge]) hM₀1
  have hcT_le : TP.c_T ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) := by
    change 37810 * (7 : ℝ) ^ max 1 1 + 1 ≤ _
    rw [show 37810 * (7 : ℝ) ^ max 1 1 + 1 = 37810 * 7 + 1 by norm_num]
    exact le_trans (hConst_Cpoly (37810 * 7 + 1) (by norm_num) hcpoly_cT)
      (exp_23_24_mono_LL (by linarith only [hCγ_ge]) hM₀1)
  have hcL_le : LP.c_last ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) := by
    change (8 : ℝ) ≤ _
    exact le_trans (hConst_Cpoly 8 (by norm_num) (by linarith only [hCpoly_1k]))
      (exp_23_24_mono_LL (by linarith only [hCγ_ge]) hM₀1)
  have hlogF_le : (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 3) ≤
      Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) := by
    rw [show max TP.p_T LP.p_last + 3 = 5 by change max (max 1 1 + 1) 0 + 3 = 5; norm_num]
    have hPM₀ : P.M₀ = M₀ := rfl
    have hlf : logFactor P N₀ ≤ (1 + C_N) * L := by
      unfold logFactor; rw [hPM₀]
      have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
      have hN0_nn : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
      have harg_le : (M₀ : ℝ) + (N₀ : ℝ) + 2 ≤ ((M₀ : ℝ) + 2) * ((N₀ : ℝ) + 2) := by
        nlinarith only [hM0_nn, hN0_nn]
      have h1 : Real.log ((M₀ : ℝ) + (N₀ : ℝ) + 2) ≤ L + Real.log ((N₀ : ℝ) + 2) := by
        calc Real.log ((M₀ : ℝ) + (N₀ : ℝ) + 2)
            ≤ Real.log (((M₀ : ℝ) + 2) * ((N₀ : ℝ) + 2)) := Real.log_le_log (by positivity) harg_le
          _ = L + Real.log ((N₀ : ℝ) + 2) := Real.log_mul (by positivity) (by positivity)
      linarith only [h1, hlogN2]
    have hlf_nn : 0 ≤ logFactor P N₀ := by
      unfold logFactor; rw [hPM₀]
      exact Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) M₀, Nat.cast_nonneg (α := ℝ) N₀])
    have hpow5 : (2 * logFactor P N₀) ^ 5 ≤ (2 * (1 + C_N)) ^ 5 * L ^ 5 := by
      have hmul5 : 2 * logFactor P N₀ ≤ 2 * ((1 + C_N) * L) := by linarith only [hlf]
      calc (2 * logFactor P N₀) ^ 5 ≤ (2 * ((1 + C_N) * L)) ^ 5 :=
            pow_le_pow_left₀ (by positivity) hmul5 5
        _ = (2 * (1 + C_N)) ^ 5 * L ^ 5 := by ring
    exact le_trans hpow5 (le_trans (hPoly_exp ((2 * (1 + C_N)) ^ 5) 5 (by positivity) hp_log5 (by norm_num))
      (le_trans hExp1_47 (exp_47_48_mono_LL (by linarith only [hCγ_ge]) hM₀1)))
  exact ⟨hσT_le, hσM_le, hcT_le, hcL_le, hlogF_le⟩

private lemma asymp_params_tail_2
    (C_lsst C_last C_γ C_poly : ℝ) (M₀ B_cap D_cap : ℕ) (hM₀1 : 1 ≤ M₀) (hM₀2 : 2 ≤ M₀)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hCγ_ge : 3 ≤ C_γ) (hp_1250 : 1250 * max 1 C_last ≤ C_poly)
    (hPoly_exp : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * (Real.log ((M₀ : ℝ) + 2)) ^ j ≤
        Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)))
    (hDom : C_γ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2) ≤
      (1 / 4 : ℝ) * Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ))
    (hγℓ_le : (sparseCoreParams (concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap)).γ_ℓ (M₀ ^ 2) ≤
      Real.exp (C_γ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2))) :
    let P := concreteChainParams M₀ hM₀1
    let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap
    let TP := sparseCoreParams E
    let L := Real.log ((M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    TP.γ_ℓ (M₀ ^ 2) ≤ M₀ ∧
    TP.γ_ℓ (M₀ ^ 2) ≤ P.k ∧
    (lastLevelParams C_last).σ_last (levelM TP P P.d + 1) ≤
      Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) := by
  intro P E TP L LL
  have hL1 : 1 ≤ L := one_le_log_add_two_of_one hM₀1
  have hL_pos : 0 < L := by linarith
  have hPd_bounds := chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM₀1
  have hConst_Cpoly : ∀ A : ℝ, 0 ≤ A → A ≤ C_poly → A ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    fun A hA0 hAC => by simpa using hPoly_exp A 0 hA0 hAC (by norm_num)
  have hExp1_47 : Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) ≤
      Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) := by
    have h23_47 : L ^ (23 / 24 : ℝ) ≤ L ^ (47 / 48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hLL1 : 1 ≤ LL := one_le_LL_of_one hM₀1
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (P.k : ℝ) := by
    have hM0_pos : (0 : ℝ) < M₀ := by positivity
    have hM2_le : (M₀ : ℝ) + 2 ≤ (M₀ : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀2
      nlinarith
    have hL_le_2M : L ≤ 2 * Real.log (M₀ : ℝ) := by
      calc L ≤ Real.log ((M₀ : ℝ) ^ 2) := Real.log_le_log (by positivity) hM2_le
        _ = 2 * Real.log (M₀ : ℝ) := by rw [Real.log_pow]; norm_num
    have hsplit : L = L ^ (47 / 48 : ℝ) * L ^ ((1 - (23 : ℝ) / 24) / 2) := by
      rw [← Real.rpow_add hL_pos]; norm_num
    have hd_pos : 0 < (P.d : ℝ) := by exact_mod_cast P.hd
    have hlogM_div : (1 / 4 : ℝ) * L ^ (47 / 48 : ℝ) ≤ Real.log (M₀ : ℝ) / (P.d : ℝ) := by
      have h1 : (1 / 4 : ℝ) * L ^ (47 / 48 : ℝ) = ((1 / 2 : ℝ) * L) / (2 * L ^ ((1 - (23 : ℝ) / 24) / 2)) := by
        have hpos1 : (L ^ ((1 - (23 : ℝ) / 24) / 2)) ≠ 0 := (Real.rpow_pos_of_pos hL_pos _).ne'
        have hdiv : L / L ^ ((1 - (23 : ℝ) / 24) / 2) = L ^ (47 / 48 : ℝ) := by
          conv_lhs => arg 1; rw [hsplit]
          exact mul_div_cancel_right₀ _ hpos1
        calc (1 / 4 : ℝ) * L ^ (47 / 48 : ℝ)
            = (1 / 4 : ℝ) * (L / L ^ ((1 - (23 : ℝ) / 24) / 2)) := by rw [hdiv]
          _ = ((1 / 2 : ℝ) * L) / (2 * L ^ ((1 - (23 : ℝ) / 24) / 2)) := by ring
      rw [h1]
      gcongr
      · linarith
      · exact hPd_bounds.2.2
    have hexp_k : Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ≤ (M₀ : ℝ) ^ (1 / (P.d : ℝ)) := by
      rw [Real.rpow_def_of_pos hM0_pos, mul_one_div]
      exact Real.exp_le_exp.mpr (le_trans hDom hlogM_div)
    have hk_ge : (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (P.k : ℝ) := Nat.le_ceil _
    exact le_trans hγℓ_le (le_trans hexp_k hk_ge)
  have hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ (M₀ : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast P.hd
    have hM0_r : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
    have h1_div : 1 / (P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd1 (by linarith)
    have hceil_le_M₀ : (P.k : ℝ) ≤ (M₀ : ℝ) := by
      change (Nat.ceil ((M₀ : ℝ) ^ (1 / (P.d : ℝ))) : ℝ) ≤ (M₀ : ℝ)
      exact_mod_cast (Nat.ceil_le.mpr (by
        calc (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (M₀ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM0_r h1_div
          _ = (M₀ : ℝ) := Real.rpow_one _))
    exact le_trans hγk hceil_le_M₀
  have hσL_levelD : (lastLevelParams C_last).σ_last (levelM TP P P.d + 1) ≤
      Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) := by
    have hM0_pow : (M₀ : ℝ) ≤ (P.k : ℝ) ^ P.d := by
      have hceil : (M₀ : ℝ) ^ (1 / (P.d : ℝ)) ≤ (P.k : ℝ) := Nat.le_ceil _
      have hd_pos : (0 : ℝ) < (P.d : ℝ) := by exact_mod_cast P.hd
      have hpow := Real.rpow_le_rpow (by positivity) hceil (Nat.cast_nonneg P.d)
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hd_pos.ne', Real.rpow_one, Real.rpow_natCast] at hpow
      exact hpow
    have hγ1 : 1 ≤ TP.γ_ℓ (M₀ ^ 2) := (sparseCoreParams_valid E).2.2.1 (M₀ ^ 2)
    have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
    have hPM₀ : P.M₀ = M₀ := rfl
    have harg_le : (M₀ : ℝ) * TP.γ_ℓ (M₀ ^ 2) * (TP.γ_ℓ (M₀ ^ 2) / (P.k : ℝ)) ^ P.d ≤
        TP.γ_ℓ (M₀ ^ 2) ^ (P.d + 1) := by
      have hk_pow_pos : 0 < (P.k : ℝ) ^ P.d := pow_pos hk_pos _
      rw [div_pow, pow_succ]
      calc (M₀ : ℝ) * TP.γ_ℓ (M₀ ^ 2) * (TP.γ_ℓ (M₀ ^ 2) ^ P.d / (P.k : ℝ) ^ P.d)
          = ((M₀ : ℝ) / (P.k : ℝ) ^ P.d) * (TP.γ_ℓ (M₀ ^ 2) ^ P.d * TP.γ_ℓ (M₀ ^ 2)) := by ring
        _ ≤ 1 * (TP.γ_ℓ (M₀ ^ 2) ^ P.d * TP.γ_ℓ (M₀ ^ 2)) :=
            mul_le_mul_of_nonneg_right ((div_le_one hk_pow_pos).mpr hM0_pow) (by positivity)
        _ = TP.γ_ℓ (M₀ ^ 2) ^ P.d * TP.γ_ℓ (M₀ ^ 2) := one_mul _
    have hn_d_le : ((levelM TP P P.d + 1 : ℕ) : ℝ) ≤ 3 * TP.γ_ℓ (M₀ ^ 2) ^ (P.d + 1) := by
      unfold levelM; rw [hPM₀]
      have hceil_lt := Nat.ceil_lt_add_one (by positivity :
        0 ≤ (M₀ : ℝ) * TP.γ_ℓ (M₀ ^ 2) * (TP.γ_ℓ (M₀ ^ 2) / (P.k : ℝ)) ^ P.d)
      have h1pow : 1 ≤ TP.γ_ℓ (M₀ ^ 2) ^ (P.d + 1) := one_le_pow₀ hγ1
      push_cast; linarith only [harg_le, hceil_lt, h1pow]
    have hLL_nn : 0 ≤ LL := by linarith [one_le_LL_of_one hM₀1]
    have hL47_nn : 0 ≤ L ^ (47 / 48 : ℝ) := Real.rpow_nonneg hL_pos.le _
    have hd1_le_3L : (P.d : ℝ) + 1 ≤ 3 * L ^ (1 / 48 : ℝ) := by
      have h1L48 : 1 ≤ L ^ (1 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      have hd2 : (P.d : ℝ) ≤ 2 * L ^ (1 / 48 : ℝ) := by
        change (chosenD (23 / 24) M₀ : ℝ) ≤ 2 * L ^ (1 / 48 : ℝ)
        simpa [show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] using hPd_bounds.2.2
      linarith
    have hpow_exp : TP.γ_ℓ (M₀ ^ 2) ^ (P.d + 1) ≤ Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL) := by
      have hmul_exp : ((P.d + 1 : ℕ) : ℝ) * (C_γ * L ^ (23 / 24 : ℝ) * LL) ≤
          3 * C_γ * L ^ (47 / 48 : ℝ) * LL := by
        have hsplit47 : L ^ (1 / 48 : ℝ) * L ^ (23 / 24 : ℝ) = L ^ (47 / 48 : ℝ) := by
          rw [← Real.rpow_add hL_pos]; norm_num
        have hLa23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_pos.le _
        have hmul_pos : 0 ≤ C_γ * L ^ (23 / 24 : ℝ) * LL := by positivity
        calc ((P.d + 1 : ℕ) : ℝ) * (C_γ * L ^ (23 / 24 : ℝ) * LL)
            ≤ (3 * L ^ (1 / 48 : ℝ)) * (C_γ * L ^ (23 / 24 : ℝ) * LL) := by
                push_cast; exact mul_le_mul_of_nonneg_right hd1_le_3L hmul_pos
          _ = 3 * C_γ * (L ^ (1 / 48 : ℝ) * L ^ (23 / 24 : ℝ)) * LL := by ring
          _ = 3 * C_γ * L ^ (47 / 48 : ℝ) * LL := by rw [hsplit47]
      calc TP.γ_ℓ (M₀ ^ 2) ^ (P.d + 1)
          ≤ (Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL)) ^ (P.d + 1) :=
            pow_le_pow_left₀ (by linarith) hγℓ_le _
        _ = Real.exp (((P.d + 1 : ℕ) : ℝ) * (C_γ * L ^ (23 / 24 : ℝ) * LL)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL) := Real.exp_le_exp.mpr hmul_exp
    have hn_d2_le : ((levelM TP P P.d + 1 : ℕ) : ℝ) + 2 ≤
        5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL) := by
      have h1exp : 1 ≤ Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL) := Real.one_le_exp (by positivity)
      linarith only [hn_d_le, hpow_exp, h1exp]
    have hlog_nd : Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2) ≤
        ((levelM TP P P.d + 1 : ℕ) : ℝ) + 2 := by
      linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < ((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)]
    have hlog_nd_nn : 0 ≤ Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (levelM TP P P.d + 1)])
    have hprod_4 : ((levelM TP P P.d + 1 : ℕ) : ℝ) ^ 2 *
        (Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)) ^ 2 ≤
        (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 4 := by
      have h1 : ((levelM TP P P.d + 1 : ℕ) : ℝ) ≤ 5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL) := by
        linarith [Nat.cast_nonneg (α := ℝ) (levelM TP P P.d + 1)]
      have h2 := le_trans hlog_nd hn_d2_le
      calc ((levelM TP P P.d + 1 : ℕ) : ℝ) ^ 2 *
            (Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)) ^ 2
          ≤ (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 2 *
            (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 2 := by gcongr
        _ = (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 4 := by ring
    have hK_const : 2 * max 1 C_last * 5 ^ 4 ≤ Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) :=
      le_trans (hConst_Cpoly (2 * max 1 C_last * 5 ^ 4) (by positivity) (by linarith only [hp_1250])) hExp1_47
    have hpow4 : (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 4 =
        5 ^ 4 * Real.exp (12 * C_γ * L ^ (47 / 48 : ℝ) * LL) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
    have hmain_last : 2 * max 1 C_last * ((levelM TP P P.d + 1 : ℕ) : ℝ) ^ 2 *
        (Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)) ^ 2 ≤
        Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) := by
      have hMx : 0 ≤ max 1 C_last := by positivity
      calc 2 * max 1 C_last * ((levelM TP P P.d + 1 : ℕ) : ℝ) ^ 2 *
            (Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)) ^ 2
          ≤ (2 * max 1 C_last) * (5 * Real.exp (3 * C_γ * L ^ (47 / 48 : ℝ) * LL)) ^ 4 := by
              nlinarith only [hMx, hprod_4]
        _ = (2 * max 1 C_last * 5 ^ 4) * Real.exp (12 * C_γ * L ^ (47 / 48 : ℝ) * LL) := by
              rw [hpow4]; ring
        _ ≤ Real.exp (1 * L ^ (47 / 48 : ℝ) * LL) * Real.exp (12 * C_γ * L ^ (47 / 48 : ℝ) * LL) :=
            mul_le_mul_of_nonneg_right hK_const (Real.exp_pos _).le
        _ = Real.exp ((12 * C_γ + 1) * L ^ (47 / 48 : ℝ) * LL) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) := exp_47_48_mono_LL (by linarith only [hCγ_ge]) hM₀1
    change max 1 (2 * max 1 C_last * ((levelM TP P P.d + 1 : ℕ) : ℝ) ^ 2 *
      (Real.log (((levelM TP P P.d + 1 : ℕ) : ℝ) + 2)) ^ 2) ≤ _
    exact max_le (Real.one_le_exp (by positivity)) hmain_last
  exact ⟨hγM₀, hγk, hσL_levelD⟩

/-- Core asymptotic parameter bounds for `concreteEnv` and `concreteAlg2CfgWithLast`.
Generalizes `concrete_params_asymptotics` to an arbitrary `lastTool : LastLevelTool`
at parameter bundle `lastLevelParams C_last`. -/
theorem concrete_params_asymptotics_with_last
    (C_lsst C_last C_sp K_s K_t : ℝ)
    (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (integerBuckets : Bool := false) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ), 3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
        (lastTool : LastLevelTool)
        (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
        (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤
          Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤
          Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool C_last sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        let L := Real.log ((M₀ : ℝ) + 2)
        let LL := Real.log (L + 2)
        cfg.TP.Valid ∧
        cfg.LP.Valid ∧
        cfg.P.d = chosenD (23 / 24) M₀ ∧
        (∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂) ∧
        0 ≤ cfg.σ_mwu cfg.N₀ ∧
        ((B_cap : ℝ) ≤ Real.exp ((3 + C_ψ) * L ^ (23 / 24 : ℝ) * LL)) ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.γ_r (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.σ cfg.P.k N₀ ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) ∧
        max 0 (cfg.σ_mwu N₀) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.c_T ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.LP.c_last ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        (2 * logFactor cfg.P N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
          Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k ∧
        (lastLevelParams C_last).σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
          Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) := by
  let C_poly : ℝ := max (max 1000 (2 * mwuK0 (8192 * max 1 C_lsst) * C_N ^ 6 + 2)) (
    2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) +
    37810 * 49 + 1 + 8 + (32 * (C_N + 1)) ^ 5)
  have hCpoly_1k : (1000 : ℝ) ≤ C_poly := (le_max_left _ _).trans (le_max_left _ _)
  have hCpoly_big : 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) +
      37810 * 49 + 1 + 8 + (32 * (C_N + 1)) ^ 5 ≤ C_poly := le_max_right _ _
  obtain ⟨u₁, _, hu₁⟩ := polylog_le_exp_rpow_23_24 C_poly 8 (by linarith)
  let C_B : ℝ := 3 + C_ψ
  let C_rec : ℝ := 950 + 240 * C_sp + 2 * C_B + C_D
  let C_cost : ℝ := 1500 + 360 * C_sp + C_D
  let C_γ : ℝ := max 10 (2 * C_rec + C_cost + 10)
  obtain ⟨u₂, _, hu₂⟩ := rpow_23_24_mul_loglog_dominates_log C_γ (1 / 4) (by positivity) (by norm_num)
  let u₀ : ℝ := max u₁ (max u₂ 4)
  obtain ⟨M_thresh, hMth2, hMth_u⟩ := exp_dominates_of_u0 u₀
  have hCγ_ge : 3 ≤ C_γ := by linarith [le_max_left (10 : ℝ) (2 * C_rec + C_cost + 10)]
  refine ⟨C_γ, M_thresh, hCγ_ge, hMth2, fun oracle lastTool sparsify M₀ N₀ D_cap α Ψ ε hM₀1 hM₀_ge hlogN hDcap hΨ => ?_⟩
  have hM₀2 : 2 ≤ M₀ := le_trans hMth2 hM₀_ge
  let B_cap := concreteBucketCapacity integerBuckets C_lsst Ψ M₀ N₀ hM₀1
  let E := concreteEnv C_lsst params
    (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
    M₀ B_cap D_cap
  let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool C_last sparsify params
    (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
    M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
  let L : ℝ := Real.log ((M₀ : ℝ) + 2)
  let LL : ℝ := Real.log (L + 2)
  have hL_ge : u₀ ≤ L := by
    have hcast : ((M_thresh : ℝ) + 2) ≤ (M₀ : ℝ) + 2 := by
      have : (M_thresh : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀_ge
      linarith
    exact le_trans hMth_u (Real.log_le_log (by positivity) hcast)
  have hL1 : 1 ≤ L := by linarith [le_trans (le_trans (le_max_right u₂ 4) (le_max_right u₁ _)) hL_ge]
  have hExp_poly : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * L ^ j ≤ Real.exp (L ^ (23 / 24 : ℝ)) := fun A j hA0 hAC hj => by
    have h1 := hu₁ L (le_trans (le_max_left u₁ _) hL_ge)
    have hj_pow : L ^ j ≤ L ^ 8 := pow_le_pow_right₀ hL1 hj
    calc A * L ^ j ≤ C_poly * L ^ 8 := mul_le_mul hAC hj_pow (by positivity) (by linarith)
      _ ≤ Real.exp (L ^ (23 / 24 : ℝ)) := h1
  have hExp1_23 : Real.exp (L ^ (23 / 24 : ℝ)) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) := by
    simpa [one_mul] using rpow_exp_le_LL (C := 1) zero_le_one hM₀1
  have hPoly_exp : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ C_poly → j ≤ 8 →
      A * L ^ j ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) :=
    fun A j hA0 hAC hj => le_trans (hExp_poly A j hA0 hAC hj) hExp1_23
  have hC1 : 1 ≤ max 1 C_N := le_max_left 1 C_N
  have hC7 : 1 ≤ (max 1 C_N) ^ 7 := one_le_pow₀ hC1
  have hCN6 : C_N ^ 6 ≤ (max 1 C_N) ^ 7 :=
    le_trans (pow_le_pow_left₀ (by linarith) (le_max_right 1 C_N) 6) (pow_le_pow_right₀ hC1 (by norm_num))
  have hCN7 : C_N ^ 7 ≤ (max 1 C_N) ^ 7 := pow_le_pow_left₀ (by linarith) (le_max_right 1 C_N) 7
  have hK0 := (mwuK0_pos C_lsst).le
  have hK_bd : 1 ≤ mwuK0 C_lsst + max 1 C_last + 128 := by linarith [le_max_left 1 C_last]
  have hbase_le : 2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) ≤ C_poly := by
    have h12 : 1 ≤ (K_s + 1) * (K_t + 1) := by nlinarith
    have hprod : 2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) ≤
        2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by
      calc 2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128)
          = 2000 * 1 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by ring
        _ ≤ 2000 * ((K_s + 1) * (K_t + 1)) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by gcongr
        _ = 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by ring
    linarith [hCpoly_big, show (0 : ℝ) ≤ 37810 * 49 + 1 + 8 + (32 * (C_N + 1)) ^ 5 by positivity]
  have hp_bcap1 : 2 * mwuK0 C_lsst * C_N ^ 6 + 2 ≤ C_poly := by
    have h1 : 2 * mwuK0 C_lsst * C_N ^ 6 ≤ 2 * (mwuK0 C_lsst + max 1 C_last + 128) * (max 1 C_N) ^ 7 := by
      have : mwuK0 C_lsst ≤ mwuK0 C_lsst + max 1 C_last + 128 := by linarith [le_max_left 1 C_last]
      gcongr
    have h2 : 2 * (mwuK0 C_lsst + max 1 C_last + 128) * (max 1 C_N) ^ 7 ≤
        2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) - 2 := by
      have : 1998 * 1 * 1 ≤ 1998 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by gcongr
      linarith
    linarith
  have hp_mwu : 4 * (26 * mwuK0 C_lsst + 128) * C_N ^ 7 ≤ C_poly := by
    have h1 : 4 * (26 * mwuK0 C_lsst + 128) ≤ 2000 * (mwuK0 C_lsst + max 1 C_last + 128) := by
      linarith [le_max_left 1 C_last]
    have h2 : 4 * (26 * mwuK0 C_lsst + 128) * C_N ^ 7 ≤
        2000 * (mwuK0 C_lsst + max 1 C_last + 128) * (max 1 C_N) ^ 7 := by gcongr
    linarith
  have hp_log5 : (2 * (1 + C_N)) ^ 5 ≤ C_poly := by
    have hbase : 2 * (1 + C_N) ≤ 32 * (C_N + 1) := by linarith
    have h1 : (2 * (1 + C_N)) ^ 5 ≤ (32 * (C_N + 1)) ^ 5 := pow_le_pow_left₀ (by positivity) hbase 5
    have h2 : (0 : ℝ) ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 *
        (mwuK0 C_lsst + max 1 C_last + 128) + 37810 * 49 + 1 + 8 := by positivity
    linarith
  have hp_1250 : 1250 * max 1 C_last ≤ C_poly := by
    have h1 : 1250 * max 1 C_last ≤ 2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by
      have hmx : max 1 C_last ≤ mwuK0 C_lsst + max 1 C_last + 128 := by linarith
      calc 1250 * max 1 C_last ≤ 1250 * (mwuK0 C_lsst + max 1 C_last + 128) := by gcongr
        _ = 1250 * 1 * (mwuK0 C_lsst + max 1 C_last + 128) := by ring
        _ ≤ 2000 * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by gcongr; norm_num
    linarith
  have hp_22Ks : 22 * (K_s + 1) ≤ C_poly := by
    have h1 : 22 * (K_s + 1) ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 *
        (mwuK0 C_lsst + max 1 C_last + 128) := by
      have hKt1 : 1 ≤ K_t + 1 := by linarith
      calc 22 * (K_s + 1) = 22 * (K_s + 1) * 1 * 1 * 1 := by ring
        _ ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by
            gcongr; norm_num
    linarith [hCpoly_big, show (0 : ℝ) ≤ 37810 * 49 + 1 + 8 + (32 * (C_N + 1)) ^ 5 by positivity]
  have hp_2Kt : 2 * K_t + 2 ≤ C_poly := by
    have h1 : 2 * (K_t + 1) ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 *
        (mwuK0 C_lsst + max 1 C_last + 128) := by
      have hKs1 : 1 ≤ K_s + 1 := by linarith
      calc 2 * (K_t + 1) = 2 * 1 * (K_t + 1) * 1 * 1 := by ring
        _ ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 * (mwuK0 C_lsst + max 1 C_last + 128) := by
            gcongr; norm_num
    linarith [hCpoly_big, show (0 : ℝ) ≤ 37810 * 49 + 1 + 8 + (32 * (C_N + 1)) ^ 5 by positivity]
  have hp_cT : 37810 * 7 + 1 ≤ C_poly := by
    have h0 : 0 ≤ 2000 * (K_s + 1) * (K_t + 1) * (max 1 C_N) ^ 7 *
        (mwuK0 C_lsst + max 1 C_last + 128) + 8 + (32 * (C_N + 1)) ^ 5 := by positivity
    linarith only [hCpoly_big, h0]
  have hlogN2 : Real.log ((N₀ : ℝ) + 2) ≤ C_N * L := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N₀] : (1 : ℝ) ≤ (N₀ : ℝ) + 2)
    linarith
  have hSec8 := asymp_sec8_bounds hCsp hKs params hp_spec hM₀1 hPoly_exp (by linarith)
  have hBcap_le : (B_cap : ℝ) ≤ Real.exp (C_B * L ^ (23 / 24 : ℝ) * LL) :=
    by
      cases integerBuckets
      · exact asymp_bcap_bound C_lsst C_ψ C_N C_poly hCψ hCN hM₀1 Ψ hlogN2 hΨ
          hExp_poly hPoly_exp ⟨hp_bcap1, by linarith⟩
      · exact asymp_bucketCap_bound C_lsst C_ψ C_N C_poly hCψ hCN hM₀1 Ψ hlogN2 hΨ
          hExp_poly hPoly_exp ⟨(le_max_right _ _).trans (le_max_left _ _), by linarith⟩
  have hGR := asymp_gammaL_recEnv_bounds (C_lsst := C_lsst) hKs hKt hCD hCψ params
    (fun m => ⟨(hp_spec m).1, (hp_spec m).2.1, (hp_spec m).2.2.1, (hp_spec m).2.2.2.1⟩)
    hM₀1 hPoly_exp ⟨hCpoly_1k, hp_22Ks, hp_2Kt⟩ hDcap hBcap_le hSec8 hCsp.le
  have hγℓ_le : cfg.TP.γ_ℓ (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) :=
    le_trans hGR.1 (exp_23_24_mono_LL (le_trans (by dsimp only [C_rec]; linarith) (le_max_right (10 : ℝ) _)) hM₀1)
  have hγr_le : cfg.TP.γ_r (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) :=
    le_trans hGR.2 (exp_23_24_mono_LL (le_trans (by linarith) (le_max_right (10 : ℝ) _)) hM₀1)
  have hT1 := asymp_params_tail_1 C_lsst C_last C_N C_γ C_poly M₀ N₀ B_cap D_cap hM₀1 params
    (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
    hCγ_ge hCpoly_1k hp_cT (by linarith only [hp_bcap1]) hp_mwu hp_log5 hlogN2 hPoly_exp
  have hDom : C_γ * L ^ (23 / 24 : ℝ) * LL ≤ (1 / 4 : ℝ) * L ^ (47 / 48 : ℝ) :=
    hu₂ L (le_trans (le_trans (le_max_left u₂ 4) (le_max_right u₁ _)) hL_ge)
  have hT2 := asymp_params_tail_2 C_lsst C_last C_γ C_poly M₀ B_cap D_cap hM₀1 hM₀2 params
    (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
    hCγ_ge hp_1250 hPoly_exp hDom hγℓ_le
  exact ⟨sparseCoreParams_valid E, lastLevelParams_valid C_last, rfl,
    concreteSigmaMWU_mono C_lsst M₀, concreteSigmaMWU_nonneg C_lsst M₀ N₀,
    hBcap_le, hγℓ_le, hγr_le, hT1.1, hT1.2.1, hT1.2.2.1, hT1.2.2.2.1, hT1.2.2.2.2,
    hT2.1, hT2.2.1, hT2.2.2⟩

/-- Core asymptotic parameter bounds for `concreteEnv` and `concreteAlg2Cfg`
(specialized at `lastLevelTool oracle C_lsst` and `lastLevelParams C_lsst`). -/
theorem concrete_params_asymptotics
    (C_lsst C_sp K_s K_t : ℝ)
    (hCsp : 0 < C_sp) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (C_D C_ψ C_N : ℝ) (hCD : 0 ≤ C_D) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N) :
    ∃ (C_γ : ℝ) (M_thresh : ℕ), 3 ≤ C_γ ∧ 2 ≤ M_thresh ∧
      ∀ (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
        (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
        (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ C_N * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤
          Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤
          Real.exp (C_ψ * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
            Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
        let cfg := concreteAlg2Cfg oracle C_lsst sparsify params
          (fun m => le_of_eq (hp_spec m).2.1) (fun m => le_of_eq (hp_spec m).2.2.2.1)
          M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
        let L := Real.log ((M₀ : ℝ) + 2)
        let LL := Real.log (L + 2)
        cfg.TP.Valid ∧
        cfg.LP.Valid ∧
        cfg.P.d = chosenD (23 / 24) M₀ ∧
        (∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂) ∧
        0 ≤ cfg.σ_mwu cfg.N₀ ∧
        ((B_cap : ℝ) ≤ Real.exp ((3 + C_ψ) * L ^ (23 / 24 : ℝ) * LL)) ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.γ_r (M₀ ^ 2) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.σ cfg.P.k N₀ ≤ Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) ∧
        max 0 (cfg.σ_mwu N₀) ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.TP.c_T ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        cfg.LP.c_last ≤ Real.exp (C_γ * L ^ (23 / 24 : ℝ) * LL) ∧
        (2 * logFactor cfg.P N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
          Real.exp (C_γ * L ^ (47 / 48 : ℝ) * LL) ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k ∧
        (lastLevelParams C_lsst).σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
          Real.exp ((14 * C_γ + 2) * L ^ (47 / 48 : ℝ) * LL) :=
  let ⟨C_γ, M_thresh, hCγ, hMth, hAll⟩ :=
    concrete_params_asymptotics_with_last C_lsst C_lsst C_sp K_s K_t hCsp hKs hKt params hp_spec
      C_D C_ψ C_N hCD hCψ hCN
  ⟨C_γ, M_thresh, hCγ, hMth, fun oracle => hAll oracle (lastLevelTool oracle C_lsst)⟩

/-- **Obstruction explaining why `hσL` cannot be discharged at global `N₀ ≥ M₀`**:
for `lastLevelParams C_lsst` and any `1 ≤ N₀`, `σ_last N₀ ≥ 2 * N₀^2`. Whenever `N₀ = Ω(M₀)`,
this grows quadratically in `M₀` and violates any `exp(O(L^{47/48} * LL))` bound. -/
theorem sigmaLast_N0_obstruction (C_lsst : ℝ) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    2 * (N₀ : ℝ) ^ 2 ≤ (lastLevelParams C_lsst).σ_last N₀ := by
  have hlog : 1 ≤ Real.log ((N₀ : ℝ) + 2) := one_le_log_add_two_of_one hN₀
  have hsq : 1 ≤ (Real.log ((N₀ : ℝ) + 2)) ^ 2 := one_le_pow₀ hlog
  have hmx : 1 ≤ max 1 C_lsst := le_max_left 1 C_lsst
  have h2 : 2 * (N₀ : ℝ) ^ 2 ≤ 2 * max 1 C_lsst * (N₀ : ℝ) ^ 2 * (Real.log ((N₀ : ℝ) + 2)) ^ 2 := by
    calc 2 * (N₀ : ℝ) ^ 2 = 2 * 1 * (N₀ : ℝ) ^ 2 * 1 := by ring
      _ ≤ 2 * max 1 C_lsst * (N₀ : ℝ) ^ 2 * (Real.log ((N₀ : ℝ) + 2)) ^ 2 := by gcongr
  exact le_trans h2 (le_max_right _ _)

end ConcreteBounds

end MinCostFlow.Chain
