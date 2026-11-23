module

public import MinCostFlow.SparseCore.SparseCoreCostEnv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime Envelope Bridge without `hComp_bound`

Eliminates `hComp_bound` (`n₀ ≤ E.c_n * (m₀ + 1)`) from `restartCost_le_params`,
`cost_env_baseline_parts`, and `treeRunSeq_cost_le_params`:
* `initTreeCore` charges `(activeSubgraph G₀).n ≤ 2 * m₀` instead of `G₀.n`, and
  `m₀ + n_act + 1 ≤ 3 * (m₀ + 1) ≤ T ≤ (1 + E.c_n) * T` using `4 ≤ recBase E m₀`.
* Component-wise root and quotient-batch bounds use `n_eff := min n₀ (m₀ + 1) ≤ E.c_n * (m₀ + 1)`,
  which holds unconditionally for every `E : SparseCoreEnv` since `1 ≤ E.c_n`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma restartCost_le_params_noComp (E : SparseCoreEnv) (m₀ n₀ Δ₀ m_cur bucketCost : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hm_cur : m_cur ≤ 2 * m₀)
    (hΔ₀ : (Δ₀ : ℝ) ≤ (E.d_fn m₀ : ℝ))
    (hbuck : (bucketCost : ℝ) ≤
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * coreLambda (E.P_fn m₀) m₀ +
        3 + (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
        coreLambda (E.P_fn m₀) m₀) * (m₀ : ℝ)) :
    let P := sparseCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let T := ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T ∧
    ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T ≤ P.c_T * T := by
  intro P p_max logMN T
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    have := lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))
    linarith
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨_, hKs_piece, _, _, hγ_le_rec, hLp1_cm⟩ :=
    env_core_bounds E m₀ (min n₀ (m₀ + 1)) Δ₀ 0 (E.B_fn m₀) le_rfl hΔ₀
      (by exact_mod_cast Nat.zero_le (E.d_fn m₀)) (min_le_cn_mul_m_add_one E m₀ n₀)
  set Λ := coreLambda (E.P_fn m₀) m₀
  have hΛ_nn : 0 ≤ Λ := by linarith [coreLambda_ge_one (E.P_fn m₀) m₀]
  have hΛ_bound : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max := by
    unfold Λ coreLambda
    have hlogC := log_coreNMax_le m₀ n₀ hn₀_pos
    have hp_le : max (E.P_fn m₀).p_s (E.P_fn m₀).p_t ≤ p_max :=
      max_le (le_trans (E.hp_s m₀) (le_max_left _ _)) (le_trans (E.hp_t m₀) (le_max_right _ _))
    have h1 : 1 ≤ 7 * logMN := by linarith
    have hbase : 0 ≤ 1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t
        ≤ (7 * logMN) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t := pow_le_pow_left₀ hbase hlogC _
      _ ≤ (7 * logMN) ^ p_max := pow_le_pow_right₀ h1 hp_le
      _ = (7 : ℝ) ^ p_max * logMN ^ p_max := by rw [mul_pow]
  have hΛs_ge1 : 1 ≤ coreLambdaS (E.P_fn m₀) m₀ := coreLambdaS_ge_one _ m₀
  have hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max * coreLambdaS (E.P_fn m₀) m₀ := by
    have := mul_le_mul_of_nonneg_left hΛs_ge1 (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ p_max * logMN ^ p_max)
    linarith
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith [recEnv_ge_four E m₀]
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_ge1 : 1 ≤ recBase E m₀ * costMult E m₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith [recEnv_ge_four E m₀]) hcm_ge1
  have h1_le : (1 : ℝ) ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) :=
    one_le_mul_of_one_le_of_one_le hγr_ge1 hlog_pow_ge1
  have hm_cur_T : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * T := by
    have hmc : ((m_cur + 1 : ℕ) : ℝ) ≤ 2 * ((m₀ : ℝ) + 1) := by
      have : (m_cur : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hm_cur
      push_cast; linarith
    have hstep := mul_le_mul_of_nonneg_left h1_le (show 0 ≤ 2 * ((m₀ : ℝ) + 1) by linarith)
    have hEq : 2 * ((m₀ : ℝ) + 1) * ((recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) = 2 * T := by
      dsimp only [T]; ring
    linarith
  have hp2a := cost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := cost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn hΛ_bound hΛ_mul_Λs
  have hinit_split :
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
        ((E.L : ℝ) + 1) * (m₀ : ℝ) +
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
            2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) := by ring
  have htot : ((m_cur + 1 + bucketCost : ℕ) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T := by
    dsimp only [T, p_max] at hm_cur_T ⊢
    push_cast at hm_cur_T ⊢
    linarith [hm_cur_T, hbuck, hinit_split, hp2a, hp2b]
  refine ⟨htot, ?_⟩
  have hT_nn : 0 ≤ T := by
    dsimp only [T]
    have : 0 ≤ logMN := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg this _)
  have hcT : (4 + 3 * (7 : ℝ) ^ p_max) + 12600 * (7 : ℝ) ^ p_max ≤ P.c_T := by
    dsimp only [P, sparseCoreParams, p_max]
    linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := max E.p_s_hi E.p_t_hi), E.hc_n]
  calc ((m_cur + 1 + bucketCost : ℕ) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T
      ≤ (4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * T := by linarith [htot]
    _ ≤ P.c_T * T := mul_le_mul_of_nonneg_right hcT hT_nn

lemma cost_env_baseline_parts_noComp (E : SparseCoreEnv) (m₀ n₀ n_act Δ₀ dC q_τ : ℕ)
    (hn₀_pos : 1 ≤ n₀) (hn_act : n_act ≤ 2 * m₀) (hqτ_le_m0 : q_τ ≤ m₀) (hΔ₀_raw : Δ₀ ≤ 2 * m₀)
    (hΔ₀_le : (Δ₀ : ℝ) ≤ (E.d_fn m₀ : ℝ)) (hdC_le : (dC : ℝ) ≤ (E.d_fn m₀ : ℝ)) :
    let P := sparseCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)
    let Λ := coreLambda (E.P_fn m₀) m₀
    let n_eff := min n₀ (m₀ + 1)
    let T := ((m₀ : ℝ) + 1) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)
    ((m₀ : ℝ) + (n_act : ℝ) + 1) +
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
        (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
      (q_τ : ℝ) + 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ) +
      coreRecoursePerQ E.L (E.P_fn m₀) m₀ n_eff Δ₀ (E.B_fn m₀) * (q_τ : ℝ) ≤
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T ∧
    (∀ q_ep : ℕ,
      90 * (E.L : ℝ) * coreNRoot E.L m₀ * ((E.P_fn m₀).K_t + (E.P_fn m₀).K_s + 1) *
        coreE_L E.L (E.P_fn m₀) * ((dC : ℝ) + 1) * Λ *
        (20 * ((m₀ : ℝ) + (E.B_fn m₀ : ℝ) * (2 * coreUCRatio n_eff Δ₀ * (q_ep : ℝ))) *
          Real.log ((m₀ : ℝ) + 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ) + 2)) ≤
        12600 * (7 : ℝ) ^ p_max * T +
        25200 * (7 : ℝ) ^ p_max *
          ((q_ep : ℝ) * (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1))) ∧
    (((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * T ≤
      P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T ∧
      (0 ≤ T ∧ 0 ≤ recBase E m₀ * costMult E m₀ ∧ 1 ≤ logMN)) := by
  intro P p_max logMN Λ n_eff T
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_pos
  have hlogMN_ge1 : 1 ≤ logMN := by
    have := lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))
    linarith
  have hlog_pow_ge1 : 1 ≤ logMN ^ (p_max + 1) := one_le_pow₀ hlogMN_ge1
  obtain ⟨hrec_split, hKs_piece, huc_le, hRec_le, hγ_le_rec, hLp1_cm⟩ :=
    env_core_bounds E m₀ n_eff Δ₀ dC (E.B_fn m₀) le_rfl hΔ₀_le hdC_le
      (min_le_cn_mul_m_add_one E m₀ n₀)
  have hΛ_nn : 0 ≤ Λ := by linarith [coreLambda_ge_one (E.P_fn m₀) m₀]
  have hΛ_bound : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max := by
    unfold Λ coreLambda
    have hlogC := log_coreNMax_le m₀ n₀ hn₀_pos
    have hp_le : max (E.P_fn m₀).p_s (E.P_fn m₀).p_t ≤ p_max :=
      max_le (le_trans (E.hp_s m₀) (le_max_left _ _)) (le_trans (E.hp_t m₀) (le_max_right _ _))
    have h1 : 1 ≤ 7 * logMN := by linarith
    have hbase : 0 ≤ 1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
    calc (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t
        ≤ (7 * logMN) ^ max (E.P_fn m₀).p_s (E.P_fn m₀).p_t := pow_le_pow_left₀ hbase hlogC _
      _ ≤ (7 * logMN) ^ p_max := pow_le_pow_right₀ h1 hp_le
      _ = (7 : ℝ) ^ p_max * logMN ^ p_max := by rw [mul_pow]
  have hΛs_ge1 : 1 ≤ coreLambdaS (E.P_fn m₀) m₀ := coreLambdaS_ge_one _ m₀
  have hΛ_mul_Λs : Λ ≤ (7 : ℝ) ^ p_max * logMN ^ p_max * coreLambdaS (E.P_fn m₀) m₀ := by
    have := mul_le_mul_of_nonneg_left hΛs_ge1 (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ p_max * logMN ^ p_max)
    linarith
  have hrec_ge4 : 4 ≤ recEnv E m₀ := recEnv_ge_four E m₀
  have hrb_ge : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
  have hrb_nn : 0 ≤ recBase E m₀ := by linarith
  have hcm_ge1 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
  have hcm_nn : 0 ≤ costMult E m₀ := by linarith
  have hγr_ge4 : 4 ≤ recBase E m₀ * costMult E m₀ := by nlinarith
  have hT_nn : 0 ≤ T := by
    dsimp only [T]
    have : 0 ≤ logMN := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hrb_nn hcm_nn)) (pow_nonneg this _)
  have hp1 : (m₀ : ℝ) + (n_act : ℝ) + 1 ≤ (1 + E.c_n) * T := by
    have hactR : (n_act : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hn_act
    have hmn : (m₀ : ℝ) + (n_act : ℝ) + 1 ≤ 3 * ((m₀ : ℝ) + 1) := by linarith
    have h4_le : (4 : ℝ) ≤ (recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1) := by nlinarith
    have h3T : 3 * ((m₀ : ℝ) + 1) ≤ T := by
      have hstep := mul_le_mul_of_nonneg_left (show (3 : ℝ) ≤ (recBase E m₀ * costMult E m₀) *
        logMN ^ (p_max + 1) by linarith) (show (0 : ℝ) ≤ (m₀ : ℝ) + 1 by linarith)
      have hEq : ((m₀ : ℝ) + 1) * ((recBase E m₀ * costMult E m₀) * logMN ^ (p_max + 1)) = T := by
        dsimp only [T]; ring
      linarith
    have hcn_ge1 : (1 : ℝ) ≤ 1 + E.c_n := by linarith [E.hc_n]
    have hT_le : T ≤ (1 + E.c_n) * T := by nlinarith
    exact le_trans hmn (le_trans h3T hT_le)
  have hp2a := cost_piece2a E m₀ hLp1_cm hlogMN_ge1
  have hp2b := cost_piece2b E m₀ hKs_piece hγ_le_rec hLp1_cm hlogMN_ge1 hΛ_nn hΛ_bound hΛ_mul_Λs
  obtain ⟨hp3, hp3b, hp4⟩ := cost_piece34 E m₀ n_eff Δ₀ (E.B_fn m₀) q_τ
    hqτ_le_m0 le_rfl huc_le hrec_split hRec_le hlogMN_ge1
  have hlog_uc := log_ucBound_le_min m₀ n₀ hn₀_pos Δ₀ hΔ₀_raw q_τ hqτ_le_m0
  have hinit_split :
      ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) =
        ((E.L : ℝ) + 1) * (m₀ : ℝ) +
          ((E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 + (E.P_fn m₀).γ_ℓ +
            2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) := by ring
  have hbase_le :
      ((m₀ : ℝ) + (n_act : ℝ) + 1) +
        ((E.L : ℝ) + 1 + (E.P_fn m₀).K_t * (2 + (E.P_fn m₀).γ_ℓ ^ 2) * Λ + 3 +
          (E.P_fn m₀).γ_ℓ + 2 * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ * Λ) * (m₀ : ℝ) +
        (q_τ : ℝ) + 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ) +
        coreRecoursePerQ E.L (E.P_fn m₀) m₀ n_eff Δ₀ (E.B_fn m₀) * (q_τ : ℝ) ≤
          ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by
    have hsum_eq : (1 + E.c_n) * T + (T + (3 * (7 : ℝ) ^ p_max + 1) * T) + T + 2 * T + T =
        ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T := by ring
    linarith [hinit_split, hp1, hp2a, hp2b, hp3, hp3b, hp4, hsum_eq]
  refine ⟨hbase_le, fun q_ep => ?_, ?_⟩
  · exact cost_piece5_split E m₀ n_eff Δ₀ dC (E.B_fn m₀) q_ep q_τ
      le_rfl hdC_le huc_le hrec_split hKs_piece hlogMN_ge1 hlog_uc hΛ_nn hΛ_bound
  · have hcT_le : (7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max ≤ P.c_T := by
      dsimp only [P, sparseCoreParams]
      linarith only [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 7) (n := p_max), E.hc_n]
    have hFinal_eq : P.c_T * T =
        P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * logMN ^ P.p_T := by
      dsimp only [T, P, sparseCoreParams, p_max]
      ring
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hcT_le hT_nn) (le_of_eq hFinal_eq),
      hT_nn, mul_nonneg hrb_nn hcm_nn, hlogMN_ge1⟩

lemma treeRunSeq_cost_le_params_noComp_at (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (j : ℕ) (hj : j < k) :
    let P := sparseCoreParams E
    ((treeRunSeq oracle E.C_lsst E.L sparsify k M N D j τ).1.cost : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro P
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  have hCL := treeRunSeq_cost_le_active oracle E.C_lsst E.L E.hL (E.P_fn M)
    sparsify hHyps.hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps.hSp j hj
    (E.B_fn M) (hHyps.hB_bound j hj)
  dsimp only at hCL
  set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
  set ts₀ := fun C => initTildeState (cs₀.compSt C)
  set dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length
  obtain ⟨hbase, hd5, hfin, _, hγr_nn, hlogMN_ge1⟩ := cost_env_baseline_parts_noComp E M N
    (activeSubgraph (D.G 0)).n (D.G 0).maxDeg dC q_τ hN_pos
    (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
    (le_trans (maxDeg_le_two_m (D.G 0)) (Nat.mul_le_mul_left 2 hM))
    (by exact_mod_cast hHyps.hDeg_bound.1) (by exact_mod_cast hHyps.hDeg_bound.2 j hj)
  have hd5_tau := hd5 q_τ
  have hq_m1 : (q_τ : ℝ) ≤ (M : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqτ_le_M
    linarith
  have hfac_nn : 0 ≤ 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      ((recBase E M * costMult E M) * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
    have : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) := by linarith
    positivity
  have hq_T : 25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      ((q_τ : ℝ) * (recBase E M * costMult E M) * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) ≤
      25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
      (((M : ℝ) + 1) * (recBase E M * costMult E M) * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
    nlinarith [hq_m1, hfac_nn]
  have hring :
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
          (((M : ℝ) + 1) * (recBase E M * costMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) +
        (12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((M : ℝ) + 1) * (recBase E M * costMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) +
        25200 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((M : ℝ) + 1) * (recBase E M * costMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1))) =
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi +
          37800 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) *
        (((M : ℝ) + 1) * (recBase E M * costMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by ring
  linarith [hCL, hbase, hd5_tau, hq_T, hfin, hring]

lemma treeRunSeq_cost_le_params_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : SparseCoreCoreHyps E oracle sparsify k τ D)
    (j : ℕ) (hj : j < k) :
    let P := sparseCoreParams E
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j τ).1.cost : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T :=
  treeRunSeq_cost_le_params_noComp_at E oracle sparsify k (D.G 0).m (D.G 0).n τ D
    hk hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hHyps j hj

end

end MinCostFlow.SparseCore
