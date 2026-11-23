module

public import MinCostFlow.SparseCore.SparseCoreCost
public import MinCostFlow.Chain.SparseCoreNoHidden
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter Envelope and Omitted Hypotheses for Lemma 5.17

This file defines:
* `IsSpecNoHidden`: alias for `MinCostFlow.Chain.SparseCoreTool.IsSpecNoHidden`.
* `MonoSparsifyParams` and `SparseCoreEnv`: parameter and instance envelope `(L, P_fn, B_fn, d_fn,
  c_n, p_s_hi, p_t_hi)` producing explicit `sparseCoreParams E : SparseCoreParams` together with
  `sparseCoreParams_valid`.
* `SparseCoreInstanceHyps`: the clean, explicit instance boundedness hypotheses omitted by Lemma 5.17
  (`hB_bound`, `hDeg_bound`, `hComp_bound`, with no extra run hypotheses).
* Empty-vertex-set helpers (`empty_dyn_eq`, `sparseCoreTool_run_empty`) and logarithmic/threshold
  utilities (`updateThreshold_le_div_k`, `log_coreNMax_le`, `log_ucBound_le`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. `IsSpecNoHidden`, parameter envelope `SparseCoreEnv`, and `sparseCoreParams` -/

/-- `WeakHiddenStable`-free specification of `SparseCoreTool` needed by Theorem 5.1's worst-case
runtime analysis (`MinCostFlow.Chain.SparseCoreTool.IsSpecNoHidden`). -/
abbrev IsSpecNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  SparseCoreTool.IsSpecNoHidden T P

/-- Monotonicity of a `SparsifyParams` family with respect to the edge-count bound `mMax`. -/
def MonoSparsifyParams (P_fn : ℕ → SparsifyParams) : Prop :=
  ∀ ⦃m₁ m₂ : ℕ⦄, m₁ ≤ m₂ →
    (P_fn m₁).γ_c ≤ (P_fn m₂).γ_c ∧
    (P_fn m₁).γ_ℓ ≤ (P_fn m₂).γ_ℓ ∧
    (P_fn m₁).K_s ≤ (P_fn m₂).K_s ∧
    (P_fn m₁).p_s ≤ (P_fn m₂).p_s ∧
    (P_fn m₁).K_t ≤ (P_fn m₂).K_t ∧
    (P_fn m₁).p_t ≤ (P_fn m₂).p_t

lemma monoSparsifyParams_const (P_b : SparsifyParams) :
    MonoSparsifyParams (fun _ => P_b) :=
  fun _ _ _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Parameter and instance envelope for `sparseCoreTool` with depth `L` and static sparsifier
parameter family `P_fn`. Setting `B_fn m = max 1 m` and `d_fn m = 2 * m` holds unconditionally
for every valid graph; in the paper's bounded-degree/bounded-length regime `B_fn m = O(log m)` and
`d_fn m = Δ₀`. -/
structure SparseCoreEnv where
  C_lsst : ℝ
  L : ℕ
  hL : 1 ≤ L
  P_fn : ℕ → SparsifyParams
  hMono : MonoSparsifyParams P_fn
  p_s_hi : ℕ
  p_t_hi : ℕ
  hp_s : ∀ m, (P_fn m).p_s ≤ p_s_hi
  hp_t : ∀ m, (P_fn m).p_t ≤ p_t_hi
  B_fn : ℕ → ℕ
  hB_pos : ∀ m, 1 ≤ B_fn m
  hB_mono : Monotone B_fn
  d_fn : ℕ → ℕ
  hd_mono : Monotone d_fn
  c_n : ℝ
  hc_n : 1 ≤ c_n

noncomputable def ucRatioHi (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  (E.d_fn m : ℝ) + 1 + 56 * (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2

noncomputable def recEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  (E.B_fn m : ℝ) *
    ((3 + 2 * coreE82Len E.L (E.P_fn m)) * coreBucketRecUH E.L (E.P_fn m) m +
      2 * coreBucketRecD E.L (E.P_fn m) m) * (2 * ucRatioHi E m) +
    22 * (E.B_fn m : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
      coreLambdaS (E.P_fn m) m +
    7 + 224 * (Real.log (E.c_n * ((m : ℝ) + 1) + 2)) ^ 2

noncomputable def gammaLEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max (coreE82Len E.L (E.P_fn m))
    (11 * (((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
      coreLambdaS (E.P_fn m) m * (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) + 115))

noncomputable def encEnv (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  20 * max (gammaLEnv E m) (recEnv E m) *
    Real.log ((m : ℝ) + recEnv E m * (m : ℝ) + 2)

noncomputable def recBase (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max (recEnv E m) (encEnv E m)

noncomputable def costMult (E : SparseCoreEnv) (m : ℕ) : ℝ :=
  max 1 (coreE_L E.L (E.P_fn m) * ((E.d_fn m : ℝ) + 1) *
    ((E.P_fn m).K_t * (2 + (E.P_fn m).γ_ℓ ^ 2) + 1) *
    max 1 ((E.L : ℝ) * coreNRoot E.L m) * ((E.L : ℝ) + 1))

/-- Concrete `SparseCoreParams` associated with a `SparseCoreEnv`. -/
noncomputable def sparseCoreParams (E : SparseCoreEnv) : SparseCoreParams where
  σ := fun k n => max 1 (mwuK0 E.C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6)
  γ_ℓ := gammaLEnv E
  γ_c := fun m => 1 + coreE82Cong E.L (E.P_fn m) * (E.d_fn m : ℝ)
  γ_r := fun m => recBase E m * costMult E m
  c_R := 112
  c_T := 37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n
  p_T := max E.p_s_hi E.p_t_hi + 1

/-! ## 2. Positivity, monotonicity, and `SparseCoreParams.Valid` -/

lemma coreNMax_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : coreNMax m₁ ≤ coreNMax m₂ := by
  unfold coreNMax coreSplitMax
  gcongr

lemma coreNRoot_ge_one (L m : ℕ) : 1 ≤ coreNRoot L m := by
  unfold coreNRoot
  by_cases hL0 : L = 0
  · subst hL0; simp
  · have hge1 : (1 : ℝ) ≤ (max (coreNMax m) 1 : ℕ) := by
      exact_mod_cast le_max_right (coreNMax m) 1
    exact Real.one_le_rpow hge1 (by positivity)

lemma coreNRoot_mono {L m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : coreNRoot L m₁ ≤ coreNRoot L m₂ := by
  unfold coreNRoot
  have h1 : (max (coreNMax m₁) 1 : ℝ) ≤ (max (coreNMax m₂) 1 : ℕ) := by
    exact_mod_cast max_le_max_right 1 (coreNMax_mono h)
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1) (by positivity)

lemma coreE82Len_ge_three (L : ℕ) (hL : 1 ≤ L) (P_b : SparsifyParams) :
    (3 : ℝ) ≤ coreE82Len L P_b := by
  unfold coreE82Len
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ L := by
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (3 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hL
  have hγ : 1 ≤ P_b.γ_ℓ ^ (L + 1) := one_le_pow₀ P_b.hγ_ℓ
  nlinarith

lemma coreE82Len_mono {L : ℕ} {P₁ P₂ : SparsifyParams}
    (hγ : P₁.γ_ℓ ≤ P₂.γ_ℓ) : coreE82Len L P₁ ≤ coreE82Len L P₂ := by
  unfold coreE82Len
  have hγ₁ : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  gcongr

lemma coreE82Cong_nonneg (L : ℕ) (P_b : SparsifyParams) : 0 ≤ coreE82Cong L P_b := by
  unfold coreE82Cong
  have h1 : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have h2 : 0 ≤ P_b.γ_c := by linarith [P_b.hγ_c]
  positivity

lemma coreE82Cong_mono {L : ℕ} {P₁ P₂ : SparsifyParams}
    (hγc : P₁.γ_c ≤ P₂.γ_c) (hγℓ : P₁.γ_ℓ ≤ P₂.γ_ℓ) :
    coreE82Cong L P₁ ≤ coreE82Cong L P₂ := by
  unfold coreE82Cong
  have h1 : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  have h2 : 0 ≤ P₁.γ_c := by linarith [P₁.hγ_c]
  have h1' : 0 ≤ P₂.γ_ℓ := by linarith [P₂.hγ_ℓ]
  have h2' : 0 ≤ P₂.γ_c := by linarith [P₂.hγ_c]
  have hpowℓ : P₁.γ_ℓ ^ (L * (L + 1) / 2) ≤ P₂.γ_ℓ ^ (L * (L + 1) / 2) :=
    pow_le_pow_left₀ h1 hγℓ _
  have hpowc : P₁.γ_c ^ (L + 1) ≤ P₂.γ_c ^ (L + 1) :=
    pow_le_pow_left₀ h2 hγc _
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2) := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpowℓ h3) (by positivity) |>.trans
    (mul_le_mul_of_nonneg_left hpowc (by positivity))

lemma coreLambdaS_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    coreLambdaS (E.P_fn m₁) m₁ ≤ coreLambdaS (E.P_fn m₂) m₂ := by
  unfold coreLambdaS
  have harg1 : (1 : ℝ) ≤ (coreNMax m₁ : ℝ) + (m₁ : ℝ) + 2 := by linarith
  have harg2 : (coreNMax m₁ : ℝ) + (m₁ : ℝ) + 2 ≤ (coreNMax m₂ : ℝ) + (m₂ : ℝ) + 2 := by
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    have : (coreNMax m₁ : ℝ) ≤ (coreNMax m₂ : ℝ) := by exact_mod_cast coreNMax_mono h
    linarith
  have hbase1 : 1 ≤ 1 + Real.log ((coreNMax m₁ : ℝ) + (m₁ : ℝ) + 2) := by
    linarith [Real.log_nonneg harg1]
  have hbase_le :
      1 + Real.log ((coreNMax m₁ : ℝ) + (m₁ : ℝ) + 2) ≤
        1 + Real.log ((coreNMax m₂ : ℝ) + (m₂ : ℝ) + 2) :=
    add_le_add le_rfl (Real.log_le_log (by linarith) harg2)
  exact le_trans
    (pow_le_pow_left₀ (by linarith) hbase_le _)
    (pow_le_pow_right₀ (by linarith) (E.hMono h).2.2.2.1)

lemma coreE_L_ge_one (L : ℕ) (P_b : SparsifyParams) : 1 ≤ coreE_L L P_b := by
  unfold coreE_L
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) := by
    exact_mod_cast Nat.one_le_pow _ 3 (by norm_num)
  have h2 : 1 ≤ P_b.γ_c ^ (L + 1) := one_le_pow₀ P_b.hγ_c
  have h3 : 1 ≤ P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := one_le_pow₀ P_b.hγ_ℓ
  nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]

lemma coreE_L_mono {L : ℕ} {P₁ P₂ : SparsifyParams}
    (hγc : P₁.γ_c ≤ P₂.γ_c) (hγℓ : P₁.γ_ℓ ≤ P₂.γ_ℓ) :
    coreE_L L P₁ ≤ coreE_L L P₂ := by
  unfold coreE_L
  have h1 : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  have h2 : 0 ≤ P₁.γ_c := by linarith [P₁.hγ_c]
  have hpowc : P₁.γ_c ^ (L + 1) ≤ P₂.γ_c ^ (L + 1) := pow_le_pow_left₀ h2 hγc _
  have hpowℓ : P₁.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) ≤ P₂.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
    pow_le_pow_left₀ h1 hγℓ _
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpowc h3) hpowℓ (by positivity) (by
    have := P₂.hγ_c; positivity)

lemma coreBucketRec_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    coreBucketRecUH E.L (E.P_fn m₁) m₁ ≤ coreBucketRecUH E.L (E.P_fn m₂) m₂ ∧
    coreBucketRecD E.L (E.P_fn m₁) m₁ ≤ coreBucketRecD E.L (E.P_fn m₂) m₂ := by
  have hm := E.hMono h
  have hKs_le := hm.2.2.1
  have hγ_le := hm.2.1
  have hnr := coreNRoot_mono (L := E.L) h
  have hls := coreLambdaS_mono E h
  have hnr1 : 0 ≤ coreNRoot E.L m₁ := by linarith [coreNRoot_ge_one E.L m₁]
  have hnr2 : 0 ≤ coreNRoot E.L m₂ := by linarith [coreNRoot_ge_one E.L m₂]
  have hls1 : 0 ≤ coreLambdaS (E.P_fn m₁) m₁ := coreLambdaS_pos _ _
  have hls2 : 0 ≤ coreLambdaS (E.P_fn m₂) m₂ := coreLambdaS_pos _ _
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hγℓ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hL_nn : (0 : ℝ) ≤ (E.L : ℝ) := Nat.cast_nonneg _
  have hp1 : 12 * (E.L : ℝ) * coreNRoot E.L m₁ * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ ≤
      12 * (E.L : ℝ) * coreNRoot E.L m₂ * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ := by
    have ha := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ 12 * (E.L : ℝ))
    have hb := mul_le_mul ha hKs_le hKs1 (by positivity)
    exact mul_le_mul hb hγ_le hγℓ1 (by positivity)
  constructor
  · unfold coreBucketRecUH
    have hc := mul_le_mul hp1 hls hls1 (by positivity)
    linarith
  · unfold coreBucketRecD
    have hpow : (3 : ℝ) ^ E.L * (E.P_fn m₁).γ_ℓ ^ (E.L + 1) + 1 ≤
        (3 : ℝ) ^ E.L * (E.P_fn m₂).γ_ℓ ^ (E.L + 1) + 1 := by
      have hp := pow_le_pow_left₀ hγℓ1 hγ_le (E.L + 1)
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ E.L := by positivity
      linarith [mul_le_mul_of_nonneg_left hp h3]
    have h6 : 6 * (E.L : ℝ) * coreNRoot E.L m₁ * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ ≤
        6 * (E.L : ℝ) * coreNRoot E.L m₂ * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ := by
      have ha := mul_le_mul_of_nonneg_left hnr (by positivity : 0 ≤ 6 * (E.L : ℝ))
      have hb := mul_le_mul ha hKs_le hKs1 (by positivity)
      exact mul_le_mul hb hγ_le hγℓ1 (by positivity)
    have hd1 := mul_le_mul h6 hpow (by positivity) (by positivity)
    exact mul_le_mul hd1 hls hls1 (by positivity)

lemma ucRatioHi_ge_one (E : SparseCoreEnv) (m : ℕ) : 1 ≤ ucRatioHi E m := by
  unfold ucRatioHi
  have harg : (1 : ℝ) ≤ E.c_n * ((m : ℝ) + 1) + 2 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [E.hc_n]
  nlinarith [Nat.cast_nonneg (α := ℝ) (E.d_fn m),
    sq_nonneg (Real.log (E.c_n * ((m : ℝ) + 1) + 2))]

lemma ucRatioHi_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    ucRatioHi E m₁ ≤ ucRatioHi E m₂ := by
  unfold ucRatioHi
  have h1 : (1 : ℝ) ≤ E.c_n * ((m₁ : ℝ) + 1) + 2 := by
    have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁
    nlinarith [E.hc_n]
  have hlog1 : 0 ≤ Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) := Real.log_nonneg h1
  have harg : E.c_n * ((m₁ : ℝ) + 1) + 2 ≤ E.c_n * ((m₂ : ℝ) + 1) + 2 := by
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    nlinarith [E.hc_n]
  have hlog_le : Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) ≤ Real.log (E.c_n * ((m₂ : ℝ) + 1) + 2) :=
    Real.log_le_log (by linarith) harg
  have hd_le : (E.d_fn m₁ : ℝ) ≤ (E.d_fn m₂ : ℝ) := by exact_mod_cast E.hd_mono h
  gcongr

lemma recEnv_ge_four (E : SparseCoreEnv) (m : ℕ) : (4 : ℝ) ≤ recEnv E m := by
  unfold recEnv
  have h1 : 0 ≤ (E.B_fn m : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ coreBucketRecUH E.L (E.P_fn m) m := (coreBucketRec_pos E.L _ m).1
  have h3 : 0 ≤ coreBucketRecD E.L (E.P_fn m) m := (coreBucketRec_pos E.L _ m).2.1
  have h4 : 0 ≤ coreE82Len E.L (E.P_fn m) := (coreBucketRec_pos E.L _ m).2.2
  have h5 : 0 ≤ ucRatioHi E m := by linarith [ucRatioHi_ge_one E m]
  have hKs := (E.P_fn m).hK_s
  have hγℓ : 0 ≤ (E.P_fn m).γ_ℓ := by linarith [(E.P_fn m).hγ_ℓ]
  have hls := coreLambdaS_pos (E.P_fn m) m
  have ht1 : 0 ≤ (E.B_fn m : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m)) *
      coreBucketRecUH E.L (E.P_fn m) m + 2 * coreBucketRecD E.L (E.P_fn m) m) *
      (2 * ucRatioHi E m) := by
    positivity
  have ht2 : 0 ≤ 22 * (E.B_fn m : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m).K_s *
      (E.P_fn m).γ_ℓ * coreLambdaS (E.P_fn m) m := by positivity
  nlinarith [sq_nonneg (Real.log (E.c_n * ((m : ℝ) + 1) + 2))]

lemma recEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    recEnv E m₁ ≤ recEnv E m₂ := by
  unfold recEnv
  have hm := E.hMono h
  have hB : (E.B_fn m₁ : ℝ) ≤ (E.B_fn m₂ : ℝ) := by exact_mod_cast E.hB_mono h
  have hL1 := coreE82Len_mono (L := E.L) hm.2.1
  have hrec := coreBucketRec_mono E h
  have huc := ucRatioHi_mono E h
  have hls_le := coreLambdaS_mono E h
  have h1 : (1 : ℝ) ≤ E.c_n * ((m₁ : ℝ) + 1) + 2 := by
    have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁
    nlinarith [E.hc_n]
  have hlog1 : 0 ≤ Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) := Real.log_nonneg h1
  have hlog_le : Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2) ≤ Real.log (E.c_n * ((m₂ : ℝ) + 1) + 2) := by
    refine Real.log_le_log (by linarith) ?_
    have : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
    nlinarith [E.hc_n]
  have hUH_nn : 0 ≤ coreBucketRecUH E.L (E.P_fn m₁) m₁ := (coreBucketRec_pos E.L _ m₁).1
  have hD_nn : 0 ≤ coreBucketRecD E.L (E.P_fn m₁) m₁ := (coreBucketRec_pos E.L _ m₁).2.1
  have hLen_nn : 0 ≤ coreE82Len E.L (E.P_fn m₁) := (coreBucketRec_pos E.L _ m₁).2.2
  have hLen2_nn : 0 ≤ coreE82Len E.L (E.P_fn m₂) := (coreBucketRec_pos E.L _ m₂).2.2
  have hUH2_nn : 0 ≤ coreBucketRecUH E.L (E.P_fn m₂) m₂ := (coreBucketRec_pos E.L _ m₂).1
  have hD2_nn : 0 ≤ coreBucketRecD E.L (E.P_fn m₂) m₂ := (coreBucketRec_pos E.L _ m₂).2.1
  have huc_nn : 0 ≤ 2 * ucRatioHi E m₁ := by linarith [ucRatioHi_ge_one E m₁]
  have hbracket_nn : 0 ≤ (3 + 2 * coreE82Len E.L (E.P_fn m₁)) *
      coreBucketRecUH E.L (E.P_fn m₁) m₁ + 2 * coreBucketRecD E.L (E.P_fn m₁) m₁ := by positivity
  have hB_nn : (0 : ℝ) ≤ (E.B_fn m₁ : ℝ) := Nat.cast_nonneg _
  have hB2_nn : (0 : ℝ) ≤ (E.B_fn m₂ : ℝ) := Nat.cast_nonneg _
  have hbr_le : (3 + 2 * coreE82Len E.L (E.P_fn m₁)) * coreBucketRecUH E.L (E.P_fn m₁) m₁ +
        2 * coreBucketRecD E.L (E.P_fn m₁) m₁ ≤
      (3 + 2 * coreE82Len E.L (E.P_fn m₂)) * coreBucketRecUH E.L (E.P_fn m₂) m₂ +
        2 * coreBucketRecD E.L (E.P_fn m₂) m₂ :=
    add_le_add (mul_le_mul (by linarith) hrec.1 hUH_nn (by linarith)) (by linarith [hrec.2])
  have hmul1 : (E.B_fn m₁ : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m₁)) *
        coreBucketRecUH E.L (E.P_fn m₁) m₁ + 2 * coreBucketRecD E.L (E.P_fn m₁) m₁) *
        (2 * ucRatioHi E m₁) ≤
      (E.B_fn m₂ : ℝ) * ((3 + 2 * coreE82Len E.L (E.P_fn m₂)) *
        coreBucketRecUH E.L (E.P_fn m₂) m₂ + 2 * coreBucketRecD E.L (E.P_fn m₂) m₂) *
        (2 * ucRatioHi E m₂) :=
    mul_le_mul (mul_le_mul hB hbr_le hbracket_nn hB2_nn) (by linarith) huc_nn (by positivity)
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hls1 : 0 ≤ coreLambdaS (E.P_fn m₁) m₁ := coreLambdaS_pos _ _
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγℓ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hKs_le := hm.2.2.1
  have hγ_le := hm.2.1
  have hmul2 : 22 * (E.B_fn m₁ : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m₁).K_s * (E.P_fn m₁).γ_ℓ *
        coreLambdaS (E.P_fn m₁) m₁ ≤
      22 * (E.B_fn m₂ : ℝ) * ((E.L : ℝ) + 1) * (E.P_fn m₂).K_s * (E.P_fn m₂).γ_ℓ *
        coreLambdaS (E.P_fn m₂) m₂ := by
    gcongr
  have hsq_le : (Real.log (E.c_n * ((m₁ : ℝ) + 1) + 2)) ^ 2 ≤
      (Real.log (E.c_n * ((m₂ : ℝ) + 1) + 2)) ^ 2 := pow_le_pow_left₀ hlog1 hlog_le 2
  linarith

lemma gammaLEnv_ge_three (E : SparseCoreEnv) (m : ℕ) : (3 : ℝ) ≤ gammaLEnv E m :=
  le_trans (coreE82Len_ge_three E.L E.hL (E.P_fn m)) (le_max_left _ _)

lemma gammaLEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    gammaLEnv E m₁ ≤ gammaLEnv E m₂ := by
  unfold gammaLEnv
  have hm := E.hMono h
  have hLen := coreE82Len_mono (L := E.L) hm.2.1
  have hKs1 : 0 ≤ (E.P_fn m₁).K_s := (E.P_fn m₁).hK_s
  have hKs2 : 0 ≤ (E.P_fn m₂).K_s := (E.P_fn m₂).hK_s
  have hγ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hγ2 : 0 ≤ (E.P_fn m₂).γ_ℓ := by linarith [(E.P_fn m₂).hγ_ℓ]
  have hls1 : 0 ≤ coreLambdaS (E.P_fn m₁) m₁ := coreLambdaS_pos _ _
  have hls2 : 0 ≤ coreLambdaS (E.P_fn m₂) m₂ := coreLambdaS_pos _ _
  have hls_le := coreLambdaS_mono E h
  have hB_le : (E.B_fn m₁ : ℝ) ≤ (E.B_fn m₂ : ℝ) := by exact_mod_cast E.hB_mono h
  have hd_le : (E.d_fn m₁ : ℝ) ≤ (E.d_fn m₂ : ℝ) := by exact_mod_cast E.hd_mono h
  have hB1 : (0 : ℝ) ≤ (E.B_fn m₁ : ℝ) := Nat.cast_nonneg _
  have hd1 : (0 : ℝ) ≤ 2 * (E.d_fn m₁ : ℝ) + 190 := by positivity
  have hKs_le := hm.2.2.1
  have hγ_le := hm.2.1
  refine max_le_max hLen ?_
  gcongr

lemma encEnv_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    encEnv E m₁ ≤ encEnv E m₂ := by
  unfold encEnv
  have hL1 := gammaLEnv_mono E h
  have hR := recEnv_mono E h
  have hR_nn : 0 ≤ recEnv E m₁ := by linarith [recEnv_ge_four E m₁]
  have hm_le : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
  have hlog1 : 0 ≤ Real.log ((m₁ : ℝ) + recEnv E m₁ * (m₁ : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁
    nlinarith
  have hlog_le : Real.log ((m₁ : ℝ) + recEnv E m₁ * (m₁ : ℝ) + 2) ≤
      Real.log ((m₂ : ℝ) + recEnv E m₂ * (m₂ : ℝ) + 2) := by
    refine Real.log_le_log ?_ ?_
    · have : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁; nlinarith
    · nlinarith [Nat.cast_nonneg (α := ℝ) m₁]
  have hmax_le : max (gammaLEnv E m₁) (recEnv E m₁) ≤
      max (gammaLEnv E m₂) (recEnv E m₂) := max_le_max hL1 hR
  have hmax_nn : 0 ≤ max (gammaLEnv E m₁) (recEnv E m₁) :=
    le_trans hR_nn (le_max_right _ _)
  have hmax2_nn : 0 ≤ max (gammaLEnv E m₂) (recEnv E m₂) :=
    le_trans hmax_nn hmax_le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmax_le (by norm_num)) hlog_le hlog1 (by linarith)

lemma costMult_ge_one (E : SparseCoreEnv) (m : ℕ) : 1 ≤ costMult E m :=
  le_max_left _ _

lemma costMult_mono (E : SparseCoreEnv) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    costMult E m₁ ≤ costMult E m₂ := by
  unfold costMult
  have hm := E.hMono h
  have hγ_le := hm.2.1
  have hKt_le := hm.2.2.2.2.1
  have hKt2 := (E.P_fn m₂).hK_t
  have hE := coreE_L_mono (L := E.L) hm.1 hm.2.1
  have hE2 := coreE_L_ge_one E.L (E.P_fn m₂)
  have hd : (E.d_fn m₁ : ℝ) + 1 ≤ (E.d_fn m₂ : ℝ) + 1 := by
    have : (E.d_fn m₁ : ℝ) ≤ (E.d_fn m₂ : ℝ) := by exact_mod_cast E.hd_mono h
    linarith
  have hnr := coreNRoot_mono (L := E.L) h
  have hK1 : 0 ≤ (E.P_fn m₁).K_t := (E.P_fn m₁).hK_t
  have hγℓ1 : 0 ≤ (E.P_fn m₁).γ_ℓ := by linarith [(E.P_fn m₁).hγ_ℓ]
  have hE1 : 0 ≤ coreE_L E.L (E.P_fn m₁) := by linarith [coreE_L_ge_one E.L (E.P_fn m₁)]
  have hL_nn : (0 : ℝ) ≤ (E.L : ℝ) := Nat.cast_nonneg _
  have hd1_nn : (0 : ℝ) ≤ (E.d_fn m₁ : ℝ) + 1 := by positivity
  have hkt_nn : 0 ≤ (E.P_fn m₁).K_t * (2 + (E.P_fn m₁).γ_ℓ ^ 2) + 1 := by positivity
  have hnr_nn : 0 ≤ coreNRoot E.L m₁ := by linarith [coreNRoot_ge_one E.L m₁]
  have hmx_nn : 0 ≤ max 1 ((E.L : ℝ) * coreNRoot E.L m₁) := by positivity
  have hL1_nn : (0 : ℝ) ≤ (E.L : ℝ) + 1 := by positivity
  refine max_le_max le_rfl ?_
  gcongr

theorem sparseCoreParams_valid (E : SparseCoreEnv) : (sparseCoreParams E).Valid := by
  dsimp only [SparseCoreParams.Valid, sparseCoreParams]
  have hK₀ : 0 < mwuK0 E.C_lsst := mwuK0_pos E.C_lsst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_⟩
  · intro _ _ _; exact le_max_left _ _
  · intro k₁ k₂ n₁ n₂ hk hn
    refine max_le_max le_rfl ?_
    have hk' : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hk
    have hlog1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := by linarith [half_lt_log_add_two n₁]
    have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) := by
      refine Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₁]) ?_
      have : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
      linarith
    gcongr
  · intro m; linarith [gammaLEnv_ge_three E m]
  · intro m₁ m₂ h; exact gammaLEnv_mono E h
  · intro m
    have h1 := coreE82Cong_nonneg E.L (E.P_fn m)
    have h2 : (0 : ℝ) ≤ (E.d_fn m : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro m₁ m₂ h
    have h1 := coreE82Cong_nonneg E.L (E.P_fn m₁)
    have h2 : (E.d_fn m₁ : ℝ) ≤ (E.d_fn m₂ : ℝ) := by exact_mod_cast E.hd_mono h
    have hm := E.hMono h
    have h3 := coreE82Cong_mono (L := E.L) hm.1 hm.2.1
    linarith [mul_le_mul h3 h2 (Nat.cast_nonneg _) (by linarith)]
  · intro m
    have h1 : 4 ≤ recBase E m := le_trans (recEnv_ge_four E m) (le_max_left _ _)
    have h2 : 1 ≤ costMult E m := costMult_ge_one E m
    nlinarith
  · intro m₁ m₂ h
    have hrb : recBase E m₁ ≤ recBase E m₂ := max_le_max (recEnv_mono E h) (encEnv_mono E h)
    have hcm := costMult_mono E h
    have h1 : 0 ≤ recBase E m₁ := le_trans (by linarith [recEnv_ge_four E m₁]) (le_max_left _ _)
    have h2 : 0 ≤ costMult E m₁ := by linarith [costMult_ge_one E m₁]
    have hcm2 : 0 ≤ costMult E m₂ := by linarith [costMult_ge_one E m₂]
    exact mul_le_mul hrb hcm h2 (by linarith)
  · have : (0 : ℝ) ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := by positivity
    linarith [E.hc_n]

/-! ## 3. Instance hypotheses omitted from Lemma 5.17, empty-graph & log helpers -/

/-- The four per-instance boundedness hypotheses of `sparseCoreTool` / `sparseCoreRestartTool`
at edge-count scale `M` (with `(D.G 0).m ≤ M`) and without `hComp_bound`. -/
structure SparseCoreCoreHypsAt (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M : ℕ) (D : DynamicInstance) : Prop where
  hLSST : HasLSSTSpec oracle E.C_lsst
  hSp : SparsifySpec M (E.P_fn M) (sparsify M)
  hB_bound : ∀ j < k,
    let cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
    ∀ C ∈ components (D.G 0),
      ((initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))).card ≤ E.B_fn M
  hDeg_bound : (D.G 0).maxDeg ≤ E.d_fn M ∧
    ∀ j < k,
      let cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
      (components (D.G 0)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤
        E.d_fn M

/-- Special case of `SparseCoreCoreHypsAt` at `M = (D.G 0).m`. -/
abbrev SparseCoreCoreHyps (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k _τ : ℕ) (D : DynamicInstance) : Prop :=
  SparseCoreCoreHypsAt E oracle sparsify k (D.G 0).m D

/-- The explicit per-instance boundedness hypotheses omitted by the paper's Lemma 5.17 statement
(including the `hComp_bound` field). -/
structure SparseCoreInstanceHyps (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) : Prop where
  hLSST : HasLSSTSpec oracle E.C_lsst
  hSp : SparsifySpec (D.G 0).m (E.P_fn (D.G 0).m) (sparsify (D.G 0).m)
  hB_bound : ∀ j < k,
    let cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
    ∀ C ∈ components (D.G 0),
      ((initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))).card ≤ E.B_fn (D.G 0).m
  hDeg_bound : (D.G 0).maxDeg ≤ E.d_fn (D.G 0).m ∧
    ∀ j < k,
      let cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
      (components (D.G 0)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤
        E.d_fn (D.G 0).m
  hComp_bound : ((D.G 0).n : ℝ) ≤ E.c_n * (((D.G 0).m : ℝ) + 1)

theorem SparseCoreInstanceHyps.toCoreHyps {E : SparseCoreEnv}
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k τ : ℕ} {D : DynamicInstance}
    (h : SparseCoreInstanceHyps E oracle sparsify k τ D) :
    SparseCoreCoreHyps E oracle sparsify k τ D where
  hLSST := h.hLSST
  hSp := h.hSp
  hB_bound := h.hB_bound
  hDeg_bound := h.hDeg_bound

lemma min_le_cn_mul_m_add_one (E : SparseCoreEnv) (m₀ n₀ : ℕ) :
    ((min n₀ (m₀ + 1) : ℕ) : ℝ) ≤ E.c_n * ((m₀ : ℝ) + 1) := by
  have h1 : ((min n₀ (m₀ + 1) : ℕ) : ℝ) ≤ (m₀ : ℝ) + 1 := by
    have : min n₀ (m₀ + 1) ≤ m₀ + 1 := min_le_right _ _
    exact_mod_cast this
  have h2 : (m₀ : ℝ) + 1 ≤ E.c_n * ((m₀ : ℝ) + 1) := by
    have hm : (0 : ℝ) ≤ (m₀ : ℝ) + 1 := by positivity
    nlinarith [E.hc_n]
  exact le_trans h1 h2

lemma empty_batch_eq_nil {G : MGraph} (hV : ¬ G.V.Nonempty) (hG : G.IsValid)
    {U : List Update} (hBV : G.BatchIsValid U) : U = [] := by
  cases U with
  | nil => rfl
  | cons u _ =>
    exfalso
    cases u with
    | insert e v₁ v₂ => exact hV ⟨v₁, hBV.1.2.1⟩
    | delete e => exact hV ⟨G.tail e, (hG e hBV.1).1⟩
    | split v _ _ _ => exact hV ⟨v, hBV.1.1⟩

lemma empty_dyn_eq {τ : ℕ} {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : ¬ (D.G 0).V.Nonempty) (hD : D.IsValid τ) :
    (∀ t ≤ τ, ¬ (D.G t).V.Nonempty ∧ (D.G t).IsValid ∧ (D.G t).E = ∅) ∧
    (∀ t, 1 ≤ t → t ≤ τ → D.U t = []) := by
  have h₀E : (D.G 0).E = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he; exact hV₀ ⟨(D.G 0).tail e, (hG₀ e he).1⟩
  have hbase : ∀ t ≤ τ, ¬ (D.G t).V.Nonempty ∧ (D.G t).IsValid ∧ (D.G t).E = ∅ := by
    intro t ht
    induction t with
    | zero => exact ⟨hV₀, hG₀, h₀E⟩
    | succ s ih =>
      rcases ih (Nat.le_of_succ_le ht) with ⟨hVs, hGs, hEs⟩
      have hst := hD (s + 1) (Nat.succ_pos s) ht
      simp only [Nat.add_sub_cancel] at hst
      have hU : D.U (s + 1) = [] := empty_batch_eq_nil hVs hGs hst.1
      have hG_eq : D.G (s + 1) = D.G s := by rw [hst.2, hU]; rfl
      rw [hG_eq]
      exact ⟨hVs, hGs, hEs⟩
  refine ⟨hbase, fun t ht1 htτ => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hst := hD s.succ (Nat.succ_pos s) htτ
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one] at hst
  rcases hbase s (Nat.le_of_succ_le htτ) with ⟨hVs, hGs, _⟩
  exact empty_batch_eq_nil hVs hGs hst.1

lemma sparseCoreToolWith_runAt_empty (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).runAt k M N D t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] := by
  intro t
  induction t with
  | zero =>
    dsimp only [SparseCoreTool.runAt, sparseCoreToolWith]
    simp only [hV₀, ↓reduceIte]
    exact ⟨trivial, trivial⟩
  | succ s ih =>
    dsimp only [SparseCoreTool.runAt]
    rcases ih with ⟨hne, _⟩
    dsimp only [sparseCoreToolWith] at hne ⊢
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, trivial⟩

lemma sparseCoreToolWith_run_empty (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).run k D t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] :=
  sparseCoreToolWith_runAt_empty reinsertD oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀

lemma sparseCoreTool_runAt_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] :=
  sparseCoreToolWith_runAt_empty true oracle C_lsst L sparsify k M N D hV₀

lemma sparseCoreTool_run_empty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : ¬ (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreTool oracle C_lsst L sparsify).run k D t
      r.1.isNonempty = false ∧ r.2 = fun _ => [] :=
  sparseCoreToolWith_run_empty true oracle C_lsst L sparsify k D hV₀

lemma updateThreshold_le_div_k_at {k M N τ : ℕ} {D : DynamicInstance} (hk : 0 < k)
    (hN : 1 ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N) :
    ∀ t ≤ τ, (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      (M : ℝ) / (k : ℝ) ∧
    (Finset.Icc 1 t).sum (fun s => (D.U s).length) ≤ M := by
  intro t ht
  have hqt_le_qτ :
      (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right ht)
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog_gt : (21 / 20 : ℝ) < Real.log ((N : ℝ) + 2) :=
    lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (N : ℝ) + 2) (by norm_num)
        (by linarith [show (1 : ℝ) ≤ (N : ℝ) from by exact_mod_cast hN]))
  have hlog2 : (1 : ℝ) ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := by nlinarith
  have hth_le : SparseCoreTool.updateThreshold k M N ≤ (M : ℝ) / (k : ℝ) := by
    rw [SparseCoreTool.updateThreshold, ← div_div]
    exact div_le_self (by positivity) hlog2
  have hdiv_le : (M : ℝ) / (k : ℝ) ≤ (M : ℝ) := div_le_self (Nat.cast_nonneg _) hk_ge1
  have hqR : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ (M : ℝ) / (k : ℝ) :=
    le_trans (le_trans hqt_le_qτ hThresh) hth_le
  exact ⟨hqR, by exact_mod_cast le_trans hqR hdiv_le⟩

lemma updateThreshold_le_div_k {k τ : ℕ} {D : DynamicInstance} (hk : 0 < k)
    (hG₀ : (D.G 0).IsValid)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n) :
    ∀ t ≤ τ, (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      ((D.G 0).m : ℝ) / (k : ℝ) ∧
    (Finset.Icc 1 t).sum (fun s => (D.U s).length) ≤ (D.G 0).m := by
  intro t ht
  by_cases hm₀ : (D.G 0).m = 0
  · have hqt_le_qτ :
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
          (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right ht)
    have hth0 : SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n = 0 := by
      rw [SparseCoreTool.updateThreshold, hm₀, Nat.cast_zero, zero_div]
    have hq0 : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ 0 := by
      linarith
    have hq_eq : (Finset.Icc 1 t).sum (fun s => (D.U s).length) = 0 :=
      Nat.eq_zero_of_le_zero (by exact_mod_cast hq0)
    rw [hq_eq, hm₀]
    simp
  · obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm₀)
    have hn₀ : 1 ≤ (D.G 0).n := Finset.card_pos.mpr ⟨(D.G 0).tail e₀, (hG₀ e₀ he₀).1⟩
    exact updateThreshold_le_div_k_at hk hn₀ hThresh t ht

lemma log_coreNMax_le (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) :
    1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hlog3 : (1 : ℝ) ≤ Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
    have := lt_of_lt_of_le real_log_three_gt
      (Real.log_le_log (x := 3) (y := (m₀ : ℝ) + (n₀ : ℝ) + 2) (by norm_num) (by linarith))
    linarith
  have harg : (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 ≤ ((m₀ : ℝ) + (n₀ : ℝ) + 2) ^ 6 := by
    have hcN : (coreNMax m₀ : ℝ) = 2 * (m₀ : ℝ) ^ 2 + 59 * (m₀ : ℝ) := by
      unfold coreNMax coreSplitMax
      push_cast
      ring
    have hsq1 : 2 * (m₀ : ℝ) ^ 2 + 60 * (m₀ : ℝ) + 2 ≤ 65 * ((m₀ : ℝ) + 1) ^ 2 := by nlinarith
    have h65 : (65 : ℝ) ≤ ((m₀ : ℝ) + 3) ^ 4 := by
      have h34 : (81 : ℝ) ≤ ((m₀ : ℝ) + 3) ^ 4 := by
        have : (3 : ℝ) ≤ (m₀ : ℝ) + 3 := by linarith
        calc (81 : ℝ) = 3 ^ 4 := by norm_num
          _ ≤ ((m₀ : ℝ) + 3) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
      linarith
    have hpow6 : 65 * ((m₀ : ℝ) + 1) ^ 2 ≤ ((m₀ : ℝ) + 3) ^ 6 := by
      calc 65 * ((m₀ : ℝ) + 1) ^ 2 ≤ ((m₀ : ℝ) + 3) ^ 4 * ((m₀ : ℝ) + 3) ^ 2 := by
            refine mul_le_mul h65 (pow_le_pow_left₀ (by linarith) (by linarith) 2)
              (by positivity) (by positivity)
        _ = ((m₀ : ℝ) + 3) ^ 6 := by ring
    have hmon : ((m₀ : ℝ) + 3) ^ 6 ≤ ((m₀ : ℝ) + (n₀ : ℝ) + 2) ^ 6 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 6
    linarith [hsq1, hpow6, hmon, hcN]
  have hlog_le : Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2) ≤
      6 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
    calc Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)
        ≤ Real.log (((m₀ : ℝ) + (n₀ : ℝ) + 2) ^ 6) := Real.log_le_log (by positivity) harg
      _ = 6 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
          rw [Real.log_pow]; norm_num
  linarith

lemma log_ucBound_le (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) (Δ₀ : ℕ) (hΔ : Δ₀ ≤ 2 * m₀)
    (q_τ : ℕ) (hq : q_τ ≤ m₀) :
    Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg m₀
  have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hΔR : (Δ₀ : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hΔ
  have hqR : (q_τ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq
  set X := (m₀ : ℝ) + (n₀ : ℝ) + 2
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hmX : (m₀ : ℝ) ≤ X := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2
      _ = 1 := Real.log_exp 1
  have hlog_X : Real.log ((n₀ : ℝ) + 2) ≤ X / 2 := by
    have h1 : Real.log ((n₀ : ℝ) + 2) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by linarith)
    have hX2 : Real.log X = Real.log 2 + Real.log (X / 2) := by
      have : X = 2 * (X / 2) := by ring
      conv_lhs => rw [this, Real.log_mul (by norm_num) (by linarith)]
    have hX_sub := Real.log_le_sub_one_of_pos (by linarith : 0 < X / 2)
    linarith
  have hlog_nn : 0 ≤ Real.log ((n₀ : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsq_le : (Real.log ((n₀ : ℝ) + 2)) ^ 2 ≤ (X / 2) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog_X 2
  have huc : 2 * coreUCRatio n₀ Δ₀ ≤ 2 * (2 * (m₀ : ℝ) + 1) + 28 * X ^ 2 := by
    unfold coreUCRatio
    linarith [hΔR, hsq_le]
  have huc' : 2 * coreUCRatio n₀ Δ₀ ≤ 30 * X ^ 2 := by
    have hm1 : 2 * (2 * (m₀ : ℝ) + 1) ≤ 2 * X ^ 2 := by nlinarith
    linarith
  have harg : (m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2 ≤ X ^ 7 := by
    have hp1 : (m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2 ≤ X + 30 * X ^ 3 := by
      have h1 : 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) ≤ 30 * X ^ 2 * X :=
        mul_le_mul huc' (le_trans hqR hmX) (Nat.cast_nonneg _) (by positivity)
      linarith
    have hX31 : X + 30 * X ^ 3 ≤ 31 * X ^ 3 := by nlinarith
    have hX4 : (31 : ℝ) ≤ X ^ 4 := by
      calc (31 : ℝ) ≤ 3 ^ 4 := by norm_num
        _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX3 4
    have hmul : 31 * X ^ 3 ≤ X ^ 7 := by
      calc 31 * X ^ 3 ≤ X ^ 4 * X ^ 3 := mul_le_mul_of_nonneg_right hX4 (by positivity)
        _ = X ^ 7 := by ring
    linarith
  calc Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2)
      ≤ Real.log (X ^ 7) := by
        refine Real.log_le_log ?_ harg
        have : 0 ≤ coreUCRatio n₀ Δ₀ := coreUCRatio_pos n₀ Δ₀
        have : 0 ≤ (q_τ : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ = 7 * Real.log X := by rw [Real.log_pow]; norm_num

lemma log_ucBound_le_min (m₀ n₀ : ℕ) (hn₀ : 1 ≤ n₀) (Δ₀ : ℕ) (hΔ : Δ₀ ≤ 2 * m₀)
    (q_τ : ℕ) (hq : q_τ ≤ m₀) :
    Real.log ((m₀ : ℝ) + 2 * coreUCRatio (min n₀ (m₀ + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      7 * Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
  have huc := coreUCRatio_mono (min_le_left n₀ (m₀ + 1)) Δ₀
  have huc_nn := coreUCRatio_pos (min n₀ (m₀ + 1)) Δ₀
  have h1 : Real.log ((m₀ : ℝ) + 2 * coreUCRatio (min n₀ (m₀ + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      Real.log ((m₀ : ℝ) + 2 * coreUCRatio n₀ Δ₀ * (q_τ : ℝ) + 2) := by
    refine Real.log_le_log (by
      have : 0 ≤ 2 * coreUCRatio (min n₀ (m₀ + 1)) Δ₀ * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) m₀]) ?_
    have := mul_le_mul_of_nonneg_right (show 2 * coreUCRatio (min n₀ (m₀ + 1)) Δ₀ ≤ 2 * coreUCRatio n₀ Δ₀ by linarith)
      (Nat.cast_nonneg (α := ℝ) q_τ)
    linarith
  exact le_trans h1 (log_ucBound_le m₀ n₀ hn₀ Δ₀ hΔ q_τ hq)

lemma holds_mono_sigma {L : LSF} {G : MGraph} {ℓ : ℕ → ℝ} {σ₁ σ₂ : ℝ}
    (h : L.Holds G ℓ σ₁) (hle : σ₁ ≤ σ₂) : L.Holds G ℓ σ₂ :=
  ⟨h.1, h.2.1, h.2.2.1, fun e he => ⟨(h.2.2.2 e he).1, le_trans (h.2.2.2 e he).2 hle⟩⟩

end

end MinCostFlow.SparseCore
