module

public import MinCostFlow.Chain.Algorithm2PsiGame
public import MinCostFlow.Chain.Theorem5_1
public import MinCostFlow.Chain.SparseCoreRestart
public import MinCostFlow.SparseCore.Lemma517
public import MinCostFlow.SparseCore.LastLevel
public import MinCostFlow.Expander.Section8Params
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Definitions and Basic Asymptotic Helpers for `ConcreteInstantiation`

Defines `concreteEnv`, `concreteChainParams`, `concreteSigmaMWU`, `concreteBCap`,
`concreteAlg2Cfg`, and general polylog/subpolynomial comparison lemmas used in
`ConcreteAsymptotics` and `ConcreteInstantiation`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Expander

section ConcreteDefs

/-- Monotonicity of `DynSpanner.SparsifySpec` in `mMax`: smaller edge caps inherit the same spec. -/
lemma sparsifySpec_mono_mMax {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    {P : DynSpanner.SparsifyParams} {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
    (hSp : DynSpanner.SparsifySpec m₂ P sparsify) :
    DynSpanner.SparsifySpec m₁ P sparsify :=
  fun H' J emb hH hJ hm1 hlen hEmb => hSp H' J emb hH hJ (le_trans hm1 hm) hlen hEmb

/-- Concrete `SparseCoreEnv` at edge bound `M₀`, bucket cap `max 1 B_cap`, degree cap `D_cap`,
depth `L = chosenL (M₀ ^ 2)`, constant `P_fn := fun _ => params (M₀ ^ 2)`, and `c_n = 1`. -/
noncomputable def concreteEnv (C_lsst : ℝ) (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ B_cap D_cap : ℕ) : SparseCoreEnv where
  C_lsst := C_lsst
  L := chosenL (M₀ ^ 2)
  hL := one_le_chosenL (M₀ ^ 2)
  P_fn := fun _ => params (M₀ ^ 2)
  hMono := monoSparsifyParams_const (params (M₀ ^ 2))
  p_s_hi := 1
  p_t_hi := 1
  hp_s := fun _ => hp_s (M₀ ^ 2)
  hp_t := fun _ => hp_t (M₀ ^ 2)
  B_fn := fun _ => max 1 B_cap
  hB_pos := fun _ => le_max_left 1 B_cap
  hB_mono := fun _ _ _ => le_rfl
  d_fn := fun _ => D_cap
  hd_mono := fun _ _ _ => le_rfl
  c_n := 1
  hc_n := le_rfl

/-- Concrete `ChainParams` at `(M₀, d = chosenD (23/24) M₀)` for `1 ≤ M₀`. -/
noncomputable def concreteChainParams (M₀ : ℕ) (hM₀ : 1 ≤ M₀) : ChainParams :=
  mkChainParams (chosenD (23 / 24) M₀) M₀ (chosenD_bounds (by norm_num) hM₀).1 hM₀

/-- Explicit `σ_mwu` from `lemma_5_17_mwu` using `μ = ⌈log(M₀^2 + 2) / log 3⌉ + 1` so that
`m + 2 ≤ (n + 2)^μ` holds automatically for every valid graph with `m ≤ M₀^2`. -/
noncomputable def concreteSigmaMWU (C_lsst : ℝ) (M₀ n : ℕ) : ℝ :=
  let μ := Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1
  (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7

lemma concreteSigmaMWU_nonneg (C_lsst : ℝ) (M₀ n : ℕ) :
    0 ≤ concreteSigmaMWU C_lsst M₀ n := by
  unfold concreteSigmaMWU
  have hK := mwuK0_pos C_lsst
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := by linarith [half_lt_log_add_two n]
  positivity

lemma concreteSigmaMWU_mono (C_lsst : ℝ) (M₀ : ℕ) :
    ∀ n₁ n₂, n₁ ≤ n₂ → concreteSigmaMWU C_lsst M₀ n₁ ≤ concreteSigmaMWU C_lsst M₀ n₂ := by
  intro n₁ n₂ hn
  dsimp only [concreteSigmaMWU]
  have hK := mwuK0_pos C_lsst
  have hlog1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := by linarith [half_lt_log_add_two n₁]
  have hlog_le : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) := by
    refine Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n₁]) ?_
    have : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 7) (by positivity)

lemma concrete_m_poly_of_le_sq {G : MGraph} (hG : G.IsValid) {M₀ : ℕ} (hm : G.m ≤ M₀ ^ 2) :
    let μ := Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1
    (G.m : ℝ) + 2 ≤ ((G.n : ℝ) + 2) ^ μ := by
  intro μ
  by_cases hn0 : G.n = 0
  · have hV_empty : G.V = ∅ := Finset.card_eq_zero.mp hn0
    have hE_empty : G.E = ∅ := Finset.eq_empty_of_forall_notMem fun e he => by
      have ht := (hG e he).1
      rw [hV_empty] at ht
      exact Finset.notMem_empty _ ht
    have hm0 : G.m = 0 := by change G.E.card = 0; rw [hE_empty, Finset.card_empty]
    rw [hm0, hn0]
    norm_num
    have hμ1 : 1 ≤ μ := Nat.le_add_left 1 _
    calc (2 : ℝ) = 2 ^ 1 := by ring
      _ ≤ (2 : ℝ) ^ μ := pow_le_pow_right₀ (by norm_num) hμ1
  · have hn1 : 1 ≤ G.n := Nat.pos_of_ne_zero hn0
    have h3_le : (3 : ℝ) ≤ (G.n : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (G.n : ℝ) := by exact_mod_cast hn1
      linarith
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hm2_pos : 0 < ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by positivity
    have hceil : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3 ≤ (μ : ℝ) := by
      have h1 : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3 ≤
          (Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) : ℝ) ≤ (μ : ℝ) := by
        dsimp only [μ]; push_cast; linarith
      exact le_trans h1 h2
    have hm2_le_pow : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ (3 : ℝ) ^ μ := by
      have hmul : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ (μ : ℝ) * Real.log 3 :=
        (div_le_iff₀ hlog3).mp hceil
      have hexp := Real.exp_le_exp.mpr hmul
      have h3eq : Real.exp ((μ : ℝ) * Real.log 3) = (3 : ℝ) ^ μ := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [Real.exp_log hm2_pos, h3eq] at hexp
      exact hexp
    have hm_le : (G.m : ℝ) + 2 ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by
      have : (G.m : ℝ) ≤ ((M₀ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hm
      linarith
    exact le_trans hm_le (le_trans hm2_le_pow (pow_le_pow_left₀ (by norm_num) h3_le μ))

/-- Explicit level-`0..d-1` bucket count for `concreteChainParams M₀` and `Ψ`: matches
`chainInv_bucket_bound_all_levels` definitionally for `concreteEnv.TP.σ`. -/
noncomputable def concreteBCap (C_lsst Ψ : ℝ) (M₀ N₀ : ℕ) (hM₀ : 1 ≤ M₀) : ℕ :=
  let P := concreteChainParams M₀ hM₀
  let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  Nat.ceil ((2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2) + 2

/-- Integer upper bound on the stretch factor used to count length buckets. -/
def concreteBucketStretch (lsstConstant branches vertices : ℕ) : ℕ :=
  6272 * max 1 lsstConstant * branches * Nat.clog 2 (vertices + 2) ^ 6

/-- Bucket capacity computed from the integer width and chain dimensions. The LSST
constant is rounded up once when selecting the program. -/
def concreteBucketCap (lsstConstant width branches depth vertices : ℕ) : ℕ :=
  3 * width + depth * Nat.clog 2 (max 2 (concreteBucketStretch lsstConstant branches vertices)) + 2

/-- Select the capacity used by the chain model. The integer option matches
the machine, while the real option retains the earlier model bound. -/
noncomputable def concreteBucketCapacity (integerBuckets : Bool) (C Ψ : ℝ)
    (M N : ℕ) (hM : 1 ≤ M) : ℕ :=
  match integerBuckets with
  | true => concreteBucketCap ⌈C⌉₊ ⌈Ψ⌉₊ (concreteChainParams M hM).k (concreteChainParams M hM).d N
  | false => concreteBCap C Ψ M N hM

private lemma log_le_clog_mul_log_two (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) ≤ (Nat.clog 2 n : ℝ) * Real.log 2 := by
  have h : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
    exact_mod_cast Nat.le_pow_clog Nat.one_lt_two n
  simpa only [Real.log_pow] using Real.log_le_log (by exact_mod_cast hn) h

/-- The integer capacity covers every bucket certified by the real ceiling bound. -/
theorem concreteBCap_le_bucketCap (C : ℝ) (width M N : ℕ) (hM : 1 ≤ M) :
    concreteBCap C (width : ℝ) M N hM ≤
      concreteBucketCap ⌈C⌉₊ width (concreteChainParams M hM).k
        (concreteChainParams M hM).d N := by
  let P := concreteChainParams M hM
  let S := max 2 (concreteBucketStretch ⌈C⌉₊ P.k N)
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hN : Real.log ((N : ℝ) + 2) ≤ (Nat.clog 2 (N + 2) : ℝ) := by
    have h := log_le_clog_mul_log_two (N + 2) (by omega)
    push_cast at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hlog2')
  have hC : max 1 C ≤ (max 1 ⌈C⌉₊ : ℕ) := by
    push_cast
    exact max_le_max le_rfl (Nat.le_ceil C)
  have hstretch : mwuK0 C * (P.k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6 ≤
      (concreteBucketStretch ⌈C⌉₊ P.k N : ℝ) := by
    unfold mwuK0 concreteBucketStretch
    push_cast
    push_cast at hC
    have hN0 := Real.log_nonneg (show 1 ≤ (N : ℝ) + 2 by linarith [Nat.cast_nonneg (α := ℝ) N])
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num)) (by positivity))
      (pow_le_pow_left₀ hN0 hN 6) (pow_nonneg hN0 _) (by positivity)
  have hS : 2 ≤ S := le_max_left _ _
  have hσ : max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) *
      Real.log ((N : ℝ) + 2) ^ 6)) ≤ (S : ℝ) := by
    dsimp [S]
    push_cast
    exact max_le (le_max_left _ _) (max_le
      (le_max_of_le_left (by norm_num)) (hstretch.trans (le_max_right _ _)))
  have hlogσ := (Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hσ).trans
    (log_le_clog_mul_log_two S (by omega))
  unfold concreteBCap concreteBucketCap
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  change (2 * max 0 (width : ℝ) + (P.d : ℝ) * Real.log
    (max 2 (max 1 (mwuK0 C * (P.k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6)))) /
      Real.log 2 ≤ ((3 * width + P.d * Nat.clog 2 S : ℕ) : ℝ)
  rw [max_eq_right (Nat.cast_nonneg width), div_le_iff₀ (by linarith)]
  push_cast
  have hw := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) width)
  have hd := mul_le_mul_of_nonneg_left hlogσ (Nat.cast_nonneg (α := ℝ) P.d)
  nlinarith only [hw, hd]

/-- The same comparison for a real width rounded up before initialization. -/
theorem concreteBCap_le_bucketCap_ceil (C Ψ : ℝ) (M N : ℕ) (hM : 1 ≤ M) :
    concreteBCap C Ψ M N hM ≤
      concreteBucketCap ⌈C⌉₊ ⌈Ψ⌉₊ (concreteChainParams M hM).k
        (concreteChainParams M hM).d N := by
  refine le_trans ?_ (concreteBCap_le_bucketCap C ⌈Ψ⌉₊ M N hM)
  unfold concreteBCap
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (max_le_max le_rfl (Nat.le_ceil Ψ)) (by norm_num : (0 : ℝ) ≤ 2)) _

private lemma clog_le_log_div_add_one {n : ℕ} (hn : 1 < n) :
    (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  have hpow : (2 : ℝ) ^ (Nat.clog 2 n - 1) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.pow_pred_clog_lt_self Nat.one_lt_two hn).le
  have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (Nat.clog 2 n - 1)) hpow
  rw [Real.log_pow] at h
  have hcl : 1 ≤ Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two hn
  rw [Nat.cast_sub hcl, Nat.cast_one] at h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith [(le_div_iff₀ htwo).mpr h]

private lemma clog_add_two_le_four_log (N : ℕ) :
    (Nat.clog 2 (N + 2) : ℝ) ≤ 4 * Real.log ((N : ℝ) + 2) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpos : 0 < Real.log 2 := by linarith
  have hN0 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hN := clog_le_log_div_add_one (n := N + 2) (by omega)
  push_cast at hN
  have h := (div_le_iff₀ hpos).mpr
      (show Real.log ((N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2) * Real.log 2 by
        nlinarith only [htwo, hN0, mul_nonneg (show 0 ≤ Real.log ((N : ℝ) + 2) by linarith)
          (show 0 ≤ 2 * Real.log 2 - 1 by linarith)])
  linarith

/-- Compare the integer capacity with a constant enlargement of the real
bound, so that the same subpolynomial estimate applies. -/
theorem concreteBucketCap_le_twice_bcap (C Ψ : ℝ) (M N : ℕ) (hM : 1 ≤ M) :
    concreteBucketCap ⌈C⌉₊ ⌈Ψ⌉₊ (concreteChainParams M hM).k
      (concreteChainParams M hM).d N ≤
      2 * concreteBCap (8192 * max 1 C) Ψ M N hM + 3 := by
  let P := concreteChainParams M hM
  let S := max 2 (concreteBucketStretch ⌈C⌉₊ P.k N)
  let σ := max (2 : ℝ) (max 1 (mwuK0 (8192 * max 1 C) * (P.k : ℝ) *
    Real.log ((N : ℝ) + 2) ^ 6))
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwo' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpos : 0 < Real.log 2 := by linarith
  have hN' := clog_add_two_le_four_log N
  have hC : (max 1 (⌈C⌉₊ : ℝ)) ≤ 2 * max 1 C := by
    have hc := Nat.ceil_lt_add_one (le_max_left (0 : ℝ) C)
    have hm := Nat.ceil_mono (le_max_right (0 : ℝ) C)
    have hm' : (⌈C⌉₊ : ℝ) ≤ (⌈max 0 C⌉₊ : ℝ) := by exact_mod_cast hm
    exact max_le (by linarith [le_max_left (1 : ℝ) C]) (by
      have : max 0 C ≤ max 1 C := max_le_max (by norm_num) le_rfl
      linarith [le_max_left (1 : ℝ) C])
  have hS : (S : ℝ) ≤ σ := by
    change ((max 2 (concreteBucketStretch ⌈C⌉₊ P.k N) : ℕ) : ℝ) ≤ σ
    push_cast [concreteBucketStretch]
    apply max_le (le_max_left _ _)
    apply le_max_of_le_right
    apply le_max_of_le_right
    unfold mwuK0
    calc
      _ ≤ 6272 * (2 * max 1 C) * (P.k : ℝ) * (4 * Real.log ((N : ℝ) + 2)) ^ 6 := by
        gcongr
      _ ≤ _ := by
        rw [max_eq_right (show (1 : ℝ) ≤ 8192 * max 1 C by
          linarith [le_max_left (1 : ℝ) C])]
        ring_nf
        exact le_rfl
  have hS2 : 2 ≤ S := le_max_left _ _
  have hσ2 : (2 : ℝ) ≤ σ := le_max_left _ _
  have hclS := clog_le_log_div_add_one (n := S) (by omega)
  have hlogs := Real.log_le_log (show (0 : ℝ) < (S : ℝ) by exact_mod_cast (show 0 < S by omega)) hS
  have hσdiv : 1 ≤ Real.log σ / Real.log 2 :=
    (le_div_iff₀ hpos).mpr (by simpa using Real.log_le_log (by norm_num) hσ2)
  have hcl : (Nat.clog 2 S : ℝ) ≤ 2 * (Real.log σ / Real.log 2) := by
    linarith [div_le_div_of_nonneg_right hlogs hpos.le]
  have hΨceil : (⌈Ψ⌉₊ : ℝ) ≤ max 0 Ψ + 1 := by
    have hm := Nat.ceil_mono (le_max_right (0 : ℝ) Ψ)
    exact (show (⌈Ψ⌉₊ : ℝ) ≤ (⌈max 0 Ψ⌉₊ : ℝ) by exact_mod_cast hm).trans
      (Nat.ceil_lt_add_one (le_max_left _ _)).le
  have hΨdiv : 3 * max 0 Ψ ≤ 4 * max 0 Ψ / Real.log 2 := by
    apply (le_div_iff₀ hpos).mpr
    have h := mul_le_mul_of_nonneg_left htwo'
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_max_left (0 : ℝ) Ψ))
    linarith only [h, le_max_left (0 : ℝ) Ψ]
  apply (Nat.cast_le (α := ℝ)).mp
  change ((3 * ⌈Ψ⌉₊ + P.d * Nat.clog 2 S + 2 : ℕ) : ℝ) ≤
    ((2 * (⌈(2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2⌉₊ + 2) + 3 : ℕ) : ℝ)
  push_cast
  have hd := mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg (α := ℝ) P.d)
  have hc := Nat.le_ceil ((2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2)
  have hsplit : 2 * ((2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2) =
      4 * max 0 Ψ / Real.log 2 + (P.d : ℝ) * (2 * (Real.log σ / Real.log 2)) := by ring
  have hceil := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsplit] at hceil
  linarith only [hΨceil, hΨdiv, hd, hceil]

/-- Integer level edge bound for Algorithm 1 (page 24).
The length growth factor is supplied as the ratio of two natural numbers. -/
def concreteLevelEdgeBound (edges branches numerator scale level : ℕ) : ℕ :=
  let top := edges * numerator ^ (level + 1)
  let bottom := scale ^ (level + 1) * branches ^ level
  (top + bottom - 1) / bottom

private lemma concreteLevelEdgeBound_eq (m k a s i : ℕ) (hk : 0 < k) (hs : 0 < s) :
    concreteLevelEdgeBound m k a s i =
      ⌈(m : ℝ) * ((a : ℝ) / s) ^ (i + 1) / (k : ℝ) ^ i⌉₊ := by
  let t := m * a ^ (i + 1)
  let b := s ^ (i + 1) * k ^ i
  have hb : 0 < b := by dsimp [b]; positivity
  have hbc : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have he : (m : ℝ) * ((a : ℝ) / s) ^ (i + 1) / (k : ℝ) ^ i = (t : ℝ) / b := by
    simp only [t, b, Nat.cast_mul, Nat.cast_pow, div_pow]
    ring
  rw [he]
  change (t + b - 1) / b = ⌈(t : ℝ) / b⌉₊
  rw [← Nat.ceilDiv_eq_add_pred_div]
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hb).mpr
    have h := (div_le_iff₀ hbc).mp (Nat.le_ceil ((t : ℝ) / b))
    exact_mod_cast (by simpa only [mul_comm] using h : (t : ℝ) ≤ (b : ℝ) * (⌈(t : ℝ) / b⌉₊ : ℕ))
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hbc).mpr
    have h := (ceilDiv_le_iff_le_mul hb).mp (le_refl (t ⌈/⌉ b))
    exact_mod_cast (by simpa only [mul_comm] using h : t ≤ (t ⌈/⌉ b) * b)

/-- An upper approximation to the length growth factor gives a valid
edge bound. A factor-three bound on its accumulated power keeps the
integer edge bound within three times the original level budget. -/
theorem concreteLevelEdgeBound_bounds (TP : SparseCoreParams) (P : ChainParams)
    (a s i : ℕ) (hs : 0 < s)
    (hγ : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : ((a : ℝ) / s) ^ (i + 1) ≤ 3 * TP.γ_ℓ (P.M₀ ^ 2) ^ (i + 1)) :
    levelM TP P i ≤ concreteLevelEdgeBound P.M₀ P.k a s i ∧
      concreteLevelEdgeBound P.M₀ P.k a s i ≤ 3 * levelM TP P i := by
  let g := TP.γ_ℓ (P.M₀ ^ 2)
  have hk : 0 < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have he : (P.M₀ : ℝ) * g * (g / (P.k : ℝ)) ^ i =
      (P.M₀ : ℝ) * g ^ (i + 1) / (P.k : ℝ) ^ i := by
    rw [div_pow, pow_succ]
    ring
  have hh : levelM TP P i = ⌈(P.M₀ : ℝ) * g ^ (i + 1) / (P.k : ℝ) ^ i⌉₊ := by
    unfold levelM
    exact congrArg Nat.ceil he
  rw [concreteLevelEdgeBound_eq _ _ _ _ _ P.hk hs, hh]
  constructor
  · apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hγ hlo _) (Nat.cast_nonneg _)) (by positivity)
  · apply Nat.ceil_le.mpr
    push_cast
    calc
      _ ≤ (P.M₀ : ℝ) * (3 * g ^ (i + 1)) / (P.k : ℝ) ^ i :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg _)) (by positivity)
      _ = 3 * ((P.M₀ : ℝ) * g ^ (i + 1) / (P.k : ℝ) ^ i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)

/-- Round a scaled upper endpoint upward to a coarser denominator that
divides its current scale. The extra error is at most one coarse unit. -/
theorem roundLevelGrowthUpper_bounds (upper scale divisor : ℕ)
    (hs : 0 < scale) (hd : 0 < divisor) :
    let a := (upper + divisor - 1) / divisor
    (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) ≤ (a : ℝ) / scale ∧
    (a : ℝ) / scale ≤ (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) + 1 / scale := by
  let a := (upper + divisor - 1) / divisor
  have he : a = upper ⌈/⌉ divisor := Nat.ceilDiv_eq_add_pred_div _ _ |>.symm
  have hlow : upper ≤ divisor * a := by
    rw [he]
    exact (ceilDiv_le_iff_le_mul hd).mp le_rfl
  have hu : divisor * a ≤ upper + divisor := by
    have h := Nat.div_mul_le_self (upper + divisor - 1) divisor
    change a * divisor ≤ _ at h
    rw [Nat.mul_comm] at h
    exact h.trans (Nat.sub_le _ _)
  have hsd : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  have hdd : (0 : ℝ) < divisor := Nat.cast_pos.mpr hd
  have hl : (upper : ℝ) / divisor ≤ a :=
    (div_le_iff₀ hdd).mpr (by exact_mod_cast (show upper ≤ a * divisor by simpa [Nat.mul_comm] using hlow))
  have hh : (a : ℝ) ≤ (upper : ℝ) / divisor + 1 := by
    rw [← div_self hdd.ne', ← add_div]
    apply (le_div_iff₀ hdd).mpr
    exact_mod_cast (show a * divisor ≤ upper + divisor by simpa [Nat.mul_comm] using hu)
  change (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) ≤ (a : ℝ) / scale ∧ _
  push_cast
  rw [mul_comm (scale : ℝ) (divisor : ℝ), ← div_div, ← add_div]
  exact ⟨div_le_div_of_nonneg_right hl hsd.le, div_le_div_of_nonneg_right hh hsd.le⟩

/-- A length-factor enclosure of width at most the reciprocal of one
plus the chain depth suffices at every level. The bound follows by
raising the relative error to the level power and using the exponential. -/
theorem concreteLevelEdgeBound_of_enclosure (TP : SparseCoreParams) (P : ChainParams)
    (a s i : ℕ) (hs : 0 < s) (hi : i ≤ P.d)
    (hγ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : (a : ℝ) / s ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1)) :
    levelM TP P i ≤ concreteLevelEdgeBound P.M₀ P.k a s i ∧
      concreteLevelEdgeBound P.M₀ P.k a s i ≤ 3 * levelM TP P i := by
  let g := TP.γ_ℓ (P.M₀ ^ 2)
  let e := 1 / ((P.d : ℝ) + 1)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hΔ : g + e ≤ g * (1 + e) := by
    have h := mul_le_mul_of_nonneg_right hγ he
    change (1 : ℝ) * e ≤ g * e at h
    linarith only [h, show g * (1 + e) = g + g * e by ring]
  have h₁ : (a : ℝ) / s ≤ g * Real.exp e :=
    (hhi.trans hΔ).trans (mul_le_mul_of_nonneg_left
      (by simpa [add_comm] using Real.add_one_le_exp e) (by linarith))
  have hDepth : ((i + 1 : ℕ) : ℝ) * e ≤ 1 := by
    dsimp [e]
    rw [mul_one_div, div_le_one (by positivity)]
    exact_mod_cast Nat.succ_le_succ hi
  have hExp : (Real.exp e) ^ (i + 1) ≤ 3 := by
    rw [← Real.exp_nat_mul]
    exact (Real.exp_le_exp.mpr hDepth).trans Real.exp_one_lt_three.le
  apply concreteLevelEdgeBound_bounds TP P a s i hs (by linarith) hlo
  calc
    _ ≤ (g * Real.exp e) ^ (i + 1) := pow_le_pow_left₀ (by positivity) h₁ _
    _ = g ^ (i + 1) * (Real.exp e) ^ (i + 1) := mul_pow _ _ _
    _ ≤ 3 * g ^ (i + 1) := by
      rw [mul_comm 3]
      exact mul_le_mul_of_nonneg_left hExp (pow_nonneg (by linarith) _)

/-- Bounding the denominator suffices to budget the exact numerator
and denominator used by the Word RAM level table. -/
theorem concreteLevelEdgePowers_le (TP : SparseCoreParams) (P : ChainParams)
    (hTP : TP.Valid) (a s i : ℕ) (hs : 0 < s) (hi : i ≤ P.d)
    (hγM : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : (a : ℝ) / s ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1)) :
    P.M₀ * a ^ (i + 1) + s ^ (i + 1) * P.k ^ i ≤
      (3 * P.M₀ ^ 2 + 1) * (s ^ (i + 1) * P.k ^ i) := by
  let top := P.M₀ * a ^ (i + 1)
  let bottom := s ^ (i + 1) * P.k ^ i
  have hb : 0 < bottom := by
    dsimp [bottom]
    exact Nat.mul_pos (Nat.pow_pos hs) (Nat.pow_pos P.hk)
  obtain ⟨_, hEdge⟩ := concreteLevelEdgeBound_of_enclosure TP P a s i hs hi
    (hTP.2.2.1 (P.M₀ ^ 2)) hlo hhi
  have hTop : top ≤ bottom * concreteLevelEdgeBound P.M₀ P.k a s i := by
    change top ≤ bottom * ((top + bottom - 1) / bottom)
    rw [← Nat.ceilDiv_eq_add_pred_div]
    exact (ceilDiv_le_iff_le_mul hb).mp le_rfl
  have hcap := hEdge.trans (Nat.mul_le_mul_left 3 (levelM_le_sq hTP hγM hγk i))
  change top + bottom ≤ _
  calc
    _ ≤ bottom * concreteLevelEdgeBound P.M₀ P.k a s i + bottom :=
      Nat.add_le_add_right hTop _
    _ ≤ bottom * (3 * P.M₀ ^ 2) + bottom :=
      Nat.add_le_add_right (Nat.mul_le_mul_left bottom hcap) _
    _ = _ := by dsimp [bottom]; ring

/-- Use a power of two at least twice the number of levels. This leaves
half the required error budget for upward rounding. -/
def concreteThresholdScale (depth : ℕ) : ℕ :=
  2 ^ Nat.clog 2 (2 * (depth + 1))

/-- The coarse scale lies between two and four times the number of levels. -/
theorem concreteThresholdScale_bounds (depth : ℕ) :
    2 * (depth + 1) ≤ concreteThresholdScale depth ∧
      concreteThresholdScale depth ≤ 4 * (depth + 1) := by
  let n := 2 * (depth + 1)
  let e := Nat.clog 2 n
  have hn : 1 < n := by dsimp [n]; omega
  have he : 0 < e := Nat.clog_pos Nat.one_lt_two hn
  have hp := Nat.pow_pred_clog_lt_self Nat.one_lt_two hn
  change 2 ^ (e - 1) < n at hp
  change n ≤ 2 ^ e ∧ 2 ^ e ≤ 4 * (depth + 1)
  refine ⟨Nat.le_pow_clog Nat.one_lt_two _, ?_⟩
  have hpow : 2 ^ e = 2 ^ (e - 1) * 2 := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
  rw [hpow]
  omega

/-- A coarse scale at most four times the chain depth plus one keeps
the terminal denominator polynomial in the padded edge bound. -/
theorem concreteThresholdScale_power_le (M scale : ℕ) (hM : 1 ≤ M) (hs : 0 < scale)
    (hscale : scale ≤ 4 * ((concreteChainParams M hM).d + 1)) :
    (2 * scale) ^ ((concreteChainParams M hM).d + 1) ≤ (M + 2) ^ 72 := by
  let d := (concreteChainParams M hM).d
  let L := Real.log ((M : ℝ) + 2)
  have hL : 1 ≤ L := by
    have hcast : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ (M : ℝ) + 2 by linarith [Real.exp_one_lt_three])
    simpa only [Real.log_exp, L] using h
  have hd : (d : ℝ) ≤ 2 * L ^ (1 / 48 : ℝ) := by
    change (chosenD (23 / 24) M : ℝ) ≤ _
    have he : (1 - (23 / 24 : ℝ)) / 2 = 1 / 48 := by norm_num
    simpa only [he] using (chosenD_bounds (by norm_num : (23 / 24 : ℝ) < 1) hM).2.2
  have hr : 1 ≤ L ^ (1 / 48 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hds : (d : ℝ) + 1 ≤ 3 * L ^ (1 / 48 : ℝ) := by linarith
  have hsq : (L ^ (1 / 48 : ℝ)) ^ 2 ≤ L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
    simpa only [Nat.cast_ofNat, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : 1 / 48 * (2 : ℝ) ≤ 1)
  have hc : (scale : ℝ) ≤ 4 * ((d : ℝ) + 1) := by exact_mod_cast hscale
  have hpos : 0 < (2 : ℝ) * scale := mul_pos (by norm_num) (by exact_mod_cast hs)
  have hg : Real.log ((2 : ℝ) * scale) ≤ 8 * ((d : ℝ) + 1) := by
    linarith only [Real.log_le_sub_one_of_pos hpos, hc]
  have hprod : ((d : ℝ) + 1) * Real.log ((2 : ℝ) * scale) ≤ 72 * L := by
    have ht := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ (d : ℝ) + 1)
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (d : ℝ) + 1) hds 2
    nlinarith only [ht, hh, hsq]
  have h : (((2 : ℝ) * scale) ^ (d + 1)) ≤ ((M : ℝ) + 2) ^ (72 : ℕ) := by
    rw [← Real.exp_log (pow_pos hpos _),
      ← Real.exp_log (pow_pos (by positivity : (0 : ℝ) < (M : ℝ) + 2) (72 : ℕ))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow, Real.log_pow]
    push_cast
    exact hprod
  exact_mod_cast h

/-- Integer update budget for the rebuild schedule of Algorithm 2 (page 28).
The binary ceiling logarithm bounds the natural logarithm from above,
so the schedule rebuilds before it exhausts the corresponding real budget. -/
def concreteRebuildCount (branches edges vertices : ℕ) : ℕ :=
  edges / (branches * Nat.clog 2 (vertices + 2) ^ 2)

/-- `intRebuildThreshold` is `concreteRebuildCount` at branching power `P.k ^ (i + 1)`. -/
theorem intRebuildThreshold_eq_concreteRebuildCount (P : ChainParams) (N₀ i : ℕ) :
    intRebuildThreshold P N₀ i = concreteRebuildCount (P.k ^ (i + 1)) P.M₀ N₀ :=
  rfl

/-- The integer budget stays within the real update threshold. Its successor,
which is the smallest count that triggers a rebuild, is at least a sixteenth
of the real threshold. -/
theorem concreteRebuildCount_bounds (k m n : ℕ) (hk : 0 < k) :
    (concreteRebuildCount k m n : ℝ) ≤ SparseCoreTool.updateThreshold k m n ∧
    SparseCoreTool.updateThreshold k m n ≤ 16 * ((concreteRebuildCount k m n : ℝ) + 1) := by
  let L := Real.log ((n : ℝ) + 2)
  let b := Nat.clog 2 (n + 2)
  let D := k * b ^ 2
  have hL : 0 < L := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hLb : L ≤ (b : ℝ) := by
    have h := log_le_clog_mul_log_two (n + 2) (by omega)
    push_cast at h
    exact h.trans (mul_le_of_le_one_right (Nat.cast_nonneg b) hlog2)
  have hbl : (b : ℝ) ≤ 4 * L := clog_add_two_le_four_log n
  have hb : 0 < b := Nat.clog_pos Nat.one_lt_two (by omega)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDcast : (D : ℝ) = (k : ℝ) * (b : ℝ) ^ 2 := by push_cast [D]; rfl
  have hDlo : (k : ℝ) * L ^ 2 ≤ (D : ℝ) := by
    rw [hDcast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hLb 2) (Nat.cast_nonneg k)
  have hDhi : (D : ℝ) ≤ 16 * ((k : ℝ) * L ^ 2) := by
    rw [hDcast]
    calc
      _ ≤ (k : ℝ) * (4 * L) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg b) hbl 2) (Nat.cast_nonneg k)
      _ = _ := by ring
  have hd : 0 < (k : ℝ) * L ^ 2 := by positivity
  have hlo : ((m / D : ℕ) : ℝ) * (D : ℝ) ≤ m := by exact_mod_cast Nat.div_mul_le_self m D
  have hhi : (m : ℝ) ≤ (((m / D : ℕ) : ℝ) + 1) * (D : ℝ) := by
    have h := (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self (m / D))
    exact_mod_cast h.le
  change ((m / D : ℕ) : ℝ) ≤ (m : ℝ) / ((k : ℝ) * L ^ 2) ∧
    (m : ℝ) / ((k : ℝ) * L ^ 2) ≤ 16 * (((m / D : ℕ) : ℝ) + 1)
  refine ⟨(le_div_iff₀ hd).mpr ?_, (div_le_iff₀ hd).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_left hDlo (Nat.cast_nonneg (m / D))).trans hlo
  · calc
      _ ≤ (((m / D : ℕ) : ℝ) + 1) * (D : ℝ) := hhi
      _ ≤ (((m / D : ℕ) : ℝ) + 1) * (16 * ((k : ℝ) * L ^ 2)) :=
        mul_le_mul_of_nonneg_left hDhi (by positivity)
      _ = _ := by ring

/-- Rebuild budget for a rounded level bound. The extra factor of three
in the denominator pays for the possible increase in the edge bound. -/
def concreteLevelRebuildCount (edges branches numerator scale level vertices : ℕ) : ℕ :=
  concreteRebuildCount (3 * branches)
    (concreteLevelEdgeBound edges branches numerator scale level) vertices

/-- An exact integer growth factor gives the same rebuild count at
every positive fixed-point scale. -/
theorem concreteLevelRebuildCount_exact_scale (m k a s i n : ℕ)
    (hk : 0 < k) (hs : 0 < s) :
    concreteLevelRebuildCount m k (s * a) s i n =
      concreteLevelRebuildCount m k a 1 i n := by
  unfold concreteLevelRebuildCount
  rw [concreteLevelEdgeBound_eq _ _ _ _ _ hk hs,
    concreteLevelEdgeBound_eq _ _ _ _ _ hk (by decide)]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Nat.cast_mul, mul_comm (s : ℝ), mul_div_cancel_right₀ _ hs',
    Nat.cast_one, div_one]

/-- The rounded schedule respects the original update budget of Lemma 5.17
(page 23). The first update count that exceeds it pays at least one
forty-eighth of the original threshold in the amortized analysis. -/
theorem concreteLevelRebuildCount_bounds (TP : SparseCoreParams) (P : ChainParams)
    (a s i n : ℕ) (hs : 0 < s) (hi : i ≤ P.d)
    (hγ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / s)
    (hhi : (a : ℝ) / s ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1)) :
    let count := concreteLevelRebuildCount P.M₀ P.k a s i n
    let budget := SparseCoreTool.updateThreshold P.k (levelM TP P i) n
    (count : ℝ) ≤ budget ∧ budget ≤ 48 * ((count : ℝ) + 1) := by
  dsimp only
  let m := levelM TP P i
  let E := concreteLevelEdgeBound P.M₀ P.k a s i
  let Y := (P.k : ℝ) * Real.log ((n : ℝ) + 2) ^ 2
  let T := concreteRebuildCount (3 * P.k) E n
  have hY : 0 < Y := by
    have hl : 0 < Real.log ((n : ℝ) + 2) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [Y]
    exact mul_pos (Nat.cast_pos.mpr P.hk) (pow_pos hl _)
  obtain ⟨hm, hE⟩ := concreteLevelEdgeBound_of_enclosure TP P a s i hs hi hγ hlo hhi
  obtain ⟨hlo', hhi'⟩ := concreteRebuildCount_bounds (3 * P.k) E n (by
    exact Nat.mul_pos (by decide) P.hk)
  have he : SparseCoreTool.updateThreshold (3 * P.k) E n = (E : ℝ) / (3 * Y) := by
    unfold SparseCoreTool.updateThreshold
    push_cast
    congr 1
    unfold Y
    ring
  rw [he] at hlo' hhi'
  change (T : ℝ) ≤ (m : ℝ) / Y ∧ (m : ℝ) / Y ≤ 48 * ((T : ℝ) + 1)
  have h3Y : 0 < 3 * Y := by positivity
  have hlow : (E : ℝ) / (3 * Y) ≤ (m : ℝ) / Y := by
    apply (div_le_div_iff₀ h3Y hY).mpr
    have hcast : (E : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hE
    calc
      _ ≤ (3 * (m : ℝ)) * Y := mul_le_mul_of_nonneg_right hcast hY.le
      _ = _ := by ring
  have hhigh : (m : ℝ) / Y ≤ 3 * ((E : ℝ) / (3 * Y)) := by
    have hm' : (m : ℝ) ≤ E := by exact_mod_cast hm
    calc
      _ ≤ (E : ℝ) / Y := div_le_div_of_nonneg_right hm' hY.le
      _ = _ := by ring
  exact ⟨hlo'.trans hlow, hhigh.trans (by linarith only [hhi'])⟩

/-- Concrete `Alg2Config` assembling `sparseCoreRestartTool`, an arbitrary `lastTool : LastLevelTool`
at `LP := lastLevelParams C_last`, `sparseCoreParams`, and `concreteChainParams`. -/
noncomputable def concreteAlg2CfgWithLast
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (lastTool : LastLevelTool) (C_last : ℝ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap D_cap : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) : Alg2Config where
  T := sparseCoreRestartTool oracle C_lsst (chosenL (M₀ ^ 2)) (fun _ => sparsify)
  L := lastTool
  TP := sparseCoreParams (concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap)
  LP := lastLevelParams C_last
  P := concreteChainParams M₀ hM₀
  σ_mwu := concreteSigmaMWU C_lsst M₀
  N₀ := N₀
  α := α
  Ψ := Ψ
  ε := ε

/-- Concrete `Alg2Config` assembling `sparseCoreRestartTool`, `lastLevelTool`, `sparseCoreParams`,
and `lastLevelParams`. -/
noncomputable def concreteAlg2Cfg
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap D_cap : ℕ) (hM₀ : 1 ≤ M₀) (α Ψ ε : ℝ) : Alg2Config :=
  concreteAlg2CfgWithLast oracle C_lsst (lastLevelTool oracle C_lsst) C_lsst
    sparsify params hp_s hp_t M₀ N₀ B_cap D_cap hM₀ α Ψ ε

end ConcreteDefs

section AsymptoticHelpers

lemma log_sq_add_two_le_double (M₀ : ℕ) :
    Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((M₀ : ℝ) + 2) := by
  have hm2_pos : 0 < ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by positivity
  have hM0_nn : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have hm2_eq : ((M₀ ^ 2 : ℕ) : ℝ) = (M₀ : ℝ) ^ 2 := by push_cast; rfl
  have hle : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ ((M₀ : ℝ) + 2) ^ 2 := by
    rw [hm2_eq]; nlinarith only [hM0_nn]
  calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2)
      ≤ Real.log (((M₀ : ℝ) + 2) ^ 2) := Real.log_le_log hm2_pos hle
    _ = 2 * Real.log ((M₀ : ℝ) + 2) := by rw [Real.log_pow]; norm_num

lemma rpow_sq_23_24_le (M₀ : ℕ) :
    Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (23 / 24 : ℝ) ≤
      2 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := by
  have hL_nn : 0 ≤ Real.log ((M₀ : ℝ) + 2) := by linarith [half_lt_log_add_two M₀]
  have hsq_nn : 0 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := by linarith [half_lt_log_add_two (M₀ ^ 2)]
  have hpow := Real.rpow_le_rpow hsq_nn (log_sq_add_two_le_double M₀) (by norm_num : (0 : ℝ) ≤ 23 / 24)
  rw [Real.mul_rpow (by norm_num) hL_nn] at hpow
  have h2_le : (2 : ℝ) ^ (23 / 24 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (23 / 24 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hrpow_nn : 0 ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_nn _
  calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (23 / 24 : ℝ)
      ≤ (2 : ℝ) ^ (23 / 24 : ℝ) * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := hpow
    _ ≤ 2 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) := mul_le_mul_of_nonneg_right h2_le hrpow_nn

lemma one_le_log_add_two_of_one {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    1 ≤ Real.log ((M₀ : ℝ) + 2) := by
  have h3 : Real.exp 1 ≤ (M₀ : ℝ) + 2 := by
    have : (3 : ℝ) ≤ (M₀ : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
      linarith
    exact le_trans Real.exp_one_lt_three.le this
  simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

lemma one_le_LL_of_one {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    1 ≤ Real.log (Real.log ((M₀ : ℝ) + 2) + 2) := by
  have hL1 := one_le_log_add_two_of_one hM₀
  have h3 : Real.exp 1 ≤ Real.log ((M₀ : ℝ) + 2) + 2 := le_trans Real.exp_one_lt_three.le (by linarith)
  simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

lemma rpow_exp_le_LL {C : ℝ} (hC : 0 ≤ C) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    Real.exp (C * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
      Real.exp (C * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  refine Real.exp_le_exp.mpr ?_
  have hLL := one_le_LL_of_one hM₀
  have hL_nn : 0 ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) :=
    Real.rpow_nonneg (by linarith [one_le_log_add_two_of_one hM₀]) _
  exact le_mul_of_one_le_right (mul_nonneg hC hL_nn) hLL

lemma exp_23_24_mono_LL {A B : ℝ} (hAB : A ≤ B) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    Real.exp (A * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ≤
      Real.exp (B * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  refine Real.exp_le_exp.mpr ?_
  have hL_nn : 0 ≤ Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) :=
    Real.rpow_nonneg (by linarith [one_le_log_add_two_of_one hM₀]) _
  have hLL_nn : 0 ≤ Real.log (Real.log ((M₀ : ℝ) + 2) + 2) := by linarith [one_le_LL_of_one hM₀]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hL_nn) hLL_nn

lemma exp_47_48_mono_LL {A B : ℝ} (hAB : A ≤ B) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    Real.exp (A * Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ≤
      Real.exp (B * Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  refine Real.exp_le_exp.mpr ?_
  have hL_nn : 0 ≤ Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) :=
    Real.rpow_nonneg (by linarith [one_le_log_add_two_of_one hM₀]) _
  have hLL_nn : 0 ≤ Real.log (Real.log ((M₀ : ℝ) + 2) + 2) := by linarith [one_le_LL_of_one hM₀]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hL_nn) hLL_nn

lemma polylog_le_exp_rpow_23_24 (A : ℝ) (k : ℕ) (hA : 1 ≤ A) :
    ∃ u₀ : ℝ, 3 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → A * u ^ k ≤ Real.exp (u ^ (23 / 24 : ℝ)) := by
  let K : ℝ := Real.log A + (48 * (k : ℝ))
  let R : ℝ := max 1 (max K 3)
  let u₀ : ℝ := R ^ (2 : ℝ)
  have hR1 : 1 ≤ R := le_max_left 1 _
  have hR_pos : 0 < R := by linarith
  have hu₀_3 : 3 ≤ u₀ := by
    have h3R : 3 ≤ R := le_trans (le_max_right K 3) (le_max_right 1 _)
    have : R ≤ R ^ (2 : ℝ) := by
      calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
        _ ≤ R ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    linarith
  refine ⟨u₀, hu₀_3, fun u hu => ?_⟩
  have hu_pos : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hAu_pos : 0 < A * u ^ k := by positivity
  rw [← Real.exp_log hAu_pos]
  refine Real.exp_le_exp.mpr ?_
  have hlog_u : Real.log u ≤ 48 * u ^ (1 / 48 : ℝ) := by
    have hu48_pos : 0 < u ^ (1 / 48 : ℝ) := Real.rpow_pos_of_pos hu_pos _
    have h1 := Real.log_le_sub_one_of_pos hu48_pos
    have hlog_pow : Real.log (u ^ (1 / 48 : ℝ)) = (1 / 48 : ℝ) * Real.log u :=
      Real.log_rpow hu_pos (1 / 48)
    linarith
  have hu_rpow_11_12 : R ≤ u ^ (22 / 24 : ℝ) := by
    have huR : R ^ (2 : ℝ) ≤ u := hu
    have hpow := Real.rpow_le_rpow (by positivity) huR (by norm_num : (0 : ℝ) ≤ 22 / 24)
    rw [← Real.rpow_mul hR_pos.le] at hpow
    have hR_mono : R ≤ R ^ ((2 : ℝ) * (22 / 24)) := by
      calc R = R ^ (1 : ℝ) := (Real.rpow_one R).symm
        _ ≤ R ^ ((2 : ℝ) * (22 / 24)) := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    exact le_trans hR_mono hpow
  have hKu : K ≤ u ^ (22 / 24 : ℝ) :=
    le_trans (le_trans (le_max_left K 3) (le_max_right 1 _)) hu_rpow_11_12
  have hu_124_ge1 : 1 ≤ u ^ (1 / 24 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
  have hlogAu : Real.log (A * u ^ k) ≤ K * u ^ (1 / 24 : ℝ) := by
    rw [Real.log_mul (by linarith) (pow_ne_zero k hu_pos.ne'), Real.log_pow]
    have h48k : (k : ℝ) * Real.log u ≤ 48 * (k : ℝ) * u ^ (1 / 48 : ℝ) := by nlinarith
    have hu148_24 : u ^ (1 / 48 : ℝ) ≤ u ^ (1 / 24 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have hlogA_nn : 0 ≤ Real.log A := Real.log_nonneg hA
    nlinarith [mul_le_mul_of_nonneg_left hu_124_ge1 hlogA_nn, hu148_24]
  have hsplit : u ^ (22 / 24 : ℝ) * u ^ (1 / 24 : ℝ) = u ^ (23 / 24 : ℝ) := by
    rw [← Real.rpow_add hu_pos]; norm_num
  have h124_nn : 0 ≤ u ^ (1 / 24 : ℝ) := by positivity
  calc Real.log (A * u ^ k) ≤ K * u ^ (1 / 24 : ℝ) := hlogAu
    _ ≤ u ^ (22 / 24 : ℝ) * u ^ (1 / 24 : ℝ) := mul_le_mul_of_nonneg_right hKu h124_nn
    _ = u ^ (23 / 24 : ℝ) := hsplit

lemma rpow_23_24_mul_loglog_dominates_log (C c : ℝ) (hC : 0 < C) (hc : 0 < c) :
    ∃ u₀ : ℝ, 3 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      C * u ^ (23 / 24 : ℝ) * Real.log (u + 2) ≤ c * u ^ (47 / 48 : ℝ) := by
  let M_const : ℝ := (96 * C * 2 / c) ^ (96 : ℝ)
  let u₀ : ℝ := max 3 M_const
  refine ⟨u₀, le_max_left 3 M_const, fun u hu => ?_⟩
  have hu3 : 3 ≤ u := le_trans (le_max_left 3 M_const) hu
  have hu_pos : 0 < u := by linarith
  have hM_le : M_const ≤ u := le_trans (le_max_right 3 M_const) hu
  have hu_196 : 96 * C * 2 / c ≤ u ^ (1 / 96 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity) hM_le (by norm_num : (0 : ℝ) ≤ 1 / 96)
    dsimp only [M_const] at h1
    rw [← Real.rpow_mul (by positivity)] at h1
    simpa [Real.rpow_one] using h1
  have hu2_le : u + 2 ≤ 2 * u := by linarith
  have hu2_196 : (u + 2) ^ (1 / 96 : ℝ) ≤ 2 * u ^ (1 / 96 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity) hu2_le (by norm_num : (0 : ℝ) ≤ 1 / 96)
    rw [Real.mul_rpow (by norm_num) hu_pos.le] at h1
    have h2 : (2 : ℝ) ^ (1 / 96 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 96 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    nlinarith [Real.rpow_nonneg hu_pos.le (1 / 96 : ℝ)]
  have hlog_u2 : Real.log (u + 2) ≤ 96 * (u + 2) ^ (1 / 96 : ℝ) := by
    have hpos : 0 < (u + 2) ^ (1 / 96 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_rpow (by linarith)] at h1
    linarith
  have hlog_le : C * Real.log (u + 2) ≤ c * u ^ (1 / 48 : ℝ) := by
    have hsplit48 : u ^ (1 / 96 : ℝ) * u ^ (1 / 96 : ℝ) = u ^ (1 / 48 : ℝ) := by
      rw [← Real.rpow_add hu_pos]; norm_num
    have h96_nn : 0 ≤ u ^ (1 / 96 : ℝ) := by positivity
    have h1 : 96 * C * 2 * u ^ (1 / 96 : ℝ) ≤ c * (u ^ (1 / 96 : ℝ) * u ^ (1 / 96 : ℝ)) := by
      have hmul := (div_le_iff₀ hc).mp hu_196
      calc 96 * C * 2 * u ^ (1 / 96 : ℝ)
          ≤ (u ^ (1 / 96 : ℝ) * c) * u ^ (1 / 96 : ℝ) :=
            mul_le_mul_of_nonneg_right hmul h96_nn
        _ = c * (u ^ (1 / 96 : ℝ) * u ^ (1 / 96 : ℝ)) := by ring
    rw [hsplit48] at h1
    calc C * Real.log (u + 2)
        ≤ C * (96 * (u + 2) ^ (1 / 96 : ℝ)) := mul_le_mul_of_nonneg_left hlog_u2 hC.le
      _ ≤ C * (96 * (2 * u ^ (1 / 96 : ℝ))) := by gcongr
      _ = 96 * C * 2 * u ^ (1 / 96 : ℝ) := by ring
      _ ≤ c * u ^ (1 / 48 : ℝ) := h1
  have hsplit47 : u ^ (23 / 24 : ℝ) * u ^ (1 / 48 : ℝ) = u ^ (47 / 48 : ℝ) := by
    rw [← Real.rpow_add hu_pos]; norm_num
  have h23_nn : 0 ≤ u ^ (23 / 24 : ℝ) := by positivity
  calc C * u ^ (23 / 24 : ℝ) * Real.log (u + 2)
      = u ^ (23 / 24 : ℝ) * (C * Real.log (u + 2)) := by ring
    _ ≤ u ^ (23 / 24 : ℝ) * (c * u ^ (1 / 48 : ℝ)) := mul_le_mul_of_nonneg_left hlog_le h23_nn
    _ = c * (u ^ (23 / 24 : ℝ) * u ^ (1 / 48 : ℝ)) := by ring
    _ = c * u ^ (47 / 48 : ℝ) := by rw [hsplit47]

lemma exp_dominates_of_u0 (u₀ : ℝ) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ u₀ ≤ Real.log ((M₀ : ℝ) + 2) := by
  refine ⟨max 2 (Nat.ceil (Real.exp u₀)), le_max_left 2 _, ?_⟩
  have hle : Real.exp u₀ ≤ ((max 2 (Nat.ceil (Real.exp u₀)) : ℕ) : ℝ) + 2 := by
    have h1 : Real.exp u₀ ≤ (Nat.ceil (Real.exp u₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp u₀) : ℝ) ≤ ((max 2 (Nat.ceil (Real.exp u₀)) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 2 _
    linarith
  calc u₀ = Real.log (Real.exp u₀) := (Real.log_exp u₀).symm
    _ ≤ Real.log (((max 2 (Nat.ceil (Real.exp u₀)) : ℕ) : ℝ) + 2) :=
        Real.log_le_log (Real.exp_pos u₀) hle

lemma max_zero_le_alg2PsiGame (Ψ : ℝ) (M₀ : ℕ) :
    max 0 Ψ ≤ alg2PsiGame Ψ M₀ := by
  by_cases hΨ : Ψ ≤ 0
  · rw [max_eq_left hΨ]
    exact le_trans zero_le_one (alg2PsiGame_ge_one Ψ M₀)
  · push Not at hΨ
    rw [max_eq_right hΨ.le]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_lt1 : Real.log 2 < 1 := by
      have h2_lt_e : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      simpa [Real.log_exp] using Real.log_lt_log (by norm_num) h2_lt_e
    have hdiv : Ψ ≤ Ψ / Real.log 2 := by
      calc Ψ = Ψ * 1 := by ring
        _ ≤ Ψ * (1 / Real.log 2) :=
            mul_le_mul_of_nonneg_left (one_le_one_div hlog2_pos hlog2_lt1.le) hΨ.le
        _ = Ψ / Real.log 2 := by ring
    have hlogM : 0 ≤ Real.log ((M₀ : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₀])
    have hnum : Ψ / Real.log 2 ≤ (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 + 1 := by
      have : Ψ / Real.log 2 ≤ (Ψ + Real.log ((M₀ : ℝ) + 1)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2_pos.le
      linarith
    exact le_trans (le_trans hdiv hnum) (alg2PsiGame_real_le Ψ M₀)

lemma add_exp_23_24_LL {x y c₁ c₂ L LL : ℝ} (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂)
    (hL_nn : 0 ≤ L ^ (23 / 24 : ℝ)) (hLL_nn : 0 ≤ LL)
    (h2_le : (2 : ℝ) ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL))
    (hx : x ≤ Real.exp (c₁ * L ^ (23 / 24 : ℝ) * LL))
    (hy : y ≤ Real.exp (c₂ * L ^ (23 / 24 : ℝ) * LL)) :
    x + y ≤ Real.exp ((c₁ + c₂ + 1) * L ^ (23 / 24 : ℝ) * LL) := by
  have hx' := le_trans hx (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : c₁ ≤ c₁ + c₂) hL_nn) hLL_nn))
  have hy' := le_trans hy (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : c₂ ≤ c₁ + c₂) hL_nn) hLL_nn))
  calc x + y ≤ 2 * Real.exp ((c₁ + c₂) * L ^ (23 / 24 : ℝ) * LL) := by linarith
    _ ≤ Real.exp (1 * L ^ (23 / 24 : ℝ) * LL) *
          Real.exp ((c₁ + c₂) * L ^ (23 / 24 : ℝ) * LL) :=
        mul_le_mul_of_nonneg_right h2_le (Real.exp_pos _).le
    _ = Real.exp ((c₁ + c₂ + 1) * L ^ (23 / 24 : ℝ) * LL) := by
        rw [← Real.exp_add]; congr 1; ring

end AsymptoticHelpers

end MinCostFlow.Chain
