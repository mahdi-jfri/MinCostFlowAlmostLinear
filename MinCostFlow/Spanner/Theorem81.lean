module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift
public import MinCostFlow.Spanner.Task2Base
public import MinCostFlow.Spanner.Analysis1
public import MinCostFlow.Spanner.Claim87
public import MinCostFlow.Spanner.Task3Base
public import MinCostFlow.Spanner.Analysis2
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Runtime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import MinCostFlow.Spanner.Theorem81Local

/-!
# Theorem 8.1 (`Sparsify`)

This file proves **`theorem_8_1_local`** and **`theorem_8_1_internal`** (**Theorem 8.1**, `spanner.tex`,
page 39; proof pages 44–45) for Algorithm 4 (`sparsifyLocal` and `sparsify`), as well as the
paper's explicit-parameter form **`theorem_8_1`** and uniform-cap form **`theorem_8_1_at_cap`**:

1. `out.Jtilde` is a valid subgraph of `J` (`out.keptEdges.Nodup`, indices `< J.m`),
   `out.embWJtilde : W → Jtilde` and `out.embJJtilde : J → Jtilde` are valid embeddings, and
   `Π_{J̃ → H'} := restrictEmb embJH out.keptEdges` is a valid `Jtilde → H'` embedding.
2. **Congestion** (via **Fact 1**, Corollary 8.8, and Corollary 8.10):
   `vcong J H' 1 (Π_{J̃ → H'} ∘ Π_{J → J̃}) ≤ (η₁ + 1/2)(η₂ + 1/2) τ₁ τ₂`.
3. **Length**:
   `length J Π_{J → J̃} ≤ γ_ExpPath²` and
   `length J (Π_{J̃ → H'} ∘ Π_{J → J̃}) ≤ γ_ExpPath² · length J Π_{J → H'}`.
4. **Sparsity**:
   `J̃.m ≤ W.m · γ_ExpPath`, yielding both
   `J̃.m ≤ (n + ℓ · c_deg · n / φ_dec) · γ_ExpPath` and
   `J̃.m ≤ (m + c_deg · m / (2 φ_dec)) · γ_ExpPath`.
5. **Work**: exact bounds on all fields of `out.stats : SparsifyStats`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Paper-form Theorem 8.1 and Uniform `M`-cap Corollary -/

lemma combine_dec_cost_le (decCost : DecomposeCost)
    (J : Graph) {M : ℕ} {γ_ℓ K_b lenJ : ℝ}
    (hJm : J.m ≤ M) (hγ : 1 ≤ γ_ℓ) (_hKb : 0 ≤ K_b)
    (hLen : 1 ≤ J.m → 1 ≤ lenJ) (hlen_nn : 0 ≤ lenJ) :
    (decCost.callCost (stripLoops J).m : ℝ) +
      K_b * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
      ((decCost.K_dec + 1) * decCost.decFactor M + K_b) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  set L_log := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log J.n J.m
  have hL1_nn : 0 ≤ L_log := by linarith only [hL1]
  have hKdec : 0 ≤ decCost.K_dec + 1 := by linarith only [decCost.hK_dec]
  have hfac_ge : 1 ≤ decCost.decFactor M := decCost.hdec_ge M
  have hfac_nn : 0 ≤ (decCost.K_dec + 1) * decCost.decFactor M :=
    mul_nonneg hKdec (by linarith only [hfac_ge])
  have hsum_nn : 0 ≤ (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ :=
    add_nonneg (Nat.cast_nonneg J.n)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg J.m) (sq_nonneg γ_ℓ)) hlen_nn)
  rcases Nat.eq_zero_or_pos J.m with hm0 | hm_pos
  · have hstrip0 : (stripLoops J).m = 0 :=
      Nat.eq_zero_of_le_zero (hm0 ▸ stripLoops_m_le J)
    rw [hstrip0, decCost.callCost_zero, Nat.cast_zero, zero_add]
    have hcoeff : K_b ≤ (decCost.K_dec + 1) * decCost.decFactor M + K_b := by linarith only [hfac_nn]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hsum_nn) hL1_nn
  · have hL_len : 1 ≤ lenJ := hLen hm_pos
    have hdec_call0 : (decCost.callCost (stripLoops J).m : ℝ) ≤
        (decCost.K_dec + 1) * ((stripLoops J).m : ℝ) * decCost.decFactor M :=
      decCost.callCost_le_of_le (le_trans (stripLoops_m_le J) hJm)
    have hstrip_m : ((stripLoops J).m : ℝ) ≤ (J.m : ℝ) :=
      Nat.cast_le.mpr (stripLoops_m_le J)
    have hdec_call : (decCost.callCost (stripLoops J).m : ℝ) ≤
        (decCost.K_dec + 1) * (J.m : ℝ) * decCost.decFactor M :=
      le_trans hdec_call0
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstrip_m hKdec)
          (by linarith only [hfac_ge]))
    have hγ2 : 1 ≤ γ_ℓ ^ 2 := by nlinarith only [hγ]
    have h1 : 1 ≤ γ_ℓ ^ 2 * lenJ := by nlinarith only [hγ2, hL_len]
    have h2 : (J.m : ℝ) ≤ (J.m : ℝ) * (γ_ℓ ^ 2 * lenJ) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) h1
    have h3 : (J.m : ℝ) ≤ ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ) := by
      have : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
      linarith only [h2, this]
    have h4 : (J.m : ℝ) ≤ ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ) * L_log :=
      le_trans h3 (le_mul_of_one_le_right hsum_nn hL1)
    have h5 : (decCost.callCost (stripLoops J).m : ℝ) ≤
        ((decCost.K_dec + 1) * decCost.decFactor M) *
          (((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * lenJ) * L_log) := by
      have hre : (decCost.K_dec + 1) * (J.m : ℝ) * decCost.decFactor M =
          ((decCost.K_dec + 1) * decCost.decFactor M) * (J.m : ℝ) := by ring
      exact le_trans hdec_call (hre ▸ mul_le_mul_of_nonneg_left h4 hfac_nn)
    linarith only [h5]

private lemma gammaC_ge_one {η₁ η₂ : ℕ} {γE γd φ : ℝ}
    (hη₁ : 1 ≤ η₁) (hη₂ : 1 ≤ η₂) (hγE : 2 ≤ γE) (hγd : 1 ≤ γd)
    (hφ_pos : 0 < φ) (hφ_half : φ ≤ 1 / 2) :
    1 ≤ 2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) * γE ^ 2 * γd ^ 2 / φ ^ 2 := by
  have hη₁_r : (1 : ℝ) ≤ η₁ := by exact_mod_cast hη₁
  have hη₂_r : (1 : ℝ) ≤ η₂ := by exact_mod_cast hη₂
  have hη : 1 ≤ ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) := by nlinarith only [hη₁_r, hη₂_r]
  have hγE2 : 1 ≤ γE ^ 2 := by nlinarith only [hγE]
  have hγd2 : 1 ≤ γd ^ 2 := by nlinarith only [hγd]
  have hγ : 1 ≤ γE ^ 2 * γd ^ 2 := by nlinarith only [hγE2, hγd2]
  have hnum : 1 ≤ 2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) * γE ^ 2 * γd ^ 2 := by
    nlinarith only [hη, hγ]
  have hφ2 : φ ^ 2 ≤ 1 := by nlinarith only [hφ_pos, hφ_half]
  rw [one_le_div (sq_pos_of_pos hφ_pos)]
  linarith only [hnum, hφ2]

private lemma four_le_sq_of_two_le {x : ℝ} (hx : 2 ≤ x) : 4 ≤ x ^ 2 := by
  nlinarith only [hx]

/-- **Theorem 8.1** (`spanner.tex`, page 39, lines 6–15 & 205–220) in paper form, for any
`tools : SpannerTools` and per-call cost specification `costs : SpannerToolCosts`:
given valid `H'`, `J` and embedding `Π_{J → H'}` (with `1 ≤ length Π_{J → H'}` when `1 ≤ J.m`),
`out := sparsify tools H' J embJH` returns subgraph `J̃ ⊆ J` (`out.Jtilde`), embedding
`embJJtilde : J → J̃`, and restricted embedding `embJHtilde : J̃ → H'` satisfying:
1. Vertex congestion `vcong(Π_{J→H'} ∘ Π_{J→J̃}) ≤ γ_c · length(Π_{J→H'}) · (vcong(Π_{J→H'}) + Δ_max(J))`
   with `γ_c = 2 (η₁ + 1/2)(η₂ + 1/2) γ_ExpPath² γ_del² / φ_ds² = O(γ_ExpPath² γ_del² log(m/φ_dec) log m / φ_ds²)`.
2. Length `length(Π_{J→H'} ∘ Π_{J→J̃}) ≤ γ_ℓ · length(Π_{J→H'})` with `γ_ℓ = γ_ExpPath²`.
3. Sparsity `|E(J̃)| ≤ (1 + c_ℓ · c_deg / log 2) |V(J)| γ_ℓ (1 + log(|V(J)| + |E(J)| + 2))`.
4. Runtime `sparsifyCost ≤ callCost(Decompose) + O(|V(J)| + |E(J)| γ_ℓ² length(Π_{J→H'}) log(|V(J)| + |E(J)| + 2))`,
   and combined bound `≤ ((K_dec + 1) decFactor(J.m) + sparsifyBaseConst) · (|V(J)| + |E(J)| γ_ℓ² length(Π_{J→H'})) (1 + log(|V(J)| + |E(J)| + 2))`. -/
private lemma dec_gamma_t_absorb {A B M γ : ℝ} (hA : 0 ≤ A) (hγ : 1 ≤ γ) (hM : 0 ≤ M) :
    (A + B * γ) * M ≤ (A + B) * γ * M := by
  have h1 : A + B * γ ≤ (A + B) * γ := by nlinarith only [hA, hγ]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h1 hM

theorem theorem_8_1_with_time (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (γ_t : ℝ) (hγt : 1 ≤ γ_t)
    (hγJq : let wd := (sparsifyLocal (tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))) H' J embJH).wd
      tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m ≤ γ_t * wd.γ_ExpPath)
    (hγWq : let wd := (sparsifyLocal (tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))) H' J embJH).wd
      tools.pathDS.γ_query wd.φ_Const wd.M_W ≤ γ_t * wd.γ_ExpPath) :
    let out := sparsify tools H' J embJH
    let wd := out.wd
    let embJHtilde := restrictEmb embJH out.keptEdges
    let γ_ℓ := wd.γ_ExpPath ^ 2
    let γ_c := 2 * ((eta1Bound wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2) *
      wd.γ_ExpPath ^ 2 * wd.γ_del ^ 2 / wd.φ_ds ^ 2
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    1 ≤ γ_c ∧
    4 ≤ γ_ℓ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) ∧
    (length J out.embJJtilde : ℝ) ≤ γ_ℓ ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      γ_ℓ * (length J embJH : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤ (1 + tools.decompose.c_ℓ * wd.c_deg / Real.log 2) *
      (J.n : ℝ) * γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      ((costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m +
        sparsifyBaseConst wd.c_deg costs) * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro out wd embJHtilde γ_ℓ γ_c
  let ltools := tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))
  have hw := buildWitness_ok ltools H' J embJH hJ hembJH le_rfl le_rfl
  have h1 := theorem_8_1_internal tools H' J embJH hJ hembJH
  rcases h1 with ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid,
    _, _, hembJHtilde, hembJJtilde, _, hcong_eta, hJJtilde_len, hcomp_len,
    _, hJtilde_m_n, _⟩
  have hγE_ge2 : 2 ≤ wd.γ_ExpPath := by
    have hdiv : (2 : ℝ) ≤ 1 / wd.φ_ds :=
      (le_div_iff₀ hw.φ_ds_pos).mpr (by nlinarith only [hw.φ_ds_half])
    exact le_trans hdiv hw.γ_ExpPath_ge
  have hγ_ℓ_ge4 : 4 ≤ γ_ℓ := four_le_sq_of_two_le hγE_ge2
  have hη₁ : 1 ≤ eta1Bound wd J := by unfold eta1Bound; omega
  have hη₂ : 1 ≤ eta2Bound J := by unfold eta2Bound; omega
  have hγ_c_ge1 : 1 ≤ γ_c :=
    gammaC_ge_one hη₁ hη₂ hγE_ge2 hw.γ_del_ge hw.φ_ds_pos hw.φ_ds_half
  have hcong_paper : vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by
    have hτ_eq : ((eta1Bound wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2) *
        wd.τ₁ * wd.τ₂ =
        γ_c * (length J embJH : ℝ) * (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by
      dsimp only [γ_c]
      change ((eta1Bound wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2) *
          (2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) *
          (wd.γ_ExpPath * wd.γ_del / wd.φ_ds) = _
      ring
    exact hτ_eq ▸ hcong_eta
  have hsp := sparsifySparsity_le ltools H' J embJH hJ hw hJtilde_m_n
  have hrt := sparsifyLocalCost_le_with_time ltools costs H' J embJH hJ hembJH le_rfl le_rfl hLen
    γ_t hγt hγJq hγWq
  have hcomb : (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
      ((costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m +
        sparsifyBaseConst wd.c_deg costs * γ_t) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
    combine_dec_cost_le costs.decompose J le_rfl
      (le_trans (by norm_num) hγ_ℓ_ge4)
      (mul_nonneg (sparsifyBaseConst_nonneg hw.c_deg_ge costs) (by linarith only [hγt]))
      (fun hm => by exact_mod_cast hLen hm) (Nat.cast_nonneg _)
  have hgt_comb : ((costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m +
        sparsifyBaseConst wd.c_deg costs * γ_t) *
      ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
      ((costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m +
        sparsifyBaseConst wd.c_deg costs) * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have hfac_nn : 0 ≤ (costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m :=
      mul_nonneg (by linarith only [costs.decompose.hK_dec])
        (by linarith only [costs.decompose.hdec_ge J.m])
    have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
      linarith only [one_le_one_add_log J.n J.m]
    have hmain_nn : 0 ≤ ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
      mul_nonneg (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))) hL_nn
    simpa only [mul_assoc] using dec_gamma_t_absorb hfac_nn hγt hmain_nn
  refine ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid, hembJHtilde, hembJJtilde,
    hγ_c_ge1, hγ_ℓ_ge4, hcong_paper, hJJtilde_len, hcomp_len, hsp, hrt,
    le_trans hrt (le_trans hcomb hgt_comb)⟩

/-- **Theorem 8.1** (`spanner.tex`, pages 39–41) in the `γ_query = γ_ExpPath` specialization. -/
theorem theorem_8_1 (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    let out := sparsify tools H' J embJH
    let wd := out.wd
    let embJHtilde := restrictEmb embJH out.keptEdges
    let φ_ds := wd.φ_ds
    let γ_ExpPath := wd.γ_ExpPath
    let γ_del := wd.γ_del
    let γ_ℓ := γ_ExpPath ^ 2
    let η₁ := eta1Bound wd J
    let η₂ := eta2Bound J
    let γ_c := 2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) * γ_ExpPath ^ 2 * γ_del ^ 2 / φ_ds ^ 2
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    1 ≤ γ_c ∧
    4 ≤ γ_ℓ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) * (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) ∧
    (length J out.embJJtilde : ℝ) ≤ γ_ℓ ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤ γ_ℓ * (length J embJH : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤
      (1 + tools.decompose.c_ℓ * wd.c_deg / Real.log 2) * (J.n : ℝ) * γ_ℓ *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost wd.J0_strip.m : ℝ) +
      sparsifyBaseConst wd.c_deg costs *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      ((costs.decompose.K_dec + 1) * costs.decompose.decFactor J.m +
        sparsifyBaseConst wd.c_deg costs) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  let ltools := tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))
  have hw := buildWitness_ok ltools H' J embJH hJ hembJH le_rfl le_rfl
  let wd := (sparsifyLocal ltools H' J embJH).wd
  have hJ_eq : tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m =
      tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m :=
    hγq wd.φ_dec wd.J0_strip.m hw.φ_dec_pos
  have hW_eq : tools.pathDS.γ_query wd.φ_Const wd.M_W =
      tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W :=
    hγq wd.φ_Const wd.M_W hw.φ_Const_pos
  have h1 := theorem_8_1_with_time tools costs H' J embJH hJ hembJH hLen 1 le_rfl
    (by change tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m ≤ 1 * wd.γ_ExpPath
        rw [hJ_eq, one_mul]; exact le_max_left _ _)
    (by change tools.pathDS.γ_query wd.φ_Const wd.M_W ≤ 1 * wd.γ_ExpPath
        rw [hW_eq, one_mul]; exact le_max_right _ _)
  simpa only [mul_one] using h1

private lemma gammaC_le_cap {η₁ η₂ η₁_c η₂_c : ℕ} {γE γd φ γE_c γd_c φ_c : ℝ}
    (hη₁ : η₁ ≤ η₁_c) (hη₂ : η₂ ≤ η₂_c)
    (hγE_nn : 0 ≤ γE) (hγE : γE ≤ γE_c)
    (hγd_nn : 0 ≤ γd) (hγd : γd ≤ γd_c)
    (hφ_c_pos : 0 < φ_c) (hφ : φ_c ≤ φ) :
    2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) * γE ^ 2 * γd ^ 2 / φ ^ 2 ≤
      2 * ((η₁_c : ℝ) + 1 / 2) * ((η₂_c : ℝ) + 1 / 2) * γE_c ^ 2 * γd_c ^ 2 / φ_c ^ 2 := by
  have hη₁_r : (η₁ : ℝ) + 1 / 2 ≤ (η₁_c : ℝ) + 1 / 2 := by
    have : (η₁ : ℝ) ≤ (η₁_c : ℝ) := by exact_mod_cast hη₁
    linarith only [this]
  have hη₂_r : (η₂ : ℝ) + 1 / 2 ≤ (η₂_c : ℝ) + 1 / 2 := by
    have : (η₂ : ℝ) ≤ (η₂_c : ℝ) := by exact_mod_cast hη₂
    linarith only [this]
  have h1_nn : 0 ≤ (η₁ : ℝ) + 1 / 2 := by positivity
  have h2_nn : 0 ≤ (η₂ : ℝ) + 1 / 2 := by positivity
  have hE2 : γE ^ 2 ≤ γE_c ^ 2 := by
    rw [sq, sq]; exact mul_le_mul hγE hγE hγE_nn (le_trans hγE_nn hγE)
  have hd2 : γd ^ 2 ≤ γd_c ^ 2 := by
    rw [sq, sq]; exact mul_le_mul hγd hγd hγd_nn (le_trans hγd_nn hγd)
  have hp1 : 2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) ≤
      2 * ((η₁_c : ℝ) + 1 / 2) * ((η₂_c : ℝ) + 1 / 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hη₁_r (by norm_num)) hη₂_r h2_nn (by positivity)
  have hp2 : γE ^ 2 * γd ^ 2 ≤ γE_c ^ 2 * γd_c ^ 2 :=
    mul_le_mul hE2 hd2 (sq_nonneg _) (by positivity)
  have hnum : 2 * ((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2) * γE ^ 2 * γd ^ 2 ≤
      2 * ((η₁_c : ℝ) + 1 / 2) * ((η₂_c : ℝ) + 1 / 2) * γE_c ^ 2 * γd_c ^ 2 := by
    have hp3 := mul_le_mul hp1 hp2 (by positivity) (by positivity)
    linarith only [hp3]
  have hφ2 : φ_c ^ 2 ≤ φ ^ 2 := by
    rw [sq, sq]; exact mul_le_mul hφ hφ hφ_c_pos.le (le_trans hφ_c_pos.le hφ)
  exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hφ_c_pos) hφ2

/-- Parametrized uniform-cap **Theorem 8.1** at edge-count cap `M`, carrying multiplicative
query/fallback runtime overhead `γ_t = capGammaQuery c_deg φ_Const tools.pathDS φ_min M`. -/
theorem theorem_8_1_at_cap_with_time (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (M : ℕ) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hJm : J.m ≤ M) (hLen : 1 ≤ J.m → 1 ≤ length J embJH) :
    let out := sparsify tools H' J embJH
    let embJHtilde := restrictEmb embJH out.keptEdges
    let φ_min := hdec.φ_lb M
    let c_deg := tools.constructExpander.c_deg
    let φ_Const := tools.constructExpander.φ_Const
    let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min M
    let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min M
    let γ_t := capGammaQuery c_deg φ_Const tools.pathDS φ_min M
    let K_s := 1 + tools.decompose.c_ℓ * c_deg / Real.log 2
    let K_t := (costs.decompose.K_dec + 1) * costs.decompose.decFactor M +
      sparsifyBaseConst c_deg costs
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    1 ≤ γ_c ∧
    4 ≤ γ_ℓ ∧
    0 ≤ K_s ∧
    1 ≤ K_t ∧
    1 ≤ γ_t ∧
    out.wd.γ_ExpPath ^ 2 ≤ γ_ℓ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) ∧
    (length J out.embJJtilde : ℝ) ≤ γ_ℓ ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      γ_ℓ * (length J embJH : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      K_t * γ_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro out embJHtilde φ_min c_deg φ_Const γ_ℓ γ_c γ_t K_s K_t
  let ltools := tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))
  have hw := buildWitness_ok ltools H' J embJH hJ hembJH le_rfl le_rfl
  have hφ_pos : 0 < φ_min := hdec.hφ_lb_pos M
  have hφ_dec_ge : φ_min ≤ out.wd.φ_dec :=
    le_trans (hdec.hφ_lb_anti (le_trans (stripLoops_m_le J) hJm))
      (hdec.hφ_dec_ge (stripLoops J) (stripLoops_isValid hJ) (stripLoops_isLoopless J))
  obtain ⟨hcap_φ, hcap_γE, hcap_γd, hcap_η₁, hcap_η₂⟩ :=
    cap_bounds_of_le ltools H' J embJH hJ hw hpds hJm hφ_pos hφ_dec_ge
  obtain ⟨hqJ, hqW⟩ := capGammaQuery_bounds_of_le ltools H' J embJH hJ hw hpds hJm hφ_pos hφ_dec_ge
  have hγt_ge1 : 1 ≤ γ_t := by
    have h2 := two_le_capGammaExpPath (c_deg := c_deg) (φ_Const := φ_Const)
      (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos M
    have hq := capGammaExpPath_le_capGammaQuery (c_deg := c_deg) (φ_Const := φ_Const)
      (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos M
    dsimp only [γ_t]; linarith
  have hγE_ge1 : 1 ≤ (buildWitness ltools H' J embJH).γ_ExpPath := by
    have h2 : (2 : ℝ) ≤ 1 / (buildWitness ltools H' J embJH).φ_ds := by
      rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
    linarith [hw.γ_ExpPath_ge]
  have hγt_nn : 0 ≤ γ_t := by linarith only [hγt_ge1]
  have ht := theorem_8_1_with_time tools costs H' J embJH hJ hembJH hLen γ_t hγt_ge1
    (le_trans hqJ (le_mul_of_one_le_right hγt_nn hγE_ge1))
    (le_trans hqW (le_mul_of_one_le_right hγt_nn hγE_ge1))
  rcases ht with ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid, hembJHtilde, hembJJtilde,
    _, _, hcong, hJJ_len, hcomp_len, hsp, hrt, _⟩
  have hγE_nn : 0 ≤ out.wd.γ_ExpPath :=
    le_trans (div_nonneg zero_le_one hw.φ_ds_pos.le) hw.γ_ExpPath_ge
  have hγE_cap_nn : 0 ≤ capGammaExpPath c_deg φ_Const tools.pathDS φ_min M :=
    le_trans hγE_nn hcap_γE
  have hγ_ℓ_le : out.wd.γ_ExpPath ^ 2 ≤ γ_ℓ := by
    change (buildWitness ltools H' J embJH).γ_ExpPath ^ 2 ≤
      (capGammaExpPath (buildWitness ltools H' J embJH).c_deg
        (buildWitness ltools H' J embJH).φ_Const ltools.pathDS φ_min M) ^ 2
    rw [sq, sq]
    exact mul_le_mul hcap_γE hcap_γE hγE_nn hγE_cap_nn
  have hφC_pos : 0 < φ_Const := hw.φ_Const_pos
  have hγ_c_ge : 1 ≤ γ_c := one_le_capGammaC hφC_pos hφ_pos M
  have hγ_ℓ_ge : 4 ≤ γ_ℓ := four_le_capGammaL hφC_pos hφ_pos M
  have hc_deg_eq : out.wd.c_deg = c_deg := rfl
  have hKs_nn : 0 ≤ K_s := by
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hcl := tools.decompose.hc_ℓ
    have hcd := tools.constructExpander.hc_deg
    exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (by linarith only [hcl])
      (by linarith only [hcd])) hl2.le)
  have hbase_ge1 : 1 ≤ sparsifyBaseConst c_deg costs :=
    sparsifyBaseConst_ge_one tools.constructExpander.hc_deg costs
  have hdec_nn : 0 ≤ (costs.decompose.K_dec + 1) * costs.decompose.decFactor M :=
    mul_nonneg (by linarith only [costs.decompose.hK_dec])
      (by linarith only [costs.decompose.hdec_ge M])
  have hKt_ge1 : 1 ≤ K_t := by linarith only [hbase_ge1, hdec_nn]
  have hγ_c_local_le : 2 * ((eta1Bound out.wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2) *
      out.wd.γ_ExpPath ^ 2 * out.wd.γ_del ^ 2 / out.wd.φ_ds ^ 2 ≤ γ_c := by
    have hcap_φ_pos : 0 < capPhiDS c_deg φ_Const tools.pathDS φ_min M :=
      capPhiDS_pos hφC_pos hφ_pos M
    have hγd_nn : 0 ≤ out.wd.γ_del := le_trans (by norm_num) hw.γ_del_ge
    exact gammaC_le_cap hcap_η₁ hcap_η₂ hγE_nn hcap_γE hγd_nn hcap_γd hcap_φ_pos hcap_φ
  have hcong_cap : vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by
    have hfac_nn : 0 ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) :=
      add_nonneg (vcong_nonneg J H' (fun _ => 1) embJH) (Nat.cast_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ_c_local_le (Nat.cast_nonneg (length J embJH))) hfac_nn
    exact le_trans hcong h1
  have hJJ_cap : (length J out.embJJtilde : ℝ) ≤ γ_ℓ := le_trans hJJ_len hγ_ℓ_le
  have hcomp_cap : (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      γ_ℓ * (length J embJH : ℝ) :=
    le_trans hcomp_len (mul_le_mul_of_nonneg_right hγ_ℓ_le (Nat.cast_nonneg _))
  have hsp_cap : (out.Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have h1 : (1 + tools.decompose.c_ℓ * out.wd.c_deg / Real.log 2) * (J.n : ℝ) *
        out.wd.γ_ExpPath ^ 2 ≤ K_s * (J.n : ℝ) * γ_ℓ := by
      rw [hc_deg_eq]
      exact mul_le_mul_of_nonneg_left hγ_ℓ_le (mul_nonneg hKs_nn (Nat.cast_nonneg J.n))
    have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
      linarith only [one_le_one_add_log J.n J.m]
    exact le_trans hsp (mul_le_mul_of_nonneg_right h1 hL_nn)
  have hrt_cap : (sparsifyCost tools costs H' J embJH : ℝ) ≤
      K_t * γ_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have hγ_ℓ_nn : 0 ≤ γ_ℓ := by linarith only [hγ_ℓ_ge]
    have hγE4 : (out.wd.γ_ExpPath ^ 2) ^ 2 ≤ γ_ℓ ^ 2 := by
      rw [pow_two (out.wd.γ_ExpPath ^ 2), pow_two γ_ℓ]
      exact mul_le_mul hγ_ℓ_le hγ_ℓ_le (sq_nonneg _) hγ_ℓ_nn
    have hmono : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
        sparsifyBaseConst out.wd.c_deg costs * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
        (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
        sparsifyBaseConst c_deg costs * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      have h1 : (J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ) ≤
          (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγE4 (Nat.cast_nonneg J.m))
          (Nat.cast_nonneg (length J embJH))
        linarith only [this]
      have h2 : sparsifyBaseConst out.wd.c_deg costs * γ_t *
            ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) ≤
          sparsifyBaseConst c_deg costs * γ_t *
            ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) := by
        rw [hc_deg_eq]
        exact mul_le_mul_of_nonneg_left h1 (mul_nonneg
          (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs) hγt_nn)
      have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
        linarith only [one_le_one_add_log J.n J.m]
      have h3 := mul_le_mul_of_nonneg_right h2 hL_nn
      linarith only [h3]
    have hcomb := combine_dec_cost_le costs.decompose J hJm
      (le_trans (by norm_num) hγ_ℓ_ge)
      (mul_nonneg (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs) hγt_nn)
      (fun hm => by exact_mod_cast hLen hm) (Nat.cast_nonneg _)
    have hcoeff_comb : ((costs.decompose.K_dec + 1) * costs.decompose.decFactor M +
          sparsifyBaseConst c_deg costs * γ_t) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
        K_t * γ_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
        linarith only [one_le_one_add_log J.n J.m]
      have hmain_nn : 0 ≤ ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
        mul_nonneg (add_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))) hL_nn
      change ((costs.decompose.K_dec + 1) * costs.decompose.decFactor M +
          sparsifyBaseConst c_deg costs * γ_t) * _ * _ ≤ _
      simpa only [K_t, mul_assoc] using dec_gamma_t_absorb hdec_nn hγt_ge1 hmain_nn
    exact le_trans hrt (le_trans hmono (le_trans hcomb hcoeff_comb))
  exact ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid, hembJHtilde, hembJJtilde,
    hγ_c_ge, hγ_ℓ_ge, hKs_nn, hKt_ge1, hγt_ge1, hγ_ℓ_le, hcong_cap, hJJ_cap, hcomp_cap, hsp_cap, hrt_cap⟩

/-- **Theorem 8.1** at edge-count cap `M` (`spanner.tex`, page 39) in the `γ_query = γ_ExpPath`
specialization. -/
theorem theorem_8_1_at_cap (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (M : ℕ) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hJm : J.m ≤ M) (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    let out := sparsify tools H' J embJH
    let embJHtilde := restrictEmb embJH out.keptEdges
    let φ_min := hdec.φ_lb M
    let c_deg := tools.constructExpander.c_deg
    let φ_Const := tools.constructExpander.φ_Const
    let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min M
    let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min M
    let K_s := 1 + tools.decompose.c_ℓ * c_deg / Real.log 2
    let K_t := (costs.decompose.K_dec + 1) * costs.decompose.decFactor M +
      sparsifyBaseConst c_deg costs
    out.keptEdges.Nodup ∧
    (∀ j ∈ out.keptEdges, j < J.m) ∧
    out.Jtilde.n = J.n ∧
    out.Jtilde.m = out.keptEdges.length ∧
    out.Jtilde.IsValid ∧
    IsEmbedding out.Jtilde H' embJHtilde ∧
    IsEmbedding J out.Jtilde out.embJJtilde ∧
    1 ≤ γ_c ∧
    4 ≤ γ_ℓ ∧
    0 ≤ K_s ∧
    1 ≤ K_t ∧
    out.wd.γ_ExpPath ^ 2 ≤ γ_ℓ ∧
    vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) ∧
    (length J out.embJJtilde : ℝ) ≤ γ_ℓ ∧
    (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      γ_ℓ * (length J embJH : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ∧
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      K_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro out embJHtilde φ_min c_deg φ_Const γ_ℓ γ_c K_s K_t
  let ltools := tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))
  have hw := buildWitness_ok ltools H' J embJH hJ hembJH le_rfl le_rfl
  have hφ_pos : 0 < φ_min := hdec.hφ_lb_pos M
  have hφ_dec_ge : φ_min ≤ out.wd.φ_dec :=
    le_trans (hdec.hφ_lb_anti (le_trans (stripLoops_m_le J) hJm))
      (hdec.hφ_dec_ge (stripLoops J) (stripLoops_isValid hJ) (stripLoops_isLoopless J))
  obtain ⟨hcap_φ, hcap_γE, hcap_γd, hcap_η₁, hcap_η₂⟩ :=
    cap_bounds_of_le ltools H' J embJH hJ hw hpds hJm hφ_pos hφ_dec_ge
  have ht := theorem_8_1 tools costs H' J embJH hJ hembJH hLen hγq
  rcases ht with ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid, hembJHtilde, hembJJtilde,
    _, _, hcong, hJJ_len, hcomp_len, hsp, hrt, _⟩
  have hγE_nn : 0 ≤ out.wd.γ_ExpPath :=
    le_trans (div_nonneg zero_le_one hw.φ_ds_pos.le) hw.γ_ExpPath_ge
  have hγE_cap_nn : 0 ≤ capGammaExpPath c_deg φ_Const tools.pathDS φ_min M :=
    le_trans hγE_nn hcap_γE
  have hγ_ℓ_le : out.wd.γ_ExpPath ^ 2 ≤ γ_ℓ := by
    change (buildWitness ltools H' J embJH).γ_ExpPath ^ 2 ≤
      (capGammaExpPath (buildWitness ltools H' J embJH).c_deg
        (buildWitness ltools H' J embJH).φ_Const ltools.pathDS φ_min M) ^ 2
    rw [sq, sq]
    exact mul_le_mul hcap_γE hcap_γE hγE_nn hγE_cap_nn
  have hφC_pos : 0 < φ_Const := hw.φ_Const_pos
  have hγ_c_ge : 1 ≤ γ_c := one_le_capGammaC hφC_pos hφ_pos M
  have hγ_ℓ_ge : 4 ≤ γ_ℓ := four_le_capGammaL hφC_pos hφ_pos M
  have hc_deg_eq : out.wd.c_deg = c_deg := rfl
  have hKs_nn : 0 ≤ K_s := by
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hcl := tools.decompose.hc_ℓ
    have hcd := tools.constructExpander.hc_deg
    exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (by linarith only [hcl])
      (by linarith only [hcd])) hl2.le)
  have hbase_ge1 : 1 ≤ sparsifyBaseConst c_deg costs :=
    sparsifyBaseConst_ge_one tools.constructExpander.hc_deg costs
  have hdec_nn : 0 ≤ (costs.decompose.K_dec + 1) * costs.decompose.decFactor M :=
    mul_nonneg (by linarith only [costs.decompose.hK_dec])
      (by linarith only [costs.decompose.hdec_ge M])
  have hKt_ge1 : 1 ≤ K_t := by linarith only [hbase_ge1, hdec_nn]
  have hγ_c_local_le : 2 * ((eta1Bound out.wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2) *
      out.wd.γ_ExpPath ^ 2 * out.wd.γ_del ^ 2 / out.wd.φ_ds ^ 2 ≤ γ_c := by
    have hcap_φ_pos : 0 < capPhiDS c_deg φ_Const tools.pathDS φ_min M :=
      capPhiDS_pos hφC_pos hφ_pos M
    have hγd_nn : 0 ≤ out.wd.γ_del := le_trans (by norm_num) hw.γ_del_ge
    exact gammaC_le_cap hcap_η₁ hcap_η₂ hγE_nn hcap_γE hγd_nn hcap_γd hcap_φ_pos hcap_φ
  have hcong_cap : vcong J H' (fun _ => 1) (compose out.Jtilde embJHtilde out.embJJtilde) ≤
      γ_c * (length J embJH : ℝ) *
        (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by
    have hfac_nn : 0 ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) :=
      add_nonneg (vcong_nonneg J H' (fun _ => 1) embJH) (Nat.cast_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ_c_local_le (Nat.cast_nonneg (length J embJH))) hfac_nn
    exact le_trans hcong h1
  have hJJ_cap : (length J out.embJJtilde : ℝ) ≤ γ_ℓ := le_trans hJJ_len hγ_ℓ_le
  have hcomp_cap : (length J (compose out.Jtilde embJHtilde out.embJJtilde) : ℝ) ≤
      γ_ℓ * (length J embJH : ℝ) :=
    le_trans hcomp_len (mul_le_mul_of_nonneg_right hγ_ℓ_le (Nat.cast_nonneg _))
  have hsp_cap : (out.Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have h1 : (1 + tools.decompose.c_ℓ * out.wd.c_deg / Real.log 2) * (J.n : ℝ) *
        out.wd.γ_ExpPath ^ 2 ≤ K_s * (J.n : ℝ) * γ_ℓ := by
      rw [hc_deg_eq]
      exact mul_le_mul_of_nonneg_left hγ_ℓ_le (mul_nonneg hKs_nn (Nat.cast_nonneg J.n))
    have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
      linarith only [one_le_one_add_log J.n J.m]
    exact le_trans hsp (mul_le_mul_of_nonneg_right h1 hL_nn)
  have hrt_cap : (sparsifyCost tools costs H' J embJH : ℝ) ≤
      K_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have hγ_ℓ_nn : 0 ≤ γ_ℓ := by linarith only [hγ_ℓ_ge]
    have hγE4 : (out.wd.γ_ExpPath ^ 2) ^ 2 ≤ γ_ℓ ^ 2 := by
      rw [pow_two (out.wd.γ_ExpPath ^ 2), pow_two γ_ℓ]
      exact mul_le_mul hγ_ℓ_le hγ_ℓ_le (sq_nonneg _) hγ_ℓ_nn
    have hmono : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
        sparsifyBaseConst out.wd.c_deg costs *
          ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ≤
        (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
        sparsifyBaseConst c_deg costs *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      have h1 : (J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ) ≤
          (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγE4 (Nat.cast_nonneg J.m))
          (Nat.cast_nonneg (length J embJH))
        linarith only [this]
      have h2 : sparsifyBaseConst out.wd.c_deg costs *
            ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) ≤
          sparsifyBaseConst c_deg costs *
            ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) := by
        rw [hc_deg_eq]
        exact mul_le_mul_of_nonneg_left h1 (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs)
      have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by
        linarith only [one_le_one_add_log J.n J.m]
      have h3 := mul_le_mul_of_nonneg_right h2 hL_nn
      linarith only [h3]
    have hcomb := combine_dec_cost_le costs.decompose J hJm
      (le_trans (by norm_num) hγ_ℓ_ge) (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs)
      (fun hm => by exact_mod_cast hLen hm) (Nat.cast_nonneg _)
    exact le_trans (le_trans hrt hmono) hcomb
  exact ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hJtilde_valid, hembJHtilde, hembJJtilde,
    hγ_c_ge, hγ_ℓ_ge, hKs_nn, hKt_ge1, hγ_ℓ_le, hcong_cap, hJJ_cap, hcomp_cap, hsp_cap, hrt_cap⟩

/-- Corollary of `theorem_8_1_at_cap` when `decFactor M ≤ C_dec · γ_ℓ²` (e.g. `csGamma_dominates_sb`
in `DecrementalPaths.lean`): `|V(J)|` is multiplied only by the constant `sparsifyBaseConst`,
without any `decFactor M` dependence on `|V(J)|`. -/
theorem theorem_8_1_at_cap_of_dec_le_with_time (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (M : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : costs.decompose.decFactor M ≤
      C_dec * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (hdec.φ_lb M) M) ^ 2)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hJm : J.m ≤ M) (hLen : 1 ≤ J.m → 1 ≤ length J embJH) :
    let γ_ℓ := capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb M) M
    let γ_t := capGammaQuery tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb M) M
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (C_dec * (costs.decompose.K_dec + 1) +
        sparsifyBaseConst tools.constructExpander.c_deg costs) * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro γ_ℓ γ_t
  let out := sparsify tools H' J embJH
  set c_deg := tools.constructExpander.c_deg
  let ltools := tools.toLocal J.n (2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J))
  have hw := buildWitness_ok ltools H' J embJH hJ hembJH le_rfl le_rfl
  have hφ_pos : 0 < hdec.φ_lb M := hdec.hφ_lb_pos M
  have hφ_dec_ge : hdec.φ_lb M ≤ out.wd.φ_dec :=
    le_trans (hdec.hφ_lb_anti (le_trans (stripLoops_m_le J) hJm))
      (hdec.hφ_dec_ge (stripLoops J) (stripLoops_isValid hJ) (stripLoops_isLoopless J))
  obtain ⟨hqJ, hqW⟩ := capGammaQuery_bounds_of_le ltools H' J embJH hJ hw hpds hJm hφ_pos hφ_dec_ge
  have hγt_ge1 : 1 ≤ γ_t := by
    have h2 := two_le_capGammaExpPath (c_deg := c_deg)
      (φ_Const := tools.constructExpander.φ_Const) (pds := tools.pathDS)
      tools.constructExpander.hφ_pos hφ_pos M
    have hq := capGammaExpPath_le_capGammaQuery (c_deg := c_deg)
      (φ_Const := tools.constructExpander.φ_Const) (pds := tools.pathDS)
      tools.constructExpander.hφ_pos hφ_pos M
    dsimp only [γ_t]; linarith
  have hγE_ge1 : 1 ≤ (buildWitness ltools H' J embJH).γ_ExpPath := by
    have h2 : (2 : ℝ) ≤ 1 / (buildWitness ltools H' J embJH).φ_ds := by
      rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
    linarith [hw.γ_ExpPath_ge]
  have hγt_nn : 0 ≤ γ_t := by linarith only [hγt_ge1]
  have h1 := theorem_8_1_with_time tools costs H' J embJH hJ hembJH hLen γ_t hγt_ge1
    (le_trans hqJ (le_mul_of_one_le_right hγt_nn hγE_ge1))
    (le_trans hqW (le_mul_of_one_le_right hγt_nn hγE_ge1))
  have h2 := theorem_8_1_at_cap_with_time tools costs hdec hpds M H' J embJH hJ hembJH hJm hLen
  have hrt := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases h2 with ⟨_, _, _, _, _, _, _, _, hγ_ℓ_ge, _, _, _, hγ_ℓ_le, _⟩
  set L_log := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log J.n J.m
  have hγ_ℓ_nn : 0 ≤ γ_ℓ := by linarith only [hγ_ℓ_ge]
  have hγ4 : (out.wd.γ_ExpPath ^ 2) ^ 2 ≤ γ_ℓ ^ 2 := by
    rw [pow_two (out.wd.γ_ExpPath ^ 2), pow_two γ_ℓ]
    exact mul_le_mul hγ_ℓ_le hγ_ℓ_le (sq_nonneg _) hγ_ℓ_nn
  have hmono : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst out.wd.c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) * L_log ≤
      (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
    have ha : (J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ) ≤
        (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγ4 (Nat.cast_nonneg J.m))
        (Nat.cast_nonneg (length J embJH))
      linarith only [this]
    have hL_nn : 0 ≤ L_log := by linarith only [hL1]
    have hc_deg_eq : out.wd.c_deg = c_deg := rfl
    have hb : sparsifyBaseConst out.wd.c_deg costs * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) ≤
        sparsifyBaseConst c_deg costs * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) := by
      rw [hc_deg_eq]
      exact mul_le_mul_of_nonneg_left ha (mul_nonneg
        (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs) hγt_nn)
    have hc := mul_le_mul_of_nonneg_right hb hL_nn
    linarith only [hc]
  have hrt' : (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst c_deg costs * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log :=
    le_trans hrt hmono
  have hdec_term : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) ≤
      (C_dec * (costs.decompose.K_dec + 1)) * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
    have hKdec : 0 ≤ costs.decompose.K_dec + 1 := by linarith only [costs.decompose.hK_dec]
    rcases Nat.eq_zero_or_pos J.m with hm0 | hm_pos
    · have hstrip0 : out.wd.J0_strip.m = 0 := by
        have : out.wd.J0_strip.m ≤ J.m := stripLoops_m_le J
        exact Nat.eq_zero_of_le_zero (hm0 ▸ this)
      rw [hstrip0, costs.decompose.callCost_zero, Nat.cast_zero]
      have hpos1 : 0 ≤ C_dec * (costs.decompose.K_dec + 1) * γ_t := mul_nonneg (mul_nonneg hC_nn hKdec) hγt_nn
      exact mul_nonneg (mul_nonneg hpos1 (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))))
        (by linarith only [hL1])
    · have hlen1 : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hLen hm_pos
      have hcall := costs.decompose.callCost_le_of_le (le_trans (stripLoops_m_le J) hJm)
      have hstrip_m : (out.wd.J0_strip.m : ℝ) ≤ (J.m : ℝ) :=
        Nat.cast_le.mpr (stripLoops_m_le J)
      have hcall' : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) ≤
          (C_dec * (costs.decompose.K_dec + 1)) * ((J.m : ℝ) * γ_ℓ ^ 2) := by
        have h0 : (costs.decompose.K_dec + 1) * (out.wd.J0_strip.m : ℝ) * costs.decompose.decFactor M ≤
            (costs.decompose.K_dec + 1) * (J.m : ℝ) * costs.decompose.decFactor M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstrip_m hKdec)
            (by linarith only [costs.decompose.hdec_ge M])
        have h1 : (costs.decompose.K_dec + 1) * (J.m : ℝ) * costs.decompose.decFactor M ≤
            (costs.decompose.K_dec + 1) * (J.m : ℝ) * (C_dec * γ_ℓ ^ 2) :=
          mul_le_mul_of_nonneg_left hdec_le (mul_nonneg hKdec (Nat.cast_nonneg _))
        exact le_trans (le_trans hcall h0) (le_trans h1 (le_of_eq (by ring)))
      have hm_le_rhs : (J.m : ℝ) * γ_ℓ ^ 2 ≤
          γ_t * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
        have h1 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) :=
          le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hlen1
        have h2 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
          have : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
          linarith only [h1, this]
        have hprod_nn : 0 ≤ ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log :=
          mul_nonneg (add_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)))
            (by linarith only [hL1])
        have h3 := le_trans h2 (le_mul_of_one_le_right
          (add_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))) hL1)
        exact le_trans h3 (le_trans (le_mul_of_one_le_left hprod_nn hγt_ge1) (le_of_eq (by ring)))
      have hmul := mul_le_mul_of_nonneg_left hm_le_rhs (mul_nonneg hC_nn hKdec)
      exact le_trans hcall' (le_trans hmul (le_of_eq (by ring)))
  have heq : (C_dec * (costs.decompose.K_dec + 1) + sparsifyBaseConst c_deg costs) * γ_t *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log =
      (C_dec * (costs.decompose.K_dec + 1)) * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log +
        sparsifyBaseConst c_deg costs * γ_t *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by ring
  rw [heq]
  linarith only [hrt', hdec_term]

theorem theorem_8_1_at_cap_of_dec_le (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (M : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : costs.decompose.decFactor M ≤
      C_dec * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (hdec.φ_lb M) M) ^ 2)
    (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hJm : J.m ≤ M) (hLen : 1 ≤ J.m → 1 ≤ length J embJH)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    let γ_ℓ := capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb M) M
    (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (C_dec * (costs.decompose.K_dec + 1) +
        sparsifyBaseConst tools.constructExpander.c_deg costs) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro γ_ℓ
  let out := sparsify tools H' J embJH
  set c_deg := tools.constructExpander.c_deg
  have h1 := theorem_8_1 tools costs H' J embJH hJ hembJH hLen hγq
  have h2 := theorem_8_1_at_cap tools costs hdec hpds M H' J embJH hJ hembJH hJm hLen hγq
  have hrt := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hγ_ℓ_le := h2.2.2.2.2.2.2.2.2.2.2.2.1
  have hγ_ℓ_ge := h2.2.2.2.2.2.2.2.2.1
  set L_log := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log J.n J.m
  have hγ4 : (out.wd.γ_ExpPath ^ 2) ^ 2 ≤ γ_ℓ ^ 2 := by
    rw [pow_two (out.wd.γ_ExpPath ^ 2), pow_two γ_ℓ]
    exact mul_le_mul hγ_ℓ_le hγ_ℓ_le (sq_nonneg _) (by linarith only [hγ_ℓ_ge])
  have hmono : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst out.wd.c_deg costs *
        ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) * L_log ≤
      (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst c_deg costs *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
    have ha : (J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ) ≤
        (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγ4 (Nat.cast_nonneg J.m))
        (Nat.cast_nonneg (length J embJH))
      linarith only [this]
    have hL_nn : 0 ≤ L_log := by linarith only [hL1]
    have hc_deg_eq : out.wd.c_deg = c_deg := rfl
    have hb : sparsifyBaseConst out.wd.c_deg costs *
          ((J.n : ℝ) + (J.m : ℝ) * (out.wd.γ_ExpPath ^ 2) ^ 2 * (length J embJH : ℝ)) ≤
        sparsifyBaseConst c_deg costs *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) := by
      rw [hc_deg_eq]
      exact mul_le_mul_of_nonneg_left ha (sparsifyBaseConst_nonneg tools.constructExpander.hc_deg costs)
    have hc := mul_le_mul_of_nonneg_right hb hL_nn
    linarith only [hc]
  have hrt' : (sparsifyCost tools costs H' J embJH : ℝ) ≤
      (costs.decompose.callCost out.wd.J0_strip.m : ℝ) +
      sparsifyBaseConst c_deg costs *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log :=
    le_trans hrt hmono
  have hdec_term : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) ≤
      (C_dec * (costs.decompose.K_dec + 1)) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
    have hKdec : 0 ≤ costs.decompose.K_dec + 1 := by linarith only [costs.decompose.hK_dec]
    rcases Nat.eq_zero_or_pos J.m with hm0 | hm_pos
    · have hstrip0 : out.wd.J0_strip.m = 0 := by
        have : out.wd.J0_strip.m ≤ J.m := stripLoops_m_le J
        exact Nat.eq_zero_of_le_zero (hm0 ▸ this)
      rw [hstrip0, costs.decompose.callCost_zero, Nat.cast_zero]
      have hpos1 : 0 ≤ C_dec * (costs.decompose.K_dec + 1) := mul_nonneg hC_nn hKdec
      positivity
    · have hlen1 : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hLen hm_pos
      have hcall := costs.decompose.callCost_le_of_le (le_trans (stripLoops_m_le J) hJm)
      have hstrip_m : (out.wd.J0_strip.m : ℝ) ≤ (J.m : ℝ) :=
        Nat.cast_le.mpr (stripLoops_m_le J)
      have hcall' : (costs.decompose.callCost out.wd.J0_strip.m : ℝ) ≤
          (C_dec * (costs.decompose.K_dec + 1)) * ((J.m : ℝ) * γ_ℓ ^ 2) := by
        have h0 : (costs.decompose.K_dec + 1) * (out.wd.J0_strip.m : ℝ) * costs.decompose.decFactor M ≤
            (costs.decompose.K_dec + 1) * (J.m : ℝ) * costs.decompose.decFactor M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstrip_m hKdec)
            (by linarith only [costs.decompose.hdec_ge M])
        have h1 : (costs.decompose.K_dec + 1) * (J.m : ℝ) * costs.decompose.decFactor M ≤
            (costs.decompose.K_dec + 1) * (J.m : ℝ) * (C_dec * γ_ℓ ^ 2) :=
          mul_le_mul_of_nonneg_left hdec_le (mul_nonneg hKdec (Nat.cast_nonneg _))
        exact le_trans (le_trans hcall h0) (le_trans h1 (le_of_eq (by ring)))
      have hm_le_rhs : (J.m : ℝ) * γ_ℓ ^ 2 ≤
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by
        have h1 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) :=
          le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hlen1
        have h2 : (J.m : ℝ) * γ_ℓ ^ 2 ≤ (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ) := by
          have : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
          linarith only [h1, this]
        exact le_trans h2 (le_mul_of_one_le_right (by positivity) hL1)
      have hmul := mul_le_mul_of_nonneg_left hm_le_rhs (mul_nonneg hC_nn hKdec)
      exact le_trans hcall' (le_trans hmul (le_of_eq (by ring)))
  have heq : (C_dec * (costs.decompose.K_dec + 1) + sparsifyBaseConst c_deg costs) *
        ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log =
      (C_dec * (costs.decompose.K_dec + 1)) *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log +
        sparsifyBaseConst c_deg costs *
          ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (length J embJH : ℝ)) * L_log := by ring
  rw [heq]
  linarith only [hrt', hdec_term]

end MinCostFlow.Spanner
