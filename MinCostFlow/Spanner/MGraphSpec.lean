module

public import MinCostFlow.Basic.Graph
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Runtime
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.DynSpanner.Tools

import MinCostFlow.Spanner.Embedding
import MinCostFlow.Spanner.Subgraph
import MinCostFlow.Spanner.Algorithm
import MinCostFlow.Spanner.Theorem81
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import MinCostFlow.Spanner.MGraphSpecBase

/-!
# `DynSpanner.SparsifySpec` for Algorithm 4 on `MGraph`

This file proves the reverse walk/embedding/congestion/length bounds for `outJtilde` and
`citedEmbToMGraph`, defines `sparsifyMG : SpannerTools → SpannerToolCosts → MGraph → MGraph →
Embedding → DynSpanner.SparsifyOut`, and establishes `DynSpanner.SparsifySpec` (`DynSpanner/Tools.lean`)
with explicit `M`-cap parameters `sparsifyMGParams` and `sparsifyMGParamsOfDec`.
-/

public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## `sparsifyMG`, `sparsifyMGParams`, and `DynSpanner.SparsifySpec` -/

/-- Translation and return-assembly cost for `sparsifyMG`, independent of `|V(H')|` and `|E(H')|`. -/
@[expose] def translateCost (J : MGraph) (embJH : MinCostFlow.Embedding) (kept : List ℕ)
    (embJJtilde : ℕ → Walk) : ℕ :=
  J.n + J.m + (∑ e ∈ J.E, ((embJH e).length + 1)) + kept.length +
    ∑ j ∈ Finset.range J.m, ((embJJtilde j).edges.length + 1)

/-- `Sparsify` on `MGraph`: translates `(H', J, embJH)` to `Cited.Graph` (touching only `V(J)` and
the vertices/edges visited by `embJH`), invokes `sparsify tools`, and translates `J̃`, `Π_{J → J̃}`,
and the combined operation count back to `MGraph` and `DynSpanner.SparsifyOut`. -/
@[expose] noncomputable def sparsifyMG (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : MGraph) (embJH : MinCostFlow.Embedding) : DynSpanner.SparsifyOut :=
  let cH := toCitedH H' J embJH
  let cJ := toCitedJ J
  let cEmbJH := embToCited H' J embJH
  let cOut := sparsify tools cH cJ cEmbJH
  { Jtilde := outJtilde J cOut.keptEdges
    emb := citedEmbToMGraph J cOut.Jtilde cOut.keptEdges cOut.embJJtilde
    cost := sparsifyCost tools costs cH cJ cEmbJH +
      translateCost J embJH cOut.keptEdges cOut.embJJtilde }

/-- Explicit `DynSpanner.SparsifyParams` at edge-count cap `mMax` using `φ_min ≤ φ_dec`. -/
@[expose] noncomputable def sparsifyMGParams (tools : SpannerTools) (costs : SpannerToolCosts)
    (φ_min : ℝ) (hφ_pos : 0 < φ_min) (mMax : ℕ) : DynSpanner.SparsifyParams :=
  let c_deg := tools.constructExpander.c_deg
  let φ_Const := tools.constructExpander.φ_Const
  let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min mMax + 1
  let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min mMax
  let K_s := 1 + tools.decompose.c_ℓ * c_deg / Real.log 2
  let K_t := (costs.decompose.K_dec + 1) * costs.decompose.decFactor mMax +
    sparsifyBaseConst c_deg costs + 4
  { γ_c := γ_c
    γ_ℓ := γ_ℓ
    K_s := K_s
    p_s := 1
    K_t := K_t
    p_t := 1
    hγ_c := by
      have h1 : 1 ≤ capGammaC c_deg φ_Const tools.pathDS φ_min mMax :=
        one_le_capGammaC tools.constructExpander.hφ_pos hφ_pos mMax
      linarith only [h1]
    hγ_ℓ := by
      have h4 : 4 ≤ capGammaL c_deg φ_Const tools.pathDS φ_min mMax :=
        four_le_capGammaL tools.constructExpander.hφ_pos hφ_pos mMax
      linarith only [h4]
    hK_s := by
      have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      exact add_nonneg zero_le_one (div_nonneg (mul_nonneg
        (le_trans zero_le_one tools.decompose.hc_ℓ)
        (le_trans zero_le_one tools.constructExpander.hc_deg)) hl2.le)
    hK_t := by
      have h1 := sparsifyBaseConst_ge_one tools.constructExpander.hc_deg costs
      have h2 := mul_nonneg (add_nonneg costs.decompose.hK_dec zero_le_one)
        (le_trans zero_le_one (costs.decompose.hdec_ge mMax))
      linarith only [h1, h2] }

/-- Explicit `DynSpanner.SparsifyParams` at edge-count cap `mMax` when `decFactor mMax ≤ C_dec · γ_ℓ²`,
eliminating `decFactor mMax` from the `|V(J)|` term of the runtime bound. -/
@[expose] noncomputable def sparsifyMGParamsOfDec (tools : SpannerTools) (costs : SpannerToolCosts)
    (φ_min : ℝ) (hφ_pos : 0 < φ_min) (mMax : ℕ) (C_dec : ℝ) (hC_nn : 0 ≤ C_dec) :
    DynSpanner.SparsifyParams :=
  let c_deg := tools.constructExpander.c_deg
  let φ_Const := tools.constructExpander.φ_Const
  let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min mMax + 1
  let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min mMax
  let K_s := 1 + tools.decompose.c_ℓ * c_deg / Real.log 2
  let K_t := C_dec * (costs.decompose.K_dec + 1) + sparsifyBaseConst c_deg costs + 4
  { γ_c := γ_c
    γ_ℓ := γ_ℓ
    K_s := K_s
    p_s := 1
    K_t := K_t
    p_t := 1
    hγ_c := by
      have h1 : 1 ≤ capGammaC c_deg φ_Const tools.pathDS φ_min mMax :=
        one_le_capGammaC tools.constructExpander.hφ_pos hφ_pos mMax
      linarith only [h1]
    hγ_ℓ := by
      have h4 : 4 ≤ capGammaL c_deg φ_Const tools.pathDS φ_min mMax :=
        four_le_capGammaL tools.constructExpander.hφ_pos hφ_pos mMax
      linarith only [h4]
    hK_s := by
      have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      exact add_nonneg zero_le_one (div_nonneg (mul_nonneg
        (le_trans zero_le_one tools.decompose.hc_ℓ)
        (le_trans zero_le_one tools.constructExpander.hc_deg)) hl2.le)
    hK_t := by
      have h1 := sparsifyBaseConst_ge_one tools.constructExpander.hc_deg costs
      have h2 := mul_nonneg hC_nn (add_nonneg costs.decompose.hK_dec zero_le_one)
      linarith only [h1, h2] }

/-- Explicit `DynSpanner.SparsifyParams` at edge-count cap `mMax` with runtime overhead `γ_t = capGammaQuery`. -/
@[expose] noncomputable def sparsifyMGParamsWithTime (tools : SpannerTools) (costs : SpannerToolCosts)
    (φ_min : ℝ) (hφ_pos : 0 < φ_min) (mMax : ℕ) : DynSpanner.SparsifyParams :=
  let P := sparsifyMGParams tools costs φ_min hφ_pos mMax
  let c_deg := tools.constructExpander.c_deg
  let φ_Const := tools.constructExpander.φ_Const
  let γ_t := capGammaQuery c_deg φ_Const tools.pathDS φ_min mMax
  { P with
    γ_t := γ_t
    hγ_t := by
      have h2 := two_le_capGammaExpPath (c_deg := c_deg) (φ_Const := φ_Const)
        (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos mMax
      have hq := capGammaExpPath_le_capGammaQuery (c_deg := c_deg) (φ_Const := φ_Const)
        (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos mMax
      dsimp only [γ_t]
      linarith }

/-- Explicit `DynSpanner.SparsifyParams` at edge-count cap `mMax` when `decFactor mMax ≤ C_dec · γ_ℓ²`,
carrying runtime overhead `γ_t = capGammaQuery`. -/
@[expose] noncomputable def sparsifyMGParamsOfDecWithTime (tools : SpannerTools) (costs : SpannerToolCosts)
    (φ_min : ℝ) (hφ_pos : 0 < φ_min) (mMax : ℕ) (C_dec : ℝ) (hC_nn : 0 ≤ C_dec) :
    DynSpanner.SparsifyParams :=
  let P := sparsifyMGParamsOfDec tools costs φ_min hφ_pos mMax C_dec hC_nn
  let c_deg := tools.constructExpander.c_deg
  let φ_Const := tools.constructExpander.φ_Const
  let γ_t := capGammaQuery c_deg φ_Const tools.pathDS φ_min mMax
  { P with
    γ_t := γ_t
    hγ_t := by
      have h2 := two_le_capGammaExpPath (c_deg := c_deg) (φ_Const := φ_Const)
        (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos mMax
      have hq := capGammaExpPath_le_capGammaQuery (c_deg := c_deg) (φ_Const := φ_Const)
        (pds := tools.pathDS) tools.constructExpander.hφ_pos hφ_pos mMax
      dsimp only [γ_t]
      linarith }

private lemma translateCost_le {J : MGraph} {embJH : MinCostFlow.Embedding}
    {kept : List ℕ} {embJJtilde : ℕ → Walk} {γ_ℓ : ℝ}
    (hnodup : kept.Nodup) (hkept : ∀ j ∈ kept, j < J.m)
    (hlen_out : (length (toCitedJ J) embJJtilde : ℝ) ≤ γ_ℓ)
    (hγ_ge4 : 4 ≤ γ_ℓ)
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J) :
    (translateCost J embJH kept embJJtilde : ℝ) ≤
      4 * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  set L_log := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log J.n J.m
  have hkept_len : kept.length ≤ J.m := by
    have hsub : kept.toFinset ⊆ Finset.range J.m := by
      intro j hj
      exact Finset.mem_range.mpr (hkept j (List.mem_toFinset.mp hj))
    rw [← List.toFinset_card_of_nodup hnodup]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  rcases Nat.eq_zero_or_pos J.m with hm0 | hm_pos
  · have hm_empty : kept = [] := by
      rw [← List.length_eq_zero_iff]; omega
    have hJE_empty : J.E = ∅ := Finset.card_eq_zero.mp hm0
    have htr : translateCost J embJH kept embJJtilde = J.n := by
      unfold translateCost
      rw [hm0, hm_empty, hJE_empty]
      simp
    rw [htr, hm0, Nat.cast_zero, zero_mul, zero_mul, add_zero]
    have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
    have h1 : (J.n : ℝ) ≤ 4 * (J.n : ℝ) := by linarith only [hn_nn]
    have h4n_nn : 0 ≤ 4 * (J.n : ℝ) := by linarith only [hn_nn]
    exact le_trans h1 (le_mul_of_one_le_right h4n_nn hL1)
  · have hEne : J.E.Nonempty := Finset.card_pos.mp hm_pos
    have hLen1 : (1 : ℝ) ≤ (embJH.length J : ℝ) := by exact_mod_cast hLen hEne
    have hsum1 : (∑ e ∈ J.E, ((embJH e).length + 1) : ℕ) ≤ J.m * (embJH.length J + 1) := by
      calc ∑ e ∈ J.E, ((embJH e).length + 1)
          ≤ ∑ _e ∈ J.E, (embJH.length J + 1) :=
            Finset.sum_le_sum fun e he => Nat.add_le_add_right
              (Finset.le_sup (f := fun e => (embJH e).length) he) 1
        _ = J.m * (embJH.length J + 1) := by rw [Finset.sum_const, smul_eq_mul]; rfl
    have hsum2 : ((∑ j ∈ Finset.range J.m, ((embJJtilde j).edges.length + 1) : ℕ) : ℝ) ≤
        (J.m : ℝ) * (γ_ℓ + 1) := by
      rw [Nat.cast_sum]
      have h1 : (∑ j ∈ Finset.range J.m, (((embJJtilde j).edges.length + 1 : ℕ) : ℝ)) ≤
          ∑ _j ∈ Finset.range J.m, (γ_ℓ + 1) := by
        refine Finset.sum_le_sum fun j hj => ?_
        push_cast
        have hj' : j < (toCitedJ J).m := by rw [toCitedJ_m]; exact Finset.mem_range.mp hj
        have hle : ((embJJtilde j).edges.length : ℝ) ≤ (length (toCitedJ J) embJJtilde : ℝ) :=
          Nat.cast_le.mpr (edges_length_le_length embJJtilde hj')
        linarith only [hle, hlen_out]
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h1
    have htr_unfold : (translateCost J embJH kept embJJtilde : ℝ) ≤
        (J.n : ℝ) + (J.m : ℝ) + (J.m : ℝ) * ((embJH.length J : ℝ) + 1) + (J.m : ℝ) +
          (J.m : ℝ) * (γ_ℓ + 1) := by
      unfold translateCost
      simp only [Nat.cast_add]
      have hs1 : ((∑ e ∈ J.E, ((embJH e).length + 1) : ℕ) : ℝ) ≤
          (J.m : ℝ) * ((embJH.length J : ℝ) + 1) := by exact_mod_cast hsum1
      have hk_r : (kept.length : ℝ) ≤ (J.m : ℝ) := by exact_mod_cast hkept_len
      linarith only [hs1, hk_r, hsum2]
    have hm_nn : (0 : ℝ) ≤ J.m := Nat.cast_nonneg J.m
    have hL_nn : 0 ≤ (embJH.length J : ℝ) := Nat.cast_nonneg _
    have hγ2_ge16 : 16 ≤ γ_ℓ ^ 2 := by nlinarith only [hγ_ge4]
    have hγ_le_sq : γ_ℓ + 4 ≤ γ_ℓ ^ 2 := by nlinarith only [hγ_ge4]
    have h_m1 : (J.m : ℝ) + (J.m : ℝ) * ((embJH.length J : ℝ) + 1) + (J.m : ℝ) +
          (J.m : ℝ) * (γ_ℓ + 1) =
        (J.m : ℝ) * ((embJH.length J : ℝ) + (γ_ℓ + 4)) := by ring
    have h_m2 : (embJH.length J : ℝ) + (γ_ℓ + 4) ≤ 2 * γ_ℓ ^ 2 * (embJH.length J : ℝ) := by
      have h1 : (embJH.length J : ℝ) ≤ γ_ℓ ^ 2 * (embJH.length J : ℝ) := by nlinarith only [hγ2_ge16, hL_nn]
      have h2 : γ_ℓ + 4 ≤ γ_ℓ ^ 2 * (embJH.length J : ℝ) :=
        le_trans hγ_le_sq (le_mul_of_one_le_right (le_trans (by norm_num) hγ2_ge16) hLen1)
      linarith only [h1, h2]
    have h_tot1 : (translateCost J embJH kept embJJtilde : ℝ) ≤
        (J.n : ℝ) + 2 * (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left h_m2 hm_nn
      linarith only [htr_unfold, h_m1, hmul]
    have h_tot2 : (J.n : ℝ) + 2 * (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ) ≤
        4 * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ)) := by
      have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
      have hprod_nn : 0 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ) :=
        mul_nonneg (mul_nonneg hm_nn (sq_nonneg _)) hL_nn
      linarith only [hn_nn, hprod_nn]
    have h_tot_nn : 0 ≤ 4 * ((J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ)) := by
      have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
      have hprod_nn : 0 ≤ (J.m : ℝ) * γ_ℓ ^ 2 * (embJH.length J : ℝ) :=
        mul_nonneg (mul_nonneg hm_nn (sq_nonneg _)) hL_nn
      linarith only [hn_nn, hprod_nn]
    exact le_trans (le_trans h_tot1 h_tot2) (le_mul_of_one_le_right h_tot_nn hL1)

private lemma mgraph_vcong_nonneg (J H' : MGraph) (emb : MinCostFlow.Embedding) :
    0 ≤ emb.vcong J H' (fun _ => 1) := by
  unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
  split_ifs with hne
  · exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
      (Finset.le_sup' (fun v => ∑ e ∈ J.E with v ∈ H'.walkVertices (J.tail e) (emb e), (1 : ℝ))
        hne.choose_spec)
  · exact le_rfl

private lemma sparsifyMG_vcong_le
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hembJH : embJH.IsEmbedding J H')
    {G : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hG_valid : G.IsValid) (hkept : ∀ k ∈ kept, k < J.m)
    (hG_n : G.n = J.n)
    (hG_edges : G.edges = kept.map fun k => (toCitedJ J).edges.getD k (0, 0))
    (hemb_J : IsEmbedding (toCitedJ J) G embJJtilde)
    (hemb_G : IsEmbedding G (toCitedH H' J embJH) (restrictEmb (embToCited H' J embJH) kept))
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J)
    {γ_c_cap : ℝ} (hγ_c_nn : 0 ≤ γ_c_cap)
    (hcong : vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1)
        (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) ≤
      γ_c_cap * (length (toCitedJ J) (embToCited H' J embJH) : ℝ) *
        (vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1) (embToCited H' J embJH) +
          (maxDeg (toCitedJ J) : ℝ))) :
    (MinCostFlow.Embedding.comp embJH (citedEmbToMGraph J G kept embJJtilde)).vcong
        J H' (fun _ => 1) ≤
      (γ_c_cap + 1) * (embJH.length J : ℝ) *
        (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by
  have hvc_mg := vcong_comp_mgraph_le hH' hJ hembJH hG_valid hkept hG_n hG_edges hemb_J hemb_G
  have hvc_cit := vcong_embToCited_le hH' hJ hembJH
  have hdeg_cit : (maxDeg (toCitedJ J) : ℝ) ≤ (J.maxDeg : ℝ) := Nat.cast_le.mpr (maxDeg_toCitedJ_le hJ)
  have hlen_cit : (length (toCitedJ J) (embToCited H' J embJH) : ℝ) = (embJH.length J : ℝ) := by
    exact_mod_cast length_embToCited_eq H' J embJH
  have hcong' : vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1)
      (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) ≤
      γ_c_cap * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by
    refine le_trans hcong ?_
    rw [hlen_cit]
    exact mul_le_mul_of_nonneg_left (add_le_add hvc_cit hdeg_cit)
      (mul_nonneg hγ_c_nn (Nat.cast_nonneg _))
  by_cases hEne : J.E.Nonempty
  · have hLen1 : (1 : ℝ) ≤ (embJH.length J : ℝ) := by exact_mod_cast hLen hEne
    have hvc_nn : 0 ≤ embJH.vcong J H' (fun _ => 1) := mgraph_vcong_nonneg J H' embJH
    have hsum_nn : 0 ≤ embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ) :=
      add_nonneg hvc_nn (Nat.cast_nonneg _)
    have hdeg_le : (J.maxDeg : ℝ) ≤ 1 * (embJH.length J : ℝ) *
        (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by
      have h1 : (J.maxDeg : ℝ) ≤ embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ) :=
        le_add_of_nonneg_left hvc_nn
      have h2 := le_mul_of_one_le_left hsum_nn hLen1
      linarith only [h1, h2]
    linarith only [hvc_mg, hcong', hdeg_le]
  · have hemp : J.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEne
    have hv_zero : (MinCostFlow.Embedding.comp embJH
        (citedEmbToMGraph J G kept embJJtilde)).vcong J H' (fun _ => 1) = 0 := by
      unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
      split_ifs <;> simp [hemp]
    rw [hv_zero]
    exact mul_nonneg (mul_nonneg (by linarith only [hγ_c_nn]) (Nat.cast_nonneg _))
      (add_nonneg (mgraph_vcong_nonneg J H' embJH) (Nat.cast_nonneg _))

private lemma sparsify_Jtilde_edges (tools : SpannerTools) (H' J : Graph) (embJH : ℕ → Walk) :
    (sparsify tools H' J embJH).Jtilde.edges =
      (sparsify tools H' J embJH).keptEdges.map fun j => J.edges.getD j (0, 0) := by
  dsimp only [sparsify, sparsifyLocal]

private lemma sparsifyMG_Jtilde (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    (sparsifyMG tools costs H' J embJH).Jtilde =
      outJtilde J (sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)).keptEdges :=
  rfl

private lemma sparsifyMG_emb (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    (sparsifyMG tools costs H' J embJH).emb =
      citedEmbToMGraph J
        (sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)).Jtilde
        (sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)).keptEdges
        (sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)).embJJtilde :=
  rfl

private lemma sparsifyMG_core (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ) {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J) (hembJH : embJH.IsEmbedding J H') :
    let out := sparsifyMG tools costs H' J embJH
    let γ_c := capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax + 1
    let γ_ℓ := capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax
    let K_s := 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2
    J.IsSubgraph out.Jtilde ∧
    out.emb.IsEmbedding J out.Jtilde ∧
    (MinCostFlow.Embedding.comp embJH out.emb).vcong J H' (fun _ => 1) ≤
      γ_c * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) ∧
    ((MinCostFlow.Embedding.comp embJH out.emb).length J : ℝ) ≤ γ_ℓ * (embJH.length J : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  dsimp only
  rw [sparsifyMG_Jtilde, sparsifyMG_emb]
  have hcJ_valid : (toCitedJ J).IsValid := toCitedJ_isValid hJ
  have hcEmbJH : IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) :=
    embToCited_isEmbedding hJ hembJH
  have hcJm : (toCitedJ J).m ≤ mMax := by rw [toCitedJ_m]; exact hJm
  have hcLen : 1 ≤ (toCitedJ J).m → 1 ≤ length (toCitedJ J) (embToCited H' J embJH) := by
    intro hm
    have hEne : J.E.Nonempty := Finset.card_pos.mp (by rwa [toCitedJ_m] at hm)
    have h1 := hLen hEne
    rwa [length_embToCited_eq H' J embJH]
  have ht := theorem_8_1_at_cap_with_time tools costs hdec hpds mMax
    (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
    hcJ_valid hcEmbJH hcJm hcLen
  rcases ht with ⟨hnodup, hkept_lt, hJtilde_n, hJtilde_m, hG_valid, hembJHtilde, hembJJtilde,
    hγ_c_ge, _, _, _, _, _, hcong, hJJ_len, _, hsp, _⟩
  let cOut := sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
  have hkept : ∀ k ∈ cOut.keptEdges, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_lt k hk
  have hcOut_n : cOut.Jtilde.n = J.n :=
    hJtilde_n.trans (by dsimp only [toCitedJ]; exact vertsOf_length J.V)
  have hcOut_edges : cOut.Jtilde.edges =
      cOut.keptEdges.map fun k => (toCitedJ J).edges.getD k (0, 0) :=
    sparsify_Jtilde_edges tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
  refine ⟨outJtilde_isSubgraph J cOut.keptEdges hkept,
    citedEmbToMGraph_isEmbedding hJ hkept hcOut_n hcOut_edges hembJJtilde, ?_, ?_, ?_⟩
  · exact sparsifyMG_vcong_le hH' hJ hembJH hG_valid hkept hcOut_n hcOut_edges
      hembJJtilde hembJHtilde hLen (le_trans zero_le_one hγ_c_ge) hcong
  · have hlen_mg : ((MinCostFlow.Embedding.comp embJH
        (citedEmbToMGraph J cOut.Jtilde cOut.keptEdges cOut.embJJtilde)).length J : ℝ) ≤
        (length (toCitedJ J) cOut.embJJtilde : ℝ) * (embJH.length J : ℝ) := by
      exact_mod_cast length_comp_mgraph_le hkept
        (citedEmbToMGraph_isEmbedding hJ hkept hcOut_n hcOut_edges hembJJtilde)
    exact le_trans hlen_mg (mul_le_mul_of_nonneg_right hJJ_len (Nat.cast_nonneg _))
  · have hm_eq : ((outJtilde J cOut.keptEdges).m : ℝ) = (cOut.Jtilde.m : ℝ) := by
      rw [outJtilde_m_eq J cOut.keptEdges hnodup hkept, hJtilde_m]
    have hcJn : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp only [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    rw [hm_eq, ← hcJn, ← hcJm']
    exact hsp

/-- Parametrized `DynSpanner.SparsifySpecWithTime` theorem on `MGraph` carrying explicit runtime
overhead `γ_t = capGammaQuery`, valid for arbitrary `(tools, costs)` (including fallback pruning). -/
theorem sparsifyMG_spec_with_time (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ) :
    DynSpanner.SparsifySpecWithTime mMax
      (sparsifyMGParamsWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax)
      (sparsifyMG tools costs) := by
  intro H' J embJH hH' hJ hJm hLen hembJH
  let P := sparsifyMGParamsWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax
  have hP_γc : P.γ_c = capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax + 1 := rfl
  have hP_γℓ : P.γ_ℓ = capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_Ks : P.K_s = 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 := rfl
  have hP_ps : P.p_s = 1 := rfl
  have hP_Kt : P.K_t = (costs.decompose.K_dec + 1) * costs.decompose.decFactor mMax +
      sparsifyBaseConst tools.constructExpander.c_deg costs + 4 := rfl
  have hP_γt : P.γ_t = capGammaQuery tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_pt : P.p_t = 1 := rfl
  have hcore := sparsifyMG_core tools costs hdec hpds mMax hH' hJ hJm hLen hembJH
  refine ⟨hcore.1, hcore.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hP_γc]; exact hcore.2.2.1
  · rw [hP_γℓ]; exact hcore.2.2.2.1
  · rw [hP_Ks, hP_γℓ, hP_ps, pow_one]; exact hcore.2.2.2.2
  · have hcJ_valid : (toCitedJ J).IsValid := toCitedJ_isValid hJ
    have hcEmbJH : IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) :=
      embToCited_isEmbedding hJ hembJH
    have hcJm : (toCitedJ J).m ≤ mMax := by rw [toCitedJ_m]; exact hJm
    have hcLen : 1 ≤ (toCitedJ J).m → 1 ≤ length (toCitedJ J) (embToCited H' J embJH) := by
      intro hm
      have hEne : J.E.Nonempty := Finset.card_pos.mp (by rwa [toCitedJ_m] at hm)
      have h1 := hLen hEne
      rwa [length_embToCited_eq H' J embJH]
    have ht := theorem_8_1_at_cap_with_time tools costs hdec hpds mMax
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen
    rcases ht with ⟨hnodup, hkept_lt, _, _, _, _, _, _, hγ_ℓ_ge, _, _, _, _, _, hJJ_len, _, _, hrt⟩
    let cOut := sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
    have hkept : ∀ k ∈ cOut.keptEdges, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_lt k hk
    have hcJn : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp only [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    have hlen_cit : (length (toCitedJ J) (embToCited H' J embJH) : ℝ) = (embJH.length J : ℝ) := by
      exact_mod_cast length_embToCited_eq H' J embJH
    rw [hcJn, hcJm', hlen_cit] at hrt
    have htr_le := translateCost_le hnodup hkept hJJ_len hγ_ℓ_ge hLen
    have hcost_cast : ((sparsifyMG tools costs H' J embJH).cost : ℝ) =
        (sparsifyCost tools costs (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) : ℝ) +
        (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) := by
      unfold sparsifyMG; push_cast; rfl
    have hmain_nn : 0 ≤ ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      have hL1 := one_le_one_add_log J.n J.m
      exact mul_nonneg (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)))
        (by linarith only [hL1])
    have htr_γt : (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) ≤
        4 * capGammaQuery tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (hdec.φ_lb mMax) mMax *
        ((J.n : ℝ) + (J.m : ℝ) *
          (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
            tools.pathDS (hdec.φ_lb mMax) mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      rw [← hP_γt, ← hP_γℓ]
      have ht1 : 4 ≤ 4 * P.γ_t := by linarith [P.hγ_t]
      have htr0 : (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) ≤
          4 * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
        rw [hP_γℓ]; exact htr_le
      calc (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ)
          ≤ 4 * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := htr0
        _ = 4 * (((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) := by ring
        _ ≤ (4 * P.γ_t) * (((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_right ht1 hmain_nn
        _ = 4 * P.γ_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by ring
    have hadd := add_le_add hrt htr_γt
    change (sparsifyMG tools costs H' J embJH).cost ≤
      P.K_t * P.γ_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t
    rw [hcost_cast, hP_Kt, hP_γℓ, hP_γt, hP_pt, pow_one]
    linarith only [hadd]

/-- Main `DynSpanner.SparsifySpec` theorem on `MGraph` in the `γ_query = γ_ExpPath` specialization. -/
theorem sparsifyMG_spec (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    DynSpanner.SparsifySpec mMax
      (sparsifyMGParams tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax)
      (sparsifyMG tools costs) := by
  intro H' J embJH hH' hJ hJm hLen hembJH
  let P := sparsifyMGParams tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax
  have hP_γc : P.γ_c = capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax + 1 := rfl
  have hP_γℓ : P.γ_ℓ = capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_Ks : P.K_s = 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 := rfl
  have hP_ps : P.p_s = 1 := rfl
  have hP_Kt : P.K_t = (costs.decompose.K_dec + 1) * costs.decompose.decFactor mMax +
      sparsifyBaseConst tools.constructExpander.c_deg costs + 4 := rfl
  have hP_pt : P.p_t = 1 := rfl
  have hcore := sparsifyMG_core tools costs hdec hpds mMax hH' hJ hJm hLen hembJH
  refine ⟨hcore.1, hcore.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hP_γc]; exact hcore.2.2.1
  · rw [hP_γℓ]; exact hcore.2.2.2.1
  · rw [hP_Ks, hP_γℓ, hP_ps, pow_one]; exact hcore.2.2.2.2
  · have hcJ_valid : (toCitedJ J).IsValid := toCitedJ_isValid hJ
    have hcEmbJH : IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) :=
      embToCited_isEmbedding hJ hembJH
    have hcJm : (toCitedJ J).m ≤ mMax := by rw [toCitedJ_m]; exact hJm
    have hcLen : 1 ≤ (toCitedJ J).m → 1 ≤ length (toCitedJ J) (embToCited H' J embJH) := by
      intro hm
      have hEne : J.E.Nonempty := Finset.card_pos.mp (by rwa [toCitedJ_m] at hm)
      have h1 := hLen hEne
      rwa [length_embToCited_eq H' J embJH]
    have ht := theorem_8_1_at_cap tools costs hdec hpds mMax
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen hγq
    rcases ht with ⟨hnodup, hkept_lt, _, _, _, _, _, _, hγ_ℓ_ge, _, _, _, _, hJJ_len, _, _, hrt⟩
    let cOut := sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
    have hkept : ∀ k ∈ cOut.keptEdges, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_lt k hk
    have hcJn : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp only [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    have hlen_cit : (length (toCitedJ J) (embToCited H' J embJH) : ℝ) = (embJH.length J : ℝ) := by
      exact_mod_cast length_embToCited_eq H' J embJH
    rw [hcJn, hcJm', hlen_cit] at hrt
    have htr_le := translateCost_le hnodup hkept hJJ_len hγ_ℓ_ge hLen
    have hcost_cast : ((sparsifyMG tools costs H' J embJH).cost : ℝ) =
        (sparsifyCost tools costs (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) : ℝ) +
        (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) := by
      unfold sparsifyMG; push_cast; rfl
    have hadd := add_le_add hrt htr_le
    change (sparsifyMG tools costs H' J embJH).cost ≤
      P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t
    rw [hcost_cast, hP_Kt, hP_γℓ, hP_pt, pow_one]
    linarith only [hadd]

/-- Corollary of `sparsifyMG_spec_with_time` when `decFactor mMax ≤ C_dec · γ_ℓ²`, eliminating
`decFactor mMax` from `K_t` while preserving the explicit `γ_t = capGammaQuery` overhead. -/
theorem sparsifyMG_spec_of_dec_le_with_time (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : costs.decompose.decFactor mMax ≤
      C_dec * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (hdec.φ_lb mMax) mMax) ^ 2) :
    DynSpanner.SparsifySpecWithTime mMax
      (sparsifyMGParamsOfDecWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn)
      (sparsifyMG tools costs) := by
  intro H' J embJH hH' hJ hJm hLen hembJH
  let P := sparsifyMGParamsOfDecWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn
  have hP_γc : P.γ_c = capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax + 1 := rfl
  have hP_γℓ : P.γ_ℓ = capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_Ks : P.K_s = 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 := rfl
  have hP_ps : P.p_s = 1 := rfl
  have hP_Kt : P.K_t = C_dec * (costs.decompose.K_dec + 1) +
      sparsifyBaseConst tools.constructExpander.c_deg costs + 4 := rfl
  have hP_γt : P.γ_t = capGammaQuery tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_pt : P.p_t = 1 := rfl
  have hcore := sparsifyMG_core tools costs hdec hpds mMax hH' hJ hJm hLen hembJH
  refine ⟨hcore.1, hcore.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hP_γc]; exact hcore.2.2.1
  · rw [hP_γℓ]; exact hcore.2.2.2.1
  · rw [hP_Ks, hP_γℓ, hP_ps, pow_one]; exact hcore.2.2.2.2
  · have hcJ_valid : (toCitedJ J).IsValid := toCitedJ_isValid hJ
    have hcEmbJH : IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) :=
      embToCited_isEmbedding hJ hembJH
    have hcJm : (toCitedJ J).m ≤ mMax := by rw [toCitedJ_m]; exact hJm
    have hcLen : 1 ≤ (toCitedJ J).m → 1 ≤ length (toCitedJ J) (embToCited H' J embJH) := by
      intro hm
      have hEne : J.E.Nonempty := Finset.card_pos.mp (by rwa [toCitedJ_m] at hm)
      have h1 := hLen hEne
      rwa [length_embToCited_eq H' J embJH]
    have ht := theorem_8_1_at_cap_with_time tools costs hdec hpds mMax
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen
    rcases ht with ⟨hnodup, hkept_lt, _, _, _, _, _, _, hγ_ℓ_ge, _, _, _, _, _, hJJ_len, _, _, _⟩
    have hrt := theorem_8_1_at_cap_of_dec_le_with_time tools costs hdec hpds mMax hC_nn hdec_le
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen
    let cOut := sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
    have hkept : ∀ k ∈ cOut.keptEdges, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_lt k hk
    have hcJn : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp only [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    have hlen_cit : (length (toCitedJ J) (embToCited H' J embJH) : ℝ) = (embJH.length J : ℝ) := by
      exact_mod_cast length_embToCited_eq H' J embJH
    dsimp only at hrt
    rw [hcJn, hcJm', hlen_cit] at hrt
    have htr_le := translateCost_le hnodup hkept hJJ_len hγ_ℓ_ge hLen
    have hcost_cast : ((sparsifyMG tools costs H' J embJH).cost : ℝ) =
        (sparsifyCost tools costs (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) : ℝ) +
        (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) := by
      unfold sparsifyMG; push_cast; rfl
    have hmain_nn : 0 ≤ ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      have hL1 := one_le_one_add_log J.n J.m
      exact mul_nonneg (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)))
        (by linarith only [hL1])
    have htr_γt : (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) ≤
        4 * capGammaQuery tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (hdec.φ_lb mMax) mMax *
        ((J.n : ℝ) + (J.m : ℝ) *
          (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
            tools.pathDS (hdec.φ_lb mMax) mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
      rw [← hP_γt, ← hP_γℓ]
      have ht1 : 4 ≤ 4 * P.γ_t := by linarith [P.hγ_t]
      have htr0 : (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) ≤
          4 * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
        rw [hP_γℓ]; exact htr_le
      calc (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ)
          ≤ 4 * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := htr0
        _ = 4 * (((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) := by ring
        _ ≤ (4 * P.γ_t) * (((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_right ht1 hmain_nn
        _ = 4 * P.γ_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
              (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by ring
    have hadd := add_le_add hrt htr_γt
    change (sparsifyMG tools costs H' J embJH).cost ≤
      P.K_t * P.γ_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t
    rw [hcost_cast, hP_Kt, hP_γℓ, hP_γt, hP_pt, pow_one]
    linarith only [hadd]

/-- Corollary of `sparsifyMG_spec` when `decFactor mMax ≤ C_dec · γ_ℓ²` (e.g. from Chuzhoy–Saranurak
cut-matching parameters) in the `γ_query = γ_ExpPath` specialization. -/
theorem sparsifyMG_spec_of_dec_le (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : costs.decompose.decFactor mMax ≤
      C_dec * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (hdec.φ_lb mMax) mMax) ^ 2)
    (hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M) :
    DynSpanner.SparsifySpec mMax
      (sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn)
      (sparsifyMG tools costs) := by
  intro H' J embJH hH' hJ hJm hLen hembJH
  let P := sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn
  have hP_γc : P.γ_c = capGammaC tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax + 1 := rfl
  have hP_γℓ : P.γ_ℓ = capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (hdec.φ_lb mMax) mMax := rfl
  have hP_Ks : P.K_s = 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 := rfl
  have hP_ps : P.p_s = 1 := rfl
  have hP_Kt : P.K_t = C_dec * (costs.decompose.K_dec + 1) +
      sparsifyBaseConst tools.constructExpander.c_deg costs + 4 := rfl
  have hP_pt : P.p_t = 1 := rfl
  have hcore := sparsifyMG_core tools costs hdec hpds mMax hH' hJ hJm hLen hembJH
  refine ⟨hcore.1, hcore.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hP_γc]; exact hcore.2.2.1
  · rw [hP_γℓ]; exact hcore.2.2.2.1
  · rw [hP_Ks, hP_γℓ, hP_ps, pow_one]; exact hcore.2.2.2.2
  · have hcJ_valid : (toCitedJ J).IsValid := toCitedJ_isValid hJ
    have hcEmbJH : IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) :=
      embToCited_isEmbedding hJ hembJH
    have hcJm : (toCitedJ J).m ≤ mMax := by rw [toCitedJ_m]; exact hJm
    have hcLen : 1 ≤ (toCitedJ J).m → 1 ≤ length (toCitedJ J) (embToCited H' J embJH) := by
      intro hm
      have hEne : J.E.Nonempty := Finset.card_pos.mp (by rwa [toCitedJ_m] at hm)
      have h1 := hLen hEne
      rwa [length_embToCited_eq H' J embJH]
    have ht := theorem_8_1_at_cap tools costs hdec hpds mMax
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen hγq
    rcases ht with ⟨hnodup, hkept_lt, _, _, _, _, _, _, hγ_ℓ_ge, _, _, _, _, hJJ_len, _, _, _⟩
    have hrt := theorem_8_1_at_cap_of_dec_le tools costs hdec hpds mMax hC_nn hdec_le
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
      hcJ_valid hcEmbJH hcJm hcLen hγq
    let cOut := sparsify tools (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH)
    have hkept : ∀ k ∈ cOut.keptEdges, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_lt k hk
    have hcJn : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp only [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    have hlen_cit : (length (toCitedJ J) (embToCited H' J embJH) : ℝ) = (embJH.length J : ℝ) := by
      exact_mod_cast length_embToCited_eq H' J embJH
    dsimp only at hrt
    rw [hcJn, hcJm', hlen_cit] at hrt
    have htr_le := translateCost_le hnodup hkept hJJ_len hγ_ℓ_ge hLen
    have hcost_cast : ((sparsifyMG tools costs H' J embJH).cost : ℝ) =
        (sparsifyCost tools costs (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) : ℝ) +
        (translateCost J embJH cOut.keptEdges cOut.embJJtilde : ℝ) := by
      unfold sparsifyMG; push_cast; rfl
    have hadd := add_le_add hrt htr_le
    change (sparsifyMG tools costs H' J embJH).cost ≤
      P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t
    rw [hcost_cast, hP_Kt, hP_γℓ, hP_pt, pow_one]
    linarith only [hadd]

end MinCostFlow.Spanner
