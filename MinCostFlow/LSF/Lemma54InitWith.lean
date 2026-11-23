module

public import MinCostFlow.LSF.ModelWith
public import MinCostFlow.LSF.Lemma54Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Initial Invariants for Parameterized `initLSFWith`

This file adapts `initLSF_spec` from `MinCostFlow.LSF.Lemma54Init` to `initLSFWith`, using
`lemma_B_6_factor` for an approximate congestion order (`IsApproxCongOrder` with factor `α ≥ 1`)
and explicit `(T_raw, r₀, C_reps, π, W_T, thresh)` satisfying `ValidLSFParams`.

It also proves `validLSFParams_initLSF`, showing that `initLSF`'s default choices are an instance
with `α = 1` and `K_σ = 6272 * max 1 C_lsst`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Helper lemmas for `IsCompReps` and `IsApproxCongOrder` -/

lemma isCompReps_eq_singleton_of_connected {G : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ}
    (hr₀ : r₀ ∈ G.V) (hC : IsCompReps G r₀ C_reps)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    C_reps = {r₀} := by
  have hcomp_card : (components G).card ≤ 1 := by
    have hsub : components G ⊆ {compOf G r₀} := by
      intro C hCmem
      unfold components at hCmem
      obtain ⟨w, hwV, rfl⟩ := Finset.mem_image.mp hCmem
      rw [Finset.mem_singleton]
      exact compOf_eq_of_connected (hconn w hwV r₀ hr₀)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hcard1 : C_reps.card ≤ 1 := hC.2.2.1.trans hcomp_card
  exact (Finset.card_le_one.mp hcard1 |> fun h =>
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hC.1, fun x hx => h x hx r₀ hC.1⟩)

lemma isApproxCongOrder_bridge_lt {H G T₀ : MGraph} {r₀ : ℕ} (hT₀ : IsRootedTree T₀ r₀)
    (hsub : H.V ⊆ G.V ∧ H.E ⊆ G.E ∧ ∀ e ∈ H.E, H.tail e = G.tail e ∧ H.head e = G.head e)
    (hTH : ∀ f ∈ T₀.E, f ∈ H.E → T₀.tail f = H.tail f ∧ T₀.head f = H.head f)
    (hTp : ∀ e' ∈ G.E, walkEdges (T₀.forestPath (G.tail e') (G.head e')) ⊆ H.E)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e' ∈ G.E, 0 < ℓ e')
    {α : ℝ} {π : ℕ → ℕ} (hπ : IsApproxCongOrder G T₀ ℓ α π)
    {b g : ℕ} (hbT : b ∈ T₀.E) (hbH : b ∉ H.E) (hgT : g ∈ T₀.E) (hgH : g ∈ H.E) :
    π b < π g := by
  by_contra hle
  push Not at hle
  have hle_cong : congestion G T₀ ℓ g ≤ α * congestion G T₀ ℓ b := hπ.2.2 g hgT b hbT hle
  have hb0 : congestion G T₀ ℓ b = 0 := by
    unfold congestion
    refine Finset.sum_eq_zero (fun e' he' => ?_)
    have hnot : b ∉ walkEdges (T₀.forestPath (G.tail e') (G.head e')) := fun h => hbH (hTp e' he' h)
    exact ite_eq_right_iff.mpr (fun h => absurd h hnot)
  have hg_mem_G : g ∈ G.E := hsub.2.1 hgH
  have hTG_edges : T₀.tail g = G.tail g ∧ T₀.head g = G.head g :=
    ⟨(hTH g hgT hgH).1.trans (hsub.2.2 g hgH).1, (hTH g hgT hgH).2.trans (hsub.2.2 g hgH).2⟩
  have hg_pos : 0 < congestion G T₀ ℓ g :=
    congestion_pos_of_mem hT₀ hℓ hgT hg_mem_G hTG_edges
  rw [hb0, mul_zero] at hle_cong
  exact absurd (lt_of_lt_of_le hg_pos hle_cong) (lt_irrefl 0)

/-! ## Tree and stretch properties for `initLSFWith` -/

private lemma initLSFWith_tree_nonempty {C_lsst α : ℝ} {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty) (hE : G₀.E.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {T_raw : MGraph} {r₀ : ℕ} {π : ℕ → ℕ}
    (hT_raw : IsLSST (weightedCopyGraph G₀ v) (weightedCopyLen G₀ ℓ₀) (fun _ => 1)
      (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw)
    (hr₀ : r₀ ∈ G₀.V)
    (hπ : IsApproxCongOrder (weightedCopyGraph G₀ v) (projectTree G₀ v T_raw)
      (weightedCopyLen G₀ ℓ₀) α π) :
    let T₀ := projectTree G₀ v T_raw
    let C := max 1 C_lsst
    let raw := fun e => levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e
    IsRootedTree T₀ r₀ ∧ T₀.V = G₀.V ∧
      (∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f) ∧
      (∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
      (∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g) ∧
      ∑ e ∈ G₀.E, raw e ≤
        4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      ∑ e ∈ G₀.E, v e * raw e ≤
        112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
  classical
  intro T₀ C raw
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  have hℓ_v : ∀ e' ∈ G_v.E, 0 < ℓ_v e' := fun _ he' => weightedCopyLen_pos hE hℓ₀ he'
  have hα0 : 0 ≤ α := zero_le_one.trans hπ.2.1
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hproj := projectTree_isLSST hG₀ hℓ₀ hv hT_raw
  have hST₀ : T₀.IsSpanningTreeOn G₀.V := hproj.1
  have hT₀_rt : IsRootedTree T₀ r₀ := isRootedTree_of_spanningTreeOn hST₀ hr₀
  have hTV : T₀.V = G₀.V := hST₀.2.1
  have hTG₀ := hproj.2.1
  have hTp₀ := hproj.2.2.1
  have hTpGv := hproj.2.2.2.1
  have hTpGv_orig : ∀ e' ∈ G_v.E, walkEdges (T₀.forestPath (G_v.tail e') (G_v.head e')) ⊆ G₀.E := by
    intro e' he'
    obtain ⟨hmem, htail, hhead⟩ := weightedCopyGraph_origEdge_mem hE he'
    rw [htail, hhead]
    exact hTp₀ _ hmem
  have hlsst_sum := hproj.2.2.2.2.2
  have hsubGv := weightedCopyGraph_subgraph hv
  have hpi_br : ∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g := fun b hb hbG g hg hgG =>
    isApproxCongOrder_bridge_lt hT₀_rt hsubGv hTG₀ hTpGv_orig hℓ_v hπ hb hbG hg hgG
  have hTGv_edges : ∀ f ∈ T₀.E, f ∈ G_v.E → T₀.tail f = G_v.tail f ∧ T₀.head f = G_v.head f :=
    projectTree_G_v_edges hE hv
  have hpi_art : ∀ f ∈ T₀.E \ G_v.E, ∀ g ∈ T₀.E ∩ G_v.E, π f < π g := by
    intro f hf g hg
    rw [Finset.mem_sdiff] at hf
    rw [Finset.mem_inter] at hg
    exact isApproxCongOrder_bridge_lt hT₀_rt
      ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩
      hTGv_edges hTpGv hℓ_v hπ hf.1 hf.2 hg.1 hg.2
  have hB6_Gv : ∑ e' ∈ G_v.E, raw (origEdge (copyMod G₀) e') ≤
      4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    have h_rw : ∀ e' ∈ G_v.E, raw (origEdge (copyMod G₀) e') =
        levelStretchBound T₀ r₀ π G_v ℓ_v e' := fun e' he' =>
      levelStretchBound_G0_eq_Gv hG₀ hE hT₀_rt hTV hℓ₀ hv hTG₀ hTp₀ hπ.1 hpi_br he'
    rw [Finset.sum_congr rfl h_rw]
    unfold levelStretchBound
    have hVcard : T₀.V.card = G₀.n := by rw [hTV]; rfl
    have hsum_swap : ∑ e' ∈ G_v.E, 2 * ∑ i ∈ Finset.range (hldDepthBound G₀.n + 1),
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e' =
        2 * ∑ i ∈ Finset.range (hldDepthBound G₀.n + 1), ∑ e' ∈ G_v.E,
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e' := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have h_each_i : ∀ i ∈ Finset.range (hldDepthBound G₀.n + 1),
        ∑ e' ∈ G_v.E, (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch
          G_v ℓ_v e' ≤ (1 + α) * ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := by
      intro i _
      have hBi_bf : IsBranchFree T₀ r₀ (levelRoots T₀ r₀ i) :=
        upClosure_levelRoots hT₀_rt ▸ upClosure_isBranchFree hT₀_rt levelRoots_subset
      have hBi_ne : (levelRoots T₀ r₀ i).Nonempty := ⟨r₀, root_mem_levelRoots hT₀_rt⟩
      exact lemma_B_6_factor (weightedCopyGraph_isValid hG₀ v) hT₀_rt
        (hTV.trans (weightedCopyGraph_V G₀ v).symm) hBi_bf hBi_ne hℓ_v hTpGv hα0 hpi_art hπ.2.2
    have h_range_congr : (Nat.log 2 T₀.V.card + 1) * (Nat.log 2 T₀.V.card + 2) + 1 =
        hldDepthBound G₀.n + 1 := by
      rw [hVcard]; rfl
    have hstep1 : ∑ e' ∈ G_v.E, 2 * ∑ i ∈ Finset.range ((Nat.log 2 T₀.V.card + 1) *
          (Nat.log 2 T₀.V.card + 2) + 1),
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e' ≤
        2 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
          ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := by
      simp_rw [h_range_congr]
      rw [hsum_swap]
      have hsum_le := Finset.sum_le_sum h_each_i
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
      nlinarith
    have hcard_Gv := weightedCopyGraph_card_le hv
    have hGvn_eq : G_v.n = G₀.n := by
      unfold MGraph.n; rw [weightedCopyGraph_V]
    have hlsst_C : ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' ≤
        C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      calc ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e'
          ≤ C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * (G_v.E.card : ℝ) := hlsst_sum
        _ = C_lsst * (G_v.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
        _ ≤ C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact mul_le_mul (le_max_right _ _) hcard_Gv (Nat.cast_nonneg _)
              (zero_le_one.trans (le_max_left _ _))
    calc ∑ e' ∈ G_v.E, 2 * ∑ i ∈ Finset.range ((Nat.log 2 T₀.V.card + 1) *
          (Nat.log 2 T₀.V.card + 2) + 1),
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e'
        ≤ 2 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
            ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := hstep1
      _ ≤ 2 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
            (C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hlsst_C (by positivity)
      _ = 4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
  have hsum_mult := weightedCopyGraph_sum_eq hE v raw
  rw [hsum_mult] at hB6_Gv
  have hraw_ge0 : ∀ e ∈ G₀.E, 0 ≤ raw e := fun e he => by
    dsimp only [raw]
    have hlen := levelStretchBound_ge_two hT₀_rt π G₀ (fun f _ => safeLen_nonneg hℓ₀ f)
      (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he)
    linarith
  have hunw : ∑ e ∈ G₀.E, raw e ≤
      4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    have h1le : ∑ e ∈ G₀.E, raw e ≤ ∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ) * raw e :=
      Finset.sum_le_sum (fun e he => by
        have hm1 : (1 : ℝ) ≤ (edgeMult G₀ v e : ℝ) := by exact_mod_cast edgeMult_pos hE hv he
        exact le_mul_of_one_le_left (hraw_ge0 e he) hm1)
    exact h1le.trans hB6_Gv
  have hwtd : ∑ e ∈ G₀.E, v e * raw e ≤
      112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
    have hnorm_pos : 0 < G₀.norm1 v := by
      rw [norm1_eq_sum_pos hv]
      exact Finset.sum_pos hv hE
    have hm_pos : (0 : ℝ) < (G₀.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
    have h_term : ∀ e ∈ G₀.E, v e * raw e ≤
        (G₀.norm1 v / (G₀.E.card : ℝ)) * ((edgeMult G₀ v e : ℝ) * raw e) := by
      intro e he
      have hceil : (G₀.E.card : ℝ) * v e / G₀.norm1 v ≤ (edgeMult G₀ v e : ℝ) := by
        unfold edgeMult; exact Nat.le_ceil _
      have h1 : v e ≤ (G₀.norm1 v / (G₀.E.card : ℝ)) * (edgeMult G₀ v e : ℝ) := by
        have := mul_le_mul_of_nonneg_left hceil (div_nonneg (le_of_lt hnorm_pos) (le_of_lt hm_pos))
        have hEq : (G₀.norm1 v / (G₀.E.card : ℝ)) * ((G₀.E.card : ℝ) * v e / G₀.norm1 v) = v e := by
          field_simp [ne_of_gt hnorm_pos, ne_of_gt hm_pos]
        rwa [hEq] at this
      calc v e * raw e
          ≤ ((G₀.norm1 v / (G₀.E.card : ℝ)) * (edgeMult G₀ v e : ℝ)) * raw e :=
            mul_le_mul_of_nonneg_right h1 (hraw_ge0 e he)
        _ = (G₀.norm1 v / (G₀.E.card : ℝ)) * ((edgeMult G₀ v e : ℝ) * raw e) := by ring
    have hsum1 : ∑ e ∈ G₀.E, v e * raw e ≤
        (G₀.norm1 v / (G₀.E.card : ℝ)) * (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C *
          (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
      calc ∑ e ∈ G₀.E, v e * raw e
          ≤ ∑ e ∈ G₀.E, (G₀.norm1 v / (G₀.E.card : ℝ)) * ((edgeMult G₀ v e : ℝ) * raw e) :=
            Finset.sum_le_sum h_term
        _ = (G₀.norm1 v / (G₀.E.card : ℝ)) * ∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ) * raw e := by
            rw [← Finset.mul_sum]
        _ ≤ (G₀.norm1 v / (G₀.E.card : ℝ)) * (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
              C * (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left hB6_Gv (div_nonneg (le_of_lt hnorm_pos) (le_of_lt hm_pos))
    have hEq2 : (G₀.norm1 v / (G₀.E.card : ℝ)) * (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
          C * (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) =
        4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      field_simp [ne_of_gt hm_pos]
    rw [hEq2] at hsum1
    have hD_le := hldDepthBound_add_one_le G₀.n
    have hstep2 : 4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ≤
        112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
      have h4C : 0 ≤ 4 * (1 + α) * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
        have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
        have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hC0 hnorm0) (sq_nonneg _))
      calc 4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2
          = ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
              (4 * (1 + α) * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)) := by ring
        _ ≤ (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) *
              (4 * (1 + α) * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)) :=
            mul_le_mul_of_nonneg_right hD_le h4C
        _ = 112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by ring
    exact hsum1.trans hstep2
  exact ⟨hT₀_rt, hTV, hTG₀, hTp₀, hpi_br, hunw, hwtd⟩

private lemma initLSFWith_tree_props {C_lsst α thresh K_σ : ℝ} {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e) (k : ℝ)
    {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)}
    (hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T) :
    let S₀ := initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh
    let C := max 1 C_lsst
    let rawWstr := fun e => levelStretchBound S₀.T₀ S₀.r₀ S₀.π G₀ (safeLen G₀ ℓ₀) e
    IsRootedTree S₀.T₀ S₀.r₀ ∧ S₀.T₀.V = G₀.V ∧
      (∀ f ∈ S₀.T₀.E, f ∈ G₀.E → S₀.T₀.tail f = G₀.tail f ∧ S₀.T₀.head f = G₀.head f) ∧
      (∀ e ∈ G₀.E, walkEdges (S₀.T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
      (∀ b ∈ S₀.T₀.E, b ∉ G₀.E → ∀ g ∈ S₀.T₀.E, g ∈ G₀.E → S₀.π b < S₀.π g) ∧
      ∑ e ∈ G₀.E, rawWstr e ≤
        4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      ∑ e ∈ G₀.E, v e * rawWstr e ≤
        112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
  classical
  intro S₀ C rawWstr
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  by_cases hE : G₀.E.Nonempty
  · have hT_raw : IsLSST (weightedCopyGraph G₀ v) (weightedCopyLen G₀ ℓ₀) (fun _ => 1)
        (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
      have h := hp.hT_raw
      simp only [hE, ↓reduceIte] at h
      exact h
    have hπ : IsApproxCongOrder (weightedCopyGraph G₀ v) (projectTree G₀ v T_raw)
        (weightedCopyLen G₀ ℓ₀) α π := by
      have h := hp.hπ
      simp only [hE, ↓reduceIte] at h
      exact h
    have hres := initLSFWith_tree_nonempty hG₀ hV₀ hE hℓ₀ hv hT_raw hp.hr₀ hπ
    exact hres
  · have hG₀E : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hT_raw : IsLSST G₀ (fun _ => 1) (fun _ => 1)
        (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
      have h := hp.hT_raw
      simp only [hE, ↓reduceIte] at h
      exact h
    have hT₀_eq : S₀.T₀ = T_raw := by
      change (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh).T₀ = _
      unfold initLSFWith projectTree
      dsimp only
      exact ite_eq_right_iff.mpr (fun h => absurd h hE)
    rw [hT₀_eq]
    have hT₀_rt := isRootedTree_of_spanningTreeOn hT_raw.1 hp.hr₀
    refine ⟨hT₀_rt, hT_raw.1.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ hf; rw [hG₀E] at hf; exact absurd hf (Finset.notMem_empty _)
    · intro _ he; rw [hG₀E] at he; exact absurd he (Finset.notMem_empty _)
    · intro _ _ _ _ _ hg; rw [hG₀E] at hg; exact absurd hg (Finset.notMem_empty _)
    · rw [hG₀E, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
    · rw [hG₀E, Finset.sum_empty]
      have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
      have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hα0 : 0 ≤ α := zero_le_one.trans hp.hπ.2.1
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0) hnorm0) (pow_nonneg hL_nn 4)

/-! ## Main initialization specification `initLSFWith_spec` -/

open Classical in
/-- Full specification of the initial state `initLSFWith` under `ValidLSFParams`. -/
lemma initLSFWith_spec {C_lsst α thresh K_σ : ℝ} {G₀ : MGraph}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {k : ℝ} (hk : 1 ≤ k)
    {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)}
    (hp : ValidLSFParams C_lsst α thresh K_σ G₀ ℓ₀ v k T_raw r₀ C_reps π W_T) :
    let S₀ := initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh
    let C := max 1 C_lsst
    let rawWstr := fun e => levelStretchBound S₀.T₀ S₀.r₀ S₀.π G₀ (safeLen G₀ ℓ₀) e
    S₀.G₀ = G₀ ∧ S₀.G = G₀ ∧ S₀.v = v ∧ S₀.k = k ∧
    S₀.isolatedVerts = ∅ ∧ S₀.insertedEdges = ∅ ∧ S₀.numUpdates = 0 ∧
    S₀.T_cur = S₀.T₀ ∧ S₀.origVert = id ∧
    IsRootedTree S₀.T₀ S₀.r₀ ∧ S₀.T₀.V = G₀.V ∧ S₀.r₀ ∈ S₀.R₀_base ∧ S₀.R₀_base ⊆ S₀.T₀.V ∧
    IsEdgeOrder S₀.T₀ S₀.π ∧
    (∀ f ∈ S₀.T₀.E, f ∈ G₀.E → S₀.T₀.tail f = G₀.tail f ∧ S₀.T₀.head f = G₀.head f) ∧
    (∀ e ∈ G₀.E, walkEdges (S₀.T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
    (∀ b ∈ S₀.T₀.E, b ∉ G₀.E → ∀ g ∈ S₀.T₀.E, g ∈ G₀.E → S₀.π b < S₀.π g) ∧
    G₀.IsSubgraph S₀.RF.F ∧
    (S₀.R.card : ℝ) ≤
      (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        4 * (G₀.E.card : ℝ) / k ∧
    (∀ e ∈ G₀.E, S₀.wstr e ≤ K_σ * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
    (∀ e ∈ G₀.E,
      (rawWstr e < thresh → S₀.wstr e = rawWstr e) ∧
      (thresh ≤ rawWstr e → S₀.wstr e = 1 ∧ G₀.tail e ∈ S₀.R_orig ∧ G₀.head e ∈ S₀.R_orig)) ∧
    ∑ e ∈ G₀.E, v e * S₀.wstr e ≤
      112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 ∧
    (S₀.W_init.card : ℝ) ≤
      6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        10 * (G₀.E.card : ℝ) / k ∧
    boundary S₀.W_init ⊆ S₀.R_orig ∧
    S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E ∧
    (∀ W₁ ∈ S₀.W_init, ∀ W₂ ∈ S₀.W_init, W₁ ≠ W₂ →
      Disjoint (inducedEdges S₀.RF.F W₁) (inducedEdges S₀.RF.F W₂)) ∧
    (∀ W ∈ S₀.W_init, PathConvex S₀.T₀ W ∧ W ⊆ G₀.V ∧ (pieceBoundary S₀.W_init W).card ≤ 1 ∧
      (G₀.vol (W \ S₀.R_orig) : ℝ) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
  intro S₀ C rawWstr
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hD1_pos : (0 : ℝ) < ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hT_props := initLSFWith_tree_props hG₀ hV₀ hℓ₀ hv k hp
  rcases hT_props with ⟨hT₀_rt, hTV, hTG₀, hTp₀, hpi_br, hunw_raw, hwtd_raw⟩
  have hord : IsEdgeOrder S₀.T₀ S₀.π := hp.hπ.1
  have hWD := hp.hW_T
  let E_high := G₀.E.filter (fun e => thresh ≤ rawWstr e)
  let V_high := E_high.biUnion (fun e => {G₀.tail e, G₀.head e})
  have hE_high_card : (E_high.card : ℝ) ≤
      (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := by
    have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith [half_lt_log_add_two G₀.n]
    have hL2_pos : (0 : ℝ) < (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := sq_pos_of_pos hL_pos
    have hα0 : 0 ≤ α := zero_le_one.trans hp.hπ.2.1
    have hden_pos : 0 < 4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k :=
      mul_pos (mul_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_pos hD1_pos))
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _))) hL2_pos) hk_pos
    have hth_ge : 4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k ≤ thresh := hp.hthresh.2.1
    have hraw_nn : ∀ e ∈ G₀.E, 0 ≤ rawWstr e := fun e he => by
      dsimp only [rawWstr]
      have hlen := levelStretchBound_ge_two hT₀_rt S₀.π G₀ (fun f _ => safeLen_nonneg hℓ₀ f)
        (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he)
      linarith
    have hmarkov : (E_high.card : ℝ) * thresh ≤ ∑ e ∈ G₀.E, rawWstr e := by
      calc (E_high.card : ℝ) * thresh
          = ∑ _e ∈ E_high, thresh := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e ∈ E_high, rawWstr e := Finset.sum_le_sum (fun e he => (Finset.mem_filter.mp he).2)
        _ ≤ ∑ e ∈ G₀.E, rawWstr e :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun e he _ => hraw_nn e he)
    have hprod_le : (E_high.card : ℝ) * (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 *
          C * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k) ≤
        4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 :=
      (mul_le_mul_of_nonneg_left hth_ge (Nat.cast_nonneg _)).trans (hmarkov.trans hunw_raw)
    have hrhs_eq : (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) =
        (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2) /
          (4 * (1 + α) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k) := by
      have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have h1α_pos : 0 < 1 + α := by positivity
      field_simp [ne_of_gt h1α_pos, ne_of_gt hD1_pos, ne_of_gt hC_pos, ne_of_gt hL2_pos,
        ne_of_gt hk_pos]
    rw [hrhs_eq]
    exact (le_div_iff₀ hden_pos).mpr hprod_le
  have hr₀_base : S₀.r₀ ∈ S₀.R₀_base :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hp.hC_reps.1)
  have hR₀_sub : S₀.R₀_base ⊆ S₀.T₀.V := by
    intro x hx
    change x ∈ C_reps ∪ boundary W_T ∪ V_high at hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hC | hB) | hH
    · exact hTV.symm ▸ hp.hC_reps.2.1 hC
    · rw [mem_boundary_iff] at hB
      obtain ⟨W₁, hW₁, _, _, _, hxW₁, _⟩ := hB
      exact (hWD.1 W₁ hW₁).2.1 hxW₁
    · rw [Finset.mem_biUnion] at hH
      obtain ⟨e, he, hxe⟩ := hH
      have heG₀ := (Finset.mem_filter.mp he).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      rw [hTV]
      rcases hxe with rfl | rfl
      · exact (hG₀ e heG₀).1
      · exact (hG₀ e heG₀).2
  have hBV_sub : boundary W_T ∪ V_high ⊆ S₀.T₀.V := by
    intro x hx
    apply hR₀_sub
    change x ∈ C_reps ∪ boundary W_T ∪ V_high
    rw [Finset.mem_union] at hx
    rcases hx with hB | hH
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
    · exact Finset.mem_union_right _ hH
  have hBV_card : ((boundary W_T ∪ V_high).card : ℝ) ≤
      ((boundary W_T).card : ℝ) + 2 * (E_high.card : ℝ) := by
    have h1 : (boundary W_T ∪ V_high).card ≤ (boundary W_T).card + V_high.card :=
      Finset.card_union_le _ _
    have h2 : V_high.card ≤ 2 * E_high.card := by
      calc V_high.card
          ≤ ∑ e ∈ E_high, ({G₀.tail e, G₀.head e} : Finset ℕ).card := Finset.card_biUnion_le
        _ ≤ ∑ _e ∈ E_high, 2 := Finset.sum_le_sum (fun e _ =>
            (Finset.card_insert_le _ _).trans (by simp))
        _ = 2 * E_high.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  have hD1_eq : (hldDepthBound S₀.T₀.V.card + 1 : ℕ) = hldDepthBound G₀.n + 1 := by
    rw [hTV]; rfl
  have hsum_BV : ((boundary W_T).card : ℝ) + 2 * (E_high.card : ℝ) ≤
      4 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := by
    have h1 : ((boundary W_T).card : ℝ) ≤
        2 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := hWD.2.2.2.1
    have h2 := mul_le_mul_of_nonneg_left hE_high_card zero_le_two
    calc ((boundary W_T).card : ℝ) + 2 * (E_high.card : ℝ)
        ≤ 2 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) +
            2 * ((G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ))) := add_le_add h1 h2
      _ = 4 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := by ring
  have hBV_up_le : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card : ℝ) ≤
      4 * (G₀.E.card : ℝ) / k := by
    have hnat := upClosure_union_ancestors_card_le hT₀_rt hBV_sub
    rw [hD1_eq] at hnat
    have hreal : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card : ℝ) ≤
        ((boundary W_T ∪ V_high).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right (hBV_card.trans hsum_BV) (le_of_lt hD1_pos)
    have hEq : (4 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ))) *
          ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) = 4 * (G₀.E.card : ℝ) / k := by
      field_simp [ne_of_gt hD1_pos]
    linarith [hreal, hEq]
  have hR_eq_orig : S₀.R = S₀.R_orig := by
    change S₀.R_orig ∪ ∅ = S₀.R_orig; exact Finset.union_empty _
  have hS₀R_card : (S₀.R.card : ℝ) ≤
      (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        4 * (G₀.E.card : ℝ) / k := by
    have hRo_eq : S₀.R_orig = upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
        (C_reps ∪ (boundary W_T ∪ V_high)) := by
      change upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
          (C_reps ∪ boundary W_T ∪ V_high) = _
      rw [Finset.union_assoc]
    rw [hR_eq_orig, hRo_eq]
    split_ifs with hconn
    · have hcr : C_reps = {S₀.r₀} :=
        isCompReps_eq_singleton_of_connected (hTV ▸ hT₀_rt.2) hp.hC_reps hconn
      rw [hcr, Finset.singleton_union]
      have hcard_up := upClosure_insert_root_card_le hT₀_rt hBV_sub
      rw [hD1_eq] at hcard_up
      have hprod_le : ((boundary W_T ∪ V_high).card : ℝ) *
          ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ≤ 4 * (G₀.E.card : ℝ) / k := by
        have hmul := mul_le_mul_of_nonneg_right (hBV_card.trans hsum_BV) (le_of_lt hD1_pos)
        have hEq : (4 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ))) *
              ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) = 4 * (G₀.E.card : ℝ) / k := by
          rw [div_eq_mul_inv, mul_inv, mul_assoc (4 * (G₀.E.card : ℝ)),
            inv_mul_cancel_right₀ (ne_of_gt hD1_pos), ← div_eq_mul_inv]
        exact hmul.trans_eq hEq
      have hcard_up_real : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
          (insert S₀.r₀ (boundary W_T ∪ V_high))).card : ℝ) ≤
          1 + ((boundary W_T ∪ V_high).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard_up
      exact hcard_up_real.trans (add_le_add le_rfl hprod_le)
    · have hun : (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
            (C_reps ∪ (boundary W_T ∪ V_high))).card ≤
          (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card +
            (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card := by
        have hEq : upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (C_reps ∪ (boundary W_T ∪ V_high)) =
            upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps ∪
              upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high) := by
          unfold upClosure; exact Finset.union_biUnion
        rw [hEq]
        exact Finset.card_union_le _ _
      have h1_nat : (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card ≤
          (components G₀).card * (hldDepthBound G₀.n + 1) := by
        have hsubC : C_reps ⊆ S₀.T₀.V := hTV.symm ▸ hp.hC_reps.2.1
        have h1a := upClosure_union_ancestors_card_le hT₀_rt hsubC
        rw [hD1_eq] at h1a
        exact h1a.trans (Nat.mul_le_mul_right _ hp.hC_reps.2.2.1)
      have h1_real : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card : ℝ) ≤
          ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
        have h1' : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card : ℝ) ≤
            ((components G₀).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1_nat
        have hD_le := hldDepthBound_add_one_le G₀.n
        calc ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card : ℝ)
            ≤ ((components G₀).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := h1'
          _ ≤ ((components G₀).card : ℝ) * (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
              mul_le_mul_of_nonneg_left hD_le (Nat.cast_nonneg _)
          _ = ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
      have h_nat_real : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
            (C_reps ∪ (boundary W_T ∪ V_high))).card : ℝ) ≤
          ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ C_reps).card : ℝ) +
            ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card : ℝ) := by
        exact_mod_cast hun
      exact h_nat_real.trans (add_le_add h1_real hBV_up_le)
  have hwstr_cases : ∀ e ∈ G₀.E,
      (rawWstr e < thresh → S₀.wstr e = rawWstr e) ∧
      (thresh ≤ rawWstr e → S₀.wstr e = 1 ∧ G₀.tail e ∈ S₀.R_orig ∧ G₀.head e ∈ S₀.R_orig) := by
    intro e he
    have hw_def : S₀.wstr e = if thresh ≤ rawWstr e then 1 else rawWstr e := by
      change (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh).wstr e = _
      unfold initLSFWith
      dsimp only
      exact ite_eq_left_iff.mpr (fun h => absurd he h)
    constructor
    · intro hlt
      rw [hw_def]
      exact ite_eq_right_iff.mpr (fun h => absurd h (not_le_of_gt hlt))
    · intro hge
      have hw1 : S₀.wstr e = 1 := by
        rw [hw_def]; exact ite_eq_left_iff.mpr (fun h => absurd hge h)
      have heH : e ∈ E_high := Finset.mem_filter.mpr ⟨he, hge⟩
      have ht_mem : G₀.tail e ∈ S₀.R_orig := subset_upClosure (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, heH, Finset.mem_insert_self _ _⟩))
      have hh_mem : G₀.head e ∈ S₀.R_orig := subset_upClosure (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨e, heH, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))
      exact ⟨hw1, ht_mem, hh_mem⟩
  have hwstr_le : ∀ e ∈ G₀.E, S₀.wstr e ≤ K_σ * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by
    intro e he
    have hth_le : thresh ≤ K_σ * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := hp.hthresh.2.2
    by_cases hlt : rawWstr e < thresh
    · rw [(hwstr_cases e he).1 hlt]
      exact (le_of_lt hlt).trans hth_le
    · rw [(hwstr_cases e he).2 (not_lt.mp hlt) |>.1]
      exact hp.hthresh.1.trans hth_le
  have hwstr_sum : ∑ e ∈ G₀.E, v e * S₀.wstr e ≤
      112 * (1 + α) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
    have hpoint : ∀ e ∈ G₀.E, v e * S₀.wstr e ≤ v e * rawWstr e := by
      intro e he
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hv e he))
      by_cases hlt : rawWstr e < thresh
      · rw [(hwstr_cases e he).1 hlt]
      · rw [(hwstr_cases e he).2 (not_lt.mp hlt) |>.1]
        dsimp only [rawWstr]
        exact one_le_two.trans (levelStretchBound_ge_two hT₀_rt S₀.π G₀
          (fun f _ => safeLen_nonneg hℓ₀ f) (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he))
    exact (Finset.sum_le_sum hpoint).trans hwtd_raw
  have hr₀_orig : S₀.r₀ ∈ S₀.R_orig := subset_upClosure hr₀_base
  have hR_bf : IsBranchFree S₀.T₀ S₀.r₀ S₀.R_orig := upClosure_isBranchFree hT₀_rt hR₀_sub
  have hR_ne : S₀.R_orig.Nonempty := ⟨S₀.r₀, hr₀_orig⟩
  have hBW_sub : boundary W_T ⊆ S₀.R_orig := fun x hx =>
    subset_upClosure (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have href := refinement_decomp_spec hT₀_rt hTV hR_bf hR_ne S₀.π W_T
    hWD.1 hWD.2.1 hWD.2.2.1 hBW_sub hWD.2.2.2.2.2
  have hRF_F_eq : S₀.RF.F = forestGivenRoots S₀.T₀ S₀.r₀ S₀.R_orig S₀.π := rfl
  have hF₀_sub_G₀ : G₀.IsSubgraph S₀.RF.F := by
    rw [hRF_F_eq]
    exact forestGivenRoots_isSubgraph_of_compReps hG₀ hT₀_rt hTV hTG₀ hTp₀ hpi_br hR_bf hr₀_orig
      (fun w hw => let ⟨r, hr, hc⟩ := hp.hC_reps.2.2.2 w hw;
        ⟨r, subset_upClosure (Finset.mem_union_left _ (Finset.mem_union_left _ hr)), hc⟩)
  have hW_card : (S₀.W_init.card : ℝ) ≤
      6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        10 * (G₀.E.card : ℝ) / k := by
    have h1 : (S₀.W_init.card : ℝ) ≤ (W_T.card : ℝ) + (S₀.R.card : ℝ) := by
      have hcard_nat : S₀.W_init.card ≤ W_T.card + S₀.R_orig.card := href.2.2.2.2
      rw [hR_eq_orig]
      exact_mod_cast hcard_nat
    have h2 : (W_T.card : ℝ) ≤ 6 * (G₀.E.card : ℝ) / k + 6 := hWD.2.2.2.2.1
    calc (S₀.W_init.card : ℝ)
        ≤ (W_T.card : ℝ) + (S₀.R.card : ℝ) := h1
      _ ≤ (6 * (G₀.E.card : ℝ) / k + 6) +
          ((if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            4 * (G₀.E.card : ℝ) / k) := add_le_add h2 hS₀R_card
      _ = 6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            10 * (G₀.E.card : ℝ) / k := by ring
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hT₀_rt, hTV, hr₀_base, hR₀_sub, hord,
    hTG₀, hTp₀, hpi_br, hF₀_sub_G₀, hS₀R_card, hwstr_le, hwstr_cases, hwstr_sum, hW_card,
    href.2.1.trans hBW_sub, href.2.2.1, href.2.2.2.1, href.1⟩

/-! ## Exact `initLSF` satisfies `ValidLSFParams` -/

lemma isWstrThresh_wstrThresh {C_lsst : ℝ} {n : ℕ} {k : ℝ} (hk : 1 ≤ k) :
    IsWstrThresh C_lsst 1 n k (wstrThresh C_lsst n k) (6272 * max 1 C_lsst) := by
  refine ⟨wstrThresh_ge_one C_lsst n k, ?_, wstrThresh_le hk⟩
  unfold wstrThresh
  calc 4 * (1 + 1) * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * max 1 C_lsst *
        (Real.log ((n : ℝ) + 2)) ^ 2 * k
      = 8 * ((hldDepthBound n + 1 : ℝ) ^ 2) * max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k := by
          push_cast; ring
    _ ≤ max 1 (8 * ((hldDepthBound n + 1 : ℝ) ^ 2) * max 1 C_lsst *
          (Real.log ((n : ℝ) + 2)) ^ 2 * k) := le_max_right _ _

open Classical in
lemma validLSFParams_initLSF {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {k : ℝ} (hk : 1 ≤ k) :
    let G_v := weightedCopyGraph G₀ v
    let ℓ_v := weightedCopyLen G₀ ℓ₀
    let T_raw := if G₀.E.Nonempty then oracle G_v ℓ_v (fun _ => 1)
      else oracle G₀ (fun _ => 1) (fun _ => 1)
    let T₀ := projectTree G₀ v T_raw
    let r₀ := pickRoot G₀
    let π :=
      if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
      else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
    ValidLSFParams C_lsst 1 (wstrThresh C_lsst G₀.n k) (6272 * max 1 C_lsst) G₀ ℓ₀ v k
      T_raw r₀ (compReps G₀ r₀) π (pickDecomp G₀ T₀ r₀ k) := by
  intro G_v ℓ_v T_raw T₀ r₀ π
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hr₀_mem : r₀ ∈ G₀.V := pickRoot_mem hV₀
  have hT_raw : IsLSST (if G₀.E.Nonempty then G_v else G₀)
      (if G₀.E.Nonempty then ℓ_v else fun _ => 1) (fun _ => 1)
      (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
    by_cases hE : G₀.E.Nonempty
    · simp only [hE, ↓reduceIte, T_raw]
      have hGvn : G_v.n = G₀.n := by unfold MGraph.n; rw [weightedCopyGraph_V]
      simpa only [hGvn] using hLSST G_v ℓ_v (fun _ => 1)
        (weightedCopyGraph_isValid hG₀ v) ((weightedCopyGraph_V G₀ v).symm ▸ hV₀)
        (fun _ he' => weightedCopyLen_pos hE hℓ₀ he') (fun _ _ => zero_lt_one)
    · simp only [hE, ↓reduceIte, T_raw]
      exact hLSST G₀ (fun _ => 1) (fun _ => 1) hG₀ hV₀ (fun _ _ => zero_lt_one) (fun _ _ => zero_lt_one)
  have hT₀_st : T₀.IsSpanningTreeOn G₀.V := by
    by_cases hE : G₀.E.Nonempty
    · have h1 := hT_raw
      simp only [hE, ↓reduceIte] at h1
      exact (projectTree_isLSST hG₀ hℓ₀ hv h1).1
    · have h1 := hT_raw
      simp only [hE, ↓reduceIte] at h1
      dsimp only [T₀]; unfold projectTree
      rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
      exact h1.1
  have hT₀_rt : IsRootedTree T₀ r₀ := isRootedTree_of_spanningTreeOn hT₀_st hr₀_mem
  refine ⟨hT_raw, hr₀_mem, ⟨compReps_mem hr₀_mem, compReps_subset hG₀ hr₀_mem,
    compReps_card_le G₀ r₀, fun _ hw => compReps_connected hw⟩, ?_, ?_, isWstrThresh_wstrThresh hk⟩
  · by_cases hE : G₀.E.Nonempty <;> simp only [hE, ↓reduceIte, π] <;>
      exact isApproxCongOrder_congOrder _ _ _
  · exact pickDecomp_spec hG₀ hT₀_rt hT₀_st.2.1 hV₀ hk_pos

end MinCostFlow.LSF
