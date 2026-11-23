module

public import MinCostFlow.LSF.Lemma54InitBase
public import MinCostFlow.LSF.SafePaths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Initialization Specification for Lemma 5.4 (`initLSF_spec`)

This file proves the initial guarantees for `initLSF oracle C_lsst G₀ ℓ₀ v k`:
* Dynamic graph validity (`applyUpdate_isValid`, `applyBatch_isValid`, `BatchesIsValid`).
* Upward closure cardinality bounds in `T_H = hldAuxTree T₀ r₀` (`upClosure_insert_card_le`,
  `upClosure_insert_root_union_card_le`).
* Equivalence between forest/level stretches on `(G₀, safeLen G₀ ℓ₀)` and `(G_v, ℓ_v)` using
  `no_bridge_in_endpoint_path` and `congOrder_bridge_lt`.
* Weighted stretch sum (`Item 3`), Markov bound on high-stretch edges `E_high`, initial root
  count `R_orig.card ≤ 1 + 4 * m / k` (`Item 1`), and decomposition refinement guarantees (`Item 4`).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Initialization specification (`initLSF_spec`) -/

private lemma initLSF_tree_nonempty {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) (hE : G₀.E.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e) :
    let G_v := weightedCopyGraph G₀ v
    let ℓ_v := weightedCopyLen G₀ ℓ₀
    let T₀ := projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1))
    let r₀ := pickRoot G₀
    let π := congOrder T₀ (congestion G_v T₀ ℓ_v)
    let C := max 1 C_lsst
    let raw := fun e => levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e
    IsRootedTree T₀ r₀ ∧ T₀.V = G₀.V ∧
      (∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f) ∧
      (∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
      (∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g) ∧
      ∑ e ∈ G₀.E, raw e ≤
        8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      ∑ e ∈ G₀.E, v e * raw e ≤ 224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
  classical
  intro G_v ℓ_v T₀ r₀ π C raw
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hCL : C_lsst ≤ C := le_max_right _ _
  have hr₀_G₀ : r₀ ∈ G₀.V := pickRoot_mem hV₀
  have hT_raw_lsst : IsLSST G_v ℓ_v (fun _ => 1)
      (C_lsst * (Real.log ((G_v.n : ℝ) + 2)) ^ 2) (oracle G_v ℓ_v (fun _ => 1)) :=
    hLSST G_v ℓ_v (fun _ => 1) (weightedCopyGraph_isValid hG₀ v)
      ((weightedCopyGraph_V G₀ v).symm ▸ hV₀) (fun _ he' => weightedCopyLen_pos (v := v) hE hℓ₀ he')
      (fun _ _ => zero_lt_one)
  have hproj := projectTree_isLSST hG₀ hℓ₀ hv hT_raw_lsst
  have hST₀ : T₀.IsSpanningTreeOn G₀.V := hproj.1
  have hT₀_rt : IsRootedTree T₀ r₀ := isRootedTree_of_spanningTreeOn hST₀ hr₀_G₀
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
    congOrder_bridge_lt hT₀_rt hsubGv hTG₀ hTpGv_orig (fun _ he' => weightedCopyLen_pos (v := v) hE hℓ₀ he')
      hb hbG hg hgG
  have hB6_Gv : ∑ e' ∈ G_v.E, raw (origEdge (copyMod G₀) e') ≤
      8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    have h_rw : ∀ e' ∈ G_v.E, raw (origEdge (copyMod G₀) e') =
        levelStretchBound T₀ r₀ π G_v ℓ_v e' := fun e' he' =>
      levelStretchBound_G0_eq_Gv hG₀ hE hT₀_rt hTV hℓ₀ hv hTG₀ hTp₀
        (congOrder_isEdgeOrder _ _) hpi_br he'
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
          G_v ℓ_v e' ≤ 2 * ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := by
      intro i _
      have hBi_bf : IsBranchFree T₀ r₀ (levelRoots T₀ r₀ i) :=
        upClosure_levelRoots hT₀_rt ▸ upClosure_isBranchFree hT₀_rt levelRoots_subset
      have hBi_ne : (levelRoots T₀ r₀ i).Nonempty := ⟨r₀, root_mem_levelRoots hT₀_rt⟩
      have hTGv_edges : ∀ f ∈ T₀.E, f ∈ G_v.E → T₀.tail f = G_v.tail f ∧ T₀.head f = G_v.head f :=
        projectTree_G_v_edges hE hv
      exact lemma_B_6 (weightedCopyGraph_isValid hG₀ v) hT₀_rt
        (hTV.trans (weightedCopyGraph_V G₀ v).symm) hBi_bf hBi_ne
        (fun _ he' => weightedCopyLen_pos (v := v) hE hℓ₀ he') hTGv_edges hTpGv
        (congOrder_isEdgeOrder _ _) (congOrder_isSortedByCong _ _)
    have h_range_congr : (Nat.log 2 T₀.V.card + 1) * (Nat.log 2 T₀.V.card + 2) + 1 =
        hldDepthBound G₀.n + 1 := by
      rw [hVcard]; rfl
    have hstep1 : ∑ e' ∈ G_v.E, 2 * ∑ i ∈ Finset.range ((Nat.log 2 T₀.V.card + 1) *
          (Nat.log 2 T₀.V.card + 2) + 1),
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e' ≤
        4 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := by
      simp_rw [h_range_congr]
      rw [hsum_swap]
      have hsum_le := Finset.sum_le_sum h_each_i
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
      linarith
    have hcard_Gv := weightedCopyGraph_card_le hv
    have hGvn_eq : G_v.n = G₀.n := by
      unfold MGraph.n; rw [weightedCopyGraph_V]
    have hlsst_C : ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' ≤
        C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      rw [hGvn_eq] at hlsst_sum
      calc ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e'
          ≤ C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * (G_v.E.card : ℝ) := hlsst_sum
        _ = C_lsst * (G_v.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
        _ ≤ C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
            have h1 : C_lsst * (G_v.E.card : ℝ) ≤ C * (2 * (G₀.E.card : ℝ)) :=
              mul_le_mul hCL hcard_Gv (Nat.cast_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    calc ∑ e' ∈ G_v.E, (2 * ∑ i ∈ Finset.range ((Nat.log 2 T₀.V.card + 1) *
          (Nat.log 2 T₀.V.card + 2) + 1),
          (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G_v ℓ_v e')
        ≤ 4 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * ∑ e' ∈ G_v.E, treeStretch G_v T₀ ℓ_v e' := hstep1
      _ ≤ 4 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
            (C * (2 * (G₀.E.card : ℝ)) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hlsst_C (by positivity)
      _ = 8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
  have hsum_mult := weightedCopyGraph_sum_eq hE v raw
  rw [hsum_mult] at hB6_Gv
  have hraw_ge0 : ∀ e ∈ G₀.E, 0 ≤ raw e := fun e he => by
    dsimp only [raw]
    have hlen := levelStretchBound_ge_two hT₀_rt π G₀ (fun f _ => safeLen_nonneg hℓ₀ f)
      (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he)
    linarith
  have hunw : ∑ e ∈ G₀.E, raw e ≤
      8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    have h1le : ∑ e ∈ G₀.E, raw e ≤ ∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ) * raw e :=
      Finset.sum_le_sum (fun e he => by
        have hm1 : (1 : ℝ) ≤ (edgeMult G₀ v e : ℝ) := by exact_mod_cast edgeMult_pos hE hv he
        exact le_mul_of_one_le_left (hraw_ge0 e he) hm1)
    exact h1le.trans hB6_Gv
  have hwtd : ∑ e ∈ G₀.E, v e * raw e ≤
      224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
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
        (G₀.norm1 v / (G₀.E.card : ℝ)) * (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C *
          (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
      calc ∑ e ∈ G₀.E, v e * raw e
          ≤ ∑ e ∈ G₀.E, (G₀.norm1 v / (G₀.E.card : ℝ)) * ((edgeMult G₀ v e : ℝ) * raw e) :=
            Finset.sum_le_sum h_term
        _ = (G₀.norm1 v / (G₀.E.card : ℝ)) * ∑ e ∈ G₀.E, (edgeMult G₀ v e : ℝ) * raw e := by
            rw [← Finset.mul_sum]
        _ ≤ (G₀.norm1 v / (G₀.E.card : ℝ)) * (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C *
              (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left hB6_Gv (div_nonneg (le_of_lt hnorm_pos) (le_of_lt hm_pos))
    have hEq2 : (G₀.norm1 v / (G₀.E.card : ℝ)) * (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C *
          (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) =
        8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
      field_simp [ne_of_gt hm_pos]
    rw [hEq2] at hsum1
    have hD_le := hldDepthBound_add_one_le G₀.n
    have hstep2 : 8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ≤
        224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
      have h8C : 0 ≤ 8 * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
        have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
        have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hC0 hnorm0) (sq_nonneg _))
      calc 8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2
          = ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) *
              (8 * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)) := by ring
        _ ≤ (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) *
              (8 * (C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)) :=
            mul_le_mul_of_nonneg_right hD_le h8C
        _ = 224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by ring
    exact hsum1.trans hstep2
  exact ⟨hT₀_rt, hTV, hTG₀, hTp₀, hpi_br, hunw, hwtd⟩

private lemma initLSF_tree_props {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e) (k : ℝ) :
    let S₀ := initLSF oracle C_lsst G₀ ℓ₀ v k
    let C := max 1 C_lsst
    let rawWstr := fun e => levelStretchBound S₀.T₀ S₀.r₀ S₀.π G₀ (safeLen G₀ ℓ₀) e
    IsRootedTree S₀.T₀ S₀.r₀ ∧ S₀.T₀.V = G₀.V ∧
      (∀ f ∈ S₀.T₀.E, f ∈ G₀.E → S₀.T₀.tail f = G₀.tail f ∧ S₀.T₀.head f = G₀.head f) ∧
      (∀ e ∈ G₀.E, walkEdges (S₀.T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
      (∀ b ∈ S₀.T₀.E, b ∉ G₀.E → ∀ g ∈ S₀.T₀.E, g ∈ G₀.E → S₀.π b < S₀.π g) ∧
      ∑ e ∈ G₀.E, rawWstr e ≤
        8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * C * (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      ∑ e ∈ G₀.E, v e * rawWstr e ≤ 224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
  classical
  intro S₀ C rawWstr
  have hL := half_lt_log_add_two G₀.n
  have hL_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hr₀_G₀ : S₀.r₀ ∈ G₀.V := pickRoot_mem hV₀
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  by_cases hE : G₀.E.Nonempty
  · have hT₀_eq : S₀.T₀ = projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1)) := by
      change (initLSF oracle C_lsst G₀ ℓ₀ v k).T₀ = _
      unfold initLSF; dsimp only
      rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
    have hr₀_eq : S₀.r₀ = pickRoot G₀ := rfl
    have hπ_eq : S₀.π = congOrder (projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1)))
        (congestion G_v (projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1))) ℓ_v) := by
      change (initLSF oracle C_lsst G₀ ℓ₀ v k).π = _
      unfold initLSF; dsimp only
      simp only [hE, ↓reduceIte]
      rfl
    have hres := initLSF_tree_nonempty hLSST hG₀ hV₀ hE hℓ₀ hv
    have hraw_eq : rawWstr = fun e => levelStretchBound (projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1)))
        (pickRoot G₀) (congOrder (projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1)))
          (congestion G_v (projectTree G₀ v (oracle G_v ℓ_v (fun _ => 1))) ℓ_v)) G₀ (safeLen G₀ ℓ₀) e := by
      funext e; dsimp only [rawWstr]; rw [hT₀_eq, hr₀_eq, hπ_eq]
    rw [hT₀_eq, hr₀_eq, hπ_eq, hraw_eq]
    exact hres
  · have hG₀E : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hT_raw_lsst : IsLSST G₀ (fun _ => 1) (fun _ => 1)
        (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) (oracle G₀ (fun _ => 1) (fun _ => 1)) :=
      hLSST G₀ (fun _ => 1) (fun _ => 1) hG₀ hV₀ (fun _ _ => zero_lt_one) (fun _ _ => zero_lt_one)
    have hT₀_eq : S₀.T₀ = oracle G₀ (fun _ => 1) (fun _ => 1) := by
      change (initLSF oracle C_lsst G₀ ℓ₀ v k).T₀ = _
      unfold initLSF
      dsimp only
      rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
      unfold projectTree
      rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
    rw [hT₀_eq]
    have hT₀_rt := isRootedTree_of_spanningTreeOn hT_raw_lsst.1 hr₀_G₀
    refine ⟨hT₀_rt, hT_raw_lsst.1.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ hf; rw [hG₀E] at hf; exact absurd hf (Finset.notMem_empty _)
    · intro _ he; rw [hG₀E] at he; exact absurd he (Finset.notMem_empty _)
    · intro _ _ _ _ _ hg; rw [hG₀E] at hg; exact absurd hg (Finset.notMem_empty _)
    · rw [hG₀E, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
    · rw [hG₀E, Finset.sum_empty]
      have hC0 : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
      have hnorm0 : 0 ≤ G₀.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0) hnorm0) (pow_nonneg hL_nn 4)

open Classical in
/-- Full specification of the initial state `initLSF oracle C_lsst G₀ ℓ₀ v k`. -/
lemma initLSF_spec {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    {k : ℝ} (hk : 1 ≤ k) :
    let S₀ := initLSF oracle C_lsst G₀ ℓ₀ v k
    let C := max 1 C_lsst
    let rawWstr := fun e => levelStretchBound S₀.T₀ S₀.r₀ S₀.π G₀ (safeLen G₀ ℓ₀) e
    let thresh := wstrThresh C_lsst G₀.n k
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
    (∀ e ∈ G₀.E, S₀.wstr e ≤ 6272 * C * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
    (∀ e ∈ G₀.E,
      (rawWstr e < thresh → S₀.wstr e = rawWstr e) ∧
      (thresh ≤ rawWstr e → S₀.wstr e = 1 ∧ G₀.tail e ∈ S₀.R_orig ∧ G₀.head e ∈ S₀.R_orig)) ∧
    ∑ e ∈ G₀.E, v e * S₀.wstr e ≤ 224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 ∧
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
  classical
  intro S₀ C rawWstr thresh
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hD1_pos : (0 : ℝ) < ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hT_props := initLSF_tree_props hLSST hG₀ hV₀ hℓ₀ hv k
  rcases hT_props with ⟨hT₀_rt, hTV, hTG₀, hTp₀, hpi_br, hunw_raw, hwtd_raw⟩
  have hord : IsEdgeOrder S₀.T₀ S₀.π := by
    change IsEdgeOrder (initLSF oracle C_lsst G₀ ℓ₀ v k).T₀ (initLSF oracle C_lsst G₀ ℓ₀ v k).π
    unfold initLSF
    dsimp only
    split_ifs <;> exact congOrder_isEdgeOrder _ _
  let E_high := G₀.E.filter (fun e => thresh ≤ rawWstr e)
  let W_T := pickDecomp G₀ S₀.T₀ S₀.r₀ k
  let V_high := E_high.biUnion (fun e => {G₀.tail e, G₀.head e})
  have hE_high_card : (E_high.card : ℝ) ≤ (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := by
    have hD1 : (0 : ℝ) < ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := hD1_pos
    have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith [half_lt_log_add_two G₀.n]
    have hL2_pos : (0 : ℝ) < (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := sq_pos_of_pos hL_pos
    have hden_pos : 0 < 8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k :=
      mul_pos (mul_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_pos hD1))
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _))) hL2_pos) hk_pos
    have hth_ge : 8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k ≤ thresh := by
      dsimp only [thresh, C]; unfold wstrThresh
      simpa only [Nat.cast_add, Nat.cast_one] using le_max_right (1 : ℝ) _
    have hraw_nn : ∀ e ∈ G₀.E, 0 ≤ rawWstr e := fun e he => by
      dsimp only [rawWstr]
      exact zero_le_two.trans (levelStretchBound_ge_two hT₀_rt S₀.π G₀
        (fun f _ => safeLen_nonneg hℓ₀ f) (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he))
    have hsum1 : (E_high.card : ℝ) * (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
        (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k) ≤ ∑ e ∈ E_high, rawWstr e := by
      calc (E_high.card : ℝ) * (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * C *
            (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k)
          ≤ (E_high.card : ℝ) * thresh := mul_le_mul_of_nonneg_left hth_ge (Nat.cast_nonneg _)
        _ = ∑ _e ∈ E_high, thresh := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e ∈ E_high, rawWstr e :=
            Finset.sum_le_sum (fun e he => (Finset.mem_filter.mp he).2)
    have hsum2 : ∑ e ∈ E_high, rawWstr e ≤ ∑ e ∈ G₀.E, rawWstr e :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun e he _ => hraw_nn e he)
    have hsum3 := (hsum1.trans hsum2).trans hunw_raw
    have hdiv := (le_div_iff₀ hden_pos).mpr hsum3
    have hC_pos : (0 : ℝ) < max 1 C_lsst := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hEq : (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * max 1 C_lsst * (G₀.E.card : ℝ) *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2) /
        (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * max 1 C_lsst *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k) =
        (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hD1, ne_of_gt hL_pos, ne_of_gt hk_pos, ne_of_gt hC_pos]
    change (E_high.card : ℝ) ≤ (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) * max 1 C_lsst *
        (G₀.E.card : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) /
        (8 * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) ^ 2 * max 1 C_lsst *
          (Real.log ((G₀.n : ℝ) + 2)) ^ 2 * k) at hdiv
    rwa [hEq] at hdiv
  have hWD := pickDecomp_spec hG₀ hT₀_rt hTV hV₀ hk_pos
  have hR₀_sub : S₀.R₀_base ⊆ S₀.T₀.V := by
    change S₀.R₀_init ⊆ S₀.T₀.V
    intro x hx
    change x ∈ compReps G₀ S₀.r₀ ∪ boundary W_T ∪ V_high at hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hC | hB) | hH
    · exact hTV.symm ▸ compReps_subset hG₀ (hTV ▸ hT₀_rt.2) hC
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
    change x ∈ compReps G₀ S₀.r₀ ∪ boundary W_T ∪ V_high
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
        (compReps G₀ S₀.r₀ ∪ (boundary W_T ∪ V_high)) := by
      change upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
          (compReps G₀ S₀.r₀ ∪ boundary W_T ∪ V_high) = _
      rw [Finset.union_assoc]
    rw [hR_eq_orig, hRo_eq]
    split_ifs with hconn
    · have hcr : compReps G₀ S₀.r₀ = {S₀.r₀} :=
        compReps_eq_singleton_of_connected (hTV ▸ hT₀_rt.2) hconn
      rw [hcr, Finset.singleton_union]
      have hcard_up := upClosure_insert_root_card_le hT₀_rt hBV_sub
      rw [hD1_eq] at hcard_up
      have h_real : (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
            (insert S₀.r₀ (boundary W_T ∪ V_high))).card ≤
          (1 : ℝ) + ((boundary W_T ∪ V_high).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard_up
      have hmul := mul_le_mul_of_nonneg_right (hBV_card.trans hsum_BV) (le_of_lt hD1_pos)
      have hEq : (4 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ))) *
            ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) = 4 * (G₀.E.card : ℝ) / k := by
        field_simp [ne_of_gt hD1_pos]
      linarith [h_real, hEq]
    · have hun : (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
            (compReps G₀ S₀.r₀ ∪ (boundary W_T ∪ V_high))).card ≤
          (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀)).card +
            (upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card := by
        have hEq : upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
              (compReps G₀ S₀.r₀ ∪ (boundary W_T ∪ V_high)) =
            upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀) ∪
              upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high) := by
          unfold upClosure; exact Finset.union_biUnion
        rw [hEq]; exact Finset.card_union_le _ _
      have hcomp_sub : compReps G₀ S₀.r₀ ⊆ S₀.T₀.V :=
        hTV.symm ▸ compReps_subset hG₀ (hTV ▸ hT₀_rt.2)
      have h1_nat := (upClosure_union_ancestors_card_le hT₀_rt hcomp_sub).trans
        (Nat.mul_le_mul_right _ (compReps_card_le G₀ S₀.r₀))
      rw [hD1_eq] at h1_nat
      have h1_real : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀)).card : ℝ) ≤
          ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
        have h1' : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀)).card : ℝ) ≤
            ((components G₀).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1_nat
        have hD_le := hldDepthBound_add_one_le G₀.n
        calc ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀)).card : ℝ)
            ≤ ((components G₀).card : ℝ) * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := h1'
          _ ≤ ((components G₀).card : ℝ) * (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
              mul_le_mul_of_nonneg_left hD_le (Nat.cast_nonneg _)
          _ = ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
      have h_nat_real : ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀
            (compReps G₀ S₀.r₀ ∪ (boundary W_T ∪ V_high))).card : ℝ) ≤
          ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (compReps G₀ S₀.r₀)).card : ℝ) +
            ((upClosure (hldAuxTree S₀.T₀ S₀.r₀) S₀.r₀ (boundary W_T ∪ V_high)).card : ℝ) := by
        exact_mod_cast hun
      exact h_nat_real.trans (add_le_add h1_real hBV_up_le)
  have hwstr_cases : ∀ e ∈ G₀.E,
      (rawWstr e < thresh → S₀.wstr e = rawWstr e) ∧
      (thresh ≤ rawWstr e → S₀.wstr e = 1 ∧ G₀.tail e ∈ S₀.R_orig ∧ G₀.head e ∈ S₀.R_orig) := by
    intro e he
    have hw_def : S₀.wstr e = if thresh ≤ rawWstr e then 1 else rawWstr e := by
      change (initLSF oracle C_lsst G₀ ℓ₀ v k).wstr e = _
      unfold initLSF
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
  have hwstr_le : ∀ e ∈ G₀.E, S₀.wstr e ≤ 6272 * C * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by
    intro e he
    have hth_le : thresh ≤ 6272 * C * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 :=
      wstrThresh_le hk
    by_cases hlt : rawWstr e < thresh
    · rw [(hwstr_cases e he).1 hlt]
      exact (le_of_lt hlt).trans hth_le
    · rw [(hwstr_cases e he).2 (not_lt.mp hlt) |>.1]
      exact (wstrThresh_ge_one C_lsst G₀.n k).trans hth_le
  have hwstr_sum : ∑ e ∈ G₀.E, v e * S₀.wstr e ≤
      224 * C * G₀.norm1 v * (Real.log ((G₀.n : ℝ) + 2)) ^ 4 := by
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
  have hr₀_orig : S₀.r₀ ∈ S₀.R_orig :=
    subset_upClosure (Finset.mem_union_left _ (Finset.mem_union_left _
      (compReps_mem (hTV ▸ hT₀_rt.2))))
  have hR_bf : IsBranchFree S₀.T₀ S₀.r₀ S₀.R_orig := upClosure_isBranchFree hT₀_rt hR₀_sub
  have hR_ne : S₀.R_orig.Nonempty := ⟨S₀.r₀, hr₀_orig⟩
  have hBW_sub : boundary W_T ⊆ S₀.R_orig := fun x hx =>
    subset_upClosure (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have href := refinement_decomp_spec hT₀_rt hTV hR_bf hR_ne S₀.π W_T
    hWD.1 hWD.2.1 hWD.2.2.1 hBW_sub hWD.2.2.2.2.2
  have hW_init_eq : S₀.W_init = refineDecomp W_T (forestGivenRoots S₀.T₀ S₀.r₀ S₀.R_orig S₀.π) := rfl
  have hRF_F_eq : S₀.RF.F = forestGivenRoots S₀.T₀ S₀.r₀ S₀.R_orig S₀.π := rfl
  have hF₀_sub_G₀ : G₀.IsSubgraph S₀.RF.F := by
    rw [hRF_F_eq]
    exact forestGivenRoots_isSubgraph_of_compReps hG₀ hT₀_rt hTV hTG₀ hTp₀ hpi_br hR_bf hr₀_orig
      (fun w hw => let ⟨r, hr, hc⟩ := compReps_connected hw;
        ⟨r, subset_upClosure (Finset.mem_union_left _ (Finset.mem_union_left _ hr)), hc⟩)
  have hW_card : (S₀.W_init.card : ℝ) ≤
      6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
        10 * (G₀.E.card : ℝ) / k := by
    have h1 : (S₀.W_init.card : ℝ) ≤ (W_T.card : ℝ) + (S₀.R.card : ℝ) := by
      rw [hR_eq_orig]
      exact_mod_cast href.2.2.2.2
    have hWT_le : (W_T.card : ℝ) ≤ 6 * (G₀.E.card : ℝ) / k + 6 := hWD.2.2.2.2.1
    calc (S₀.W_init.card : ℝ)
        ≤ (W_T.card : ℝ) + (S₀.R.card : ℝ) := h1
      _ ≤ (6 * (G₀.E.card : ℝ) / k + 6) +
          ((if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            4 * (G₀.E.card : ℝ) / k) := add_le_add hWT_le hS₀R_card
      _ = 6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
            else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
            10 * (G₀.E.card : ℝ) / k := by ring
  have hb_W : boundary S₀.W_init ⊆ S₀.R_orig := by
    rw [hW_init_eq]
    exact href.2.1.trans hBW_sub
  have hcov_W : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E := by
    rw [hW_init_eq, hRF_F_eq]
    exact href.2.2.1
  have hdisj_W : ∀ W₁ ∈ S₀.W_init, ∀ W₂ ∈ S₀.W_init, W₁ ≠ W₂ →
      Disjoint (inducedEdges S₀.RF.F W₁) (inducedEdges S₀.RF.F W₂) := by
    rw [hW_init_eq, hRF_F_eq]
    exact href.2.2.2.1
  have hprops_W : ∀ W ∈ S₀.W_init, PathConvex S₀.T₀ W ∧ W ⊆ G₀.V ∧
      (pieceBoundary S₀.W_init W).card ≤ 1 ∧
      (G₀.vol (W \ S₀.R_orig) : ℝ) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    rw [hW_init_eq]
    exact href.1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hT₀_rt, hTV,
    Finset.mem_union_left _ (Finset.mem_union_left _ (compReps_mem (hTV ▸ hT₀_rt.2))),
    hR₀_sub, hord, hTG₀, hTp₀, hpi_br, hF₀_sub_G₀, hS₀R_card, hwstr_le, hwstr_cases,
    hwstr_sum, hW_card, hb_W, hcov_W, hdisj_W, hprops_W⟩

end MinCostFlow.LSF
