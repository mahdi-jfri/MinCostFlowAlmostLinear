module

public import MinCostFlow.LSF.Model
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log Bounds, Bridge-Free Endpoint Paths, and Decomposition Refinement (Lemma 5.4)

This file provides the analytic and structural helper lemmas for `lemma_5_4` and `lemma_5_5`:

1. Numeric bounds comparing `Nat.log 2 n`, `hldDepthBound n`, and `wstrThresh` to powers of
   `Real.log (n + 2)` (`half_lt_log_add_two`, `hldDepthBound_add_one_le`, `wstrThresh_le`).
2. Bridge-avoidance (`no_bridge_in_endpoint_path`): when `π` orders all bridge edges outside
   `H = G₀.E` before all edges inside `H` (as `congOrder T₀ (congestion G_v T₀ ℓ_v)` does),
   for every edge `(u, v)` whose `T₀`-path lies in `H`, the path `T₀[u, RF.root u]` used by
   `RF.stretch` never leaves `H` whenever `RF.root u ≠ RF.root v ∨ v ∈ R`.
3. `refinement_decomp_spec`: properties of `refineDecomp W_T F₀` (`|∂W| ≤ 1`,
   `G₀.vol (W \ R) ≤ 80 * k * (hldDepthBound G₀.n + 1)`, `𝒲.card ≤ W_T.card + R.card`).
4. Forest and degree stability under dynamic updates (`addVerts_isForest`, `deg_le_of_update`).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Log and depth bounds -/

lemma half_lt_log_add_two (n : ℕ) : (1 / 2 : ℝ) < Real.log ((n : ℝ) + 2) := by
  have h2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hle : (2 : ℝ) ≤ (n : ℝ) + 2 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact lt_of_lt_of_le h2 (Real.log_le_log (by norm_num) hle)

lemma nat_log_two_le (n : ℕ) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log ((n : ℝ) + 2) := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.log_zero_right, Nat.cast_zero]
    have hlog2_pos : (0 : ℝ) < Real.log (0 + 2) := Real.log_pos (by norm_num)
    linarith
  · have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hn
    have hn2 : (n : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n) (hpow.trans hn2)
    rw [Real.log_pow] at hlog
    have h2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hnonneg : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
    have hmul : (Nat.log 2 n : ℝ) * (1 / 2 : ℝ) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt h2) hnonneg
    linarith

lemma hldDepthBound_add_one_le (n : ℕ) :
    ((hldDepthBound n + 1 : ℕ) : ℝ) ≤ 28 * (Real.log ((n : ℝ) + 2)) ^ 2 := by
  have hL : 1 ≤ 2 * Real.log ((n : ℝ) + 2) := by linarith [half_lt_log_add_two n]
  have hlog_nn : 0 ≤ Real.log ((n : ℝ) + 2) := by linarith
  have hnl := nat_log_two_le n
  have h1 : (Nat.log 2 n : ℝ) + 1 ≤ 4 * Real.log ((n : ℝ) + 2) := by linarith
  have h2 : (Nat.log 2 n : ℝ) + 2 ≤ 6 * Real.log ((n : ℝ) + 2) := by linarith
  have hprod : ((Nat.log 2 n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 2) ≤
      (4 * Real.log ((n : ℝ) + 2)) * (6 * Real.log ((n : ℝ) + 2)) :=
    mul_le_mul h1 h2 (by positivity) (by linarith)
  have h24 : (hldDepthBound n : ℝ) ≤ 24 * (Real.log ((n : ℝ) + 2)) ^ 2 := by
    unfold hldDepthBound
    push_cast
    linarith [show (4 * Real.log ((n : ℝ) + 2)) * (6 * Real.log ((n : ℝ) + 2)) =
      24 * (Real.log ((n : ℝ) + 2)) ^ 2 by ring]
  have hL2 : 1 ≤ 4 * (Real.log ((n : ℝ) + 2)) ^ 2 := by nlinarith
  push_cast
  linarith

lemma wstrThresh_ge_one (C_lsst : ℝ) (n : ℕ) (k : ℝ) :
    1 ≤ wstrThresh C_lsst n k :=
  le_max_left _ _

lemma wstrThresh_le {C_lsst : ℝ} {n : ℕ} {k : ℝ} (hk : 1 ≤ k) :
    wstrThresh C_lsst n k ≤ 6272 * max 1 C_lsst * k * (Real.log ((n : ℝ) + 2)) ^ 6 := by
  have hL := half_lt_log_add_two n
  have hL2 : 1 ≤ 4 * (Real.log ((n : ℝ) + 2)) ^ 2 := by nlinarith
  have hL6 : 1 ≤ 64 * (Real.log ((n : ℝ) + 2)) ^ 6 := by
    have : 64 * (Real.log ((n : ℝ) + 2)) ^ 6 = (4 * (Real.log ((n : ℝ) + 2)) ^ 2) ^ 3 := by ring
    rw [this]; exact one_le_pow₀ hL2
  have hC : 1 ≤ max 1 C_lsst := le_max_left _ _
  have hD := hldDepthBound_add_one_le n
  have hD2 : ((hldDepthBound n : ℝ) + 1) ^ 2 ≤ (28 * (Real.log ((n : ℝ) + 2)) ^ 2) ^ 2 := by
    have hD' : (hldDepthBound n : ℝ) + 1 ≤ 28 * (Real.log ((n : ℝ) + 2)) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hD
    nlinarith
  have hRhs_ge1 : 1 ≤ 6272 * max 1 C_lsst * k * (Real.log ((n : ℝ) + 2)) ^ 6 := by
    have hck : 1 ≤ max 1 C_lsst * k := by nlinarith
    have hckL : 1 ≤ max 1 C_lsst * k * (64 * (Real.log ((n : ℝ) + 2)) ^ 6) := by nlinarith
    linarith
  unfold wstrThresh
  refine max_le hRhs_ge1 ?_
  have hmul1 : 8 * ((hldDepthBound n : ℝ) + 1) ^ 2 ≤ 6272 * (Real.log ((n : ℝ) + 2)) ^ 4 := by
    calc 8 * ((hldDepthBound n : ℝ) + 1) ^ 2
        ≤ 8 * (28 * (Real.log ((n : ℝ) + 2)) ^ 2) ^ 2 := by linarith
      _ = 6272 * (Real.log ((n : ℝ) + 2)) ^ 4 := by ring
  have hck_nn : 0 ≤ max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k := by positivity
  calc 8 * ((hldDepthBound n : ℝ) + 1) ^ 2 * max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k
      = (8 * ((hldDepthBound n : ℝ) + 1) ^ 2) * (max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k) := by ring
    _ ≤ (6272 * (Real.log ((n : ℝ) + 2)) ^ 4) * (max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k) :=
        mul_le_mul_of_nonneg_right hmul1 hck_nn
    _ = 6272 * max 1 C_lsst * k * (Real.log ((n : ℝ) + 2)) ^ 6 := by ring

/-! ## Congestion bridge ordering & bridge-free endpoint paths -/

lemma congOrder_bridge_lt {G₀ T₀ G_v : MGraph} {r₀ : ℕ} (hT₀ : IsRootedTree T₀ r₀)
    (hsub : G₀.V ⊆ G_v.V ∧ G₀.E ⊆ G_v.E ∧ ∀ e ∈ G₀.E, G₀.tail e = G_v.tail e ∧ G₀.head e = G_v.head e)
    (hTG_edges : ∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f)
    (hGv_paths : ∀ e' ∈ G_v.E, walkEdges (T₀.forestPath (G_v.tail e') (G_v.head e')) ⊆ G₀.E)
    {ℓ_v : ℕ → ℝ} (hℓ : ∀ e' ∈ G_v.E, 0 < ℓ_v e')
    {b g : ℕ} (hb : b ∈ T₀.E) (hbG : b ∉ G₀.E) (hg : g ∈ T₀.E) (hgG : g ∈ G₀.E) :
    congOrder T₀ (congestion G_v T₀ ℓ_v) b < congOrder T₀ (congestion G_v T₀ ℓ_v) g := by
  have hb_cong : congestion G_v T₀ ℓ_v b = 0 := by
    unfold congestion
    refine Finset.sum_eq_zero (fun e' he' => ?_)
    have hnot : b ∉ walkEdges (T₀.forestPath (G_v.tail e') (G_v.head e')) :=
      fun h => hbG (hGv_paths e' he' h)
    exact ite_eq_right_iff.mpr (fun h => absurd h hnot)
  have hg_cong_pos : 0 < congestion G_v T₀ ℓ_v g := by
    have hge := hsub.2.1 hgG
    have htail := (hsub.2.2 g hgG).1.symm.trans (hTG_edges g hg hgG).1.symm
    have hhead := (hsub.2.2 g hgG).2.symm.trans (hTG_edges g hg hgG).2.symm
    have hne : T₀.tail g ≠ T₀.head g := isForest_no_selfLoop hT₀.isForest hg
    have hP_g : T₀.IsPath (G_v.tail g) (G_v.head g) [(g, true)] := by
      rw [htail, hhead]
      exact ⟨.cons hg rfl (.nil _), by simp [MGraph.walkVertices, MGraph.dst, hne]⟩
    have hfp : T₀.forestPath (G_v.tail g) (G_v.head g) = [(g, true)] :=
      forestPath_eq_of_isPath hT₀.isForest hP_g
    have hg_mem : g ∈ walkEdges (T₀.forestPath (G_v.tail g) (G_v.head g)) := by
      rw [hfp, walkEdges_cons, Finset.mem_insert]; exact Or.inl rfl
    have hterm : 0 < if g ∈ walkEdges (T₀.forestPath (G_v.tail g) (G_v.head g)) then 1 / ℓ_v g else 0 := by
      rw [ite_eq_left_iff.mpr (fun h => absurd hg_mem h)]
      exact div_pos zero_lt_one (hℓ g hge)
    have hnonneg : ∀ e' ∈ G_v.E,
        0 ≤ if g ∈ walkEdges (T₀.forestPath (G_v.tail e') (G_v.head e')) then 1 / ℓ_v e' else 0 := by
      intro e' he'
      split_ifs
      · exact div_nonneg zero_le_one (le_of_lt (hℓ e' he'))
      · exact le_rfl
    unfold congestion
    exact lt_of_lt_of_le hterm (Finset.single_le_sum hnonneg hge)
  exact congOrder_lt_of_lex (congestion G_v T₀ ℓ_v) hb (Or.inl (hb_cong ▸ hg_cong_pos))

private lemma walkEdges_forestPath_split_sub {T : MGraph} (hT : T.IsForest)
    {a b z : ℕ} (hab : T.Connected a b) (hz : z ∈ T.walkVertices a (T.forestPath a b)) :
    walkEdges (T.forestPath a b) = walkEdges (T.forestPath a z) ∪ walkEdges (T.forestPath z b) := by
  rw [(forestPath_mem_walkVertices_split hT hab hz).1, walkEdges_append]

private lemma forestPath_parentEdge_endpoints_in_T {T : MGraph} {r f : ℕ} (hT : IsRootedTree T r)
    (hf : f ∈ T.E) :
    ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = f := by
  rcases edge_parent_orientation hT hf with ⟨_, hpe, htr⟩ | ⟨_, hpe, hhr⟩
  · exact ⟨T.tail f, (hT.isForest.1 f hf).1, htr, hpe⟩
  · exact ⟨T.head f, (hT.isForest.1 f hf).2, hhr, hpe⟩

private lemma parentEdge_mem_walkEdges_forestPath_iff {T : MGraph} {r c a b : ℕ}
    (hT : IsRootedTree T r) (hc : c ∈ T.V) (hcr : c ≠ r) (ha : a ∈ T.V) (hb : b ∈ T.V) :
    parentEdge T r c ∈ walkEdges (T.forestPath a b) ↔
      (IsAncestor T r c a ∧ ¬ IsAncestor T r c b) ∨
      (IsAncestor T r c b ∧ ¬ IsAncestor T r c a) := by
  let l := lca T r a b
  have hlV : l ∈ T.V := lca_mem hT ha hb
  have hla := lca_isAncestor_left hT ha hb
  have hlb := lca_isAncestor_right hT ha hb
  have hsplit := walkEdges_forestPath_split_sub hT.isForest (hT.connected ha hb)
    (lca_mem_forestPath hT ha hb)
  have hrev : walkEdges (T.forestPath l b) = walkEdges (T.forestPath b l) := by
    rw [forestPath_rev hT.isForest (hT.connected hlV hb), walkEdges_walkRev]
  rw [hsplit, hrev, Finset.mem_union,
    parentEdge_mem_walkEdges_ancestor_iff hT hc hcr ha hla,
    parentEdge_mem_walkEdges_ancestor_iff hT hc hcr hb hlb,
    isAncestor_lca_iff hT ha hb]
  tauto

private lemma isWalk_of_walkEdges_sub {T F : MGraph} {a b : ℕ} {Q : List (ℕ × Bool)}
    (hW : T.IsWalk a b Q) (hsub : walkEdges Q ⊆ F.E)
    (ht : F.tail = T.tail) (hh : F.head = T.head) : F.IsWalk a b Q := by
  have hsrc : F.src = T.src := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.src, ht, hh]
  have hdst : F.dst = T.dst := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.dst, ht, hh]
  induction hW with
  | nil w => exact .nil w
  | @cons _ _ x xs _ hs _ ih =>
    have hxe : x.1 ∈ F.E := hsub (by rw [walkEdges_cons]; exact Finset.mem_insert_self _ _)
    have hsub' : walkEdges xs ⊆ F.E :=
      fun e he => hsub (by rw [walkEdges_cons]; exact Finset.mem_insert_of_mem he)
    exact .cons hxe (by rw [hsrc, hs]) (hdst ▸ ih hsub')

/-- Whenever `π` sorts bridge edges outside `H` strictly before all edges inside `H`, for any
edge `(u, v)` whose `T`-path lies in `H`, the endpoint path `T[u, RF.root u]` used by
`RF.stretch` stays entirely inside `H` whenever `RF.root u ≠ RF.root v ∨ v ∈ R`. -/
lemma no_bridge_in_endpoint_path {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {H R : Finset ℕ} (hR : IsBranchFree T r R) (hrR : r ∈ R)
    {π : ℕ → ℕ} (_hord : IsEdgeOrder T π)
    (hpi : ∀ b ∈ T.E, b ∉ H → ∀ g ∈ T.E, g ∈ H → π b < π g)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V)
    (huv_H : walkEdges (T.forestPath u v) ⊆ H)
    (hcond : (rootedForestGivenRoots T r R π).root u ≠
        (rootedForestGivenRoots T r R π).root v ∨ v ∈ R) :
    walkEdges (T.forestPath u ((rootedForestGivenRoots T r R π).root u)) ⊆ H := by
  classical
  let RF := rootedForestGivenRoots T r R π
  let F := forestGivenRoots T r R π
  have hRne : R.Nonempty := ⟨r, hrR⟩
  have hRS := forestGivenRoots_isRootedSpanningForest hT hR hRne π
  let r_u := RF.root u
  have hru_spec := rootedForest_root_spec hRS hu
  have hru_R : r_u ∈ R := hru_spec.1
  have hru_V : r_u ∈ T.V := hR.1 hru_R
  have hF_sub : T.IsSubgraph F := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have h_u_ru_F : walkEdges (T.forestPath u r_u) ⊆ F.E := by
    have := forestPath_subgraph hT.isForest hF_sub hru_spec.2
    rw [← this]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact IsWalk_edges_mem (forestPath_isPath hRS.1 hru_spec.2).1 hx
  intro f hf_mem
  by_contra hfH
  have hfT : f ∈ T.E := walkEdges_forestPath_sub_edges hT.isForest hf_mem
  have hv_ne_ru : v ≠ r_u := by
    intro hEq
    rw [hEq] at huv_H
    exact hfH (huv_H hf_mem)
  have h_not_conn_v : ¬ F.Connected v r_u := by
    intro hcv
    rcases hcond with hne | hvR
    · have := (rootedForest_root_eq_iff hRS hv hru_V).mpr hcv
      rw [rootedForest_root_self hRS hru_R] at this
      exact hne this.symm
    · exact forestGivenRoots_not_connected_roots hT hR hRne π hvR hru_R hv_ne_ru hcv
  let z := med T r u v r_u
  have hz_spec := med_mem_forestPath hT hu hv hru_V
  have hzV : z ∈ T.V := hz_spec.1
  have hz_uru : z ∈ T.walkVertices u (T.forestPath u r_u) := by
    have hmem := hz_spec.2.2.2
    rw [forestPath_rev hT.isForest (hT.connected hu hru_V),
      walkVertices_walkRev (forestPath_isPath hT.isForest (hT.connected hu hru_V)).1,
      List.mem_reverse] at hmem
    exact hmem
  have h_uv_split := walkEdges_forestPath_split_sub hT.isForest (hT.connected hu hv) hz_spec.2.1
  have h_uru_split := walkEdges_forestPath_split_sub hT.isForest (hT.connected hu hru_V) hz_uru
  have h_vru_split : walkEdges (T.forestPath v r_u) =
      walkEdges (T.forestPath v z) ∪ walkEdges (T.forestPath z r_u) :=
    walkEdges_forestPath_split_sub hT.isForest (hT.connected hv hru_V) hz_spec.2.2.1
  have h_uz_H : walkEdges (T.forestPath u z) ⊆ H :=
    Finset.Subset.trans (h_uv_split ▸ Finset.subset_union_left) huv_H
  have h_zv_H : walkEdges (T.forestPath v z) ⊆ H := by
    have : walkEdges (T.forestPath v z) = walkEdges (T.forestPath z v) := by
      rw [forestPath_rev hT.isForest (hT.connected hzV hv), walkEdges_walkRev]
    rw [this]
    exact Finset.Subset.trans (h_uv_split ▸ Finset.subset_union_right) huv_H
  have hf_zru : f ∈ walkEdges (T.forestPath z r_u) := by
    rw [h_uru_split, Finset.mem_union] at hf_mem
    exact hf_mem.resolve_left (fun h => hfH (h_uz_H h))
  have h_zru_F : walkEdges (T.forestPath z r_u) ⊆ F.E :=
    Finset.Subset.trans (h_uru_split ▸ Finset.subset_union_right) h_u_ru_F
  have hd_ex : ∃ d ∈ walkEdges (T.forestPath v z), d ∈ deletedEdges T r R π := by
    by_contra hnone
    push Not at hnone
    apply h_not_conn_v
    have hP := forestPath_isPath hT.isForest (hT.connected hv hru_V)
    refine ⟨T.forestPath v r_u, ?_⟩
    have hsubE : ∀ e ∈ walkEdges (T.forestPath v r_u), e ∈ F.E := by
      intro e he
      rw [h_vru_split, Finset.mem_union] at he
      rcases he with h1 | h2
      · refine Finset.mem_sdiff.mpr ⟨walkEdges_forestPath_sub_edges hT.isForest h1, hnone e h1⟩
      · exact h_zru_F h2
    exact isWalk_of_walkEdges_sub hP.1 hsubE rfl rfl
  obtain ⟨d, hd_vz, hd_del⟩ := hd_ex
  have hdH : d ∈ H := h_zv_H hd_vz
  have hdT : d ∈ T.E := walkEdges_forestPath_sub_edges hT.isForest hd_vz
  unfold deletedEdges at hd_del
  rw [ite_eq_left_iff.mpr (fun h => absurd hRne h), Finset.mem_image] at hd_del
  obtain ⟨x, hx_er, hxd_eq⟩ := hd_del
  have hxR : x ∈ R := (Finset.mem_erase.mp hx_er).2
  have hxV : x ∈ T.V := hR.1 hxR
  have hy_spec := rootParent_spec hT hR hRne hx_er
  let y := rootParent T r R x
  have hyR : y ∈ R := hy_spec.1
  have hyV : y ∈ T.V := hR.1 hyR
  have hyx_anc : IsAncestor T r y x := hy_spec.2.2.1
  have hd_xy : d ∈ walkEdges (T.forestPath x y) := by
    rw [← hxd_eq]; exact deletedEdge_mem_walkEdges hT hR hRne hx_er
  obtain ⟨c_d, hcd_V, hcd_r, hcd_eq⟩ := forestPath_parentEdge_endpoints_in_T hT hdT
  have hcd_x : IsAncestor T r c_d x := by
    have hm := hd_xy
    rw [← hcd_eq, parentEdge_mem_walkEdges_ancestor_iff hT hcd_V hcd_r hxV hyx_anc] at hm
    exact hm.1
  have h_not_cd_y : ¬ IsAncestor T r c_d y := by
    have hm := hd_xy
    rw [← hcd_eq, parentEdge_mem_walkEdges_ancestor_iff hT hcd_V hcd_r hxV hyx_anc] at hm
    exact hm.2
  have h_pi_fg : π f < π d := hpi f hfT hfH d hdT hdH
  have h_f_not_xy : f ∉ walkEdges (T.forestPath x y) := by
    intro hmem
    have hle := deletedEdge_le (π := π) (T := T) (r := r) (R := R) (x := x) hmem
    rw [hxd_eq] at hle
    omega
  obtain ⟨c, hcV, hcr, hce⟩ := forestPath_parentEdge_endpoints_in_T hT hfT
  have h_no_other_root_zru : ∀ q ∈ R, q ∈ T.walkVertices z (T.forestPath z r_u) → q = r_u := by
    intro q hqR hq_mem
    have hP_zru := forestPath_isPath hT.isForest (hT.connected hzV hru_V)
    obtain ⟨_, Q₂, hQp, _, hQ2⟩ := walkVertices_mem_split hP_zru.1 hq_mem
    have hq_ru_F : F.Connected q r_u :=
      ⟨Q₂, isWalk_of_walkEdges_sub hQ2 (fun e he => h_zru_F (by
        rw [hQp, walkEdges_append, Finset.mem_union]; exact Or.inr he)) rfl rfl⟩
    by_contra hne
    exact forestGivenRoots_not_connected_roots hT hR hRne π hqR hru_R hne hq_ru_F
  rw [← hce, parentEdge_mem_walkEdges_forestPath_iff hT hcV hcr hzV hru_V] at hf_zru
  rcases hf_zru with ⟨hcz, h_not_cru⟩ | ⟨h_cru, h_not_cz⟩
  · have hcv : IsAncestor T r c v := by
      by_contra h_not_cv
      have hf_vz : f ∈ walkEdges (T.forestPath v z) := by
        rw [← hce, parentEdge_mem_walkEdges_forestPath_iff hT hcV hcr hv hzV]
        exact Or.inr ⟨hcz, h_not_cv⟩
      exact hfH (h_zv_H hf_vz)
    have hd_cases := (parentEdge_mem_walkEdges_forestPath_iff hT hcd_V hcd_r hv hzV).mp (hcd_eq.symm ▸ hd_vz)
    have hc_cd : IsAncestor T r c c_d := by
      rcases hd_cases with ⟨hcd_v, hnot_z⟩ | ⟨hcd_z, hnot_v⟩
      · rcases isAncestor_total_on_ancestors hT hv hcv hcd_v with h1 | h2
        · exact h1
        · exact absurd (isAncestor_trans hT hzV h2 hcz) hnot_z
      · rcases isAncestor_total_on_ancestors hT hzV hcz hcd_z with h1 | h2
        · exact h1
        · exact absurd (isAncestor_trans hT hv h2 hcv) hnot_v
    have hcx : IsAncestor T r c x := isAncestor_trans hT hxV hc_cd hcd_x
    have hcy : IsAncestor T r c y := by
      by_contra h_not_cy
      exact h_f_not_xy (hce ▸ (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hxV hyx_anc).mpr ⟨hcx, h_not_cy⟩)
    let S_cy := (R.filter (IsAncestor T r c)).filter (fun q => IsAncestor T r q y)
    have hyS : y ∈ S_cy := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyR, hcy⟩, isAncestor_refl T r y⟩
    obtain ⟨w, hwS, hw_min⟩ := Finset.exists_min_image S_cy (depth T r) ⟨y, hyS⟩
    have hwR : w ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hwS).1).1
    have hwV : w ∈ T.V := hR.1 hwR
    have hcw : IsAncestor T r c w := (Finset.mem_filter.mp (Finset.mem_filter.mp hwS).1).2
    have hwy : IsAncestor T r w y := (Finset.mem_filter.mp hwS).2
    have hw_ne_top : w ≠ topRoot T r R := by
      intro hEq
      have hanc := hEq ▸ topRoot_isAncestor hT hR hRne hru_R
      exact h_not_cru (isAncestor_trans hT hru_V hcw hanc)
    have hw_er : w ∈ R.erase (topRoot T r R) := Finset.mem_erase.mpr ⟨hw_ne_top, hwR⟩
    have hwp_spec := rootParent_spec hT hR hRne hw_er
    let wp := rootParent T r R w
    have hwpR : wp ∈ R := hwp_spec.1
    have hwp_ne_w : wp ≠ w := hwp_spec.2.1
    have hwp_w : IsAncestor T r wp w := hwp_spec.2.2.1
    have h_not_c_wp : ¬ IsAncestor T r c wp := by
      intro hcp
      have hmem : wp ∈ S_cy := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hwpR, hcp⟩, isAncestor_trans hT hyV hwp_w hwy⟩
      have hd_lt : depth T r wp < depth T r w := by
        have hle := isAncestor_depth_le hT hwV hwp_w
        have hne_d : depth T r wp ≠ depth T r w := fun h => hwp_ne_w ((isAncestor_eq_iff_depth hT hwV hwp_w).mp h)
        omega
      have := hw_min wp hmem
      omega
    have hf_wwp : f ∈ walkEdges (T.forestPath w wp) :=
      hce ▸ (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hwV hwp_w).mpr ⟨hcw, h_not_c_wp⟩
    let e := deletedEdge T r R π w
    have he_walk : e ∈ walkEdges (T.forestPath w wp) := deletedEdge_mem_walkEdges hT hR hRne hw_er
    have he_del : e ∈ deletedEdges T r R π := by
      unfold deletedEdges
      rw [ite_eq_left_iff.mpr (fun h => absurd hRne h)]
      exact Finset.mem_image_of_mem _ hw_er
    have heT : e ∈ T.E := deletedEdge_mem_E hT hR hRne hw_er
    have he_not_H : e ∉ H := by
      intro heH
      have hle_ew : π e ≤ π f := deletedEdge_le hf_wwp
      have hlt_fe : π f < π e := hpi f hfT hfH e heT heH
      omega
    have h_lca_eq : lca T r w r_u = lca T r z r_u := by
      have h_not_cr_lca : ¬ IsAncestor T r c (lca T r z r_u) := fun h =>
        h_not_cru (isAncestor_trans hT hru_V h (lca_isAncestor_right hT hzV hru_V))
      have h_not_cr_lw : ¬ IsAncestor T r c (lca T r w r_u) := fun h =>
        h_not_cru (isAncestor_trans hT hru_V h (lca_isAncestor_right hT hwV hru_V))
      have h_lw_sub : IsAncestor T r (lca T r w r_u) (lca T r z r_u) := by
        have h1 : IsAncestor T r (lca T r w r_u) w := lca_isAncestor_left hT hwV hru_V
        have h2 : IsAncestor T r (lca T r w r_u) c := by
          rcases isAncestor_total_on_ancestors hT hwV h1 hcw with ha | hb
          · exact ha
          · exact absurd hb h_not_cr_lw
        exact (isAncestor_lca_iff hT hzV hru_V).mpr
          ⟨isAncestor_trans hT hzV h2 hcz, lca_isAncestor_right hT hwV hru_V⟩
      have h_lz_sub : IsAncestor T r (lca T r z r_u) (lca T r w r_u) := by
        have h1 : IsAncestor T r (lca T r z r_u) z := lca_isAncestor_left hT hzV hru_V
        have h2 : IsAncestor T r (lca T r z r_u) c := by
          rcases isAncestor_total_on_ancestors hT hzV h1 hcz with ha | hb
          · exact ha
          · exact absurd hb h_not_cr_lca
        exact (isAncestor_lca_iff hT hwV hru_V).mpr
          ⟨isAncestor_trans hT hwV h2 hcw, lca_isAncestor_right hT hzV hru_V⟩
      exact isAncestor_antisymm hT (lca_mem hT hwV hru_V) (lca_mem hT hzV hru_V) h_lw_sub h_lz_sub
    have hl_R : lca T r z r_u ∈ R := h_lca_eq ▸ hR.2 w hwR r_u hru_R
    have hl_eq_ru : lca T r z r_u = r_u :=
      h_no_other_root_zru _ hl_R (lca_mem_forestPath hT hzV hru_V)
    have hru_wp : IsAncestor T r r_u wp := by
      have hru_anc_w : IsAncestor T r r_u w := by
        rw [← hl_eq_ru, ← h_lca_eq]; exact lca_isAncestor_left hT hwV hru_V
      have hru_ne_w : r_u ≠ w := fun h => h_not_cru (h ▸ hcw)
      exact hwp_spec.2.2.2 r_u hru_R hru_ne_w hru_anc_w
    obtain ⟨c_e, hce_V, hce_r, hce_eq⟩ := forestPath_parentEdge_endpoints_in_T hT heT
    have hce_w : IsAncestor T r c_e w := by
      have hm := he_walk
      rw [← hce_eq, parentEdge_mem_walkEdges_ancestor_iff hT hce_V hce_r hwV hwp_w] at hm
      exact hm.1
    have hnot_ce_wp : ¬ IsAncestor T r c_e wp := by
      have hm := he_walk
      rw [← hce_eq, parentEdge_mem_walkEdges_ancestor_iff hT hce_V hce_r hwV hwp_w] at hm
      exact hm.2
    have hnot_ce_ru : ¬ IsAncestor T r c_e r_u := fun h =>
      hnot_ce_wp (isAncestor_trans hT (hR.1 hwpR) h hru_wp)
    rcases isAncestor_total_on_ancestors hT hwV hce_w hcw with h_cec | h_cce
    · have he_zru : e ∈ walkEdges (T.forestPath z r_u) := by
        rw [← hce_eq, parentEdge_mem_walkEdges_forestPath_iff hT hce_V hce_r hzV hru_V]
        exact Or.inl ⟨isAncestor_trans hT hzV h_cec hcz, hnot_ce_ru⟩
      exact (Finset.mem_sdiff.mp (h_zru_F he_zru)).2 he_del
    · have hy_anc_cd : IsAncestor T r y c_d := by
        rcases isAncestor_total_on_ancestors hT hxV hyx_anc hcd_x with h1 | h2
        · exact h1
        · exact absurd h2 h_not_cd_y
      have hce_cd : IsAncestor T r c_e c_d :=
        isAncestor_trans hT hcd_V hce_w (isAncestor_trans hT hcd_V hwy hy_anc_cd)
      by_cases hce_z : IsAncestor T r c_e z
      · have he_zru : e ∈ walkEdges (T.forestPath z r_u) := by
          rw [← hce_eq, parentEdge_mem_walkEdges_forestPath_iff hT hce_V hce_r hzV hru_V]
          exact Or.inl ⟨hce_z, hnot_ce_ru⟩
        exact (Finset.mem_sdiff.mp (h_zru_F he_zru)).2 he_del
      · have hcd_v : IsAncestor T r c_d v := by
          rcases hd_cases with ⟨hcd_v, _⟩ | ⟨hcd_z, _⟩
          · exact hcd_v
          · exact absurd (isAncestor_trans hT hzV hce_cd hcd_z) hce_z
        have he_vz : e ∈ walkEdges (T.forestPath v z) := by
          rw [← hce_eq, parentEdge_mem_walkEdges_forestPath_iff hT hce_V hce_r hv hzV]
          exact Or.inl ⟨isAncestor_trans hT hv hce_cd hcd_v, hce_z⟩
        exact he_not_H (h_zv_H he_vz)
  · have hnot_cv : ¬ IsAncestor T r c v := by
      intro hcv
      have hf_vz : f ∈ walkEdges (T.forestPath v z) := by
        rw [← hce, parentEdge_mem_walkEdges_forestPath_iff hT hcV hcr hv hzV]
        exact Or.inl ⟨hcv, h_not_cz⟩
      exact hfH (h_zv_H hf_vz)
    have hd_cases := (parentEdge_mem_walkEdges_forestPath_iff hT hcd_V hcd_r hv hzV).mp (hcd_eq.symm ▸ hd_vz)
    have hnot_cx : ¬ IsAncestor T r c x := by
      intro hcx
      have h_cd_c : IsAncestor T r c_d c := by
        rcases isAncestor_total_on_ancestors hT hxV hcd_x hcx with h1 | h2
        · exact h1
        · rcases hd_cases with ⟨hcd_v, _⟩ | ⟨hcd_z, _⟩
          · exact absurd (isAncestor_trans hT hv h2 hcd_v) hnot_cv
          · exact absurd (isAncestor_trans hT hzV h2 hcd_z) h_not_cz
      have hnot_cy : ¬ IsAncestor T r c y := fun hcy => h_not_cd_y (isAncestor_trans hT hyV h_cd_c hcy)
      exact h_f_not_xy (hce ▸ (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hxV hyx_anc).mpr ⟨hcx, hnot_cy⟩)
    let a := lca T r x r_u
    have haR : a ∈ R := hR.2 x hxR r_u hru_R
    have haV : a ∈ T.V := hR.1 haR
    have hnot_ca : ¬ IsAncestor T r c a := fun hca => hnot_cx (isAncestor_trans hT hxV hca (lca_isAncestor_left hT hxV hru_V))
    have ha_c : IsAncestor T r a c := by
      rcases isAncestor_total_on_ancestors hT hru_V (lca_isAncestor_right hT hxV hru_V) h_cru with h1 | h2
      · exact h1
      · exact absurd h2 hnot_ca
    let l := lca T r z r_u
    have hlV : l ∈ T.V := lca_mem hT hzV hru_V
    have ha_l : IsAncestor T r a l := by
      rcases isAncestor_total_on_ancestors hT hru_V (lca_isAncestor_right hT hxV hru_V)
          (lca_isAncestor_right hT hzV hru_V) with h1 | h2
      · exact h1
      · exfalso
        have ha_mem : a ∈ T.walkVertices z (T.forestPath z r_u) := by
          rw [mem_walkVertices_forestPath_iff hT hzV hru_V]
          exact ⟨h2, Or.inr (lca_isAncestor_right hT hxV hru_V)⟩
        exact hnot_ca ((h_no_other_root_zru a haR ha_mem) ▸ h_cru)
    have hru_ne_top : r_u ≠ topRoot T r R := by
      intro hEq
      have hru_a := hEq ▸ topRoot_isAncestor hT hR hRne haR
      exact hnot_ca (isAncestor_trans hT haV h_cru hru_a)
    have hru_er : r_u ∈ R.erase (topRoot T r R) := Finset.mem_erase.mpr ⟨hru_ne_top, hru_R⟩
    have hrp_spec := rootParent_spec hT hR hRne hru_er
    let rp := rootParent T r R r_u
    have hrpR : rp ∈ R := hrp_spec.1
    have hrp_ne_ru : rp ≠ r_u := hrp_spec.2.1
    have hrp_ru : IsAncestor T r rp r_u := hrp_spec.2.2.1
    have ha_ne_ru : a ≠ r_u := fun h => hnot_ca (h ▸ h_cru)
    have ha_rp : IsAncestor T r a rp := hrp_spec.2.2.2 a haR ha_ne_ru (lca_isAncestor_right hT hxV hru_V)
    have hnot_l_rp : ¬ IsAncestor T r l rp := by
      intro hlrp
      have hrp_mem : rp ∈ T.walkVertices z (T.forestPath z r_u) := by
        rw [mem_walkVertices_forestPath_iff hT hzV hru_V]
        exact ⟨hlrp, Or.inr hrp_ru⟩
      exact hrp_ne_ru (h_no_other_root_zru rp hrpR hrp_mem)
    have hrp_l : IsAncestor T r rp l := by
      rcases isAncestor_total_on_ancestors hT hru_V hrp_ru (lca_isAncestor_right hT hzV hru_V) with h1 | h2
      · exact h1
      · exact absurd h2 hnot_l_rp
    have hnot_c_rp : ¬ IsAncestor T r c rp := fun hcrp =>
      h_not_cz (isAncestor_trans hT hzV (isAncestor_trans hT hlV hcrp hrp_l) (lca_isAncestor_left hT hzV hru_V))
    have hf_rurp : f ∈ walkEdges (T.forestPath r_u rp) :=
      hce ▸ (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hru_V hrp_ru).mpr ⟨h_cru, hnot_c_rp⟩
    let e := deletedEdge T r R π r_u
    have he_walk : e ∈ walkEdges (T.forestPath r_u rp) := deletedEdge_mem_walkEdges hT hR hRne hru_er
    have he_del : e ∈ deletedEdges T r R π := by
      unfold deletedEdges
      rw [ite_eq_left_iff.mpr (fun h => absurd hRne h)]
      exact Finset.mem_image_of_mem _ hru_er
    have heT : e ∈ T.E := deletedEdge_mem_E hT hR hRne hru_er
    have he_not_H : e ∉ H := by
      intro heH
      have hle_er : π e ≤ π f := deletedEdge_le hf_rurp
      have hlt_fe : π f < π e := hpi f hfT hfH e heT heH
      omega
    obtain ⟨c_e, hce_V, hce_r, hce_eq⟩ := forestPath_parentEdge_endpoints_in_T hT heT
    have hce_ru : IsAncestor T r c_e r_u := by
      have hm := he_walk
      rw [← hce_eq, parentEdge_mem_walkEdges_ancestor_iff hT hce_V hce_r hru_V hrp_ru] at hm
      exact hm.1
    have hnot_ce_rp : ¬ IsAncestor T r c_e rp := by
      have hm := he_walk
      rw [← hce_eq, parentEdge_mem_walkEdges_ancestor_iff hT hce_V hce_r hru_V hrp_ru] at hm
      exact hm.2
    have hce_z : IsAncestor T r c_e z := by
      by_contra hnot_cez
      have he_zru : e ∈ walkEdges (T.forestPath z r_u) := by
        rw [← hce_eq, parentEdge_mem_walkEdges_forestPath_iff hT hce_V hce_r hzV hru_V]
        exact Or.inr ⟨hce_ru, hnot_cez⟩
      exact (Finset.mem_sdiff.mp (h_zru_F he_zru)).2 he_del
    have hnot_ce_v : ¬ IsAncestor T r c_e v := by
      intro hce_v
      have hce_cd : IsAncestor T r c_e c_d := by
        rcases hd_cases with ⟨hcd_v, hnot_z⟩ | ⟨hcd_z, hnot_v⟩
        · rcases isAncestor_total_on_ancestors hT hv hce_v hcd_v with h1 | h2
          · exact h1
          · exact absurd (isAncestor_trans hT hzV h2 hce_z) hnot_z
        · rcases isAncestor_total_on_ancestors hT hzV hce_z hcd_z with h1 | h2
          · exact h1
          · exact absurd (isAncestor_trans hT hv h2 hce_v) hnot_v
      have hce_x : IsAncestor T r c_e x := isAncestor_trans hT hxV hce_cd hcd_x
      have hce_a : IsAncestor T r c_e a := (isAncestor_lca_iff hT hxV hru_V).mpr ⟨hce_x, hce_ru⟩
      exact hnot_ce_rp (isAncestor_trans hT (hR.1 hrpR) hce_a ha_rp)
    have he_vz : e ∈ walkEdges (T.forestPath v z) := by
      rw [← hce_eq, parentEdge_mem_walkEdges_forestPath_iff hT hce_V hce_r hv hzV]
      exact Or.inr ⟨hce_z, hnot_ce_v⟩
    exact he_not_H (h_zv_H he_vz)

/-! ## Decomposition refinement and dynamic stability -/

/-- Adding isolated vertices without adding edges preserves being a forest. -/
lemma addVerts_isForest {T : MGraph} (hT : T.IsForest) (S : Finset ℕ) :
    { T with V := T.V ∪ S }.IsForest := by
  refine ⟨fun e he => ⟨Finset.mem_union_left _ (hT.1 e he).1,
    Finset.mem_union_left _ (hT.1 e he).2⟩, fun P hcyc => ?_⟩
  rcases hcyc with ⟨hne, hnd, u, hW⟩
  have hW_to_T : ∀ a b Q, { T with V := T.V ∪ S }.IsWalk a b Q → T.IsWalk a b Q := by
    intro a b Q hQ
    induction hQ with
    | nil w => exact .nil w
    | cons hx hs _ ih => exact .cons hx hs ih
  exact hT.2 P ⟨hne, hnd, u, hW_to_T u u P hW⟩

/-- Degree of any vertex untouched by an update `u` does not increase. -/
lemma deg_le_of_update (G : MGraph) (u : Update) {x : ℕ}
    (h_untouched : match u with
      | .insert _ a b => x ≠ a ∧ x ≠ b
      | .delete _ => True
      | .split v v' _ _ => x ≠ v ∧ x ≠ v') :
    (G.applyUpdate u).deg x ≤ G.deg x := by
  cases u with
  | insert e a b =>
    obtain ⟨hxa, hxb⟩ := h_untouched
    have hnot : e ∉ G.E → True := fun _ => trivial
    unfold MGraph.applyUpdate MGraph.deg
    dsimp only
    have ht_sub : ((insert e G.E).filter (fun f => Function.update G.tail e a f = x)) ⊆
        G.E.filter (fun f => G.tail f = x) := by
      intro f hf
      rw [Finset.mem_filter, Finset.mem_insert] at hf
      rw [Finset.mem_filter]
      rcases hf with ⟨rfl | hfG, hval⟩
      · rw [Function.update_self] at hval; exact absurd hval.symm hxa
      · have hfe : f ≠ e := fun h => by
          rw [h, Function.update_self] at hval; exact hxa hval.symm
        rw [Function.update_of_ne hfe] at hval
        exact ⟨hfG, hval⟩
    have hh_sub : ((insert e G.E).filter (fun f => Function.update G.head e b f = x)) ⊆
        G.E.filter (fun f => G.head f = x) := by
      intro f hf
      rw [Finset.mem_filter, Finset.mem_insert] at hf
      rw [Finset.mem_filter]
      rcases hf with ⟨rfl | hfG, hval⟩
      · rw [Function.update_self] at hval; exact absurd hval.symm hxb
      · have hfe : f ≠ e := fun h => by
          rw [h, Function.update_self] at hval; exact hxb hval.symm
        rw [Function.update_of_ne hfe] at hval
        exact ⟨hfG, hval⟩
    exact Nat.add_le_add (Finset.card_le_card ht_sub) (Finset.card_le_card hh_sub)
  | delete e =>
    unfold MGraph.applyUpdate MGraph.deg
    dsimp only
    exact Nat.add_le_add
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset e G.E)))
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset e G.E)))
  | split v v' St Sh =>
    obtain ⟨hxv, hxv'⟩ := h_untouched
    unfold MGraph.applyUpdate MGraph.deg
    dsimp only
    have ht_eq : (G.E.filter (fun f => (if f ∈ St ∧ G.tail f = v then v' else G.tail f) = x)) =
        G.E.filter (fun f => G.tail f = x) := by
      apply Finset.filter_congr
      intro f _
      split_ifs with h
      · exact ⟨fun h1 => absurd h1.symm hxv', fun h1 => absurd (h1.symm.trans h.2) hxv⟩
      · rfl
    have hh_eq : (G.E.filter (fun f => (if f ∈ Sh ∧ G.head f = v then v' else G.head f) = x)) =
        G.E.filter (fun f => G.head f = x) := by
      apply Finset.filter_congr
      intro f _
      split_ifs with h
      · exact ⟨fun h1 => absurd h1.symm hxv', fun h1 => absurd (h1.symm.trans h.2) hxv⟩
      · rfl
    rw [ht_eq, hh_eq]

private lemma pathConvex_compOf {T F : MGraph} (hT : T.IsForest) (hF : F.IsForest)
    (hsub : T.IsSubgraph F) {x : ℕ} (hx : x ∈ F.V) :
    PathConvex T (compOf F x) := by
  refine ⟨⟨x, self_mem_compOf hx⟩, fun v hv => hsub.1 (mem_compOf_iff.mp hv).1, ?_⟩
  intro a ha b hb w hw
  rw [mem_compOf_iff] at ha hb ⊢
  have hab : F.Connected a b := connected_trans (connected_symm ha.2) hb.2
  have hP := forestPath_isPath hF hab
  have hfp := forestPath_subgraph hT hsub hab
  have hwV_eq : F.walkVertices a (F.forestPath a b) = T.walkVertices a (T.forestPath a b) := by
    rw [hfp]
    unfold MGraph.walkVertices
    congr 1
    refine List.map_congr_left (fun y hy => ?_)
    have hyE : y.1 ∈ F.E := IsWalk_edges_mem (hfp ▸ hP.1) hy
    have heq := hsub.2.2 y.1 hyE
    rcases y with ⟨e, _ | _⟩ <;> simp only [MGraph.dst, heq.1, heq.2]
  have hwF_mem : w ∈ F.walkVertices a (F.forestPath a b) := hwV_eq.symm ▸ hw
  obtain ⟨P₁, _, _, h1, _⟩ := walkVertices_mem_split hP.1 hwF_mem
  have hwF : w ∈ F.V := (IsWalk_vertices_mem hF.1 ha.1 hP.1).2 w hwF_mem
  exact ⟨hwF, connected_trans ha.2 ⟨P₁, h1⟩⟩

private lemma firstDeleted_spec {T F : MGraph} {D : Finset ℕ}
    (hFE : F.E = T.E \ D) (hFtail : F.tail = T.tail) (hFhead : F.head = T.head) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, T.IsWalk a b P → ¬ F.Connected a b →
      ∃ x ∈ P, x.1 ∈ D ∧ F.Connected a (T.src x) := by
  have hsrc_eq : F.src = T.src := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.src, hFtail, hFhead]
  have hdst_eq : F.dst = T.dst := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.dst, hFtail, hFhead]
  intro a b P hW hnot
  induction hW with
  | nil u => exact absurd (connected_refl F u) hnot
  | @cons u _ x xs hxE hsrc hrest ih =>
    by_cases hxD : x.1 ∈ D
    · refine ⟨x, List.mem_cons_self, hxD, ?_⟩
      rw [← hsrc]
      exact connected_refl F (T.src x)
    · have hxF : x.1 ∈ F.E := by rw [hFE]; exact Finset.mem_sdiff.mpr ⟨hxE, hxD⟩
      have hsrcF : F.src x = u := by rw [hsrc_eq, hsrc]
      have hconn_ud : F.Connected u (T.dst x) :=
        ⟨[x], .cons hxF hsrcF (hdst_eq ▸ .nil _)⟩
      have hnot_rest : ¬ F.Connected (T.dst x) _ :=
        fun h => hnot (connected_trans hconn_ud h)
      obtain ⟨y, hy_mem, hyD, hy_conn⟩ := ih hnot_rest
      exact ⟨y, List.mem_cons_of_mem _ hy_mem, hyD, connected_trans hconn_ud hy_conn⟩

private lemma ancestorPath_step_depth {T : MGraph} {r t : ℕ} (hT : IsRootedTree T r) :
    ∀ d a, depth T r a = d → a ∈ T.V → IsAncestor T r t a →
      ∀ x ∈ T.forestPath a t, depth T r (T.src x) = depth T r (T.dst x) + 1 := by
  intro d
  induction d with
  | zero =>
    intro a hda haV hta x hx
    have har : a = r := by
      by_contra hne
      obtain ⟨_, hEq, _⟩ := forestPath_parent hT haV hne
      unfold depth at hda; rw [hEq, List.length_cons] at hda; omega
    have htr : t = r := by
      rw [har] at hta
      exact isAncestor_antisymm hT (isAncestor_mem hT hT.2 hta) hT.2 hta
        (isAncestor_root hT (isAncestor_mem hT hT.2 hta))
    rw [har, htr, forestPath_self hT.isForest r] at hx
    simp at hx
  | succ k ih =>
    intro a hda haV hta x hx
    by_cases hat : a = t
    · rw [hat, forestPath_self hT.isForest t] at hx; simp at hx
    · have har : a ≠ r := fun h => by
        unfold depth at hda; rw [h, forestPath_self hT.isForest r, List.length_nil] at hda; omega
      have hp_mem := parent_mem hT haV
      have hdp := depth_parent hT haV har
      have htp : IsAncestor T r t (parent T r a) := by
        rcases (isAncestor_iff_eq_or_parent hT haV).mp hta with hEq | ⟨_, hp⟩
        · exact absurd hEq.symm hat
        · exact hp
      obtain ⟨y, hEq_a, hy_dst, _, _, hy_src⟩ := forestPath_parent hT haV har
      have hsplit_a := (forestPath_eq_of_isAncestor hT haV hta).1
      have hsplit_p := (forestPath_eq_of_isAncestor hT hp_mem htp).1
      have hfp_at : T.forestPath a t = y :: T.forestPath (parent T r a) t := by
        refine (List.append_left_inj (T.forestPath t r)).mp ?_
        rw [← hsplit_a, hEq_a, List.cons_append, ← hsplit_p]
      rw [hfp_at, List.mem_cons] at hx
      rcases hx with rfl | hx_p
      · rw [hy_src, ← hy_dst]; omega
      · exact ih (parent T r a) (by omega) hp_mem htp x hx_p

private lemma src_eq_of_step_depth_eq {T : MGraph} {r : ℕ} {x₁ x₂ : ℕ × Bool}
    (h1 : x₁.1 ∈ T.E) (h2 : x₂.1 ∈ T.E) (heq : x₁.1 = x₂.1)
    (hd1 : depth T r (T.src x₁) = depth T r (T.dst x₁) + 1)
    (hd2 : depth T r (T.src x₂) = depth T r (T.dst x₂) + 1) :
    T.src x₁ = T.src x₂ := by
  rcases x₁ with ⟨e1, _ | _⟩ <;> rcases x₂ with ⟨e2, _ | _⟩ <;>
    dsimp only at heq <;> subst heq <;>
    simp [MGraph.src, MGraph.dst] at hd1 hd2 ⊢ <;>
    omega

private lemma pathConvex_top {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {W : Finset ℕ} (hW : PathConvex T W) :
    ∃ t ∈ W, ∀ v ∈ W, IsAncestor T r t v := by
  classical
  obtain ⟨t, htW, htmin⟩ := Finset.exists_min_image W (depth T r) hW.1
  refine ⟨t, htW, fun v hvW => ?_⟩
  have hl_mem : lca T r t v ∈ W :=
    hW.2.2 t htW v hvW (lca T r t v) (lca_mem_forestPath hT (hW.2.1 htW) (hW.2.1 hvW))
  have hl_t := lca_isAncestor_left hT (hW.2.1 htW) (hW.2.1 hvW)
  have hd_min := htmin _ hl_mem
  have hd_le := isAncestor_depth_le hT (hW.2.1 htW) hl_t
  have hl_eq : lca T r t v = t :=
    (isAncestor_eq_iff_depth hT (hW.2.1 htW) hl_t).mp (Nat.le_antisymm hd_le hd_min)
  have hl_v := lca_isAncestor_right hT (hW.2.1 htW) (hW.2.1 hvW)
  rwa [← hl_eq]

/-- Properties of the refinement `refineDecomp W_T F₀` of a Spielman–Teng decomposition `W_T`
by the connected components of `F₀ = F_{T₀}(R, π)` (`[chen2022maximum, Appendix B.3]`). -/
lemma refinement_decomp_spec {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    {R : Finset ℕ} (hR : IsBranchFree T₀ r₀ R) (hRne : R.Nonempty) (π : ℕ → ℕ)
    (W_T : Finset (Finset ℕ))
    (hW_pc : ∀ W₀ ∈ W_T, PathConvex T₀ W₀)
    (hW_disj : ∀ W₀₁ ∈ W_T, ∀ W₀₂ ∈ W_T, W₀₁ ≠ W₀₂ →
      Disjoint (inducedEdges T₀ W₀₁) (inducedEdges T₀ W₀₂))
    (hW_cov : W_T.biUnion (inducedEdges T₀) = T₀.E)
    (hBW_sub : boundary W_T ⊆ R)
    {bound : ℝ} (hVol_T : ∀ W₀ ∈ W_T, (G₀.vol (W₀ \ boundary W_T) : ℝ) ≤ bound) :
    let F₀ := forestGivenRoots T₀ r₀ R π
    let 𝒲 := refineDecomp W_T F₀
    (∀ W ∈ 𝒲, PathConvex T₀ W ∧ W ⊆ G₀.V ∧ (pieceBoundary 𝒲 W).card ≤ 1 ∧
      (G₀.vol (W \ R) : ℝ) ≤ bound) ∧
    boundary 𝒲 ⊆ boundary W_T ∧
    𝒲.biUnion (inducedEdges F₀) = F₀.E ∧
    (∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, W₁ ≠ W₂ → Disjoint (inducedEdges F₀ W₁) (inducedEdges F₀ W₂)) ∧
    𝒲.card ≤ W_T.card + R.card := by
  classical
  let F₀ := forestGivenRoots T₀ r₀ R π
  let RF₀ := rootedForestGivenRoots T₀ r₀ R π
  let 𝒲 := refineDecomp W_T F₀
  have hRS := forestGivenRoots_isRootedSpanningForest hT₀ hR hRne π
  have hF_sub : T₀.IsSubgraph F₀ := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have hW_mem : ∀ W ∈ 𝒲, ∃ W₀ ∈ W_T, ∃ K ∈ components F₀, W = W₀ ∩ K ∧ (inducedEdges F₀ W).Nonempty := by
    intro W hW
    simp only [𝒲, refineDecomp, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at hW
    obtain ⟨⟨p, hp, rfl⟩, hne⟩ := hW
    exact ⟨p.1, hp.1, p.2, hp.2, rfl, hne⟩
  have hcomp_disj : ∀ K₁ ∈ components F₀, ∀ K₂ ∈ components F₀,
      (K₁ ∩ K₂).Nonempty → K₁ = K₂ := by
    intro K₁ hK₁ K₂ hK₂ ⟨z, hz⟩
    rw [Finset.mem_inter] at hz
    rw [components, Finset.mem_image] at hK₁ hK₂
    obtain ⟨x₁, hx₁, rfl⟩ := hK₁
    obtain ⟨x₂, hx₂, rfl⟩ := hK₂
    rw [mem_compOf_iff] at hz
    have hz1 := hz.1.2
    rw [mem_compOf_iff] at hz
    exact compOf_eq_of_connected (connected_trans hz1 (connected_symm hz.2.2))
  have hb_sub : boundary 𝒲 ⊆ boundary W_T := by
    intro v hv
    rw [mem_boundary_iff] at hv
    obtain ⟨W₁, hW₁, W₂, hW₂, hne12, hv1, hv2⟩ := hv
    obtain ⟨W₀₁, h01, K₁, hK₁, rfl, _⟩ := hW_mem W₁ hW₁
    obtain ⟨W₀₂, h02, K₂, hK₂, rfl, _⟩ := hW_mem W₂ hW₂
    rw [Finset.mem_inter] at hv1 hv2
    have hK_eq : K₁ = K₂ := hcomp_disj K₁ hK₁ K₂ hK₂ ⟨v, Finset.mem_inter.mpr ⟨hv1.2, hv2.2⟩⟩
    have hW0_ne : W₀₁ ≠ W₀₂ := fun hEq => hne12 (by rw [hEq, hK_eq])
    exact mem_boundary_iff.mpr ⟨W₀₁, h01, W₀₂, h02, hW0_ne, hv1.1, hv2.1⟩
  have hW_props : ∀ W ∈ 𝒲, PathConvex T₀ W ∧ W ⊆ G₀.V ∧ (pieceBoundary 𝒲 W).card ≤ 1 ∧
      (G₀.vol (W \ R) : ℝ) ≤ bound := by
    intro W hW
    obtain ⟨W₀, h0, K, hK, rfl, ⟨e, he⟩⟩ := hW_mem W hW
    have hW_ne : (W₀ ∩ K).Nonempty := ⟨F₀.tail e, (Finset.mem_filter.mp he).2.1⟩
    rw [components, Finset.mem_image] at hK
    obtain ⟨x, hxF, rfl⟩ := hK
    have hpc : PathConvex T₀ (W₀ ∩ compOf F₀ x) :=
      (hW_pc W₀ h0).inter (pathConvex_compOf hT₀.isForest hRS.1 hF_sub hxF) hW_ne
    have hsubV : W₀ ∩ compOf F₀ x ⊆ G₀.V :=
      hTV ▸ Finset.Subset.trans Finset.inter_subset_left (hW_pc W₀ h0).2.1
    have hpb_card : (pieceBoundary 𝒲 (W₀ ∩ compOf F₀ x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [pieceBoundary, Finset.mem_inter] at ha hb
      have haR : a ∈ R := hBW_sub (hb_sub ha.2)
      have hbR : b ∈ R := hBW_sub (hb_sub hb.2)
      have haK := (Finset.mem_inter.mp ha.1).2
      have hbK := (Finset.mem_inter.mp hb.1).2
      rw [mem_compOf_iff] at haK hbK
      have hab : F₀.Connected a b := connected_trans (connected_symm haK.2) hbK.2
      have hroot_eq := (rootedForest_root_eq_iff hRS (hR.1 haR) (hR.1 hbR)).mpr hab
      rwa [rootedForest_root_self hRS haR, rootedForest_root_self hRS hbR] at hroot_eq
    have hvol_le : (G₀.vol ((W₀ ∩ compOf F₀ x) \ R) : ℝ) ≤ bound := by
      have hsub_set : (W₀ ∩ compOf F₀ x) \ R ⊆ W₀ \ boundary W_T := by
        intro v hv
        rw [Finset.mem_sdiff, Finset.mem_inter] at hv
        exact Finset.mem_sdiff.mpr ⟨hv.1.1, fun h => hv.2 (hBW_sub h)⟩
      have hle_nat : G₀.vol ((W₀ ∩ compOf F₀ x) \ R) ≤ G₀.vol (W₀ \ boundary W_T) :=
        Finset.sum_le_sum_of_subset hsub_set
      exact (Nat.cast_le.mpr hle_nat).trans (hVol_T W₀ h0)
    exact ⟨hpc, hsubV, hpb_card, hvol_le⟩
  have hcov_F : 𝒲.biUnion (inducedEdges F₀) = F₀.E := by
    apply Finset.Subset.antisymm
    · rw [Finset.biUnion_subset_iff_forall_subset]
      intro W _ e he
      exact (Finset.mem_filter.mp he).1
    · intro e heF
      have heT : e ∈ T₀.E := hF_sub.2.1 heF
      rw [← hW_cov, Finset.mem_biUnion] at heT
      obtain ⟨W₀, hW₀, heW₀⟩ := heT
      have huv := hRS.1.1 e heF
      let K := compOf F₀ (F₀.tail e)
      have hK_mem : K ∈ components F₀ := Finset.mem_image_of_mem _ huv.1
      have htail_K : F₀.tail e ∈ K := self_mem_compOf huv.1
      have hhead_K : F₀.head e ∈ K := mem_compOf_iff.mpr
        ⟨huv.2, ⟨[(e, true)], .cons heF rfl (.nil _)⟩⟩
      have htail_W0 := (Finset.mem_filter.mp heW₀).2.1
      have hhead_W0 := (Finset.mem_filter.mp heW₀).2.2
      rw [← (hF_sub.2.2 e heF).1] at htail_W0
      rw [← (hF_sub.2.2 e heF).2] at hhead_W0
      have he_inter : e ∈ inducedEdges F₀ (W₀ ∩ K) := Finset.mem_filter.mpr
        ⟨heF, Finset.mem_inter.mpr ⟨htail_W0, htail_K⟩,
          Finset.mem_inter.mpr ⟨hhead_W0, hhead_K⟩⟩
      refine Finset.mem_biUnion.mpr ⟨W₀ ∩ K, ?_, he_inter⟩
      simp only [𝒲, refineDecomp, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
      exact ⟨⟨(W₀, K), ⟨hW₀, hK_mem⟩, rfl⟩, ⟨e, he_inter⟩⟩
  have hdisj_F : ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, W₁ ≠ W₂ → Disjoint (inducedEdges F₀ W₁) (inducedEdges F₀ W₂) := by
    intro W₁ hW₁ W₂ hW₂ hne
    obtain ⟨W₀₁, h01, K₁, hK₁, rfl, _⟩ := hW_mem W₁ hW₁
    obtain ⟨W₀₂, h02, K₂, hK₂, rfl, _⟩ := hW_mem W₂ hW₂
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [inducedEdges, Finset.mem_filter, Finset.mem_inter, Finset.mem_inter] at he1 he2
    have hK_eq : K₁ = K₂ := hcomp_disj K₁ hK₁ K₂ hK₂ ⟨F₀.tail e, Finset.mem_inter.mpr ⟨he1.2.1.2, he2.2.1.2⟩⟩
    have hW0_ne : W₀₁ ≠ W₀₂ := fun hEq => hne (by rw [hEq, hK_eq])
    have he_T1 : e ∈ inducedEdges T₀ W₀₁ := Finset.mem_filter.mpr ⟨hF_sub.2.1 he1.1,
      (hF_sub.2.2 e he1.1).1 ▸ he1.2.1.1, (hF_sub.2.2 e he1.1).2 ▸ he1.2.2.1⟩
    have he_T2 : e ∈ inducedEdges T₀ W₀₂ := Finset.mem_filter.mpr ⟨hF_sub.2.1 he2.1,
      (hF_sub.2.2 e he2.1).1 ▸ he2.2.1.1, (hF_sub.2.2 e he2.1).2 ▸ he2.2.2.1⟩
    exact Finset.disjoint_left.mp (hW_disj W₀₁ h01 W₀₂ h02 hW0_ne) he_T1 he_T2
  have hcard_le : 𝒲.card ≤ W_T.card + R.card := by
    let chooseW0 : Finset ℕ → Finset ℕ := fun W =>
      if h : W ∈ 𝒲 then (hW_mem W h).choose else ∅
    let chooseK : Finset ℕ → Finset ℕ := fun W =>
      if h : W ∈ 𝒲 then (hW_mem W h).choose_spec.2.choose else ∅
    have hchoose_spec : ∀ W (hW : W ∈ 𝒲),
        chooseW0 W ∈ W_T ∧ chooseK W ∈ components F₀ ∧ W = chooseW0 W ∩ chooseK W ∧
        (inducedEdges F₀ W).Nonempty := by
      intro W hW
      have h1 : chooseW0 W = (hW_mem W hW).choose := dite_eq_left_of_eq_true (eq_true hW)
      have h2 : chooseK W = (hW_mem W hW).choose_spec.2.choose :=
        dite_eq_left_of_eq_true (eq_true hW)
      rw [h1, h2]
      exact ⟨(hW_mem W hW).choose_spec.1, (hW_mem W hW).choose_spec.2.choose_spec⟩
    let topOf : Finset ℕ → ℕ := fun S =>
      if h : PathConvex T₀ S then Classical.choose (pathConvex_top hT₀ h) else r₀
    have htop_spec : ∀ S (hS : PathConvex T₀ S),
        topOf S ∈ S ∧ ∀ v ∈ S, IsAncestor T₀ r₀ (topOf S) v := by
      intro S hS
      have : topOf S = Classical.choose (pathConvex_top hT₀ hS) :=
        dite_eq_left_of_eq_true (eq_true hS)
      rw [this]
      exact Classical.choose_spec (pathConvex_top hT₀ hS)
    have htop_K_mem : ∀ W (hW : W ∈ 𝒲), topOf W ∈ chooseK W := by
      intro W hW
      have ht : topOf W ∈ chooseW0 W ∩ chooseK W := by
        rw [← (hchoose_spec W hW).2.2.1]; exact (htop_spec W (hW_props W hW).1).1
      exact (Finset.mem_inter.mp ht).2
    have hK_eq_conn : ∀ K₁ ∈ components F₀, ∀ K₂ ∈ components F₀,
        ∀ a ∈ K₁, ∀ b ∈ K₂, F₀.Connected a b → K₁ = K₂ := by
      intro K₁ hK₁ K₂ hK₂ a ha b hb hab
      rw [components, Finset.mem_image] at hK₁ hK₂
      obtain ⟨x₁, hx₁, rfl⟩ := hK₁
      obtain ⟨x₂, hx₂, rfl⟩ := hK₂
      rw [mem_compOf_iff] at ha hb
      exact compOf_eq_of_connected (connected_trans ha.2 (connected_trans hab (connected_symm hb.2)))
    let W_root := 𝒲.filter (fun W => F₀.Connected (topOf W) (topOf (chooseW0 W)))
    let W_other := 𝒲.filter (fun W => ¬ F₀.Connected (topOf W) (topOf (chooseW0 W)))
    have hW_root_card : W_root.card ≤ W_T.card := by
      refine Finset.card_le_card_of_injOn chooseW0 (fun W hW => (hchoose_spec W (Finset.mem_filter.mp hW).1).1) ?_
      intro W₁ h1 W₂ h2 hEq
      have h1f := Finset.mem_filter.mp h1
      have h2f := Finset.mem_filter.mp h2
      have hconn : F₀.Connected (topOf W₁) (topOf W₂) :=
        connected_trans h1f.2 (connected_symm (hEq ▸ h2f.2))
      have hK_eq := hK_eq_conn _ (hchoose_spec W₁ h1f.1).2.1 _ (hchoose_spec W₂ h2f.1).2.1
        _ (htop_K_mem W₁ h1f.1) _ (htop_K_mem W₂ h2f.1) hconn
      rw [(hchoose_spec W₁ h1f.1).2.2.1, (hchoose_spec W₂ h2f.1).2.2.1, hEq, hK_eq]
    let D := deletedEdges T₀ r₀ R π
    have h_del_ex : ∀ W (hW : W ∈ W_other),
        ∃ x ∈ T₀.forestPath (topOf W) (topOf (chooseW0 W)),
          x.1 ∈ D ∧ F₀.Connected (topOf W) (T₀.src x) := by
      intro W hW
      have hf := Finset.mem_filter.mp hW
      have hcs := hchoose_spec W hf.1
      have htW_V : topOf W ∈ T₀.V := (hW_props W hf.1).1.2.1 (htop_spec W (hW_props W hf.1).1).1
      have ht0_V : topOf (chooseW0 W) ∈ T₀.V :=
        (hW_pc _ hcs.1).2.1 (htop_spec _ (hW_pc _ hcs.1)).1
      have hP := forestPath_isPath hT₀.isForest (hT₀.connected htW_V ht0_V)
      exact firstDeleted_spec (T := T₀) (F := F₀) (D := D) rfl rfl rfl hP.1 hf.2
    let delStep : Finset ℕ → ℕ × Bool := fun W =>
      if h : W ∈ W_other then (h_del_ex W h).choose else (0, true)
    have hdelStep_spec : ∀ W (hW : W ∈ W_other),
        delStep W ∈ T₀.forestPath (topOf W) (topOf (chooseW0 W)) ∧
          (delStep W).1 ∈ D ∧ F₀.Connected (topOf W) (T₀.src (delStep W)) := by
      intro W hW
      have : delStep W = (h_del_ex W hW).choose := dite_eq_left_of_eq_true (eq_true hW)
      rw [this]
      exact (h_del_ex W hW).choose_spec
    have hW_other_card : W_other.card ≤ D.card := by
      refine Finset.card_le_card_of_injOn (fun W => (delStep W).1)
        (fun W hW => (hdelStep_spec W hW).2.1) ?_
      intro W₁ h1 W₂ h2 hEq
      dsimp only at hEq
      have hs₁ := hdelStep_spec W₁ h1
      have hs₂ := hdelStep_spec W₂ h2
      have h1f := Finset.mem_filter.mp h1
      have h2f := Finset.mem_filter.mp h2
      have hcs₁ := hchoose_spec W₁ h1f.1
      have hcs₂ := hchoose_spec W₂ h2f.1
      have hpc₀₁ := hW_pc _ hcs₁.1
      have hpc₀₂ := hW_pc _ hcs₂.1
      have htW₁ : topOf W₁ ∈ chooseW0 W₁ := by
        have ht : topOf W₁ ∈ chooseW0 W₁ ∩ chooseK W₁ := by
          rw [← hcs₁.2.2.1]; exact (htop_spec W₁ (hW_props W₁ h1f.1).1).1
        exact (Finset.mem_inter.mp ht).1
      have htW₂ : topOf W₂ ∈ chooseW0 W₂ := by
        have ht : topOf W₂ ∈ chooseW0 W₂ ∩ chooseK W₂ := by
          rw [← hcs₂.2.2.1]; exact (htop_spec W₂ (hW_props W₂ h2f.1).1).1
        exact (Finset.mem_inter.mp ht).1
      have hanc₁ : IsAncestor T₀ r₀ (topOf (chooseW0 W₁)) (topOf W₁) :=
        (htop_spec _ hpc₀₁).2 _ htW₁
      have hanc₂ : IsAncestor T₀ r₀ (topOf (chooseW0 W₂)) (topOf W₂) :=
        (htop_spec _ hpc₀₂).2 _ htW₂
      have hd₁ := ancestorPath_step_depth hT₀ (depth T₀ r₀ (topOf W₁)) _ rfl
        (hpc₀₁.2.1 htW₁) hanc₁ _ hs₁.1
      have hd₂ := ancestorPath_step_depth hT₀ (depth T₀ r₀ (topOf W₂)) _ rfl
        (hpc₀₂.2.1 htW₂) hanc₂ _ hs₂.1
      have he₁T : (delStep W₁).1 ∈ T₀.E :=
        IsWalk_edges_mem (forestPath_isPath hT₀.isForest (hT₀.connected (hpc₀₁.2.1 htW₁)
          (hpc₀₁.2.1 (htop_spec _ hpc₀₁).1))).1 hs₁.1
      have he₂T : (delStep W₂).1 ∈ T₀.E :=
        IsWalk_edges_mem (forestPath_isPath hT₀.isForest (hT₀.connected (hpc₀₂.2.1 htW₂)
          (hpc₀₂.2.1 (htop_spec _ hpc₀₂).1))).1 hs₂.1
      have hsrc_eq := src_eq_of_step_depth_eq he₁T he₂T hEq hd₁ hd₂
      have hconn_top : F₀.Connected (topOf W₁) (topOf W₂) :=
        connected_trans hs₁.2.2 (hsrc_eq ▸ connected_symm hs₂.2.2)
      have hK_eq := hK_eq_conn _ hcs₁.2.1 _ hcs₂.2.1 _ (htop_K_mem W₁ h1f.1) _
        (htop_K_mem W₂ h2f.1) hconn_top
      have h_in_ind : ∀ {W : Finset ℕ} (hW : W ∈ W_other),
          (delStep W).1 ∈ inducedEdges T₀ (chooseW0 W) := by
        intro W hW
        have hWf := Finset.mem_filter.mp hW
        have hcs := hchoose_spec W hWf.1
        have hpc₀ := hW_pc _ hcs.1
        have htW : topOf W ∈ chooseW0 W := by
          have ht : topOf W ∈ chooseW0 W ∩ chooseK W := by
            rw [← hcs.2.2.1]; exact (htop_spec W (hW_props W hWf.1).1).1
          exact (Finset.mem_inter.mp ht).1
        have hsW := hdelStep_spec W hW
        have hsub_ind := (pathConvex_edges_between_mem hT₀.isForest hpc₀
          (fun a ha b hb => hT₀.connected (hpc₀.2.1 ha) (hpc₀.2.1 hb))
          htW (htop_spec _ hpc₀).1 (fun h => by
            have hd := hsW.1; rw [h, forestPath_self hT₀.isForest] at hd; simp at hd)).2
        exact hsub_ind (List.mem_toFinset.mpr (List.mem_map.mpr ⟨delStep W, hsW.1, rfl⟩))
      have hW0_eq : chooseW0 W₁ = chooseW0 W₂ := by
        by_contra hne0
        have he1 := h_in_ind h1
        have he2 := h_in_ind h2
        rw [← hEq] at he2
        exact Finset.disjoint_left.mp (hW_disj _ hcs₁.1 _ hcs₂.1 hne0) he1 he2
      rw [hcs₁.2.2.1, hcs₂.2.2.1, hW0_eq, hK_eq]
    have hD_card : D.card ≤ R.card := by
      have h1 := deletedEdges_card hT₀ hR hRne π
      change D.card + 1 = R.card at h1
      omega
    have hsub_union : 𝒲 ⊆ W_root ∪ W_other := by
      intro W hW
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hc : F₀.Connected (topOf W) (topOf (chooseW0 W))
      · exact Or.inl ⟨hW, hc⟩
      · exact Or.inr ⟨hW, hc⟩
    have hcard_u := (Finset.card_le_card hsub_union).trans (Finset.card_union_le W_root W_other)
    omega
  exact ⟨hW_props, hb_sub, hcov_F, hdisj_F, hcard_le⟩

end MinCostFlow.LSF

