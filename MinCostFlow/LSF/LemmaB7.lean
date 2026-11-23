module

public import MinCostFlow.LSF.TreeDecomp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma B.7 (`[chen2022maximum]` Spielman–Teng Tree Decomposition)

This file derives `lemma_B_7` from `treeDecompSub` (`MinCostFlow.LSF.TreeDecomp`):
Given a valid graph `G`, nonnegative edge weights `w : ℕ → ℝ`, a spanning tree `T` on `G.V`
rooted at `r` with `2 ≤ G.V.card`, and parameter `0 < k`, there is an edge-disjoint decomposition
`𝒲` of `T` into path-convex subtrees covering `T.V` and `T.E` such that:
1. `𝒲.card ≤ 6 * (G.E.card : ℝ) / k + 6`.
2. `(boundary 𝒲).card ≤ 2 * (G.E.card : ℝ) / k` and `boundary 𝒲` is branch-free in `(T, r)`.
3. For every piece `C ∈ 𝒲`, the total `w`-weight of edges of `G` with an endpoint in `C \ boundary 𝒲`
   is at most `40 * (∑ e ∈ G.E, w e) * k / G.E.card`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

private lemma exists_incident_tree_edge {T : MGraph} {r v : ℕ} (hT : IsRootedTree T r)
    (hV2 : 2 ≤ T.V.card) (hv : v ∈ T.V) :
    ∃ e ∈ T.E, v = T.tail e ∨ v = T.head e := by
  by_cases hvr : v = r
  · subst hvr
    have her : (T.V.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
      omega
    obtain ⟨y, hy⟩ := her
    rw [Finset.mem_erase] at hy
    have hP := forestPath_isPath hT.isForest (hT.connected hv hy.2)
    rcases hEq : T.forestPath v y with _ | ⟨x, xs⟩
    · rw [hEq] at hP
      cases hP.1 with
      | nil _ => exact absurd rfl hy.1
    · have hw := hP.1
      rw [hEq] at hw
      cases hw with
      | cons hx hs _ =>
        refine ⟨x.1, hx, ?_⟩
        rcases x with ⟨e, b⟩
        cases b <;> dsimp [MGraph.src] at hs
        · exact Or.inr hs.symm
        · exact Or.inl hs.symm
  · refine ⟨parentEdge T r v, parentEdge_mem hT hv hvr, ?_⟩
    have hend := parentEdge_endpoints hT hv hvr
    have hmem : v ∈ ({T.tail (parentEdge T r v), T.head (parentEdge T r v)} : Set ℕ) := by
      rw [hend]; exact Set.mem_insert _ _
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

private lemma pathConvex_full (T : MGraph) (hT : T.IsForest) (hV : T.V.Nonempty)
    (hconn : ∀ u ∈ T.V, ∀ v ∈ T.V, T.Connected u v) :
    PathConvex T T.V := by
  refine ⟨hV, Finset.Subset.refl _, fun u hu v hv w hw => ?_⟩
  exact (IsWalk_vertices_mem hT.1 hu (forestPath_isPath hT (hconn u hu v hv)).1).2 w hw

private lemma pathConvex_singleton {T : MGraph} (hT : T.IsForest) {u : ℕ} (hu : u ∈ T.V) :
    PathConvex T {u} := by
  refine ⟨⟨u, Finset.mem_singleton_self u⟩, Finset.singleton_subset_iff.mpr hu, fun a ha b hb w hw => ?_⟩
  rw [Finset.mem_singleton] at ha hb
  rw [ha, hb, forestPath_self hT u, MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
  exact Finset.mem_singleton.mpr hw

private lemma inducedEdges_singleton_empty {T : MGraph} (hT : T.IsForest) (u : ℕ) :
    inducedEdges T {u} = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  rw [inducedEdges, Finset.mem_filter, Finset.mem_singleton, Finset.mem_singleton] at he
  exact isForest_no_selfLoop hT he.1 (he.2.1.trans he.2.2.symm)

private lemma inducedEdges_full {T : MGraph} (hT : T.IsValid) :
    inducedEdges T T.V = T.E := by
  apply Finset.ext
  intro e
  simp only [inducedEdges, Finset.mem_filter, and_iff_left_iff_imp]
  intro he
  exact hT e he

private lemma subtree_root_eq {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    subtree T r r = T.V := by
  apply Finset.ext
  intro v
  rw [mem_subtree_iff]
  exact ⟨fun h => h.1, fun hv => ⟨hv, isAncestor_root hT hv⟩⟩

/-- **Lemma B.7** (`[chen2022maximum, Lemma B.7]`, Spielman–Teng Tree Decomposition):
Given a valid graph `G`, nonnegative edge weights `w`, a rooted spanning tree `(T, r)` on `G.V`
with `2 ≤ G.V.card`, and a threshold parameter `0 < k`, there exists a decomposition `𝒲` of `T`
into path-convex subtrees covering all vertices and edges of `T`, with edge-disjoint pieces, such that:
- `𝒲.card ≤ 6 * G.E.card / k + 6`,
- `(boundary 𝒲).card ≤ 2 * G.E.card / k` and `boundary 𝒲` is branch-free in `(T, r)`,
- every piece `C ∈ 𝒲` has incident non-boundary weight at most `40 * (∑ e ∈ G.E, w e) * k / G.E.card`. -/
lemma lemma_B_7 {G T : MGraph} {r : ℕ} (hG : G.IsValid) (hT : IsRootedTree T r)
    (hTV : T.V = G.V) (hV2 : 2 ≤ G.V.card)
    (w : ℕ → ℝ) (hw : ∀ e ∈ G.E, 0 ≤ w e) (k : ℝ) (hk : 0 < k) :
    ∃ 𝒲 : Finset (Finset ℕ),
      (∀ C ∈ 𝒲, PathConvex T C) ∧
      (∀ C₁ ∈ 𝒲, ∀ C₂ ∈ 𝒲, C₁ ≠ C₂ → Disjoint (inducedEdges T C₁) (inducedEdges T C₂)) ∧
      𝒲.biUnion (inducedEdges T) = T.E ∧
      𝒲.biUnion id = T.V ∧
      (𝒲.card : ℝ) ≤ 6 * (G.E.card : ℝ) / k + 6 ∧
      (boundary 𝒲).card ≤ 2 * (G.E.card : ℝ) / k ∧
      IsBranchFree T r (boundary 𝒲) ∧
      (∀ C ∈ 𝒲,
        ∑ e ∈ G.E.filter (fun e =>
            (G.tail e ∈ C ∧ G.tail e ∉ boundary 𝒲) ∨
            (G.head e ∈ C ∧ G.head e ∉ boundary 𝒲)), w e ≤
          40 * (∑ e ∈ G.E, w e) * k / (G.E.card : ℝ)) := by
  classical
  let W₁ : ℝ := ∑ e ∈ G.E, w e
  have hW₁_nonneg : 0 ≤ W₁ := Finset.sum_nonneg hw
  by_cases hW₁_pos : 0 < W₁
  · have hE_ne : G.E.Nonempty := by
      by_contra hE
      rw [Finset.not_nonempty_iff_eq_empty] at hE
      have h0 : W₁ = 0 := by dsimp only [W₁]; rw [hE, Finset.sum_empty]
      linarith
    have hm_pos : (0 : ℝ) < (G.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE_ne)
    let θ : ℝ := 4 * W₁ * k / (G.E.card : ℝ)
    have hθ : 0 < θ := by positivity
    let H : Finset ℕ := G.V.filter (fun v => θ < vWeight G w v)
    let ν : ℕ → ℝ := fun v => if v ∈ H then 0 else vWeight G w v
    have hν : ∀ v ∈ T.V, 0 ≤ ν v := by
      intro v _
      dsimp only [ν]
      split_ifs
      · exact le_rfl
      · exact vWeight_nonneg hw v
    have hν_le : ∀ v ∈ T.V, ν v ≤ θ := by
      intro v hv
      dsimp only [ν]
      split_ifs with hvH
      · exact le_of_lt hθ
      · rw [Finset.mem_filter] at hvH
        by_contra hlt
        exact hvH ⟨hTV ▸ hv, lt_of_not_ge hlt⟩
    have hsub_r : subtree T r r ⊆ T.V := fun _ hx => (mem_subtree_iff.mp hx).1
    have hsub_card : (subtree T r r).card ≤ T.V.card := Finset.card_le_card hsub_r
    obtain ⟨𝒲_r, B_r, hB_pc, hr_B, _, hB_sum, hW_spec, hW_disj, hB_disj, hcov, hcount⟩ :=
      treeDecompSub hT ν hν θ hθ hν_le T.V.card r hsub_card hT.2
    rw [subtree_root_eq hT, inducedEdges_full hT.isForest.1] at hcov
    rw [subtree_root_eq hT] at hcount
    let 𝒲₁ : Finset (Finset ℕ) := if B_r = {r} then 𝒲_r else insert B_r 𝒲_r
    have hW₁_pc : ∀ C ∈ 𝒲₁, PathConvex T C ∧ (inducedEdges T C).Nonempty ∧ (∑ x ∈ C, ν x < 4 * θ) := by
      intro C hC
      dsimp only [𝒲₁] at hC
      split_ifs at hC with hBr
      · exact ⟨(hW_spec C hC).1, (hW_spec C hC).2.2.1, (hW_spec C hC).2.2.2⟩
      · rw [Finset.mem_insert] at hC
        rcases hC with hEq | hCr
        · rw [hEq]
          have hex : ∃ x ∈ B_r, x ≠ r := by
            by_contra hnone
            apply hBr
            apply Finset.ext
            intro x
            rw [Finset.mem_singleton]
            exact ⟨fun hx => by by_contra hne; exact hnone ⟨x, hx, hne⟩, fun h => h ▸ hr_B⟩
          obtain ⟨x, hxB, hxr⟩ := hex
          have hconn : ∀ a ∈ B_r, ∀ b ∈ B_r, T.Connected a b :=
            fun a ha b hb => hT.connected (hB_pc.2.1 ha) (hB_pc.2.1 hb)
          obtain ⟨⟨e, he⟩, hsub_e⟩ := pathConvex_edges_between_mem hT.isForest hB_pc hconn hxB hr_B hxr
          exact ⟨hB_pc, ⟨e, hsub_e he⟩, by linarith⟩
        · exact ⟨(hW_spec C hCr).1, (hW_spec C hCr).2.2.1, (hW_spec C hCr).2.2.2⟩
    have hW₁_disj : ∀ C₁ ∈ 𝒲₁, ∀ C₂ ∈ 𝒲₁, C₁ ≠ C₂ → Disjoint (inducedEdges T C₁) (inducedEdges T C₂) := by
      intro C₁ hC₁ C₂ hC₂ hne
      dsimp only [𝒲₁] at hC₁ hC₂
      split_ifs at hC₁ hC₂
      · exact hW_disj C₁ hC₁ C₂ hC₂ hne
      · rw [Finset.mem_insert] at hC₁ hC₂
        rcases hC₁ with rfl | h1 <;> rcases hC₂ with rfl | h2
        · exact absurd rfl hne
        · exact (hB_disj C₂ h2).symm
        · exact hB_disj C₁ h1
        · exact hW_disj C₁ h1 C₂ h2 hne
    have hW₁_cov : 𝒲₁.biUnion (inducedEdges T) = T.E := by
      dsimp only [𝒲₁]
      split_ifs with hBr
      · have hE_empty : inducedEdges T B_r = ∅ := by
          rw [hBr]; exact inducedEdges_singleton_empty hT.isForest r
        rwa [hE_empty, Finset.union_empty] at hcov
      · rw [Finset.biUnion_insert, Finset.union_comm, hcov]
    have hTV2 : 2 ≤ T.V.card := hTV ▸ hV2
    have hTE_ne : T.E.Nonempty := by
      obtain ⟨e, he, _⟩ := exists_incident_tree_edge hT hTV2 hT.2
      exact ⟨e, he⟩
    have hW₁_ne : 𝒲₁.Nonempty := by
      obtain ⟨e, he⟩ := hTE_ne
      rw [← hW₁_cov, Finset.mem_biUnion] at he
      obtain ⟨C, hC, _⟩ := he
      exact ⟨C, hC⟩
    have h_sum_nu_le : ∑ x ∈ T.V \ B_r, ν x ≤ 2 * W₁ := by
      have hsub : ∑ x ∈ T.V \ B_r, ν x ≤ ∑ x ∈ T.V, ν x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun v hv _ => hν v hv)
      have hle_vw : ∀ v ∈ T.V, ν v ≤ vWeight G w v := by
        intro v _
        dsimp only [ν]
        split_ifs
        · exact vWeight_nonneg hw v
        · exact le_rfl
      have h2 : ∑ v ∈ T.V, ν v ≤ 2 * W₁ := by
        have hsum_le := Finset.sum_le_sum hle_vw
        have hvw : ∑ v ∈ T.V, vWeight G w v = 2 * W₁ := by rw [hTV, sum_vWeight hG w]
        exact hsum_le.trans_eq hvw
      exact hsub.trans h2
    have hWr_card : (𝒲_r.card : ℝ) ≤ (G.E.card : ℝ) / (2 * k) := by
      have hprod : θ * (𝒲_r.card : ℝ) ≤ 2 * W₁ := hcount.trans h_sum_nu_le
      have h1 : (2 * W₁) * ((𝒲_r.card : ℝ) * (2 * k)) ≤ (2 * W₁) * (G.E.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hprod (le_of_lt hm_pos)
        dsimp only [θ] at hmul
        rw [mul_right_comm _ (𝒲_r.card : ℝ) (G.E.card : ℝ),
            div_mul_cancel₀ _ (ne_of_gt hm_pos)] at hmul
        linarith [show (2 * W₁) * ((𝒲_r.card : ℝ) * (2 * k)) = 4 * W₁ * k * (𝒲_r.card : ℝ) by ring]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
        (le_of_mul_le_mul_left h1 (by positivity))
    have hH_card : (H.card : ℝ) ≤ (G.E.card : ℝ) / (2 * k) := by
      have hsum_H : θ * (H.card : ℝ) ≤ ∑ v ∈ H, vWeight G w v := by
        have h1 : θ * (H.card : ℝ) = ∑ _v ∈ H, θ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        rw [h1]
        exact Finset.sum_le_sum (fun v hv => le_of_lt (Finset.mem_filter.mp hv).2)
      have hsum_V : ∑ v ∈ H, vWeight G w v ≤ 2 * W₁ := by
        have h1 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun v => θ < vWeight G w v) G.V)
          (fun v _ _ => vWeight_nonneg hw v)
        rwa [sum_vWeight hG w] at h1
      have hprod := hsum_H.trans hsum_V
      have h1 : (2 * W₁) * ((H.card : ℝ) * (2 * k)) ≤ (2 * W₁) * (G.E.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hprod (le_of_lt hm_pos)
        dsimp only [θ] at hmul
        rw [mul_right_comm _ (H.card : ℝ) (G.E.card : ℝ),
            div_mul_cancel₀ _ (ne_of_gt hm_pos)] at hmul
        linarith [show (2 * W₁) * ((H.card : ℝ) * (2 * k)) = 4 * W₁ * k * (H.card : ℝ) by ring]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
        (le_of_mul_le_mul_left h1 (by positivity))
    have hbW₁_card_nat : (boundary 𝒲₁).card ≤ 𝒲_r.card := by
      have hb_lt := boundary_card_lt hT 𝒲₁.card 𝒲₁ rfl hW₁_ne
        (fun C hC => (hW₁_pc C hC).1) hW₁_disj
      have hW₁_card : 𝒲₁.card ≤ 𝒲_r.card + 1 := by
        dsimp only [𝒲₁]
        split_ifs
        · exact Nat.le_succ _
        · exact Finset.card_insert_le _ _
      omega
    have hbW₁_card : ((boundary 𝒲₁).card : ℝ) ≤ (G.E.card : ℝ) / (2 * k) :=
      (Nat.cast_le.mpr hbW₁_card_nat).trans hWr_card
    have hS_sub : boundary 𝒲₁ ∪ H ⊆ T.V := by
      rw [Finset.union_subset_iff]
      constructor
      · intro v hv
        rw [mem_boundary_iff] at hv
        obtain ⟨A, hA, _, _, _, hvA, _⟩ := hv
        exact (hW₁_pc A hA).1.2.1 hvA
      · exact hTV.symm ▸ Finset.filter_subset _ G.V
    let R : Finset ℕ := lcaClosure T r (boundary 𝒲₁ ∪ H)
    have hR_sub : R ⊆ T.V := lcaClosure_subset hT hS_sub
    have hm2k : (G.E.card : ℝ) / (2 * k) = ((G.E.card : ℝ) / k) / 2 := by ring
    have hR_card : (R.card : ℝ) ≤ 2 * (G.E.card : ℝ) / k := by
      have h1 := (lcaClosure_card_le hT hS_sub).1
      have h2 : (boundary 𝒲₁ ∪ H).card ≤ (boundary 𝒲₁).card + H.card := Finset.card_union_le _ _
      have h3 : (R.card : ℝ) ≤ 2 * (((boundary 𝒲₁).card : ℝ) + (H.card : ℝ)) := by
        dsimp only [R]
        exact_mod_cast (by omega : (lcaClosure T r (boundary 𝒲₁ ∪ H)).card ≤ 2 * ((boundary 𝒲₁).card + H.card))
      rw [hm2k] at hbW₁_card hH_card
      calc (R.card : ℝ)
          ≤ 2 * (((boundary 𝒲₁).card : ℝ) + (H.card : ℝ)) := h3
        _ ≤ 2 * (((G.E.card : ℝ) / k) / 2 + ((G.E.card : ℝ) / k) / 2) := by linarith
        _ = 2 * (G.E.card : ℝ) / k := by ring
    let 𝒲 : Finset (Finset ℕ) := 𝒲₁ ∪ R.image (fun u => {u})
    have hb_eq : boundary 𝒲 = R := by
      apply Finset.ext
      intro u
      rw [mem_boundary_iff]
      constructor
      · rintro ⟨A, hA, B, hB, hneAB, huA, huB⟩
        rw [Finset.mem_union, Finset.mem_image] at hA hB
        rcases hA with hA1 | ⟨a, haR, rfl⟩
        · rcases hB with hB1 | ⟨b, hbR, rfl⟩
          · exact subset_lcaClosure hT hS_sub
              (Finset.mem_union_left _ (mem_boundary_iff.mpr ⟨A, hA1, B, hB1, hneAB, huA, huB⟩))
          · rw [Finset.mem_singleton] at huB
            exact huB ▸ hbR
        · rw [Finset.mem_singleton] at huA
          exact huA ▸ haR
      · intro huR
        have huV := hR_sub huR
        obtain ⟨e, heT, hu_end⟩ := exists_incident_tree_edge hT hTV2 huV
        rw [← hW₁_cov, Finset.mem_biUnion] at heT
        obtain ⟨P, hP, heP⟩ := heT
        have huP : u ∈ P := by
          rw [inducedEdges, Finset.mem_filter] at heP
          rcases hu_end with h | h <;> rw [h] <;> [exact heP.2.1; exact heP.2.2]
        have hP_ne_sing : P ≠ {u} := by
          intro hEq
          rw [hEq, inducedEdges_singleton_empty hT.isForest u] at heP
          exact Finset.notMem_empty e heP
        refine ⟨P, Finset.mem_union_left _ hP, {u},
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ huR), hP_ne_sing,
          huP, Finset.mem_singleton_self u⟩
    refine ⟨𝒲, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro C hC
      rw [Finset.mem_union, Finset.mem_image] at hC
      rcases hC with hC1 | ⟨u, huR, rfl⟩
      · exact (hW₁_pc C hC1).1
      · exact pathConvex_singleton hT.isForest (hR_sub huR)
    · intro C₁ hC₁ C₂ hC₂ hne
      rw [Finset.mem_union, Finset.mem_image] at hC₁ hC₂
      rcases hC₁ with h1 | ⟨u, _, rfl⟩ <;> rcases hC₂ with h2 | ⟨v, _, rfl⟩
      · exact hW₁_disj C₁ h1 C₂ h2 hne
      · rw [inducedEdges_singleton_empty hT.isForest v]
        exact Finset.disjoint_empty_right _
      · rw [inducedEdges_singleton_empty hT.isForest u]
        exact Finset.disjoint_empty_left _
      · rw [inducedEdges_singleton_empty hT.isForest u]
        exact Finset.disjoint_empty_left _
    · apply Finset.Subset.antisymm
      · rw [Finset.biUnion_subset_iff_forall_subset]
        intro C hC
        rw [Finset.mem_union, Finset.mem_image] at hC
        rcases hC with hC1 | ⟨u, _, rfl⟩
        · rw [← hW₁_cov]
          exact Finset.subset_biUnion_of_mem (inducedEdges T) hC1
        · rw [inducedEdges_singleton_empty hT.isForest u]
          exact Finset.empty_subset _
      · rw [← hW₁_cov]
        exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
    · apply Finset.Subset.antisymm
      · rw [Finset.biUnion_subset_iff_forall_subset]
        intro C hC
        rw [Finset.mem_union, Finset.mem_image] at hC
        rcases hC with hC1 | ⟨u, huR, rfl⟩
        · exact (hW₁_pc C hC1).1.2.1
        · exact Finset.singleton_subset_iff.mpr (hR_sub huR)
      · intro v hv
        obtain ⟨e, heT, hv_end⟩ := exists_incident_tree_edge hT hTV2 hv
        rw [← hW₁_cov, Finset.mem_biUnion] at heT
        obtain ⟨P, hP, heP⟩ := heT
        rw [inducedEdges, Finset.mem_filter] at heP
        refine Finset.mem_biUnion.mpr ⟨P, Finset.mem_union_left _ hP, ?_⟩
        rcases hv_end with h | h <;> rw [h] <;> [exact heP.2.1; exact heP.2.2]
    · have hW₁_card_real : (𝒲₁.card : ℝ) ≤ (G.E.card : ℝ) / (2 * k) + 1 := by
        have hnat : 𝒲₁.card ≤ 𝒲_r.card + 1 := by
          dsimp only [𝒲₁]
          split_ifs
          · omega
          · exact Finset.card_insert_le _ _
        exact (Nat.cast_le.mpr hnat).trans (by push_cast; linarith)
      have hcard_union : (𝒲.card : ℝ) ≤ (𝒲₁.card : ℝ) + (R.card : ℝ) := by
        have h1 : 𝒲.card ≤ 𝒲₁.card + (R.image (fun u => ({u} : Finset ℕ))).card :=
          Finset.card_union_le 𝒲₁ (R.image fun u => {u})
        have h2 : (R.image (fun u => ({u} : Finset ℕ))).card ≤ R.card := Finset.card_image_le
        exact_mod_cast (by omega : 𝒲.card ≤ 𝒲₁.card + R.card)
      have hmk_nonneg : 0 ≤ (G.E.card : ℝ) / k := by positivity
      calc (𝒲.card : ℝ)
          ≤ (𝒲₁.card : ℝ) + (R.card : ℝ) := hcard_union
        _ ≤ ((G.E.card : ℝ) / (2 * k) + 1) + 2 * (G.E.card : ℝ) / k := add_le_add hW₁_card_real hR_card
        _ = (5 / 2 : ℝ) * ((G.E.card : ℝ) / k) + 1 := by ring
        _ ≤ 6 * (G.E.card : ℝ) / k + 6 := by
          have h5 : (5 / 2 : ℝ) * ((G.E.card : ℝ) / k) ≤ 6 * ((G.E.card : ℝ) / k) := by linarith
          linarith [mul_div_assoc (6 : ℝ) (G.E.card : ℝ) k]
    · rw [hb_eq]; exact hR_card
    · rw [hb_eq]; exact lcaClosure_isBranchFree hT hS_sub
    · intro C hC
      have hstep := sum_nonboundary_edges_le_vWeight hw C (boundary 𝒲)
      rw [hb_eq] at hstep ⊢
      rw [Finset.mem_union, Finset.mem_image] at hC
      rcases hC with hC1 | ⟨u, huR, rfl⟩
      · have hv_eq : ∀ v ∈ C \ R, vWeight G w v = ν v := by
          intro v hv
          rw [Finset.mem_sdiff] at hv
          have hvH : v ∉ H := fun h => hv.2 (subset_lcaClosure hT hS_sub (Finset.mem_union_right _ h))
          dsimp only [ν]
          exact (ite_eq_right_iff.mpr (fun h => absurd h hvH)).symm
        have hsum_eq : ∑ v ∈ C \ R, vWeight G w v = ∑ v ∈ C \ R, ν v := Finset.sum_congr rfl hv_eq
        have hsum_sub : ∑ v ∈ C \ R, ν v ≤ ∑ v ∈ C, ν v :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            (fun v hv _ => hν v ((hW₁_pc C hC1).1.2.1 hv))
        have h4θ : 4 * θ = 16 * W₁ * k / (G.E.card : ℝ) := by
          dsimp only [θ]; ring
        have h16_le : 16 * W₁ * k / (G.E.card : ℝ) ≤ 40 * W₁ * k / (G.E.card : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hm_pos)
          have : 0 ≤ W₁ * k := by positivity
          rw [mul_assoc 16, mul_assoc 40]
          linarith
        exact hstep.trans (hsum_eq ▸ hsum_sub.trans (le_of_lt (hW₁_pc C hC1).2.2 |>.trans (h4θ ▸ h16_le)))
      · have hdiff : ({u} \ R : Finset ℕ) = ∅ := by
          rw [Finset.sdiff_eq_empty_iff_subset, Finset.singleton_subset_iff]
          exact huR
        rw [hdiff, Finset.sum_empty] at hstep
        have hrhs : 0 ≤ 40 * W₁ * k / (G.E.card : ℝ) := by positivity
        exact hstep.trans hrhs
  · have hW₁_zero : W₁ = 0 := le_antisymm (not_lt.mp hW₁_pos) hW₁_nonneg
    have hw_zero : ∀ e ∈ G.E, w e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW₁_zero
    let 𝒲 : Finset (Finset ℕ) := {T.V}
    have hbe : boundary 𝒲 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro v hv
      rw [mem_boundary_iff] at hv
      obtain ⟨A, hA, B, hB, hne, _⟩ := hv
      rw [Finset.mem_singleton] at hA hB
      exact hne (hA.trans hB.symm)
    refine ⟨𝒲, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro C hC
      rw [Finset.mem_singleton] at hC
      rw [hC]
      exact pathConvex_full T hT.isForest ⟨r, hT.2⟩ (fun a ha b hb => hT.connected ha hb)
    · intro C₁ hC₁ C₂ hC₂ hne
      rw [Finset.mem_singleton] at hC₁ hC₂
      exact absurd (hC₁.trans hC₂.symm) hne
    · simp only [𝒲, Finset.singleton_biUnion]
      exact inducedEdges_full hT.isForest.1
    · simp [𝒲]
    · simp only [𝒲, Finset.card_singleton, Nat.cast_one]
      have : 0 ≤ 6 * (G.E.card : ℝ) / k := by positivity
      linarith
    · rw [hbe, Finset.card_empty, Nat.cast_zero]
      positivity
    · rw [hbe]
      exact ⟨Finset.empty_subset _, fun _ hx => by simp at hx⟩
    · intro C _
      have hlhs : ∑ e ∈ G.E.filter (fun e =>
          (G.tail e ∈ C ∧ G.tail e ∉ boundary 𝒲) ∨
          (G.head e ∈ C ∧ G.head e ∉ boundary 𝒲)), w e = 0 :=
        Finset.sum_eq_zero (fun e he => hw_zero e (Finset.mem_filter.mp he).1)
      rw [hlhs]
      change 0 ≤ 40 * W₁ * k / (G.E.card : ℝ)
      rw [hW₁_zero]
      simp

end MinCostFlow.LSF
