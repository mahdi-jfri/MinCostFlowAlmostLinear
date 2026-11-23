module

public import MinCostFlow.LSF.ForestFromRoots
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Congestion and Lemma B.6 ([chen2022maximum] Appendix B.3)

This file formalizes Definition B.5 (`congestion`) and **Lemma B.6** (`lemma_B_6`, Valid `π`) of
[chen2022maximum, Appendix B.3]:
when `π` sorts `E(T)` by increasing congestion `Cong^{T, ℓ}_e`, the rooted spanning forest
`F_T(R, π)` satisfies `∑_{e ∈ E(G)} str^{F, ℓ}_e ≤ 2 ∑_{e ∈ E(G)} str^{T, ℓ}_e`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Edge congestion (Definition B.5) -/

/-- Edge congestion `Cong^{T, ℓ}_e = ∑_{e' = (u, v) ∈ E(G) : e ∈ T[u, v]} 1 / ℓ_{e'}`
(`[chen2022maximum, Definition B.5]`). -/
noncomputable def congestion (G T : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  open Classical in
  ∑ e' ∈ G.E, if e ∈ walkEdges (T.forestPath (G.tail e') (G.head e')) then 1 / ℓ e' else 0

lemma congestion_nonneg (G T : MGraph) {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (e : ℕ) :
    0 ≤ congestion G T ℓ e := by
  classical
  apply Finset.sum_nonneg
  intro e' he'
  split_ifs
  · exact div_nonneg zero_le_one (le_of_lt (hℓ e' he'))
  · exact le_rfl

lemma congestion_eq_zero_of_not_mem (G T : MGraph) (ℓ : ℕ → ℝ)
    (hTG : ∀ e' ∈ G.E, walkEdges (T.forestPath (G.tail e') (G.head e')) ⊆ G.E)
    {e : ℕ} (he : e ∉ G.E) :
    congestion G T ℓ e = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e' he'
  rw [ite_eq_right_iff]
  intro hmem
  exact absurd (hTG e' he' hmem) he

lemma congestion_pos_of_mem {G T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    {e : ℕ} (heT : e ∈ T.E) (heG : e ∈ G.E)
    (he_ends : T.tail e = G.tail e ∧ T.head e = G.head e) :
    0 < congestion G T ℓ e := by
  classical
  have hnl := isForest_no_selfLoop hT.isForest heT
  have he_fp : e ∈ walkEdges (T.forestPath (G.tail e) (G.head e)) := by
    have hW : T.IsWalk (G.tail e) (G.head e) [(e, true)] := by
      refine .cons (x := (e, true)) heT (by simp [MGraph.src, he_ends.1]) ?_
      rw [show T.dst (e, true) = G.head e from he_ends.2]
      exact .nil (G.head e)
    have hP : T.IsPath (G.tail e) (G.head e) [(e, true)] := by
      refine ⟨hW, ?_⟩
      rw [walkVertices_cons]
      simp only [MGraph.walkVertices, List.map_nil, MGraph.dst, ↓reduceIte, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
      simpa [he_ends.1, he_ends.2] using hnl
    rw [forestPath_eq_of_isPath hT.isForest hP, walkEdges_cons]
    exact Finset.mem_insert_self _ _
  have hsingle : 1 / ℓ e ≤ congestion G T ℓ e := by
    unfold congestion
    have hle := Finset.single_le_sum (f := fun e' =>
        if e ∈ walkEdges (T.forestPath (G.tail e') (G.head e')) then 1 / ℓ e' else 0)
      (fun e' he' => by split_ifs; exact div_nonneg zero_le_one (le_of_lt (hℓ e' he')); exact le_rfl)
      heG
    simpa [he_fp] using hle
  exact lt_of_lt_of_le (div_pos zero_lt_one (hℓ e heG)) hsingle

/-! ## Walk decomposition and routing helpers -/

private lemma walk_first_mem_split {G : MGraph} (D : Finset ℕ) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → ¬ Disjoint (walkEdges P) D →
      ∃ P₁ x P₂, P = P₁ ++ x :: P₂ ∧ G.IsWalk u (G.src x) P₁ ∧
        x.1 ∈ D ∧ Disjoint (walkEdges P₁) D := by
  intro u v P hW
  induction hW with
  | nil s =>
    intro hnd
    simp [walkEdges] at hnd
  | @cons s t x Q hx hs _ ih =>
    intro hnd
    by_cases hxD : x.1 ∈ D
    · refine ⟨[], x, Q, rfl, ?_, hxD, by simp [walkEdges]⟩
      rw [hs]
      exact .nil s
    · have hndQ : ¬ Disjoint (walkEdges Q) D := by
        intro hdisjQ
        apply hnd
        rw [walkEdges_cons, Finset.disjoint_insert_left]
        exact ⟨hxD, hdisjQ⟩
      obtain ⟨P₁, y, P₂, hQ_eq, hWP1, hyD, hdisjP1⟩ := ih hndQ
      refine ⟨x :: P₁, y, P₂, by rw [hQ_eq]; rfl, .cons hx hs hWP1, hyD, ?_⟩
      rw [walkEdges_cons, Finset.disjoint_insert_left]
      exact ⟨hxD, hdisjP1⟩

lemma walk_mem_edge_split {G : MGraph} :
    ∀ {u v e : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → e ∈ walkEdges P →
      ∃ P₁ x P₂, P = P₁ ++ x :: P₂ ∧ x.1 = e ∧
        G.IsWalk u (G.src x) P₁ ∧ G.IsWalk (G.dst x) v P₂ := by
  intro u v e P hW
  induction hW with
  | nil _ =>
    intro he
    simp [walkEdges] at he
  | @cons s t x Q hx hs hr ih =>
    intro he
    rw [walkEdges_cons, Finset.mem_insert] at he
    rcases he with rfl | heQ
    · refine ⟨[], x, Q, rfl, rfl, ?_, hr⟩
      rw [hs]
      exact .nil s
    · obtain ⟨P₁, y, P₂, hQ_eq, hy, h1, h2⟩ := ih heQ
      exact ⟨x :: P₁, y, P₂, by rw [hQ_eq]; rfl, hy, .cons hx hs h1, h2⟩

lemma walkEdges_forestPath_sub_edges {T : MGraph} (hT : T.IsForest) {u v : ℕ} :
    walkEdges (T.forestPath u v) ⊆ T.E := by
  by_cases hconn : T.Connected u v
  · have hP := forestPath_isPath hT hconn
    intro e he
    obtain ⟨x, hx, ha_eq⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    rw [← ha_eq]
    exact IsWalk_edges_mem hP.1 hx
  · unfold MGraph.forestPath
    classical
    have hnot : ¬ ∃ P, T.IsPath u v P := fun ⟨P, hP⟩ => hconn ⟨P, hP.1⟩
    rw [dite_eq_right_iff.mpr (fun h => absurd h hnot)]
    simp [walkEdges]

private lemma sum_union_le_of_nonneg {A B : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ x ∈ A ∩ B, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  classical
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have hnn : 0 ≤ ∑ x ∈ A ∩ B, f x := Finset.sum_nonneg hf
  linarith

private lemma sum_biUnion_le_of_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ x ∈ s.biUnion g, 0 ≤ f x) :
    ∑ x ∈ s.biUnion g, f x ≤ ∑ i ∈ s, ∑ x ∈ g i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 := sum_union_le_of_nonneg (A := g a) (B := s'.biUnion g) (f := f) (fun x hx => by
      apply hf x
      rw [Finset.biUnion_insert, Finset.mem_union]
      exact Or.inl (Finset.mem_inter.mp hx).1)
    have h2 : ∑ x ∈ s'.biUnion g, f x ≤ ∑ i ∈ s', ∑ x ∈ g i, f x :=
      ih fun x hx => hf x (by rw [Finset.biUnion_insert, Finset.mem_union]; exact Or.inr hx)
    linarith

lemma sum_mul_congestion {G T : MGraph} (hT : T.IsForest) (ℓ : ℕ → ℝ) :
    ∑ e ∈ T.E, ℓ e * congestion G T ℓ e =
      ∑ e' ∈ G.E, walkLength ℓ (T.forestPath (G.tail e') (G.head e')) / ℓ e' := by
  classical
  have hswap : ∀ e' ∈ G.E,
      walkLength ℓ (T.forestPath (G.tail e') (G.head e')) / ℓ e' =
        ∑ e ∈ T.E, (if e ∈ walkEdges (T.forestPath (G.tail e') (G.head e')) then ℓ e / ℓ e' else 0) := by
    intro e' _
    by_cases hconn : T.Connected (G.tail e') (G.head e')
    · have hP := forestPath_isPath hT hconn
      rw [walkLength_eq_sum_of_isPath ℓ hP, Finset.sum_div]
      have hsub := walkEdges_forestPath_sub_edges hT (u := G.tail e') (v := G.head e')
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    · unfold MGraph.forestPath
      have hnot : ¬ ∃ P, T.IsPath (G.tail e') (G.head e') P := fun ⟨P, hP⟩ => hconn ⟨P, hP.1⟩
      rw [dite_eq_right_iff.mpr (fun h => absurd h hnot)]
      simp [walkLength, walkEdges]
  rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold congestion
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  split_ifs <;> simp [div_eq_mul_inv]

private lemma forestGivenRoots_walk_to_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V)
    (hdisj_not : ¬ Disjoint (walkEdges (T.forestPath u v)) (deletedEdges T r R π)) :
    ∃ x ∈ R.erase (topRoot T r R), ∃ r₀ ∈ R,
      deletedEdge T r R π x ∈ walkEdges (T.forestPath u v) ∧
      (forestGivenRoots T r R π).Connected u r₀ ∧
      walkEdges (T.forestPath u r₀) ⊆
        walkEdges (T.forestPath u v) ∪ walkEdges (T.forestPath x (rootParent T r R x)) := by
  classical
  let D := deletedEdges T r R π
  let F := forestGivenRoots T r R π
  have hP := forestPath_isPath hT.isForest (hT.connected hu hv)
  obtain ⟨P₁, hd, P₂, hP_eq, hWP1, hhdD, hdisjP1⟩ :=
    walk_first_mem_split D hP.1 hdisj_not
  have hhdD' : hd.1 ∈ deletedEdges T r R π := hhdD
  unfold deletedEdges at hhdD'
  rw [ite_eq_left_iff.mpr (fun h => absurd hRne h), Finset.mem_image] at hhdD'
  obtain ⟨x, hx, hxe⟩ := hhdD'
  have hxR := (Finset.mem_erase.mp hx).2
  have hpR := (rootParent_spec hT hR hRne hx).1
  have hQ := forestPath_isPath hT.isForest (hT.connected (hR.1 hxR) (hR.1 hpR))
  have hm_Q := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx
  obtain ⟨Q₁, y, Q₂, hQ_eq, hy_eq, hWQ1, hWQ2⟩ := walk_mem_edge_split hQ.1 hm_Q
  have hQ_nd := isPath_nodup_edges hQ
  rw [hQ_eq, List.map_append, List.map_cons, List.nodup_append] at hQ_nd
  have hy_notin_Q1 : y.1 ∉ walkEdges Q₁ := by
    have := hQ_nd.2.2 y.1
    simp only [walkEdges, List.mem_toFinset] at this ⊢
    intro h1
    exact this h1 y.1 List.mem_cons_self rfl
  have hy_notin_Q2 : y.1 ∉ walkEdges Q₂ := by
    have := (List.nodup_cons.mp hQ_nd.2.1).1
    simpa [walkEdges, List.mem_toFinset] using this
  have hQ_only_del : ∀ f ∈ walkEdges (T.forestPath x (rootParent T r R x)),
      f ∈ D → f = deletedEdge T r R π x := by
    intro f hfQ hfD
    have hfD' : f ∈ deletedEdges T r R π := hfD
    unfold deletedEdges at hfD'
    rw [ite_eq_left_iff.mpr (fun h => absurd hRne h), Finset.mem_image] at hfD'
    obtain ⟨x', hx', rfl⟩ := hfD'
    by_cases hxx' : x = x'
    · subst hxx'; rfl
    · exact absurd hfQ (Finset.disjoint_left.mp (adjacent_paths_disjoint hT hR hRne hx' hx (Ne.symm hxx'))
        (deletedEdge_mem_walkEdges (π := π) hT hR hRne hx'))
  have hdisjQ1 : Disjoint (walkEdges Q₁) D := by
    rw [Finset.disjoint_left]
    intro f hf1 hfD
    have hfQ : f ∈ walkEdges (T.forestPath x (rootParent T r R x)) := by
      rw [hQ_eq, walkEdges_append, Finset.mem_union]
      exact Or.inl hf1
    have hEq := hQ_only_del f hfQ hfD
    rw [hEq, ← hy_eq] at hf1
    exact hy_notin_Q1 hf1
  have hdisjQ2 : Disjoint (walkEdges Q₂) D := by
    rw [Finset.disjoint_left]
    intro f hf2 hfD
    have hfQ : f ∈ walkEdges (T.forestPath x (rootParent T r R x)) := by
      rw [hQ_eq, walkEdges_append, Finset.mem_union, walkEdges_cons]
      exact Or.inr (Finset.mem_insert_of_mem hf2)
    have hEq := hQ_only_del f hfQ hfD
    rw [hEq, ← hy_eq] at hf2
    exact hy_notin_Q2 hf2
  have hWalk_to_F : ∀ {a b : ℕ} {W : List (ℕ × Bool)}, T.IsWalk a b W → Disjoint (walkEdges W) D →
      F.Connected a b := by
    intro a b W hW hdisjW
    refine ⟨W, ?_⟩
    have hE : ∀ z ∈ W, z.1 ∈ F.E := fun z hz =>
      Finset.mem_sdiff.mpr ⟨IsWalk_edges_mem hW hz, Finset.disjoint_left.mp hdisjW (mem_walkEdges_of_mem hz)⟩
    induction hW with
    | nil s => exact .nil s
    | cons _ hs _ ih =>
      exact .cons (hE _ List.mem_cons_self) hs (ih (by
        rw [Finset.disjoint_left]
        intro e he heD
        exact Finset.disjoint_left.mp hdisjW (by rw [walkEdges_cons]; exact Finset.mem_insert_of_mem he) heD)
        (fun z hz => hE z (List.mem_cons_of_mem _ hz)))
  have hsub_P1 : walkEdges P₁ ⊆ walkEdges (T.forestPath u v) := by
    intro f hf; rw [hP_eq, walkEdges_append, Finset.mem_union]; exact Or.inl hf
  have hsub_Q1 : walkEdges Q₁ ⊆ walkEdges (T.forestPath x (rootParent T r R x)) := by
    intro f hf; rw [hQ_eq, walkEdges_append, Finset.mem_union]; exact Or.inl hf
  have hsub_Q2 : walkEdges Q₂ ⊆ walkEdges (T.forestPath x (rootParent T r R x)) := by
    intro f hf; rw [hQ_eq, walkEdges_append, Finset.mem_union, walkEdges_cons]
    exact Or.inr (Finset.mem_insert_of_mem hf)
  have he_in_P : deletedEdge T r R π x ∈ walkEdges (T.forestPath u v) := by
    rw [hxe, hP_eq, walkEdges_append, Finset.mem_union, walkEdges_cons]
    exact Or.inr (Finset.mem_insert_self _ _)
  have hsrc_cases : T.src hd = T.src y ∨ T.src hd = T.dst y := by
    have hEq_e : hd.1 = y.1 := hxe.symm.trans hy_eq.symm
    rcases hd with ⟨e1, _ | _⟩ <;> rcases y with ⟨e2, _ | _⟩ <;>
      dsimp only at hEq_e <;> subst hEq_e <;> simp [MGraph.src, MGraph.dst]
  rcases hsrc_cases with h_eq | h_eq
  · refine ⟨x, hx, x, hxR, he_in_P, ?_, ?_⟩
    · have hF1 := hWalk_to_F hWP1 hdisjP1
      have hF2 := connected_symm (hWalk_to_F hWQ1 hdisjQ1)
      rw [h_eq] at hF1
      exact connected_trans hF1 hF2
    · have hW_ux : T.IsWalk u x (P₁ ++ walkRev Q₁) :=
        IsWalk_append hWP1 (h_eq ▸ IsWalk_walkRev hWQ1)
      have hsub := mem_walkEdges_forestPath_of_isWalk hT.isForest hW_ux
      intro f hf
      have hf' := hsub hf
      rw [walkEdges_append, walkEdges_walkRev, Finset.mem_union] at hf'
      rcases hf' with hf1 | hf2
      · exact Finset.mem_union_left _ (hsub_P1 hf1)
      · exact Finset.mem_union_right _ (hsub_Q1 hf2)
  · refine ⟨x, hx, rootParent T r R x, hpR, he_in_P, ?_, ?_⟩
    · have hF1 := hWalk_to_F hWP1 hdisjP1
      have hF2 := hWalk_to_F hWQ2 hdisjQ2
      rw [h_eq] at hF1
      exact connected_trans hF1 hF2
    · have hW_up : T.IsWalk u (rootParent T r R x) (P₁ ++ Q₂) :=
        IsWalk_append hWP1 (h_eq ▸ hWQ2)
      have hsub := mem_walkEdges_forestPath_of_isWalk hT.isForest hW_up
      intro f hf
      have hf' := hsub hf
      rw [walkEdges_append, Finset.mem_union] at hf'
      rcases hf' with hf1 | hf2
      · exact Finset.mem_union_left _ (hsub_P1 hf1)
      · exact Finset.mem_union_right _ (hsub_Q2 hf2)

/-! ## Lemma B.6 -/

/-- **Lemma B.6** (`[chen2022maximum, Lemma B.6]`, Valid `π`):
Given a graph `G = (V, E)` with positive lengths `ℓ`, a rooted tree `T` spanning `V(G)`,
a nonempty branch-free set `R ⊆ V`, and a total ordering `π` on `E(T)` sorted by increasing
congestion `Cong^{T, ℓ}_e` (Definition B.5), the rooted spanning forest `F = F_T(R, π)` satisfies
`∑_{e ∈ E(G)} str^{F, ℓ}_e ≤ 2 ∑_{e ∈ E(G)} str^{T, ℓ}_e`.

Notice the hypotheses allow `T` to contain bridge edges outside `E(G)` when `G` is disconnected,
so long as every `G`-edge's path in `T` uses only edges of `G`. -/
lemma lemma_B_6_factor {G T : MGraph} {r : ℕ} (hG : G.IsValid) (hT : IsRootedTree T r)
    (hTV : T.V = G.V) {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    (hTG_paths : ∀ e' ∈ G.E, walkEdges (T.forestPath (G.tail e') (G.head e')) ⊆ G.E)
    {π : ℕ → ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hπ_art : ∀ f ∈ T.E \ G.E, ∀ g ∈ T.E ∩ G.E, π f < π g)
    (hπ_cong : ∀ f ∈ T.E, ∀ g ∈ T.E, π f ≤ π g → congestion G T ℓ f ≤ α * congestion G T ℓ g) :
    ∑ e' ∈ G.E, (rootedForestGivenRoots T r R π).stretch G ℓ e' ≤
      (1 + α) * ∑ e' ∈ G.E, treeStretch G T ℓ e' := by
  classical
  let F := forestGivenRoots T r R π
  let RF := rootedForestGivenRoots T r R π
  have hRS := forestGivenRoots_isRootedSpanningForest hT hR hRne π
  have hsubTF : T.IsSubgraph F :=
    ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have hQ_sub_G : ∀ x ∈ R.erase (topRoot T r R), deletedEdge T r R π x ∈ G.E →
      walkEdges (T.forestPath x (rootParent T r R x)) ⊆ G.E := by
    intro x hx hdelG f hfQ
    by_contra hf_not_G
    have hfT : f ∈ T.E := walkEdges_forestPath_sub_edges hT.isForest hfQ
    have hdelT := deletedEdge_mem_E (π := π) hT hR hRne hx
    have hlt := hπ_art f (Finset.mem_sdiff.mpr ⟨hfT, hf_not_G⟩) _ (Finset.mem_inter.mpr ⟨hdelT, hdelG⟩)
    exact absurd (deletedEdge_le hfQ) (Nat.not_le_of_lt hlt)
  let L : ℕ → ℝ := fun x => walkLength ℓ (T.forestPath x (rootParent T r R x))
  have hedge_bound : ∀ e' ∈ G.E,
      RF.stretch G ℓ e' ≤ treeStretch G T ℓ e' +
        (∑ x ∈ (R.erase (topRoot T r R)).filter
            (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath (G.tail e') (G.head e'))),
          L x) / ℓ e' := by
    intro e' he'
    let u := G.tail e'
    let v := G.head e'
    have huV : u ∈ T.V := hTV ▸ (hG e' he').1
    have hvV : v ∈ T.V := hTV ▸ (hG e' he').2
    have hℓpos : 0 < ℓ e' := hℓ e' he'
    by_cases hroot_eq : RF.root u = RF.root v
    · unfold RootedForest.stretch treeStretch
      change (if RF.root u = RF.root v then 1 + walkLength ℓ (F.forestPath u v) / ℓ e'
        else _) ≤ _
      rw [ite_eq_left_iff.mpr (fun h => absurd hroot_eq h)]
      have hr_u := rootedForest_root_spec hRS huV
      have hr_v := rootedForest_root_spec hRS hvV
      have hFconn : F.Connected u v :=
        connected_trans hr_u.2 (hroot_eq ▸ connected_symm hr_v.2)
      have hP_F := forestPath_isPath hRS.1 hFconn
      have hP_T : T.IsPath u v (F.forestPath u v) := isPath_of_subgraph hsubTF hP_F
      have hEq_path : F.forestPath u v = T.forestPath u v :=
        (forestPath_eq_of_isPath hT.isForest hP_T).symm
      rw [hEq_path]
      have hsum_nn : 0 ≤ (∑ x ∈ (R.erase (topRoot T r R)).filter
          (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath u v)), L x) / ℓ e' := by
        apply div_nonneg _ (le_of_lt hℓpos)
        apply Finset.sum_nonneg
        intro x hx
        rw [Finset.mem_filter] at hx
        exact walkLength_nonneg_of_nonneg ℓ fun f hf =>
          le_of_lt (hℓ f (hQ_sub_G x hx.1 (hTG_paths e' he' hx.2) hf))
      dsimp only [u, v] at *
      linarith
    · unfold RootedForest.stretch treeStretch
      change (if RF.root u = RF.root v then _
        else 1 + (walkLength ℓ (F.forestPath u (RF.root u)) +
          walkLength ℓ (F.forestPath v (RF.root v))) / ℓ e') ≤ _
      rw [ite_eq_right_iff.mpr (fun h => absurd h hroot_eq)]
      have hnot_F : ¬ F.Connected u v := fun hc =>
        hroot_eq ((rootedForest_root_eq_iff hRS huV hvV).mpr hc)
      rw [show F = forestGivenRoots T r R π from rfl, forestGivenRoots,
        connected_sdiff_iff_disjoint hT.isForest (hT.connected huV hvV)] at hnot_F
      obtain ⟨xu, hxu_mem, rxu, hrxu_R, hdel_u, hconn_u, hsub_u⟩ :=
        forestGivenRoots_walk_to_root hT hR hRne π huV hvV hnot_F
      have hnot_F_vu : ¬ Disjoint (walkEdges (T.forestPath v u)) (deletedEdges T r R π) := by
        rwa [forestPath_rev hT.isForest (hT.connected huV hvV), walkEdges_walkRev]
      obtain ⟨xv, hxv_mem, rxv, hrxv_R, hdel_v, hconn_v, hsub_v⟩ :=
        forestGivenRoots_walk_to_root hT hR hRne π hvV huV hnot_F_vu
      have hdel_v' : deletedEdge T r R π xv ∈ walkEdges (T.forestPath u v) := by
        rwa [forestPath_rev hT.isForest (hT.connected huV hvV), walkEdges_walkRev] at hdel_v
      have hr_u_eq : RF.root u = rxu :=
        forestGivenRoots_root_eq_of_connected hT hR hRne π huV hrxu_R hconn_u
      have hr_v_eq : RF.root v = rxv :=
        forestGivenRoots_root_eq_of_connected hT hR hRne π hvV hrxv_R hconn_v
      have hP_Fu := forestPath_isPath hRS.1 hconn_u
      have hP_Fv := forestPath_isPath hRS.1 hconn_v
      have hEq_Fu : F.forestPath u (RF.root u) = T.forestPath u rxu := by
        rw [hr_u_eq]
        exact (forestPath_eq_of_isPath hT.isForest (isPath_of_subgraph hsubTF hP_Fu)).symm
      have hEq_Fv : F.forestPath v (RF.root v) = T.forestPath v rxv := by
        rw [hr_v_eq]
        exact (forestPath_eq_of_isPath hT.isForest (isPath_of_subgraph hsubTF hP_Fv)).symm
      have hlen_Fu : walkLength ℓ (F.forestPath u (RF.root u)) =
          ∑ f ∈ walkEdges (T.forestPath u rxu), ℓ f := by
        rw [hEq_Fu, walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT.isForest (hT.connected huV (hR.1 hrxu_R)))]
      have hlen_Fv : walkLength ℓ (F.forestPath v (RF.root v)) =
          ∑ f ∈ walkEdges (T.forestPath v rxv), ℓ f := by
        rw [hEq_Fv, walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT.isForest (hT.connected hvV (hR.1 hrxv_R)))]
      have hdisj_uv : Disjoint (walkEdges (T.forestPath u rxu)) (walkEdges (T.forestPath v rxv)) := by
        rw [Finset.disjoint_left]
        intro f hf1 hf2
        have hf1' : f ∈ walkEdges (F.forestPath u (RF.root u)) := by rwa [hEq_Fu]
        have hf2' : f ∈ walkEdges (F.forestPath v (RF.root v)) := by rwa [hEq_Fv]
        have hP_Fu' := forestPath_isPath hRS.1 (hr_u_eq ▸ hconn_u)
        have hP_Fv' := forestPath_isPath hRS.1 (hr_v_eq ▸ hconn_v)
        obtain ⟨P1, x1, _, _, hx1e, h1_start, _⟩ := walk_mem_edge_split hP_Fu'.1 hf1'
        obtain ⟨Q1, x2, _, _, hx2e, h2_start, _⟩ := walk_mem_edge_split hP_Fv'.1 hf2'
        have hF_u1 : F.Connected u (F.src x1) := ⟨P1, h1_start⟩
        have hF_v2 : F.Connected v (F.src x2) := ⟨Q1, h2_start⟩
        have hfF : f ∈ F.E := walkEdges_forestPath_sub_edges hRS.1 hf1'
        have hF_12 : F.Connected (F.src x1) (F.src x2) := by
          rcases x1 with ⟨e1, _ | _⟩ <;> rcases x2 with ⟨e2, _ | _⟩ <;>
            dsimp only at hx1e hx2e <;> rw [hx1e, hx2e] <;> simp only [MGraph.src]
          · exact connected_refl F _
          · exact connected_symm (connected_of_edge hfF)
          · exact connected_of_edge hfF
          · exact connected_refl F _
        have hFuv : F.Connected u v := connected_trans hF_u1 (connected_trans hF_12 (connected_symm hF_v2))
        exact hroot_eq ((rootedForest_root_eq_iff hRS huV hvV).mpr hFuv)
      have hsub_v' : walkEdges (T.forestPath v rxv) ⊆
          walkEdges (T.forestPath u v) ∪ walkEdges (T.forestPath xv (rootParent T r R xv)) := by
        intro f hf
        have := hsub_v hf
        rwa [forestPath_rev hT.isForest (hT.connected huV hvV), walkEdges_walkRev] at this
      let S_del := (R.erase (topRoot T r R)).filter
        (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath u v))
      have hxu_S : xu ∈ S_del := Finset.mem_filter.mpr ⟨hxu_mem, hdel_u⟩
      have hxv_S : xv ∈ S_del := Finset.mem_filter.mpr ⟨hxv_mem, hdel_v'⟩
      have hunion_sub : walkEdges (T.forestPath u rxu) ∪ walkEdges (T.forestPath v rxv) ⊆
          walkEdges (T.forestPath u v) ∪ S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))) := by
        intro f hf
        rw [Finset.mem_union] at hf ⊢
        rcases hf with hf1 | hf2
        · rcases Finset.mem_union.mp (hsub_u hf1) with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_biUnion.mpr ⟨xu, hxu_S, h⟩)
        · rcases Finset.mem_union.mp (hsub_v' hf2) with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_biUnion.mpr ⟨xv, hxv_S, h⟩)
      have hrhs_G : ∀ f ∈ walkEdges (T.forestPath u v) ∪
          S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))), f ∈ G.E := by
        intro f hf
        rw [Finset.mem_union, Finset.mem_biUnion] at hf
        rcases hf with hf_uv | ⟨x, hxS, hfQ⟩
        · exact hTG_paths e' he' hf_uv
        · rw [Finset.mem_filter] at hxS
          exact hQ_sub_G x hxS.1 (hTG_paths e' he' hxS.2) hfQ
      have hsum_len : walkLength ℓ (F.forestPath u (RF.root u)) +
          walkLength ℓ (F.forestPath v (RF.root v)) ≤
          walkLength ℓ (T.forestPath u v) + ∑ x ∈ S_del, L x := by
        rw [hlen_Fu, hlen_Fv, ← Finset.sum_union hdisj_uv]
        have hle1 : ∑ f ∈ walkEdges (T.forestPath u rxu) ∪ walkEdges (T.forestPath v rxv), ℓ f ≤
            ∑ f ∈ walkEdges (T.forestPath u v) ∪
              S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))), ℓ f :=
          Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun f hf _ => le_of_lt (hℓ f (hrhs_G f hf)))
        have hle2 : ∑ f ∈ walkEdges (T.forestPath u v) ∪
              S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))), ℓ f ≤
            (∑ f ∈ walkEdges (T.forestPath u v), ℓ f) +
              ∑ f ∈ S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))), ℓ f :=
          sum_union_le_of_nonneg (fun f hf => le_of_lt (hℓ f (hTG_paths e' he' (Finset.mem_inter.mp hf).1)))
        have hle3 : ∑ f ∈ S_del.biUnion (fun x => walkEdges (T.forestPath x (rootParent T r R x))), ℓ f ≤
            ∑ x ∈ S_del, L x := by
          refine (sum_biUnion_le_of_nonneg S_del _ ℓ (fun f hf => ?_)).trans ?_
          · exact le_of_lt (hℓ f (hrhs_G f (Finset.mem_union_right _ hf)))
          · refine Finset.sum_le_sum fun x hxS => ?_
            rw [Finset.mem_filter] at hxS
            have hxV := hR.1 (Finset.mem_erase.mp hxS.1).2
            have hpV := hR.1 (rootParent_spec hT hR hRne hxS.1).1
            rw [show L x = walkLength ℓ (T.forestPath x (rootParent T r R x)) from rfl,
              walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT.isForest (hT.connected hxV hpV))]
        have h_uv_eq : walkLength ℓ (T.forestPath u v) = ∑ f ∈ walkEdges (T.forestPath u v), ℓ f :=
          walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT.isForest (hT.connected huV hvV))
        linarith [hle1, hle2, hle3]
      have hdiv : (walkLength ℓ (F.forestPath u (RF.root u)) +
            walkLength ℓ (F.forestPath v (RF.root v))) / ℓ e' ≤
          walkLength ℓ (T.forestPath u v) / ℓ e' + (∑ x ∈ S_del, L x) / ℓ e' := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right hsum_len (le_of_lt hℓpos)
      dsimp only [u, v, S_del] at hdiv ⊢
      linarith
  have hsum_step1 : ∑ e' ∈ G.E, RF.stretch G ℓ e' ≤
      (∑ e' ∈ G.E, treeStretch G T ℓ e') +
        ∑ e' ∈ G.E, (∑ x ∈ (R.erase (topRoot T r R)).filter
          (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath (G.tail e') (G.head e'))),
          L x) / ℓ e' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hedge_bound
  have hsum_swap : ∑ e' ∈ G.E, (∑ x ∈ (R.erase (topRoot T r R)).filter
        (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath (G.tail e') (G.head e'))),
        L x) / ℓ e' =
      ∑ x ∈ R.erase (topRoot T r R), L x * congestion G T ℓ (deletedEdge T r R π x) := by
    have h_rewrite : ∀ e' ∈ G.E,
        (∑ x ∈ (R.erase (topRoot T r R)).filter
            (fun x => deletedEdge T r R π x ∈ walkEdges (T.forestPath (G.tail e') (G.head e'))),
            L x) / ℓ e' =
          ∑ x ∈ R.erase (topRoot T r R),
            (if deletedEdge T r R π x ∈ walkEdges (T.forestPath (G.tail e') (G.head e'))
             then L x / ℓ e' else 0) := by
      intro e' _
      rw [Finset.sum_div, Finset.sum_filter]
    rw [Finset.sum_congr rfl h_rewrite, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold congestion
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    split_ifs <;> simp [div_eq_mul_inv]
  have hterm_nn : ∀ f ∈ T.E, 0 ≤ ℓ f * congestion G T ℓ f := by
    intro f _
    by_cases hfG : f ∈ G.E
    · exact mul_nonneg (le_of_lt (hℓ f hfG)) (congestion_nonneg G T hℓ f)
    · rw [congestion_eq_zero_of_not_mem G T ℓ hTG_paths hfG, mul_zero]
  have hterm_le : ∑ x ∈ R.erase (topRoot T r R), L x * congestion G T ℓ (deletedEdge T r R π x) ≤
      α * ∑ f ∈ T.E, ℓ f * congestion G T ℓ f := by
    have hsingle_le : ∀ x ∈ R.erase (topRoot T r R),
        L x * congestion G T ℓ (deletedEdge T r R π x) ≤
          ∑ f ∈ walkEdges (T.forestPath x (rootParent T r R x)), α * (ℓ f * congestion G T ℓ f) := by
      intro x hx
      by_cases hxG : deletedEdge T r R π x ∈ G.E
      · have hxV := hR.1 (Finset.mem_erase.mp hx).2
        have hpV := hR.1 (rootParent_spec hT hR hRne hx).1
        have hP := forestPath_isPath hT.isForest (hT.connected hxV hpV)
        have hLx : L x = ∑ f ∈ walkEdges (T.forestPath x (rootParent T r R x)), ℓ f :=
          walkLength_eq_sum_of_isPath ℓ hP
        rw [hLx, Finset.sum_mul]
        refine Finset.sum_le_sum fun f hf => ?_
        have hfG : f ∈ G.E := hQ_sub_G x hx hxG hf
        have hℓf : 0 ≤ ℓ f := le_of_lt (hℓ f hfG)
        have hfT : f ∈ T.E := walkEdges_forestPath_sub_edges hT.isForest hf
        have hdelT := deletedEdge_mem_E (π := π) hT hR hRne hx
        have hcong_le := hπ_cong (deletedEdge T r R π x) hdelT f hfT (deletedEdge_le hf)
        calc ℓ f * congestion G T ℓ (deletedEdge T r R π x)
            ≤ ℓ f * (α * congestion G T ℓ f) := mul_le_mul_of_nonneg_left hcong_le hℓf
          _ = α * (ℓ f * congestion G T ℓ f) := mul_left_comm _ _ _
      · rw [congestion_eq_zero_of_not_mem G T ℓ hTG_paths hxG, mul_zero]
        apply Finset.sum_nonneg
        intro f hf
        exact mul_nonneg hα (hterm_nn f (walkEdges_forestPath_sub_edges hT.isForest hf))
    have h1 := Finset.sum_le_sum hsingle_le
    have hdisj : Set.PairwiseDisjoint (↑(R.erase (topRoot T r R)) : Set ℕ)
        (fun x => walkEdges (T.forestPath x (rootParent T r R x))) := by
      intro x₁ hx₁ x₂ hx₂ hne
      exact adjacent_paths_disjoint hT hR hRne hx₁ hx₂ hne
    rw [← Finset.sum_biUnion hdisj] at h1
    have hsub_TE : (R.erase (topRoot T r R)).biUnion
        (fun x => walkEdges (T.forestPath x (rootParent T r R x))) ⊆ T.E := by
      intro f hf
      obtain ⟨_, _, hfQ⟩ := Finset.mem_biUnion.mp hf
      exact walkEdges_forestPath_sub_edges hT.isForest hfQ
    have hsub_le : ∑ f ∈ (R.erase (topRoot T r R)).biUnion
          (fun x => walkEdges (T.forestPath x (rootParent T r R x))),
          α * (ℓ f * congestion G T ℓ f) ≤
        ∑ f ∈ T.E, α * (ℓ f * congestion G T ℓ f) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_TE (fun f hf _ => mul_nonneg hα (hterm_nn f hf))
    calc ∑ x ∈ R.erase (topRoot T r R), L x * congestion G T ℓ (deletedEdge T r R π x)
        ≤ ∑ f ∈ (R.erase (topRoot T r R)).biUnion
            (fun x => walkEdges (T.forestPath x (rootParent T r R x))),
            α * (ℓ f * congestion G T ℓ f) := h1
      _ ≤ ∑ f ∈ T.E, α * (ℓ f * congestion G T ℓ f) := hsub_le
      _ = α * ∑ f ∈ T.E, ℓ f * congestion G T ℓ f := by rw [← Finset.mul_sum]
  have hsum_tree : ∑ f ∈ T.E, ℓ f * congestion G T ℓ f ≤ ∑ e' ∈ G.E, treeStretch G T ℓ e' := by
    rw [sum_mul_congestion hT.isForest ℓ]
    refine Finset.sum_le_sum fun e' _ => ?_
    unfold treeStretch
    linarith
  have halpha_sum := mul_le_mul_of_nonneg_left hsum_tree hα
  rw [add_mul, one_mul]
  linarith [hsum_step1, hsum_swap, hterm_le, halpha_sum]

lemma lemma_B_6 {G T : MGraph} {r : ℕ} (hG : G.IsValid) (hT : IsRootedTree T r)
    (hTV : T.V = G.V) {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    (hTG_edges : ∀ e ∈ T.E, e ∈ G.E → T.tail e = G.tail e ∧ T.head e = G.head e)
    (hTG_paths : ∀ e' ∈ G.E, walkEdges (T.forestPath (G.tail e') (G.head e')) ⊆ G.E)
    {π : ℕ → ℕ} (_hord : IsEdgeOrder T π) (hsorted : IsSortedByCong T (congestion G T ℓ) π) :
    ∑ e' ∈ G.E, (rootedForestGivenRoots T r R π).stretch G ℓ e' ≤
      2 * ∑ e' ∈ G.E, treeStretch G T ℓ e' := by
  classical
  have h11 : (1 + 1 : ℝ) = 2 := by norm_num
  rw [← h11]
  refine lemma_B_6_factor hG hT hTV hR hRne hℓ hTG_paths zero_le_one ?_ ?_
  · intro f hf g hg
    rw [Finset.mem_sdiff] at hf
    rw [Finset.mem_inter] at hg
    have hf0 : congestion G T ℓ f = 0 := congestion_eq_zero_of_not_mem G T ℓ hTG_paths hf.2
    have hg0 : 0 < congestion G T ℓ g :=
      congestion_pos_of_mem hT hℓ hg.1 hg.2 (hTG_edges g hg.1 hg.2)
    exact hsorted f hf.1 g hg.1 (hf0.symm ▸ hg0)
  · intro f hf g hg hpi
    rw [one_mul]
    by_contra hlt
    rw [not_le] at hlt
    exact Nat.not_le_of_lt (hsorted g hg f hf hlt) hpi

end MinCostFlow.LSF
