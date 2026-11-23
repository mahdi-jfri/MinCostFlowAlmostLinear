module

public import MinCostFlow.LSF.Walks
import Mathlib.Data.Finset.Card

/-!
# Connected components, forest edge-counting, and spanning tree characterization

This file proves the finite-component combinatorics needed for `F_T(R, π)` (`Lemma B.6`),
tree decompositions (`Lemma B.7`), and `[AN19]` spanning tree lifting (`Theorem 2.2`):
* `compOf` and `components` partition `G.V` along `G.Connected`,
* deleting an edge of a forest increases the number of connected components by `1`,
* `#components(F) + |E(F)| = |V(F)|` for every forest `F`,
* a connected graph on nonempty `V` with `|E| + 1 = |V|` is a spanning tree,
* for a `RootedForest` spanning `G`, `RF.F.components.card = RF.R.card` and `RF.root` properties.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Connected components of a graph -/

noncomputable def compOf (G : MGraph) (u : ℕ) : Finset ℕ :=
  open Classical in G.V.filter (G.Connected u)

noncomputable def components (G : MGraph) : Finset (Finset ℕ) :=
  G.V.image (compOf G)

lemma mem_compOf_iff {G : MGraph} {u v : ℕ} :
    v ∈ compOf G u ↔ v ∈ G.V ∧ G.Connected u v := by
  unfold compOf
  simp

lemma self_mem_compOf {G : MGraph} {u : ℕ} (hu : u ∈ G.V) : u ∈ compOf G u :=
  mem_compOf_iff.mpr ⟨hu, connected_refl G u⟩

lemma compOf_eq_of_connected {G : MGraph} {u v : ℕ} (h : G.Connected u v) :
    compOf G u = compOf G v := by
  ext w
  simp only [mem_compOf_iff]
  exact ⟨fun ⟨hw, huw⟩ => ⟨hw, connected_trans (connected_symm h) huw⟩,
         fun ⟨hw, hvw⟩ => ⟨hw, connected_trans h hvw⟩⟩

lemma compOf_eq_iff {G : MGraph} {u v : ℕ} (hv : v ∈ G.V) :
    compOf G u = compOf G v ↔ G.Connected u v := by
  refine ⟨fun h => ?_, compOf_eq_of_connected⟩
  have : v ∈ compOf G u := h ▸ self_mem_compOf hv
  exact (mem_compOf_iff.mp this).2

lemma compOf_disjoint_of_not_connected {G : MGraph} {u v : ℕ} (h : ¬ G.Connected u v) :
    Disjoint (compOf G u) (compOf G v) := by
  rw [Finset.disjoint_left]
  intro w hwu hwv
  rw [mem_compOf_iff] at hwu hwv
  exact h (connected_trans hwu.2 (connected_symm hwv.2))

lemma compOf_mem_components {G : MGraph} {u : ℕ} (hu : u ∈ G.V) :
    compOf G u ∈ components G :=
  Finset.mem_image_of_mem _ hu

lemma components_card_one_of_connected {G : MGraph} (hne : G.V.Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    (components G).card = 1 := by
  obtain ⟨r, hr⟩ := hne
  have hEq : components G = {compOf G r} := by
    ext C
    simp only [components, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact compOf_eq_of_connected (hconn u hu r hr)
    · rintro rfl
      exact ⟨r, hr, rfl⟩
  rw [hEq, Finset.card_singleton]

/-! ## Edge deletion in a forest and `#components + |E| = |V|` -/

lemma isWalk_eraseEdge_of_not_mem {G : MGraph} {e u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hne : e ∉ walkEdges P) :
    ({ G with E := G.E.erase e } : MGraph).IsWalk u v P := by
  induction hP with
  | nil s => exact .nil s
  | @cons u₀ v₀ x₀ P₀ hx hs _ ih =>
    have hxe : x₀.1 ≠ e := fun hEq => hne (hEq ▸ mem_walkEdges_of_mem List.mem_cons_self)
    refine .cons (Finset.mem_erase.mpr ⟨hxe, hx⟩) hs ?_
    exact ih (fun h => hne (by rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr h))

private lemma connected_eraseEdge_to_graph {F : MGraph} {e u v : ℕ}
    (h : ({ F with E := F.E.erase e } : MGraph).Connected u v) : F.Connected u v :=
  connected_of_subgraph
    (H := F) (F := { F with E := F.E.erase e })
    ⟨Finset.Subset.refl _, Finset.erase_subset e F.E, fun _ _ => ⟨rfl, rfl⟩⟩ h

private lemma connected_erase_or_of_connected {F : MGraph} (hF : F.IsForest) {e u : ℕ}
    (he : e ∈ F.E) (hu : F.Connected (F.tail e) u) :
    ({ F with E := F.E.erase e } : MGraph).Connected (F.tail e) u ∨
      ({ F with E := F.E.erase e } : MGraph).Connected (F.head e) u := by
  let P := F.forestPath (F.tail e) u
  have hP := forestPath_isPath hF hu
  by_cases heP : e ∈ walkEdges P
  · right
    obtain ⟨b, hbP⟩ := mem_walkEdges_iff.mp heP
    obtain ⟨P₁, P₂, hEq, h1, h2⟩ := IsWalk_mem_split_edge hP.1 hbP
    have hnd := isPath_nodup_edges hP
    rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hnd
    have he_not_P2 : e ∉ walkEdges P₂ := by
      have hnd2 := (List.nodup_cons.mp hnd.2.1).1
      simpa [walkEdges, List.mem_toFinset] using hnd2
    have hP2_in_F' := isWalk_eraseEdge_of_not_mem h2 he_not_P2
    cases b
    · exfalso
      have hpref : F.IsPath (F.tail e) (F.tail e) (P₁ ++ [(e, false)]) :=
        IsPath_append_left (P := P₁ ++ [(e, false)]) (Q := P₂)
          (by simpa [hEq, List.append_assoc] using hP)
          (IsWalk_append h1 (.cons he rfl (.nil (F.tail e))))
      have hnil := IsPath_nil_of_eq hpref
      simp at hnil
    · exact ⟨P₂, hP2_in_F'⟩
  · left
    exact ⟨P, isWalk_eraseEdge_of_not_mem hP.1 heP⟩

private lemma not_connected_eraseEdge_endpoints {F : MGraph} (hF : F.IsForest) {e : ℕ}
    (he : e ∈ F.E) :
    ¬ ({ F with E := F.E.erase e } : MGraph).Connected (F.tail e) (F.head e) := by
  have hp : F.IsPath (F.tail e) (F.head e) [(e, true)] := by
    refine ⟨.cons he rfl (.nil (F.head e)), ?_⟩
    simp [MGraph.walkVertices, MGraph.dst, isForest_no_selfLoop hF he]
  have hfp := forestPath_eq_of_isPath hF hp
  apply not_connected_erase_of_mem_forestPath hF
  rw [hfp]
  exact mem_walkEdges_of_mem List.mem_cons_self

private lemma connected_eraseEdge_iff_of_not_in_edge_comp
    {F : MGraph} {e u v : ℕ} (he : e ∈ F.E) (hu : ¬ F.Connected (F.tail e) u) :
    ({ F with E := F.E.erase e } : MGraph).Connected u v ↔ F.Connected u v := by
  refine ⟨connected_eraseEdge_to_graph, fun huv => ?_⟩
  obtain ⟨P, hP⟩ := connected_isPath huv
  have hne_e : e ∉ walkEdges P := by
    intro heP
    obtain ⟨b, hbP⟩ := mem_walkEdges_iff.mp heP
    obtain ⟨P₁, _, _, h1, _⟩ := IsWalk_mem_split_edge hP.1 hbP
    have hconn : F.Connected u (F.tail e) := by
      cases b
      · refine connected_trans ⟨P₁, h1⟩ (connected_symm (connected_of_edge he))
      · exact ⟨P₁, h1⟩
    exact hu (connected_symm hconn)
  exact ⟨P, isWalk_eraseEdge_of_not_mem hP.1 hne_e⟩

lemma forest_eraseEdge_components_card {F : MGraph} (hF : F.IsForest) {e : ℕ} (he : e ∈ F.E) :
    (components ({ F with E := F.E.erase e } : MGraph)).card = (components F).card + 1 := by
  let F' : MGraph := { F with E := F.E.erase e }
  let u := F.tail e
  let v := F.head e
  have huv_V : u ∈ F.V ∧ v ∈ F.V := hF.1 e he
  have huv_F : F.Connected u v := connected_of_edge he
  have huv_not_F' : ¬ F'.Connected u v := not_connected_eraseEdge_endpoints hF he
  let Cu := compOf F u
  let Cu' := compOf F' u
  let Cv' := compOf F' v
  have hCu_mem : Cu ∈ components F := compOf_mem_components huv_V.1
  have hCu'_mem : Cu' ∈ components F' := compOf_mem_components huv_V.1
  have hCv'_mem : Cv' ∈ components F' := compOf_mem_components huv_V.2
  have hne_Cu'_Cv' : Cu' ≠ Cv' := by
    intro hEq
    exact huv_not_F' ((compOf_eq_iff (G := F') huv_V.2).mp hEq)
  have hCu'_not_in_rest : Cu' ∉ (components F).erase Cu := by
    intro hmem
    have hne := (Finset.mem_erase.mp hmem).1
    obtain ⟨w, hwV, hCw⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hmem).2
    have h1 : w ∈ compOf F' u := by
      have : w ∈ Cu' := hCw ▸ self_mem_compOf hwV
      exact this
    have h2 : F.Connected u w := connected_eraseEdge_to_graph (mem_compOf_iff.mp h1).2
    exact hne (by rw [← hCw]; exact (compOf_eq_of_connected h2).symm)
  have hCv'_not_in_rest : Cv' ∉ (components F).erase Cu := by
    intro hmem
    have hne := (Finset.mem_erase.mp hmem).1
    obtain ⟨w, hwV, hCw⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hmem).2
    have h1 : w ∈ compOf F' v := by
      have : w ∈ Cv' := hCw ▸ self_mem_compOf hwV
      exact this
    have h2 : F.Connected u w :=
      connected_trans huv_F (connected_eraseEdge_to_graph (mem_compOf_iff.mp h1).2)
    exact hne (by rw [← hCw]; exact (compOf_eq_of_connected h2).symm)
  have hEq_comps : components F' = insert Cu' (insert Cv' ((components F).erase Cu)) := by
    ext C
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hC
      obtain ⟨w, hwV, rfl⟩ := Finset.mem_image.mp hC
      by_cases hwu : F.Connected u w
      · rcases connected_erase_or_of_connected hF he hwu with h1 | h2
        · left; exact (compOf_eq_of_connected h1).symm
        · right; left; exact (compOf_eq_of_connected h2).symm
      · right; right
        refine ⟨?_, ?_⟩
        · intro hEq
          have : w ∈ Cu := hEq ▸ self_mem_compOf hwV
          exact hwu (mem_compOf_iff.mp this).2
        · have hC_eq : compOf F' w = compOf F w := by
            ext z
            simp only [mem_compOf_iff]
            have hzV : z ∈ F'.V ↔ z ∈ F.V := Iff.rfl
            have hzw : F'.Connected w z ↔ F.Connected w z :=
              connected_eraseEdge_iff_of_not_in_edge_comp he hwu
            exact and_congr hzV hzw
          rw [hC_eq]
          exact compOf_mem_components hwV
    · rintro (rfl | rfl | ⟨hne, hC⟩)
      · exact hCu'_mem
      · exact hCv'_mem
      · obtain ⟨w, hwV, rfl⟩ := Finset.mem_image.mp hC
        have hwu : ¬ F.Connected u w := fun hconn => hne (compOf_eq_of_connected hconn).symm
        have hC_eq : compOf F w = compOf F' w := by
          ext z
          simp only [mem_compOf_iff]
          exact and_congr Iff.rfl (connected_eraseEdge_iff_of_not_in_edge_comp he hwu).symm
        rw [hC_eq]
        exact compOf_mem_components hwV
  rw [hEq_comps, Finset.card_insert_of_notMem (by
    simp [hne_Cu'_Cv', hCu'_not_in_rest]),
    Finset.card_insert_of_notMem hCv'_not_in_rest,
    Finset.card_erase_of_mem hCu_mem]
  have hpos : 0 < (components F).card := Finset.card_pos.mpr ⟨Cu, hCu_mem⟩
  omega

lemma forest_components_add_edges (F : MGraph) (hF : F.IsForest) :
    (components F).card + F.E.card = F.V.card := by
  have hgen : ∀ (E₀ : Finset ℕ) (F₀ : MGraph),
      F₀.E = E₀ → F₀.IsForest → (components F₀).card + F₀.E.card = F₀.V.card := by
    intro E₀
    induction E₀ using Finset.induction with
    | empty =>
      intro F₀ hE0 _
      have hcard0 : F₀.E.card = 0 := by rw [hE0]; simp
      have hcomp_eq : ∀ u ∈ F₀.V, compOf F₀ u = ({u} : Finset ℕ) := by
        intro u hu
        ext w
        simp only [mem_compOf_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hw⟩
          obtain ⟨P, hP⟩ := hw
          cases hP with
          | nil _ => rfl
          | cons he _ _ => rw [hE0] at he; simp at he
        · intro hEq
          subst hEq
          exact ⟨hu, connected_refl F₀ w⟩
      have hcomps : components F₀ = F₀.V.image (fun u => ({u} : Finset ℕ)) := by
        ext C
        simp only [components, Finset.mem_image]
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact ⟨u, hu, (hcomp_eq u hu).symm⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨u, hu, hcomp_eq u hu⟩
      rw [hcard0, add_zero, hcomps,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    | @insert e E' he_not ih =>
      intro F₀ hE0 hF0
      have he_in : e ∈ F₀.E := by rw [hE0]; exact Finset.mem_insert_self e E'
      let F' : MGraph := { F₀ with E := F₀.E.erase e }
      have hF' : F'.IsForest := isForest_eraseEdge hF0 e
      have hE' : F'.E = E' := by simp [F', hE0, Finset.erase_insert he_not]
      have ih' := ih F' hE' hF'
      have hstep : (components F').card = (components F₀).card + 1 :=
        forest_eraseEdge_components_card hF0 he_in
      have hVcard : F'.V.card = F₀.V.card := rfl
      have hEcard : F'.E.card + 1 = F₀.E.card := by
        dsimp only [F']
        rw [Finset.card_erase_of_mem he_in]
        have : 0 < F₀.E.card := Finset.card_pos.mpr ⟨e, he_in⟩
        omega
      omega
  exact hgen F.E F rfl hF

lemma forest_sdiff_components_card {T : MGraph} (hT : T.IsForest) {S : Finset ℕ} (hS : S ⊆ T.E) :
    (components ({ T with E := T.E \ S } : MGraph)).card = (components T).card + S.card := by
  let F : MGraph := { T with E := T.E \ S }
  have hF : F.IsForest := by
    refine isForest_subgraph hT ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩ ?_
    intro e he
    exact hT.1 e (Finset.sdiff_subset he)
  have h1 := forest_components_add_edges T hT
  have h2 := forest_components_add_edges F hF
  have hE : F.E.card + S.card = T.E.card := by
    have := Finset.card_sdiff_add_card_inter T.E S
    rw [Finset.inter_eq_right.mpr hS] at this
    exact this
  have hVcard : F.V.card = T.V.card := rfl
  change (components F).card = (components T).card + S.card
  omega

lemma spanningTree_edge_card {T : MGraph} {V : Finset ℕ}
    (hT : T.IsSpanningTreeOn V) (hne : V.Nonempty) :
    T.E.card + 1 = V.card := by
  have h1 := forest_components_add_edges T hT.1
  have hV : T.V = V := hT.2.1
  have hc := components_card_one_of_connected (hV ▸ hne) (by simpa [hV] using hT.2.2)
  rw [hc, hV, add_comm] at h1
  exact h1

/-! ## Connected graphs with `|E| + 1 = |V|` are spanning trees -/

private lemma connected_erase_cycle_edge {G : MGraph} {P : List (ℕ × Bool)}
    (hcyc : G.IsCycle P) {e : ℕ} (he : e ∈ walkEdges P) :
    ∀ u v, G.Connected u v → ({ G with E := G.E.erase e } : MGraph).Connected u v := by
  rcases hcyc with ⟨hne, hnd, w₀, hw₀⟩
  obtain ⟨b, hbP⟩ := mem_walkEdges_iff.mp he
  obtain ⟨P₁, P₂, hEq, h1, h2⟩ := IsWalk_mem_split_edge hw₀ hbP
  let G' : MGraph := { G with E := G.E.erase e }
  have hP12_no_e : e ∉ walkEdges P₁ ∧ e ∉ walkEdges P₂ := by
    have hnd' := hnd
    rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hnd'
    have h12 := hnd'.2.1
    have h1e : e ∉ P₁.map Prod.fst := fun h => hnd'.2.2 e h e (by simp) rfl
    have h2e : e ∉ P₂.map Prod.fst := (List.nodup_cons.mp h12).1
    exact ⟨by simpa [walkEdges] using h1e, by simpa [walkEdges] using h2e⟩
  have h2' := isWalk_eraseEdge_of_not_mem h2 hP12_no_e.2
  have h1' := isWalk_eraseEdge_of_not_mem h1 hP12_no_e.1
  have hw_G'_rev : G'.IsWalk (G.dst (e, b)) (G.src (e, b)) (P₂ ++ P₁) :=
    IsWalk_append h2' h1'
  have hconn_ends : G'.Connected (G.tail e) (G.head e) := by
    cases b
    · exact ⟨P₂ ++ P₁, hw_G'_rev⟩
    · exact connected_symm ⟨P₂ ++ P₁, hw_G'_rev⟩
  intro u v huv
  obtain ⟨Q, hQ⟩ := huv
  induction hQ with
  | nil s => exact connected_refl G' s
  | @cons s _ x _ hx hs _ ih =>
    have hstep : G'.Connected s (G.dst x) := by
      by_cases hxe : x.1 = e
      · rw [← hs]
        rcases x with ⟨xe, _ | _⟩
        · dsimp only at hxe; subst hxe; simpa [MGraph.src, MGraph.dst] using connected_symm hconn_ends
        · dsimp only at hxe; subst hxe; simpa [MGraph.src, MGraph.dst] using hconn_ends
      · exact ⟨[x], .cons (Finset.mem_erase.mpr ⟨hxe, hx⟩) hs (.nil _)⟩
    exact connected_trans hstep ih

lemma isForest_of_connected_card {G : MGraph} {V : Finset ℕ}
    (hvalid : G.IsValid) (hV : G.V = V) (hne : V.Nonempty)
    (hconn : ∀ u ∈ V, ∀ v ∈ V, G.Connected u v) (hcard : G.E.card + 1 = V.card) :
    G.IsSpanningTreeOn V := by
  have exists_tree_sub : ∀ (m : ℕ) (H : MGraph),
      H.E.card = m → H.IsValid → H.V = V →
      (∀ u ∈ V, ∀ v ∈ V, H.Connected u v) →
      ∃ T : MGraph, T.IsSpanningTreeOn V ∧ H.IsSubgraph T ∧
        (∀ P, H.IsCycle P → T.E.card < H.E.card) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro H hm hHv hHV hHc
      by_cases hcyc : ∃ P, H.IsCycle P
      · obtain ⟨P, hP⟩ := hcyc
        have hPne : P ≠ [] := hP.1
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil P hPne
        have haE : a.1 ∈ H.E := by
          obtain ⟨_, _, u₀, hw₀⟩ := hP
          exact IsWalk_edges_mem hw₀ ha
        let H' : MGraph := { H with E := H.E.erase a.1 }
        have hH'm : H'.E.card < m := by
          rw [← hm, Finset.card_erase_of_mem haE]
          have : 0 < H.E.card := Finset.card_pos.mpr ⟨a.1, haE⟩
          omega
        have hH'v : H'.IsValid := fun x hx => hHv x (Finset.mem_of_mem_erase hx)
        have hH'c : ∀ u ∈ V, ∀ v ∈ V, H'.Connected u v := fun u hu v hv =>
          connected_erase_cycle_edge hP (mem_walkEdges_of_mem ha) u v (hHc u hu v hv)
        obtain ⟨T, hT, hsub', _⟩ := ih H'.E.card hH'm H' rfl hH'v hHV hH'c
        have hsub : H.IsSubgraph T :=
          ⟨hsub'.1, hsub'.2.1.trans (Finset.erase_subset a.1 H.E),
            fun x hx => hsub'.2.2 x hx⟩
        have hlt : T.E.card < H.E.card := by
          have : T.E.card ≤ H'.E.card := Finset.card_le_card hsub'.2.1
          omega
        exact ⟨T, hT, hsub, fun _ _ => hlt⟩
      · have hF : H.IsForest := ⟨hHv, fun P hP => hcyc ⟨P, hP⟩⟩
        have hT : H.IsSpanningTreeOn V := ⟨hF, hHV, hHc⟩
        exact ⟨H, hT, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩,
          fun P hP => absurd ⟨P, hP⟩ hcyc⟩
  obtain ⟨T, hT, _, hlt⟩ := exists_tree_sub G.E.card G rfl hvalid hV hconn
  refine ⟨⟨hvalid, fun P hP => ?_⟩, hV, hconn⟩
  have h1 := hlt P hP
  have h2 := spanningTree_edge_card hT hne
  omega

/-! ## Rooted spanning forests (`Definition 5.2`) -/

lemma rootedForest_root_spec {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {v : ℕ} (hv : v ∈ G.V) :
    RF.root v ∈ RF.R ∧ RF.F.Connected v (RF.root v) := by
  unfold RootedForest.root
  obtain ⟨r, ⟨hr, _⟩⟩ := hRF.2.2.2.1 v hv
  have hex : ∃ r, r ∈ RF.R ∧ RF.F.Connected v r := ⟨r, hr⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

lemma rootedForest_root_eq_of_mem {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {v r : ℕ} (hv : v ∈ G.V)
    (hr : r ∈ RF.R) (hconn : RF.F.Connected v r) : RF.root v = r := by
  obtain ⟨_, _, huniq⟩ := hRF.2.2.2.1 v hv
  have hspec := rootedForest_root_spec hRF hv
  exact (huniq (RF.root v) hspec).trans (huniq r ⟨hr, hconn⟩).symm

lemma rootedForest_root_self {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {r : ℕ} (hr : r ∈ RF.R) : RF.root r = r :=
  rootedForest_root_eq_of_mem hRF (hRF.2.2.1 hr) hr (connected_refl RF.F r)

lemma rootedForest_root_eq_iff {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V) :
    RF.root u = RF.root v ↔ RF.F.Connected u v := by
  have hsu := rootedForest_root_spec hRF hu
  have hsv := rootedForest_root_spec hRF hv
  refine ⟨fun hEq => ?_, fun huv => ?_⟩
  · exact connected_trans hsu.2 (connected_symm (hEq ▸ hsv.2))
  · exact rootedForest_root_eq_of_mem hRF hu hsv.1 (connected_trans huv hsv.2)

lemma rootedForest_components_card {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) :
    (components RF.F).card = RF.R.card := by
  have hEq : components RF.F = RF.R.image (compOf RF.F) := by
    ext C
    simp only [components, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvG : v ∈ G.V := hRF.2.1 ▸ hv
      have hs := rootedForest_root_spec hRF hvG
      exact ⟨RF.root v, hs.1, compOf_eq_of_connected (connected_symm hs.2)⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hRF.2.1 ▸ hRF.2.2.1 hr, rfl⟩
  rw [hEq, Finset.card_image_of_injOn]
  intro r₁ hr₁ r₂ hr₂ hC
  have hr₂V : r₂ ∈ RF.F.V := hRF.2.1 ▸ hRF.2.2.1 hr₂
  have hconn : RF.F.Connected r₁ r₂ := (compOf_eq_iff hr₂V).mp hC
  rw [← rootedForest_root_self hRF hr₁, ← rootedForest_root_self hRF hr₂]
  exact (rootedForest_root_eq_iff hRF (hRF.2.2.1 hr₁) (hRF.2.2.1 hr₂)).mpr hconn

lemma rootedForest_stretch_eq_one_of_roots {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) (ℓ : ℕ → ℝ) {e : ℕ}
    (htail : G.tail e ∈ RF.R) (hhead : G.head e ∈ RF.R) :
    RF.stretch G ℓ e = 1 := by
  unfold RootedForest.stretch
  dsimp only
  rw [rootedForest_root_self hRF htail, rootedForest_root_self hRF hhead]
  split_ifs with hEq
  · rw [hEq, forestPath_self hRF.1]
    simp [walkLength, walkEdges]
  · rw [forestPath_self hRF.1, forestPath_self hRF.1]
    simp [walkLength, walkEdges]

end MinCostFlow.LSF
