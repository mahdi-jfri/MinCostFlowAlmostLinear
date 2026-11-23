module

public import MinCostFlow.LSF.SafePaths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma54Init, first part

The first part of `Lemma54Init.lean`, split off to keep files short. It contains:
- Update and batch validity
- Upward closure cardinality bounds
- Decomposition and weighted-copy bridge helpers
- Component representatives and bridge deletion (`G₀.IsSubgraph F₀`)
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Update and batch validity -/

lemma applyUpdate_isValid {G : MGraph} (hG : G.IsValid) {u : Update} (hu : G.UpdateIsValid u) :
    (G.applyUpdate u).IsValid := by
  intro f hf
  cases u with
  | insert e a b =>
    rcases hu with ⟨_, ha, hb⟩
    dsimp only [MGraph.applyUpdate] at hf ⊢
    rw [Finset.mem_insert] at hf
    by_cases hfe : f = e
    · subst hfe
      simp [Function.update_self, ha, hb]
    · have hfG := hf.resolve_left hfe
      simp [Function.update_of_ne hfe, hG f hfG]
  | delete e =>
    exact hG f (Finset.erase_subset _ _ hf)
  | split _ _ _ _ =>
    dsimp [MGraph.applyUpdate] at hf ⊢
    constructor
    · split_ifs
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hG f hf).1
    · split_ifs
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hG f hf).2

lemma applyBatch_isValid {G : MGraph} (hG : G.IsValid) :
    ∀ {U : List Update}, G.BatchIsValid U → (G.applyBatch U).IsValid
  | [], _ => hG
  | u :: U, ⟨hu, hU⟩ => by
    rw [MGraph.applyBatch, List.foldl_cons]
    exact applyBatch_isValid (applyUpdate_isValid hG hu) hU

/-- Validity of a sequence of batches applied sequentially to `G`. -/
def BatchesIsValid : MGraph → List (List Update) → Prop
  | _, [] => True
  | G, U :: Us => G.BatchIsValid U ∧ BatchesIsValid (G.applyBatch U) Us

/-- Total number of single updates across all batches in `Us`. -/
def totalUpdates (Us : List (List Update)) : ℕ :=
  (Us.map List.length).sum

/-! ## Upward closure cardinality bounds -/

lemma ancestors_card_le_hldDepthBound {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) :
    (ancestors (hldAuxTree T r) r u).card ≤ hldDepthBound T.V.card + 1 := by
  have hTH := hldAuxTree_isRootedTree hT
  have huTH : u ∈ (hldAuxTree T r).V := hu
  rw [ancestors_card_eq hTH huTH]
  exact Nat.succ_le_succ (hldAuxTree_height hT hu)

lemma upClosure_insert_card_le {T : MGraph} {r a : ℕ} (hT : IsRootedTree T r)
    (ha : a ∈ T.V) (S : Finset ℕ) :
    (upClosure (hldAuxTree T r) r (insert a S)).card ≤
      (upClosure (hldAuxTree T r) r S).card + (hldDepthBound T.V.card + 1) := by
  have hEq : upClosure (hldAuxTree T r) r (insert a S) =
      ancestors (hldAuxTree T r) r a ∪ upClosure (hldAuxTree T r) r S := by
    unfold upClosure
    exact Finset.biUnion_insert
  rw [hEq]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_right (ancestors_card_le_hldDepthBound hT ha)
      (upClosure (hldAuxTree T r) r S).card).trans (Nat.add_comm _ _).le)

lemma upClosure_union_ancestors_card_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) :
    (upClosure (hldAuxTree T r) r S).card ≤ S.card * (hldDepthBound T.V.card + 1) := by
  unfold upClosure
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ u ∈ S, (ancestors (hldAuxTree T r) r u).card
      ≤ ∑ _u ∈ S, (hldDepthBound T.V.card + 1) :=
        Finset.sum_le_sum (fun u hu => ancestors_card_le_hldDepthBound hT (hS hu))
    _ = S.card * (hldDepthBound T.V.card + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

lemma upClosure_insert_root_card_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) :
    (upClosure (hldAuxTree T r) r (insert r S)).card ≤
      1 + S.card * (hldDepthBound T.V.card + 1) := by
  have hTH := hldAuxTree_isRootedTree hT
  have hrTH : r ∈ (hldAuxTree T r).V := hTH.2
  have hEq : upClosure (hldAuxTree T r) r (insert r S) =
      ancestors (hldAuxTree T r) r r ∪ upClosure (hldAuxTree T r) r S := by
    unfold upClosure
    exact Finset.biUnion_insert
  have hr_card : (ancestors (hldAuxTree T r) r r).card = 1 := by
    rw [ancestors_card_eq hTH hrTH, depth, forestPath_self hTH.isForest r, List.length_nil]
  rw [hEq]
  exact (Finset.card_union_le _ _).trans
    (by rw [hr_card]; exact Nat.add_le_add_left (upClosure_union_ancestors_card_le hT hS) 1)

/-! ## Decomposition and weighted-copy bridge helpers -/

lemma isRootedTree_of_spanningTreeOn {T : MGraph} {V : Finset ℕ} {r : ℕ}
    (hST : T.IsSpanningTreeOn V) (hr : r ∈ V) : IsRootedTree T r :=
  ⟨⟨hST.1, rfl, fun u hu v hv => hST.2.2 u (hST.2.1 ▸ hu) v (hST.2.1 ▸ hv)⟩, hST.2.1.symm ▸ hr⟩

private lemma edges_empty_of_card_le_one {T : MGraph} (hT : T.IsForest) (hV : T.V.card ≤ 1) :
    T.E = ∅ := by
  by_contra hne
  have hne' : T.E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨e, he⟩ := hne'
  have huv := hT.1 e he
  have hne_end := isForest_no_selfLoop hT he
  exact hne_end (Finset.card_le_one.mp hV _ huv.1 _ huv.2)

/-! ## Component representatives and bridge deletion (`G₀.IsSubgraph F₀`) -/

private lemma compOf_subset_V {G : MGraph} (hG : G.IsValid) {v : ℕ} (hv : v ∈ G.V) :
    compOf G v ⊆ G.V := by
  intro w hw
  rw [mem_compOf_iff] at hw
  obtain ⟨P, hW⟩ := hw.2
  exact (IsWalk_vertices_mem hG hv hW).2 w (IsWalk_end_mem_walkVertices hW)

lemma compReps_mem {G : MGraph} {r₀ : ℕ} (hr₀ : r₀ ∈ G.V) : r₀ ∈ compReps G r₀ := by
  unfold compReps
  refine Finset.mem_image.mpr ⟨compOf G r₀, compOf_mem_components hr₀, ?_⟩
  simp [self_mem_compOf hr₀]

lemma compReps_subset {G : MGraph} (hG : G.IsValid) {r₀ : ℕ} (hr₀ : r₀ ∈ G.V) :
    compReps G r₀ ⊆ G.V := by
  intro x hx
  unfold compReps at hx
  rw [Finset.mem_image] at hx
  obtain ⟨C, hC, rfl⟩ := hx
  rw [components, Finset.mem_image] at hC
  obtain ⟨w, hw, rfl⟩ := hC
  split_ifs with h1 h2
  · exact hr₀
  · exact compOf_subset_V hG hw (Classical.choose_spec h2)
  · exact absurd ⟨w, self_mem_compOf hw⟩ h2

lemma compReps_connected {G : MGraph} {r₀ v : ℕ} (hv : v ∈ G.V) :
    ∃ r ∈ compReps G r₀, G.Connected v r := by
  have hvC : v ∈ compOf G v := self_mem_compOf hv
  have hne : (compOf G v).Nonempty := ⟨v, hvC⟩
  let r := if r₀ ∈ compOf G v then r₀ else Classical.choose hne
  have hr_comp : r ∈ compOf G v := by
    dsimp only [r]; split_ifs with h1
    · exact h1
    · exact Classical.choose_spec hne
  have hr_mem : r ∈ compReps G r₀ := by
    unfold compReps
    refine Finset.mem_image.mpr ⟨compOf G v, compOf_mem_components hv, ?_⟩
    dsimp only [r]
    by_cases h1 : r₀ ∈ compOf G v <;> simp [h1, hne]
  exact ⟨r, hr_mem, (mem_compOf_iff.mp hr_comp).2⟩

lemma compReps_eq_singleton_of_connected {G : MGraph} {r₀ : ℕ} (hr₀ : r₀ ∈ G.V)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    compReps G r₀ = {r₀} := by
  apply Finset.Subset.antisymm
  · intro x hx
    unfold compReps at hx
    rw [Finset.mem_image] at hx
    obtain ⟨C, hC, rfl⟩ := hx
    rw [components, Finset.mem_image] at hC
    obtain ⟨w, hw, rfl⟩ := hC
    have hrC : r₀ ∈ compOf G w := mem_compOf_iff.mpr ⟨hr₀, hconn w hw r₀ hr₀⟩
    simp only [hrC, ↓reduceIte]
    exact Finset.mem_singleton_self _
  · exact Finset.singleton_subset_iff.mpr (compReps_mem hr₀)

lemma compReps_card_le (G : MGraph) (r₀ : ℕ) : (compReps G r₀).card ≤ (components G).card :=
  Finset.card_image_le

private lemma walkEdges_forestPath_sub_of_connected {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    (hTp₀ : ∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E)
    {x y : ℕ} (hconn : G₀.Connected x y) :
    walkEdges (T₀.forestPath x y) ⊆ G₀.E := by
  obtain ⟨P, hW⟩ := hconn
  induction hW with
  | nil u =>
    rw [forestPath_self hT₀.isForest u, walkEdges]
    exact Finset.empty_subset _
  | @cons u w e xs heG hsrc hrest ih =>
    have hstep : walkEdges (T₀.forestPath u (G₀.dst e)) ⊆ G₀.E := by
      rcases e with ⟨f, _ | _⟩ <;> dsimp only [MGraph.src, MGraph.dst] at hsrc ⊢
      · rw [← hsrc, forestPath_rev hT₀.isForest
          (hT₀.connected (hTV ▸ (hG₀ f heG).1) (hTV ▸ (hG₀ f heG).2)), walkEdges_walkRev]
        exact hTp₀ f heG
      · rw [← hsrc]
        exact hTp₀ f heG
    have huV : u ∈ T₀.V := by
      rcases e with ⟨f, _ | _⟩ <;> dsimp only [MGraph.src] at hsrc <;> rw [← hsrc]
      · exact hTV ▸ (hG₀ f heG).2
      · exact hTV ▸ (hG₀ f heG).1
    have hdV : G₀.dst e ∈ T₀.V := by
      rcases e with ⟨f, _ | _⟩ <;> dsimp only [MGraph.dst]
      · exact hTV ▸ (hG₀ f heG).1
      · exact hTV ▸ (hG₀ f heG).2
    have hwV : w ∈ T₀.V := hTV ▸ (IsWalk_vertices_mem hG₀ (hTV ▸ hdV) hrest).2 w
      (IsWalk_end_mem_walkVertices hrest)
    have hW_uw : T₀.IsWalk u w (T₀.forestPath u (G₀.dst e) ++ T₀.forestPath (G₀.dst e) w) :=
      IsWalk_append
        (forestPath_isPath hT₀.isForest (hT₀.connected huV hdV)).1
        (forestPath_isPath hT₀.isForest (hT₀.connected hdV hwV)).1
    have hmem := mem_walkEdges_forestPath_of_isWalk hT₀.isForest hW_uw
    intro g hg
    have hg' := hmem hg
    rw [walkEdges_append, Finset.mem_union] at hg'
    exact hg'.elim (fun h => hstep h) (fun h => ih h)

lemma forestGivenRoots_isSubgraph_of_compReps {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    (hTG₀ : ∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f)
    (hTp₀ : ∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E)
    {π : ℕ → ℕ} (hpi_br : ∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g)
    {R : Finset ℕ} (hR : IsBranchFree T₀ r₀ R) (hrR : r₀ ∈ R)
    (hcomp : ∀ v ∈ G₀.V, ∃ r ∈ R, G₀.Connected v r) :
    G₀.IsSubgraph (forestGivenRoots T₀ r₀ R π) := by
  classical
  have hsubE : (forestGivenRoots T₀ r₀ R π).E ⊆ T₀.E := Finset.sdiff_subset
  have hconn_sub : ∀ {x y : ℕ}, G₀.Connected x y → walkEdges (T₀.forestPath x y) ⊆ G₀.E :=
    fun h => walkEdges_forestPath_sub_of_connected hG₀ hT₀ hTV hTp₀ h
  have hmemE : (forestGivenRoots T₀ r₀ R π).E ⊆ G₀.E := by
    intro f hf
    have hfT : f ∈ T₀.E := hsubE hf
    by_contra hf_nG₀
    obtain ⟨c, hcV, hcr, hpec⟩ : ∃ c ∈ T₀.V, c ≠ r₀ ∧ parentEdge T₀ r₀ c = f := by
      rcases edge_parent_orientation hT₀ hfT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
      · exact ⟨T₀.tail f, (hT₀.isForest.1 f hfT).1, hne, hpe⟩
      · exact ⟨T₀.head f, (hT₀.isForest.1 f hfT).2, hne, hpe⟩
    let p := parent T₀ r₀ c
    have hpV : p ∈ T₀.V := parent_mem hT₀ hcV
    have hp_anc : IsAncestor T₀ r₀ p c := isAncestor_parent hT₀ hcV hcr
    have hp_ne : p ≠ c := parent_ne_self hT₀ hcV hcr
    obtain ⟨rc, hrc_R, hconn_c⟩ := hcomp c (hTV ▸ hcV)
    obtain ⟨rp, hrp_R, hconn_p⟩ := hcomp p (hTV ▸ hpV)
    have hrcV : rc ∈ T₀.V := hR.1 hrc_R
    have hrpV : rp ∈ T₀.V := hR.1 hrp_R
    have h_not_crc : f ∉ walkEdges (T₀.forestPath c rc) := fun h => hf_nG₀ (hconn_sub hconn_c h)
    have h_not_prp : f ∉ walkEdges (T₀.forestPath p rp) := fun h => hf_nG₀ (hconn_sub hconn_p h)
    have h_anc_rc : IsAncestor T₀ r₀ c rc := by
      rw [← hpec, parentEdge_mem_walkEdges_iff hT₀ hcV hcr hcV hrcV] at h_not_crc
      push Not at h_not_crc
      exact (h_not_crc.mp (isAncestor_refl T₀ r₀ c))
    have hn_anc_rp : ¬ IsAncestor T₀ r₀ c rp := by
      rw [← hpec, parentEdge_mem_walkEdges_iff hT₀ hcV hcr hpV hrpV] at h_not_prp
      push Not at h_not_prp
      intro hcp
      exact hp_ne (isAncestor_antisymm hT₀ hpV hcV hp_anc (h_not_prp.mpr hcp))
    let Sc := R.filter (fun z => IsAncestor T₀ r₀ c z)
    have hSc_ne : Sc.Nonempty := ⟨rc, Finset.mem_filter.mpr ⟨hrc_R, h_anc_rc⟩⟩
    obtain ⟨x, hxSc, hx_min⟩ := Finset.exists_min_image Sc (depth T₀ r₀) hSc_ne
    have hxR : x ∈ R := (Finset.mem_filter.mp hxSc).1
    have hcx : IsAncestor T₀ r₀ c x := (Finset.mem_filter.mp hxSc).2
    have hxV : x ∈ T₀.V := hR.1 hxR
    have hxr : x ≠ r₀ := fun h =>
      hcr (isAncestor_antisymm hT₀ hT₀.2 hcV (isAncestor_root hT₀ hcV) (h ▸ hcx)).symm
    have htop_eq : topRoot T₀ r₀ R = r₀ :=
      isAncestor_antisymm hT₀ (hR.1 (topRoot_mem hT₀ hR ⟨r₀, hrR⟩)) hT₀.2
        (topRoot_isAncestor hT₀ hR ⟨r₀, hrR⟩ hrR)
        (isAncestor_root hT₀ (hR.1 (topRoot_mem hT₀ hR ⟨r₀, hrR⟩)))
    have hx_erase : x ∈ R.erase (topRoot T₀ r₀ R) :=
      Finset.mem_erase.mpr ⟨htop_eq.symm ▸ hxr, hxR⟩
    let px := rootParent T₀ r₀ R x
    have hpx := rootParent_spec hT₀ hR ⟨r₀, hrR⟩ hx_erase
    have hn_anc_cpx : ¬ IsAncestor T₀ r₀ c px := by
      intro hcp
      have hd_min := hx_min px (Finset.mem_filter.mpr ⟨hpx.1, hcp⟩)
      have hd_lt : depth T₀ r₀ px < depth T₀ r₀ x := by
        have hpxV := hR.1 hpx.1
        have hle := isAncestor_depth_le hT₀ hxV hpx.2.2.1
        by_contra hge
        exact hpx.2.1 ((isAncestor_eq_iff_depth hT₀ hxV hpx.2.2.1).mp
          (Nat.le_antisymm hle (Nat.le_of_not_lt hge)))
      omega
    have hf_path : f ∈ walkEdges (T₀.forestPath x px) := by
      rw [← hpec, parentEdge_mem_walkEdges_ancestor_iff hT₀ hcV hcr hxV hpx.2.2.1]
      exact ⟨hcx, hn_anc_cpx⟩
    have hother_G₀ : ∀ g ∈ walkEdges (T₀.forestPath x px), g ≠ f → g ∈ G₀.E := by
      intro g hg hgf
      have hgT : g ∈ T₀.E := walkEdges_forestPath_sub_edges hT₀.isForest hg
      obtain ⟨w, hwV, hwr, hpew⟩ : ∃ w ∈ T₀.V, w ≠ r₀ ∧ parentEdge T₀ r₀ w = g := by
        rcases edge_parent_orientation hT₀ hgT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
        · exact ⟨T₀.tail g, (hT₀.isForest.1 g hgT).1, hne, hpe⟩
        · exact ⟨T₀.head g, (hT₀.isForest.1 g hgT).2, hne, hpe⟩
      have hwg := hg
      rw [← hpew, parentEdge_mem_walkEdges_ancestor_iff hT₀ hwV hwr hxV hpx.2.2.1] at hwg
      rcases isAncestor_total_on_ancestors hT₀ hxV hwg.1 hcx with hwc | hcw
      · have hwc_ne : w ≠ c := fun h => hgf (by rw [← hpew, h, hpec])
        have hwp : IsAncestor T₀ r₀ w p := by
          rcases (isAncestor_iff_eq_or_parent hT₀ hcV).mp hwc with hEq | ⟨_, hwp⟩
          · exact absurd hEq hwc_ne
          · exact hwp
        let z := lca T₀ r₀ x rp
        have hzR : z ∈ R := hR.2 _ hxR _ hrp_R
        have hzx : IsAncestor T₀ r₀ z x := lca_isAncestor_left hT₀ hxV hrpV
        have hzr : IsAncestor T₀ r₀ z rp := lca_isAncestor_right hT₀ hxV hrpV
        have hzx_ne : z ≠ x := fun h => hn_anc_rp
          (isAncestor_trans hT₀ hrpV (h ▸ hcx) hzr)
        have hzpx : IsAncestor T₀ r₀ z px := hpx.2.2.2 z hzR hzx_ne hzx
        have hn_wz : ¬ IsAncestor T₀ r₀ w z := fun hwz =>
          hwg.2 (isAncestor_trans hT₀ (hR.1 hpx.1) hwz hzpx)
        have hn_wrp : ¬ IsAncestor T₀ r₀ w rp := fun hwrp =>
          hn_wz ((isAncestor_lca_iff hT₀ hxV hrpV).mpr ⟨hwg.1, hwrp⟩)
        have hg_in : g ∈ walkEdges (T₀.forestPath p rp) := by
          rw [← hpew, parentEdge_mem_walkEdges_iff hT₀ hwV hwr hpV hrpV]
          exact fun hiff => hn_wrp (hiff.mp hwp)
        exact hconn_sub hconn_p hg_in
      · have hcw_ne : c ≠ w := fun h => hgf (by rw [← hpew, ← h, hpec])
        have hn_wc : ¬ IsAncestor T₀ r₀ w c := fun hwc =>
          hcw_ne (isAncestor_antisymm hT₀ hcV hwV hcw hwc)
        let y := lca T₀ r₀ x rc
        have hyR : y ∈ R := hR.2 _ hxR _ hrc_R
        have hyx : IsAncestor T₀ r₀ y x := lca_isAncestor_left hT₀ hxV hrcV
        have hyrc : IsAncestor T₀ r₀ y rc := lca_isAncestor_right hT₀ hxV hrcV
        have hcy : IsAncestor T₀ r₀ c y := (isAncestor_lca_iff hT₀ hxV hrcV).mpr ⟨hcx, h_anc_rc⟩
        have hy_min := hx_min y (Finset.mem_filter.mpr ⟨hyR, hcy⟩)
        have hxy : x = y := (isAncestor_eq_iff_depth hT₀ hxV hyx).mp
          (Nat.le_antisymm (isAncestor_depth_le hT₀ hxV hyx) hy_min) |>.symm
        have hxrc : IsAncestor T₀ r₀ x rc := hxy ▸ hyrc
        have hwrc : IsAncestor T₀ r₀ w rc := isAncestor_trans hT₀ hrcV hwg.1 hxrc
        have hg_in : g ∈ walkEdges (T₀.forestPath c rc) := by
          rw [← hpew, parentEdge_mem_walkEdges_iff hT₀ hwV hwr hcV hrcV]
          exact fun hiff => hn_wc (hiff.mpr hwrc)
        exact hconn_sub hconn_c hg_in
    have hSne : (walkEdges (T₀.forestPath x px)).Nonempty := ⟨f, hf_path⟩
    let m := minEdgeOn π (walkEdges (T₀.forestPath x px))
    have hm_spec := minEdgeOn_spec (π := π) hSne
    have hmf : m = f := by
      by_contra hne
      have hmT : m ∈ T₀.E := walkEdges_forestPath_sub_edges hT₀.isForest hm_spec.1
      have hmG : m ∈ G₀.E := hother_G₀ m hm_spec.1 hne
      have hlt := hpi_br f hfT hf_nG₀ m hmT hmG
      exact Nat.not_lt.mpr (hm_spec.2 f hf_path) hlt
    have hf_del : f ∈ deletedEdges T₀ r₀ R π := by
      unfold deletedEdges
      rw [ite_eq_left ⟨r₀, hrR⟩, Finset.mem_image]
      exact ⟨x, hx_erase, hmf⟩
    exact (Finset.mem_sdiff.mp hf).2 hf_del
  · refine ⟨hTV.subset, hmemE, fun f hf => ?_⟩
    have hfG₀ := hmemE hf
    have hfT := hsubE hf
    exact hTG₀ f hfT hfG₀

lemma vol_le_two_mul_filter_card (G : MGraph) (S : Finset ℕ) :
    G.vol S ≤ 2 * (G.E.filter (fun e => G.tail e ∈ S ∨ G.head e ∈ S)).card := by
  have h1 : G.vol S = ∑ x ∈ S, ∑ e ∈ G.E, ((if G.tail e = x then 1 else 0) +
      (if G.head e = x then 1 else 0)) := by
    unfold MGraph.vol MGraph.deg
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_add_distrib]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ e ∈ G.E, ∑ x ∈ S, ((if G.tail e = x then 1 else 0) +
        (if G.head e = x then 1 else 0)) ≤
      if G.tail e ∈ S ∨ G.head e ∈ S then 2 else 0 := by
    intro e _
    rw [Finset.sum_add_distrib]
    have ht : ∑ x ∈ S, (if G.tail e = x then 1 else 0) ≤ if G.tail e ∈ S then 1 else 0 := by
      simp
    have hh : ∑ x ∈ S, (if G.head e = x then 1 else 0) ≤ if G.head e ∈ S then 1 else 0 := by
      simp
    have hsum := Nat.add_le_add ht hh
    refine hsum.trans ?_
    by_cases h1 : G.tail e ∈ S <;> by_cases h2 : G.head e ∈ S <;> simp [h1, h2]
  calc ∑ e ∈ G.E, ∑ x ∈ S, ((if G.tail e = x then 1 else 0) + (if G.head e = x then 1 else 0))
      ≤ ∑ e ∈ G.E, (if G.tail e ∈ S ∨ G.head e ∈ S then 2 else 0) := Finset.sum_le_sum h2
    _ = 2 * (G.E.filter (fun e => G.tail e ∈ S ∨ G.head e ∈ S)).card := by
        classical
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]

lemma pickDecomp_spec {G₀ T₀ : MGraph} {r₀ : ℕ} (hG₀ : G₀.IsValid)
    (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V) (_hV₀ : G₀.V.Nonempty)
    {k : ℝ} (hk : 0 < k) :
    let W_T := pickDecomp G₀ T₀ r₀ k
    let D1 : ℝ := ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)
    (∀ W₀ ∈ W_T, PathConvex T₀ W₀) ∧
    (∀ W₀₁ ∈ W_T, ∀ W₀₂ ∈ W_T, W₀₁ ≠ W₀₂ →
      Disjoint (inducedEdges T₀ W₀₁) (inducedEdges T₀ W₀₂)) ∧
    W_T.biUnion (inducedEdges T₀) = T₀.E ∧
    ((boundary W_T).card : ℝ) ≤ 2 * (G₀.E.card : ℝ) / (k * D1) ∧
    (W_T.card : ℝ) ≤ 6 * (G₀.E.card : ℝ) / k + 6 ∧
    (∀ W₀ ∈ W_T, (G₀.vol (W₀ \ boundary W_T) : ℝ) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) := by
  classical
  by_cases hV2 : 2 ≤ G₀.V.card
  · have hcond : G₀.IsValid ∧ IsRootedTree T₀ r₀ ∧ T₀.V = G₀.V ∧ 2 ≤ G₀.V.card ∧ 0 < k :=
      ⟨hG₀, hT₀, hTV, hV2, hk⟩
    have hD1_pos : (0 : ℝ) < ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hsp := (lemma_B_7 hG₀ hT₀ hTV hV2 (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) (mul_pos hk hD1_pos)).choose_spec
    have hEq : pickDecomp G₀ T₀ r₀ k =
        (lemma_B_7 hG₀ hT₀ hTV hV2 (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
          (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) (mul_pos hk hD1_pos)).choose := by
      unfold pickDecomp
      rw [dite_eq_left_of_eq_true (eq_true hcond)]
    rw [hEq]
    refine ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.2.2.1, ?_, ?_⟩
    · have h1le : (1 : ℝ) ≤ ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hk_le : k ≤ k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) :=
        le_mul_of_one_le_right (le_of_lt hk) h1le
      have hdiv : 6 * (G₀.E.card : ℝ) / (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) ≤
          6 * (G₀.E.card : ℝ) / k :=
        div_le_div_of_nonneg_left (by positivity) hk hk_le
      linarith [hsp.2.2.2.2.1]
    · intro W₀ hW₀
      have hv0 := hsp.2.2.2.2.2.2.2 W₀ hW₀
      have hD_le := hldDepthBound_add_one_le G₀.n
      have hlog_nn : 0 ≤ Real.log ((G₀.n : ℝ) + 2) :=
        by linarith [half_lt_log_add_two G₀.n]
      let W_B := (lemma_B_7 hG₀ hT₀ hTV hV2 (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
          (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) (mul_pos hk hD1_pos)).choose
      have hvol_le : (G₀.vol (W₀ \ boundary W_B) : ℝ) ≤
          2 * ∑ e ∈ G₀.E.filter (fun e =>
            (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary W_B) ∨
            (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary W_B)), (1 : ℝ) := by
        have hnat := vol_le_two_mul_filter_card G₀ (W₀ \ boundary W_B)
        have hfil : G₀.E.filter (fun e => G₀.tail e ∈ W₀ \ boundary W_B ∨ G₀.head e ∈ W₀ \ boundary W_B) =
            G₀.E.filter (fun e => (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary W_B) ∨
              (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary W_B)) := by
          apply Finset.filter_congr
          intro e _
          simp only [Finset.mem_sdiff]
        rw [hfil] at hnat
        have hcast : (G₀.vol (W₀ \ boundary W_B) : ℝ) ≤
            2 * ((G₀.E.filter (fun e => (G₀.tail e ∈ W₀ ∧ G₀.tail e ∉ boundary W_B) ∨
              (G₀.head e ∈ W₀ ∧ G₀.head e ∉ boundary W_B))).card : ℝ) := by
          exact_mod_cast hnat
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hcast
      have h40_bound : 2 * (40 * (∑ _e ∈ G₀.E, (1 : ℝ)) * (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) /
          (G₀.E.card : ℝ)) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        by_cases hE : G₀.E.card = 0
        · rw [hE, Nat.cast_zero, div_zero, mul_zero]
          positivity
        · have hm_ne : (G₀.E.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hE
          calc 2 * (40 * (G₀.E.card : ℝ) * (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)) / (G₀.E.card : ℝ))
              = 80 * k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ) := by field_simp [hm_ne]; ring
            _ ≤ 80 * k * (28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) :=
                mul_le_mul_of_nonneg_left hD_le (by positivity)
            _ = 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by ring
      exact hvol_le.trans ((mul_le_mul_of_nonneg_left hv0 zero_le_two).trans h40_bound)
  · have hEq : pickDecomp G₀ T₀ r₀ k = ∅ := by
      unfold pickDecomp
      rw [dite_eq_right_iff.mpr (fun h => absurd h.2.2.2.1 hV2)]
    have hV1 : T₀.V.card ≤ 1 := by rw [hTV]; omega
    have hTE : T₀.E = ∅ := edges_empty_of_card_le_one hT₀.isForest hV1
    have hB : boundary (∅ : Finset (Finset ℕ)) = ∅ := by
      ext v
      simp only [mem_boundary_iff, Finset.notMem_empty, false_and, exists_false]
    rw [hEq]
    refine ⟨fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (Finset.notMem_empty _), ?_, ?_, ?_,
      fun _ h => absurd h (Finset.notMem_empty _)⟩
    · simp [hTE]
    · rw [hB, Finset.card_empty, Nat.cast_zero]
      positivity
    · rw [Finset.card_empty, Nat.cast_zero]
      positivity

private lemma projectEdge_not_mem_weightedCopyGraph {G₀ : MGraph} (hE : G₀.E.Nonempty)
    {v : ℕ → ℝ} {f : ℕ} (hf : f ∉ (weightedCopyGraph G₀ v).E) :
    f + copyMod G₀ ∉ (weightedCopyGraph G₀ v).E := by
  intro hmem
  rw [mem_weightedCopyGraph_E_iff hE] at hmem
  obtain ⟨e, he, j, hj, hEq⟩ := hmem
  unfold copyId at hEq
  cases j with
  | zero =>
    have hlt := lt_copyMod he
    omega
  | succ j' =>
    have hsub : copyId (copyMod G₀) e j' = f := by
      unfold copyId
      rw [Nat.mul_succ] at hEq
      omega
    exact hf ((mem_weightedCopyGraph_E_iff hE).mpr ⟨e, he, j', Nat.lt_of_succ_lt hj, hsub⟩)

lemma projectTree_G_v_edges {G₀ T_raw : MGraph} {v : ℕ → ℝ}
    (hE : G₀.E.Nonempty) (hv : ∀ e ∈ G₀.E, 0 < v e) :
    let T₀ := projectTree G₀ v T_raw
    let G_v := weightedCopyGraph G₀ v
    ∀ f' ∈ T₀.E, f' ∈ G_v.E → T₀.tail f' = G_v.tail f' ∧ T₀.head f' = G_v.head f' := by
  intro T₀ G_v f' hf'T hf'Gv
  have hT₀_unfold : T₀ = {
      V := T_raw.V
      E := T_raw.E.image (projectEdge G₀ v)
      tail := fun e => if e ∈ G₀.E then G₀.tail e else T_raw.tail (e - copyMod G₀)
      head := fun e => if e ∈ G₀.E then G₀.head e else T_raw.head (e - copyMod G₀) } := by
    change projectTree G₀ v T_raw = _
    unfold projectTree
    rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
  have hf'_img : f' ∈ T_raw.E.image (projectEdge G₀ v) := by
    rw [hT₀_unfold] at hf'T
    exact hf'T
  rw [Finset.mem_image] at hf'_img
  obtain ⟨f_raw, _, rfl⟩ := hf'_img
  by_cases hf_in : f_raw ∈ G_v.E
  · have hpe : projectEdge G₀ v f_raw = origEdge (copyMod G₀) f_raw := by
      unfold projectEdge
      exact ite_eq_left_iff.mpr (fun h => absurd hf_in h)
    have horig : origEdge (copyMod G₀) f_raw ∈ G₀.E :=
      (weightedCopyGraph_origEdge_mem hE hf_in).1
    have hsub := weightedCopyGraph_subgraph hv
    have hT₀_G₀ : T₀.tail (origEdge (copyMod G₀) f_raw) = G₀.tail (origEdge (copyMod G₀) f_raw) ∧
        T₀.head (origEdge (copyMod G₀) f_raw) = G₀.head (origEdge (copyMod G₀) f_raw) := by
      rw [hT₀_unfold]
      dsimp only
      rw [ite_eq_left_iff.mpr (fun h => absurd horig h),
          ite_eq_left_iff.mpr (fun h => absurd horig h)]
      exact ⟨rfl, rfl⟩
    rw [hpe]
    exact ⟨hT₀_G₀.1.trans (hsub.2.2 _ horig).1, hT₀_G₀.2.trans (hsub.2.2 _ horig).2⟩
  · have hpe : projectEdge G₀ v f_raw = f_raw + copyMod G₀ := by
      unfold projectEdge
      exact ite_eq_right_iff.mpr (fun h => absurd h hf_in)
    rw [hpe] at hf'Gv
    exact absurd hf'Gv (projectEdge_not_mem_weightedCopyGraph hE hf_in)

lemma RF_stretch_G0_eq_Gv {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hE : G₀.E.Nonempty) (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    {ℓ₀ v : ℕ → ℝ} (_hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (_hv : ∀ e ∈ G₀.E, 0 < v e)
    (_hTG₀ : ∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f)
    (hTpaths : ∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T₀ π)
    (hpi_bridge : ∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g)
    {R : Finset ℕ} (hR : IsBranchFree T₀ r₀ R) (hrR : r₀ ∈ R)
    {e' : ℕ} (he' : e' ∈ (weightedCopyGraph G₀ v).E) :
    let G_v := weightedCopyGraph G₀ v
    let ℓ_v := weightedCopyLen G₀ ℓ₀
    let RF := rootedForestGivenRoots T₀ r₀ R π
    let e := origEdge (copyMod G₀) e'
    RF.stretch G₀ (safeLen G₀ ℓ₀) e = RF.stretch G_v ℓ_v e' := by
  classical
  intro G_v ℓ_v RF e
  have horig := weightedCopyGraph_origEdge_mem hE he'
  have heG₀ : e ∈ G₀.E := horig.1
  have htail_eq : G_v.tail e' = G₀.tail e := horig.2.1
  have hhead_eq : G_v.head e' = G₀.head e := horig.2.2
  have hℓ_eq_e : safeLen G₀ ℓ₀ e = ℓ_v e' := by
    rw [safeLen_eq_of_mem ℓ₀ heG₀]
    rfl
  have hℓ_agree : ∀ f ∈ G₀.E, safeLen G₀ ℓ₀ f = ℓ_v f := by
    intro f hf
    rw [safeLen_eq_of_mem ℓ₀ hf]
    change ℓ₀ f = ℓ₀ (origEdge (copyMod G₀) f)
    unfold origEdge
    rw [Nat.mod_eq_of_lt (lt_copyMod hf)]
  have hwalk_len_eq : ∀ {a b : ℕ} {P : List (ℕ × Bool)}, T₀.IsPath a b P →
      walkEdges P ⊆ G₀.E → walkLength (safeLen G₀ ℓ₀) P = walkLength ℓ_v P := by
    intro a b P hP hsub
    rw [walkLength_eq_sum_of_isPath _ hP, walkLength_eq_sum_of_isPath _ hP]
    exact Finset.sum_congr rfl (fun f hf => hℓ_agree f (hsub hf))
  have hRne : R.Nonempty := ⟨r₀, hrR⟩
  have hRS := forestGivenRoots_isRootedSpanningForest hT₀ hR hRne π
  have hF_sub : T₀.IsSubgraph RF.F := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have huV : G₀.tail e ∈ T₀.V := hTV ▸ (hG₀ e heG₀).1
  have hvV : G₀.head e ∈ T₀.V := hTV ▸ (hG₀ e heG₀).2
  unfold RootedForest.stretch
  dsimp only
  rw [htail_eq, hhead_eq, hℓ_eq_e]
  by_cases h_eq : RF.root (G₀.tail e) = RF.root (G₀.head e)
  · rw [ite_eq_left_iff.mpr (fun h => absurd h_eq h),
      ite_eq_left_iff.mpr (fun h => absurd h_eq h)]
    have hconn : RF.F.Connected (G₀.tail e) (G₀.head e) :=
      connected_trans (rootedForest_root_spec hRS huV).2
        (connected_symm (h_eq ▸ (rootedForest_root_spec hRS hvV).2))
    rw [forestPath_subgraph hT₀.isForest hF_sub hconn]
    rw [hwalk_len_eq (forestPath_isPath hT₀.isForest (hT₀.connected huV hvV)) (hTpaths e heG₀)]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h h_eq),
      ite_eq_right_iff.mpr (fun h => absurd h h_eq)]
    have hconn_u := (rootedForest_root_spec hRS huV).2
    have hconn_v := (rootedForest_root_spec hRS hvV).2
    have huR_V : RF.root (G₀.tail e) ∈ T₀.V := hR.1 (rootedForest_root_spec hRS huV).1
    have hvR_V : RF.root (G₀.head e) ∈ T₀.V := hR.1 (rootedForest_root_spec hRS hvV).1
    have hvu_sub : walkEdges (T₀.forestPath (G₀.head e) (G₀.tail e)) ⊆ G₀.E := by
      rw [forestPath_rev hT₀.isForest (hT₀.connected huV hvV), walkEdges_walkRev]
      exact hTpaths e heG₀
    have hu_sub := no_bridge_in_endpoint_path hT₀ hR hrR hord hpi_bridge huV hvV
      (hTpaths e heG₀) (Or.inl h_eq)
    have hv_sub := no_bridge_in_endpoint_path hT₀ hR hrR hord hpi_bridge hvV huV
      hvu_sub (Or.inl (Ne.symm h_eq))
    rw [forestPath_subgraph hT₀.isForest hF_sub hconn_u,
      forestPath_subgraph hT₀.isForest hF_sub hconn_v,
      hwalk_len_eq (forestPath_isPath hT₀.isForest (hT₀.connected huV huR_V)) hu_sub,
      hwalk_len_eq (forestPath_isPath hT₀.isForest (hT₀.connected hvV hvR_V)) hv_sub]

lemma levelStretchBound_G0_eq_Gv {G₀ T₀ : MGraph} {r₀ : ℕ}
    (hG₀ : G₀.IsValid) (hE : G₀.E.Nonempty) (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G₀.V)
    {ℓ₀ v : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    (hTG₀ : ∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f)
    (hTpaths : ∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T₀ π)
    (hpi_bridge : ∀ b ∈ T₀.E, b ∉ G₀.E → ∀ g ∈ T₀.E, g ∈ G₀.E → π b < π g)
    {e' : ℕ} (he' : e' ∈ (weightedCopyGraph G₀ v).E) :
    let G_v := weightedCopyGraph G₀ v
    let ℓ_v := weightedCopyLen G₀ ℓ₀
    levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) (origEdge (copyMod G₀) e') =
      levelStretchBound T₀ r₀ π G_v ℓ_v e' := by
  intro G_v ℓ_v
  unfold levelStretchBound
  dsimp only
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hBi_bf : IsBranchFree T₀ r₀ (levelRoots T₀ r₀ i) :=
    upClosure_levelRoots hT₀ ▸ upClosure_isBranchFree hT₀ levelRoots_subset
  exact RF_stretch_G0_eq_Gv hG₀ hE hT₀ hTV hℓ₀ hv hTG₀ hTpaths hord hpi_bridge hBi_bf
    (root_mem_levelRoots hT₀) he'


end MinCostFlow.LSF
