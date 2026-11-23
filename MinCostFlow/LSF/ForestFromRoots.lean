module

public import MinCostFlow.LSF.Subtrees
import Mathlib.Data.Finset.Max

/-!
# Rooted spanning forests from branch-free root sets ([chen2022maximum] Appendix B.3)

This file formalizes Definitions B.3 and B.4 of [chen2022maximum, Appendix B.3]:
* `IsBranchFree` (Definition B.3): closed under taking LCA in `(T, r)`.
* `forestGivenRoots` / `rootedForestGivenRoots` (`F_T(R, π)`, Definition B.4): deleting the
  `π`-smallest edge on each path between adjacent roots in a branch-free set `R`.
* Proof that `F_T(R, π)` is a rooted spanning forest with `|R|` components and is decremental as
  `R` grows (`deletedEdges_mono`).
* `congOrder`: canonical edge order sorted by increasing weight/congestion.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Branch-free sets and adjacent roots (Definition B.3) -/

/-- A subset `R ⊆ V(T)` is branch-free in `(T, r)` if the LCA of any two vertices in `R` also lies
in `R` (`[chen2022maximum, Definition B.3]`). -/
def IsBranchFree (T : MGraph) (r : ℕ) (R : Finset ℕ) : Prop :=
  R ⊆ T.V ∧ ∀ r₁ ∈ R, ∀ r₂ ∈ R, lca T r r₁ r₂ ∈ R

lemma lcaClosure_isBranchFree {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) : IsBranchFree T r (lcaClosure T r S) :=
  ⟨lcaClosure_subset hT hS, fun _ hx _ hy => lca_mem_lcaClosure hT hS hx hy⟩

lemma exists_topRoot {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) :
    ∃ t ∈ R, ∀ x ∈ R, IsAncestor T r t x := by
  obtain ⟨t, htR, htmin⟩ := Finset.exists_min_image R (depth T r) hRne
  refine ⟨t, htR, fun x hxR => ?_⟩
  have hl_mem : lca T r t x ∈ R := hR.2 t htR x hxR
  have htV := hR.1 htR
  have hxV := hR.1 hxR
  have hl_anc : IsAncestor T r (lca T r t x) t := lca_isAncestor_left hT htV hxV
  have hd_le := isAncestor_depth_le hT htV hl_anc
  have hd_min := htmin (lca T r t x) hl_mem
  have hEq : lca T r t x = t :=
    (isAncestor_eq_iff_depth hT htV hl_anc).mp (Nat.le_antisymm hd_le hd_min)
  exact (lca_eq_left_iff hT htV hxV).mp hEq

/-- The unique shallowest (top) root in a nonempty branch-free set `R`. -/
noncomputable def topRoot (T : MGraph) (r : ℕ) (R : Finset ℕ) : ℕ :=
  open Classical in
  if h : ∃ t ∈ R, ∀ x ∈ R, IsAncestor T r t x then Classical.choose h else r

lemma topRoot_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) :
    topRoot T r R ∈ R ∧ ∀ x ∈ R, IsAncestor T r (topRoot T r R) x := by
  have hex := exists_topRoot hT hR hRne
  unfold topRoot
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma topRoot_mem {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) :
    topRoot T r R ∈ R :=
  (topRoot_spec hT hR hRne).1

lemma topRoot_isAncestor {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x : ℕ} (hx : x ∈ R) : IsAncestor T r (topRoot T r R) x :=
  (topRoot_spec hT hR hRne).2 x hx

/-- The strict ancestors of `x` belonging to `R`. -/
noncomputable def strictRootAncestors (T : MGraph) (r : ℕ) (R : Finset ℕ) (x : ℕ) : Finset ℕ :=
  open Classical in
  (R.erase x).filter (fun a => IsAncestor T r a x)

lemma exists_rootParent {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R)) :
    ∃ p ∈ strictRootAncestors T r R x,
      ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a p := by
  have hx' := Finset.mem_erase.mp hx
  have hne_top : topRoot T r R ≠ x := hx'.1.symm
  have hSA_ne : (strictRootAncestors T r R x).Nonempty := by
    refine ⟨topRoot T r R, ?_⟩
    simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨hne_top, topRoot_mem hT hR hRne⟩, topRoot_isAncestor hT hR hRne hx'.2⟩
  obtain ⟨p, hpS, hpmax⟩ :=
    Finset.exists_max_image (strictRootAncestors T r R x) (depth T r) hSA_ne
  refine ⟨p, hpS, fun a haS => ?_⟩
  have hxV := hR.1 hx'.2
  have hp_anc : IsAncestor T r p x := by
    simp only [strictRootAncestors, Finset.mem_filter] at hpS; exact hpS.2
  have ha_anc : IsAncestor T r a x := by
    simp only [strictRootAncestors, Finset.mem_filter] at haS; exact haS.2
  rcases isAncestor_total_on_ancestors hT hxV ha_anc hp_anc with hap | hpa
  · exact hap
  · have haV := isAncestor_mem hT hxV ha_anc
    have hd_le := isAncestor_depth_le hT haV hpa
    have hd_max := hpmax a haS
    have hEq : p = a := (isAncestor_eq_iff_depth hT haV hpa).mp (Nat.le_antisymm hd_le hd_max)
    rw [hEq]
    exact isAncestor_refl T r a

/-- The closest proper ancestor of `x ∈ R \ {topRoot}` in `R`. -/
noncomputable def rootParent (T : MGraph) (r : ℕ) (R : Finset ℕ) (x : ℕ) : ℕ :=
  open Classical in
  if h : ∃ p ∈ strictRootAncestors T r R x,
      ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a p
  then Classical.choose h
  else x

lemma rootParent_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R)) :
    rootParent T r R x ∈ R ∧ rootParent T r R x ≠ x ∧
      IsAncestor T r (rootParent T r R x) x ∧
      ∀ a ∈ R, a ≠ x → IsAncestor T r a x → IsAncestor T r a (rootParent T r R x) := by
  have hex := exists_rootParent hT hR hRne hx
  suffices rootParent T r R x ∈ strictRootAncestors T r R x ∧
      ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a (rootParent T r R x) by
    simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase] at this
    exact ⟨this.1.1.2, this.1.1.1, this.1.2, fun a haR hax hanc =>
      this.2 a ⟨⟨hax, haR⟩, hanc⟩⟩
  unfold rootParent
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma no_root_between_rootParent {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R))
    {z : ℕ} (hzR : z ∈ R) (hz_on : z ∈ T.walkVertices x (T.forestPath x (rootParent T r R x))) :
    z = x ∨ z = rootParent T r R x := by
  obtain ⟨hpR, hpx, hanc_px, hmax⟩ := rootParent_spec hT hR hRne hx
  have hxV := hR.1 (Finset.mem_erase.mp hx).2
  have hpV := hR.1 hpR
  rw [mem_walkVertices_ancestorPath_iff hT hxV hanc_px] at hz_on
  by_cases hzx : z = x
  · exact Or.inl hzx
  · right
    have hzp := hmax z hzR hzx hz_on.2
    exact isAncestor_antisymm hT (hR.1 hzR) hpV hzp hz_on.1

lemma adjacent_paths_disjoint {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x₁ x₂ : ℕ} (hx₁ : x₁ ∈ R.erase (topRoot T r R)) (hx₂ : x₂ ∈ R.erase (topRoot T r R))
    (hne : x₁ ≠ x₂) :
    Disjoint (walkEdges (T.forestPath x₁ (rootParent T r R x₁)))
      (walkEdges (T.forestPath x₂ (rootParent T r R x₂))) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  have hx1R := (Finset.mem_erase.mp hx₁).2
  have hx2R := (Finset.mem_erase.mp hx₂).2
  have hx1V := hR.1 hx1R
  have hx2V := hR.1 hx2R
  obtain ⟨hp1R, _, hanc1, hmax1⟩ := rootParent_spec hT hR hRne hx₁
  obtain ⟨hp2R, _, hanc2, hmax2⟩ := rootParent_spec hT hR hRne hx₂
  have heT : e ∈ T.E := by
    have hP := forestPath_isPath hT.isForest (hT.connected hx1V (hR.1 hp1R))
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he1)
    exact IsWalk_edges_mem hP.1 ha
  have hpe_src : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = e := by
    rcases edge_parent_orientation hT heT with ⟨_, hpe, hcr⟩ | ⟨_, hpe, hcr⟩
    · exact ⟨T.tail e, (hT.isForest.1 e heT).1, hcr, hpe⟩
    · exact ⟨T.head e, (hT.isForest.1 e heT).2, hcr, hpe⟩
  obtain ⟨c, hcV, hcr, rfl⟩ := hpe_src
  have h1 := (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hx1V hanc1).mp he1
  have h2 := (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hx2V hanc2).mp he2
  set l := lca T r x₁ x₂
  have hlR : l ∈ R := hR.2 x₁ hx1R x₂ hx2R
  have hcl : IsAncestor T r c l := (isAncestor_lca_iff hT hx1V hx2V).mpr ⟨h1.1, h2.1⟩
  by_cases hl1 : l = x₁
  · have hl2 : l ≠ x₂ := hl1.symm ▸ hne
    have hlp2 : IsAncestor T r l (rootParent T r R x₂) :=
      hmax2 l hlR hl2 (lca_isAncestor_right hT hx1V hx2V)
    exact h2.2 (isAncestor_trans hT (hR.1 hp2R) hcl hlp2)
  · have hlp1 : IsAncestor T r l (rootParent T r R x₁) :=
      hmax1 l hlR hl1 (lca_isAncestor_left hT hx1V hx2V)
    exact h1.2 (isAncestor_trans hT (hR.1 hp1R) hcl hlp1)

/-! ## Total orderings on tree edges and `forestGivenRoots` (Definition B.4) -/

/-- A key function `π : ℕ → ℕ` represents a total ordering on `E(T)` when it is injective on `T.E`. -/
def IsEdgeOrder (T : MGraph) (π : ℕ → ℕ) : Prop :=
  ∀ e₁ ∈ T.E, ∀ e₂ ∈ T.E, π e₁ = π e₂ → e₁ = e₂

/-- `π` is sorted by increasing weight/congestion function `c` on `E(T)`. -/
def IsSortedByCong (T : MGraph) (c : ℕ → ℝ) (π : ℕ → ℕ) : Prop :=
  ∀ e₁ ∈ T.E, ∀ e₂ ∈ T.E, c e₁ < c e₂ → π e₁ < π e₂

/-- Canonical total ordering on `T.E` sorted by increasing `c`, breaking ties by edge ID. -/
noncomputable def congOrder (T : MGraph) (c : ℕ → ℝ) (e : ℕ) : ℕ :=
  open Classical in
  (T.E.filter (fun f => c f < c e ∨ (c f = c e ∧ f < e))).card

lemma congOrder_lt_of_lex {T : MGraph} (c : ℕ → ℝ) {e₁ e₂ : ℕ}
    (he₁ : e₁ ∈ T.E) (hlex : c e₁ < c e₂ ∨ (c e₁ = c e₂ ∧ e₁ < e₂)) :
    congOrder T c e₁ < congOrder T c e₂ := by
  classical
  unfold congOrder
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨hf.1, ?_⟩
    rcases hf.2 with hc1 | ⟨hc1, hf1⟩ <;> rcases hlex with hc2 | ⟨hc2, h12⟩
    · exact Or.inl (lt_trans hc1 hc2)
    · exact Or.inl (hc2 ▸ hc1)
    · exact Or.inl (hc1 ▸ hc2)
    · exact Or.inr ⟨hc1.trans hc2, lt_trans hf1 h12⟩
  · intro hEq
    have hmem : e₁ ∈ T.E.filter (fun f => c f < c e₂ ∨ (c f = c e₂ ∧ f < e₂)) :=
      Finset.mem_filter.mpr ⟨he₁, hlex⟩
    rw [← hEq, Finset.mem_filter] at hmem
    rcases hmem.2 with hlt | ⟨_, hlt⟩
    · exact lt_irrefl _ hlt
    · exact lt_irrefl _ hlt

lemma congOrder_isEdgeOrder (T : MGraph) (c : ℕ → ℝ) : IsEdgeOrder T (congOrder T c) := by
  intro e₁ he₁ e₂ he₂ hpi
  by_contra hne
  rcases lt_trichotomy (c e₁) (c e₂) with hlt | heq | hgt
  · exact Nat.ne_of_lt (congOrder_lt_of_lex c he₁ (Or.inl hlt)) hpi
  · rcases lt_or_gt_of_ne hne with h12 | h21
    · exact Nat.ne_of_lt (congOrder_lt_of_lex c he₁ (Or.inr ⟨heq, h12⟩)) hpi
    · exact Nat.ne_of_gt (congOrder_lt_of_lex c he₂ (Or.inr ⟨heq.symm, h21⟩)) hpi
  · exact Nat.ne_of_gt (congOrder_lt_of_lex c he₂ (Or.inl hgt)) hpi

lemma congOrder_isSortedByCong (T : MGraph) (c : ℕ → ℝ) : IsSortedByCong T c (congOrder T c) :=
  fun _ he₁ _ _ hc => congOrder_lt_of_lex c he₁ (Or.inl hc)

/-- The edge in a finite set `S` minimizing `π` (or `0` if `S` is empty). -/
noncomputable def minEdgeOn (π : ℕ → ℕ) (S : Finset ℕ) : ℕ :=
  open Classical in
  if h : ∃ e ∈ S, ∀ f ∈ S, π e ≤ π f then Classical.choose h else 0

lemma minEdgeOn_spec {π : ℕ → ℕ} {S : Finset ℕ} (hS : S.Nonempty) :
    minEdgeOn π S ∈ S ∧ ∀ f ∈ S, π (minEdgeOn π S) ≤ π f := by
  obtain ⟨e, heS, hmin⟩ := Finset.exists_min_image S π hS
  have hex : ∃ e ∈ S, ∀ f ∈ S, π e ≤ π f := ⟨e, heS, hmin⟩
  unfold minEdgeOn
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma minEdgeOn_mem {π : ℕ → ℕ} {S : Finset ℕ} (hS : S.Nonempty) :
    minEdgeOn π S ∈ S :=
  (minEdgeOn_spec hS).1

lemma minEdgeOn_le {π : ℕ → ℕ} {S : Finset ℕ} {f : ℕ} (hf : f ∈ S) :
    π (minEdgeOn π S) ≤ π f :=
  (minEdgeOn_spec ⟨f, hf⟩).2 f hf

/-- The `π`-smallest edge on `T[x, rootParent T r R x]` (`[chen2022maximum, Definition B.4]`). -/
noncomputable def deletedEdge (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) (x : ℕ) : ℕ :=
  minEdgeOn π (walkEdges (T.forestPath x (rootParent T r R x)))

/-- The set of edges deleted from `T` to form `F_T(R, π)` (`[chen2022maximum, Definition B.4]`). -/
noncomputable def deletedEdges (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) : Finset ℕ :=
  open Classical in
  if R.Nonempty then (R.erase (topRoot T r R)).image (deletedEdge T r R π) else ∅

/-- `F_T(R, π)`: the rooted spanning forest obtained by removing the `π`-smallest edge on each path
between adjacent roots of a branch-free set `R` (`[chen2022maximum, Definition B.4]`). -/
noncomputable def forestGivenRoots (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) : MGraph :=
  { T with E := T.E \ deletedEdges T r R π }

/-- `F_T(R, π)` bundled as a `RootedForest` with root set `R`. -/
noncomputable def rootedForestGivenRoots (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) :
    RootedForest :=
  { F := forestGivenRoots T r R π, R := R }

lemma walkEdges_rootParent_nonempty {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty)
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R)) :
    (walkEdges (T.forestPath x (rootParent T r R x))).Nonempty := by
  obtain ⟨hpR, hne, _, _⟩ := rootParent_spec hT hR hRne hx
  have hxV := hR.1 (Finset.mem_erase.mp hx).2
  have hpV := hR.1 hpR
  have hP := forestPath_isPath hT.isForest (hT.connected hxV hpV)
  generalize rootParent T r R x = p at hP hne ⊢
  rcases hEq : T.forestPath x p with _ | ⟨a, _⟩
  · rw [hEq] at hP
    cases hP.1
    exact absurd rfl hne
  · exact ⟨a.1, by rw [walkEdges_cons]; exact Finset.mem_insert_self _ _⟩

lemma deletedEdge_mem_walkEdges {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) {π : ℕ → ℕ}
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R)) :
    deletedEdge T r R π x ∈ walkEdges (T.forestPath x (rootParent T r R x)) :=
  minEdgeOn_mem (walkEdges_rootParent_nonempty hT hR hRne hx)

lemma deletedEdge_mem_E {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) {π : ℕ → ℕ}
    {x : ℕ} (hx : x ∈ R.erase (topRoot T r R)) :
    deletedEdge T r R π x ∈ T.E := by
  have hxV := hR.1 (Finset.mem_erase.mp hx).2
  have hpV := hR.1 (rootParent_spec hT hR hRne hx).1
  have hP := forestPath_isPath hT.isForest (hT.connected hxV hpV)
  have hmem := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx
  obtain ⟨a, ha, ha_eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
  rw [← ha_eq]
  exact IsWalk_edges_mem hP.1 ha

lemma deletedEdge_le {T : MGraph} {r : ℕ} {R : Finset ℕ} {π : ℕ → ℕ} {x f : ℕ}
    (hf : f ∈ walkEdges (T.forestPath x (rootParent T r R x))) :
    π (deletedEdge T r R π x) ≤ π f :=
  minEdgeOn_le hf

lemma deletedEdges_subset {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) {π : ℕ → ℕ} :
    deletedEdges T r R π ⊆ T.E := by
  classical
  unfold deletedEdges
  split_ifs with hRne
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact deletedEdge_mem_E hT hR hRne hx
  · exact Finset.empty_subset _

lemma deletedEdge_inj {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) {π : ℕ → ℕ} :
    ∀ x₁ ∈ R.erase (topRoot T r R), ∀ x₂ ∈ R.erase (topRoot T r R),
      deletedEdge T r R π x₁ = deletedEdge T r R π x₂ → x₁ = x₂ := by
  intro x₁ hx₁ x₂ hx₂ hEq
  by_contra hne
  have hdisj := adjacent_paths_disjoint hT hR hRne hx₁ hx₂ hne
  have hm1 := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx₁
  have hm2 := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx₂
  rw [← hEq] at hm2
  exact Finset.disjoint_left.mp hdisj hm1 hm2

lemma deletedEdges_card {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ) :
    (deletedEdges T r R π).card + 1 = R.card := by
  classical
  unfold deletedEdges
  rw [ite_eq_left_iff.mpr (fun h => absurd hRne h)]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_erase_add_one (topRoot_mem hT hR hRne)
  · intro x₁ hx₁ x₂ hx₂ hEq
    exact deletedEdge_inj hT hR hRne x₁ hx₁ x₂ hx₂ hEq

/-! ## Rooted spanning forest, component count, and decremental monotonicity -/

lemma forestGivenRoots_not_connected_roots {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ)
    {r₁ r₂ : ℕ} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R) (hne : r₁ ≠ r₂) :
    ¬ (forestGivenRoots T r R π).Connected r₁ r₂ := by
  have hr1V := hR.1 hr₁
  have hr2V := hR.1 hr₂
  intro hconn
  rw [forestGivenRoots, connected_sdiff_iff_disjoint hT.isForest (hT.connected hr1V hr2V)] at hconn
  set z := lca T r r₁ r₂
  have hzR : z ∈ R := hR.2 r₁ hr₁ r₂ hr₂
  have hzV := hR.1 hzR
  have hz1 : IsAncestor T r z r₁ := lca_isAncestor_left hT hr1V hr2V
  have hz2 : IsAncestor T r z r₂ := lca_isAncestor_right hT hr1V hr2V
  have hsep : ∃ e ∈ deletedEdges T r R π, e ∈ walkEdges (T.forestPath r₁ r₂) := by
    by_cases h1 : r₁ ≠ z
    · have htop1 : r₁ ≠ topRoot T r R := by
        intro hEq
        have hanc := topRoot_isAncestor hT hR hRne hzR
        rw [← hEq] at hanc
        exact h1 (isAncestor_antisymm hT hr1V hzV hanc hz1)
      have hx1 : r₁ ∈ R.erase (topRoot T r R) := Finset.mem_erase.mpr ⟨htop1, hr₁⟩
      have he_mem : deletedEdge T r R π r₁ ∈ deletedEdges T r R π := by
        classical
        unfold deletedEdges
        rw [ite_eq_left_iff.mpr (fun h => absurd hRne h)]
        exact Finset.mem_image_of_mem _ hx1
      have hm := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx1
      have hpx := (rootParent_spec hT hR hRne hx1).2.2.1
      have hpz : IsAncestor T r z (rootParent T r R r₁) :=
        (rootParent_spec hT hR hRne hx1).2.2.2 z hzR h1.symm hz1
      have heT : deletedEdge T r R π r₁ ∈ T.E := deletedEdge_mem_E hT hR hRne hx1
      obtain ⟨c, hcV, hcr, hce⟩ : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = deletedEdge T r R π r₁ := by
        rcases edge_parent_orientation hT heT with ⟨_, hpe, hne_r⟩ | ⟨_, hpe, hne_r⟩
        · exact ⟨T.tail _, (hT.isForest.1 _ heT).1, hne_r, hpe⟩
        · exact ⟨T.head _, (hT.isForest.1 _ heT).2, hne_r, hpe⟩
      rw [← hce] at hm
      rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hr1V hpx] at hm
      refine ⟨deletedEdge T r R π r₁, he_mem, ?_⟩
      rw [← hce, parentEdge_mem_walkEdges_iff hT hcV hcr hr1V hr2V]
      intro h_iff
      have hc2 : IsAncestor T r c r₂ := h_iff.mp hm.1
      have hcz : IsAncestor T r c z := (isAncestor_lca_iff hT hr1V hr2V).mpr ⟨hm.1, hc2⟩
      exact hm.2 (isAncestor_trans hT (hR.1 (rootParent_spec hT hR hRne hx1).1) hcz hpz)
    · push Not at h1
      have h2 : r₂ ≠ z := fun hEq => hne (h1.trans hEq.symm)
      have htop2 : r₂ ≠ topRoot T r R := by
        intro hEq
        have hanc := topRoot_isAncestor hT hR hRne hzR
        rw [← hEq] at hanc
        exact h2 (isAncestor_antisymm hT hr2V hzV hanc hz2)
      have hx2 : r₂ ∈ R.erase (topRoot T r R) := Finset.mem_erase.mpr ⟨htop2, hr₂⟩
      have he_mem : deletedEdge T r R π r₂ ∈ deletedEdges T r R π := by
        classical
        unfold deletedEdges
        rw [ite_eq_left_iff.mpr (fun h => absurd hRne h)]
        exact Finset.mem_image_of_mem _ hx2
      have hm := deletedEdge_mem_walkEdges (π := π) hT hR hRne hx2
      have hpx := (rootParent_spec hT hR hRne hx2).2.2.1
      have hpz : IsAncestor T r z (rootParent T r R r₂) :=
        (rootParent_spec hT hR hRne hx2).2.2.2 z hzR h2.symm hz2
      have heT : deletedEdge T r R π r₂ ∈ T.E := deletedEdge_mem_E hT hR hRne hx2
      obtain ⟨c, hcV, hcr, hce⟩ : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = deletedEdge T r R π r₂ := by
        rcases edge_parent_orientation hT heT with ⟨_, hpe, hne_r⟩ | ⟨_, hpe, hne_r⟩
        · exact ⟨T.tail _, (hT.isForest.1 _ heT).1, hne_r, hpe⟩
        · exact ⟨T.head _, (hT.isForest.1 _ heT).2, hne_r, hpe⟩
      rw [← hce] at hm
      rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hr2V hpx] at hm
      refine ⟨deletedEdge T r R π r₂, he_mem, ?_⟩
      rw [← hce, parentEdge_mem_walkEdges_iff hT hcV hcr hr1V hr2V]
      intro h_iff
      have hc1 : IsAncestor T r c r₁ := h_iff.mpr hm.1
      have hcz : IsAncestor T r c z := (isAncestor_lca_iff hT hr1V hr2V).mpr ⟨hc1, hm.1⟩
      exact hm.2 (isAncestor_trans hT (hR.1 (rootParent_spec hT hR hRne hx2).1) hcz hpz)
  obtain ⟨e, heD, heP⟩ := hsep
  exact Finset.disjoint_left.mp hconn heP heD

lemma forestGivenRoots_components_card {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ) :
    (components (forestGivenRoots T r R π)).card = R.card := by
  have hsub := deletedEdges_subset hT hR (π := π)
  have hcard := forest_sdiff_components_card hT.isForest hsub
  have hcompT := components_card_one_of_connected ⟨r, hT.2⟩ (fun u hu v hv => hT.connected hu hv)
  have hdel := deletedEdges_card hT hR hRne π
  unfold forestGivenRoots
  omega

lemma forestGivenRoots_isRootedSpanningForest {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ) :
    (rootedForestGivenRoots T r R π).IsRootedSpanningForestOf T := by
  classical
  let F := forestGivenRoots T r R π
  have hsubE := deletedEdges_subset hT hR (π := π)
  have hsub : T.IsSubgraph F := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have hFV : F.V = T.V := rfl
  have hF_valid : F.IsValid := by
    intro e he
    have heT : e ∈ T.E := (Finset.mem_sdiff.mp he).1
    exact hT.isForest.1 e heT
  have hF_forest : F.IsForest := isForest_subgraph hT.isForest hsub hF_valid
  refine ⟨hF_forest, rfl, hR.1, ?_, hsub⟩
  have hinj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, compOf F r₁ = compOf F r₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ hEq
    by_contra hne
    have hconn : F.Connected r₁ r₂ := (compOf_eq_iff (hFV ▸ hR.1 hr₂)).mp hEq
    exact forestGivenRoots_not_connected_roots hT hR hRne π hr₁ hr₂ hne hconn
  have hbij : R.image (compOf F) = components F := by
    apply Finset.eq_of_subset_of_card_le
    · intro K hK
      rw [Finset.mem_image] at hK
      obtain ⟨x, hxR, rfl⟩ := hK
      exact compOf_mem_components (hFV ▸ hR.1 hxR)
    · rw [Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h)]
      rw [forestGivenRoots_components_card hT hR hRne π]
  intro v hv
  have hvF : v ∈ F.V := hFV ▸ hv
  have hKv : compOf F v ∈ R.image (compOf F) := by
    rw [hbij]; exact compOf_mem_components hvF
  rw [Finset.mem_image] at hKv
  obtain ⟨r₀, hr₀R, hcomp⟩ := hKv
  refine ⟨r₀, ⟨hr₀R, ?_⟩, ?_⟩
  · exact connected_symm ((compOf_eq_iff hvF).mp hcomp)
  · intro r' ⟨hr'R, hconn'⟩
    exact hinj r' hr'R r₀ hr₀R
      ((compOf_eq_iff hvF).mpr (connected_symm hconn') |>.trans hcomp.symm)

lemma forestGivenRoots_root_eq_of_connected {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : IsBranchFree T r R) (hRne : R.Nonempty) (π : ℕ → ℕ)
    {v r₀ : ℕ} (hv : v ∈ T.V) (hr₀ : r₀ ∈ R) (hconn : (forestGivenRoots T r R π).Connected v r₀) :
    (rootedForestGivenRoots T r R π).root v = r₀ := by
  have hRS := forestGivenRoots_isRootedSpanningForest hT hR hRne π
  exact rootedForest_root_eq_of_mem hRS hv hr₀ hconn

lemma deletedEdges_mono {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R₁ R₂ : Finset ℕ} (hR₁ : IsBranchFree T r R₁) (hR₂ : IsBranchFree T r R₂)
    (hR₁ne : R₁.Nonempty) (hsub : R₁ ⊆ R₂) (π : ℕ → ℕ) (hord : IsEdgeOrder T π) :
    deletedEdges T r R₁ π ⊆ deletedEdges T r R₂ π := by
  classical
  have hR₂ne : R₂.Nonempty := Finset.Nonempty.mono hsub hR₁ne
  intro e he
  unfold deletedEdges at he ⊢
  rw [ite_eq_left_iff.mpr (fun h => absurd hR₁ne h), Finset.mem_image] at he
  rw [ite_eq_left_iff.mpr (fun h => absurd hR₂ne h), Finset.mem_image]
  obtain ⟨x, hx, rfl⟩ := he
  have hxR₁ := (Finset.mem_erase.mp hx).2
  have hxR₂ := hsub hxR₁
  obtain ⟨hp₁R, hp₁x, hanc_p1x, _⟩ := rootParent_spec hT hR₁ hR₁ne hx
  have hp₁R₂ := hsub hp₁R
  have heT : deletedEdge T r R₁ π x ∈ T.E := deletedEdge_mem_E hT hR₁ hR₁ne hx
  obtain ⟨c, hcV, hcr, hce⟩ : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = deletedEdge T r R₁ π x := by
    rcases edge_parent_orientation hT heT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
    · exact ⟨T.tail _, (hT.isForest.1 _ heT).1, hne, hpe⟩
    · exact ⟨T.head _, (hT.isForest.1 _ heT).2, hne, hpe⟩
  have hxm := deletedEdge_mem_walkEdges (π := π) hT hR₁ hR₁ne hx
  rw [← hce, parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr (hR₁.1 hxR₁) hanc_p1x] at hxm
  let S_sub := R₂.filter (IsAncestor T r c)
  have hxS : x ∈ S_sub := Finset.mem_filter.mpr ⟨hxR₂, hxm.1⟩
  obtain ⟨y, hyS, hymin⟩ := Finset.exists_min_image S_sub (depth T r) ⟨x, hxS⟩
  have hyR₂ : y ∈ R₂ := (Finset.mem_filter.mp hyS).1
  have hcy : IsAncestor T r c y := (Finset.mem_filter.mp hyS).2
  have hp1_anc_c : IsAncestor T r (rootParent T r R₁ x) c := by
    rcases isAncestor_total_on_ancestors hT (hR₁.1 hxR₁) hxm.1 hanc_p1x with hcp | hpc
    · exact absurd hcp hxm.2
    · exact hpc
  have hp1_anc_y : IsAncestor T r (rootParent T r R₁ x) y :=
    isAncestor_trans hT (hR₂.1 hyR₂) hp1_anc_c hcy
  have hp1_ne_y : rootParent T r R₁ x ≠ y := fun hEq => hxm.2 (hEq ▸ hcy)
  have hy_ne_top2 : y ≠ topRoot T r R₂ := by
    intro hEq
    have hanc_yp1 : IsAncestor T r y (rootParent T r R₁ x) := hEq ▸ topRoot_isAncestor hT hR₂ hR₂ne hp₁R₂
    have hEq' := isAncestor_antisymm hT (hR₂.1 hyR₂) (hR₂.1 hp₁R₂) hanc_yp1 hp1_anc_y
    exact hp1_ne_y hEq'.symm
  have hy_erase : y ∈ R₂.erase (topRoot T r R₂) := Finset.mem_erase.mpr ⟨hy_ne_top2, hyR₂⟩
  obtain ⟨hp₂R, _, hanc_p2y, hmax₂⟩ := rootParent_spec hT hR₂ hR₂ne hy_erase
  have hnot_cp2 : ¬ IsAncestor T r c (rootParent T r R₂ y) := by
    intro hcp2
    have hmemS : rootParent T r R₂ y ∈ S_sub := Finset.mem_filter.mpr ⟨hp₂R, hcp2⟩
    have hd_lt : depth T r (rootParent T r R₂ y) < depth T r y := by
      have hp2y_anc := hanc_p2y
      have hp2_ne := (rootParent_spec hT hR₂ hR₂ne hy_erase).2.1
      have hle := isAncestor_depth_le hT (hR₂.1 hyR₂) hp2y_anc
      have hne_d : depth T r (rootParent T r R₂ y) ≠ depth T r y := fun h =>
        hp2_ne ((isAncestor_eq_iff_depth hT (hR₂.1 hyR₂) hp2y_anc).mp h)
      omega
    have := hymin _ hmemS
    omega
  have he_in_2 : deletedEdge T r R₁ π x ∈ walkEdges (T.forestPath y (rootParent T r R₂ y)) := by
    rw [← hce, parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr (hR₂.1 hyR₂) hanc_p2y]
    exact ⟨hcy, hnot_cp2⟩
  have hy_anc_x : IsAncestor T r y x := by
    set l := lca T r y x
    have hlR₂ : l ∈ R₂ := hR₂.2 y hyR₂ x hxR₂
    have hcl : IsAncestor T r c l := (isAncestor_lca_iff hT (hR₂.1 hyR₂) (hR₁.1 hxR₁)).mpr ⟨hcy, hxm.1⟩
    have hlS : l ∈ S_sub := Finset.mem_filter.mpr ⟨hlR₂, hcl⟩
    have hly : IsAncestor T r l y := lca_isAncestor_left hT (hR₂.1 hyR₂) (hR₁.1 hxR₁)
    have hle := isAncestor_depth_le hT (hR₂.1 hyR₂) hly
    have hmin := hymin l hlS
    have hEq : l = y := (isAncestor_eq_iff_depth hT (hR₂.1 hyR₂) hly).mp (Nat.le_antisymm hle hmin)
    exact hEq ▸ lca_isAncestor_right hT (hR₂.1 hyR₂) (hR₁.1 hxR₁)
  have hp1_anc_p2 : IsAncestor T r (rootParent T r R₁ x) (rootParent T r R₂ y) :=
    hmax₂ (rootParent T r R₁ x) hp₁R₂ hp1_ne_y hp1_anc_y
  have hpath_sub : walkEdges (T.forestPath y (rootParent T r R₂ y)) ⊆
      walkEdges (T.forestPath x (rootParent T r R₁ x)) := by
    intro f hf
    have hfT : f ∈ T.E := by
      have hP := forestPath_isPath hT.isForest (hT.connected (hR₂.1 hyR₂) (hR₂.1 hp₂R))
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
      exact IsWalk_edges_mem hP.1 ha
    obtain ⟨d, hdV, hdr, hde⟩ : ∃ d ∈ T.V, d ≠ r ∧ parentEdge T r d = f := by
      rcases edge_parent_orientation hT hfT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
      · exact ⟨T.tail _, (hT.isForest.1 _ hfT).1, hne, hpe⟩
      · exact ⟨T.head _, (hT.isForest.1 _ hfT).2, hne, hpe⟩
    rw [← hde] at hf ⊢
    rw [parentEdge_mem_walkEdges_ancestor_iff hT hdV hdr (hR₂.1 hyR₂) hanc_p2y] at hf
    rw [parentEdge_mem_walkEdges_ancestor_iff hT hdV hdr (hR₁.1 hxR₁) hanc_p1x]
    exact ⟨isAncestor_trans hT (hR₁.1 hxR₁) hf.1 hy_anc_x,
      fun hdp1 => hf.2 (isAncestor_trans hT (hR₂.1 hp₂R) hdp1 hp1_anc_p2)⟩
  have he₂_mem_T := deletedEdge_mem_E (π := π) hT hR₂ hR₂ne hy_erase
  have hle1 : π (deletedEdge T r R₁ π x) ≤ π (deletedEdge T r R₂ π y) :=
    deletedEdge_le (hpath_sub (deletedEdge_mem_walkEdges (π := π) hT hR₂ hR₂ne hy_erase))
  have hle2 : π (deletedEdge T r R₂ π y) ≤ π (deletedEdge T r R₁ π x) :=
    deletedEdge_le he_in_2
  exact ⟨y, hy_erase, (hord _ heT _ he₂_mem_T (Nat.le_antisymm hle1 hle2)).symm⟩

end MinCostFlow.LSF
