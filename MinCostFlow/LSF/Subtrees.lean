module

public import MinCostFlow.LSF.TreeOps
import Mathlib.Data.Finset.Max

/-!
# Tree medians, LCA closures, induced subtrees, and edge-disjoint partitions

This file builds higher-level tree decomposition primitives on top of `TreeOps.lean`:
* `med`: tree median of three vertices and path membership,
* `lcaClosure`: pairwise LCA closure and the size bound `|lcaClosure S| ≤ 2 |S|`,
* `inducedEdges`, `inducedGraph`, `PathConvex`: induced subtrees of `T`,
* `boundary`, `pieceBoundary`: boundary vertices of a family of vertex sets,
* `splitTreeAtEdge`: splitting a path-convex subtree along an edge into two edge-disjoint
  path-convex subtrees sharing one endpoint.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Tree median -/

/-- The tree median of three vertices `a, b, c` in `(T, r)`: the unique vertex lying on
`T[a, b]`, `T[b, c]`, and `T[c, a]`. -/
noncomputable def med (T : MGraph) (r a b c : ℕ) : ℕ :=
  let x := lca T r a b
  let y := lca T r b c
  let z := lca T r c a
  if depth T r y ≤ depth T r x ∧ depth T r z ≤ depth T r x then x
  else if depth T r z ≤ depth T r y then y
  else z

lemma lca_pair_eq_of_three {T : MGraph} {r a b c : ℕ} (hT : IsRootedTree T r)
    (ha : a ∈ T.V) (hb : b ∈ T.V) (hc : c ∈ T.V) :
    (lca T r a b = lca T r b c ∧ IsAncestor T r (lca T r a b) (lca T r c a)) ∨
    (lca T r b c = lca T r c a ∧ IsAncestor T r (lca T r b c) (lca T r a b)) ∨
    (lca T r c a = lca T r a b ∧ IsAncestor T r (lca T r c a) (lca T r b c)) := by
  set x := lca T r a b
  set y := lca T r b c
  set z := lca T r c a
  have hxV := lca_mem hT ha hb
  have hyV := lca_mem hT hb hc
  have hzV := lca_mem hT hc ha
  have hxb := lca_isAncestor_right hT ha hb
  have hyb := lca_isAncestor_left hT hb hc
  rcases isAncestor_total_on_ancestors hT hb hxb hyb with hxy | hyx
  · have hxz : IsAncestor T r x z :=
      (isAncestor_lca_iff hT hc ha).mpr
        ⟨isAncestor_trans hT hc hxy (lca_isAncestor_right hT hb hc), lca_isAncestor_left hT ha hb⟩
    rcases isAncestor_total_on_ancestors hT hc (lca_isAncestor_right hT hb hc)
        (lca_isAncestor_left hT hc ha) with hyz | hzy
    · left
      have hyx' : IsAncestor T r y x :=
        (isAncestor_lca_iff hT ha hb).mpr
          ⟨isAncestor_trans hT ha hyz (lca_isAncestor_right hT hc ha), hyb⟩
      exact ⟨isAncestor_antisymm hT hxV hyV hxy hyx', hxz⟩
    · right; right
      have hzx : IsAncestor T r z x :=
        (isAncestor_lca_iff hT ha hb).mpr
          ⟨lca_isAncestor_right hT hc ha, isAncestor_trans hT hb hzy hyb⟩
      exact ⟨isAncestor_antisymm hT hzV hxV hzx hxz, hzy⟩
  · have hyz : IsAncestor T r y z :=
      (isAncestor_lca_iff hT hc ha).mpr
        ⟨lca_isAncestor_right hT hb hc, isAncestor_trans hT ha hyx (lca_isAncestor_left hT ha hb)⟩
    rcases isAncestor_total_on_ancestors hT ha (lca_isAncestor_right hT hc ha)
        (lca_isAncestor_left hT ha hb) with hzx | hxz
    · right; left
      have hzy : IsAncestor T r z y :=
        (isAncestor_lca_iff hT hb hc).mpr
          ⟨isAncestor_trans hT hb hzx hxb, lca_isAncestor_left hT hc ha⟩
      have hEqyz : y = z := isAncestor_antisymm hT hyV hzV hyz hzy
      exact ⟨hEqyz, hEqyz ▸ hzx⟩
    · left
      have hxy' : IsAncestor T r x y :=
        (isAncestor_lca_iff hT hb hc).mpr
          ⟨hxb, isAncestor_trans hT hc hxz (lca_isAncestor_left hT hc ha)⟩
      exact ⟨isAncestor_antisymm hT hxV hyV hxy' hyx, hxz⟩

lemma med_mem_forestPath {T : MGraph} {r a b c : ℕ} (hT : IsRootedTree T r)
    (ha : a ∈ T.V) (hb : b ∈ T.V) (hc : c ∈ T.V) :
    med T r a b c ∈ T.V ∧
      med T r a b c ∈ T.walkVertices a (T.forestPath a b) ∧
      med T r a b c ∈ T.walkVertices b (T.forestPath b c) ∧
      med T r a b c ∈ T.walkVertices c (T.forestPath c a) := by
  have hxV := lca_mem hT ha hb
  have hyV := lca_mem hT hb hc
  have hzV := lca_mem hT hc ha
  rcases lca_pair_eq_of_three hT ha hb hc with ⟨hxy, hxz⟩ | ⟨hyz, hyx⟩ | ⟨hzx, hzy⟩
  · have dx_le : depth T r (lca T r a b) ≤ depth T r (lca T r c a) := isAncestor_depth_le hT hzV hxz
    have hm : med T r a b c = lca T r c a := by
      unfold med
      dsimp only
      rw [← hxy]
      by_cases h1 : depth T r (lca T r c a) ≤ depth T r (lca T r a b)
      · rw [ite_eq_left_iff.mpr (fun h => absurd ⟨le_rfl, h1⟩ h)]
        exact (isAncestor_eq_iff_depth hT hzV hxz).mp (Nat.le_antisymm dx_le h1)
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.2 h1),
          ite_eq_right_iff.mpr (fun h => absurd h h1)]
    rw [hm]
    refine ⟨hzV, ?_, ?_, lca_mem_forestPath hT hc ha⟩
    · rw [mem_walkVertices_forestPath_iff hT ha hb]
      exact ⟨hxz, Or.inl (lca_isAncestor_right hT hc ha)⟩
    · rw [mem_walkVertices_forestPath_iff hT hb hc]
      exact ⟨hxy ▸ hxz, Or.inr (lca_isAncestor_left hT hc ha)⟩
  · have dy_le : depth T r (lca T r b c) ≤ depth T r (lca T r a b) := isAncestor_depth_le hT hxV hyx
    have hm : med T r a b c = lca T r a b := by
      unfold med
      dsimp only
      rw [← hyz]
      rw [ite_eq_left_iff.mpr (fun h => absurd ⟨dy_le, dy_le⟩ h)]
    rw [hm]
    refine ⟨hxV, lca_mem_forestPath hT ha hb, ?_, ?_⟩
    · rw [mem_walkVertices_forestPath_iff hT hb hc]
      exact ⟨hyx, Or.inl (lca_isAncestor_right hT ha hb)⟩
    · rw [mem_walkVertices_forestPath_iff hT hc ha]
      exact ⟨hyz ▸ hyx, Or.inr (lca_isAncestor_left hT ha hb)⟩
  · have dz_le : depth T r (lca T r c a) ≤ depth T r (lca T r b c) := isAncestor_depth_le hT hyV hzy
    have hm : med T r a b c = lca T r b c := by
      unfold med
      dsimp only
      rw [← hzx]
      by_cases h1 : depth T r (lca T r b c) ≤ depth T r (lca T r c a)
      · rw [ite_eq_left_iff.mpr (fun h => absurd ⟨h1, le_rfl⟩ h)]
        exact (isAncestor_eq_iff_depth hT hyV hzy).mp (Nat.le_antisymm dz_le h1)
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.1 h1),
          ite_eq_left_iff.mpr (fun h => absurd dz_le h)]
    rw [hm]
    refine ⟨hyV, ?_, lca_mem_forestPath hT hb hc, ?_⟩
    · rw [mem_walkVertices_forestPath_iff hT ha hb]
      exact ⟨hzx ▸ hzy, Or.inr (lca_isAncestor_left hT hb hc)⟩
    · rw [mem_walkVertices_forestPath_iff hT hc ha]
      exact ⟨hzy, Or.inl (lca_isAncestor_right hT hb hc)⟩

/-! ## LCA closure -/

/-- The LCA closure of `S` in `(T, r)`: all pairwise LCAs of vertices in `S`. -/
noncomputable def lcaClosure (T : MGraph) (r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S ×ˢ S).image (fun p => lca T r p.1 p.2)

lemma mem_lcaClosure_iff {T : MGraph} {r : ℕ} {S : Finset ℕ} {z : ℕ} :
    z ∈ lcaClosure T r S ↔ ∃ u ∈ S, ∃ v ∈ S, lca T r u v = z := by
  simp only [lcaClosure, Finset.mem_image, Finset.mem_product, Prod.exists]
  exact ⟨fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ⟨a, ha, b, hb, h⟩,
    fun ⟨a, ha, b, hb, h⟩ => ⟨a, b, ⟨ha, hb⟩, h⟩⟩

lemma subset_lcaClosure {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) : S ⊆ lcaClosure T r S := by
  intro u hu
  rw [mem_lcaClosure_iff]
  exact ⟨u, hu, u, hu, lca_self hT (hS hu)⟩

lemma lcaClosure_subset {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) : lcaClosure T r S ⊆ T.V := by
  intro z hz
  rw [mem_lcaClosure_iff] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := hz
  exact lca_mem hT (hS hu) (hS hv)

lemma lca_mem_lcaClosure {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) {x y : ℕ}
    (hx : x ∈ lcaClosure T r S) (hy : y ∈ lcaClosure T r S) :
    lca T r x y ∈ lcaClosure T r S := by
  rw [mem_lcaClosure_iff] at hx hy ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hy
  have haV := hS ha
  have hbV := hS hb
  have hcV := hS hc
  have hdV := hS hd
  have hxV := lca_mem hT haV hbV
  have hyV := lca_mem hT hcV hdV
  have hwV := lca_mem hT hxV hyV
  have hlacV := lca_mem hT haV hcV
  have hwa : IsAncestor T r (lca T r (lca T r a b) (lca T r c d)) a :=
    isAncestor_trans hT haV (lca_isAncestor_left hT hxV hyV) (lca_isAncestor_left hT haV hbV)
  have hwc : IsAncestor T r (lca T r (lca T r a b) (lca T r c d)) c :=
    isAncestor_trans hT hcV (lca_isAncestor_right hT hxV hyV) (lca_isAncestor_left hT hcV hdV)
  have hw_lac : IsAncestor T r (lca T r (lca T r a b) (lca T r c d)) (lca T r a c) :=
    (isAncestor_lca_iff hT haV hcV).mpr ⟨hwa, hwc⟩
  rcases isAncestor_total_on_ancestors hT haV (lca_isAncestor_left hT haV hbV)
      (lca_isAncestor_left hT haV hcV) with hx_lac | hlac_x
  · have hxc : IsAncestor T r (lca T r a b) c :=
      isAncestor_trans hT hcV hx_lac (lca_isAncestor_right hT haV hcV)
    rcases isAncestor_total_on_ancestors hT hcV hxc (lca_isAncestor_left hT hcV hdV) with hxy | hyx
    · have hEq : lca T r (lca T r a b) (lca T r c d) = lca T r a b :=
        (lca_eq_left_iff hT hxV hyV).mpr hxy
      exact ⟨a, ha, b, hb, hEq.symm⟩
    · have hEq : lca T r (lca T r a b) (lca T r c d) = lca T r c d := by
        rw [lca_comm hT hxV hyV]
        exact (lca_eq_left_iff hT hyV hxV).mpr hyx
      exact ⟨c, hc, d, hd, hEq.symm⟩
  · rcases isAncestor_total_on_ancestors hT hcV (lca_isAncestor_left hT hcV hdV)
        (lca_isAncestor_right hT haV hcV) with hy_lac | hlac_y
    · have hyx : IsAncestor T r (lca T r c d) (lca T r a b) :=
        isAncestor_trans hT hxV hy_lac hlac_x
      have hEq : lca T r (lca T r a b) (lca T r c d) = lca T r c d := by
        rw [lca_comm hT hxV hyV]
        exact (lca_eq_left_iff hT hyV hxV).mpr hyx
      exact ⟨c, hc, d, hd, hEq.symm⟩
    · have hlac_w : IsAncestor T r (lca T r a c) (lca T r (lca T r a b) (lca T r c d)) :=
        (isAncestor_lca_iff hT hxV hyV).mpr ⟨hlac_x, hlac_y⟩
      have hEq : lca T r (lca T r a b) (lca T r c d) = lca T r a c :=
        isAncestor_antisymm hT hwV hlacV hw_lac hlac_w
      exact ⟨a, ha, c, hc, hEq.symm⟩

private lemma lcaClosure_insert_aux {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) {u : ℕ} (hu : u ∈ T.V)
    {s₁ s₂ : ℕ} (hs₁S : s₁ ∈ S) (hs₂S : s₂ ∈ S)
    (hle : depth T r (lca T r u s₁) ≤ depth T r (lca T r u s₂))
    (hne : lca T r u s₁ ≠ lca T r u s₂) :
    lca T r u s₁ ∈ lcaClosure T r S := by
  have hs1V := hS hs₁S
  have hs2V := hS hs₂S
  have hz1V := lca_mem hT hu hs1V
  have hz2V := lca_mem hT hu hs2V
  have h12 : IsAncestor T r (lca T r u s₁) (lca T r u s₂) := by
    rcases isAncestor_total_on_ancestors hT hu (lca_isAncestor_left hT hu hs1V)
        (lca_isAncestor_left hT hu hs2V) with h12 | h21
    · exact h12
    · have hle2 := isAncestor_depth_le hT hz1V h21
      have hEq := (isAncestor_eq_iff_depth hT hz1V h21).mp (Nat.le_antisymm hle2 hle)
      exact absurd hEq.symm hne
  have hlt : depth T r (lca T r u s₁) < depth T r (lca T r u s₂) := by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ((isAncestor_eq_iff_depth hT hz2V h12).mp h) hne
  have hw_ge : IsAncestor T r (lca T r u s₁) (lca T r s₁ s₂) :=
    (isAncestor_lca_iff hT hs1V hs2V).mpr
      ⟨lca_isAncestor_right hT hu hs1V,
       isAncestor_trans hT hs2V h12 (lca_isAncestor_right hT hu hs2V)⟩
  have hw_le : IsAncestor T r (lca T r s₁ s₂) (lca T r u s₁) := by
    rcases isAncestor_total_on_ancestors hT hs2V (lca_isAncestor_right hT hs1V hs2V)
        (lca_isAncestor_right hT hu hs2V) with hw_z | hz_w
    · exact (isAncestor_lca_iff hT hu hs1V).mpr
        ⟨isAncestor_trans hT hu hw_z (lca_isAncestor_left hT hu hs2V),
         lca_isAncestor_left hT hs1V hs2V⟩
    · have hz2_s1 : IsAncestor T r (lca T r u s₂) s₁ :=
        isAncestor_trans hT hs1V hz_w (lca_isAncestor_left hT hs1V hs2V)
      have hz2_z1 : IsAncestor T r (lca T r u s₂) (lca T r u s₁) :=
        (isAncestor_lca_iff hT hu hs1V).mpr ⟨lca_isAncestor_left hT hu hs2V, hz2_s1⟩
      have hle2 := isAncestor_depth_le hT hz1V hz2_z1
      omega
  rw [mem_lcaClosure_iff]
  exact ⟨s₁, hs₁S, s₂, hs₂S,
    (isAncestor_antisymm hT hz1V (lca_mem hT hs1V hs2V) hw_ge hw_le).symm⟩

private lemma lcaClosure_insert_diff_card {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {S : Finset ℕ} (hS : S ⊆ T.V) {u : ℕ} (hu : u ∈ T.V) :
    ((lcaClosure T r (insert u S)) \ lcaClosure T r S).card ≤ if S.Nonempty then 2 else 1 := by
  by_cases hSne : S.Nonempty
  · rw [ite_eq_left_iff.mpr (fun h => absurd hSne h)]
    set A := S.image (fun s => lca T r u s)
    have hAne : A.Nonempty := Finset.Nonempty.image hSne _
    obtain ⟨zmax, hzmaxA, hmax⟩ := Finset.exists_max_image A (depth T r) hAne
    obtain ⟨s₂, hs₂S, rfl⟩ := Finset.mem_image.mp hzmaxA
    have hsub : lcaClosure T r (insert u S) \ lcaClosure T r S ⊆ {u, lca T r u s₂} := by
      intro z hz
      rw [Finset.mem_sdiff, mem_lcaClosure_iff] at hz
      rcases hz with ⟨⟨a, ha, b, hb, rfl⟩, hnot⟩
      rcases Finset.mem_insert.mp ha with rfl | haS <;> rcases Finset.mem_insert.mp hb with rfl | hbS
      · rw [lca_self hT hu]; exact Finset.mem_insert_self _ _
      · by_cases hEq : lca T r a b = lca T r a s₂
        · simp [hEq]
        · exact absurd (lcaClosure_insert_aux hT hS hu hbS hs₂S
            (hmax _ (Finset.mem_image_of_mem _ hbS)) hEq) hnot
      · rw [lca_comm hT (hS haS) hu] at hnot ⊢
        by_cases hEq : lca T r b a = lca T r b s₂
        · simp [hEq]
        · exact absurd (lcaClosure_insert_aux hT hS hu haS hs₂S
            (hmax _ (Finset.mem_image_of_mem _ haS)) hEq) hnot
      · exact absurd (mem_lcaClosure_iff.mpr ⟨a, haS, b, hbS, rfl⟩) hnot
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hSne)]
    rw [Finset.not_nonempty_iff_eq_empty] at hSne
    subst hSne
    simp [lcaClosure, lca_self hT hu]

lemma lcaClosure_card_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ {S : Finset ℕ}, S ⊆ T.V →
      (lcaClosure T r S).card ≤ 2 * S.card ∧
        (S.Nonempty → (lcaClosure T r S).card + 1 ≤ 2 * S.card) := by
  intro S hS
  induction S using Finset.induction_on with
  | empty =>
    simp [lcaClosure]
  | @insert u S' huS' ih =>
    have hS' : S' ⊆ T.V := Finset.Subset.trans (Finset.subset_insert u S') hS
    have huV : u ∈ T.V := hS (Finset.mem_insert_self u S')
    have ih' := ih hS'
    have hdiff := lcaClosure_insert_diff_card hT hS' huV
    have hsub : lcaClosure T r (insert u S') ⊆
        lcaClosure T r S' ∪ (lcaClosure T r (insert u S') \ lcaClosure T r S') := by
      intro z hz
      by_cases hz' : z ∈ lcaClosure T r S'
      · exact Finset.mem_union_left _ hz'
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hz'⟩)
    have hle : (lcaClosure T r (insert u S')).card ≤
        (lcaClosure T r S').card + (lcaClosure T r (insert u S') \ lcaClosure T r S').card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_insert_of_notMem huS']
    by_cases hne : S'.Nonempty
    · rw [ite_eq_left_iff.mpr (fun h => absurd hne h)] at hdiff
      have := ih'.2 hne
      constructor
      · omega
      · intro _; omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at hdiff
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp only [Finset.card_empty] at hle ih'
      have hzero : (lcaClosure T r ∅).card = 0 := by simp [lcaClosure]
      rw [hzero] at hle
      constructor
      · omega
      · intro _; omega

/-! ## Induced subtrees, boundary vertices, and splitting -/

/-- Edges of `T` with both endpoints in `W`. -/
def inducedEdges (T : MGraph) (W : Finset ℕ) : Finset ℕ :=
  T.E.filter (fun e => T.tail e ∈ W ∧ T.head e ∈ W)

/-- The subgraph of `T` induced by `W`. -/
def inducedGraph (T : MGraph) (W : Finset ℕ) : MGraph :=
  { V := W, E := inducedEdges T W, tail := T.tail, head := T.head }

/-- `W` is path-convex in `T` (equivalently, induces a nonempty connected subtree of `T`). -/
def PathConvex (T : MGraph) (W : Finset ℕ) : Prop :=
  W.Nonempty ∧ W ⊆ T.V ∧
    ∀ u ∈ W, ∀ v ∈ W, ∀ w ∈ T.walkVertices u (T.forestPath u v), w ∈ W

lemma inducedGraph_isSubgraph (T : MGraph) {W : Finset ℕ} (hW : W ⊆ T.V) :
    T.IsSubgraph (inducedGraph T W) :=
  ⟨hW, Finset.filter_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩

lemma inducedEdges_isValid (T : MGraph) (W : Finset ℕ) : (inducedGraph T W).IsValid := by
  intro e he
  simp only [inducedGraph, inducedEdges, Finset.mem_filter] at he
  exact he.2

lemma PathConvex.connected {T : MGraph} (hT : T.IsForest) {W : Finset ℕ}
    (hW : PathConvex T W) (hconn : ∀ u ∈ W, ∀ v ∈ W, T.Connected u v)
    {u v : ℕ} (hu : u ∈ W) (hv : v ∈ W) :
    (inducedGraph T W).Connected u v := by
  have hP := forestPath_isPath hT (hconn u hu v hv)
  have hverts : ∀ w ∈ T.walkVertices u (T.forestPath u v), w ∈ W := hW.2.2 u hu v hv
  suffices hwalk : ∀ {s t : ℕ} {Q : List (ℕ × Bool)}, T.IsWalk s t Q →
      (∀ w ∈ T.walkVertices s Q, w ∈ W) → (inducedGraph T W).IsWalk s t Q by
    exact ⟨T.forestPath u v, hwalk hP.1 hverts⟩
  intro s t Q hQ hQw
  induction hQ with
  | nil a => exact .nil a
  | @cons a b x R hx hs hr ih =>
    have haW : a ∈ W := hQw a (List.mem_cons_self)
    have hdW : T.dst x ∈ W :=
      hQw (T.dst x) (by rw [walkVertices_cons]; exact List.mem_cons_of_mem _ (IsWalk_start_mem_walkVertices T _ _))
    have hx_ind : x.1 ∈ inducedEdges T W := by
      simp only [inducedEdges, Finset.mem_filter]
      refine ⟨hx, ?_⟩
      rcases x with ⟨e, b'⟩
      cases b'
      · simp only [MGraph.src, MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hs hdW ⊢
        exact ⟨hdW, by rw [hs]; exact haW⟩
      · simp only [MGraph.src, MGraph.dst, ↓reduceIte] at hs hdW ⊢
        exact ⟨by rw [hs]; exact haW, hdW⟩
    refine .cons hx_ind hs (ih ?_)
    intro w hw
    exact hQw w (by rw [walkVertices_cons]; exact List.mem_cons_of_mem _ hw)

lemma PathConvex.isSpanningTreeOn {T : MGraph} (hT : T.IsForest) {W : Finset ℕ}
    (hW : PathConvex T W) (hconn : ∀ u ∈ W, ∀ v ∈ W, T.Connected u v) :
    (inducedGraph T W).IsSpanningTreeOn W := by
  have hsub := inducedGraph_isSubgraph T hW.2.1
  refine ⟨(isForest_subgraph hT hsub (inducedEdges_isValid T W)), rfl, ?_⟩
  exact fun u hu v hv => hW.connected hT hconn hu hv

lemma PathConvex.inter {T : MGraph} {A B : Finset ℕ}
    (hA : PathConvex T A) (hB : PathConvex T B) (hne : (A ∩ B).Nonempty) :
    PathConvex T (A ∩ B) := by
  refine ⟨hne, Finset.Subset.trans Finset.inter_subset_left hA.2.1, ?_⟩
  intro u hu v hv w hw
  rw [Finset.mem_inter] at hu hv ⊢
  exact ⟨hA.2.2 u hu.1 v hv.1 w hw, hB.2.2 u hu.2 v hv.2 w hw⟩

lemma PathConvex.disjoint_edges_inter_card_le_one {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {A B : Finset ℕ} (hA : PathConvex T A) (hB : PathConvex T B)
    (hdisj : Disjoint (inducedEdges T A) (inducedEdges T B)) :
    (A ∩ B).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  by_contra hne
  rw [Finset.mem_inter] at hu hv
  have hP := forestPath_isPath hT.isForest (hT.connected (hA.2.1 hu.1) (hA.2.1 hv.1))
  rcases hEq : T.forestPath u v with _ | ⟨x, Q⟩
  · rw [hEq] at hP
    cases hP.1
    exact hne rfl
  · have hu_w : T.src x = u := by
      rw [hEq] at hP
      cases hP.1 with | cons _ hs _ => exact hs
    have hxE : x.1 ∈ T.E := by
      rw [hEq] at hP
      cases hP.1 with | cons hx _ _ => exact hx
    have hsW : u ∈ T.walkVertices u (T.forestPath u v) := IsWalk_start_mem_walkVertices T u _
    have htW : T.dst x ∈ T.walkVertices u (T.forestPath u v) := by
      rw [hEq, walkVertices_cons]
      exact List.mem_cons_of_mem _ (IsWalk_start_mem_walkVertices T (T.dst x) Q)
    have hmem_e : ∀ W, PathConvex T W → u ∈ W → v ∈ W → x.1 ∈ inducedEdges T W := by
      intro W hW huW hvW
      have hsu := hW.2.2 u huW v hvW u hsW
      have htu := hW.2.2 u huW v hvW (T.dst x) htW
      rw [← hu_w] at hsu
      simp only [inducedEdges, Finset.mem_filter]
      refine ⟨hxE, ?_⟩
      rcases x with ⟨e, b'⟩
      cases b'
      · simp only [MGraph.src, MGraph.dst] at hsu htu ⊢
        exact ⟨htu, hsu⟩
      · simp only [MGraph.src, MGraph.dst] at hsu htu ⊢
        exact ⟨hsu, htu⟩
    exact Finset.disjoint_left.mp hdisj (hmem_e A hA hu.1 hv.1) (hmem_e B hB hu.2 hv.2)

/-- Boundary vertices of a collection `𝒲` of vertex subsets: vertices belonging to at least two
distinct pieces of `𝒲`. -/
noncomputable def boundary (𝒲 : Finset (Finset ℕ)) : Finset ℕ :=
  open Classical in
  (𝒲.biUnion id).filter (fun v => ∃ W₁ ∈ 𝒲, ∃ W₂ ∈ 𝒲, W₁ ≠ W₂ ∧ v ∈ W₁ ∧ v ∈ W₂)

/-- The boundary vertices `∂W = W ∩ ∂𝒲` of a single piece `W ∈ 𝒲`. -/
noncomputable def pieceBoundary (𝒲 : Finset (Finset ℕ)) (W : Finset ℕ) : Finset ℕ :=
  W ∩ boundary 𝒲

lemma mem_boundary_iff {𝒲 : Finset (Finset ℕ)} {v : ℕ} :
    v ∈ boundary 𝒲 ↔ ∃ W₁ ∈ 𝒲, ∃ W₂ ∈ 𝒲, W₁ ≠ W₂ ∧ v ∈ W₁ ∧ v ∈ W₂ := by
  unfold boundary
  simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨W₁, hW₁, W₂, hW₂, hne, hv1, hv2⟩
    exact ⟨⟨W₁, hW₁, hv1⟩, ⟨W₁, hW₁, W₂, hW₂, hne, hv1, hv2⟩⟩

lemma splitTreeAtEdge {T : MGraph} (hT : T.IsForest) {C : Finset ℕ}
    (hC : PathConvex T C) (hconn : ∀ u ∈ C, ∀ v ∈ C, T.Connected u v)
    {e : ℕ} (he : e ∈ inducedEdges T C) :
    ∃ C₁ C₂ : Finset ℕ, PathConvex T C₁ ∧ PathConvex T C₂ ∧
      (∀ u ∈ C₁, ∀ v ∈ C₁, T.Connected u v) ∧
      (∀ u ∈ C₂, ∀ v ∈ C₂, T.Connected u v) ∧
      C₁ ∪ C₂ = C ∧ C₁ ∩ C₂ = {T.head e} ∧
      inducedEdges T C₁ ∪ inducedEdges T C₂ = inducedEdges T C ∧
      Disjoint (inducedEdges T C₁) (inducedEdges T C₂) ∧
      e ∈ inducedEdges T C₁ := by
  classical
  let H := inducedGraph T C
  have htree := hC.isSpanningTreeOn hT hconn
  have hsubH : T.IsSubgraph H := inducedGraph_isSubgraph T hC.2.1
  have heC : T.tail e ∈ C ∧ T.head e ∈ C := (Finset.mem_filter.mp he).2
  have heT : e ∈ T.E := (Finset.mem_filter.mp he).1
  have heH : e ∈ H.E := he
  have hne_ends : T.tail e ≠ T.head e := isForest_no_selfLoop hT heT
  have hH_rt : IsRootedTree H (T.head e) := ⟨htree, heC.2⟩
  let u := T.tail e
  let r₀ := T.head e
  have hfp_ur : H.forestPath u r₀ = [(e, true)] := by
    have hW : H.IsWalk u r₀ [(e, true)] := by
      refine .cons (x := (e, true)) heH rfl ?_
      exact MGraph.IsWalk.nil r₀
    refine forestPath_eq_of_isPath hH_rt.isForest ⟨hW, ?_⟩
    simp [H, inducedGraph, MGraph.walkVertices, MGraph.dst, hne_ends, u]
  have hpar_u : parent H r₀ u = r₀ := by
    unfold parent; rw [hfp_ur]; simp [H, inducedGraph, MGraph.dst, r₀]
  have hpare_u : parentEdge H r₀ u = e := by
    unfold parentEdge; rw [hfp_ur]
  have hAnc_only : ∀ w, IsAncestor H r₀ w u → w = u ∨ w = r₀ := by
    intro w hw
    unfold IsAncestor at hw
    rw [hfp_ur] at hw
    simp [MGraph.walkVertices, MGraph.dst] at hw
    exact hw
  let A : Finset ℕ := C.filter (IsAncestor H r₀ u)
  let B : Finset ℕ := C.filter (fun w => ¬ IsAncestor H r₀ u w)
  let C₁ : Finset ℕ := insert r₀ A
  let C₂ : Finset ℕ := B
  have hH_fp_eq : ∀ {a b : ℕ}, a ∈ C → b ∈ C → H.forestPath a b = T.forestPath a b := by
    intro a b ha hb
    have hP_H := forestPath_isPath htree.1 (htree.2.2 a ha b hb)
    have hP_T : T.IsPath a b (H.forestPath a b) := isPath_of_subgraph hsubH hP_H
    exact (forestPath_eq_of_isPath hT hP_T).symm
  have huA : u ∈ A := by
    simp only [A, Finset.mem_filter]
    exact ⟨heC.1, isAncestor_refl H r₀ u⟩
  have hr₀_not_A : r₀ ∉ A := by
    simp only [A, Finset.mem_filter]
    intro ⟨_, hanc⟩
    exact hne_ends (isAncestor_antisymm hH_rt heC.1 heC.2 hanc (isAncestor_root hH_rt heC.1))
  have hr₀_B : r₀ ∈ B := by
    simp only [B, Finset.mem_filter]
    exact ⟨heC.2, fun h => hr₀_not_A (Finset.mem_filter.mpr ⟨heC.2, h⟩)⟩
  have hC₁_sub : C₁ ⊆ C := Finset.insert_subset_iff.mpr ⟨heC.2, Finset.filter_subset _ _⟩
  have hC₂_sub : C₂ ⊆ C := Finset.filter_subset _ _
  have hPC₁ : PathConvex T C₁ := by
    refine ⟨⟨u, Finset.mem_insert_of_mem huA⟩, Finset.Subset.trans hC₁_sub hC.2.1, ?_⟩
    intro a ha b hb w hw
    have haC := hC₁_sub ha
    have hbC := hC₁_sub hb
    rw [← hH_fp_eq haC hbC] at hw
    change w ∈ H.walkVertices a (H.forestPath a b) at hw
    have hwC : w ∈ C := by
      have hP := forestPath_isPath htree.1 (htree.2.2 a haC b hbC)
      exact (IsWalk_vertices_mem htree.1.1 haC hP.1).2 w hw
    rw [mem_walkVertices_forestPath_iff hH_rt haC hbC] at hw
    rcases Finset.mem_insert.mp ha with rfl | haA <;> rcases Finset.mem_insert.mp hb with rfl | hbA
    · have : w = r₀ := by
        rcases hw.2 with hwa | hwb
        · exact isAncestor_antisymm hH_rt hwC heC.2 hwa (isAncestor_root hH_rt hwC)
        · exact isAncestor_antisymm hH_rt hwC heC.2 hwb (isAncestor_root hH_rt hwC)
      rw [this]; exact Finset.mem_insert_self _ _
    · have hb_anc : IsAncestor H r₀ u b := (Finset.mem_filter.mp hbA).2
      rcases hw.2 with hwr | hwb
      · have hEq := isAncestor_antisymm hH_rt hwC heC.2 hwr (isAncestor_root hH_rt hwC)
        rw [hEq]; exact Finset.mem_insert_self _ _
      · rcases isAncestor_total_on_ancestors hH_rt hbC hb_anc hwb with huw | hwu
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwC, huw⟩)
        · rcases hAnc_only w hwu with rfl | rfl
          · exact Finset.mem_insert_of_mem huA
          · exact Finset.mem_insert_self _ _
    · have ha_anc : IsAncestor H r₀ u a := (Finset.mem_filter.mp haA).2
      rcases hw.2 with hwa | hwr
      · rcases isAncestor_total_on_ancestors hH_rt haC ha_anc hwa with huw | hwu
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwC, huw⟩)
        · rcases hAnc_only w hwu with rfl | rfl
          · exact Finset.mem_insert_of_mem huA
          · exact Finset.mem_insert_self _ _
      · have hEq := isAncestor_antisymm hH_rt hwC heC.2 hwr (isAncestor_root hH_rt hwC)
        rw [hEq]; exact Finset.mem_insert_self _ _
    · have ha_anc := (Finset.mem_filter.mp haA).2
      have hb_anc := (Finset.mem_filter.mp hbA).2
      have hu_lca : IsAncestor H r₀ u (lca H r₀ a b) :=
        (isAncestor_lca_iff hH_rt haC hbC).mpr ⟨ha_anc, hb_anc⟩
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwC, isAncestor_trans hH_rt hwC hu_lca hw.1⟩)
  have hPC₂ : PathConvex T C₂ := by
    refine ⟨⟨r₀, hr₀_B⟩, Finset.Subset.trans hC₂_sub hC.2.1, ?_⟩
    intro a ha b hb w hw
    have haC := hC₂_sub ha
    have hbC := hC₂_sub hb
    rw [← hH_fp_eq haC hbC] at hw
    change w ∈ H.walkVertices a (H.forestPath a b) at hw
    have hwC : w ∈ C := by
      have hP := forestPath_isPath htree.1 (htree.2.2 a haC b hbC)
      exact (IsWalk_vertices_mem htree.1.1 haC hP.1).2 w hw
    rw [mem_walkVertices_forestPath_iff hH_rt haC hbC] at hw
    refine Finset.mem_filter.mpr ⟨hwC, ?_⟩
    intro huw
    rcases hw.2 with hwa | hwb
    · exact (Finset.mem_filter.mp ha).2 (isAncestor_trans hH_rt haC huw hwa)
    · exact (Finset.mem_filter.mp hb).2 (isAncestor_trans hH_rt hbC huw hwb)
  have hunion : C₁ ∪ C₂ = C := by
    apply Finset.Subset.antisymm (Finset.union_subset hC₁_sub hC₂_sub)
    intro v hv
    by_cases hanc : IsAncestor H r₀ u v
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hv, hanc⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hanc⟩)
  have hinter : C₁ ∩ C₂ = {r₀} := by
    apply Finset.ext
    intro v
    simp only [C₁, C₂, A, B, Finset.mem_inter, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | ⟨_, hanc⟩), ⟨_, hnanc⟩⟩
      · rfl
      · exact absurd hanc hnanc
    · rintro rfl
      exact ⟨Or.inl rfl, ⟨heC.2, fun h => hr₀_not_A (Finset.mem_filter.mpr ⟨heC.2, h⟩)⟩⟩
  have hdisjE : Disjoint (inducedEdges T C₁) (inducedEdges T C₂) := by
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    rw [inducedEdges, Finset.mem_filter] at hf1 hf2
    have hft : T.tail f ∈ C₁ ∩ C₂ := Finset.mem_inter.mpr ⟨hf1.2.1, hf2.2.1⟩
    have hfh : T.head f ∈ C₁ ∩ C₂ := Finset.mem_inter.mpr ⟨hf1.2.2, hf2.2.2⟩
    rw [hinter, Finset.mem_singleton] at hft hfh
    exact isForest_no_selfLoop hT hf1.1 (hft.trans hfh.symm)
  have heC1 : e ∈ inducedEdges T C₁ := by
    simp only [inducedEdges, Finset.mem_filter]
    exact ⟨heT, Finset.mem_insert_of_mem huA, Finset.mem_insert_self _ _⟩
  have hunionE : inducedEdges T C₁ ∪ inducedEdges T C₂ = inducedEdges T C := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset
        (fun f hf => by
          rw [inducedEdges, Finset.mem_filter] at hf ⊢
          exact ⟨hf.1, hC₁_sub hf.2.1, hC₁_sub hf.2.2⟩)
        (fun f hf => by
          rw [inducedEdges, Finset.mem_filter] at hf ⊢
          exact ⟨hf.1, hC₂_sub hf.2.1, hC₂_sub hf.2.2⟩)
    · intro f hf
      by_cases hfe : f = e
      · subst hfe; exact Finset.mem_union_left _ heC1
      · have hfH : f ∈ H.E := hf
        rcases edge_parent_orientation hH_rt hfH with ⟨hp, hpe, htr⟩ | ⟨hp, hpe, hhr⟩
        · dsimp [H, inducedGraph] at hp hpe htr
          have htC := (htree.1.1 f hfH).1
          have hhC := (htree.1.1 f hfH).2
          have htne : T.tail f ≠ u := fun hEq => hfe (hpe.symm.trans (by rw [hEq]; exact hpare_u))
          have h_iff : IsAncestor H r₀ u (T.tail f) ↔ IsAncestor H r₀ u (T.head f) := by
            rw [← hp]
            constructor
            · intro hanc
              have := (isAncestor_iff_eq_or_parent hH_rt htC).mp hanc
              rcases this with hEq | ⟨_, hpanc⟩
              · exact absurd hEq.symm htne
              · exact hpanc
            · intro hanc
              exact isAncestor_trans hH_rt htC hanc (isAncestor_parent hH_rt htC htr)
          by_cases hanc : IsAncestor H r₀ u (T.tail f)
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, ?_, ?_⟩)
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨htC, hanc⟩)
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hhC, h_iff.mp hanc⟩)
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, ?_, ?_⟩)
            · exact Finset.mem_filter.mpr ⟨htC, hanc⟩
            · exact Finset.mem_filter.mpr ⟨hhC, fun h => hanc (h_iff.mpr h)⟩
        · dsimp [H, inducedGraph] at hp hpe hhr
          have htC := (htree.1.1 f hfH).1
          have hhC := (htree.1.1 f hfH).2
          have hhne : T.head f ≠ u := fun hEq => hfe (hpe.symm.trans (by rw [hEq]; exact hpare_u))
          have h_iff : IsAncestor H r₀ u (T.head f) ↔ IsAncestor H r₀ u (T.tail f) := by
            rw [← hp]
            constructor
            · intro hanc
              have := (isAncestor_iff_eq_or_parent hH_rt hhC).mp hanc
              rcases this with hEq | ⟨_, hpanc⟩
              · exact absurd hEq.symm hhne
              · exact hpanc
            · intro hanc
              exact isAncestor_trans hH_rt hhC hanc (isAncestor_parent hH_rt hhC hhr)
          by_cases hanc : IsAncestor H r₀ u (T.head f)
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, ?_, ?_⟩)
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨htC, h_iff.mp hanc⟩)
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hhC, hanc⟩)
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, ?_, ?_⟩)
            · exact Finset.mem_filter.mpr ⟨htC, fun h => hanc (h_iff.mpr h)⟩
            · exact Finset.mem_filter.mpr ⟨hhC, hanc⟩
  exact ⟨C₁, C₂, hPC₁, hPC₂, fun a ha b hb => hconn a (hC₁_sub ha) b (hC₁_sub hb),
    fun a ha b hb => hconn a (hC₂_sub ha) b (hC₂_sub hb), hunion, hinter, hunionE, hdisjE, heC1⟩

end MinCostFlow.LSF
