module

public import MinCostFlow.LSF.Components
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

/-!
# Rooted trees, ancestors, parent edges, LCA, and subtrees

This file defines rooted trees `(T, r)` over `MinCostFlow.MGraph` (`IsRootedTree`) and develops:
* `depth`, `IsAncestor`, `ancestors`, `subtree`, `parent`, and `parentEdge`,
* the bijection between `T.V \ {r}` and `T.E` via `parentEdge`,
* the subtree-edge cut characterization `e ∈ T[u, v] ↔ (c ≤ u ↔ ¬ c ≤ v)`,
* lowest common ancestor `lca` and path splitting `T[u, v] = T[u, lca] ++ T[lca, v]`,
* connectedness in edge-deleted subtrees `T \ D`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-- `(T, r)` is a rooted tree: `T` is a spanning tree on `T.V` and `r ∈ T.V`. -/
def IsRootedTree (T : MGraph) (r : ℕ) : Prop :=
  T.IsSpanningTreeOn T.V ∧ r ∈ T.V

lemma IsRootedTree.isForest {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) : T.IsForest :=
  hT.1.1

lemma IsRootedTree.connected {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V) : T.Connected u v :=
  hT.1.2.2 u hu v hv

lemma IsRootedTree.connected_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {u : ℕ} (hu : u ∈ T.V) : T.Connected u r :=
  hT.connected hu hT.2

/-! ## Depth, ancestors, and subtrees -/

/-- The depth of `u` in the rooted tree `(T, r)`: the number of edges on `T[u, r]`. -/
noncomputable def depth (T : MGraph) (r u : ℕ) : ℕ :=
  (T.forestPath u r).length

/-- `w` is an ancestor of `u` in `(T, r)` if `w` lies on the path `T[u, r]`. -/
noncomputable def IsAncestor (T : MGraph) (r w u : ℕ) : Prop :=
  w ∈ T.walkVertices u (T.forestPath u r)

/-- The set `u^{↑ T}` of ancestors of `u` (including `u`) in `(T, r)`. -/
noncomputable def ancestors (T : MGraph) (r u : ℕ) : Finset ℕ :=
  (T.walkVertices u (T.forestPath u r)).toFinset

/-- The subtree of `(T, r)` rooted at `w`. -/
noncomputable def subtree (T : MGraph) (r w : ℕ) : Finset ℕ :=
  open Classical in T.V.filter (IsAncestor T r w)

lemma mem_ancestors_iff {T : MGraph} {r w u : ℕ} :
    w ∈ ancestors T r u ↔ IsAncestor T r w u := by
  simp [ancestors, IsAncestor]

lemma mem_subtree_iff {T : MGraph} {r w u : ℕ} :
    u ∈ subtree T r w ↔ u ∈ T.V ∧ IsAncestor T r w u := by
  unfold subtree
  simp

lemma isAncestor_refl (T : MGraph) (r u : ℕ) : IsAncestor T r u u :=
  IsWalk_start_mem_walkVertices T u (T.forestPath u r)

lemma isAncestor_root {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) :
    IsAncestor T r r u := by
  unfold IsAncestor
  have hP := forestPath_isPath hT.isForest (hT.connected_root hu)
  exact IsWalk_end_mem_walkVertices hP.1

lemma isAncestor_mem {T : MGraph} {r w u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hw : IsAncestor T r w u) : w ∈ T.V := by
  have hP := forestPath_isPath hT.isForest (hT.connected_root hu)
  exact (IsWalk_vertices_mem hT.isForest.1 hu hP.1).2 w hw

lemma forestPath_eq_of_isAncestor {T : MGraph} {r w u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hw : IsAncestor T r w u) :
    T.forestPath u r = T.forestPath u w ++ T.forestPath w r ∧
      Disjoint (walkEdges (T.forestPath u w)) (walkEdges (T.forestPath w r)) :=
  forestPath_mem_walkVertices_split hT.isForest (hT.connected_root hu) hw

lemma isAncestor_trans {T : MGraph} {r a b c : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ T.V) (hab : IsAncestor T r a b) (hbc : IsAncestor T r b c) :
    IsAncestor T r a c := by
  have hb : b ∈ T.V := isAncestor_mem hT hc hbc
  have hsplit := (forestPath_eq_of_isAncestor hT hc hbc).1
  unfold IsAncestor
  rw [hsplit, walkVertices_append, List.mem_append]
  have ha_map : a ∈ T.walkVertices b (T.forestPath b r) := hab
  rcases List.mem_cons.mp ha_map with rfl | ha_dst
  · exact Or.inl (IsWalk_end_mem_walkVertices (forestPath_isPath hT.isForest (hT.connected hc hb)).1)
  · exact Or.inr ha_dst

lemma isAncestor_depth_le {T : MGraph} {r w u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hw : IsAncestor T r w u) :
    depth T r w ≤ depth T r u := by
  have hsplit := (forestPath_eq_of_isAncestor hT hu hw).1
  unfold depth
  rw [hsplit, List.length_append]
  omega

lemma isAncestor_antisymm {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (huv : IsAncestor T r u v) (hvu : IsAncestor T r v u) :
    u = v := by
  have hsplit := (forestPath_eq_of_isAncestor hT hv huv).1
  have hlen1 := isAncestor_depth_le hT hv huv
  have hlen2 := isAncestor_depth_le hT hu hvu
  have hlen : (T.forestPath v u).length = 0 := by
    have : depth T r v = (T.forestPath v u).length + depth T r u := by
      unfold depth; rw [hsplit, List.length_append]
    omega
  have hnil : T.forestPath v u = [] := List.length_eq_zero_iff.mp hlen
  have hP := forestPath_isPath hT.isForest (hT.connected hv hu)
  rw [hnil] at hP
  cases hP.1
  rfl

lemma isAncestor_eq_iff_depth {T : MGraph} {r w u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hw : IsAncestor T r w u) :
    depth T r w = depth T r u ↔ w = u := by
  refine ⟨fun hEq => ?_, fun hEq => by subst hEq; rfl⟩
  have hsplit := (forestPath_eq_of_isAncestor hT hu hw).1
  have hlen : (T.forestPath u w).length = 0 := by
    have : depth T r u = (T.forestPath u w).length + depth T r w := by
      unfold depth; rw [hsplit, List.length_append]
    omega
  have hnil : T.forestPath u w = [] := List.length_eq_zero_iff.mp hlen
  have hwV := isAncestor_mem hT hu hw
  have hP := forestPath_isPath hT.isForest (hT.connected hu hwV)
  rw [hnil] at hP
  cases hP.1
  rfl

lemma ancestors_card_eq {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) :
    (ancestors T r u).card = depth T r u + 1 := by
  have hP := forestPath_isPath hT.isForest (hT.connected_root hu)
  unfold ancestors depth
  rw [List.toFinset_card_of_nodup hP.2, MGraph.walkVertices, List.length_cons, List.length_map]

lemma isAncestor_total_on_ancestors {T : MGraph} {r u a b : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (ha : IsAncestor T r a u) (hb : IsAncestor T r b u) :
    IsAncestor T r a b ∨ IsAncestor T r b a := by
  have hsplit_a := (forestPath_eq_of_isAncestor hT hu ha).1
  have hP_r := forestPath_isPath hT.isForest (hT.connected_root hu)
  have hb_in : b ∈ T.walkVertices u (T.forestPath u a ++ T.forestPath a r) := by
    rw [← hsplit_a]; exact hb
  rw [walkVertices_append, List.mem_append] at hb_in
  rcases hb_in with hb_ua | hb_ar
  · left
    have haV := isAncestor_mem hT hu ha
    have hbu := forestPath_mem_walkVertices_split hT.isForest (hT.connected hu haV) hb_ua
    have hEqr : T.forestPath u r = T.forestPath u b ++ (T.forestPath b a ++ T.forestPath a r) := by
      rw [hsplit_a, hbu.1, List.append_assoc]
    have hbV := isAncestor_mem hT hu hb
    have hsub : T.forestPath b r = T.forestPath b a ++ T.forestPath a r := by
      have hP1 := forestPath_isPath hT.isForest (hT.connected hu hbV)
      have hW_ba : T.IsWalk b a (T.forestPath b a) :=
        (forestPath_isPath hT.isForest (hT.connected hbV haV)).1
      have hW_ar : T.IsWalk a r (T.forestPath a r) :=
        (forestPath_isPath hT.isForest (hT.connected_root haV)).1
      have hP_br : T.IsPath b r (T.forestPath b a ++ T.forestPath a r) :=
        IsPath_append_right (P := T.forestPath u b) (Q := T.forestPath b a ++ T.forestPath a r)
          (by simpa [hEqr] using hP_r) hP1.1 (IsWalk_append hW_ba hW_ar)
      exact forestPath_eq_of_isPath hT.isForest hP_br
    unfold IsAncestor
    rw [hsub, walkVertices_append, List.mem_append]
    exact Or.inl (IsWalk_end_mem_walkVertices (forestPath_isPath hT.isForest (hT.connected hbV haV)).1)
  · right
    exact List.mem_cons_of_mem a hb_ar

/-! ## Parent and parent edge -/

/-- The parent of `u` in `(T, r)` (`r` if `u = r` or `T[u, r]` is empty). -/
noncomputable def parent (T : MGraph) (r u : ℕ) : ℕ :=
  match T.forestPath u r with
  | [] => u
  | x :: _ => T.dst x

/-- The edge joining `u` to `parent T r u` in `(T, r)` (`0` if `T[u, r]` is empty). -/
noncomputable def parentEdge (T : MGraph) (r u : ℕ) : ℕ :=
  match T.forestPath u r with
  | [] => 0
  | x :: _ => x.1

lemma forestPath_nonempty_of_ne {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) : T.forestPath u r ≠ [] := by
  intro hnil
  have hP := forestPath_isPath hT.isForest (hT.connected_root hu)
  rw [hnil] at hP
  cases hP.1
  exact hne rfl

lemma parent_cons_spec {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) :
    ∃ x P, T.forestPath u r = x :: P ∧ parent T r u = T.dst x ∧ parentEdge T r u = x.1 ∧
      x.1 ∈ T.E ∧ T.src x = u ∧ T.IsPath (parent T r u) r P := by
  have hP := forestPath_isPath hT.isForest (hT.connected_root hu)
  have hneP := forestPath_nonempty_of_ne hT hu hne
  rcases hEq : T.forestPath u r with _ | ⟨x, P⟩
  · exact absurd hEq hneP
  · rw [hEq] at hP
    cases hP.1 with
    | cons hx hs hr =>
      have hp : parent T r u = T.dst x := by simp [parent, hEq]
      have hpe : parentEdge T r u = x.1 := by simp [parentEdge, hEq]
      have hP' : T.IsPath (T.dst x) r P :=
        IsPath_append_right (P := [x]) (Q := P) hP (.cons hx hs (.nil _)) hr
      exact ⟨x, P, rfl, hp, hpe, hx, hs, hp ▸ hP'⟩

lemma parent_mem {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) : parent T r u ∈ T.V := by
  by_cases hur : u = r
  · subst hur
    have hself := forestPath_self hT.isForest u
    simp [parent, hself, hu]
  · obtain ⟨x, _, _, hp, _, hx, _, _⟩ := parent_cons_spec hT hu hur
    rw [hp]
    have hend := hT.isForest.1 x.1 hx
    rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hend.1, hend.2]

lemma parentEdge_mem {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) : parentEdge T r u ∈ T.E := by
  obtain ⟨_, _, _, _, hpe, hx, _, _⟩ := parent_cons_spec hT hu hne
  rwa [hpe]

lemma parent_ne_self {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) : parent T r u ≠ u := by
  obtain ⟨x, _, _, hp, _, hx, hs, _⟩ := parent_cons_spec hT hu hne
  rw [hp, ← hs]
  have hnl := isForest_no_selfLoop hT.isForest hx
  rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.src, MGraph.dst, hnl, Ne.symm hnl]

lemma forestPath_parent {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) :
    ∃ x, T.forestPath u r = x :: T.forestPath (parent T r u) r ∧
      parent T r u = T.dst x ∧ parentEdge T r u = x.1 ∧ x.1 ∈ T.E ∧ T.src x = u := by
  obtain ⟨x, P, hEq, hp, hpe, hx, hs, hP'⟩ := parent_cons_spec hT hu hne
  have hPeq := (forestPath_eq_of_isPath hT.isForest hP').symm
  exact ⟨x, by rw [hEq, hPeq], hp, hpe, hx, hs⟩

lemma depth_parent {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) :
    depth T r (parent T r u) + 1 = depth T r u := by
  obtain ⟨x, hEq, _⟩ := forestPath_parent hT hu hne
  unfold depth
  rw [hEq, List.length_cons]

lemma isAncestor_parent {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) :
    IsAncestor T r (parent T r u) u := by
  obtain ⟨x, hEq, hp, _⟩ := forestPath_parent hT hu hne
  unfold IsAncestor
  rw [hEq, walkVertices_cons, hp]
  exact List.mem_cons_of_mem u (IsWalk_start_mem_walkVertices T _ _)

lemma isAncestor_iff_eq_or_parent {T : MGraph} {r w u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) :
    IsAncestor T r w u ↔ w = u ∨ (u ≠ r ∧ IsAncestor T r w (parent T r u)) := by
  constructor
  · intro hw
    by_cases hwu : w = u
    · exact Or.inl hwu
    · right
      have hur : u ≠ r := by
        intro hEq
        unfold IsAncestor at hw
        rw [hEq, forestPath_self hT.isForest r] at hw
        simp only [MGraph.walkVertices, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
        exact hwu (hw.trans hEq.symm)
      refine ⟨hur, ?_⟩
      obtain ⟨x, hEq, hp, _⟩ := forestPath_parent hT hu hur
      unfold IsAncestor at hw ⊢
      rw [hEq, walkVertices_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact absurd rfl hwu
      · rwa [← hp] at hw
  · rintro (rfl | ⟨hur, hw⟩)
    · exact isAncestor_refl T r w
    · exact isAncestor_trans hT hu hw (isAncestor_parent hT hu hur)

lemma parentEdge_endpoints {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) :
    ({T.tail (parentEdge T r u), T.head (parentEdge T r u)} : Set ℕ) = {u, parent T r u} := by
  obtain ⟨x, _, _, hp, hpe, _, hs, _⟩ := parent_cons_spec hT hu hne
  rw [hp, hpe, ← hs]
  rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.src, MGraph.dst, Set.pair_comm]

lemma edge_parent_orientation {T : MGraph} {r e : ℕ} (hT : IsRootedTree T r) (he : e ∈ T.E) :
    (parent T r (T.tail e) = T.head e ∧ parentEdge T r (T.tail e) = e ∧ T.tail e ≠ r) ∨
    (parent T r (T.head e) = T.tail e ∧ parentEdge T r (T.head e) = e ∧ T.head e ≠ r) := by
  have huv := hT.isForest.1 e he
  have hne := isForest_no_selfLoop hT.isForest he
  have hu_path : T.IsPath (T.tail e) (T.head e) [(e, true)] := by
    refine ⟨.cons he rfl (.nil (T.head e)), ?_⟩
    simp [MGraph.walkVertices, MGraph.dst, hne]
  have hv_path : T.IsPath (T.head e) (T.tail e) [(e, false)] := by
    refine ⟨.cons he rfl (.nil (T.tail e)), ?_⟩
    simp [MGraph.walkVertices, MGraph.dst, Ne.symm hne]
  have hp_vr := forestPath_isPath hT.isForest (hT.connected_root huv.2)
  by_cases hu_on_vr : T.tail e ∈ T.walkVertices (T.head e) (T.forestPath (T.head e) r)
  · right
    have hsplit := (forestPath_eq_of_isAncestor hT huv.2 hu_on_vr).1
    have hvu := forestPath_eq_of_isPath hT.isForest hv_path
    have hEq : T.forestPath (T.head e) r = (e, false) :: T.forestPath (T.tail e) r := by
      rw [hsplit, hvu]; rfl
    have hp : parent T r (T.head e) = T.tail e := by
      unfold parent; rw [hEq]; simp [MGraph.dst]
    have hpe : parentEdge T r (T.head e) = e := by
      unfold parentEdge; rw [hEq]
    have hvr : T.head e ≠ r := by
      intro hrv
      have hEq' := hEq
      rw [hrv, forestPath_self hT.isForest r] at hEq'
      cases hEq'
    exact ⟨hp, hpe, hvr⟩
  · left
    have hP_ur : T.IsPath (T.tail e) r ((e, true) :: T.forestPath (T.head e) r) := by
      refine ⟨.cons he rfl hp_vr.1, ?_⟩
      rw [walkVertices_cons]
      exact List.nodup_cons.mpr ⟨hu_on_vr, hp_vr.2⟩
    have hEq := (forestPath_eq_of_isPath hT.isForest hP_ur).symm
    have hp : parent T r (T.tail e) = T.head e := by
      unfold parent; rw [← hEq]; simp [MGraph.dst]
    have hpe : parentEdge T r (T.tail e) = e := by
      unfold parentEdge; rw [← hEq]
    have hur : T.tail e ≠ r := by
      intro hru
      have hEq' := hEq
      rw [hru, forestPath_self hT.isForest r] at hEq'
      cases hEq'
    exact ⟨hp, hpe, hur⟩

lemma parentEdge_inj {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (hur : u ≠ r) (hvr : v ≠ r)
    (hEq : parentEdge T r u = parentEdge T r v) : u = v := by
  have h1 := parentEdge_endpoints hT hu hur
  have h2 := parentEdge_endpoints hT hv hvr
  rw [hEq] at h1
  have hpair : ({u, parent T r u} : Set ℕ) = {v, parent T r v} := h1.symm.trans h2
  have hu_mem : u ∈ ({v, parent T r v} : Set ℕ) := by rw [← hpair]; exact Set.mem_insert _ _
  have hv_mem : v ∈ ({u, parent T r u} : Set ℕ) := by rw [hpair]; exact Set.mem_insert _ _
  rcases Set.mem_insert_iff.mp hu_mem with rfl | hup
  · rfl
  · rcases Set.mem_insert_iff.mp hv_mem with rfl | hvp
    · rfl
    · have hu_eq : u = parent T r v := by simpa using hup
      have hv_eq : v = parent T r u := by simpa using hvp
      have hd1 := depth_parent hT hv hvr
      have hd2 := depth_parent hT hu hur
      rw [← hu_eq] at hd1
      rw [← hv_eq] at hd2
      omega

lemma parentEdge_bij_image {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    (T.V.erase r).image (parentEdge T r) = T.E := by
  apply Finset.ext
  intro e
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨u, ⟨hur, huV⟩, rfl⟩
    exact parentEdge_mem hT huV hur
  · intro he
    have huv := hT.isForest.1 e he
    rcases edge_parent_orientation hT he with ⟨_, hpe, htr⟩ | ⟨_, hpe, hhr⟩
    · exact ⟨T.tail e, ⟨htr, huv.1⟩, hpe⟩
    · exact ⟨T.head e, ⟨hhr, huv.2⟩, hpe⟩

lemma parentEdge_mem_walkEdges_root_iff {T : MGraph} {r c u : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ T.V) (hcr : c ≠ r) :
    ∀ {d : ℕ}, depth T r u = d → u ∈ T.V →
      (parentEdge T r c ∈ walkEdges (T.forestPath u r) ↔ IsAncestor T r c u) := by
  intro d
  induction d generalizing u with
  | zero =>
    intro hd hu
    have hur : u = r := by
      by_contra hne
      obtain ⟨x, hEq, _⟩ := forestPath_parent hT hu hne
      unfold depth at hd
      rw [hEq, List.length_cons] at hd
      omega
    rw [hur, forestPath_self hT.isForest r]
    simp only [walkEdges, List.map_nil, List.toFinset_nil, Finset.notMem_empty, false_iff]
    intro hca
    exact hcr (isAncestor_antisymm hT hc hT.2 hca (isAncestor_root hT hc))
  | succ k ih =>
    intro hd hu
    have hur : u ≠ r := by
      intro hEq
      unfold depth at hd
      rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hd
      omega
    obtain ⟨x, hEq, _, hpe, _, _⟩ := forestPath_parent hT hu hur
    have hdp : depth T r (parent T r u) = k := by
      have h1 := depth_parent hT hu hur
      omega
    have ihp := ih hdp (parent_mem hT hu)
    rw [hEq, walkEdges_cons, Finset.mem_insert, ← hpe, ihp, isAncestor_iff_eq_or_parent hT hu]
    constructor
    · rintro (hce | hca)
      · exact Or.inl (parentEdge_inj hT hc hu hcr hur hce)
      · exact Or.inr ⟨hur, hca⟩
    · rintro (rfl | ⟨_, hca⟩)
      · exact Or.inl rfl
      · exact Or.inr hca

lemma parentEdge_mem_walkEdges_ancestor_iff {T : MGraph} {r c w u : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ T.V) (hcr : c ≠ r) (hu : u ∈ T.V) (hw : IsAncestor T r w u) :
    parentEdge T r c ∈ walkEdges (T.forestPath u w) ↔
      IsAncestor T r c u ∧ ¬ IsAncestor T r c w := by
  have hwV := isAncestor_mem hT hu hw
  obtain ⟨hsplit, hdisj⟩ := forestPath_eq_of_isAncestor hT hu hw
  have h_ur := parentEdge_mem_walkEdges_root_iff hT hc hcr rfl hu
  have h_wr := parentEdge_mem_walkEdges_root_iff hT hc hcr rfl hwV
  constructor
  · intro he
    have he_ur : parentEdge T r c ∈ walkEdges (T.forestPath u r) := by
      rw [hsplit, walkEdges_append, Finset.mem_union]
      exact Or.inl he
    have he_not_wr : parentEdge T r c ∉ walkEdges (T.forestPath w r) :=
      Finset.disjoint_left.mp hdisj he
    exact ⟨h_ur.mp he_ur, fun hc_w => he_not_wr (h_wr.mpr hc_w)⟩
  · rintro ⟨hcu, hncw⟩
    have he_ur := h_ur.mpr hcu
    rw [hsplit, walkEdges_append, Finset.mem_union] at he_ur
    rcases he_ur with he_uw | he_wr
    · exact he_uw
    · exact absurd (h_wr.mp he_wr) hncw

/-! ## Lowest common ancestor (`lca`) and path edge characterization -/

lemma exists_lca_spec {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    ∃ z ∈ T.V, IsAncestor T r z u ∧ IsAncestor T r z v ∧
      ∀ c, IsAncestor T r c u → IsAncestor T r c v → IsAncestor T r c z := by
  have hne : (ancestors T r u ∩ ancestors T r v).Nonempty :=
    ⟨r, Finset.mem_inter.mpr ⟨mem_ancestors_iff.mpr (isAncestor_root hT hu),
      mem_ancestors_iff.mpr (isAncestor_root hT hv)⟩⟩
  obtain ⟨z, hzS, hzmax⟩ :=
    Finset.exists_max_image (ancestors T r u ∩ ancestors T r v) (depth T r) hne
  have hzu : IsAncestor T r z u := mem_ancestors_iff.mp (Finset.mem_inter.mp hzS).1
  have hzv : IsAncestor T r z v := mem_ancestors_iff.mp (Finset.mem_inter.mp hzS).2
  refine ⟨z, isAncestor_mem hT hu hzu, hzu, hzv, ?_⟩
  intro c hcu hcv
  rcases isAncestor_total_on_ancestors hT hu hcu hzu with hcz | hzc
  · exact hcz
  · have hcS : c ∈ ancestors T r u ∩ ancestors T r v :=
      Finset.mem_inter.mpr ⟨mem_ancestors_iff.mpr hcu, mem_ancestors_iff.mpr hcv⟩
    have hdc_le := hzmax c hcS
    have hcV := isAncestor_mem hT hu hcu
    have hdz_le := isAncestor_depth_le hT hcV hzc
    have hEq := (isAncestor_eq_iff_depth hT hcV hzc).mp (Nat.le_antisymm hdz_le hdc_le)
    rw [hEq]
    exact isAncestor_refl T r c

/-- The lowest common ancestor of `u` and `v` in `(T, r)`. -/
noncomputable def lca (T : MGraph) (r u v : ℕ) : ℕ :=
  open Classical in
  if h : ∃ z ∈ T.V, IsAncestor T r z u ∧ IsAncestor T r z v ∧
      ∀ c, IsAncestor T r c u → IsAncestor T r c v → IsAncestor T r c z
  then Classical.choose h
  else r

lemma lca_spec {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    lca T r u v ∈ T.V ∧ IsAncestor T r (lca T r u v) u ∧ IsAncestor T r (lca T r u v) v ∧
      ∀ c, IsAncestor T r c u → IsAncestor T r c v → IsAncestor T r c (lca T r u v) := by
  have hex := exists_lca_spec hT hu hv
  unfold lca
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma lca_mem {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) : lca T r u v ∈ T.V :=
  (lca_spec hT hu hv).1

lemma lca_isAncestor_left {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) : IsAncestor T r (lca T r u v) u :=
  (lca_spec hT hu hv).2.1

lemma lca_isAncestor_right {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) : IsAncestor T r (lca T r u v) v :=
  (lca_spec hT hu hv).2.2.1

lemma isAncestor_lca_iff {T : MGraph} {r c u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    IsAncestor T r c (lca T r u v) ↔ IsAncestor T r c u ∧ IsAncestor T r c v := by
  obtain ⟨hzV, hzu, hzv, hmax⟩ := lca_spec hT hu hv
  exact ⟨fun hcz => ⟨isAncestor_trans hT hu hcz hzu, isAncestor_trans hT hv hcz hzv⟩,
    fun ⟨hcu, hcv⟩ => hmax c hcu hcv⟩

lemma lca_comm {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) : lca T r u v = lca T r v u := by
  refine isAncestor_antisymm hT (lca_mem hT hu hv) (lca_mem hT hv hu) ?_ ?_
  · rw [isAncestor_lca_iff hT hv hu]
    exact ⟨lca_isAncestor_right hT hu hv, lca_isAncestor_left hT hu hv⟩
  · rw [isAncestor_lca_iff hT hu hv]
    exact ⟨lca_isAncestor_right hT hv hu, lca_isAncestor_left hT hv hu⟩

lemma lca_self {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) :
    lca T r u u = u := by
  refine isAncestor_antisymm hT (lca_mem hT hu hu) hu (lca_isAncestor_left hT hu hu) ?_
  exact (isAncestor_lca_iff hT hu hu).mpr ⟨isAncestor_refl T r u, isAncestor_refl T r u⟩

lemma lca_eq_left_iff {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) : lca T r u v = u ↔ IsAncestor T r u v := by
  constructor
  · intro h
    rw [← h]
    exact lca_isAncestor_right hT hu hv
  · intro huv
    refine isAncestor_antisymm hT (lca_mem hT hu hv) hu (lca_isAncestor_left hT hu hv) ?_
    exact (isAncestor_lca_iff hT hu hv).mpr ⟨isAncestor_refl T r u, huv⟩

lemma lca_assoc {T : MGraph} {r u v w : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (hw : w ∈ T.V) :
    lca T r (lca T r u v) w = lca T r u (lca T r v w) := by
  have huv := lca_mem hT hu hv
  have hvw := lca_mem hT hv hw
  refine isAncestor_antisymm hT (lca_mem hT huv hw) (lca_mem hT hu hvw) ?_ ?_
  · rw [isAncestor_lca_iff hT hu hvw, isAncestor_lca_iff hT hv hw]
    have h1 := lca_isAncestor_left hT huv hw
    rw [isAncestor_lca_iff hT hu hv] at h1
    exact ⟨h1.1, h1.2, lca_isAncestor_right hT huv hw⟩
  · rw [isAncestor_lca_iff hT huv hw, isAncestor_lca_iff hT hu hv]
    have h2 := lca_isAncestor_right hT hu hvw
    rw [isAncestor_lca_iff hT hv hw] at h2
    exact ⟨⟨lca_isAncestor_left hT hu hvw, h2.1⟩, h2.2⟩

lemma disjoint_walkEdges_lca {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    Disjoint (walkEdges (T.forestPath u (lca T r u v)))
      (walkEdges (T.forestPath (lca T r u v) v)) := by
  have hzV := lca_mem hT hu hv
  rw [forestPath_rev hT.isForest (hT.connected hv hzV), walkEdges_walkRev]
  rw [Finset.disjoint_left]
  intro e heu hev
  have heT : e ∈ T.E := by
    have hP := forestPath_isPath hT.isForest (hT.connected hu hzV)
    obtain ⟨a, haP, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp heu)
    exact IsWalk_edges_mem hP.1 haP
  have hpe_src : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = e := by
    rcases edge_parent_orientation hT heT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
    · exact ⟨T.tail e, (hT.isForest.1 e heT).1, hne, hpe⟩
    · exact ⟨T.head e, (hT.isForest.1 e heT).2, hne, hpe⟩
  obtain ⟨c, hcV, hcr, rfl⟩ := hpe_src
  have h1 := (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hu (lca_isAncestor_left hT hu hv)).mp heu
  have h2 := (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hv (lca_isAncestor_right hT hu hv)).mp hev
  have hcz : IsAncestor T r c (lca T r u v) := (isAncestor_lca_iff hT hu hv).mpr ⟨h1.1, h2.1⟩
  exact h1.2 hcz

lemma forestPath_eq_lca {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    T.forestPath u v = T.forestPath u (lca T r u v) ++ T.forestPath (lca T r u v) v := by
  have hzV := lca_mem hT hu hv
  exact forestPath_concat_of_disjoint hT.isForest (hT.connected hu hzV) (hT.connected hzV hv)
    (disjoint_walkEdges_lca hT hu hv)

lemma walkEdges_forestPath_lca {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    walkEdges (T.forestPath u v) =
      walkEdges (T.forestPath u (lca T r u v)) ∪ walkEdges (T.forestPath v (lca T r u v)) := by
  have hzV := lca_mem hT hu hv
  rw [forestPath_eq_lca hT hu hv, walkEdges_append,
    forestPath_rev hT.isForest (hT.connected hv hzV), walkEdges_walkRev]

lemma lca_mem_forestPath {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    lca T r u v ∈ T.walkVertices u (T.forestPath u v) := by
  have hzV := lca_mem hT hu hv
  have hP1 := forestPath_isPath hT.isForest (hT.connected hu hzV)
  rw [forestPath_eq_lca hT hu hv, walkVertices_append, List.mem_append]
  exact Or.inl (IsWalk_end_mem_walkVertices hP1.1)

lemma parentEdge_mem_walkEdges_iff {T : MGraph} {r c u v : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ T.V) (hcr : c ≠ r) (hu : u ∈ T.V) (hv : v ∈ T.V) :
    parentEdge T r c ∈ walkEdges (T.forestPath u v) ↔
      ¬ (IsAncestor T r c u ↔ IsAncestor T r c v) := by
  rw [walkEdges_forestPath_lca hT hu hv, Finset.mem_union]
  rw [parentEdge_mem_walkEdges_ancestor_iff hT hc hcr hu (lca_isAncestor_left hT hu hv)]
  rw [parentEdge_mem_walkEdges_ancestor_iff hT hc hcr hv (lca_isAncestor_right hT hu hv)]
  have hcz := isAncestor_lca_iff hT hu hv (c := c)
  tauto

lemma mem_walkVertices_ancestorPath_iff {T : MGraph} {r w z u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hz : IsAncestor T r z u) :
    w ∈ T.walkVertices u (T.forestPath u z) ↔ IsAncestor T r z w ∧ IsAncestor T r w u := by
  have hzV := isAncestor_mem hT hu hz
  have hPuz := forestPath_isPath hT.isForest (hT.connected hu hzV)
  constructor
  · intro hw
    have hsplit := (forestPath_eq_of_isAncestor hT hu hz).1
    have hwu : IsAncestor T r w u := by
      unfold IsAncestor
      rw [hsplit, walkVertices_append, List.mem_append]
      exact Or.inl hw
    have hwV := isAncestor_mem hT hu hwu
    obtain ⟨hw_split, _⟩ := forestPath_mem_walkVertices_split hT.isForest (hT.connected hu hzV) hw
    have hzw : IsAncestor T r z w := by
      have hP1 := forestPath_isPath hT.isForest (hT.connected hu hwV)
      have hW2 := (forestPath_isPath hT.isForest (hT.connected hwV hzV)).1
      have hW3 := (forestPath_isPath hT.isForest (hT.connected_root hzV)).1
      have hP_ur := forestPath_isPath hT.isForest (hT.connected_root hu)
      have hEq1 : T.forestPath u r = T.forestPath u w ++ (T.forestPath w z ++ T.forestPath z r) := by
        rw [hsplit, hw_split, List.append_assoc]
      have hP_wr : T.IsPath w r (T.forestPath w z ++ T.forestPath z r) :=
        IsPath_append_right (hEq1 ▸ hP_ur) hP1.1 (IsWalk_append hW2 hW3)
      have hwr_eq := (forestPath_eq_of_isPath hT.isForest hP_wr).symm
      unfold IsAncestor
      rw [← hwr_eq, walkVertices_append, List.mem_append]
      exact Or.inl (IsWalk_end_mem_walkVertices hW2)
    exact ⟨hzw, hwu⟩
  · rintro ⟨hzw, hwu⟩
    have hwV := isAncestor_mem hT hu hwu
    have hP_uw := (forestPath_isPath hT.isForest (hT.connected hu hwV)).1
    have hP_wz := (forestPath_isPath hT.isForest (hT.connected hwV hzV)).1
    have hP_ur := forestPath_isPath hT.isForest (hT.connected_root hu)
    have hsplit_u := (forestPath_eq_of_isAncestor hT hu hwu).1
    have hsplit_w := (forestPath_eq_of_isAncestor hT hwV hzw).1
    have hP_uz : T.IsPath u z (T.forestPath u w ++ T.forestPath w z) := by
      have hEq : T.forestPath u r = (T.forestPath u w ++ T.forestPath w z) ++ T.forestPath z r := by
        rw [hsplit_u, hsplit_w, List.append_assoc]
      exact IsPath_append_left (hEq ▸ hP_ur) (IsWalk_append hP_uw hP_wz)
    have huz_eq := (forestPath_eq_of_isPath hT.isForest hP_uz).symm
    rw [← huz_eq, walkVertices_append, List.mem_append]
    exact Or.inl (IsWalk_end_mem_walkVertices hP_uw)

lemma mem_walkVertices_forestPath_iff {T : MGraph} {r w u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    w ∈ T.walkVertices u (T.forestPath u v) ↔
      IsAncestor T r (lca T r u v) w ∧ (IsAncestor T r w u ∨ IsAncestor T r w v) := by
  have hzV := lca_mem hT hu hv
  have hsplit := forestPath_eq_lca hT hu hv
  rw [hsplit, walkVertices_append, List.mem_append]
  have h_rev : T.forestPath (lca T r u v) v = walkRev (T.forestPath v (lca T r u v)) :=
    forestPath_rev hT.isForest (hT.connected hv hzV)
  have h_map_to_rev : ∀ x, x ∈ List.map T.dst (T.forestPath (lca T r u v) v) →
      x ∈ T.walkVertices v (T.forestPath v (lca T r u v)) := by
    intro x hx
    have hx' : x ∈ T.walkVertices (lca T r u v) (T.forestPath (lca T r u v) v) :=
      List.mem_cons_of_mem _ hx
    rw [h_rev, walkVertices_walkRev (forestPath_isPath hT.isForest (hT.connected hv hzV)).1,
      List.mem_reverse] at hx'
    exact hx'
  have h_rev_to_or : w ∈ T.walkVertices v (T.forestPath v (lca T r u v)) →
      w ∈ T.walkVertices u (T.forestPath u (lca T r u v)) ∨
        w ∈ List.map T.dst (T.forestPath (lca T r u v) v) := by
    intro hw
    rw [← List.mem_reverse, ← walkVertices_walkRev (forestPath_isPath hT.isForest (hT.connected hv hzV)).1,
      ← h_rev, MGraph.walkVertices, List.mem_cons] at hw
    rcases hw with rfl | hw'
    · exact Or.inl (IsWalk_end_mem_walkVertices (forestPath_isPath hT.isForest (hT.connected hu hzV)).1)
    · exact Or.inr hw'
  have h_left := mem_walkVertices_ancestorPath_iff hT hu (lca_isAncestor_left hT hu hv) (w := w)
  have h_right := mem_walkVertices_ancestorPath_iff hT hv (lca_isAncestor_right hT hu hv) (w := w)
  constructor
  · rintro (hw1 | hw2)
    · have ⟨h1, h2⟩ := h_left.mp hw1
      exact ⟨h1, Or.inl h2⟩
    · have ⟨h1, h2⟩ := h_right.mp (h_map_to_rev w hw2)
      exact ⟨h1, Or.inr h2⟩
  · rintro ⟨hzw, hwu | hwv⟩
    · exact Or.inl (h_left.mpr ⟨hzw, hwu⟩)
    · exact h_rev_to_or (h_right.mpr ⟨hzw, hwv⟩)

/-! ## Edge deletions from a tree -/

lemma connected_sdiff_iff_disjoint {T : MGraph} (hT : T.IsForest) {D : Finset ℕ}
    {u v : ℕ} (huv : T.Connected u v) :
    ({ T with E := T.E \ D } : MGraph).Connected u v ↔
      Disjoint (walkEdges (T.forestPath u v)) D := by
  let F : MGraph := { T with E := T.E \ D }
  have hsub : T.IsSubgraph F := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  constructor
  · intro hFuv
    obtain ⟨W, hW⟩ := hFuv
    have hWT : T.IsWalk u v W := (isWalk_of_subgraph hsub hW).1
    have hsubW := mem_walkEdges_forestPath_of_isWalk hT hWT
    rw [Finset.disjoint_left]
    intro e he hD
    have heW := hsubW he
    simp only [walkEdges, List.mem_toFinset, List.mem_map] at heW
    obtain ⟨x, hxW, rfl⟩ := heW
    have hxE := IsWalk_edges_mem hW hxW
    exact (Finset.mem_sdiff.mp hxE).2 hD
  · intro hdisj
    have hP := forestPath_isPath hT huv
    have hF_edges : ∀ x ∈ T.forestPath u v, x.1 ∈ F.E := by
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨IsWalk_edges_mem hP.1 hx, ?_⟩
      exact Finset.disjoint_left.mp hdisj (mem_walkEdges_of_mem hx)
    suffices hwalk : ∀ {s t : ℕ} {Q : List (ℕ × Bool)}, T.IsWalk s t Q →
        (∀ x ∈ Q, x.1 ∈ F.E) → F.IsWalk s t Q by
      exact ⟨T.forestPath u v, hwalk hP.1 hF_edges⟩
    intro s t Q hQ hE
    induction hQ with
    | nil a => exact .nil a
    | cons _ hs _ ih =>
      exact .cons (hE _ List.mem_cons_self) hs (ih fun y hy => hE y (List.mem_cons_of_mem _ hy))

lemma connected_sdiff_parentEdge_iff {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {D : Finset ℕ} {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V) :
    ({ T with E := T.E \ D } : MGraph).Connected u v ↔
      ∀ c ∈ T.V, c ≠ r → parentEdge T r c ∈ D →
        (IsAncestor T r c u ↔ IsAncestor T r c v) := by
  rw [connected_sdiff_iff_disjoint hT.isForest (hT.connected hu hv), Finset.disjoint_left]
  constructor
  · intro hdisj c hcV hcr hcD
    have hnot : parentEdge T r c ∉ walkEdges (T.forestPath u v) := fun hm => hdisj hm hcD
    rw [parentEdge_mem_walkEdges_iff hT hcV hcr hu hv] at hnot
    simpa only [not_not] using hnot
  · intro h e he heD
    have heT : e ∈ T.E := by
      have hP := forestPath_isPath hT.isForest (hT.connected hu hv)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
      exact IsWalk_edges_mem hP.1 hx
    rcases edge_parent_orientation hT heT with ⟨_, hpe, hne⟩ | ⟨_, hpe, hne⟩
    · have hcV := (hT.isForest.1 e heT).1
      have h_iff := h (T.tail e) hcV hne (hpe.symm ▸ heD)
      rw [← hpe, parentEdge_mem_walkEdges_iff hT hcV hne hu hv] at he
      exact he h_iff
    · have hcV := (hT.isForest.1 e heT).2
      have h_iff := h (T.head e) hcV hne (hpe.symm ▸ heD)
      rw [← hpe, parentEdge_mem_walkEdges_iff hT hcV hne hu hv] at he
      exact he h_iff

end MinCostFlow.LSF
