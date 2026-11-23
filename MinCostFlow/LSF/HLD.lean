module

public import MinCostFlow.LSF.ForestFromRoots
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Max

/-!
# Heavy-Light Decomposition ([chen2022maximum] Lemma B.8)

This file formalizes Heavy-Light Decomposition on a rooted tree `(T, r)` and proves
**Lemma B.8** (`lemma_B_8`, `[chen2022maximum, Lemma B.8]`):
* A non-root vertex `u ∈ T.V \ {r}` is a *heavy child* (`IsHeavyChild T r u`) if
  `2 * |subtree(u)| > |subtree(parent(u))|`; otherwise `(u, parent(u))` is a *light edge*.
* Each vertex has at most one heavy child, so the heavy chains (`heavyChains T r`, the connected
  components of `heavyGraph T r`) partition `T.V` into vertex-disjoint ancestral paths.
* Every root-to-vertex path `u^{↑ T}` intersects at most `Nat.log 2 |V(T)| + 1` heavy chains.
* We also provide `chainTop`, `chainBot`, and `chainList` (the vertices of a heavy chain sorted
  by increasing `depth T r`) for building the auxiliary tree `T_H` (Lemma B.9).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Heavy children and light ancestor bound -/

/-- `u` is a heavy child in `(T, r)` if `u ∈ T.V`, `u ≠ r`, and
`2 * |subtree(u)| > |subtree(parent(u))|`. -/
noncomputable def IsHeavyChild (T : MGraph) (r u : ℕ) : Prop :=
  u ∈ T.V ∧ u ≠ r ∧ (subtree T r (parent T r u)).card < 2 * (subtree T r u).card

lemma heavy_child_subtree_disjoint {T : MGraph} {r u₁ u₂ : ℕ} (hT : IsRootedTree T r)
    (hu₁ : u₁ ∈ T.V) (hu₂ : u₂ ∈ T.V) (hur₁ : u₁ ≠ r) (hur₂ : u₂ ≠ r)
    (hp : parent T r u₁ = parent T r u₂) (hne : u₁ ≠ u₂) :
    Disjoint (subtree T r u₁) (subtree T r u₂) := by
  rw [Finset.disjoint_left]
  intro w hw₁ hw₂
  rw [mem_subtree_iff] at hw₁ hw₂
  have hdp : depth T r (parent T r u₁) + 1 = depth T r u₁ := depth_parent hT hu₁ hur₁
  have hdp2 : depth T r (parent T r u₂) + 1 = depth T r u₂ := depth_parent hT hu₂ hur₂
  rcases isAncestor_total_on_ancestors hT hw₁.1 hw₁.2 hw₂.2 with h12 | h21
  · have hEq_anc := (isAncestor_iff_eq_or_parent hT hu₂).mp h12
    rcases hEq_anc with hEq | ⟨_, hp12⟩
    · exact hne hEq
    · rw [← hp] at hp12
      have := isAncestor_depth_le hT (parent_mem hT hu₁) hp12
      omega
  · have hEq_anc := (isAncestor_iff_eq_or_parent hT hu₁).mp h21
    rcases hEq_anc with hEq | ⟨_, hp21⟩
    · exact hne hEq.symm
    · rw [hp] at hp21
      have := isAncestor_depth_le hT (parent_mem hT hu₂) hp21
      omega

lemma at_most_one_heavy_child {T : MGraph} {r u₁ u₂ : ℕ} (hT : IsRootedTree T r)
    (hh₁ : IsHeavyChild T r u₁) (hh₂ : IsHeavyChild T r u₂)
    (hp : parent T r u₁ = parent T r u₂) : u₁ = u₂ := by
  by_contra hne
  have hdisj := heavy_child_subtree_disjoint hT hh₁.1 hh₂.1 hh₁.2.1 hh₂.2.1 hp hne
  have hsub₁ : subtree T r u₁ ⊆ subtree T r (parent T r u₁) := by
    intro w hw
    rw [mem_subtree_iff] at hw ⊢
    exact ⟨hw.1, isAncestor_trans hT hw.1 (isAncestor_parent hT hh₁.1 hh₁.2.1) hw.2⟩
  have hsub₂ : subtree T r u₂ ⊆ subtree T r (parent T r u₁) := by
    intro w hw
    rw [mem_subtree_iff] at hw ⊢
    exact ⟨hw.1, hp ▸ isAncestor_trans hT hw.1 (isAncestor_parent hT hh₂.1 hh₂.2.1) hw.2⟩
  have hcard : (subtree T r u₁).card + (subtree T r u₂).card ≤
      (subtree T r (parent T r u₁)).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
  have h1 := hh₁.2.2
  have h2 := hh₂.2.2
  rw [← hp] at h2
  omega

/-- Ancestors `w` of `u` in `(T, r)` whose parent edge `(w, parent w)` is light (`w ≠ r` and
`¬ IsHeavyChild T r w`). -/
noncomputable def lightAncestors (T : MGraph) (r u : ℕ) : Finset ℕ :=
  open Classical in
  (ancestors T r u).filter (fun w => w ≠ r ∧ ¬ IsHeavyChild T r w)

lemma lightAncestors_root (T : MGraph) (r : ℕ) (hT : IsRootedTree T r) :
    lightAncestors T r r = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  rw [lightAncestors, Finset.mem_filter, mem_ancestors_iff] at hw
  have hwr : w = r :=
    isAncestor_antisymm hT (isAncestor_mem hT hT.2 hw.1) hT.2 hw.1 (isAncestor_root hT (isAncestor_mem hT hT.2 hw.1))
  exact hw.2.1 hwr

lemma lightAncestors_pow_mul_subtree_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ {d : ℕ} {u : ℕ}, depth T r u = d → u ∈ T.V →
      2 ^ (lightAncestors T r u).card * (subtree T r u).card ≤ T.V.card := by
  intro d
  classical
  induction d with
  | zero =>
    intro u hd hu
    have hur : u = r := by
      by_contra hne
      obtain ⟨_, hEq, _⟩ := forestPath_parent hT hu hne
      unfold depth at hd; rw [hEq, List.length_cons] at hd; omega
    rw [hur, lightAncestors_root T r hT, Finset.card_empty, pow_zero, one_mul]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  | succ k ih =>
    intro u hd hu
    have hur : u ≠ r := by
      intro hEq
      unfold depth at hd; rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hd; omega
    have hp_mem := parent_mem hT hu
    have hp_d : depth T r (parent T r u) = k := by
      have := depth_parent hT hu hur; omega
    have ihp := ih hp_d hp_mem
    have hsub_anc : ancestors T r u = insert u (ancestors T r (parent T r u)) := by
      apply Finset.ext
      intro w
      rw [Finset.mem_insert, mem_ancestors_iff, mem_ancestors_iff, isAncestor_iff_eq_or_parent hT hu]
      simp [hur]
    have hu_not_p : u ∉ ancestors T r (parent T r u) := by
      intro hm
      rw [mem_ancestors_iff] at hm
      have := isAncestor_depth_le hT hp_mem hm
      omega
    have hsub_st : subtree T r u ⊆ subtree T r (parent T r u) := by
      intro w hw
      rw [mem_subtree_iff] at hw ⊢
      exact ⟨hw.1, isAncestor_trans hT hw.1 (isAncestor_parent hT hu hur) hw.2⟩
    by_cases hh : IsHeavyChild T r u
    · have hEq_la : lightAncestors T r u = lightAncestors T r (parent T r u) := by
        classical
        apply Finset.ext
        intro w
        simp only [lightAncestors, Finset.mem_filter, hsub_anc, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hlight⟩
          · exact absurd hh hlight.2
          · exact ⟨hw, hlight⟩
        · rintro ⟨hw, hlight⟩
          exact ⟨Or.inr hw, hlight⟩
      rw [hEq_la]
      exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub_st)).trans ihp
    · have hEq_la : lightAncestors T r u = insert u (lightAncestors T r (parent T r u)) := by
        classical
        apply Finset.ext
        intro w
        simp only [lightAncestors, Finset.mem_filter, hsub_anc, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hlight⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hw, hlight⟩
        · rintro (rfl | ⟨hw, hlight⟩)
          · exact ⟨Or.inl rfl, ⟨hur, hh⟩⟩
          · exact ⟨Or.inr hw, hlight⟩
      have hu_not_la : u ∉ lightAncestors T r (parent T r u) := by
        intro hm
        rw [lightAncestors, Finset.mem_filter] at hm
        exact hu_not_p hm.1
      rw [hEq_la, Finset.card_insert_of_notMem hu_not_la, pow_succ, mul_assoc]
      have hcard_le : 2 * (subtree T r u).card ≤ (subtree T r (parent T r u)).card := by
        unfold IsHeavyChild at hh
        push Not at hh
        exact hh hu hur
      exact (Nat.mul_le_mul_left _ hcard_le).trans ihp

lemma lightAncestors_card_le {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) :
    (lightAncestors T r u).card ≤ Nat.log 2 T.V.card := by
  have hle := lightAncestors_pow_mul_subtree_le hT rfl hu
  have hst_pos : 1 ≤ (subtree T r u).card :=
    Finset.card_pos.mpr ⟨u, mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩⟩
  have hpow : 2 ^ (lightAncestors T r u).card ≤ T.V.card :=
    (Nat.le_mul_of_pos_right _ hst_pos).trans hle
  exact Nat.le_log_of_pow_le (by decide : 1 < 2) hpow

/-! ## Heavy graph and heavy chains (Lemma B.8) -/

/-- The subgraph of `(T, r)` keeping only the heavy parent edges. -/
noncomputable def heavyGraph (T : MGraph) (r : ℕ) : MGraph :=
  open Classical in
  { V := T.V
    E := (T.V.filter (IsHeavyChild T r)).image (parentEdge T r)
    tail := T.tail
    head := T.head }

/-- The heavy chains `{P_1, ..., P_t}` of `(T, r)`: connected components of `heavyGraph T r`. -/
noncomputable def heavyChains (T : MGraph) (r : ℕ) : Finset (Finset ℕ) :=
  components (heavyGraph T r)

lemma heavyGraph_isSubgraph {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    T.IsSubgraph (heavyGraph T r) := by
  classical
  refine ⟨Finset.Subset.refl _, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  intro e he
  simp only [heavyGraph, Finset.mem_image, Finset.mem_filter] at he
  obtain ⟨u, ⟨huV, hh⟩, rfl⟩ := he
  exact parentEdge_mem hT huV hh.2.1

lemma heavyGraph_isForest {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    (heavyGraph T r).IsForest := by
  classical
  have hvalid : (heavyGraph T r).IsValid := by
    intro e he
    have heT := (heavyGraph_isSubgraph hT).2.1 he
    exact hT.isForest.1 e heT
  exact isForest_subgraph hT.isForest (heavyGraph_isSubgraph hT) hvalid

lemma heavyGraph_connected_parent {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hh : IsHeavyChild T r u) :
    (heavyGraph T r).Connected u (parent T r u) := by
  classical
  have he : parentEdge T r u ∈ (heavyGraph T r).E := by
    simp only [heavyGraph, Finset.mem_image, Finset.mem_filter]
    exact ⟨u, ⟨hh.1, hh⟩, rfl⟩
  have hconn := connected_of_edge he
  have hends := parentEdge_endpoints hT hh.1 hh.2.1
  have hu_mem : (heavyGraph T r).tail (parentEdge T r u) ∈ ({u, parent T r u} : Set ℕ) := by
    rw [← hends]; exact Set.mem_insert _ _
  have hv_mem : (heavyGraph T r).head (parentEdge T r u) ∈ ({u, parent T r u} : Set ℕ) := by
    rw [← hends]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hne : (heavyGraph T r).tail (parentEdge T r u) ≠ (heavyGraph T r).head (parentEdge T r u) :=
    isForest_no_selfLoop (heavyGraph_isForest hT) he
  rcases Set.mem_insert_iff.mp hu_mem with h1 | h1 <;> rcases Set.mem_insert_iff.mp hv_mem with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, (by simpa using h2 : (heavyGraph T r).head (parentEdge T r u) = parent T r u)] at hconn
    exact hconn
  · rw [(by simpa using h1 : (heavyGraph T r).tail (parentEdge T r u) = parent T r u), h2] at hconn
    exact connected_symm hconn
  · exact absurd ((by simpa using h1 : _ = parent T r u).trans (by simpa using h2 : _ = parent T r u).symm) hne

lemma heavyGraph_connected_comparable {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (hconn : (heavyGraph T r).Connected u v) :
    IsAncestor T r u v ∨ IsAncestor T r v u := by
  classical
  have hsub := heavyGraph_isSubgraph hT
  have hPF := forestPath_isPath (heavyGraph_isForest hT) hconn
  have hEq : (heavyGraph T r).forestPath u v = T.forestPath u v :=
    (forestPath_eq_of_isPath hT.isForest (isPath_of_subgraph hsub hPF)).symm
  have hsubE : walkEdges (T.forestPath u v) ⊆ (heavyGraph T r).E := by
    rw [← hEq]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact IsWalk_edges_mem hPF.1 hx
  let z := lca T r u v
  have hzV := lca_mem hT hu hv
  by_contra hnot
  push Not at hnot
  have hzu : z ≠ u := fun hEq => hnot.1 (hEq ▸ lca_isAncestor_right hT hu hv)
  have hzv : z ≠ v := fun hEq => hnot.2 (hEq ▸ lca_isAncestor_left hT hu hv)
  have hwu : walkEdges (T.forestPath u z) ⊆ (heavyGraph T r).E := by
    intro e he
    apply hsubE
    rw [walkEdges_forestPath_lca hT hu hv, Finset.mem_union]
    exact Or.inl he
  have hwv : walkEdges (T.forestPath v z) ⊆ (heavyGraph T r).E := by
    intro e he
    apply hsubE
    rw [walkEdges_forestPath_lca hT hu hv, Finset.mem_union]
    exact Or.inr he
  have exists_child_heavy : ∀ n w, w ∈ T.V → z ≠ w → IsAncestor T r z w →
      depth T r w = depth T r z + 1 + n →
      walkEdges (T.forestPath w z) ⊆ (heavyGraph T r).E →
      ∃ c ∈ T.V, c ≠ r ∧ parent T r c = z ∧ IsHeavyChild T r c ∧ IsAncestor T r c w := by
    intro n
    induction n with
    | zero =>
      intro w hwV hzw hanc hn hwsub
      have hw_nr : w ≠ r := by
        intro hEq
        unfold depth at hn
        rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hn
        omega
      have hz_p : IsAncestor T r z (parent T r w) := by
        rcases (isAncestor_iff_eq_or_parent hT hwV).mp hanc with hEq | ⟨_, hp⟩
        · exact absurd hEq hzw
        · exact hp
      have hp_eq : parent T r w = z := by
        have hdp := depth_parent hT hwV hw_nr
        exact ((isAncestor_eq_iff_depth hT (parent_mem hT hwV) hz_p).mp (by omega)).symm
      have he_in : parentEdge T r w ∈ (heavyGraph T r).E := by
        apply hwsub
        rw [parentEdge_mem_walkEdges_ancestor_iff hT hwV hw_nr hwV hanc]
        refine ⟨isAncestor_refl T r w, fun h => hzw (isAncestor_antisymm hT hzV hwV hanc h)⟩
      simp only [heavyGraph, Finset.mem_image, Finset.mem_filter] at he_in
      obtain ⟨c, ⟨hcV, hhc⟩, hpe_eq⟩ := he_in
      have hc_eq : c = w := parentEdge_inj hT hcV hwV hhc.2.1 hw_nr hpe_eq
      subst hc_eq
      exact ⟨c, hwV, hw_nr, hp_eq, hhc, isAncestor_refl T r c⟩
    | succ k ih =>
      intro w hwV hzw hanc hn hwsub
      have hw_nr : w ≠ r := by
        intro hEq
        unfold depth at hn
        rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hn
        omega
      have hz_p : IsAncestor T r z (parent T r w) := by
        rcases (isAncestor_iff_eq_or_parent hT hwV).mp hanc with hEq | ⟨_, hp⟩
        · exact absurd hEq hzw
        · exact hp
      have hp_mem := parent_mem hT hwV
      have hdp := depth_parent hT hwV hw_nr
      have hne_pz : z ≠ parent T r w := by
        intro hEq
        rw [← hEq] at hdp
        omega
      have hpsub : walkEdges (T.forestPath (parent T r w) z) ⊆ (heavyGraph T r).E := by
        intro e he
        apply hwsub
        obtain ⟨x, hEq, hp, _, hxE, hxs⟩ := forestPath_parent hT hwV hw_nr
        have hsplit_u := (forestPath_eq_of_isAncestor hT hwV hanc).1
        have hsplit_p := (forestPath_eq_of_isAncestor hT hp_mem hz_p).1
        have hp_w : T.forestPath w z = x :: T.forestPath (parent T r w) z := by
          refine (List.append_left_inj (T.forestPath z r)).mp ?_
          rw [← hsplit_u, hEq, List.cons_append, ← hsplit_p]
        rw [hp_w, walkEdges_cons, Finset.mem_insert]
        exact Or.inr he
      obtain ⟨c, hcV, hcr, hpc, hhc, hcp⟩ := ih (parent T r w) hp_mem hne_pz hz_p (by omega) hpsub
      exact ⟨c, hcV, hcr, hpc, hhc, isAncestor_trans hT hwV hcp (isAncestor_parent hT hwV hw_nr)⟩
  have hdu := isAncestor_depth_le hT hu (lca_isAncestor_left hT hu hv)
  have hdv := isAncestor_depth_le hT hv (lca_isAncestor_right hT hu hv)
  have hne_du : depth T r z ≠ depth T r u := fun h => hzu ((isAncestor_eq_iff_depth hT hu (lca_isAncestor_left hT hu hv)).mp h)
  have hne_dv : depth T r z ≠ depth T r v := fun h => hzv ((isAncestor_eq_iff_depth hT hv (lca_isAncestor_right hT hu hv)).mp h)
  have hdu' : depth T r z + 1 ≤ depth T r u := by dsimp only [z] at *; omega
  have hdv' : depth T r z + 1 ≤ depth T r v := by dsimp only [z] at *; omega
  obtain ⟨c₁, hc₁V, hc₁r, hpc₁, hhc₁, hc₁u⟩ :=
    exists_child_heavy (depth T r u - (depth T r z + 1)) u hu hzu (lca_isAncestor_left hT hu hv) (by omega) hwu
  obtain ⟨c₂, hc₂V, hc₂r, hpc₂, hhc₂, hc₂v⟩ :=
    exists_child_heavy (depth T r v - (depth T r z + 1)) v hv hzv (lca_isAncestor_right hT hu hv) (by omega) hwv
  have hc_eq : c₁ = c₂ := at_most_one_heavy_child hT hhc₁ hhc₂ (hpc₁.trans hpc₂.symm)
  subst hc_eq
  have hc_z : IsAncestor T r c₁ z := (isAncestor_lca_iff hT hu hv).mpr ⟨hc₁u, hc₂v⟩
  have hdp := depth_parent hT hc₁V hc₁r
  rw [hpc₁] at hdp
  have hle := isAncestor_depth_le hT hzV hc_z
  dsimp only [z] at hdp hle
  omega

/-! ## Chain endpoints, sorted lists, and Lemma B.8 -/

/-- The top (shallowest) vertex of a heavy chain `P ∈ heavyChains T r`. -/
noncomputable def chainTop (T : MGraph) (r : ℕ) (P : Finset ℕ) : ℕ :=
  open Classical in
  if h : ∃ t ∈ P, ∀ w ∈ P, IsAncestor T r t w then Classical.choose h else r

/-- The bottom (deepest) vertex of a heavy chain `P ∈ heavyChains T r`. -/
noncomputable def chainBot (T : MGraph) (r : ℕ) (P : Finset ℕ) : ℕ :=
  open Classical in
  if h : ∃ b ∈ P, ∀ w ∈ P, IsAncestor T r w b then Classical.choose h else r

lemma heavyChain_subset {T : MGraph} {r : ℕ} {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    P.Nonempty ∧ P ⊆ T.V := by
  rw [heavyChains, components, Finset.mem_image] at hP
  obtain ⟨u, huV, rfl⟩ := hP
  have huV' : u ∈ (heavyGraph T r).V := huV
  refine ⟨⟨u, self_mem_compOf huV'⟩, fun w hw => (mem_compOf_iff.mp hw).1⟩

lemma exists_chainTop_bot {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    (∃ t ∈ P, ∀ w ∈ P, IsAncestor T r t w) ∧ (∃ b ∈ P, ∀ w ∈ P, IsAncestor T r w b) := by
  obtain ⟨hPne, hPsub⟩ := heavyChain_subset hP
  have hcomp_conn : ∀ a ∈ P, ∀ b ∈ P, (heavyGraph T r).Connected a b := by
    rw [heavyChains, components, Finset.mem_image] at hP
    obtain ⟨u, _, rfl⟩ := hP
    intro a ha b hb
    exact connected_trans (connected_symm (mem_compOf_iff.mp ha).2) (mem_compOf_iff.mp hb).2
  constructor
  · obtain ⟨t, htP, htmin⟩ := Finset.exists_min_image P (depth T r) hPne
    refine ⟨t, htP, fun w hwP => ?_⟩
    rcases heavyGraph_connected_comparable hT (hPsub htP) (hPsub hwP) (hcomp_conn t htP w hwP) with h | h
    · exact h
    · have := htmin w hwP
      have hd := isAncestor_depth_le hT (hPsub htP) h
      have hEq := (isAncestor_eq_iff_depth hT (hPsub htP) h).mp (Nat.le_antisymm hd this)
      rw [hEq]
      exact isAncestor_refl T r t
  · obtain ⟨b, hbP, hbmax⟩ := Finset.exists_max_image P (depth T r) hPne
    refine ⟨b, hbP, fun w hwP => ?_⟩
    rcases heavyGraph_connected_comparable hT (hPsub hwP) (hPsub hbP) (hcomp_conn w hwP b hbP) with h | h
    · exact h
    · have := hbmax w hwP
      have hd := isAncestor_depth_le hT (hPsub hwP) h
      have hEq := (isAncestor_eq_iff_depth hT (hPsub hwP) h).mp (Nat.le_antisymm hd this)
      rw [hEq]
      exact isAncestor_refl T r w

lemma chainTop_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    chainTop T r P ∈ P ∧ ∀ w ∈ P, IsAncestor T r (chainTop T r P) w := by
  have hex := (exists_chainTop_bot hT hP).1
  unfold chainTop
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma chainBot_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    chainBot T r P ∈ P ∧ ∀ w ∈ P, IsAncestor T r w (chainBot T r P) := by
  have hex := (exists_chainTop_bot hT hP).2
  unfold chainBot
  classical
  split_ifs
  exact Classical.choose_spec hex

lemma chainTop_not_heavy {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) (htr : chainTop T r P ≠ r) :
    ¬ IsHeavyChild T r (chainTop T r P) := by
  intro hh
  obtain ⟨htP, ht_anc⟩ := chainTop_spec hT hP
  have htV := (heavyChain_subset hP).2 htP
  have hp_conn : (heavyGraph T r).Connected (chainTop T r P) (parent T r (chainTop T r P)) :=
    heavyGraph_connected_parent hT hh
  have hp_mem_P : parent T r (chainTop T r P) ∈ P := by
    rw [heavyChains, components, Finset.mem_image] at hP
    obtain ⟨u, _, rfl⟩ := hP
    rw [mem_compOf_iff] at htP ⊢
    exact ⟨parent_mem hT htV, connected_trans htP.2 hp_conn⟩
  have hanc_tp := ht_anc _ hp_mem_P
  exact absurd (isAncestor_antisymm hT htV (parent_mem hT htV) hanc_tp (isAncestor_parent hT htV htr))
    (parent_ne_self hT htV htr).symm

/-- The vertices of a heavy chain `P` sorted strictly by increasing `depth T r` (starting at
`chainTop T r P`). -/
noncomputable def chainList (T : MGraph) (r : ℕ) (P : Finset ℕ) : List ℕ :=
  (T.walkVertices (chainBot T r P) (T.forestPath (chainBot T r P) (chainTop T r P))).reverse

lemma heavyChain_eq_walkVertices {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    P = (T.walkVertices (chainBot T r P) (T.forestPath (chainBot T r P) (chainTop T r P))).toFinset := by
  obtain ⟨htP, ht_anc⟩ := chainTop_spec hT hP
  obtain ⟨hbP, hb_anc⟩ := chainBot_spec hT hP
  have hsub := (heavyChain_subset hP).2
  apply Finset.ext
  intro w
  rw [List.mem_toFinset, mem_walkVertices_ancestorPath_iff hT (hsub hbP) (ht_anc (chainBot T r P) hbP)]
  constructor
  · intro hwP
    exact ⟨ht_anc w hwP, hb_anc w hwP⟩
  · rintro ⟨htw, hwb⟩
    have hb_top_conn : (heavyGraph T r).Connected (chainBot T r P) (chainTop T r P) := by
      rw [heavyChains, components, Finset.mem_image] at hP
      obtain ⟨u, _, rfl⟩ := hP
      rw [mem_compOf_iff] at htP hbP
      exact connected_trans (connected_symm hbP.2) htP.2
    have hPF := forestPath_isPath (heavyGraph_isForest hT) hb_top_conn
    have hEq : (heavyGraph T r).forestPath (chainBot T r P) (chainTop T r P) =
        T.forestPath (chainBot T r P) (chainTop T r P) :=
      (forestPath_eq_of_isPath hT.isForest (isPath_of_subgraph (heavyGraph_isSubgraph hT) hPF)).symm
    have hw_H : w ∈ (heavyGraph T r).walkVertices (chainBot T r P)
        ((heavyGraph T r).forestPath (chainBot T r P) (chainTop T r P)) := by
      rw [hEq]
      exact (mem_walkVertices_ancestorPath_iff hT (hsub hbP) (ht_anc _ hbP)).mpr ⟨htw, hwb⟩
    obtain ⟨P₁, _, _, hW1, _⟩ := walkVertices_mem_split hPF.1 hw_H
    have h_conn_bw : (heavyGraph T r).Connected (chainBot T r P) w := ⟨P₁, hW1⟩
    rw [heavyChains, components, Finset.mem_image] at hP
    obtain ⟨u, _, rfl⟩ := hP
    exact mem_compOf_iff.mpr ⟨(IsWalk_vertices_mem (heavyGraph_isForest hT).1 (hsub hbP) hPF.1).2 w hw_H,
      connected_trans (mem_compOf_iff.mp hbP).2 h_conn_bw⟩

lemma mem_chainList_iff {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) {w : ℕ} :
    w ∈ chainList T r P ↔ w ∈ P := by
  unfold chainList
  rw [List.mem_reverse, ← List.mem_toFinset, ← heavyChain_eq_walkVertices hT hP]

lemma chainList_nodup {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    (chainList T r P).Nodup := by
  have hsub := (heavyChain_subset hP).2
  have hbV := hsub (chainBot_spec hT hP).1
  have htV := hsub (chainTop_spec hT hP).1
  have hPath := forestPath_isPath hT.isForest (hT.connected hbV htV)
  unfold chainList
  exact List.nodup_reverse.mpr hPath.2

lemma walkVertices_ancestor_reverse_spec {T : MGraph} {r t : ℕ} (hT : IsRootedTree T r) :
    ∀ {d : ℕ} {u : ℕ}, depth T r u = d → u ∈ T.V → IsAncestor T r t u →
      (∀ w ∈ (T.walkVertices u (T.forestPath u t)).reverse,
          depth T r w ≤ depth T r u) ∧
      (∀ i j, i < j → ∀ hi : i < (T.walkVertices u (T.forestPath u t)).reverse.length,
        ∀ hj : j < (T.walkVertices u (T.forestPath u t)).reverse.length,
          depth T r ((T.walkVertices u (T.forestPath u t)).reverse[i]) <
            depth T r ((T.walkVertices u (T.forestPath u t)).reverse[j])) ∧
      (∃ tail, (T.walkVertices u (T.forestPath u t)).reverse = t :: tail) := by
  intro d
  classical
  induction d with
  | zero =>
    intro u hd hu htu
    have hur : u = r := by
      by_contra hne
      obtain ⟨_, hEq, _⟩ := forestPath_parent hT hu hne
      unfold depth at hd; rw [hEq, List.length_cons] at hd; omega
    have htu_u : t = u := by
      rw [hur] at htu ⊢
      exact isAncestor_antisymm hT (isAncestor_mem hT hT.2 htu) hT.2 htu (isAncestor_root hT (isAncestor_mem hT hT.2 htu))
    rw [← htu_u, forestPath_self hT.isForest t]
    refine ⟨?_, ?_, ⟨[], by simp [MGraph.walkVertices, htu_u]⟩⟩
    · simp [MGraph.walkVertices, htu_u]
    · intro i j hij hi hj
      simp [MGraph.walkVertices] at hi hj
      omega
  | succ k ih =>
    intro u hd hu htu
    by_cases hut : u = t
    · rw [← hut, forestPath_self hT.isForest u]
      refine ⟨?_, ?_, ⟨[], by simp [MGraph.walkVertices, hut]⟩⟩
      · simp [MGraph.walkVertices, hut]
      · intro i j hij hi hj
        simp [MGraph.walkVertices] at hi hj
        omega
    · have hur : u ≠ r := by
        intro hEq
        unfold depth at hd; rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hd; omega
      have hp_mem := parent_mem hT hu
      have hdp := depth_parent hT hu hur
      have htp : IsAncestor T r t (parent T r u) := by
        rcases (isAncestor_iff_eq_or_parent hT hu).mp htu with hEq | ⟨_, hp⟩
        · exact absurd hEq.symm hut
        · exact hp
      obtain ⟨ih_le, ih_strict, ⟨tail_p, hhead_p⟩⟩ := ih (by omega) hp_mem htp
      obtain ⟨x, hEq, hp, _⟩ := forestPath_parent hT hu hur
      have hsplit_u := (forestPath_eq_of_isAncestor hT hu htu).1
      have hsplit_p := (forestPath_eq_of_isAncestor hT hp_mem htp).1
      have hEq_path : T.forestPath u t = x :: T.forestPath (parent T r u) t := by
        refine (List.append_left_inj (T.forestPath t r)).mp ?_
        rw [← hsplit_u, hEq, List.cons_append, ← hsplit_p]
      have hrev_eq : (T.walkVertices u (T.forestPath u t)).reverse =
          (T.walkVertices (parent T r u) (T.forestPath (parent T r u) t)).reverse ++ [u] := by
        rw [hEq_path, walkVertices_cons, hp, List.reverse_cons]
      rw [hrev_eq]
      refine ⟨?_, ?_, ⟨tail_p ++ [u], by rw [hhead_p, List.cons_append]⟩⟩
      · intro w hw
        rw [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw_p | rfl
        · exact (ih_le w hw_p).trans (by omega)
        · exact le_rfl
      · intro i j hij hi hj
        let L_p := (T.walkVertices (parent T r u) (T.forestPath (parent T r u) t)).reverse
        rw [List.length_append, List.length_singleton] at hi hj
        by_cases hj_p : j < L_p.length
        · have hi_p : i < L_p.length := lt_trans hij hj_p
          change depth T r ((L_p ++ [u])[i]) < depth T r ((L_p ++ [u])[j])
          rw [List.getElem_append_left hi_p, List.getElem_append_left hj_p]
          exact ih_strict i j hij hi_p hj_p
        · have hj_eq : j = L_p.length := by dsimp only [L_p] at *; omega
          have hi_p : i < L_p.length := by dsimp only [L_p] at *; omega
          have hi_mem : L_p[i] ∈ L_p := List.getElem_mem hi_p
          have hd_i := ih_le _ hi_mem
          have hget_j : (L_p ++ [u])[j] = u := by
            subst hj_eq
            simp [List.getElem_append_right]
          rw [List.getElem_append_left hi_p, hget_j]
          omega

lemma chainList_strictSorted_depth {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    (∀ i j, i < j → ∀ hi : i < (chainList T r P).length, ∀ hj : j < (chainList T r P).length,
        depth T r ((chainList T r P)[i]) < depth T r ((chainList T r P)[j])) ∧
      ∃ tail, chainList T r P = chainTop T r P :: tail := by
  have hsub := (heavyChain_subset hP).2
  have hbP := chainBot_spec hT hP
  have htP := chainTop_spec hT hP
  obtain ⟨_, hstrict, hhead⟩ :=
    walkVertices_ancestor_reverse_spec hT rfl (hsub hbP.1) (htP.2 _ hbP.1)
  exact ⟨hstrict, hhead⟩

/-- **Lemma B.8** (`[chen2022maximum, Lemma B.8]`, Heavy-Light Decomposition):
For any rooted tree `(T, r)`, `heavyChains T r` is a vertex-disjoint partition of `T.V` into paths
such that every vertex has at most one child in its heavy chain, and for every `u ∈ T.V` at most
`Nat.log 2 |V(T)| + 1` heavy chains intersect `ancestors T r u`. -/
lemma lemma_B_8 {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    (∀ u ∈ T.V, ∃! P ∈ heavyChains T r, u ∈ P) ∧
    (∀ P ∈ heavyChains T r, PathConvex T P) ∧
    (∀ P ∈ heavyChains T r, ∀ u ∈ P, ∀ c₁ ∈ P, ∀ c₂ ∈ P,
      c₁ ≠ r → c₂ ≠ r → parent T r c₁ = u → parent T r c₂ = u → c₁ = c₂) ∧
    (∀ u ∈ T.V, ((heavyChains T r).filter (fun P => open Classical in (P ∩ ancestors T r u).Nonempty)).card ≤
      Nat.log 2 T.V.card + 1) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    refine ⟨compOf (heavyGraph T r) u, ⟨compOf_mem_components hu, self_mem_compOf hu⟩, ?_⟩
    intro P ⟨hP, huP⟩
    rw [heavyChains, components, Finset.mem_image] at hP
    obtain ⟨v, _, rfl⟩ := hP
    exact (compOf_eq_iff (G := heavyGraph T r) hu).mpr (mem_compOf_iff.mp huP).2
  · intro P hP
    rw [heavyChain_eq_walkVertices hT hP]
    have hsub := (heavyChain_subset hP).2
    have hbP := chainBot_spec hT hP
    have htP := chainTop_spec hT hP
    have hbV := hsub hbP.1
    have htV := hsub htP.1
    have hP_bt := forestPath_isPath hT.isForest (hT.connected hbV htV)
    refine ⟨⟨chainTop T r P, by rw [← heavyChain_eq_walkVertices hT hP]; exact htP.1⟩, ?_, ?_⟩
    · intro w hw
      rw [List.mem_toFinset] at hw
      exact (IsWalk_vertices_mem hT.isForest.1 hbV hP_bt.1).2 w hw
    · intro a ha b hb w hw
      rw [List.mem_toFinset] at ha hb ⊢
      have haV := (IsWalk_vertices_mem hT.isForest.1 hbV hP_bt.1).2 a ha
      have hbV' := (IsWalk_vertices_mem hT.isForest.1 hbV hP_bt.1).2 b hb
      rw [mem_walkVertices_ancestorPath_iff hT hbV (htP.2 _ hbP.1)] at ha hb
      rw [mem_walkVertices_forestPath_iff hT haV hbV'] at hw
      rw [mem_walkVertices_ancestorPath_iff hT hbV (htP.2 _ hbP.1)]
      have hwb : IsAncestor T r w (chainBot T r P) := by
        rcases hw.2 with hwa | hwb
        · exact isAncestor_trans hT hbV hwa ha.2
        · exact isAncestor_trans hT hbV hwb hb.2
      have hwV := isAncestor_mem hT hbV hwb
      exact ⟨isAncestor_trans hT hwV ((isAncestor_lca_iff hT haV hbV').mpr ⟨ha.1, hb.1⟩) hw.1, hwb⟩
  · intro P hP u _ c₁ hc₁ c₂ hc₂ hcr₁ hcr₂ hp₁ hp₂
    have hsub := (heavyChain_subset hP).2
    have hc₁V := hsub hc₁
    have hc₂V := hsub hc₂
    have hconn : (heavyGraph T r).Connected c₁ c₂ := by
      rw [heavyChains, components, Finset.mem_image] at hP
      obtain ⟨w, _, rfl⟩ := hP
      exact connected_trans (connected_symm (mem_compOf_iff.mp hc₁).2) (mem_compOf_iff.mp hc₂).2
    rcases heavyGraph_connected_comparable hT hc₁V hc₂V hconn with h12 | h21
    · by_contra hne
      rcases (isAncestor_iff_eq_or_parent hT hc₂V).mp h12 with hEq | ⟨_, hp12⟩
      · exact hne hEq
      · rw [hp₂, ← hp₁] at hp12
        have h1 := depth_parent hT hc₁V hcr₁
        have h2 := isAncestor_depth_le hT (parent_mem hT hc₁V) hp12
        omega
    · by_contra hne
      rcases (isAncestor_iff_eq_or_parent hT hc₁V).mp h21 with hEq | ⟨_, hp21⟩
      · exact hne hEq.symm
      · rw [hp₁, ← hp₂] at hp21
        have h1 := depth_parent hT hc₂V hcr₂
        have h2 := isAncestor_depth_le hT (parent_mem hT hc₂V) hp21
        omega
  · intro u hu
    let S := (heavyChains T r).filter (fun P => (P ∩ ancestors T r u).Nonempty)
    have hinj : Set.InjOn (chainTop T r) (S : Set (Finset ℕ)) := by
      intro P₁ hP₁ P₂ hP₂ hEq
      rw [Finset.mem_coe, Finset.mem_filter] at hP₁ hP₂
      have ht1 := (chainTop_spec hT hP₁.1).1
      have ht2 := (chainTop_spec hT hP₂.1).1
      rw [hEq] at ht1
      rw [heavyChains, components, Finset.mem_image] at hP₁ hP₂
      obtain ⟨a, _, rfl⟩ := hP₁.1
      obtain ⟨b, _, rfl⟩ := hP₂.1
      have hm1 := (mem_compOf_iff.mp ht1).2
      have hm2 := (mem_compOf_iff.mp ht2).2
      exact compOf_eq_of_connected (connected_trans hm1 (connected_symm hm2))
    have hsub : S.image (chainTop T r) ⊆ insert r (lightAncestors T r u) := by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨P, hPS, rfl⟩ := ht
      rw [Finset.mem_filter] at hPS
      obtain ⟨w, hw_inter⟩ := hPS.2
      rw [Finset.mem_inter, mem_ancestors_iff] at hw_inter
      have ht_anc_u : IsAncestor T r (chainTop T r P) u :=
        isAncestor_trans hT hu ((chainTop_spec hT hPS.1).2 w hw_inter.1) hw_inter.2
      by_cases htr : chainTop T r P = r
      · rw [htr]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨mem_ancestors_iff.mpr ht_anc_u, htr, ?_⟩)
        exact chainTop_not_heavy hT hPS.1 htr
    have hcard : S.card ≤ (insert r (lightAncestors T r u)).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have hlight := lightAncestors_card_le hT hu
    have hcard_ins : (insert r (lightAncestors T r u)).card ≤ (lightAncestors T r u).card + 1 :=
      Finset.card_insert_le _ _
    dsimp only [S] at hcard
    omega

end MinCostFlow.LSF
