module

public import MinCostFlow.LSF.ForestFromRoots
import Mathlib.Data.Finset.Max

/-!
# The roots of `F_T(R, π)` by two passes down the tree

The program finds the root of every vertex in the forest `F_T(R, π)` of Definition B.4 when the
root set `R` is branch-free and holds the root `r` of the tree. It needs, for each `y ∈ R` other
than `r`, the deleted edge of `y`: the `π`-smallest edge on the path from `y` up to the nearest
proper ancestor of `y` in `R`. Both facts follow from rules that look only at a vertex and its
parent, so one pass from the root down computes them.

* `rootParent_step`, `upMin_step`: the nearest proper ancestor in `R` and the `π`-smallest edge up
  to it, from the values at the parent. For `y ∈ R`, `upMin y` is `deletedEdge y`.
* `forestRoot_rule`: if `rt x = x` on `R`, `rt x = y` when the parent edge of `x` is the deleted
  edge of `y`, and `rt x = rt (parent x)` otherwise, then `rt x` is the root of `x` in the forest.
* `forestGivenRoots_stretch`: the stretch of an edge in terms of tree paths and `rt`.
* `walkLength_forestPath_lca`: the length of a tree path from weighted depths.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

variable {T : MGraph} {r : ℕ}

/-! ## The nearest proper ancestor in `R` -/

lemma exists_rootParent_of_mem (hT : IsRootedTree T r) {R : Finset ℕ}
    (hrR : r ∈ R) {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    ∃ p ∈ strictRootAncestors T r R x,
      ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a p := by
  have hSA_ne : (strictRootAncestors T r R x).Nonempty := by
    refine ⟨r, ?_⟩
    simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨Ne.symm hxr, hrR⟩, isAncestor_root hT hx⟩
  obtain ⟨p, hpS, hpmax⟩ :=
    Finset.exists_max_image (strictRootAncestors T r R x) (depth T r) hSA_ne
  refine ⟨p, hpS, fun a haS => ?_⟩
  have hp_anc : IsAncestor T r p x := by
    simp only [strictRootAncestors, Finset.mem_filter] at hpS; exact hpS.2
  have ha_anc : IsAncestor T r a x := by
    simp only [strictRootAncestors, Finset.mem_filter] at haS; exact haS.2
  rcases isAncestor_total_on_ancestors hT hx ha_anc hp_anc with hap | hpa
  · exact hap
  · have haV := isAncestor_mem hT hx ha_anc
    have hd_le := isAncestor_depth_le hT haV hpa
    have hEq : p = a :=
      (isAncestor_eq_iff_depth hT haV hpa).mp (Nat.le_antisymm hd_le (hpmax a haS))
    rw [hEq]
    exact isAncestor_refl T r a

lemma rootParent_eq_of (hT : IsRootedTree T r) {R : Finset ℕ} (hRV : R ⊆ T.V) {x p : ℕ}
    (hp : p ∈ strictRootAncestors T r R x)
    (hmax : ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a p) :
    rootParent T r R x = p := by
  have hex : ∃ p ∈ strictRootAncestors T r R x,
      ∀ a ∈ strictRootAncestors T r R x, IsAncestor T r a p := ⟨p, hp, hmax⟩
  unfold rootParent
  classical
  rw [dif_pos hex]
  obtain ⟨hq, hqmax⟩ := Classical.choose_spec hex
  have hqR : Classical.choose hex ∈ R := (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).2
  have hpR : p ∈ R := (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).2
  exact isAncestor_antisymm hT (hRV hqR) (hRV hpR) (hmax _ hq) (hqmax p hp)

lemma rootParent_spec_of_mem (hT : IsRootedTree T r) {R : Finset ℕ} (hRV : R ⊆ T.V)
    (hrR : r ∈ R) {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    rootParent T r R x ∈ R ∧ rootParent T r R x ≠ x ∧
      IsAncestor T r (rootParent T r R x) x ∧
      ∀ a ∈ R, a ≠ x → IsAncestor T r a x → IsAncestor T r a (rootParent T r R x) := by
  obtain ⟨p, hp, hmax⟩ := exists_rootParent_of_mem hT hrR hx hxr
  rw [rootParent_eq_of hT hRV hp hmax]
  simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase] at hp
  exact ⟨hp.1.2, hp.1.1, hp.2, fun a haR hax hanc => hmax a (by
    simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨hax, haR⟩, hanc⟩)⟩

/-- An ancestor of the root is the root. -/
lemma eq_root_of_isAncestor (hT : IsRootedTree T r) {a : ℕ} (h : IsAncestor T r a r) : a = r := by
  rcases (isAncestor_iff_eq_or_parent hT hT.2).mp h with h | h
  · exact h
  · exact absurd rfl h.1

/-- The nearest proper ancestor in `R` from the one of the parent. -/
lemma rootParent_step (hT : IsRootedTree T r) {R : Finset ℕ} (hRV : R ⊆ T.V) (hrR : r ∈ R)
    {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    rootParent T r R x =
      if parent T r x ∈ R then parent T r x else rootParent T r R (parent T r x) := by
  have hpV := parent_mem hT hx
  have hpx := parent_ne_self hT hx hxr
  have hpanc := isAncestor_parent hT hx hxr
  -- Every proper ancestor of `x` is an ancestor of its parent.
  have hup : ∀ a, a ≠ x → IsAncestor T r a x → IsAncestor T r a (parent T r x) := by
    intro a hax ha
    rcases (isAncestor_iff_eq_or_parent hT hx).mp ha with h | h
    · exact absurd h hax
    · exact h.2
  split_ifs with hpR
  · refine rootParent_eq_of hT hRV ?_ ?_
    · simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hpx, hpR⟩, hpanc⟩
    · intro a ha
      simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase] at ha
      exact hup a ha.1.1 ha.2
  · have hpr : parent T r x ≠ r := fun h => hpR (by rw [h]; exact hrR)
    obtain ⟨hqR, hqp, hqanc, hqmax⟩ := rootParent_spec_of_mem hT hRV hrR hpV hpr
    refine rootParent_eq_of hT hRV ?_ ?_
    · simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨fun hqx => ?_, hqR⟩, isAncestor_trans hT hx hqanc hpanc⟩
      rw [hqx] at hqanc
      exact hpx (isAncestor_antisymm hT hpV hx hpanc hqanc)
    · intro a ha
      simp only [strictRootAncestors, Finset.mem_filter, Finset.mem_erase] at ha
      have hap := hup a ha.1.1 ha.2
      exact hqmax a ha.1.2 (fun h => hpR (h ▸ ha.1.2)) hap

/-! ## Tree paths going up -/

/-- Every edge of `T` is the parent edge of a vertex other than the root. -/
lemma exists_parentEdge_eq (hT : IsRootedTree T r) {e : ℕ} (he : e ∈ T.E) :
    ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = e := by
  rcases edge_parent_orientation hT he with ⟨_, hpe, hcr⟩ | ⟨_, hpe, hcr⟩
  · exact ⟨T.tail e, (hT.isForest.1 e he).1, hcr, hpe⟩
  · exact ⟨T.head e, (hT.isForest.1 e he).2, hcr, hpe⟩

lemma walkEdges_forestPath_subset (hT : IsRootedTree T r) {u v : ℕ} (hu : u ∈ T.V)
    (hv : v ∈ T.V) : walkEdges (T.forestPath u v) ⊆ T.E := by
  intro e he
  have hP := forestPath_isPath hT.isForest (hT.connected hu hv)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  exact IsWalk_edges_mem hP.1 ha

/-- Going up from `u` to a proper ancestor `w`, the first edge is the parent edge of `u`. -/
lemma walkEdges_up_step (hT : IsRootedTree T r) {u w : ℕ} (hu : u ∈ T.V)
    (hw : IsAncestor T r w u) (hne : w ≠ u) :
    u ≠ r ∧ IsAncestor T r w (parent T r u) ∧
      walkEdges (T.forestPath u w) =
        insert (parentEdge T r u) (walkEdges (T.forestPath (parent T r u) w)) ∧
      parentEdge T r u ∉ walkEdges (T.forestPath (parent T r u) w) := by
  have hur : u ≠ r := by
    rintro rfl
    exact hne (eq_root_of_isAncestor hT hw)
  have hpV := parent_mem hT hu
  have hwp : IsAncestor T r w (parent T r u) := by
    rcases (isAncestor_iff_eq_or_parent hT hu).mp hw with h | h
    · exact absurd h hne
    · exact h.2
  have hwV := isAncestor_mem hT hu hw
  -- `u` is not an ancestor of its parent.
  have hnot : ¬ IsAncestor T r u (parent T r u) := fun h =>
    parent_ne_self hT hu hur
      (isAncestor_antisymm hT hpV hu (isAncestor_parent hT hu hur) h)
  have hnotw : ¬ IsAncestor T r u w := fun h => hnot (isAncestor_trans hT hpV h hwp)
  have hmem : parentEdge T r u ∉ walkEdges (T.forestPath (parent T r u) w) := by
    rw [parentEdge_mem_walkEdges_ancestor_iff hT hu hur hpV hwp]
    exact fun h => hnot h.1
  refine ⟨hur, hwp, ?_, hmem⟩
  ext e
  constructor
  · intro he
    obtain ⟨c, hcV, hcr, rfl⟩ := exists_parentEdge_eq hT (walkEdges_forestPath_subset hT hu hwV he)
    rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hu hw] at he
    rw [Finset.mem_insert, parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hpV hwp]
    rcases (isAncestor_iff_eq_or_parent hT hu).mp he.1 with h | h
    · exact Or.inl (h ▸ rfl)
    · exact Or.inr ⟨h.2, he.2⟩
  · intro he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he, parentEdge_mem_walkEdges_ancestor_iff hT hu hur hu hw]
      exact ⟨isAncestor_refl T r u, hnotw⟩
    · obtain ⟨c, hcV, hcr, rfl⟩ :=
        exists_parentEdge_eq hT (walkEdges_forestPath_subset hT hpV hwV he)
      rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hpV hwp] at he
      rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hu hw]
      exact ⟨isAncestor_trans hT hu he.1 (isAncestor_parent hT hu hur), he.2⟩

/-! ## The smallest edge of a set -/

lemma minEdgeOn_eq_of {π : ℕ → ℕ} {S : Finset ℕ} {m : ℕ} (hm : m ∈ S)
    (hmin : ∀ f ∈ S, π m ≤ π f) (hinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b) :
    minEdgeOn π S = m := by
  obtain ⟨h1, h2⟩ := minEdgeOn_spec (π := π) ⟨m, hm⟩
  exact hinj _ h1 _ hm (Nat.le_antisymm (h2 m hm) (hmin _ h1))

lemma minEdgeOn_singleton (π : ℕ → ℕ) (e : ℕ) : minEdgeOn π {e} = e :=
  minEdgeOn_eq_of (Finset.mem_singleton_self e) (fun f hf => by rw [Finset.mem_singleton.mp hf])
    (fun a ha b hb _ => by rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb])

lemma minEdgeOn_insert {π : ℕ → ℕ} {S : Finset ℕ} {e : ℕ} (hS : S.Nonempty)
    (hinj : ∀ a ∈ insert e S, ∀ b ∈ insert e S, π a = π b → a = b) :
    minEdgeOn π (insert e S) =
      if π e < π (minEdgeOn π S) then e else minEdgeOn π S := by
  obtain ⟨h1, h2⟩ := minEdgeOn_spec (π := π) hS
  split_ifs with hlt
  · refine minEdgeOn_eq_of (Finset.mem_insert_self e S) (fun f hf => ?_) hinj
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact le_refl _
    · exact (le_of_lt hlt).trans (h2 f hf)
  · refine minEdgeOn_eq_of (Finset.mem_insert_of_mem h1) (fun f hf => ?_) hinj
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact Nat.le_of_not_lt hlt
    · exact h2 f hf

/-! ## The smallest edge up to the nearest proper ancestor in `R` -/

/-- The `π`-smallest edge on the path from `x` up to its nearest proper ancestor in `R`. -/
noncomputable def upMin (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) (x : ℕ) : ℕ :=
  minEdgeOn π (walkEdges (T.forestPath x (rootParent T r R x)))

lemma deletedEdge_eq_upMin (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) (x : ℕ) :
    deletedEdge T r R π x = upMin T r R π x := rfl

lemma upMin_step (hT : IsRootedTree T r) {R : Finset ℕ} (hRV : R ⊆ T.V) (hrR : r ∈ R)
    {π : ℕ → ℕ} (hπ : IsEdgeOrder T π) {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    upMin T r R π x =
      if parent T r x ∈ R then parentEdge T r x
      else if π (parentEdge T r x) < π (upMin T r R π (parent T r x)) then parentEdge T r x
      else upMin T r R π (parent T r x) := by
  have hpV := parent_mem hT hx
  have hstep := rootParent_step hT hRV hrR hx hxr
  obtain ⟨hqR, hqx, hqanc, -⟩ := rootParent_spec_of_mem hT hRV hrR hx hxr
  obtain ⟨-, hqp, hset, -⟩ := walkEdges_up_step hT hx hqanc hqx
  have hinj : ∀ a ∈ walkEdges (T.forestPath x (rootParent T r R x)),
      ∀ b ∈ walkEdges (T.forestPath x (rootParent T r R x)), π a = π b → a = b :=
    fun a ha b hb hab => hπ a (walkEdges_forestPath_subset hT hx (hRV hqR) ha) b
      (walkEdges_forestPath_subset hT hx (hRV hqR) hb) hab
  unfold upMin
  rw [hset] at hinj ⊢
  by_cases hpR : parent T r x ∈ R
  · rw [if_pos hpR, hstep, if_pos hpR, forestPath_self hT.isForest]
    exact minEdgeOn_singleton π _
  · rw [if_neg hpR]
    rw [hstep, if_neg hpR] at hinj hqp ⊢
    have hpr : parent T r x ≠ r := fun h => hpR (by rw [h]; exact hrR)
    have hq'R := (rootParent_spec_of_mem hT hRV hrR hpV hpr).1
    have hne : rootParent T r R (parent T r x) ≠ parent T r x :=
      fun h => hpR (by rw [← h]; exact hq'R)
    obtain ⟨-, -, hset2, -⟩ := walkEdges_up_step hT hpV hqp hne
    rw [minEdgeOn_insert ⟨_, hset2 ▸ Finset.mem_insert_self _ _⟩ hinj]

/-! ## Roots of the forest -/

lemma topRoot_eq_of_mem (hT : IsRootedTree T r) {R : Finset ℕ} (hR : IsBranchFree T r R)
    (hrR : r ∈ R) : topRoot T r R = r :=
  eq_root_of_isAncestor hT (topRoot_isAncestor hT hR ⟨r, hrR⟩ hrR)

lemma mem_deletedEdges_iff (hT : IsRootedTree T r) {R : Finset ℕ} (hR : IsBranchFree T r R)
    (hrR : r ∈ R) (π : ℕ → ℕ) {e : ℕ} :
    e ∈ deletedEdges T r R π ↔ ∃ y ∈ R.erase r, deletedEdge T r R π y = e := by
  unfold deletedEdges
  rw [if_pos ⟨r, hrR⟩, topRoot_eq_of_mem hT hR hrR, Finset.mem_image]

lemma forestGivenRoots_eq (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) :
    forestGivenRoots T r R π = { T with E := T.E \ deletedEdges T r R π } := rfl

/-- The deleted edge of `y` lies on the path from `y` up to its nearest proper ancestor in `R`. -/
lemma deletedEdge_mem (hT : IsRootedTree T r) {R : Finset ℕ} (hR : IsBranchFree T r R)
    (hrR : r ∈ R) (π : ℕ → ℕ) {y : ℕ} (hy : y ∈ R.erase r) :
    deletedEdge T r R π y ∈ walkEdges (T.forestPath y (rootParent T r R y)) := by
  have hy' : y ∈ R.erase (topRoot T r R) := by rwa [topRoot_eq_of_mem hT hR hrR]
  exact (minEdgeOn_spec (walkEdges_rootParent_nonempty hT hR ⟨r, hrR⟩ hy')).1

/-- The rules of the roots pass give the root of every vertex in `F_T(R, π)`. -/
theorem forestRoot_rule (hT : IsRootedTree T r) {R : Finset ℕ} (hR : IsBranchFree T r R)
    (hrR : r ∈ R) (π : ℕ → ℕ) (rt : ℕ → ℕ)
    (h1 : ∀ x ∈ T.V, x ∈ R → rt x = x)
    (h2 : ∀ x ∈ T.V, x ∉ R → ∀ y ∈ R.erase r,
      parentEdge T r x = deletedEdge T r R π y → rt x = y)
    (h3 : ∀ x ∈ T.V, x ∉ R → (∀ y ∈ R.erase r, parentEdge T r x ≠ deletedEdge T r R π y) →
      rt x = rt (parent T r x)) :
    ∀ x ∈ T.V, rt x ∈ R ∧ (forestGivenRoots T r R π).Connected x (rt x) := by
  have hRV := hR.1
  have hRne : R.Nonempty := ⟨r, hrR⟩
  suffices H : ∀ d, ∀ x ∈ T.V, depth T r x = d →
      rt x ∈ R ∧ (forestGivenRoots T r R π).Connected x (rt x) from
    fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd
  by_cases hxR : x ∈ R
  · rw [h1 x hx hxR]
    exact ⟨hxR, connected_refl _ x⟩
  have hxr : x ≠ r := fun h => hxR (h ▸ hrR)
  have hpV := parent_mem hT hx
  by_cases hex : ∃ y ∈ R.erase r, parentEdge T r x = deletedEdge T r R π y
  · obtain ⟨y, hy, hxy⟩ := hex
    rw [h2 x hx hxR y hy hxy]
    have hyR := (Finset.mem_erase.mp hy).2
    have hyr := (Finset.mem_erase.mp hy).1
    have hyV := hRV hyR
    refine ⟨hyR, ?_⟩
    obtain ⟨hqR, -, hqanc, -⟩ := rootParent_spec hT hR hRne
      (by rwa [topRoot_eq_of_mem hT hR hrR])
    have hqV := hRV hqR
    -- The parent edge of `x` is on the path from `y` up to `q`, so `x` lies between them.
    have hpe := deletedEdge_mem hT hR hrR π hy
    rw [← hxy, parentEdge_mem_walkEdges_ancestor_iff hT hx hxr hyV hqanc] at hpe
    have hqx : IsAncestor T r (rootParent T r R y) x := by
      rcases isAncestor_total_on_ancestors hT hyV hpe.1 hqanc with h | h
      · exact absurd h hpe.2
      · exact h
    rw [forestGivenRoots_eq, connected_sdiff_parentEdge_iff hT hx hyV]
    intro c hcV hcr hcD
    obtain ⟨y', hy', hcy'⟩ := (mem_deletedEdges_iff hT hR hrR π).mp hcD
    refine ⟨fun h => isAncestor_trans hT hyV h hpe.1, fun hcy => ?_⟩
    by_contra hcx
    -- Then the parent edge of `c` is on the path from `y` up to `q`, but it is deleted.
    have hcq : ¬ IsAncestor T r c (rootParent T r R y) :=
      fun h => hcx (isAncestor_trans hT hx h hqx)
    have hcP : parentEdge T r c ∈ walkEdges (T.forestPath y (rootParent T r R y)) :=
      (parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hyV hqanc).mpr ⟨hcy, hcq⟩
    by_cases hyy : y' = y
    · have h' : parentEdge T r c = parentEdge T r x := by rw [← hcy', hyy, ← hxy]
      have := parentEdge_inj hT hcV hx hcr hxr h'
      exact hcx (this ▸ isAncestor_refl T r c)
    · have hy1 : y ∈ R.erase (topRoot T r R) := by rwa [topRoot_eq_of_mem hT hR hrR]
      have hy2 : y' ∈ R.erase (topRoot T r R) := by rwa [topRoot_eq_of_mem hT hR hrR]
      have hdisj := adjacent_paths_disjoint hT hR hRne hy1 hy2 (Ne.symm hyy)
      exact Finset.disjoint_left.mp hdisj hcP (hcy' ▸ deletedEdge_mem hT hR hrR π hy')
  · push Not at hex
    rw [h3 x hx hxR hex]
    have hdp : depth T r (parent T r x) < d := by
      have := depth_parent hT hx hxr; omega
    obtain ⟨hR', hc⟩ := ih _ hdp _ hpV rfl
    refine ⟨hR', connected_trans ?_ hc⟩
    rw [forestGivenRoots_eq, connected_sdiff_parentEdge_iff hT hx hpV]
    intro c hcV hcr hcD
    obtain ⟨y', hy', hcy'⟩ := (mem_deletedEdges_iff hT hR hrR π).mp hcD
    rw [isAncestor_iff_eq_or_parent hT hx]
    constructor
    · rintro (rfl | h)
      · exact absurd hcy'.symm (hex y' hy')
      · exact h.2
    · exact fun h => Or.inr ⟨hxr, h⟩

lemma forestGivenRoots_root_eq (hT : IsRootedTree T r) {R : Finset ℕ} (hR : IsBranchFree T r R)
    (hrR : r ∈ R) (π : ℕ → ℕ) {rt : ℕ → ℕ}
    (hrt : ∀ x ∈ T.V, rt x ∈ R ∧ (forestGivenRoots T r R π).Connected x (rt x))
    {x : ℕ} (hx : x ∈ T.V) : (rootedForestGivenRoots T r R π).root x = rt x :=
  forestGivenRoots_root_eq_of_connected hT hR ⟨r, hrR⟩ π hx (hrt x hx).1 (hrt x hx).2

/-! ## Stretch from tree paths -/

lemma forestGivenRoots_forestPath (hT : IsRootedTree T r) (R : Finset ℕ) (π : ℕ → ℕ)
    {u v : ℕ} (h : (forestGivenRoots T r R π).Connected u v) :
    (forestGivenRoots T r R π).forestPath u v = T.forestPath u v :=
  forestPath_subgraph (F := forestGivenRoots T r R π) (H := T) hT.isForest
    ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩ h

/-- The stretch of `e` in `F_T(R, π)`, given the roots `rt`. -/
theorem forestGivenRoots_stretch (hT : IsRootedTree T r) {R : Finset ℕ}
    (hR : IsBranchFree T r R) (hrR : r ∈ R) (π : ℕ → ℕ) {rt : ℕ → ℕ}
    (hrt : ∀ x ∈ T.V, rt x ∈ R ∧ (forestGivenRoots T r R π).Connected x (rt x))
    (G : MGraph) (ℓ : ℕ → ℝ) {e : ℕ} (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V) :
    (rootedForestGivenRoots T r R π).stretch G ℓ e =
      if rt (G.tail e) = rt (G.head e) then
        1 + walkLength ℓ (T.forestPath (G.tail e) (G.head e)) / ℓ e
      else
        1 + (walkLength ℓ (T.forestPath (G.tail e) (rt (G.tail e))) +
          walkLength ℓ (T.forestPath (G.head e) (rt (G.head e)))) / ℓ e := by
  unfold RootedForest.stretch
  dsimp only
  rw [forestGivenRoots_root_eq hT hR hrR π hrt hu, forestGivenRoots_root_eq hT hR hrR π hrt hv]
  have hF : (rootedForestGivenRoots T r R π).F = forestGivenRoots T r R π := rfl
  rw [hF]
  split_ifs with heq
  · have hc : (forestGivenRoots T r R π).Connected (G.tail e) (G.head e) :=
      connected_trans (hrt _ hu).2 (heq ▸ connected_symm (hrt _ hv).2)
    rw [forestGivenRoots_forestPath hT R π hc]
  · rw [forestGivenRoots_forestPath hT R π (hrt _ hu).2,
      forestGivenRoots_forestPath hT R π (hrt _ hv).2]

/-! ## Path lengths from weighted depths -/

/-- The weighted depth: the length of the path from `x` to the root. -/
noncomputable def wDepth (T : MGraph) (r : ℕ) (ℓ : ℕ → ℝ) (x : ℕ) : ℝ :=
  walkLength ℓ (T.forestPath x r)

lemma walkLength_forestPath_eq_sum (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) {u v : ℕ}
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    walkLength ℓ (T.forestPath u v) = ∑ e ∈ walkEdges (T.forestPath u v), ℓ e :=
  walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT.isForest (hT.connected hu hv))

lemma wDepth_step (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    wDepth T r ℓ x = ℓ (parentEdge T r x) + wDepth T r ℓ (parent T r x) := by
  obtain ⟨-, -, hset, hnot⟩ := walkEdges_up_step hT hx (isAncestor_root hT hx) (Ne.symm hxr)
  unfold wDepth
  rw [walkLength_forestPath_eq_sum hT ℓ hx hT.2,
    walkLength_forestPath_eq_sum hT ℓ (parent_mem hT hx) hT.2, hset, Finset.sum_insert hnot]

lemma wDepth_root (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) : wDepth T r ℓ r = 0 := by
  unfold wDepth
  rw [forestPath_self hT.isForest]
  simp [walkLength, walkEdges]

lemma walkLength_forestPath_anc (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) {u w : ℕ}
    (hu : u ∈ T.V) (hw : IsAncestor T r w u) :
    walkLength ℓ (T.forestPath u w) = wDepth T r ℓ u - wDepth T r ℓ w := by
  have hwV := isAncestor_mem hT hu hw
  obtain ⟨hsplit, hdisj⟩ := forestPath_eq_of_isAncestor hT hu hw
  unfold wDepth
  rw [walkLength_forestPath_eq_sum hT ℓ hu hwV, walkLength_forestPath_eq_sum hT ℓ hu hT.2,
    walkLength_forestPath_eq_sum hT ℓ hwV hT.2, hsplit, walkEdges_append,
    Finset.sum_union hdisj]
  exact (add_sub_cancel_right _ _).symm

lemma walkLength_forestPath_lca (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) {u v : ℕ}
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    walkLength ℓ (T.forestPath u v) =
      (wDepth T r ℓ u - wDepth T r ℓ (lca T r u v)) +
        (wDepth T r ℓ v - wDepth T r ℓ (lca T r u v)) := by
  have hlV := lca_mem hT hu hv
  rw [← walkLength_forestPath_anc hT ℓ hu (lca_isAncestor_left hT hu hv),
    ← walkLength_forestPath_anc hT ℓ hv (lca_isAncestor_right hT hu hv),
    walkLength_forestPath_eq_sum hT ℓ hu hv, walkLength_forestPath_eq_sum hT ℓ hu hlV,
    walkLength_forestPath_eq_sum hT ℓ hv hlV, forestPath_eq_lca hT hu hv, walkEdges_append,
    Finset.sum_union (disjoint_walkEdges_lca hT hu hv),
    forestPath_rev hT.isForest (hT.connected hv hlV), walkEdges_walkRev]

end MinCostFlow.LSF.Program
