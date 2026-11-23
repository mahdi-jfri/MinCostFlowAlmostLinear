module

public import MinCostFlow.LSF.TreeDecomp
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Tree decomposition with a given child order: helper lemmas

The program for `W_T` (Lemma B.7) builds the decomposition bottom-up, as the proof of
`treeDecompSub` (`LSF/TreeDecomp.lean`) does. That proof batches the children of a vertex in the
order of `Finset.toList`, which a program cannot follow. `DecompGenStep.lean` restates the step
for any duplicate-free list of the children. This file holds copies of the helper lemmas of
`TreeDecomp.lean`, which are private there; the statements and proofs are unchanged.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

lemma greedyGroupAux_spec {α : Type*} (θ : ℝ) (f : α → ℝ) (hθ : 0 < θ) :
    ∀ rest acc (cur : ℝ),
      0 ≤ cur → cur < θ → (acc.map f).sum = cur → (∀ y ∈ acc, 0 ≤ f y) →
      (∀ x ∈ rest, 0 ≤ f x ∧ f x < 2 * θ) →
      let res := greedyGroupAux θ f acc cur rest
      (acc ++ rest).Perm (res.1.flatten ++ res.2) ∧
      (∀ b ∈ res.1, b ≠ [] ∧ θ ≤ (b.map f).sum ∧ (b.map f).sum < 3 * θ ∧ ∀ y ∈ b, 0 ≤ f y) ∧
      (res.2.map f).sum < θ ∧ ∀ y ∈ res.2, 0 ≤ f y := by
  intro rest
  induction rest with
  | nil =>
    intro acc cur _ hlt hsum hacc _
    unfold greedyGroupAux
    simp only [List.append_nil, List.flatten_nil, List.nil_append]
    exact ⟨List.Perm.refl _, fun _ hb => by simp at hb, hsum ▸ hlt, hacc⟩
  | cons x xs ih =>
    intro acc cur hcur0 hcur_lt hsum hacc hrest
    have hfx := hrest x List.mem_cons_self
    have hxs : ∀ y ∈ xs, 0 ≤ f y ∧ f y < 2 * θ := fun y hy => hrest y (List.mem_cons_of_mem _ hy)
    have hsum' : ((x :: acc).map f).sum = cur + f x := by
      simp only [List.map_cons, List.sum_cons, hsum, add_comm]
    have hacc' : ∀ y ∈ x :: acc, 0 ≤ f y := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hfx.1
      · exact hacc y hy'
    unfold greedyGroupAux
    dsimp only
    by_cases hge : θ ≤ cur + f x
    · rw [ite_eq_left_iff.mpr (fun h => absurd hge h)]
      have hres := ih [] 0 le_rfl hθ rfl (by simp) hxs
      rcases hres with ⟨hperm, hbatches, hrem_sum, hrem_nonneg⟩
      dsimp only at hperm hbatches hrem_sum hrem_nonneg ⊢
      refine ⟨?_, ?_, hrem_sum, hrem_nonneg⟩
      · have h1 : (acc ++ x :: xs).Perm ((x :: acc) ++ xs) :=
          List.perm_middle (a := x) (l₁ := acc) (l₂ := xs)
        simpa only [List.flatten_cons, List.append_assoc] using
          h1.trans ((List.Perm.refl (x :: acc)).append (by simpa using hperm))
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ⟨List.cons_ne_nil _ _, hsum'.symm ▸ hge, by rw [hsum']; linarith, hacc'⟩
        · exact hbatches b hb'
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hge)]
      have hres := ih (x :: acc) (cur + f x) (add_nonneg hcur0 hfx.1) (lt_of_not_ge hge) hsum' hacc' hxs
      rcases hres with ⟨hperm, hbatches, hrem_sum, hrem_nonneg⟩
      refine ⟨?_, hbatches, hrem_sum, hrem_nonneg⟩
      exact (List.perm_middle (a := x) (l₁ := acc) (l₂ := xs)).trans hperm

/-! ## Inductive subtree decomposition -/

lemma child_ne_root {T : MGraph} {r u c : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hc : c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u)) :
    c ≠ r := by
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc
  intro hEq
  have hanc := (mem_subtree_iff.mp hc.1.1).2
  rw [hEq] at hanc
  exact hc.1.2 (hEq.trans (isAncestor_antisymm hT hT.2 hu (isAncestor_root hT hu) hanc))

lemma children_subtree_disjoint {T : MGraph} {r u c₁ c₂ : ℕ} (hT : IsRootedTree T r)
    (hc₁ : c₁ ∈ T.V) (hc₂ : c₂ ∈ T.V) (hcr₁ : c₁ ≠ r) (hcr₂ : c₂ ≠ r)
    (hp₁ : parent T r c₁ = u) (hp₂ : parent T r c₂ = u) (hne : c₁ ≠ c₂) :
    Disjoint (subtree T r c₁) (subtree T r c₂) := by
  rw [Finset.disjoint_left]
  intro w hw₁ hw₂
  rw [mem_subtree_iff] at hw₁ hw₂
  rcases isAncestor_total_on_ancestors hT hw₁.1 hw₁.2 hw₂.2 with h12 | h21
  · rcases (isAncestor_iff_eq_or_parent hT hc₂).mp h12 with hEq | ⟨_, hp⟩
    · exact hne hEq
    · rw [hp₂, ← hp₁] at hp
      have := isAncestor_depth_le hT (parent_mem hT hc₁) hp
      have hd1 := depth_parent hT hc₁ hcr₁
      have hd2 := depth_parent hT hc₂ hcr₂
      omega
  · rcases (isAncestor_iff_eq_or_parent hT hc₁).mp h21 with hEq | ⟨_, hp⟩
    · exact hne hEq.symm
    · rw [hp₁, ← hp₂] at hp
      have := isAncestor_depth_le hT (parent_mem hT hc₂) hp
      have hd1 := depth_parent hT hc₁ hcr₁
      have hd2 := depth_parent hT hc₂ hcr₂
      omega

lemma mem_subtree_children_iff {T : MGraph} {r u x : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hx : x ∈ subtree T r u) (hxne : x ≠ u) :
    ∃! c, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) ∧ x ∈ subtree T r c := by
  have hxV := (mem_subtree_iff.mp hx).1
  have hux := (mem_subtree_iff.mp hx).2
  have h_ex : ∃ c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u), x ∈ subtree T r c := by
    have hind : ∀ d y, depth T r y = d → y ∈ T.V → IsAncestor T r u y → y ≠ u →
        ∃ c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u), y ∈ subtree T r c := by
      intro d
      induction d with
      | zero =>
        intro y hdy hyV huy hne
        have hyr : y = r := by
          by_contra hne'
          obtain ⟨_, hEq, _⟩ := forestPath_parent hT hyV hne'
          unfold depth at hdy; rw [hEq, List.length_cons] at hdy; omega
        rw [hyr] at huy hne
        exact absurd (isAncestor_antisymm hT (isAncestor_mem hT hT.2 huy) hT.2 huy
          (isAncestor_root hT (isAncestor_mem hT hT.2 huy))).symm hne
      | succ d' ih =>
        intro y hdy hyV huy hne
        have hyr : y ≠ r := by
          intro hEq; unfold depth at hdy
          rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hdy; omega
        by_cases hpy : parent T r y = u
        · exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
            ⟨mem_subtree_iff.mpr ⟨hyV, huy⟩, by simpa only [Finset.mem_singleton] using hne⟩, hpy⟩,
            mem_subtree_iff.mpr ⟨hyV, isAncestor_refl T r y⟩⟩
        · have hup : IsAncestor T r u (parent T r y) := by
            rcases (isAncestor_iff_eq_or_parent hT hyV).mp huy with hEq | ⟨_, hp⟩
            · exact absurd hEq.symm hne
            · exact hp
          have hdp := depth_parent hT hyV hyr
          obtain ⟨c, hc, hpc⟩ := ih (parent T r y) (by omega) (parent_mem hT hyV) hup hpy
          rw [mem_subtree_iff] at hpc
          exact ⟨c, hc, mem_subtree_iff.mpr ⟨hyV, isAncestor_trans hT hyV hpc.2 (isAncestor_parent hT hyV hyr)⟩⟩
    exact hind (depth T r x) x rfl hxV hux hxne
  obtain ⟨c, hc, hxc⟩ := h_ex
  refine ⟨c, ⟨hc, hxc⟩, fun c' ⟨hc', hxc'⟩ => ?_⟩
  have hcr := child_ne_root hT hu hc
  have hc'r := child_ne_root hT hu hc'
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc hc'
  have hcV := (mem_subtree_iff.mp hc.1.1).1
  have hc'V := (mem_subtree_iff.mp hc'.1.1).1
  by_contra hne'
  have hdisj := children_subtree_disjoint hT hc'V hcV hc'r hcr hc'.2 hc.2 hne'
  exact Finset.disjoint_left.mp hdisj hxc' hxc

lemma pathConvex_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (S : Finset ℕ) (L : ℕ → Finset ℕ)
    (hS : ∀ c ∈ S, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u))
    (hL_sub : ∀ c ∈ S, c ∈ L c ∧ L c ⊆ subtree T r c)
    (hL_pc : ∀ c ∈ S, PathConvex T (L c)) :
    PathConvex T (insert u (S.biUnion L)) := by
  classical
  let U := insert u (S.biUnion L)
  have hU_sub : U ⊆ T.V := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_biUnion] at hv
    rcases hv with rfl | ⟨c, hcS, hvL⟩
    · exact hu
    · exact (hL_pc c hcS).2.1 hvL
  refine ⟨⟨u, Finset.mem_insert_self _ _⟩, hU_sub, fun a ha b hb w hw => ?_⟩
  have h_to_u : ∀ {c : ℕ} (hc : c ∈ S) {x : ℕ} (hx : x ∈ L c),
      ∀ z ∈ T.walkVertices x (T.forestPath x u), z ∈ insert u (L c) := by
    intro c hc x hx z hz
    have hc_filt := hS c hc
    have hcr := child_ne_root hT hu hc_filt
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc_filt
    have hcx : IsAncestor T r c x := (mem_subtree_iff.mp ((hL_sub c hc).2 hx)).2
    have huc : IsAncestor T r u c := hc_filt.2 ▸ isAncestor_parent hT (mem_subtree_iff.mp hc_filt.1.1).1 hcr
    have hux : IsAncestor T r u x := isAncestor_trans hT ((hL_pc c hc).2.1 hx) huc hcx
    rw [mem_walkVertices_ancestorPath_iff hT ((hL_pc c hc).2.1 hx) hux] at hz
    rw [Finset.mem_insert]
    by_cases hzu : z = u
    · exact Or.inl hzu
    · right
      have hcz : IsAncestor T r c z := by
        rcases isAncestor_total_on_ancestors hT ((hL_pc c hc).2.1 hx) hcx hz.2 with h1 | h2
        · exact h1
        · rcases (isAncestor_iff_eq_or_parent hT (mem_subtree_iff.mp hc_filt.1.1).1).mp h2 with hEq | ⟨_, hp⟩
          · rw [hEq]; exact isAncestor_refl T r c
          · rw [hc_filt.2] at hp
            exact absurd (isAncestor_antisymm hT (isAncestor_mem hT hu hp) hu hp hz.1) hzu
      exact (hL_pc c hc).2.2 x hx c (hL_sub c hc).1 z
        ((mem_walkVertices_ancestorPath_iff hT ((hL_pc c hc).2.1 hx) hcx).mpr ⟨hcz, hz.2⟩)
  have haV := hU_sub ha
  have hbV := hU_sub hb
  rw [Finset.mem_insert, Finset.mem_biUnion] at ha hb
  rcases ha with h_au | ⟨c₁, hc₁, haL⟩ <;> rcases hb with h_bu | ⟨c₂, hc₂, hbL⟩
  · simp only [h_au, h_bu, forestPath_self hT.isForest u, MGraph.walkVertices, List.map_nil,
      List.mem_singleton] at hw
    rw [hw]; exact Finset.mem_insert_self _ _
  · subst h_au
    rw [forestPath_rev hT.isForest (hT.connected hbV haV),
      walkVertices_walkRev (forestPath_isPath hT.isForest (hT.connected hbV haV)).1,
      List.mem_reverse] at hw
    rcases Finset.mem_insert.mp (h_to_u hc₂ hbL w hw) with rfl | hwL
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c₂, hc₂, hwL⟩)
  · subst h_bu
    rcases Finset.mem_insert.mp (h_to_u hc₁ haL w hw) with rfl | hwL
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c₁, hc₁, hwL⟩)
  · by_cases hc_eq : c₁ = c₂
    · subst hc_eq
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c₁, hc₁, (hL_pc c₁ hc₁).2.2 a haL b hbL w hw⟩)
    · have hf₁ := hS c₁ hc₁; have hf₂ := hS c₂ hc₂
      have hcr₁ := child_ne_root hT hu hf₁
      have hcr₂ := child_ne_root hT hu hf₂
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hf₁ hf₂
      have hc₁V := (mem_subtree_iff.mp hf₁.1.1).1
      have hc₂V := (mem_subtree_iff.mp hf₂.1.1).1
      have hdisj := children_subtree_disjoint hT hc₁V hc₂V hcr₁ hcr₂ hf₁.2 hf₂.2 hc_eq
      have hua : IsAncestor T r u a := isAncestor_trans hT haV (hf₁.2 ▸ isAncestor_parent hT hc₁V hcr₁)
        (mem_subtree_iff.mp ((hL_sub c₁ hc₁).2 haL)).2
      have hub : IsAncestor T r u b := isAncestor_trans hT hbV (hf₂.2 ▸ isAncestor_parent hT hc₂V hcr₂)
        (mem_subtree_iff.mp ((hL_sub c₂ hc₂).2 hbL)).2
      have hu_lca : IsAncestor T r u (lca T r a b) := (isAncestor_lca_iff hT haV hbV).mpr ⟨hua, hub⟩
      have hlca_eq : lca T r a b = u := by
        by_contra hne_l
        have hlV := lca_mem hT haV hbV
        have hca : IsAncestor T r c₁ (lca T r a b) := by
          rcases isAncestor_total_on_ancestors hT haV (mem_subtree_iff.mp ((hL_sub c₁ hc₁).2 haL)).2
              (lca_isAncestor_left hT haV hbV) with h1 | h2
          · exact h1
          · rcases (isAncestor_iff_eq_or_parent hT hc₁V).mp h2 with hEq | ⟨_, hp⟩
            · rw [hEq]; exact isAncestor_refl T r c₁
            · rw [hf₁.2] at hp
              exact absurd (isAncestor_antisymm hT hlV hu hp hu_lca) hne_l
        have hcb : IsAncestor T r c₂ (lca T r a b) := by
          rcases isAncestor_total_on_ancestors hT hbV (mem_subtree_iff.mp ((hL_sub c₂ hc₂).2 hbL)).2
              (lca_isAncestor_right hT haV hbV) with h1 | h2
          · exact h1
          · rcases (isAncestor_iff_eq_or_parent hT hc₂V).mp h2 with hEq | ⟨_, hp⟩
            · rw [hEq]; exact isAncestor_refl T r c₂
            · rw [hf₂.2] at hp
              exact absurd (isAncestor_antisymm hT hlV hu hp hu_lca) hne_l
        exact Finset.disjoint_left.mp hdisj (mem_subtree_iff.mpr ⟨hlV, hca⟩) (mem_subtree_iff.mpr ⟨hlV, hcb⟩)
      rw [mem_walkVertices_forestPath_iff hT haV hbV, hlca_eq] at hw
      rcases hw.2 with hwa | hwb
      · rcases Finset.mem_insert.mp (h_to_u hc₁ haL w ((mem_walkVertices_ancestorPath_iff hT haV hua).mpr ⟨hw.1, hwa⟩)) with rfl | hwL
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c₁, hc₁, hwL⟩)
      · rcases Finset.mem_insert.mp (h_to_u hc₂ hbL w ((mem_walkVertices_ancestorPath_iff hT hbV hub).mpr ⟨hw.1, hwb⟩)) with rfl | hwL
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c₂, hc₂, hwL⟩)

lemma inducedEdges_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (S : Finset ℕ) (L : ℕ → Finset ℕ)
    (hS : ∀ c ∈ S, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u))
    (hL_sub : ∀ c ∈ S, c ∈ L c ∧ L c ⊆ subtree T r c) :
    inducedEdges T (insert u (S.biUnion L)) =
      (S.image (parentEdge T r)) ∪ S.biUnion (fun c => inducedEdges T (L c)) := by
  classical
  apply Finset.ext
  intro e
  simp only [inducedEdges, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_insert]
  have hL_V : ∀ {c : ℕ}, c ∈ S → ∀ {x : ℕ}, x ∈ L c → x ∈ T.V := by
    intro c hc x hx
    exact (mem_subtree_iff.mp ((hL_sub c hc).2 hx)).1
  have hc_eq : ∀ {c : ℕ}, c ∈ S → ∀ {x : ℕ}, x ∈ L c → parent T r x = u → x = c := by
    intro c hc x hx hpx
    have hf := hS c hc
    have hcr := child_ne_root hT hu hf
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hf
    have hcV := (mem_subtree_iff.mp hf.1.1).1
    have hxV := hL_V hc hx
    have hxr : x ≠ r := fun hEq => by
      have hx_anc := (mem_subtree_iff.mp ((hL_sub c hc).2 hx)).2
      rw [hEq] at hx_anc
      exact hcr (isAncestor_antisymm hT hT.2 hcV (isAncestor_root hT hcV) hx_anc).symm
    have hdc := depth_parent hT hcV hcr
    have hdx := depth_parent hT hxV hxr
    rw [hf.2] at hdc
    rw [hpx] at hdx
    have hcx := (mem_subtree_iff.mp ((hL_sub c hc).2 hx)).2
    have hle := isAncestor_depth_le hT hxV hcx
    exact ((isAncestor_eq_iff_depth hT hxV hcx).mp (by omega)).symm
  have h_dir : ∀ {p q : ℕ}, e ∈ T.E → p ∈ T.V → q ∈ T.V →
      parent T r p = q → parentEdge T r p = e → p ≠ r →
      (p = u ∨ ∃ c ∈ S, p ∈ L c) → (q = u ∨ ∃ c ∈ S, q ∈ L c) →
      (∃ c ∈ S, parentEdge T r c = e) ∨ (∃ c ∈ S, e ∈ T.E ∧ p ∈ L c ∧ q ∈ L c) := by
    intro p q heT hpV hqV hpq hpe hpr hp_in hq_in
    rcases hp_in with hpu | ⟨c₁, hc₁, hpL⟩
    · exfalso
      rcases hq_in with hqu | ⟨c₂, hc₂, hqL⟩
      · have hdp := depth_parent hT hpV hpr
        rw [hpq, hqu, ← hpu] at hdp
        omega
      · have hf₂ := hS c₂ hc₂
        have hcr₂ := child_ne_root hT hu hf₂
        rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hf₂
        have hc₂V := (mem_subtree_iff.mp hf₂.1.1).1
        have hp_anc : IsAncestor T r q u := by
          have := isAncestor_parent hT hpV hpr
          rwa [hpq, hpu] at this
        have hu_c₂ : IsAncestor T r u c₂ := hf₂.2 ▸ isAncestor_parent hT hc₂V hcr₂
        have hc₂_q : IsAncestor T r c₂ q := (mem_subtree_iff.mp ((hL_sub c₂ hc₂).2 hqL)).2
        have hqu : q = u := isAncestor_antisymm hT hqV hu hp_anc (isAncestor_trans hT hqV hu_c₂ hc₂_q)
        have hc₂u : c₂ = u := isAncestor_antisymm hT hc₂V hu (hqu ▸ hc₂_q) hu_c₂
        exact hf₂.1.2 hc₂u
    · rcases hq_in with hqu | ⟨c₂, hc₂, hqL⟩
      · have hpc₁ := hc_eq hc₁ hpL (hpq.trans hqu)
        exact Or.inl ⟨c₁, hc₁, by rw [← hpc₁, hpe]⟩
      · by_cases h_same : c₁ = c₂
        · subst h_same
          exact Or.inr ⟨c₁, hc₁, heT, hpL, hqL⟩
        · exfalso
          have hf₁ := hS c₁ hc₁; have hf₂ := hS c₂ hc₂
          have hcr₁ := child_ne_root hT hu hf₁
          have hcr₂ := child_ne_root hT hu hf₂
          rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hf₁ hf₂
          have hc₁V := (mem_subtree_iff.mp hf₁.1.1).1
          have hc₂V := (mem_subtree_iff.mp hf₂.1.1).1
          by_cases hpc₁ : p = c₁
          · have hqu : q = u := by rw [← hpq, hpc₁, hf₁.2]
            have hc₂_u : IsAncestor T r c₂ u := hqu ▸ (mem_subtree_iff.mp ((hL_sub c₂ hc₂).2 hqL)).2
            have hu_c₂ : IsAncestor T r u c₂ := hf₂.2 ▸ isAncestor_parent hT hc₂V hcr₂
            exact hf₂.1.2 (isAncestor_antisymm hT hc₂V hu hc₂_u hu_c₂)
          · have hpc_anc := (mem_subtree_iff.mp ((hL_sub c₁ hc₁).2 hpL)).2
            rcases (isAncestor_iff_eq_or_parent hT hpV).mp hpc_anc with hEq | ⟨_, hp'⟩
            · exact hpc₁ hEq.symm
            · rw [hpq] at hp'
              have hdisj := children_subtree_disjoint hT hc₁V hc₂V hcr₁ hcr₂ hf₁.2 hf₂.2 h_same
              exact Finset.disjoint_left.mp hdisj (mem_subtree_iff.mpr ⟨hqV, hp'⟩) ((hL_sub c₂ hc₂).2 hqL)
  constructor
  · rintro ⟨heT, ht_mem, hh_mem⟩
    rcases edge_parent_orientation hT heT with ⟨hp, hpe, htr⟩ | ⟨hp, hpe, hhr⟩
    · exact h_dir heT (hT.isForest.1 e heT).1 (hT.isForest.1 e heT).2 hp hpe htr ht_mem hh_mem
    · rcases h_dir heT (hT.isForest.1 e heT).2 (hT.isForest.1 e heT).1 hp hpe hhr hh_mem ht_mem with
        h1 | ⟨c, hc, he, hh, ht⟩
      · exact Or.inl h1
      · exact Or.inr ⟨c, hc, he, ht, hh⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, heT, htL, hhL⟩)
    · have hf := hS c hc
      have hcr := child_ne_root hT hu hf
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hf
      have hcV := (mem_subtree_iff.mp hf.1.1).1
      refine ⟨parentEdge_mem hT hcV hcr, ?_, ?_⟩
      · have hend := parentEdge_endpoints hT hcV hcr
        have hmem := (hend ▸ Set.mem_insert (T.tail (parentEdge T r c)) _ :
          T.tail (parentEdge T r c) ∈ ({c, parent T r c} : Set ℕ))
        rcases Set.mem_insert_iff.mp hmem with h1 | h1
        · right; exact ⟨c, hc, h1.symm ▸ (hL_sub c hc).1⟩
        · rw [Set.mem_singleton_iff.mp h1, hf.2]; exact Or.inl rfl
      · have hend := parentEdge_endpoints hT hcV hcr
        have hmem := (hend ▸ Set.mem_insert_of_mem _ (Set.mem_singleton (T.head (parentEdge T r c))) :
          T.head (parentEdge T r c) ∈ ({c, parent T r c} : Set ℕ))
        rcases Set.mem_insert_iff.mp hmem with h1 | h1
        · right; exact ⟨c, hc, h1.symm ▸ (hL_sub c hc).1⟩
        · rw [Set.mem_singleton_iff.mp h1, hf.2]; exact Or.inl rfl
    · exact ⟨heT, Or.inr ⟨c, hc, htL⟩, Or.inr ⟨c, hc, hhL⟩⟩

/-! ## Inductive subtree decomposition -/

lemma list_flatten_nodup_pairwise_disjoint :
    ∀ ls : List (List ℕ), ls.flatten.Nodup →
      ∀ b₁ ∈ ls, ∀ b₂ ∈ ls, b₁ ≠ b₂ → Disjoint b₁.toFinset b₂.toFinset
  | [], _, _, hb₁, _, _, _ => by simp at hb₁
  | a :: tl, hnd, b₁, hb₁, b₂, hb₂, hne => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    rcases List.mem_cons.mp hb₁ with rfl | hb₁' <;> rcases List.mem_cons.mp hb₂ with rfl | hb₂'
    · exact absurd rfl hne
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hnd.2.2 x (List.mem_toFinset.mp hx1) x
        (List.mem_flatten.mpr ⟨b₂, hb₂', List.mem_toFinset.mp hx2⟩) rfl
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hnd.2.2 x (List.mem_toFinset.mp hx2) x
        (List.mem_flatten.mpr ⟨b₁, hb₁', List.mem_toFinset.mp hx1⟩) rfl
    · exact list_flatten_nodup_pairwise_disjoint tl hnd.2.1 b₁ hb₁' b₂ hb₂' hne

lemma list_flatten_nodup_mem {a : List ℕ} {ls : List (List ℕ)}
    (hnd : ls.flatten.Nodup) (ha : a ∈ ls) : a.Nodup := by
  induction ls with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hnd.1
    · exact ih hnd.2.1 ha'

lemma list_sum_map_eq_sum_flatten (f : ℕ → ℝ) :
    ∀ ls : List (List ℕ), ls.flatten.Nodup →
      (ls.map (fun b => (b.map f).sum)).sum = ∑ c ∈ ls.flatten.toFinset, f c
  | [], _ => by simp
  | b :: bs, hnd => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    have hdisj : Disjoint b.toFinset bs.flatten.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hnd.2.2 x (List.mem_toFinset.mp hx1) x (List.mem_toFinset.mp hx2) rfl
    rw [List.map_cons, List.sum_cons, List.flatten_cons, List.toFinset_append,
      Finset.sum_union hdisj, list_sum_map_eq_sum_flatten f bs hnd.2.1, List.sum_toFinset _ hnd.1]

lemma subtree_child_subset {T : MGraph} {r u c : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u)) :
    subtree T r c ⊆ subtree T r u \ {u} := by
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc
  have huc : IsAncestor T r u c := (mem_subtree_iff.mp hc.1.1).2
  intro x hx
  rw [mem_subtree_iff] at hx
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  refine ⟨mem_subtree_iff.mpr ⟨hx.1, isAncestor_trans hT hx.1 huc hx.2⟩, fun hxu => hc.1.2 ?_⟩
  rw [hxu] at hx
  exact isAncestor_antisymm hT (mem_subtree_iff.mp hc.1.1).1 hx.1 hx.2 huc

lemma subtree_eq_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) :
    subtree T r u =
      insert u (((subtree T r u \ {u}).filter (fun c => parent T r c = u)).biUnion (subtree T r)) := by
  apply Finset.ext
  intro x
  rw [Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    · right
      obtain ⟨c, ⟨hc, hxc⟩, _⟩ := mem_subtree_children_iff hT hu hx hxu
      exact ⟨c, hc, hxc⟩
  · rintro (hEq | ⟨c, hc, hxc⟩)
    · rw [hEq]
      exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    · exact Finset.sdiff_subset (subtree_child_subset hT hc hxc)

lemma list_len_mul_le_sum (θ : ℝ) (f : ℕ → ℝ) :
    ∀ ls : List (List ℕ), (∀ b ∈ ls, θ ≤ (b.map f).sum) →
      θ * (ls.length : ℝ) ≤ (ls.map (fun b => (b.map f).sum)).sum
  | [], _ => by simp
  | b :: bs, h => by
    have hb := h b List.mem_cons_self
    have ih := list_len_mul_le_sum θ f bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    linarith


end MinCostFlow.LSF.Program.DecompGen
