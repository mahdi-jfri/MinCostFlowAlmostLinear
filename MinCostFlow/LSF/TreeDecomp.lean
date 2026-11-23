module

public import MinCostFlow.LSF.PathRoot
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Spielman–Teng Tree Decomposition ([chen2022maximum] Lemma B.7)

This file formalizes `[chen2022maximum, Lemma B.7]`:
Given a valid graph `G`, nonnegative edge weights `w : ℕ → ℝ`, a rooted spanning tree `(T, r)` of `G`
with `2 ≤ G.V.card` and `G.E.Nonempty`, and parameter `1 ≤ k`, `lemma_B_7` produces a decomposition
`𝒲` of `T` into edge-disjoint path-convex subtrees covering `T.E` such that:
1. `𝒲.card ≤ 6 * (G.E.card : ℝ) / k + 6` (`O(m/k + 1)`, hence `O(m/k)` when `k ≤ m`).
2. `boundary 𝒲` is branch-free in `(T, r)`.
3. For every piece `C ∈ 𝒲`, the total weight of edges with `e ∩ C ⊈ boundary 𝒲` is at most
   `40 * (∑ e ∈ G.E, w e) * k / G.E.card`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Vertex weights and boundary cardinality bound -/

/-- Total weight of edges in `G` incident to `v` (counting self-loops twice). -/
noncomputable def vWeight (G : MGraph) (w : ℕ → ℝ) (v : ℕ) : ℝ :=
  ∑ e ∈ G.E, ((if G.tail e = v then w e else 0) + (if G.head e = v then w e else 0))

lemma vWeight_nonneg {G : MGraph} {w : ℕ → ℝ} (hw : ∀ e ∈ G.E, 0 ≤ w e) (v : ℕ) :
    0 ≤ vWeight G w v := by
  refine Finset.sum_nonneg (fun e he => add_nonneg ?_ ?_) <;>
    split_ifs <;> first | exact hw e he | exact le_rfl

lemma sum_vWeight {G : MGraph} (hG : G.IsValid) (w : ℕ → ℝ) :
    ∑ v ∈ G.V, vWeight G w v = 2 * ∑ e ∈ G.E, w e := by
  unfold vWeight
  rw [Finset.sum_comm]
  have hterm : ∀ e ∈ G.E,
      ∑ v ∈ G.V, ((if G.tail e = v then w e else 0) + (if G.head e = v then w e else 0)) =
        2 * w e := by
    intro e he
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    rw [ite_eq_left_iff.mpr (fun h => absurd (hG e he).1 h),
        ite_eq_left_iff.mpr (fun h => absurd (hG e he).2 h), two_mul]
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum]

lemma sum_nonboundary_edges_le_vWeight {G : MGraph} {w : ℕ → ℝ} (hw : ∀ e ∈ G.E, 0 ≤ w e)
    (C R : Finset ℕ) :
    ∑ e ∈ G.E.filter (fun e => (G.tail e ∈ C ∧ G.tail e ∉ R) ∨ (G.head e ∈ C ∧ G.head e ∉ R)),
        w e ≤
      ∑ v ∈ C \ R, vWeight G w v := by
  classical
  unfold vWeight
  rw [Finset.sum_comm]
  have hle : ∀ e ∈ G.E,
      (if (G.tail e ∈ C ∧ G.tail e ∉ R) ∨ (G.head e ∈ C ∧ G.head e ∉ R) then w e else 0) ≤
        ∑ v ∈ C \ R, ((if G.tail e = v then w e else 0) + (if G.head e = v then w e else 0)) := by
    intro e he
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    have hwe := hw e he
    by_cases ht : G.tail e ∈ C ∧ G.tail e ∉ R <;> by_cases hh : G.head e ∈ C ∧ G.head e ∉ R
    · rw [ite_eq_left_iff.mpr (fun h => absurd (Or.inl ht) h),
          ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_sdiff.mpr ht) h),
          ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_sdiff.mpr hh) h)]
      exact le_add_of_nonneg_right hwe
    · rw [ite_eq_left_iff.mpr (fun h => absurd (Or.inl ht) h),
          ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_sdiff.mpr ht) h),
          ite_eq_right_iff.mpr (fun h => absurd (Finset.mem_sdiff.mp h) hh), add_zero]
    · rw [ite_eq_left_iff.mpr (fun h => absurd (Or.inr hh) h),
          ite_eq_right_iff.mpr (fun h => absurd (Finset.mem_sdiff.mp h) ht),
          ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_sdiff.mpr hh) h), zero_add]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h (fun h' => h'.elim (fun h1 => ht h1) (fun h2 => hh h2)))]
      refine add_nonneg ?_ ?_ <;> split_ifs <;> first | exact hwe | exact le_rfl
  rw [Finset.sum_filter]
  exact Finset.sum_le_sum hle

private lemma pathConvex_top_exists {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {W : Finset ℕ} (hW : PathConvex T W) :
    ∃ t ∈ W, ∀ v ∈ W, IsAncestor T r t v := by
  classical
  obtain ⟨t, htW, htmin⟩ := Finset.exists_min_image W (depth T r) hW.1
  refine ⟨t, htW, fun v hvW => ?_⟩
  have hl_mem : lca T r t v ∈ W :=
    hW.2.2 t htW v hvW (lca T r t v) (lca_mem_forestPath hT (hW.2.1 htW) (hW.2.1 hvW))
  have hl_t := lca_isAncestor_left hT (hW.2.1 htW) (hW.2.1 hvW)
  have hl_v := lca_isAncestor_right hT (hW.2.1 htW) (hW.2.1 hvW)
  have hd_min := htmin _ hl_mem
  have hd_le := isAncestor_depth_le hT (hW.2.1 htW) hl_t
  have hl_eq : lca T r t v = t :=
    (isAncestor_eq_iff_depth hT (hW.2.1 htW) hl_t).mp (Nat.le_antisymm hd_le hd_min)
  rwa [← hl_eq]

lemma pathConvex_edges_between_mem {T : MGraph} (hT : T.IsForest)
    {W : Finset ℕ} (hW : PathConvex T W) (hconn : ∀ a ∈ W, ∀ b ∈ W, T.Connected a b)
    {u v : ℕ} (hu : u ∈ W) (hv : v ∈ W) (hne : u ≠ v) :
    (walkEdges (T.forestPath u v)).Nonempty ∧ walkEdges (T.forestPath u v) ⊆ inducedEdges T W := by
  have hP := forestPath_isPath hT (hconn u hu v hv)
  have hne_P : T.forestPath u v ≠ [] := by
    intro hnil
    have hend : u = v := by
      have hw := hP.1
      rw [hnil] at hw
      cases hw; rfl
    exact hne hend
  obtain ⟨x, xs, hEq⟩ := List.exists_cons_of_ne_nil hne_P
  refine ⟨⟨x.1, by rw [hEq, walkEdges_cons, Finset.mem_insert]; exact Or.inl rfl⟩, ?_⟩
  intro e he
  rw [inducedEdges, Finset.mem_filter]
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  refine ⟨IsWalk_edges_mem hP.1 hy, ?_⟩
  have ⟨hsrc, hdst⟩ := IsWalk_mem_ends hP.1 hy
  rcases y with ⟨e', b'⟩
  cases b'
  · exact ⟨hW.2.2 u hu v hv _ hdst, hW.2.2 u hu v hv _ hsrc⟩
  · exact ⟨hW.2.2 u hu v hv _ hsrc, hW.2.2 u hu v hv _ hdst⟩

/-- Any nonempty collection `𝒲` of edge-disjoint path-convex subtrees of a rooted tree `(T, r)`
has `(boundary 𝒲).card + 1 ≤ 𝒲.card`. -/
lemma boundary_card_lt {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ n (𝒲 : Finset (Finset ℕ)), 𝒲.card = n → 𝒲.Nonempty →
      (∀ W ∈ 𝒲, PathConvex T W) →
      (∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, W₁ ≠ W₂ → Disjoint (inducedEdges T W₁) (inducedEdges T W₂)) →
      (boundary 𝒲).card + 1 ≤ 𝒲.card := by
  intro n
  induction n with
  | zero =>
    intro 𝒲 hn hne
    exfalso
    rw [Finset.card_eq_zero.mp hn] at hne
    exact Finset.not_nonempty_empty hne
  | succ k ih =>
    intro 𝒲 hn hne hPC hdisj
    by_cases hk0 : k = 0
    · have hcard1 : 𝒲.card = 1 := by omega
      obtain ⟨W₀, rfl⟩ := Finset.card_eq_one.mp hcard1
      have hbe : boundary ({W₀} : Finset (Finset ℕ)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [mem_boundary_iff] at hv
        obtain ⟨A, hA, B, hB, hneAB, _⟩ := hv
        rw [Finset.mem_singleton] at hA hB
        exact hneAB (hA.trans hB.symm)
      rw [hbe, Finset.card_empty]
      exact Nat.le_refl _
    · classical
      have htop : ∀ W ∈ 𝒲, ∃ t ∈ W, ∀ v ∈ W, IsAncestor T r t v :=
        fun W hW => pathConvex_top_exists hT (hPC W hW)
      let topOf : Finset ℕ → ℕ := fun W =>
        if h : W ∈ 𝒲 then Classical.choose (htop W h) else r
      have topOf_spec : ∀ W (hW : W ∈ 𝒲), topOf W ∈ W ∧ ∀ v ∈ W, IsAncestor T r (topOf W) v := by
        intro W hW
        have : topOf W = Classical.choose (htop W hW) := by
          unfold topOf; exact dite_eq_left_of_eq_true (eq_true hW)
        rw [this]
        exact Classical.choose_spec (htop W hW)
      obtain ⟨W₀, hW₀, hmax⟩ := Finset.exists_max_image 𝒲 (fun W => depth T r (topOf W)) hne
      obtain ⟨ht₀_mem, ht₀_anc⟩ := topOf_spec W₀ hW₀
      have h_only_top : ∀ W₁ ∈ 𝒲, W₁ ≠ W₀ → ∀ v ∈ W₀, v ∈ W₁ → v = topOf W₀ := by
        intro W₁ hW₁ hneW v hv0 hv1
        by_contra hvt₀
        obtain ⟨ht₁_mem, ht₁_anc⟩ := topOf_spec W₁ hW₁
        have hvV := (hPC W₀ hW₀).2.1 hv0
        have ht₀V := (hPC W₀ hW₀).2.1 ht₀_mem
        have ht₁V := (hPC W₁ hW₁).2.1 ht₁_mem
        have hconn0 : ∀ a ∈ W₀, ∀ b ∈ W₀, T.Connected a b := fun a ha b hb =>
          hT.connected ((hPC W₀ hW₀).2.1 ha) ((hPC W₀ hW₀).2.1 hb)
        have hconn1 : ∀ a ∈ W₁, ∀ b ∈ W₁, T.Connected a b := fun a ha b hb =>
          hT.connected ((hPC W₁ hW₁).2.1 ha) ((hPC W₁ hW₁).2.1 hb)
        have ht₀_in_W₁ : topOf W₀ ∈ W₁ := by
          rcases isAncestor_total_on_ancestors hT hvV (ht₀_anc v hv0) (ht₁_anc v hv1) with h01 | h10
          · have hd_max := hmax W₁ hW₁
            have hd_le := isAncestor_depth_le hT ht₁V h01
            have hEq := (isAncestor_eq_iff_depth hT ht₁V h01).mp (Nat.le_antisymm hd_le hd_max)
            exact hEq ▸ ht₁_mem
          · have hmem_rev : topOf W₀ ∈ T.walkVertices v (T.forestPath v (topOf W₁)) :=
              (mem_walkVertices_ancestorPath_iff hT hvV (ht₁_anc v hv1)).mpr ⟨h10, ht₀_anc v hv0⟩
            rw [← List.mem_reverse, ← walkVertices_walkRev
              (forestPath_isPath hT.isForest (hT.connected hvV ht₁V)).1,
              ← forestPath_rev hT.isForest (hT.connected hvV ht₁V)] at hmem_rev
            exact (hPC W₁ hW₁).2.2 _ ht₁_mem v hv1 (topOf W₀) hmem_rev
        obtain ⟨⟨e, he⟩, hsub0⟩ := pathConvex_edges_between_mem hT.isForest (hPC W₀ hW₀) hconn0
          ht₀_mem hv0 (Ne.symm hvt₀)
        have hsub1 := (pathConvex_edges_between_mem hT.isForest (hPC W₁ hW₁) hconn1
          ht₀_in_W₁ hv1 (Ne.symm hvt₀)).2
        exact Finset.disjoint_left.mp (hdisj W₀ hW₀ W₁ hW₁ hneW.symm) (hsub0 he) (hsub1 he)
      have hb_sub : boundary 𝒲 ⊆ insert (topOf W₀) (boundary (𝒲.erase W₀)) := by
        intro v hv
        rw [Finset.mem_insert]
        by_cases hv_top : v = topOf W₀
        · exact Or.inl hv_top
        · right
          rw [mem_boundary_iff] at hv ⊢
          obtain ⟨A, hA, B, hB, hneAB, hvA, hvB⟩ := hv
          have hA_ne : A ≠ W₀ := fun hEq => hv_top (h_only_top B hB (hEq ▸ hneAB.symm) v (hEq ▸ hvA) hvB)
          have hB_ne : B ≠ W₀ := fun hEq => hv_top (h_only_top A hA (hEq ▸ hneAB) v (hEq ▸ hvB) hvA)
          exact ⟨A, Finset.mem_erase.mpr ⟨hA_ne, hA⟩, B, Finset.mem_erase.mpr ⟨hB_ne, hB⟩, hneAB, hvA, hvB⟩
      have h_erase_ne : (𝒲.erase W₀).Nonempty := by
        have hpos : 0 < (𝒲.erase W₀).card := by
          rw [Finset.card_erase_of_mem hW₀]; omega
        exact Finset.card_pos.mp hpos
      have hih := ih (𝒲.erase W₀) (by rw [Finset.card_erase_of_mem hW₀, hn]; omega) h_erase_ne
        (fun W hW => hPC W (Finset.erase_subset _ _ hW))
        (fun A hA B hB hne' => hdisj A (Finset.erase_subset _ _ hA) B (Finset.erase_subset _ _ hB) hne')
      have hcard_le := (Finset.card_le_card hb_sub).trans (Finset.card_insert_le _ _)
      rw [Finset.card_erase_of_mem hW₀] at hih
      omega

/-! ## Greedy list batching -/

/-- Partition `rest` into batches whose `f`-sum lies in `[θ, 3 * θ)` and a remainder `< θ`. -/
noncomputable def greedyGroupAux {α : Type*} (θ : ℝ) (f : α → ℝ)
    (acc : List α) (cur : ℝ) : List α → List (List α) × List α
  | [] => ([], acc)
  | x :: xs =>
    let acc' := x :: acc
    let cur' := cur + f x
    if θ ≤ cur' then
      let res := greedyGroupAux θ f [] 0 xs
      (acc' :: res.1, res.2)
    else
      greedyGroupAux θ f acc' cur' xs

private lemma greedyGroupAux_spec {α : Type*} (θ : ℝ) (f : α → ℝ) (hθ : 0 < θ) :
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

private lemma child_ne_root {T : MGraph} {r u c : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hc : c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u)) :
    c ≠ r := by
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc
  intro hEq
  have hanc := (mem_subtree_iff.mp hc.1.1).2
  rw [hEq] at hanc
  exact hc.1.2 (hEq.trans (isAncestor_antisymm hT hT.2 hu (isAncestor_root hT hu) hanc))

private lemma children_subtree_disjoint {T : MGraph} {r u c₁ c₂ : ℕ} (hT : IsRootedTree T r)
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

private lemma mem_subtree_children_iff {T : MGraph} {r u x : ℕ} (hT : IsRootedTree T r)
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

private lemma pathConvex_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
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

private lemma inducedEdges_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
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

private lemma list_flatten_nodup_pairwise_disjoint :
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

private lemma list_flatten_nodup_mem {a : List ℕ} {ls : List (List ℕ)}
    (hnd : ls.flatten.Nodup) (ha : a ∈ ls) : a.Nodup := by
  induction ls with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hnd.1
    · exact ih hnd.2.1 ha'

private lemma list_sum_map_eq_sum_flatten (f : ℕ → ℝ) :
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

private lemma subtree_child_subset {T : MGraph} {r u c : ℕ} (hT : IsRootedTree T r)
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

private lemma subtree_eq_insert_biUnion {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
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

private lemma list_len_mul_le_sum (θ : ℝ) (f : ℕ → ℝ) :
    ∀ ls : List (List ℕ), (∀ b ∈ ls, θ ≤ (b.map f).sum) →
      θ * (ls.length : ℝ) ≤ (ls.map (fun b => (b.map f).sum)).sum
  | [], _ => by simp
  | b :: bs, h => by
    have hb := h b List.mem_cons_self
    have ih := list_len_mul_le_sum θ f bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
    linarith

lemma treeDecompSub {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (ν : ℕ → ℝ) (hν : ∀ v ∈ T.V, 0 ≤ ν v) (θ : ℝ) (hθ : 0 < θ) (hν_le : ∀ v ∈ T.V, ν v ≤ θ) :
    ∀ n u, (subtree T r u).card ≤ n → u ∈ T.V →
      ∃ 𝒲_u : Finset (Finset ℕ), ∃ B_u : Finset ℕ,
        PathConvex T B_u ∧ u ∈ B_u ∧ B_u ⊆ subtree T r u ∧
        (∑ x ∈ B_u, ν x < 2 * θ) ∧
        (∀ P ∈ 𝒲_u, PathConvex T P ∧ P ⊆ subtree T r u ∧
          (inducedEdges T P).Nonempty ∧ (∑ x ∈ P, ν x < 4 * θ)) ∧
        (∀ P₁ ∈ 𝒲_u, ∀ P₂ ∈ 𝒲_u, P₁ ≠ P₂ → Disjoint (inducedEdges T P₁) (inducedEdges T P₂)) ∧
        (∀ P ∈ 𝒲_u, Disjoint (inducedEdges T P) (inducedEdges T B_u)) ∧
        (𝒲_u.biUnion (inducedEdges T) ∪ inducedEdges T B_u = inducedEdges T (subtree T r u)) ∧
        (θ * (𝒲_u.card : ℝ) ≤ ∑ x ∈ subtree T r u \ B_u, ν x) := by
  classical
  intro n
  induction n with
  | zero =>
    intro u hcard hu
    exfalso
    have hmem : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    have hpos : 0 < (subtree T r u).card := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  | succ k ih =>
    intro u hcard hu
    let C := (subtree T r u \ {u}).filter (fun c => parent T r c = u)
    have hC_sub : ∀ c ∈ C, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) :=
      fun _ hc => hc
    have hC_lt : ∀ c ∈ C, (subtree T r c).card ≤ k := by
      intro c hc
      have hsub := subtree_child_subset hT hc
      have hle := Finset.card_le_card hsub
      have humem : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem humem] at hle
      omega
    have hchild : ∀ c (_ : c ∈ C), ∃ (𝒲_c : Finset (Finset ℕ)) (B_c : Finset ℕ),
        PathConvex T B_c ∧ c ∈ B_c ∧ B_c ⊆ subtree T r c ∧
        (∑ x ∈ B_c, ν x < 2 * θ) ∧
        (∀ P ∈ 𝒲_c, PathConvex T P ∧ P ⊆ subtree T r c ∧
          (inducedEdges T P).Nonempty ∧ (∑ x ∈ P, ν x < 4 * θ)) ∧
        (∀ P₁ ∈ 𝒲_c, ∀ P₂ ∈ 𝒲_c, P₁ ≠ P₂ → Disjoint (inducedEdges T P₁) (inducedEdges T P₂)) ∧
        (∀ P ∈ 𝒲_c, Disjoint (inducedEdges T P) (inducedEdges T B_c)) ∧
        (𝒲_c.biUnion (inducedEdges T) ∪ inducedEdges T B_c = inducedEdges T (subtree T r c)) ∧
        (θ * (𝒲_c.card : ℝ) ≤ ∑ x ∈ subtree T r c \ B_c, ν x) := by
      intro c hc
      have hcV := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).1).1
      exact ih c (hC_lt c hc) hcV
    let Wc : ℕ → Finset (Finset ℕ) := fun c => if hc : c ∈ C then (hchild c hc).choose else ∅
    let Bc : ℕ → Finset ℕ := fun c => if hc : c ∈ C then (hchild c hc).choose_spec.choose else ∅
    have hBc_spec : ∀ c (hc : c ∈ C),
        PathConvex T (Bc c) ∧ c ∈ Bc c ∧ Bc c ⊆ subtree T r c ∧
        (∑ x ∈ Bc c, ν x < 2 * θ) ∧
        (∀ P ∈ Wc c, PathConvex T P ∧ P ⊆ subtree T r c ∧
          (inducedEdges T P).Nonempty ∧ (∑ x ∈ P, ν x < 4 * θ)) ∧
        (∀ P₁ ∈ Wc c, ∀ P₂ ∈ Wc c, P₁ ≠ P₂ → Disjoint (inducedEdges T P₁) (inducedEdges T P₂)) ∧
        (∀ P ∈ Wc c, Disjoint (inducedEdges T P) (inducedEdges T (Bc c))) ∧
        ((Wc c).biUnion (inducedEdges T) ∪ inducedEdges T (Bc c) = inducedEdges T (subtree T r c)) ∧
        (θ * ((Wc c).card : ℝ) ≤ ∑ x ∈ subtree T r c \ Bc c, ν x) := by
      intro c hc
      have hW_eq : Wc c = (hchild c hc).choose := dite_eq_left_of_eq_true (eq_true hc)
      have hB_eq : Bc c = (hchild c hc).choose_spec.choose := dite_eq_left_of_eq_true (eq_true hc)
      rw [hW_eq, hB_eq]
      exact (hchild c hc).choose_spec.choose_spec
    let f : ℕ → ℝ := fun c => ∑ x ∈ Bc c, ν x
    let L := C.toList
    have hf_range : ∀ c ∈ L, 0 ≤ f c ∧ f c < 2 * θ := by
      intro c hc
      have hcC := Finset.mem_toList.mp hc
      have hspec := hBc_spec c hcC
      refine ⟨Finset.sum_nonneg (fun x hx => hν x (mem_subtree_iff.mp (hspec.2.2.1 hx)).1),
        hspec.2.2.2.1⟩
    let res := greedyGroupAux θ f [] 0 L
    have hres := greedyGroupAux_spec θ f hθ L [] 0 le_rfl hθ rfl (by simp) hf_range
    rcases hres with ⟨hperm, hbatches, hrem_sum, _⟩
    dsimp only [List.nil_append] at hperm hbatches hrem_sum
    have hall_nodup : (res.1.flatten ++ res.2).Nodup := hperm.nodup_iff.mp C.nodup_toList
    have hflat_nodup : res.1.flatten.Nodup := (List.nodup_append.mp hall_nodup).1
    have hrem_nodup : res.2.Nodup := (List.nodup_append.mp hall_nodup).2.1
    have hflat_disj_rem : Disjoint res.1.flatten.toFinset res.2.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (List.nodup_append.mp hall_nodup).2.2 x (List.mem_toFinset.mp hx1)
        x (List.mem_toFinset.mp hx2) rfl
    have hbatch_sub_C : ∀ b ∈ res.1, b.toFinset ⊆ C := by
      intro b hb c hc
      exact Finset.mem_toList.mp (hperm.symm.subset (List.mem_append_left _
        (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp hc⟩)))
    have hrem_sub_C : res.2.toFinset ⊆ C := by
      intro c hc
      exact Finset.mem_toList.mp (hperm.symm.subset (List.mem_append_right _ (List.mem_toFinset.mp hc)))
    have hdisj_children : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
        Disjoint (subtree T r c₁) (subtree T r c₂) := by
      intro c₁ hc₁ c₂ hc₂ hne
      have hf₁ := hc₁; have hf₂ := hc₂
      have hcr₁ := child_ne_root hT hu hf₁; have hcr₂ := child_ne_root hT hu hf₂
      rw [Finset.mem_filter, Finset.mem_sdiff] at hf₁ hf₂
      exact children_subtree_disjoint hT (mem_subtree_iff.mp hf₁.1.1).1
        (mem_subtree_iff.mp hf₂.1.1).1 hcr₁ hcr₂ hf₁.2 hf₂.2 hne
    have hu_not_Bc : ∀ {c : ℕ}, c ∈ C → u ∉ Bc c := by
      intro c hc huB
      exact (Finset.mem_sdiff.mp (subtree_child_subset hT hc ((hBc_spec c hc).2.2.1 huB))).2
        (Finset.mem_singleton_self u)
    have hBc_disj : ∀ {c₁ c₂ : ℕ}, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ → Disjoint (Bc c₁) (Bc c₂) :=
      fun hc₁ hc₂ hne => Finset.disjoint_of_subset_left (hBc_spec _ hc₁).2.2.1
        (Finset.disjoint_of_subset_right (hBc_spec _ hc₂).2.2.1 (hdisj_children _ hc₁ _ hc₂ hne))
    have h_insert_disj : ∀ (S₁ S₂ : Finset ℕ), S₁ ⊆ C → S₂ ⊆ C → Disjoint S₁ S₂ →
        Disjoint (inducedEdges T (insert u (S₁.biUnion Bc)))
          (inducedEdges T (insert u (S₂.biUnion Bc))) := by
      intro S₁ S₂ hS₁ hS₂ hSdisj
      have hE₁ := inducedEdges_insert_biUnion hT hu S₁ Bc (fun c hc => hC_sub c (hS₁ hc))
        (fun c hc => ⟨(hBc_spec c (hS₁ hc)).2.1, (hBc_spec c (hS₁ hc)).2.2.1⟩)
      have hE₂ := inducedEdges_insert_biUnion hT hu S₂ Bc (fun c hc => hC_sub c (hS₂ hc))
        (fun c hc => ⟨(hBc_spec c (hS₂ hc)).2.1, (hBc_spec c (hS₂ hc)).2.2.1⟩)
      rw [hE₁, hE₂, Finset.disjoint_left]
      intro e he₁ he₂
      have h_pe_not_in_biUnion : ∀ (S : Finset ℕ), S ⊆ C → ∀ c ∈ C,
          parentEdge T r c ∉ S.biUnion (fun c' => inducedEdges T (Bc c')) := by
        intro S hS c hc hmem
        rw [Finset.mem_biUnion] at hmem
        obtain ⟨c', hc'S, hfe⟩ := hmem
        have hcV := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).1).1
        have hcr := child_ne_root hT hu hc
        have hpar : parent T r c = u := (Finset.mem_filter.mp hc).2
        have hend := parentEdge_endpoints hT hcV hcr
        have h_u_mem : u ∈ ({T.tail (parentEdge T r c), T.head (parentEdge T r c)} : Set ℕ) := by
          rw [hend, hpar]; exact Set.mem_insert_of_mem _ (Set.mem_singleton u)
        rw [inducedEdges, Finset.mem_filter] at hfe
        have huB : u ∈ Bc c' := by
          rcases h_u_mem with h1 | h1
          · exact h1 ▸ hfe.2.1
          · exact (Set.mem_singleton_iff.mp h1) ▸ hfe.2.2
        exact hu_not_Bc (hS hc'S) huB
      rw [Finset.mem_union, Finset.mem_image] at he₁ he₂
      rcases he₁ with ⟨c₁, hc₁, rfl⟩ | he₁_sub <;> rcases he₂ with ⟨c₂, hc₂, hpe⟩ | he₂_sub
      · have hc₁V := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS₁ hc₁)).1).1).1
        have hc₂V := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS₂ hc₂)).1).1).1
        have heq := parentEdge_inj hT hc₁V hc₂V (child_ne_root hT hu (hS₁ hc₁))
          (child_ne_root hT hu (hS₂ hc₂)) hpe.symm
        exact Finset.disjoint_left.mp hSdisj hc₁ (heq ▸ hc₂)
      · exact h_pe_not_in_biUnion S₂ hS₂ c₁ (hS₁ hc₁) he₂_sub
      · rw [← hpe] at he₁_sub
        exact h_pe_not_in_biUnion S₁ hS₁ c₂ (hS₂ hc₂) he₁_sub
      · rw [Finset.mem_biUnion] at he₁_sub he₂_sub
        obtain ⟨c₁, hc₁, hf₁⟩ := he₁_sub
        obtain ⟨c₂, hc₂, hf₂⟩ := he₂_sub
        have hne : c₁ ≠ c₂ := fun hEq => Finset.disjoint_left.mp hSdisj hc₁ (hEq ▸ hc₂)
        rw [inducedEdges, Finset.mem_filter] at hf₁ hf₂
        exact Finset.disjoint_left.mp (hBc_disj (hS₁ hc₁) (hS₂ hc₂) hne) hf₁.2.1 hf₂.2.1
    have h_child_disj : ∀ (S : Finset ℕ), S ⊆ C → ∀ c₀ ∈ C, ∀ Q ∈ Wc c₀,
        Disjoint (inducedEdges T Q) (inducedEdges T (insert u (S.biUnion Bc))) := by
      intro S hS c₀ hc₀ Q hQ
      have hQ_spec := (hBc_spec c₀ hc₀).2.2.2.2.1 Q hQ
      have hE := inducedEdges_insert_biUnion hT hu S Bc (fun c hc => hC_sub c (hS hc))
        (fun c hc => ⟨(hBc_spec c (hS hc)).2.1, (hBc_spec c (hS hc)).2.2.1⟩)
      rw [hE, Finset.disjoint_left]
      intro e heQ heI
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at heI
      rcases heI with ⟨c, hc, rfl⟩ | ⟨c, hc, heBc⟩
      · have hcV := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS hc)).1).1).1
        have hend := parentEdge_endpoints hT hcV (child_ne_root hT hu (hS hc))
        have h_u_mem : u ∈ ({T.tail (parentEdge T r c), T.head (parentEdge T r c)} : Set ℕ) := by
          rw [hend, (Finset.mem_filter.mp (hS hc)).2]; exact Set.mem_insert_of_mem _ (Set.mem_singleton u)
        rw [inducedEdges, Finset.mem_filter] at heQ
        have huQ : u ∈ Q := by
          rcases h_u_mem with h1 | h1
          · exact h1 ▸ heQ.2.1
          · exact (Set.mem_singleton_iff.mp h1) ▸ heQ.2.2
        exact (Finset.mem_sdiff.mp (subtree_child_subset hT hc₀ (hQ_spec.2.1 huQ))).2
          (Finset.mem_singleton_self u)
      · by_cases heq : c = c₀
        · subst heq
          exact Finset.disjoint_left.mp ((hBc_spec c hc₀).2.2.2.2.2.2.1 Q hQ) heQ heBc
        · rw [inducedEdges, Finset.mem_filter] at heQ heBc
          exact Finset.disjoint_left.mp (hdisj_children c₀ hc₀ c (hS hc) (Ne.symm heq))
            (hQ_spec.2.1 heQ.2.1) ((hBc_spec c (hS hc)).2.2.1 heBc.2.1)
    let batchPiece : List ℕ → Finset ℕ := fun b => insert u (b.toFinset.biUnion Bc)
    let batchesPieces := res.1.toFinset.image batchPiece
    let childPieces := C.biUnion Wc
    let 𝒲_u := childPieces ∪ batchesPieces
    let B_u := insert u (res.2.toFinset.biUnion Bc)
    have hBu_sub : B_u ⊆ subtree T r u := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_biUnion] at hx
      rcases hx with hEq | ⟨c, hc, hxc⟩
      · rw [hEq]
        exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
      · exact Finset.sdiff_subset (subtree_child_subset hT (hrem_sub_C hc) ((hBc_spec c (hrem_sub_C hc)).2.2.1 hxc))
    refine ⟨𝒲_u, B_u, ?_, Finset.mem_insert_self _ _, hBu_sub, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact pathConvex_insert_biUnion hT hu res.2.toFinset Bc (fun c hc => hC_sub c (hrem_sub_C hc))
        (fun c hc => ⟨(hBc_spec c (hrem_sub_C hc)).2.1, (hBc_spec c (hrem_sub_C hc)).2.2.1⟩)
        (fun c hc => (hBc_spec c (hrem_sub_C hc)).1)
    · have hu_not_rem : u ∉ res.2.toFinset.biUnion Bc := by
        rw [Finset.mem_biUnion]; rintro ⟨c, hc, huB⟩
        exact hu_not_Bc (hrem_sub_C hc) huB
      have hdisj_rem : Set.PairwiseDisjoint (↑res.2.toFinset : Set ℕ) Bc := by
        intro c₁ hc₁ c₂ hc₂ hne
        exact hBc_disj (hrem_sub_C hc₁) (hrem_sub_C hc₂) hne
      rw [Finset.sum_insert hu_not_rem, Finset.sum_biUnion hdisj_rem]
      have hsum_rem : (∑ c ∈ res.2.toFinset, ∑ x ∈ Bc c, ν x) = (res.2.map f).sum :=
        List.sum_toFinset f hrem_nodup
      rw [hsum_rem]
      have := hν_le u hu
      linarith
    · intro P hP
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
      rcases hP with ⟨c, hc, hPQ⟩ | ⟨b, hb, rfl⟩
      · have hPs := (hBc_spec c hc).2.2.2.2.1 P hPQ
        exact ⟨hPs.1, Finset.Subset.trans hPs.2.1 (Finset.Subset.trans (subtree_child_subset hT hc) Finset.sdiff_subset),
          hPs.2.2.1, hPs.2.2.2⟩
      · have hbL := List.mem_toFinset.mp hb
        have hbS := hbatch_sub_C b hbL
        have hhb := hbatches b hbL
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact pathConvex_insert_biUnion hT hu b.toFinset Bc (fun c hc => hC_sub c (hbS hc))
            (fun c hc => ⟨(hBc_spec c (hbS hc)).2.1, (hBc_spec c (hbS hc)).2.2.1⟩)
            (fun c hc => (hBc_spec c (hbS hc)).1)
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_biUnion] at hx
          rcases hx with hEq | ⟨c, hc, hxc⟩
          · rw [hEq]
            exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
          · exact Finset.sdiff_subset (subtree_child_subset hT (hbS hc) ((hBc_spec c (hbS hc)).2.2.1 hxc))
        · obtain ⟨c, hc_mem⟩ := List.exists_mem_of_ne_nil b hhb.1
          have hE := inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c hc => hC_sub c (hbS hc))
            (fun c hc => ⟨(hBc_spec c (hbS hc)).2.1, (hBc_spec c (hbS hc)).2.2.1⟩)
          rw [hE]
          exact ⟨parentEdge T r c, Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hc_mem))⟩
        · have hu_not_b : u ∉ b.toFinset.biUnion Bc := by
            rw [Finset.mem_biUnion]; rintro ⟨c, hc, huB⟩
            exact hu_not_Bc (hbS hc) huB
          have hdisj_b : Set.PairwiseDisjoint (↑b.toFinset : Set ℕ) Bc :=
            fun c₁ hc₁ c₂ hc₂ hne => hBc_disj (hbS hc₁) (hbS hc₂) hne
          rw [Finset.sum_insert hu_not_b, Finset.sum_biUnion hdisj_b]
          have hsum_b : (∑ c ∈ b.toFinset, ∑ x ∈ Bc c, ν x) = (b.map f).sum :=
            List.sum_toFinset f (list_flatten_nodup_mem hflat_nodup hbL)
          rw [hsum_b]
          have := hν_le u hu
          linarith [hhb.2.2.1]
    · intro P₁ hP₁ P₂ hP₂ hne
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP₁ hP₂
      rcases hP₁ with ⟨c₁, hc₁, h1⟩ | ⟨b₁, hb₁, rfl⟩ <;>
        rcases hP₂ with ⟨c₂, hc₂, h2⟩ | ⟨b₂, hb₂, rfl⟩
      · by_cases hEq : c₁ = c₂
        · subst hEq; exact (hBc_spec c₁ hc₁).2.2.2.2.2.1 P₁ h1 P₂ h2 hne
        · have hs₁ := (hBc_spec c₁ hc₁).2.2.2.2.1 P₁ h1
          have hs₂ := (hBc_spec c₂ hc₂).2.2.2.2.1 P₂ h2
          rw [Finset.disjoint_left]
          intro e he₁ he₂
          rw [inducedEdges, Finset.mem_filter] at he₁ he₂
          exact Finset.disjoint_left.mp (hdisj_children c₁ hc₁ c₂ hc₂ hEq)
            (hs₁.2.1 he₁.2.1) (hs₂.2.1 he₂.2.1)
      · exact h_child_disj b₂.toFinset (hbatch_sub_C b₂ (List.mem_toFinset.mp hb₂)) c₁ hc₁ P₁ h1
      · exact (h_child_disj b₁.toFinset (hbatch_sub_C b₁ (List.mem_toFinset.mp hb₁)) c₂ hc₂ P₂ h2).symm
      · have hne_b : b₁ ≠ b₂ := fun hEq => hne (by rw [hEq])
        have hb₁L := List.mem_toFinset.mp hb₁
        have hb₂L := List.mem_toFinset.mp hb₂
        exact h_insert_disj b₁.toFinset b₂.toFinset (hbatch_sub_C b₁ hb₁L) (hbatch_sub_C b₂ hb₂L)
          (list_flatten_nodup_pairwise_disjoint res.1 hflat_nodup b₁ hb₁L b₂ hb₂L hne_b)
    · intro P hP
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
      rcases hP with ⟨c, hc, hQ⟩ | ⟨b, hb, rfl⟩
      · exact h_child_disj res.2.toFinset hrem_sub_C c hc P hQ
      · have hbL := List.mem_toFinset.mp hb
        have hdisj_br : Disjoint b.toFinset res.2.toFinset := by
          rw [Finset.disjoint_left]
          intro c hc1 hc2
          exact Finset.disjoint_left.mp hflat_disj_rem
            (List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨b, hbL, List.mem_toFinset.mp hc1⟩)) hc2
        exact h_insert_disj b.toFinset res.2.toFinset (hbatch_sub_C b hbL) hrem_sub_C hdisj_br
    · apply Finset.Subset.antisymm
      · rw [Finset.union_subset_iff]
        constructor
        · rw [Finset.biUnion_subset_iff_forall_subset]
          intro P hP
          have hsub : P ⊆ subtree T r u := by
            rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
            rcases hP with ⟨c, hc, hQ⟩ | ⟨b, hb, rfl⟩
            · exact Finset.Subset.trans ((hBc_spec c hc).2.2.2.2.1 P hQ).2.1
                (Finset.Subset.trans (subtree_child_subset hT hc) Finset.sdiff_subset)
            · intro x hx
              rw [Finset.mem_insert, Finset.mem_biUnion] at hx
              rcases hx with hEq | ⟨c, hc, hxc⟩
              · rw [hEq]
                exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
              · exact Finset.sdiff_subset (subtree_child_subset hT
                  (hbatch_sub_C b (List.mem_toFinset.mp hb) hc)
                  ((hBc_spec c (hbatch_sub_C b (List.mem_toFinset.mp hb) hc)).2.2.1 hxc))
          intro e he
          rw [inducedEdges, Finset.mem_filter] at he ⊢
          exact ⟨he.1, hsub he.2.1, hsub he.2.2⟩
        · intro e he
          rw [inducedEdges, Finset.mem_filter] at he ⊢
          exact ⟨he.1, hBu_sub he.2.1, hBu_sub he.2.2⟩
      · intro e he
        rw [subtree_eq_insert_biUnion hT hu, inducedEdges_insert_biUnion hT hu C (subtree T r)
          hC_sub (fun c hc => ⟨mem_subtree_iff.mpr ⟨(mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).1).1, isAncestor_refl T r c⟩, Finset.Subset.refl _⟩),
          Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at he
        have hc_part : ∀ c ∈ C, (∃ b ∈ res.1, c ∈ b.toFinset) ∨ c ∈ res.2.toFinset := by
          intro c hc
          have hmem := hperm.subset (Finset.mem_toList.mpr hc)
          rw [List.mem_append] at hmem
          rcases hmem with hf | hr
          · obtain ⟨b, hb, hcb⟩ := List.mem_flatten.mp hf
            exact Or.inl ⟨b, hb, List.mem_toFinset.mpr hcb⟩
          · exact Or.inr (List.mem_toFinset.mpr hr)
        rcases he with ⟨c, hc, rfl⟩ | ⟨c, hc, hec⟩
        · rcases hc_part c hc with ⟨b, hb, hcb⟩ | hcr
          · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨batchPiece b,
              Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)), ?_⟩)
            rw [inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c' hc' => hC_sub c' (hbatch_sub_C b hb hc'))
              (fun c' hc' => ⟨(hBc_spec c' (hbatch_sub_C b hb hc')).2.1, (hBc_spec c' (hbatch_sub_C b hb hc')).2.2.1⟩)]
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcb)
          · refine Finset.mem_union_right _ ?_
            rw [inducedEdges_insert_biUnion hT hu res.2.toFinset Bc (fun c' hc' => hC_sub c' (hrem_sub_C hc'))
              (fun c' hc' => ⟨(hBc_spec c' (hrem_sub_C hc')).2.1, (hBc_spec c' (hrem_sub_C hc')).2.2.1⟩)]
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcr)
        · rw [← (hBc_spec c hc).2.2.2.2.2.2.2.1, Finset.mem_union, Finset.mem_biUnion] at hec
          rcases hec with ⟨Q, hQ, heQ⟩ | heB
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨Q,
              Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, hc, hQ⟩), heQ⟩)
          · rcases hc_part c hc with ⟨b, hb, hcb⟩ | hcr
            · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨batchPiece b,
                Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)), ?_⟩)
              rw [inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c' hc' => hC_sub c' (hbatch_sub_C b hb hc'))
                (fun c' hc' => ⟨(hBc_spec c' (hbatch_sub_C b hb hc')).2.1, (hBc_spec c' (hbatch_sub_C b hb hc')).2.2.1⟩)]
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcb, heB⟩)
            · refine Finset.mem_union_right _ ?_
              rw [inducedEdges_insert_biUnion hT hu res.2.toFinset Bc (fun c' hc' => hC_sub c' (hrem_sub_C hc'))
                (fun c' hc' => ⟨(hBc_spec c' (hrem_sub_C hc')).2.1, (hBc_spec c' (hrem_sub_C hc')).2.2.1⟩)]
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcr, heB⟩)
    · have hcard_W : (𝒲_u.card : ℝ) ≤ (∑ c ∈ C, ((Wc c).card : ℝ)) + (res.1.length : ℝ) := by
        have h1 : 𝒲_u.card ≤ childPieces.card + batchesPieces.card := Finset.card_union_le _ _
        have h2 : childPieces.card ≤ ∑ c ∈ C, (Wc c).card := Finset.card_biUnion_le
        have h3 : batchesPieces.card ≤ res.1.toFinset.card := Finset.card_image_le
        have h4 : res.1.toFinset.card ≤ res.1.length := List.toFinset_card_le res.1
        have hnat : 𝒲_u.card ≤ (∑ c ∈ C, (Wc c).card) + res.1.length := by omega
        exact_mod_cast (by simpa only [Nat.cast_add, Nat.cast_sum] using hnat)
      have h_batches_theta : θ * (res.1.length : ℝ) ≤ ∑ c ∈ res.1.flatten.toFinset, f c := by
        have h1 := list_len_mul_le_sum θ f res.1 (fun b hb => (hbatches b hb).2.1)
        rwa [list_sum_map_eq_sum_flatten f res.1 hflat_nodup] at h1
      have h_children_theta : ∑ c ∈ C, θ * ((Wc c).card : ℝ) ≤ ∑ c ∈ C, ∑ x ∈ subtree T r c \ Bc c, ν x :=
        Finset.sum_le_sum (fun c hc => (hBc_spec c hc).2.2.2.2.2.2.2.2)
      have h_flat_sub_C : res.1.flatten.toFinset ⊆ C := by
        intro c hc
        exact Finset.mem_toList.mp (hperm.symm.subset (List.mem_append_left _ (List.mem_toFinset.mp hc)))
      have hC_eq_union : C = res.1.flatten.toFinset ∪ res.2.toFinset := by
        apply Finset.ext
        intro c
        rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset, ← Finset.mem_toList]
        exact ⟨fun hc => List.mem_append.mp (hperm.subset hc),
          fun hc => hperm.symm.subset (List.mem_append.mpr hc)⟩
      have h_lhs_le : θ * (𝒲_u.card : ℝ) ≤
          (∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c, ν x) +
            (∑ c ∈ res.2.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) := by
        have hmul : θ * (𝒲_u.card : ℝ) ≤
            (∑ c ∈ C, θ * ((Wc c).card : ℝ)) + θ * (res.1.length : ℝ) := by
          have := mul_le_mul_of_nonneg_left hcard_W (le_of_lt hθ)
          rwa [mul_add, Finset.mul_sum] at this
        have hC_sum : ∑ c ∈ C, ∑ x ∈ subtree T r c \ Bc c, ν x =
            (∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) +
              (∑ c ∈ res.2.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) := by
          rw [hC_eq_union, Finset.sum_union hflat_disj_rem]
        have h_combine : ∑ c ∈ res.1.flatten.toFinset, ((∑ x ∈ subtree T r c \ Bc c, ν x) + ∑ x ∈ Bc c, ν x) =
            ∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c, ν x :=
          Finset.sum_congr rfl (fun c hc =>
            Finset.sum_sdiff (hBc_spec c (h_flat_sub_C hc)).2.2.1)
        rw [← h_combine, Finset.sum_add_distrib]
        dsimp only [f] at h_batches_theta
        linarith
      have h_sub_diff : subtree T r u \ B_u =
          (res.1.flatten.toFinset.biUnion (subtree T r)) ∪
            (res.2.toFinset.biUnion (fun c => subtree T r c \ Bc c)) := by
        apply Finset.ext
        intro x
        rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
        constructor
        · rintro ⟨hx, hxBu⟩
          have hxu : x ≠ u := fun hEq => hxBu (hEq ▸ Finset.mem_insert_self _ _)
          obtain ⟨c, ⟨hcC, hxc⟩, _⟩ := mem_subtree_children_iff hT hu hx hxu
          have hmem : c ∈ res.1.flatten.toFinset ∪ res.2.toFinset := by
            rw [← hC_eq_union]; exact hcC
          rw [Finset.mem_union] at hmem
          rcases hmem with hf | hr
          · exact Or.inl ⟨c, hf, hxc⟩
          · refine Or.inr ⟨c, hr, Finset.mem_sdiff.mpr ⟨hxc, fun hxB => hxBu ?_⟩⟩
            exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, hr, hxB⟩)
        · rintro (⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩)
          · have hcC := h_flat_sub_C hc
            refine ⟨Finset.sdiff_subset (subtree_child_subset hT hcC hxc), fun hxBu => ?_⟩
            rw [Finset.mem_insert, Finset.mem_biUnion] at hxBu
            rcases hxBu with rfl | ⟨c', hc', hxB'⟩
            · exact (Finset.mem_sdiff.mp (subtree_child_subset hT hcC hxc)).2 (Finset.mem_singleton_self _)
            · have hne : c ≠ c' := fun hEq => Finset.disjoint_left.mp hflat_disj_rem hc (hEq ▸ hc')
              exact Finset.disjoint_left.mp (hdisj_children c hcC c' (hrem_sub_C hc') hne)
                hxc ((hBc_spec c' (hrem_sub_C hc')).2.2.1 hxB')
          · rw [Finset.mem_sdiff] at hxc
            have hcC := hrem_sub_C hc
            refine ⟨Finset.sdiff_subset (subtree_child_subset hT hcC hxc.1), fun hxBu => ?_⟩
            rw [Finset.mem_insert, Finset.mem_biUnion] at hxBu
            rcases hxBu with rfl | ⟨c', hc', hxB'⟩
            · exact (Finset.mem_sdiff.mp (subtree_child_subset hT hcC hxc.1)).2 (Finset.mem_singleton_self _)
            · by_cases hEq : c = c'
              · exact hxc.2 (hEq ▸ hxB')
              · exact Finset.disjoint_left.mp (hdisj_children c hcC c' (hrem_sub_C hc') hEq)
                  hxc.1 ((hBc_spec c' (hrem_sub_C hc')).2.2.1 hxB')
      have hdisj_part1 : Set.PairwiseDisjoint (↑res.1.flatten.toFinset : Set ℕ) (subtree T r) :=
        fun c₁ hc₁ c₂ hc₂ hne => hdisj_children c₁ (h_flat_sub_C hc₁) c₂ (h_flat_sub_C hc₂) hne
      have hdisj_part2 : Set.PairwiseDisjoint (↑res.2.toFinset : Set ℕ) (fun c => subtree T r c \ Bc c) :=
        fun c₁ hc₁ c₂ hc₂ hne =>
          Finset.disjoint_of_subset_left Finset.sdiff_subset
            (Finset.disjoint_of_subset_right Finset.sdiff_subset
              (hdisj_children c₁ (hrem_sub_C hc₁) c₂ (hrem_sub_C hc₂) hne))
      have hdisj_bi : Disjoint (res.1.flatten.toFinset.biUnion (subtree T r))
          (res.2.toFinset.biUnion (fun c => subtree T r c \ Bc c)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_biUnion] at hx1 hx2
        obtain ⟨c₁, hc₁, hx1⟩ := hx1
        obtain ⟨c₂, hc₂, hx2⟩ := hx2
        have hne : c₁ ≠ c₂ := fun hEq => Finset.disjoint_left.mp hflat_disj_rem hc₁ (hEq ▸ hc₂)
        exact Finset.disjoint_left.mp (hdisj_children c₁ (h_flat_sub_C hc₁) c₂ (hrem_sub_C hc₂) hne)
          hx1 (Finset.sdiff_subset hx2)
      rw [h_sub_diff, Finset.sum_union hdisj_bi, Finset.sum_biUnion hdisj_part1, Finset.sum_biUnion hdisj_part2]
      exact h_lhs_le

end MinCostFlow.LSF
