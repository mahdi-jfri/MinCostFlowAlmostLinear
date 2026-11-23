module

public import MinCostFlow.LSF.Program.DecompOnline

/-!
# What `progDecomp` is, in terms of the batch numbers

The program does not store bags or pieces. For every vertex `u` it stores the number `nb u` of
batches closed at `u`, for every non-root vertex `c` the number `bidx c` of the batch of its
parent that `c` joined, and the sum `s u` of the weights in the open bag of `u`. A child `c`
whose number is `nb (parent c)` was not put in a closed batch, so its bag was merged into the bag
of its parent.

From these numbers:
* the bag of `u` holds the vertices `x` below `u` such that every vertex strictly between `u` and
  `x`, and `x` itself if `x ≠ u`, was merged into its parent (`Merged`, `bagSet`);
* the pieces of `u` are the batch pieces `batchPiece y b` for the vertices `y` below `u` and
  `b < nb y`: `y` together with the bags of its children of number `b`.

`progDecomp_char` proves this by induction, when the numbers come from handling the children of
each vertex one at a time (`OnlineRun`). The step uses `greedy_online`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

/-- Every vertex from `x` up to `u`, `u` excluded, was merged into its parent. -/
def Merged (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (u x : ℕ) : Prop :=
  ∀ y, IsAncestor T r u y → y ≠ u → IsAncestor T r y x → bidx y = nb (parent T r y)

/-- The bag of `u`, read from the batch numbers. -/
noncomputable def bagSet (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  open Classical in (subtree T r u).filter (Merged T r bidx nb u)

/-- The piece of batch `b` at `y`: `y` and the bags of its children of number `b`. -/
noncomputable def batchPiece (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (y b : ℕ) : Finset ℕ :=
  open Classical in
  insert y (((childSet T r y).filter (fun c => bidx c = b)).biUnion (bagSet T r bidx nb))

lemma mem_childSet {T : MGraph} {r u c : ℕ} :
    c ∈ childSet T r u ↔ c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) := by
  classical
  rw [childSet]

lemma merged_self {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (bidx nb : ℕ → ℕ) {u : ℕ}
    (hu : u ∈ T.V) : Merged T r bidx nb u u := by
  intro y huy hyu hyx
  exact absurd (isAncestor_antisymm hT (isAncestor_mem hT hu hyx) hu hyx huy) hyu

/-- Going one step down from `u` to its child `c`. -/
lemma merged_child {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (bidx nb : ℕ → ℕ) {u c x : ℕ}
    (hu : u ∈ T.V) (hc : c ∈ childSet T r u) (hx : x ∈ subtree T r c) :
    Merged T r bidx nb u x ↔ bidx c = nb u ∧ Merged T r bidx nb c x := by
  have hc' := mem_childSet.mp hc
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc'
  obtain ⟨⟨hcsub, hcu⟩, hpar⟩ := hc'
  have hcV : c ∈ T.V := (mem_subtree_iff.mp hcsub).1
  have huc : IsAncestor T r u c := (mem_subtree_iff.mp hcsub).2
  have hxV : x ∈ T.V := (mem_subtree_iff.mp hx).1
  have hcx : IsAncestor T r c x := (mem_subtree_iff.mp hx).2
  constructor
  · intro h
    refine ⟨?_, fun y hcy hyc hyx => ?_⟩
    · rw [← hpar]; exact h c huc hcu hcx
    · have hyV := isAncestor_mem hT hxV hyx
      refine h y (isAncestor_trans hT hyV huc hcy) (fun hyu => ?_) hyx
      rw [hyu] at hcy
      exact hcu (isAncestor_antisymm hT hcV hu hcy huc)
  · rintro ⟨hb, h⟩ y huy hyu hyx
    have hyV := isAncestor_mem hT hxV hyx
    rcases isAncestor_total_on_ancestors hT hxV hcx hyx with hcy | hyc
    · by_cases hyc : y = c
      · rw [hyc, hpar]; exact hb
      · exact h y hcy hyc hyx
    · rcases (isAncestor_iff_eq_or_parent hT hcV).mp hyc with hEq | ⟨_, hyp⟩
      · rw [hEq, hpar]; exact hb
      · rw [hpar] at hyp
        exact absurd (isAncestor_antisymm hT hyV hu hyp huy) hyu

/-- `greedyGroupAux` only looks at `f` on the list. -/
lemma greedyGroupAux_congr {α : Type*} (θ : ℝ) {f g : α → ℝ} :
    ∀ (xs acc : List α) (cur : ℝ), (∀ x ∈ xs, f x = g x) →
      greedyGroupAux θ f acc cur xs = greedyGroupAux θ g acc cur xs := by
  intro xs
  induction xs with
  | nil => intro acc cur _; simp [greedyGroupAux]
  | cons x xs ih =>
    intro acc cur hfg
    have hx := hfg x List.mem_cons_self
    have hxs : ∀ y ∈ xs, f y = g y := fun y hy => hfg y (List.mem_cons_of_mem _ hy)
    unfold greedyGroupAux
    simp only [hx, ih [] 0 hxs, ih (x :: acc) (cur + g x) hxs]

/-- `greedyGroupAux` rearranges its input. -/
lemma greedyGroupAux_perm {α : Type*} (θ : ℝ) (f : α → ℝ) :
    ∀ (xs acc : List α) (cur : ℝ),
      (acc ++ xs).Perm ((greedyGroupAux θ f acc cur xs).1.flatten ++
        (greedyGroupAux θ f acc cur xs).2) := by
  intro xs
  induction xs with
  | nil => intro acc cur; simp [greedyGroupAux]
  | cons x xs ih =>
    intro acc cur
    unfold greedyGroupAux
    dsimp only
    split_ifs with hc
    · have h1 : (acc ++ x :: xs).Perm ((x :: acc) ++ xs) :=
        List.perm_middle (a := x) (l₁ := acc) (l₂ := xs)
      simpa only [List.flatten_cons, List.append_assoc] using
        h1.trans ((List.Perm.refl (x :: acc)).append (by simpa using ih [] 0))
    · exact (List.perm_middle (a := x) (l₁ := acc) (l₂ := xs)).trans (ih (x :: acc) (cur + f x))

/-- The bags and pieces of `progDecomp`, read from the batch numbers. -/
theorem progDecomp_char {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (ν : ℕ → ℝ) (θ : ℝ) {L : ℕ → List ℕ} (hL : IsChildLists T r L)
    (s : ℕ → ℝ) (bidx nb : ℕ → ℕ)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u)) :
    ∀ k u, u ∈ T.V → (subtree T r u).card ≤ k →
      (progDecomp ν θ L k u).2 = bagSet T r bidx nb u ∧
      ∑ x ∈ bagSet T r bidx nb u, ν x = s u ∧
      ∀ P, P ∈ (progDecomp ν θ L k u).1 ↔
        ∃ y ∈ subtree T r u, ∃ b < nb y, P = batchPiece T r bidx nb y b := by
  classical
  intro k
  induction k with
  | zero =>
    intro u hu hk
    have hmem : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    have := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  | succ k ih =>
    intro u hu hk
    rw [progDecomp_succ]
    have hu_sub : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    -- facts about the children
    have hchildC : ∀ c ∈ L u, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) :=
      fun c hc => mem_childSet.mp (((hL u hu).2 c).mp hc)
    have hcV : ∀ c ∈ L u, c ∈ T.V := fun c hc =>
      (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hchildC c hc)).1).1).1
    have hIH : ∀ c ∈ L u, (progDecomp ν θ L k c).2 = bagSet T r bidx nb c ∧
        ∑ x ∈ bagSet T r bidx nb c, ν x = s c ∧
        ∀ P, P ∈ (progDecomp ν θ L k c).1 ↔
          ∃ y ∈ subtree T r c, ∃ b < nb y, P = batchPiece T r bidx nb y b := by
      intro c hc
      have hsub := subtree_child_subset hT (hchildC c hc)
      have hlt : (subtree T r c).card < (subtree T r u).card := by
        refine Finset.card_lt_card ⟨fun x hx => Finset.sdiff_subset (hsub hx), fun h => ?_⟩
        have := hsub (h hu_sub)
        simp at this
      exact ih c (hcV c hc) (by omega)
    set Bc : ℕ → Finset ℕ := fun c => (progDecomp ν θ L k c).2 with hBc
    set Wc : ℕ → Finset (Finset ℕ) := fun c => (progDecomp ν θ L k c).1 with hWc
    -- the greedy batching
    have hgeq : stepGroups ν θ Bc (L u) = greedyGroupAux θ s [] 0 (L u) := by
      unfold stepGroups
      refine greedyGroupAux_congr θ _ _ _ (fun c hc => ?_)
      simp only [hBc, (hIH c hc).1, (hIH c hc).2.1]
    obtain ⟨hlen, hbat, hrest, hcur⟩ :=
      greedy_online θ s bidx (L u) [] 0 0 (nb u) (s u - ν u) (hrun u hu) (by simp) (by simp)
    simp only [List.not_mem_nil, false_or, Nat.zero_add] at hlen hbat hrest
    set G := greedyGroupAux θ s [] 0 (L u) with hG
    have hperm := greedyGroupAux_perm θ s (L u) [] 0
    rw [← hG, List.nil_append] at hperm
    have hrest_nd : G.2.Nodup := (List.nodup_append.mp (hperm.nodup_iff.mp (hL u hu).1)).2.1
    -- the bag
    have hbag : stepBag ν θ u Bc (L u) = bagSet T r bidx nb u := by
      unfold stepBag
      rw [hgeq]
      ext x
      rw [Finset.mem_insert, Finset.mem_biUnion, bagSet, Finset.mem_filter]
      constructor
      · rintro (rfl | ⟨c, hc, hxc⟩)
        · exact ⟨hu_sub, merged_self hT bidx nb hu⟩
        · rw [List.mem_toFinset, hrest] at hc
          have hxc' : x ∈ bagSet T r bidx nb c := by
            have := (hIH c hc.1).1; simp only [hBc] at hxc; rwa [this] at hxc
          rw [bagSet, Finset.mem_filter] at hxc'
          refine ⟨Finset.sdiff_subset (subtree_child_subset hT (hchildC c hc.1) hxc'.1), ?_⟩
          exact (merged_child hT bidx nb hu (((hL u hu).2 c).mp hc.1) hxc'.1).mpr
            ⟨hc.2, hxc'.2⟩
      · rintro ⟨hx, hm⟩
        by_cases hxu : x = u
        · exact Or.inl hxu
        · right
          obtain ⟨c, ⟨hc, hxc⟩, _⟩ := mem_subtree_children_iff hT hu hx hxu
          have hcL : c ∈ L u := ((hL u hu).2 c).mpr (mem_childSet.mpr hc)
          have hmc := (merged_child hT bidx nb hu (mem_childSet.mpr hc) hxc).mp hm
          refine ⟨c, by rw [List.mem_toFinset, hrest]; exact ⟨hcL, hmc.1⟩, ?_⟩
          simp only [hBc, (hIH c hcL).1, bagSet, Finset.mem_filter]
          exact ⟨hxc, hmc.2⟩
    refine ⟨hbag, ?_, ?_⟩
    · -- the sum over the bag
      rw [← hbag]
      unfold stepBag
      rw [hgeq]
      have hrest_C : ∀ c ∈ G.2.toFinset, c ∈ L u := fun c hc =>
        ((hrest c).mp (List.mem_toFinset.mp hc)).1
      have hu_not : u ∉ G.2.toFinset.biUnion Bc := by
        rw [Finset.mem_biUnion]
        rintro ⟨c, hc, huc⟩
        have hcL := hrest_C c hc
        simp only [hBc, (hIH c hcL).1, bagSet, Finset.mem_filter] at huc
        have := subtree_child_subset hT (hchildC c hcL) huc.1
        simp at this
      have hdisj : Set.PairwiseDisjoint (↑G.2.toFinset : Set ℕ) Bc := by
        intro c₁ hc₁ c₂ hc₂ hne
        have h1 := hrest_C c₁ hc₁
        have h2 := hrest_C c₂ hc₂
        have hf₁ := hchildC c₁ h1
        have hf₂ := hchildC c₂ h2
        have hcr₁ := child_ne_root hT hu hf₁
        have hcr₂ := child_ne_root hT hu hf₂
        rw [Finset.mem_filter, Finset.mem_sdiff] at hf₁ hf₂
        have hd := children_subtree_disjoint hT (hcV c₁ h1) (hcV c₂ h2) hcr₁ hcr₂ hf₁.2 hf₂.2 hne
        simp only [Function.onFun, hBc, (hIH c₁ h1).1, (hIH c₂ h2).1, bagSet]
        exact Finset.disjoint_filter_filter hd
      rw [Finset.sum_insert hu_not, Finset.sum_biUnion hdisj]
      have hsum : ∑ c ∈ G.2.toFinset, ∑ x ∈ Bc c, ν x = ∑ c ∈ G.2.toFinset, s c := by
        refine Finset.sum_congr rfl (fun c hc => ?_)
        have hcL := hrest_C c hc
        simp only [hBc, (hIH c hcL).1, (hIH c hcL).2.1]
      rw [hsum, List.sum_toFinset s hrest_nd, hcur]
      ring
    · -- the pieces
      intro P
      unfold stepPieces
      rw [hgeq]
      dsimp only
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
      have hbp : ∀ j < nb u, ∀ (hj : j < G.1.length),
          insert u (G.1[j].toFinset.biUnion Bc) = batchPiece T r bidx nb u j := by
        intro j _ hj
        rw [batchPiece]
        have hfs : G.1[j].toFinset = (childSet T r u).filter (fun c => bidx c = j) := by
          ext c
          rw [List.mem_toFinset, hbat j hj c, Finset.mem_filter, (hL u hu).2 c]
        rw [hfs]
        congr 1
        refine Finset.biUnion_congr rfl (fun c hc => ?_)
        have hcL : c ∈ L u := ((hL u hu).2 c).mpr (Finset.mem_filter.mp hc).1
        simp only [hBc, (hIH c hcL).1]
      constructor
      · rintro (⟨c, hc, hPc⟩ | ⟨bt, hbt, rfl⟩)
        · rw [List.mem_toFinset] at hc
          obtain ⟨y, hy, b, hb, rfl⟩ := ((hIH c hc).2.2 P).mp hPc
          exact ⟨y, Finset.sdiff_subset (subtree_child_subset hT (hchildC c hc) hy), b, hb, rfl⟩
        · rw [List.mem_toFinset] at hbt
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hbt
          exact ⟨u, hu_sub, j, by omega, hbp j (by omega) hj⟩
      · rintro ⟨y, hy, b, hb, rfl⟩
        by_cases hyu : y = u
        · subst hyu
          right
          have hj : b < G.1.length := by omega
          exact ⟨G.1[b], List.mem_toFinset.mpr (List.getElem_mem hj), hbp b hb hj⟩
        · left
          obtain ⟨c, ⟨hc, hyc⟩, _⟩ := mem_subtree_children_iff hT hu hy hyu
          have hcL : c ∈ L u := ((hL u hu).2 c).mpr (mem_childSet.mpr hc)
          exact ⟨c, List.mem_toFinset.mpr hcL, ((hIH c hcL).2.2 _).mpr ⟨y, hyc, b, hb, rfl⟩⟩

end MinCostFlow.LSF.Program.DecompGen
