module

public import MinCostFlow.MinRatio.PathTreeContract
import MinCostFlow.LinkCut.ForestExposeSpec

/-!
# Stability of the exposed edge record

Section 6 (pages 29–30) reads the edge found by Detect before
resetting it. The first exposure and the subsequent point read
identify the same payload because exposure preserves all evaluated
slot-value pairs of the forest.
-/

public section
namespace MinCostFlow.MinRatio
open LinkCut

private theorem forestKeys_perm (s : PathTreeState) (trees : List AuxTree) :
    ((forestPairs pathPayload s.splay trees).map Prod.fst).Perm (trees.flatMap AuxTree.toList) := by
  induction trees with
  | nil => simp [forestPairs]
  | cons t rest ih =>
    simp only [forestPairs, List.flatMap_cons, List.map_append]
    have ht : ((SplayState.evalPairs pathPayload s.splay t false pathPayload.idTag).map Prod.fst).Perm
        t.toList := by
      rw [SplayState.evalPairs_map_fst]
      exact t.evalInorder_perm _ _
    exact ht.append ih

private theorem pair_unique {α : Type} {xs : List (ℕ × α)}
    (hnd : (xs.map Prod.fst).Nodup) {x : ℕ} {a b : α}
    (ha : (x, a) ∈ xs) (hb : (x, b) ∈ xs) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons p rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with h₁ | h₁ <;> rcases List.mem_cons.mp hb with h₂ | h₂
    · exact congrArg Prod.snd (h₁.trans h₂.symm)
    · exact (hnd.1 (h₁ ▸ List.mem_map.mpr ⟨(x, b), h₂, rfl⟩)).elim
    · exact (hnd.1 (h₂ ▸ List.mem_map.mpr ⟨(x, a), h₁, rfl⟩)).elim
    · exact ih hnd.2 h₁ h₂

private theorem exposed_value_mem {s : PathTreeState} {trees : List AuxTree}
    {slot : ℕ} {left : AuxTree}
    (ht : AuxTree.node slot left .leaf ∈ trees)
    (hr : (s.splay.nodes slot).rev = false) (htag : (s.splay.nodes slot).tag = pathPayload.idTag) :
    (slot, (s.splay.nodes slot).val) ∈ forestPairs pathPayload s.splay trees := by
  apply List.mem_flatMap.mpr
  refine ⟨_, ht, ?_⟩
  rw [evalPairs_of_rev_false pathPayload_laws hr htag]
  simp

/-- Reading a slot already exposed by FindReady yields the same
payload. The second exposure also preserves the active slot. -/
theorem pathTree_expose_twice_value (s : PathTreeState) (slot : ℕ)
    (ha : pathTreeActive s slot) :
    let first := lctExpose pathPayload s slot
    let second := lctExpose pathPayload first slot
    pathTreeActive first slot ∧ pathTreeActive second slot ∧
      (second.splay.nodes slot).val = (first.splay.nodes slot).val := by
  dsimp only
  obtain ⟨trees, free, depth, hi, hmem⟩ := ha
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp hmem
  obtain ⟨trees₁, left₁, ht₁, hi₁, _, _, _, _, _, hrev₁, htag₁, _⟩ :=
    lctExpose_spec pathPayload_laws hi ht hs
  have hs₁ : slot ∈ (AuxTree.node slot left₁ .leaf).toList := by simp [AuxTree.toList]
  obtain ⟨trees₂, left₂, ht₂, hi₂, _, _, hperm, _, _, hrev₂, htag₂, _⟩ :=
    lctExpose_spec pathPayload_laws hi₁ ht₁ hs₁
  have hs₂ : slot ∈ (AuxTree.node slot left₂ .leaf).toList := by simp [AuxTree.toList]
  refine ⟨⟨trees₁, free, depth, hi₁, List.mem_flatMap.mpr ⟨_, ht₁, hs₁⟩⟩,
    ⟨trees₂, free, depth, hi₂, List.mem_flatMap.mpr ⟨_, ht₂, hs₂⟩⟩, ?_⟩
  have hn := (forestKeys_perm (lctExpose pathPayload s slot) trees₁).nodup_iff.mpr hi₁.activeNodup
  exact pair_unique hn (hperm.mem_iff.mp (exposed_value_mem ht₂ hrev₂ htag₂))
    (exposed_value_mem ht₁ hrev₁ htag₁)

/-- A point write changes exactly the selected raw value after
exposure. The pull recomputes the summary without changing values. -/
theorem pathTreeWrite_value (s : PathTreeState) (slot atSlot : ℕ) (value : Option PathEdgeValue) :
    ((pathTreeWrite s slot value).splay.nodes atSlot).val =
      if atSlot = slot then value else ((lctExpose pathPayload s slot).splay.nodes atSlot).val := by
  unfold pathTreeWrite
  dsimp only
  rw [SplayState.pull_val_eq']
  by_cases he : atSlot = slot
  · subst atSlot
    simp [SplayState.nodes_updateNode_self]
  · simp [he]

/-- Away from the exposed root the write and pull preserve the whole node. -/
theorem pathTreeWrite_node_of_ne (s : PathTreeState) {slot atSlot : ℕ} (h : atSlot ≠ slot)
    (value : Option PathEdgeValue) :
    (pathTreeWrite s slot value).splay.nodes atSlot =
      (lctExpose pathPayload s slot).splay.nodes atSlot := by
  unfold pathTreeWrite
  dsimp only
  by_cases hs : slot = 0
  · subst slot
    simp [SplayState.pull, SplayState.nodes_updateNode_ne _ h]
  · simp [SplayState.pull, SplayState.nodes_updateNode_ne _ h, hs]

/-- A point write preserves the evaluated payload of any auxiliary
subtree that avoids the written root. -/
theorem pathTreeWrite_evalPairs_of_not_mem (s : PathTreeState) {slot : ℕ}
    (value : Option PathEdgeValue) (tree : AuxTree) (hn : slot ∉ tree.toList) :
    SplayState.evalPairs pathPayload (pathTreeWrite s slot value).splay tree false pathPayload.idTag =
      SplayState.evalPairs pathPayload (lctExpose pathPayload s slot).splay tree false pathPayload.idTag := by
  apply SplayState.evalPairs_agree
  intro node hm
  exact pathTreeWrite_node_of_ne s (slot := slot) (atSlot := node) (fun he => hn (he ▸ hm)) value

/-- In the exposed auxiliary tree, the write keeps the left subtree
and replaces the final slot-value pair. -/
theorem pathTreeWrite_evalPairs_root (s : PathTreeState) (slot : ℕ) (left : AuxTree)
    (value : Option PathEdgeValue) (hn : slot ∉ left.toList)
    (hrev : ((lctExpose pathPayload s slot).splay.nodes slot).rev = false)
    (htag : ((lctExpose pathPayload s slot).splay.nodes slot).tag = pathPayload.idTag) :
    SplayState.evalPairs pathPayload (pathTreeWrite s slot value).splay
      (.node slot left .leaf) false pathPayload.idTag =
    SplayState.evalPairs pathPayload (lctExpose pathPayload s slot).splay
      left false pathPayload.idTag ++ [(slot, value)] := by
  have hr : ((pathTreeWrite s slot value).splay.nodes slot).rev = false := by
    unfold pathTreeWrite
    dsimp only
    rw [SplayState.pull_rev_eq, SplayState.nodes_updateNode_self]
    exact hrev
  have ht : ((pathTreeWrite s slot value).splay.nodes slot).tag = pathPayload.idTag := by
    unfold pathTreeWrite
    dsimp only
    rw [SplayState.pull_tag_eq, SplayState.nodes_updateNode_self]
    exact htag
  rw [evalPairs_of_rev_false pathPayload_laws hr ht, pathTreeWrite_evalPairs_of_not_mem s value left hn,
    pathTreeWrite_value]
  simp [SplayState.evalPairs]

private theorem pathTreeWrite_structure {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ} {left : AuxTree}
    (hi : LctInvWith pathPayload (lctExpose pathPayload s slot) trees free depth)
    (ht : AuxTree.node slot left .leaf ∈ trees) (hn : slot ∉ left.toList)
    (hrev : ((lctExpose pathPayload s slot).splay.nodes slot).rev = false)
    (htag : ((lctExpose pathPayload s slot).splay.nodes slot).tag = pathPayload.idTag)
    (value : Option PathEdgeValue) :
    LctInvWith pathPayload (pathTreeWrite s slot value) trees free depth := by
  let before := lctExpose pathPayload s slot
  let after := pathTreeWrite s slot value
  let root := AuxTree.node slot left .leaf
  let set := before.splay.updateNode slot (fun node => { node with val := value })
  have hroot : slot ∈ root.toList := by simp [root, AuxTree.toList]
  have hntr (t : AuxTree) (ht' : t ∈ trees) (hne : t ≠ root) : slot ∉ t.toList :=
    fun hm => hne (flatMap_mem_unique hi.activeNodup ht' ht hm hroot)
  have hnodes {x : ℕ} (hx : x ≠ slot) : after.splay.nodes x = before.splay.nodes x :=
    pathTreeWrite_node_of_ne s hx value
  have hpp (x : ℕ) : (after.splay.nodes x).ppar = (before.splay.nodes x).ppar := by
    change ((SplayState.pull pathPayload set slot).nodes x).ppar = _
    rw [SplayState.pull_ppar_eq]
    by_cases hx : x = slot
    · subst x
      simp [set, SplayState.nodes_updateNode_self]
    · rw [SplayState.nodes_updateNode_ne _ hx]
  have hpar (x : ℕ) : (after.splay.nodes x).par = (before.splay.nodes x).par := by
    change ((SplayState.pull pathPayload set slot).nodes x).par = _
    rw [SplayState.pull_par_eq]
    by_cases hx : x = slot
    · subst x
      simp [set, SplayState.nodes_updateNode_self]
    · rw [SplayState.nodes_updateNode_ne _ hx]
  have hrootInv : SplayState.TreeInv pathPayload after.splay root := by
    have htree := hi.treesInv root ht
    obtain ⟨hslot, hleft, hright, hp, _, _, _, hl, _⟩ := htree.sub
    have hget : set.nodes slot = { before.splay.nodes slot with val := value } :=
      SplayState.nodes_updateNode_self _ _ _
    have hl' : SplayState.SubtreeInv pathPayload set slot left :=
      SplayState.SubtreeInv_agree hl (fun x hx =>
        (SplayState.nodes_updateNode_ne before.splay (x := slot) (i := x) (fun he => hn (he ▸ hx)) _).symm)
    refine ⟨htree.nodup, ?_⟩
    apply (SplayState.pull_node_build pathPayload_laws hslot hn (by simp [AuxTree.toList])
      (by rw [hget]; exact hleft) (by rw [hget]; exact hright)
      (by rw [hget]; exact hp) (by simp)
      (by rw [hget]; exact hrev) (by rw [hget]; exact htag) hl' (show SplayState.SubtreeInv pathPayload set slot .leaf from trivial)).1
  have hids (t : AuxTree) (ht' : t ∈ trees) :
      treeIds pathPayload after.splay t = treeIds pathPayload before.splay t := by
    by_cases he : t = root
    · subst t
      have hnew := pathTreeWrite_evalPairs_root s slot left value hn hrev htag
      have hold := evalPairs_of_rev_false pathPayload_laws (l := left) (r := AuxTree.leaf) hrev htag
      unfold treeIds
      rw [hnew, hold]
      simp [SplayState.evalPairs]
    · exact treeIds_agree (fun x hm => hnodes (fun heq => hntr _ ht' he (heq ▸ hm)))
  have hinduced : ∀ x, inducedSubPar pathPayload after.splay trees x =
      inducedSubPar pathPayload before.splay trees x := by
    suffices ∀ ts : List AuxTree, (∀ t ∈ ts, t ∈ trees) → ∀ x,
        inducedSubPar pathPayload after.splay ts x = inducedSubPar pathPayload before.splay ts x from
      this trees (fun _ h => h)
    intro ts
    induction ts with
    | nil => simp [inducedSubPar]
    | cons t ts ih =>
      intro hsub x
      simp only [inducedSubPar, hids t (hsub t (by simp)), hpp,
        ih (fun u hu => hsub u (List.mem_cons_of_mem _ hu)) x]
  refine ⟨hi.treesNonEmpty, ?_, hi.activeNodup, hi.activeValid, hi.verticesActive,
    hi.freeNodup, hi.freeValid, hi.partitionSlots, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht'
    by_cases he : t = root
    · exact he.symm ▸ hrootInv
    · exact SplayState.TreeInv_agree (hi.treesInv t ht') (fun x hm =>
        (hnodes (fun heq => hntr _ ht' he (heq ▸ hm))).symm)
  · exact FreeListInv_agree hi.freeListInv (fun x _ => hpar x)
  · intro t ht'
    rw [hpp]
    exact hi.pparActive t ht'
  · intro x hx
    rw [hinduced]
    exact hi.acyclic x hx
  · intro x hx
    rw [hinduced]
    exact hi.vertexParEdge x hx
  · intro e he hs
    rw [hinduced]
    exact hi.edgeParVertex e he hs
  · intro e he hs
    change ∃! x, x ∈ trees.flatMap AuxTree.toList ∧
      inducedSubPar pathPayload after.splay trees x = e ∧ isVertex before.n x ∧
      x ≠ inducedSubPar pathPayload after.splay trees e
    simpa only [hinduced] using hi.edgeUniqueChild e he hs

/-- PointWrite preserves the active node set (up to permutation) and `inducedSubPar`. -/
theorem pathTreeWrite_inducedSubPar {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ} {tree : AuxTree}
    (hi : LctInvWith pathPayload s trees free depth)
    (htree : tree ∈ trees) (hslot : slot ∈ tree.toList) (value : Option PathEdgeValue) :
    ∃ trees', LctInvWith pathPayload (pathTreeWrite s slot value) trees' free depth ∧
      (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      ∀ z, inducedSubPar pathPayload (pathTreeWrite s slot value).splay trees' z =
        inducedSubPar pathPayload s.splay trees z := by
  obtain ⟨trees', left, ht, hinv, hperm, hpar, _, _, _, hrev, htag, _⟩ :=
    lctExpose_spec pathPayload_laws hi htree hslot
  have hleft : slot ∉ left.toList := by
    have hn := (hinv.treesInv _ ht).nodup
    simp only [AuxTree.toList, List.append_nil] at hn
    exact fun hm => (List.nodup_append.mp hn).2.2 _ hm _ (by simp) rfl
  let root := AuxTree.node slot left .leaf
  have hroot : slot ∈ root.toList := by simp [root, AuxTree.toList]
  have hntr (t : AuxTree) (ht' : t ∈ trees') (hne : t ≠ root) : slot ∉ t.toList :=
    fun hm => hne (flatMap_mem_unique hinv.activeNodup ht' ht hm hroot)
  have hpp (x : ℕ) : ((pathTreeWrite s slot value).splay.nodes x).ppar =
      ((lctExpose pathPayload s slot).splay.nodes x).ppar := by
    by_cases hx : x = slot
    · subst x
      unfold pathTreeWrite; dsimp only
      rw [SplayState.pull_ppar_eq, SplayState.nodes_updateNode_self]
    · rw [pathTreeWrite_node_of_ne s hx value]
  have hids (t : AuxTree) (ht' : t ∈ trees') :
      treeIds pathPayload (pathTreeWrite s slot value).splay t =
        treeIds pathPayload (lctExpose pathPayload s slot).splay t := by
    by_cases he : t = root
    · subst t
      have hnew := pathTreeWrite_evalPairs_root s slot left value hleft hrev htag
      have hold := evalPairs_of_rev_false pathPayload_laws (l := left) (r := AuxTree.leaf) hrev htag
      unfold treeIds
      change List.map Prod.fst (SplayState.evalPairs pathPayload (pathTreeWrite s slot value).splay
          (AuxTree.node slot left .leaf) false pathPayload.idTag) =
        List.map Prod.fst (SplayState.evalPairs pathPayload (lctExposeCost pathPayload s slot).1.splay
          (AuxTree.node slot left .leaf) false pathPayload.idTag)
      rw [hnew, hold]
      simp [SplayState.evalPairs, lctExpose]
    · exact treeIds_agree (fun x hm =>
        pathTreeWrite_node_of_ne s (fun heq => by subst heq; exact hntr _ ht' he hm) value)
  have hinduced : ∀ z, inducedSubPar pathPayload (pathTreeWrite s slot value).splay trees' z =
      inducedSubPar pathPayload (lctExpose pathPayload s slot).splay trees' z := by
    suffices ∀ ts : List AuxTree, (∀ t ∈ ts, t ∈ trees') → ∀ z,
        inducedSubPar pathPayload (pathTreeWrite s slot value).splay ts z =
          inducedSubPar pathPayload (lctExpose pathPayload s slot).splay ts z from
      this trees' (fun _ h => h)
    intro ts
    induction ts with
    | nil => simp [inducedSubPar]
    | cons t ts ih =>
      intro hsub z
      simp only [inducedSubPar, hids t (hsub t (by simp)), hpp,
        ih (fun u hu => hsub u (List.mem_cons_of_mem _ hu)) z]
  refine ⟨trees', pathTreeWrite_structure hinv ht hleft hrev htag value, hperm, fun z => ?_⟩
  rw [hinduced z]
  exact hpar z

/-- In the forest of the exposed state, PointWrite replaces exactly
the selected slot-value pair. All other evaluated pairs agree
with the incoming forest, up to the reordering caused by exposure. -/
theorem pathTreeWrite_forestPairs {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ} {tree : AuxTree}
    (hi : LctInvWith pathPayload s trees free depth)
    (htree : tree ∈ trees) (hslot : slot ∈ tree.toList) (value : Option PathEdgeValue) :
    ∃ trees', LctInvWith pathPayload (pathTreeWrite s slot value) trees' free depth ∧
      ∀ x v, (x, v) ∈ forestPairs pathPayload (pathTreeWrite s slot value).splay trees' ↔
        (x = slot ∧ v = value) ∨ (x ≠ slot ∧ (x, v) ∈ forestPairs pathPayload s.splay trees) := by
  obtain ⟨trees', left, ht, hinv, _, _, hperm, _, _, hrev, htag, _⟩ :=
    lctExpose_spec pathPayload_laws hi htree hslot
  let exposed := lctExpose pathPayload s slot
  let root := AuxTree.node slot left .leaf
  have hroot : slot ∈ root.toList := by simp [root, AuxTree.toList]
  have hleft : slot ∉ left.toList := by
    have hn := (hinv.treesInv _ ht).nodup
    simp only [AuxTree.toList, List.append_nil] at hn
    exact fun hm => (List.nodup_append.mp hn).2.2 _ hm _ (by simp) rfl
  have hnot (t : AuxTree) (ht' : t ∈ trees') (hne : t ≠ root) : slot ∉ t.toList :=
    fun h => hne (flatMap_mem_unique hinv.activeNodup ht' ht h hroot)
  have hkey {t : AuxTree} {x : ℕ} {v : Option PathEdgeValue}
      (hm : (x, v) ∈ SplayState.evalPairs pathPayload exposed.splay t false pathPayload.idTag) :
      x ∈ t.toList := by
    have hmap : x ∈ (SplayState.evalPairs pathPayload exposed.splay t false pathPayload.idTag).map Prod.fst := List.mem_map.mpr ⟨(x, v), hm, rfl⟩
    rw [SplayState.evalPairs_map_fst] at hmap
    exact (t.evalInorder_perm _ _).mem_iff.mp hmap
  refine ⟨trees', pathTreeWrite_structure hinv ht hleft hrev htag value, fun x v => ?_⟩
  constructor
  · intro hm
    obtain ⟨t, ht', hm⟩ := List.mem_flatMap.mp hm
    by_cases htr : t = root
    · subst t
      rw [pathTreeWrite_evalPairs_root s slot left value hleft hrev htag] at hm
      rcases List.mem_append.mp hm with h | h
      · have hne : x ≠ slot := fun hxs => hleft (hxs ▸ hkey h)
        exact Or.inr ⟨hne, hperm.mem_iff.mp (List.mem_flatMap.mpr ⟨root, ht, by
          rw [evalPairs_of_rev_false pathPayload_laws hrev htag]
          exact List.mem_append_left _ (List.mem_append_left _ h)⟩)⟩
      · have hp := List.mem_singleton.mp h
        exact Or.inl ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rw [pathTreeWrite_evalPairs_of_not_mem s value t (hnot t ht' htr)] at hm
      exact Or.inr ⟨fun hxs => hnot t ht' htr (hxs ▸ hkey hm),
        hperm.mem_iff.mp (List.mem_flatMap.mpr ⟨t, ht', hm⟩)⟩
  · rintro (⟨hx, hv⟩ | ⟨hne, hm⟩)
    · rw [hx, hv]
      exact List.mem_flatMap.mpr ⟨root, ht, by
        rw [pathTreeWrite_evalPairs_root s slot left value hleft hrev htag]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    · obtain ⟨t, ht', hm⟩ := List.mem_flatMap.mp (hperm.mem_iff.mpr hm)
      refine List.mem_flatMap.mpr ⟨t, ht', ?_⟩
      by_cases htr : t = root
      · subst t
        rw [evalPairs_of_rev_false pathPayload_laws hrev htag] at hm
        simp only [SplayState.evalPairs.eq_1, List.append_nil, List.mem_append,
          List.mem_singleton] at hm
        rw [pathTreeWrite_evalPairs_root s slot left value hleft hrev htag]
        exact List.mem_append_left _ (hm.resolve_right (fun hp => hne (congrArg Prod.fst hp)))
      · rw [pathTreeWrite_evalPairs_of_not_mem s value t (hnot t ht' htr)]
        exact hm

private theorem sameFreeList {s : PathTreeState} {head : ℕ} {xs ys : List ℕ}
    (hx : FreeListInv s.splay head xs) (hy : FreeListInv s.splay head ys) : xs = ys := by
  induction xs generalizing ys head with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact (hy.1 hx).elim
  | cons x xs ih =>
    cases ys with
    | nil => exact (hx.1 hy).elim
    | cons y ys =>
      have he : x = y := hx.2.1.symm.trans hy.2.1
      rw [he, ih hx.2.2 hy.2.2]

/-- An evaluated pair determines the unique value returned by a
PointRead on its slot. -/
theorem pathTreeExpose_value_of_forestPair {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ} {value : Option PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hm : (slot, value) ∈ forestPairs pathPayload s.splay trees) :
    ((lctExpose pathPayload s slot).splay.nodes slot).val = value := by
  have ha := (forestKeys_perm s trees).mem_iff.mp (List.mem_map.mpr ⟨_, hm, rfl⟩)
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp ha
  obtain ⟨trees', left, ht', _, _, _, hperm, _, _, hrev, htag, _⟩ :=
    lctExpose_spec pathPayload_laws hi ht hs
  have hval := hperm.mem_iff.mp (exposed_value_mem (trees := trees') (left := left) ht' hrev htag)
  exact pair_unique ((forestKeys_perm s trees).nodup_iff.mpr hi.activeNodup) hval hm

/-- Every evaluated payload belongs to an active forest slot. -/
theorem pathTree_forestPair_mem_active {s : PathTreeState} {trees : List AuxTree}
    {slot : ℕ} {value : Option PathEdgeValue}
    (hm : (slot, value) ∈ forestPairs pathPayload s.splay trees) :
    slot ∈ trees.flatMap AuxTree.toList :=
  (forestKeys_perm s trees).mem_iff.mp (List.mem_map.mpr ⟨_, hm, rfl⟩)

/-- Readiness is exactly a nonnegative edge payload among the
evaluated forest pairs. The statement uses any structural witness. -/
theorem pathTreeReady_iff_forestPairs {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ}
    (hi : LctInvWith pathPayload s trees free depth) (slot : ℕ) :
    pathTreeReady s slot ↔ isEdgeSlot s.n slot ∧
      ∃ value, (slot, some value) ∈ forestPairs pathPayload s.splay trees ∧ 0 ≤ value.detector := by
  have hactive : ∀ value, (slot, value) ∈ forestPairs pathPayload s.splay trees →
      slot ∈ trees.flatMap AuxTree.toList := by
    intro value hv
    exact (forestKeys_perm s trees).mem_iff.mp (List.mem_map.mpr ⟨_, hv, rfl⟩)
  have hpair (ht : slot ∈ trees.flatMap AuxTree.toList) :
      (slot, ((lctExpose pathPayload s slot).splay.nodes slot).val) ∈
        forestPairs pathPayload s.splay trees := by
    obtain ⟨t, htree, hs⟩ := List.mem_flatMap.mp ht
    obtain ⟨trees', left, ht', _, _, _, hperm, _, _, hrev, htag, _⟩ :=
      lctExpose_spec pathPayload_laws hi htree hs
    exact hperm.mem_iff.mp (exposed_value_mem (trees := trees') (left := left) ht' hrev htag)
  constructor
  · rintro ⟨hs, ⟨trees', free', depth', hInv, hmem⟩, value, hv, hnonneg⟩
    have hfree := sameFreeList hi.freeListInv hInv.freeListInv
    have ha : slot ∈ trees.flatMap AuxTree.toList := (hi.partitionSlots slot hs).2
      (hfree ▸ (hInv.partitionSlots slot hs).1 hmem)
    have hm := hpair ha
    rw [hv] at hm
    exact ⟨hs, value, hm, hnonneg⟩
  · rintro ⟨hs, value, hv, hnonneg⟩
    have ha := hactive _ hv
    have hn := (forestKeys_perm s trees).nodup_iff.mpr hi.activeNodup
    exact ⟨hs, ⟨trees, free, depth, hi, ha⟩, value, pair_unique hn (hpair ha) hv, hnonneg⟩

/-- Exposing any active node keeps the ready set of the whole forest. -/
theorem pathTreeReady_after_expose {s : PathTreeState} {slot : ℕ}
    (ha : pathTreeActive s slot) (x : ℕ) :
    pathTreeReady (lctExpose pathPayload s slot) x ↔ pathTreeReady s x := by
  obtain ⟨trees, free, depth, hi, hm⟩ := ha
  obtain ⟨tree, ht, hs⟩ := List.mem_flatMap.mp hm
  obtain ⟨trees', _, _, hi', _, _, hp, _⟩ := lctExpose_spec pathPayload_laws hi ht hs
  change LctInvWith pathPayload (lctExpose pathPayload s slot) trees' free depth at hi'
  change (forestPairs pathPayload (lctExpose pathPayload s slot).splay trees').Perm _ at hp
  rw [pathTreeReady_iff_forestPairs hi', pathTreeReady_iff_forestPairs hi]
  change (isEdgeSlot s.n x ∧ _) ↔ _
  simp only [hp.mem_iff]

/-- Writing a negative detector residual removes the selected slot
from the ready set and preserves readiness of every other slot. -/
theorem pathTreeReady_after_reset {s : PathTreeState} {slot : ℕ}
    (ha : pathTreeActive s slot) (value : PathEdgeValue) (hneg : value.detector < 0)
    (x : ℕ) :
    pathTreeReady (pathTreeWrite s slot (some value)) x ↔ x ≠ slot ∧ pathTreeReady s x := by
  obtain ⟨trees, free, depth, hi, hm⟩ := ha
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp hm
  obtain ⟨trees', hi', hpair⟩ := pathTreeWrite_forestPairs hi ht hs (some value)
  rw [pathTreeReady_iff_forestPairs hi', pathTreeReady_iff_forestPairs hi]
  change (isEdgeSlot s.n x ∧ _) ↔ _
  constructor
  · rintro ⟨he, v, hv, hn⟩
    rcases (hpair x (some v)).mp hv with ⟨_, hval⟩ | ⟨hne, hold⟩
    · have h : v = value := Option.some.inj hval
      exact False.elim ((not_le_of_gt hneg) (h ▸ hn))
    · exact ⟨hne, he, v, hold, hn⟩
  · rintro ⟨hne, he, v, hv, hn⟩
    exact ⟨he, v, (hpair x (some v)).2 (Or.inr ⟨hne, hv⟩), hn⟩

/-- The full report round changes one forest payload. The search and
read exposures preserve the other evaluated pairs. -/
theorem pathTreeReport_forestPairs {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hm : slot ∈ trees.flatMap AuxTree.toList) (value : Option PathEdgeValue) :
    let read := lctExpose pathPayload (lctExpose pathPayload s slot) slot
    let updated := pathTreeWrite read slot value
    ∃ trees', LctInvWith pathPayload updated trees' free depth ∧
      ∀ x v, (x, v) ∈ forestPairs pathPayload updated.splay trees' ↔
        (x = slot ∧ v = value) ∨ (x ≠ slot ∧ (x, v) ∈ forestPairs pathPayload s.splay trees) := by
  dsimp only
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp hm
  obtain ⟨trees₁, left₁, ht₁, hi₁, _, _, hp₁, _⟩ :=
    lctExpose_spec pathPayload_laws hi ht hs
  have hs₁ : slot ∈ (AuxTree.node slot left₁ .leaf).toList := by simp [AuxTree.toList]
  obtain ⟨trees₂, left₂, ht₂, hi₂, _, _, hp₂, _⟩ :=
    lctExpose_spec pathPayload_laws hi₁ ht₁ hs₁
  have hs₂ : slot ∈ (AuxTree.node slot left₂ .leaf).toList := by simp [AuxTree.toList]
  obtain ⟨trees', hnew, hpair⟩ := pathTreeWrite_forestPairs hi₂ ht₂ hs₂ value
  exact ⟨trees', hnew, fun x v => (hpair x v).trans
    (or_congr Iff.rfl (and_congr_right fun _ => (hp₂.trans hp₁).mem_iff))⟩

/-- The search, point read, and reset leave all other ready slots in
place. The next round can use the original slot names. -/
theorem pathTreeReady_after_report {s : PathTreeState} {slot : ℕ}
    (hr : pathTreeReady s slot) (value : PathEdgeValue) (hneg : value.detector < 0)
    (x : ℕ) :
    let first := lctExpose pathPayload s slot
    let second := lctExpose pathPayload first slot
    pathTreeReady (pathTreeWrite second slot (some value)) x ↔ x ≠ slot ∧ pathTreeReady s x := by
  dsimp only
  obtain ⟨ha₁, ha₂, _⟩ := pathTree_expose_twice_value s slot hr.2.1
  rw [pathTreeReady_after_reset ha₂ value hneg, pathTreeReady_after_expose ha₁,
    pathTreeReady_after_expose hr.2.1]

end MinCostFlow.MinRatio
