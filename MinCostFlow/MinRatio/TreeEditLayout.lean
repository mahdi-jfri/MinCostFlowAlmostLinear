module

public import MinCostFlow.Chain.Algorithm1
public import WordRAM.Logic
import WordRAM.Memory

/-!
# Tree-change records

Lemma 5.11 (page 20) returns insertions and deletions on the chain
tree. Each record contains a tag and the model edge name. The caller
resolves that name against the old graph for a cut or the new graph
for a link.
-/

public section
namespace MinCostFlow.MinRatio
open Chain WordRAM

/-- An insertion is tagged one and a deletion is tagged zero. -/
@[expose] def treeEditWords : TreeChange → List ℕ
  | .insert e => [1, e]
  | .delete e => [0, e]

/-- Tree changes occur in list order, in consecutive two-word records. -/
@[expose] def TreeEditsAt (mem : ℕ → ℕ) (base : ℕ) (changes : List TreeChange) : Prop :=
  ListAt mem base (changes.flatMap treeEditWords)

/-- The packed edit list uses exactly two words per change. -/
theorem treeEditWords_length (edits : List TreeChange) :
    (edits.flatMap treeEditWords).length = 2 * edits.length := by
  induction edits with
  | nil => rfl
  | cons edit rest ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons, Nat.mul_add]
    cases edit <;> simp [treeEditWords, Nat.add_comm]

/-- The packed changes of Lemma 5.11 occupy two words per edge in
the symmetric difference of the two tree edge sets. -/
theorem treeEditDiff_words (oldE newE : Finset ℕ) :
    ((diffTreeChanges oldE newE).flatMap treeEditWords).length =
      2 * ((oldE \ newE).card + (newE \ oldE).card) := by
  rw [treeEditWords_length, diffTreeChanges_length]

/-- Split the next record from the unread suffix without changing
the order of the model edits. -/
theorem treeEditsAt_cons {mem : ℕ → ℕ} {base : ℕ} {change : TreeChange}
    {rest : List TreeChange} (h : TreeEditsAt mem base (change :: rest)) :
    ListAt mem base (treeEditWords change) ∧ TreeEditsAt mem (base + 2) rest := by
  rw [TreeEditsAt, List.flatMap_cons] at h
  have hpair := listAt_append.mp h
  have hlen : (treeEditWords change).length = 2 := by cases change <;> rfl
  exact ⟨hpair.1, by simpa only [TreeEditsAt, hlen] using hpair.2⟩

/-- A deletion record in the symmetric difference names an edge
of the old tree that is absent from the new tree. -/
theorem treeEdit_delete_mem_diff {oldE newE : Finset ℕ} {e : ℕ} :
    TreeChange.delete e ∈ diffTreeChanges oldE newE ↔ e ∈ oldE \ newE := by
  classical
  simp [diffTreeChanges, List.mem_map]

/-- An insertion record in the symmetric difference names an edge
of the new tree that is absent from the old tree. -/
theorem treeEdit_insert_mem_diff {oldE newE : Finset ℕ} {e : ℕ} :
    TreeChange.insert e ∈ diffTreeChanges oldE newE ↔ e ∈ newE \ oldE := by
  classical
  simp [diffTreeChanges, List.mem_map]

/-- The symmetric difference has one record per changed edge and
never schedules a cut and link of the same name. -/
theorem treeEdit_diff_nodup (oldE newE : Finset ℕ) :
    (diffTreeChanges oldE newE).Nodup ∧
    ∀ e, TreeChange.delete e ∈ diffTreeChanges oldE newE →
      TreeChange.insert e ∉ diffTreeChanges oldE newE := by
  classical
  constructor
  · rw [diffTreeChanges, List.nodup_append]
    exact ⟨(Finset.nodup_toList _).map (fun _ _ h => TreeChange.delete.inj h),
      (Finset.nodup_toList _).map (fun _ _ h => TreeChange.insert.inj h), by
        intro a ha b hb heq
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        cases heq⟩
  · intro e hd hi
    exact (Finset.mem_sdiff.mp (treeEdit_delete_mem_diff.mp hd)).2
      (Finset.mem_sdiff.mp (treeEdit_insert_mem_diff.mp hi)).1

private theorem apply_delete_names (edges : Finset ℕ) (names : List ℕ) :
    applyTreeChanges edges (names.map TreeChange.delete) = edges \ names.toFinset := by
  induction names generalizing edges with
  | nil => simp [applyTreeChanges]
  | cons e rest ih =>
    change applyTreeChanges (edges.erase e) (rest.map TreeChange.delete) = _
    rw [ih]
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert, not_or]
    tauto

private theorem apply_insert_names (edges : Finset ℕ) (names : List ℕ) :
    applyTreeChanges edges (names.map TreeChange.insert) = edges ∪ names.toFinset := by
  induction names generalizing edges with
  | nil => simp [applyTreeChanges]
  | cons e rest ih =>
    change applyTreeChanges (insert e edges) (rest.map TreeChange.insert) = _
    rw [ih]
    ext f
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
    tauto

/-- All deletions in the model difference run before the insertions.
At an insertion cursor, the current edges are contained in the
target tree and the next edge is absent. -/
theorem treeEdit_insert_prefix {oldE newE : Finset ℕ} {done todo : List ℕ} {e : ℕ}
    (hs : (newE \ oldE).toList = done ++ e :: todo) :
    let current := applyTreeChanges oldE
      ((oldE \ newE).toList.map TreeChange.delete ++ done.map TreeChange.insert)
    current ⊆ newE ∧ e ∉ current ∧ e ∈ newE := by
  have hn : ¬ e ∈ done := by
    have hd := Finset.nodup_toList (newE \ oldE)
    rw [hs] at hd
    exact fun he => (List.nodup_append.mp hd).2.2 e he e (by simp) rfl
  have hnew : e ∈ newE \ oldE := Finset.mem_toList.mp (by rw [hs]; simp)
  have hsubset : done.toFinset ⊆ newE := by
    intro f hf
    have hm : f ∈ (newE \ oldE).toList := by
      rw [hs]
      exact List.mem_append_left _ (List.mem_toFinset.mp hf)
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hm)).1
  dsimp only
  have ha : applyTreeChanges oldE
      ((oldE \ newE).toList.map TreeChange.delete ++ done.map TreeChange.insert) =
      applyTreeChanges (applyTreeChanges oldE ((oldE \ newE).toList.map TreeChange.delete))
        (done.map TreeChange.insert) := List.foldl_append
  rw [ha, apply_delete_names, apply_insert_names, Finset.toList_toFinset]
  refine ⟨Finset.union_subset ?_ hsubset, ?_, (Finset.mem_sdiff.mp hnew).1⟩
  · intro f hf
    by_contra h
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hf).1, h⟩)
  · intro hm
    rcases Finset.mem_union.mp hm with ho | hd
    · exact (Finset.mem_sdiff.mp hnew).2 (Finset.mem_sdiff.mp ho).1
    · exact hn (List.mem_toFinset.mp hd)

private theorem insertion_cursor_of_map {processed suffix : List TreeChange} {names : List ℕ}
    {e : ℕ} (hs : names.map TreeChange.insert = processed ++ .insert e :: suffix) :
    ∃ done todo, names = done ++ e :: todo ∧
      processed = done.map TreeChange.insert ∧ suffix = todo.map TreeChange.insert := by
  induction processed generalizing names with
  | nil =>
    cases names with
    | nil => simp at hs
    | cons n rest =>
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at hs
      exact ⟨[], rest, by cases hs.1; rfl, rfl, hs.2.symm⟩
  | cons first processed ih =>
    cases names with
    | nil => simp at hs
    | cons n rest =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hs
      obtain ⟨done, todo, hrest, hp, htail⟩ := ih hs.2
      exact ⟨n :: done, todo, by rw [hrest]; rfl, by rw [hp, ← hs.1]; rfl, htail⟩

private theorem insertion_cursor_of_blocks {deletes inserts : List ℕ}
    {processed suffix : List TreeChange} {e : ℕ}
    (h : deletes.map TreeChange.delete ++ inserts.map TreeChange.insert =
      processed ++ .insert e :: suffix) :
    ∃ done todo, inserts = done ++ e :: todo ∧
      processed = deletes.map TreeChange.delete ++ done.map TreeChange.insert ∧
      suffix = todo.map TreeChange.insert := by
  induction deletes generalizing processed with
  | nil =>
    obtain ⟨done, todo, hn, hp, hs⟩ := insertion_cursor_of_map (by simpa using h)
    exact ⟨done, todo, hn, by simpa using hp, hs⟩
  | cons d ds ih =>
    cases processed with
    | nil => simp at h
    | cons edit processed =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨done, todo, hn, hp, hs⟩ := ih h.2
      exact ⟨done, todo, hn, by rw [hp, ← h.1]; rfl, hs⟩

/-- If the next edge change is an insertion, the processed prefix
contains all deletions followed by exactly the already linked names. -/
theorem treeEdit_diff_insertion_cursor {oldE newE : Finset ℕ} {e : ℕ}
    {processed suffix : List TreeChange}
    (hs : diffTreeChanges oldE newE = processed ++ .insert e :: suffix) :
    ∃ done todo, (newE \ oldE).toList = done ++ e :: todo ∧
      processed = (oldE \ newE).toList.map TreeChange.delete ++ done.map TreeChange.insert ∧
      suffix = todo.map TreeChange.insert := by
  exact insertion_cursor_of_blocks hs

private theorem mem_applyTreeChanges_of_absent {E : Finset ℕ} {e : ℕ}
    {changes : List TreeChange}
    (hd : TreeChange.delete e ∉ changes) (hi : TreeChange.insert e ∉ changes) :
    e ∈ applyTreeChanges E changes ↔ e ∈ E := by
  induction changes generalizing E with
  | nil => rfl
  | cons ch rest ih =>
    have hd' : TreeChange.delete e ∉ rest := fun h => hd (List.mem_cons_of_mem _ h)
    have hi' : TreeChange.insert e ∉ rest := fun h => hi (List.mem_cons_of_mem _ h)
    cases ch with
    | delete f =>
      have hne : e ≠ f := fun eq => hd (by simp [eq])
      change e ∈ applyTreeChanges (E.erase f) rest ↔ e ∈ E
      rw [ih hd' hi']
      simp [Finset.mem_erase, hne]
    | insert f =>
      have hne : e ≠ f := fun eq => hi (by simp [eq])
      change e ∈ applyTreeChanges (insert f E) rest ↔ e ∈ E
      rw [ih hd' hi']
      simp [Finset.mem_insert, hne]

/-- A deletion at the cursor is still live after the processed prefix. -/
theorem treeEdit_diff_delete_live {oldE newE : Finset ℕ} {e : ℕ}
    {processed remaining : List TreeChange}
    (hs : diffTreeChanges oldE newE = processed ++ .delete e :: remaining) :
    e ∈ applyTreeChanges oldE processed := by
  obtain ⟨hdup, hcross⟩ := treeEdit_diff_nodup oldE newE
  have hmem : TreeChange.delete e ∈ diffTreeChanges oldE newE := by rw [hs]; simp
  rw [hs] at hdup
  have hd : TreeChange.delete e ∉ processed := fun hm =>
    (List.nodup_append.mp hdup).2.2 _ hm _ List.mem_cons_self rfl
  have hi : TreeChange.insert e ∉ processed := fun hm =>
    hcross e hmem (hs.symm ▸ List.mem_append_left _ hm)
  exact (mem_applyTreeChanges_of_absent hd hi).mpr
    (Finset.mem_sdiff.mp (treeEdit_delete_mem_diff.mp hmem)).1

/-- An insertion at the cursor is absent after the processed prefix. -/
theorem treeEdit_diff_insert_absent {oldE newE : Finset ℕ} {e : ℕ}
    {processed remaining : List TreeChange}
    (hs : diffTreeChanges oldE newE = processed ++ .insert e :: remaining) :
    e ∉ applyTreeChanges oldE processed := by
  obtain ⟨done, _, hcursor, hprocessed, _⟩ := treeEdit_diff_insertion_cursor hs
  rw [hprocessed]
  exact (treeEdit_insert_prefix hcursor).2.1

/-- An emitted forest difference lists each removed name once,
then each added name once. Within each part, the order may follow
the stored edge lists of the input graphs. -/
def TreeEditDifference (oldE newE : Finset ℕ) (changes : List TreeChange) : Prop :=
  ∃ deletes inserts : List ℕ,
    deletes.Perm (oldE \ newE).toList ∧ inserts.Perm (newE \ oldE).toList ∧
    changes = deletes.map TreeChange.delete ++ inserts.map TreeChange.insert

/-- The chain model's list is one instance of the packed difference. -/
theorem treeEditDifference_model (oldE newE : Finset ℕ) :
    TreeEditDifference oldE newE (diffTreeChanges oldE newE) :=
  ⟨_, _, List.Perm.refl _, List.Perm.refl _, rfl⟩

/-- Filtering the two stored edge lists produces the required order
and membership without choosing a canonical ordering of the names. -/
theorem treeEditDifference_of_filter {oldE newE : Finset ℕ} {oldNames newNames : List ℕ}
    (ho : oldNames.Perm oldE.toList) (hn : newNames.Perm newE.toList) :
    TreeEditDifference oldE newE
      ((oldNames.filter (fun e => decide (e ∉ newE))).map TreeChange.delete ++
        (newNames.filter (fun e => decide (e ∉ oldE))).map TreeChange.insert) := by
  refine ⟨_, _, ?_, ?_, rfl⟩
  · have hnd : oldNames.Nodup := ho.nodup_iff.mpr (Finset.nodup_toList _)
    apply List.perm_of_nodup_nodup_toFinset_eq (hnd.filter _) (Finset.nodup_toList _)
    ext e
    simp [ho.mem_iff, Finset.mem_sdiff]
  · have hnd : newNames.Nodup := hn.nodup_iff.mpr (Finset.nodup_toList _)
    apply List.perm_of_nodup_nodup_toFinset_eq (hnd.filter _) (Finset.nodup_toList _)
    ext e
    simp [hn.mem_iff, Finset.mem_sdiff]

/-- Any such edit list has the model's edit count and target edge set. -/
theorem TreeEditDifference.result {oldE newE : Finset ℕ} {changes : List TreeChange}
    (h : TreeEditDifference oldE newE changes) :
    changes.length = (oldE \ newE).card + (newE \ oldE).card ∧
    applyTreeChanges oldE changes = newE := by
  obtain ⟨ds, ins, hd, hi, rfl⟩ := h
  constructor
  · simp [hd.length_eq, hi.length_eq]
  · have happ : applyTreeChanges oldE (ds.map TreeChange.delete ++ ins.map TreeChange.insert) =
        applyTreeChanges (applyTreeChanges oldE (ds.map TreeChange.delete))
          (ins.map TreeChange.insert) := List.foldl_append
    rw [happ]
    have hds : ds.toFinset = oldE \ newE := by ext e; simp [hd.mem_iff]
    have hins : ins.toFinset = newE \ oldE := by ext e; simp [hi.mem_iff]
    rw [apply_delete_names, apply_insert_names, hds, hins]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, not_and, not_not]
    tauto

/-- A packed difference contains exactly the model records. -/
theorem TreeEditDifference.perm {oldE newE : Finset ℕ} {changes : List TreeChange}
    (h : TreeEditDifference oldE newE changes) :
    changes.Perm (diffTreeChanges oldE newE) := by
  obtain ⟨ds, ins, hd, hi, rfl⟩ := h
  exact (hd.map TreeChange.delete).append (hi.map TreeChange.insert)

/-- A packed deletion names a live edge in the processed graph. -/
theorem TreeEditDifference.delete_live {oldE newE : Finset ℕ} {changes done rest : List TreeChange}
    {e : ℕ} (h : TreeEditDifference oldE newE changes) (hs : changes = done ++ .delete e :: rest) :
    e ∈ applyTreeChanges oldE done := by
  obtain ⟨hnd, hcross⟩ := treeEdit_diff_nodup oldE newE
  have hp := h.perm
  have hm : TreeChange.delete e ∈ diffTreeChanges oldE newE := hp.mem_iff.mp (by rw [hs]; simp)
  have hdup := hp.nodup_iff.mpr hnd
  rw [hs] at hdup
  have hd : TreeChange.delete e ∉ done := fun he =>
    (List.nodup_append.mp hdup).2.2 _ he _ List.mem_cons_self rfl
  have hi : TreeChange.insert e ∉ done := fun he =>
    hcross e hm (hp.mem_iff.mp (hs.symm ▸ List.mem_append_left _ he))
  exact (mem_applyTreeChanges_of_absent hd hi).mpr
    (Finset.mem_sdiff.mp (treeEdit_delete_mem_diff.mp hm)).1

/-- A pending deletion uses an old-only name, and a pending insertion uses a
new-only name. Thus the insertion cannot overwrite any old-only name's slot. -/
theorem TreeEditDifference.delete_mem_sdiff {oldE newE : Finset ℕ}
    {changes : List TreeChange} {e : ℕ} (h : TreeEditDifference oldE newE changes)
    (he : TreeChange.delete e ∈ changes) : e ∈ oldE \ newE :=
  treeEdit_delete_mem_diff.mp (h.perm.mem_iff.mp he)

/-- The insertions in the packed list use names absent from the old forest. -/
theorem TreeEditDifference.insert_mem_sdiff {oldE newE : Finset ℕ}
    {changes : List TreeChange} {e : ℕ} (h : TreeEditDifference oldE newE changes)
    (he : TreeChange.insert e ∈ changes) : e ∈ newE \ oldE :=
  treeEdit_insert_mem_diff.mp (h.perm.mem_iff.mp he)

/-- Link's slot binding keeps the original slot map on all deletion names. -/
theorem TreeEditDifference.update_slot_of_insert {oldE newE : Finset ℕ}
    {changes : List TreeChange} {e k : ℕ} {slot initial : ℕ → ℕ}
    (h : TreeEditDifference oldE newE changes)
    (he : TreeChange.insert e ∈ changes)
    (hslot : ∀ f ∈ oldE \ newE, slot f = initial f) :
    ∀ f ∈ oldE \ newE, Function.update slot e k f = initial f := by
  have heOld := (Finset.mem_sdiff.mp (h.insert_mem_sdiff he)).2
  intro f hf
  have hne : f ≠ e := fun hEq => heOld (hEq ▸ (Finset.mem_sdiff.mp hf).1)
  rw [Function.update_of_ne hne, hslot f hf]

/-- Each pending deletion has a name distinct from every processed deletion. -/
theorem TreeEditDifference.delete_not_processed {oldE newE : Finset ℕ}
    {done rest : List TreeChange} {e : ℕ}
    (h : TreeEditDifference oldE newE (done ++ .delete e :: rest)) :
    TreeChange.delete e ∉ done := by
  have hnd := h.perm.nodup_iff.mpr (treeEdit_diff_nodup oldE newE).1
  intro he
  exact (List.nodup_append.mp hnd).2.2 _ he _ List.mem_cons_self rfl

/-- The off-tree records already saved correspond to old-only names whose
deletion is no longer pending. -/
@[expose] def treeEditSavedNames (oldE newE : Finset ℕ) (rest : List TreeChange) : Finset ℕ :=
  (oldE \ newE).filter fun e => TreeChange.delete e ∉ rest

/-- Insertion leaves the set of saved deletion records unchanged. -/
theorem treeEditSavedNames_insert (oldE newE : Finset ℕ) (e : ℕ) (rest : List TreeChange) :
    treeEditSavedNames oldE newE (.insert e :: rest) = treeEditSavedNames oldE newE rest := by
  ext f
  simp [treeEditSavedNames]

/-- Consuming a deletion adds its now-saved record to the set. -/
theorem treeEditSavedNames_delete {oldE newE : Finset ℕ} {e : ℕ} {rest : List TreeChange}
    (he : e ∈ oldE \ newE) (hfresh : TreeChange.delete e ∉ rest) :
    treeEditSavedNames oldE newE rest =
      insert e (treeEditSavedNames oldE newE (.delete e :: rest)) := by
  ext f
  by_cases h : f = e
  · subst f
    simp [treeEditSavedNames, he, hfresh]
  · simp [treeEditSavedNames, h]

/-- The saved set is empty before the first packed edit. -/
theorem TreeEditDifference.savedNames_start {oldE newE : Finset ℕ} {changes : List TreeChange}
    (h : TreeEditDifference oldE newE changes) :
    treeEditSavedNames oldE newE changes = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨ho, hnot⟩ := Finset.mem_filter.mp he
  exact hnot (h.perm.mem_iff.mpr (treeEdit_delete_mem_diff.mpr ho))

/-- At the end of the packed list every old-only account has been saved. -/
theorem treeEditSavedNames_finish (oldE newE : Finset ℕ) :
    treeEditSavedNames oldE newE [] = oldE \ newE := by
  simp [treeEditSavedNames]

/-- No remaining deletion repeats the current name, so advancing the cursor
makes precisely its account newly saved. -/
theorem TreeEditDifference.savedNames_delete {oldE newE : Finset ℕ}
    {done rest : List TreeChange} {e : ℕ}
    (h : TreeEditDifference oldE newE (done ++ .delete e :: rest)) :
    treeEditSavedNames oldE newE rest =
      insert e (treeEditSavedNames oldE newE (.delete e :: rest)) := by
  have hnd := h.perm.nodup_iff.mpr (treeEdit_diff_nodup oldE newE).1
  exact treeEditSavedNames_delete (h.delete_mem_sdiff (by simp))
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1

/-- Packing puts all deletions before all insertions. -/
theorem TreeEditDifference.no_delete_after_insert {oldE newE : Finset ℕ}
    {processed rest : List TreeChange} {e j : ℕ}
    (h : TreeEditDifference oldE newE (processed ++ .insert e :: rest)) :
    TreeChange.delete j ∉ rest := by
  obtain ⟨deletes, inserts, _, _, hchanges⟩ := h
  obtain ⟨_, _, _, _, hrest⟩ := insertion_cursor_of_blocks hchanges.symm
  simp [hrest]

/-- At a packed insertion the processed graph is contained in the
target, and the edge at the cursor is still missing. -/
theorem TreeEditDifference.insert_cursor {oldE newE : Finset ℕ}
    {changes processed rest : List TreeChange} {e : ℕ}
    (h : TreeEditDifference oldE newE changes) (hs : changes = processed ++ .insert e :: rest) :
    applyTreeChanges oldE processed ⊆ newE ∧ e ∉ applyTreeChanges oldE processed ∧ e ∈ newE := by
  obtain ⟨ds, ins, hd, hi, hchanges⟩ := h
  obtain ⟨done, todo, hins, hdone, _⟩ := insertion_cursor_of_blocks (hchanges.symm.trans hs)
  have hiNd := hi.nodup_iff.mpr (Finset.nodup_toList _)
  rw [hins] at hiNd
  have hnot : e ∉ done := fun hm =>
    (List.nodup_append.mp hiNd).2.2 _ hm _ List.mem_cons_self rfl
  have hm (f : ℕ) (hf : f ∈ done ++ e :: todo) : f ∈ newE \ oldE :=
    Finset.mem_toList.mp (hi.mem_iff.mp (hins.symm ▸ hf))
  have hds : ds.toFinset = oldE \ newE := by ext f; simp [hd.mem_iff]
  have hset : applyTreeChanges oldE processed =
      (oldE \ (oldE \ newE)) ∪ done.toFinset := by
    rw [hdone]
    change List.foldl _ oldE (_ ++ _) = _
    rw [List.foldl_append]
    change applyTreeChanges (applyTreeChanges oldE (ds.map TreeChange.delete))
      (done.map TreeChange.insert) = _
    rw [apply_delete_names, apply_insert_names, hds]
  have he := Finset.mem_sdiff.mp (hm e (by simp))
  rw [hset]
  refine ⟨Finset.union_subset ?_ ?_, ?_, he.1⟩
  · intro f hf
    by_contra hnot
    obtain ⟨hfOld, hfDiff⟩ := Finset.mem_sdiff.mp hf
    exact hfDiff (Finset.mem_sdiff.mpr ⟨hfOld, hnot⟩)
  · intro f hf
    exact (Finset.mem_sdiff.mp (hm f (List.mem_append_left _ (List.mem_toFinset.mp hf)))).1
  · intro hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact he.2 (Finset.mem_sdiff.mp hf).1
    · exact hnot (List.mem_toFinset.mp hf)

/-- Read the tag and edge name at the cursor in register 6. -/
@[expose] def treeEditRead : Stmt :=
  .assign 7 (.load (.reg 6)) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 1)))

/-- One record is decoded in nine steps, without changing memory. -/
theorem treeEditRead_runs {w addr tag edge : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (ha : st.regs 6 = addr) (ht : ListAt st.mem addr [tag, edge])
    (hw : addr + 1 < 2 ^ w) :
    ∃ out, Runs w p ω treeEditRead st .normal out 9 ∧
      out.regs 7 = tag ∧ out.regs 8 = edge ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 7 → r ≠ 8 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 7 tag }
  let out := { mid with regs := Function.update mid.regs 8 edge }
  have htag : st.mem addr = tag := by simpa using ht 0 (by simp)
  have hedge : st.mem (addr + 1) = edge := ht 1 (by simp)
  have hone : 1 < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 7 (.load (.reg 6))) st .normal mid 3 :=
    runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, ha, htag], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 1)))) mid .normal out 5 :=
    runs_assign_iff.mpr ⟨edge, by simp [Expr.eval, mid, ha, hone, hw, hedge], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 3, 5, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro r h7 h8
  simp [out, mid, Function.update_of_ne, h7, h8]

end MinCostFlow.MinRatio
