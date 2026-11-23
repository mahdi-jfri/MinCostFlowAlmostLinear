module

public import MinCostFlow.HierPaths.Layout

/-!
# Writing into the block of the path data structure

The `Delete` program changes the block of `HierPaths/Layout.lean` in place: it sets bits, bumps
counters and moves cursors. Every such change writes one word and keeps the length of every
section, so the offsets stay the same. This file proves the write lemmas that the program uses:

* `listAt_set`: writing word `k` of a list in memory gives the list with entry `k` replaced;
* `csrList_set`: replacing entry `k` of list `i` of a `csrList` replaces one word of it;
* `bitsList_set`, `tabList_set`: setting one bit or one entry of a table;
* `listAt_layout_write`: writing word `k` of section `i` of a block gives the block whose section
  `i` has entry `k` replaced. The address is the one a program computes, from the offset at
  `b + i` (`listAt_section`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Writing word `k` of a list in memory. -/
theorem listAt_set {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l) (k v : ℕ) :
    ListAt (Function.update mem (a + k) v) a (l.set k v) := by
  intro i hi
  rw [List.length_set] at hi
  rw [List.getElem_set]
  by_cases hik : k = i
  · subst hik; simp
  · rw [Function.update_of_ne (by omega), if_neg hik]; exact h i hi

private theorem csrData_split' (k : ℕ) (f : ℕ → List ℕ) {i : ℕ} (hi : i < k) :
    csrData k f = csrData i f ++ (f i ++
      (List.range (k - (i + 1))).flatMap fun j => f (i + 1 + j)) := by
  have h1 : csrData (i + 1) f = csrData i f ++ f i := by
    simp [csrData, List.range_succ, List.flatMap_append]
  have hk : k = (i + 1) + (k - (i + 1)) := by omega
  have h2 : csrData k f = csrData (i + 1) f ++
      (List.range (k - (i + 1))).flatMap fun j => f (i + 1 + j) := by
    unfold csrData
    conv_lhs => rw [hk, List.range_add, List.flatMap_append, List.flatMap_map]
  rw [h2, h1, List.append_assoc]

private theorem csrData_congr {k : ℕ} {f g : ℕ → List ℕ} (h : ∀ j < k, f j = g j) :
    csrData k f = csrData k g := by
  unfold csrData
  exact List.flatMap_congr fun j hj => h j (List.mem_range.mp hj)

private theorem csrOffsets_congr {k : ℕ} {f g : ℕ → List ℕ}
    (h : ∀ j < k, (f j).length = (g j).length) : csrOffsets k f = csrOffsets k g := by
  unfold csrOffsets
  refine List.map_congr_left fun i hi => ?_
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hi
  exact h j (by have := List.mem_range.mp hj; omega)

private theorem length_csrData' (i : ℕ) (f : ℕ → List ℕ) :
    (csrData i f).length = ((List.range i).map fun j => (f j).length).sum := by
  simp [csrData, List.length_flatMap]

/-- Replacing entry `k` of list `i` of a `csrList` replaces one word of it. -/
theorem csrList_set {n : ℕ} (f : ℕ → List ℕ) {i : ℕ} (hi : i < n) {k : ℕ}
    (hk : k < (f i).length) (v : ℕ) :
    csrList n (Function.update f i ((f i).set k v)) =
      (csrList n f).set (n + 1 + ((List.range i).map fun j => (f j).length).sum + k) v := by
  have hlen : ∀ j < n, (Function.update f i ((f i).set k v) j).length = (f j).length := by
    intro j _
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
  unfold csrList
  rw [csrOffsets_congr hlen, csrData_split' n _ hi, csrData_split' n f hi]
  have hpre : csrData i (Function.update f i ((f i).set k v)) = csrData i f :=
    csrData_congr fun j hj => Function.update_of_ne (by omega) _ _
  have hpost : ((List.range (n - (i + 1))).flatMap fun j =>
      Function.update f i ((f i).set k v) (i + 1 + j)) =
      (List.range (n - (i + 1))).flatMap fun j => f (i + 1 + j) :=
    List.flatMap_congr fun j _ => Function.update_of_ne (by omega) _ _
  rw [hpre, hpost, Function.update_self]
  have e1 : n + 1 + ((List.range i).map fun j => (f j).length).sum + k =
      (csrOffsets n f).length + ((csrData i f).length + k) := by
    rw [length_csrOffsets, length_csrData']; omega
  rw [e1, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_left _ _ hk]

/-- Setting one bit. -/
theorem bitsList_set (n : ℕ) (f : ℕ → Bool) (i : ℕ) (c : Bool) :
    (bitsList n f).set i (if c then 1 else 0) = bitsList n (Function.update f i c) := by
  unfold bitsList
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  rw [List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Function.update_of_ne (Ne.symm hij)]

/-- Setting one entry of a table. -/
theorem tabList_set (n : ℕ) (f : ℕ → ℕ) (i v : ℕ) :
    (tabList n f).set i v = tabList n (Function.update f i v) := by
  unfold tabList
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  rw [List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Function.update_of_ne (Ne.symm hij)]

/-- **Writing word `k` of section `i` of a block.** The address is the start of section `i`
(read at `b + i`) plus `k`, and the block afterwards has section `i` with entry `k`
replaced. -/
theorem listAt_layout_write {mem : ℕ → ℕ} {b : ℕ} {bs : List (List ℕ)}
    (h : ListAt mem b (layoutList bs)) {i : ℕ} (hi : i < bs.length) {k : ℕ}
    (hk : k < (bs.getD i []).length) (v : ℕ) :
    ListAt (Function.update mem (b + (bs.length + 1) + mem (b + i) + k) v) b
      (layoutList (bs.set i ((bs.getD i []).set k v))) := by
  have hoff := csrList_offset h hi.le
  have hset : layoutList (bs.set i ((bs.getD i []).set k v)) =
      (layoutList bs).set (bs.length + 1 + ((List.range i).map fun j =>
        (bs.getD j []).length).sum + k) v := by
    unfold layoutList
    rw [← csrList_set (fun j => bs.getD j []) hi hk v, List.length_set]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [List.getD_eq_getElem?_getD, hi]
    · rw [Function.update_of_ne hj]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hj]
  rw [hset, hoff]
  have e : b + (bs.length + 1) + ((List.range i).map fun j => (bs.getD j []).length).sum + k =
      b + (bs.length + 1 + ((List.range i).map fun j => (bs.getD j []).length).sum + k) := by
    omega
  rw [e]
  exact listAt_set h _ v

end MinCostFlow.HierPaths

end
