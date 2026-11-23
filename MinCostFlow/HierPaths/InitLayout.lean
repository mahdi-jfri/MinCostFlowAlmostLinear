module

public import MinCostFlow.HierPaths.InitProg

/-!
# Writing a block section by section

The builder of the block of `Init` writes the `csrList` of the sections of
`HierConcrete.encode`: first the offset table, then each section at its offset. This file gives
the memory lemma it needs: `listAt_csrList_of` says that the offsets at `a` and each list at its
offset after them make the whole `csrList` at `a`. Nine of the 24 sections of the initial block
are all zero (`initConcrete_sections_zero`), so the builder need not write them: memory above
the heap pointer is zero (`listAt_of_zero`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- The data part of `k + 1` lists is that of the first `k`, then the last. -/
theorem csrData_succ (k : ℕ) (f : ℕ → List ℕ) : csrData (k + 1) f = csrData k f ++ f k := by
  simp [csrData, List.range_succ, List.flatMap_append]

theorem length_csrData_eq (k : ℕ) (f : ℕ → List ℕ) :
    (csrData k f).length = ((List.range k).map fun j => (f j).length).sum := by
  induction k with
  | zero => simp [csrData]
  | succ k ih => rw [csrData_succ, List.length_append, ih, List.range_succ]; simp

/-- **The data part from its lists.** If list `i` is in memory at `a` plus the total length of
the lists before it, for every `i < k`, then the data part of `csrList k f` is at `a`. -/
theorem listAt_csrData_of {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ}
    (h : ∀ i < k, ListAt mem (a + ((List.range i).map fun j => (f j).length).sum) (f i)) :
    ListAt mem a (csrData k f) := by
  induction k with
  | zero => intro i hi; simp [csrData] at hi
  | succ k ih =>
    rw [csrData_succ, listAt_append]
    refine ⟨ih fun i hi => h i (by omega), ?_⟩
    rw [length_csrData_eq]
    exact h k (by omega)

/-- **A `csrList` from its offsets and lists.** The offsets at `a`, and list `i` at
`a + (k + 1)` plus its offset for every `i < k`, give the whole `csrList k f` at `a`. -/
theorem listAt_csrList_of {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ}
    (hoff : ListAt mem a (csrOffsets k f))
    (h : ∀ i < k,
      ListAt mem (a + (k + 1) + ((List.range i).map fun j => (f j).length).sum) (f i)) :
    ListAt mem a (csrList k f) := by
  rw [csrList, listAt_append, length_csrOffsets]
  exact ⟨hoff, listAt_csrData_of h⟩

/-- **A block from its offsets and sections**, the form of `listAt_csrList_of` for
`layoutList`. -/
theorem listAt_layoutList_of {mem : ℕ → ℕ} {a : ℕ} {bs : List (List ℕ)}
    (hoff : ListAt mem a (csrOffsets bs.length fun i => bs.getD i []))
    (h : ∀ i < bs.length, ListAt mem (a + (bs.length + 1) +
      ((List.range i).map fun j => (bs.getD j []).length).sum) (bs.getD i [])) :
    ListAt mem a (layoutList bs) :=
  listAt_csrList_of hoff h

/-- **The offsets from their values.** If word `a + i` holds the total length of the lists before
list `i`, for every `i ≤ k`, then the offsets of `csrList k f` are at `a`. -/
theorem listAt_csrOffsets_of {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ}
    (h : ∀ i ≤ k, mem (a + i) = ((List.range i).map fun j => (f j).length).sum) :
    ListAt mem a (csrOffsets k f) := by
  intro i hi
  rw [length_csrOffsets] at hi
  simp only [csrOffsets, List.getElem_map, List.getElem_range]
  exact h i (by omega)

/-- **A block from the starts of its sections.** Let `e i` be the start of section `i` relative
to the end `a + (k + 1)` of the offsets, with `e 0 = 0` and `e (i + 1) = e i + |section i|`. If
word `a + i` holds `e i` for `i ≤ k` and section `i` is at `a + (k + 1) + e i`, then the block is
at `a`. This is the form a builder meets when it writes the sections one after the other and
records each start. -/
theorem listAt_layoutList_of_starts {mem : ℕ → ℕ} {a : ℕ} {bs : List (List ℕ)} {e : ℕ → ℕ}
    (he0 : e 0 = 0) (hes : ∀ i < bs.length, e (i + 1) = e i + (bs.getD i []).length)
    (hoff : ∀ i ≤ bs.length, mem (a + i) = e i)
    (hsec : ∀ i < bs.length, ListAt mem (a + (bs.length + 1) + e i) (bs.getD i [])) :
    ListAt mem a (layoutList bs) := by
  have hsum : ∀ i ≤ bs.length,
      e i = ((List.range i).map fun j => (bs.getD j []).length).sum := by
    intro i hi
    induction i with
    | zero => simp [he0]
    | succ i ih =>
      rw [hes i (by omega), ih (by omega), List.range_succ]
      simp
  refine listAt_layoutList_of (listAt_csrOffsets_of fun i hi => ?_) fun i hi => ?_
  · rw [hoff i hi, hsum i hi]
  · rw [← hsum i hi.le]
    exact hsec i hi

/-- Memory that is zero from `a` on holds, at every `c ≥ a`, every list of zeros. -/
theorem listAt_of_zero {mem : ℕ → ℕ} {a c : ℕ} (hz : ZeroFrom mem a) (hc : a ≤ c)
    {l : List ℕ} (hl : ∀ y ∈ l, y = 0) : ListAt mem c l := by
  intro i hi
  rw [hl _ (List.getElem_mem hi)]
  exact hz (c + i) (by omega)

/-- **The zero sections of the initial block.** In the block of `initConcrete S a s` with
`s.Vhat = ∅`, the sections of the failed, globally lost, ineligible, deleted and pruned bits,
of the two cursor arrays, and the two scratch areas are lists of zeros: in `DelState.init`
these sets are empty and the cursors are zero. -/
theorem initConcrete_sections_zero (S : StaticData) (a : ℕ) {s : PathDSAbsState}
    (hV : s.Vhat = ∅) :
    ∀ i ∈ [13, 14, 15, 16, 17, 20, 21, 22, 23],
      ∀ y ∈ (initConcrete S a s).sections.getD i [], y = 0 := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HierConcrete.sections, initConcrete, DelState.init, LossState.init, hV, bitsList,
      tabList, List.mem_replicate]

end MinCostFlow.HierPaths
