module

public import MinCostFlow.HierPaths.Model

/-!
# Encodings of arrays in memory

The layout of the path data structure (`HierPaths/Layout.lean`) writes all its arrays one after
the other, starting at the handle. This file gives the encodings it uses, each a list of words:

* `bitsList n f`: the bits `f 0, …, f (n - 1)` as `0` or `1`;
* `csrList k f`: the lists `f 0, …, f (k - 1)` in compressed form: `k + 1` start offsets
  (relative to the start of the data part), then the lists one after the other;
* `entryWords`: a support entry as three words, `[0, t, 0]` for a terminal and `[1, c, pos]` for
  a walk position.

It proves the read lemmas that programs use: `listAt_append` splits a list in memory at its
parts, `listAt_bitsList`, `csrList_offset` and `listAt_csrList_get` read a bit, an offset and an
element of a list of `csrList`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The bits `f 0, …, f (n - 1)` as words `0` or `1`. -/
def bitsList (n : ℕ) (f : ℕ → Bool) : List ℕ :=
  (List.range n).map fun i => if f i then 1 else 0

/-- The start offsets of the lists `f 0, …, f (k - 1)` in the data part, and its end. -/
def csrOffsets (k : ℕ) (f : ℕ → List ℕ) : List ℕ :=
  (List.range (k + 1)).map fun i => (((List.range i).map fun j => (f j).length).sum)

/-- The data part: the lists `f 0, …, f (k - 1)` one after the other. -/
def csrData (k : ℕ) (f : ℕ → List ℕ) : List ℕ :=
  (List.range k).flatMap f

/-- The lists `f 0, …, f (k - 1)` in compressed form: offsets, then data. -/
def csrList (k : ℕ) (f : ℕ → List ℕ) : List ℕ :=
  csrOffsets k f ++ csrData k f

/-- A support entry as three words. -/
def entryWords : SupportEntry → List ℕ
  | .term t => [0, t, 0]
  | .onWalk c pos => [1, c, pos]

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM

public section

/-- A concatenation is in memory exactly when both parts are, the second right after the
first. -/
theorem listAt_append {mem : ℕ → ℕ} {a : ℕ} {l₁ l₂ : List ℕ} :
    ListAt mem a (l₁ ++ l₂) ↔ ListAt mem a l₁ ∧ ListAt mem (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by rw [List.length_append]; omega)
      rwa [List.getElem_append_left hi] at this
    · have := h (l₁.length + i) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      rwa [Nat.add_assoc]
  · rintro ⟨h1, h2⟩ i hi
    by_cases hi1 : i < l₁.length
    · rw [List.getElem_append_left hi1]; exact h1 i hi1
    · rw [List.getElem_append_right (by omega)]
      have := h2 (i - l₁.length) (by rw [List.length_append] at hi; omega)
      have e : a + l₁.length + (i - l₁.length) = a + i := by omega
      rwa [e] at this

/-- A list in memory depends only on its own cells. -/
theorem listAt_congr {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ∀ i < l.length, mem (a + i) = mem' (a + i)) (hl : ListAt mem a l) : ListAt mem' a l :=
  fun i hi => (h i hi).symm.trans (hl i hi)

@[simp] theorem length_bitsList (n : ℕ) (f : ℕ → Bool) : (bitsList n f).length = n := by
  simp [bitsList]

/-- Reading a bit. -/
theorem listAt_bitsList {mem : ℕ → ℕ} {a n : ℕ} {f : ℕ → Bool} (h : ListAt mem a (bitsList n f))
    {i : ℕ} (hi : i < n) : mem (a + i) = if f i then 1 else 0 := by
  have := h i (by simpa using hi)
  simpa [bitsList] using this

@[simp] theorem length_csrOffsets (k : ℕ) (f : ℕ → List ℕ) : (csrOffsets k f).length = k + 1 := by
  simp [csrOffsets]

/-- Reading an offset. -/
theorem csrList_offset {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ} (h : ListAt mem a (csrList k f))
    {i : ℕ} (hi : i ≤ k) : mem (a + i) = ((List.range i).map fun j => (f j).length).sum := by
  have := (listAt_append.mp h).1 i (by simp; omega)
  simpa [csrOffsets] using this

private theorem csrData_split (k : ℕ) (f : ℕ → List ℕ) {i : ℕ} (hi : i < k) :
    ∃ rest, csrData k f = csrData i f ++ (f i ++ rest) := by
  have h1 : csrData (i + 1) f = csrData i f ++ f i := by
    simp [csrData, List.range_succ, List.flatMap_append]
  have hk : k = (i + 1) + (k - (i + 1)) := by omega
  refine ⟨(List.range (k - (i + 1))).flatMap fun j => f (i + 1 + j), ?_⟩
  have h2 : csrData k f = csrData (i + 1) f ++
      (List.range (k - (i + 1))).flatMap fun j => f (i + 1 + j) := by
    unfold csrData
    conv_lhs => rw [hk, List.range_add, List.flatMap_append, List.flatMap_map]
  rw [h2, h1, List.append_assoc]

private theorem length_csrData (i : ℕ) (f : ℕ → List ℕ) :
    (csrData i f).length = ((List.range i).map fun j => (f j).length).sum := by
  simp [csrData, List.length_flatMap]

/-- Reading the elements of list `i`: they start at the offset of list `i` in the data part. -/
theorem listAt_csrList_get {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ}
    (h : ListAt mem a (csrList k f)) {i : ℕ} (hi : i < k) :
    ListAt mem (a + (k + 1) + ((List.range i).map fun j => (f j).length).sum) (f i) := by
  have hd := (listAt_append.mp h).2
  obtain ⟨rest, hrest⟩ := csrData_split k f hi
  rw [length_csrOffsets, hrest] at hd
  have hd2 := (listAt_append.mp hd).2
  rw [length_csrData] at hd2
  exact (listAt_append.mp hd2).1

end

end MinCostFlow.HierPaths
