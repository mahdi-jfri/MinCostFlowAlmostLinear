module

public import MinCostFlow.MinRatio.PathPayloadLayout

/-!
# Reading the Section 6 path payload

Tree-operation contracts pass edge values and lazy tags through the
fixed-point layouts. These readers recover exactly the values described
by those layouts. In particular, a lazy tag reads both the signed flow
change and the separate detector change. The path summary reader retains
the distinction between an empty detector and a detector whose value is zero.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Decode the two integer blocks of a lazy path tag. -/
def readPathTag (mem : ℕ → ℕ) (a h L : ℕ) : PathTag :=
  ⟨Num.intVal mem a h L, Num.intVal mem (a + L) h L⟩

/-- Decode a vertex or edge value at the operation boundary. -/
def readPathEdge (mem : ℕ → ℕ) (a h L : ℕ) : Option PathEdgeValue :=
  if mem a = 0 then none else some
    ⟨mem (a + 1) == 1,
      Num.intVal mem (a + 2) h L,
      Num.intVal mem (a + 2 + L) h L,
      Num.intVal mem (a + 2 + 2 * L) h L,
      Num.intVal mem (a + 2 + 3 * L) h L⟩

/-- Decode a path summary, including the empty-path detector tag. -/
def readPathSummary (mem : ℕ → ℕ) (a h L : ℕ) : PathSummary :=
  ⟨Num.intVal mem a h L, Num.intVal mem (a + L) h L,
    if mem (a + 2 * L) = 0 then none else some (Num.intVal mem (a + 2 * L + 1) h L)⟩

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

private theorem read_direction_bit (forward : Bool) :
    ((if forward then 1 else 0 : ℕ) == 1) = forward := by
  cases forward <;> rfl

/-- A stored lazy tag is recovered exactly, in both coordinates. -/
theorem readPathTag_eq {mem : ℕ → ℕ} {a h L : ℕ} {tag : PathTag}
    (ht : PathTagAt mem a h L tag) : readPathTag mem a h L = tag := by
  apply PathTag.ext
  · exact ht.1.2
  · exact ht.2.2

/-- Reading a stored edge value recovers its direction and all four fields. -/
theorem readPathEdge_eq {mem : ℕ → ℕ} {a h L : ℕ} {value : Option PathEdgeValue}
    (hv : PathEdgeAt mem a h L value) : readPathEdge mem a h L = value := by
  cases value with
  | none =>
    change mem a = 0 at hv
    simp only [readPathEdge, hv, ↓reduceIte]
  | some value =>
    rcases hv with ⟨htag, hdir, hg, hl, hf, hd⟩
    simp only [readPathEdge, htag, Nat.one_ne_zero, ↓reduceIte, hdir, read_direction_bit,
      hg.2, hl.2, hf.2, hd.2]

/-- Reading a stored summary preserves its optional detector exactly. -/
theorem readPathSummary_eq {mem : ℕ → ℕ} {a h L : ℕ} {summary : PathSummary}
    (hs : PathSummaryAt mem a h L summary) : readPathSummary mem a h L = summary := by
  rcases summary with ⟨gradient, length, detector⟩
  rcases hs with ⟨hg, hl, hd⟩
  cases detector with
  | none =>
    change mem (a + 2 * L) = 0 at hd
    simp only [readPathSummary, hg.2, hl.2, hd, ↓reduceIte]
  | some detector =>
    simp only [readPathSummary, hg.2, hl.2, hd.1, Nat.one_ne_zero, ↓reduceIte, hd.2.2]

/-- Tag-layout validity is exactly validity of the two numeric blocks
when the tag is read from those blocks. -/
theorem pathTagAt_read_iff (mem : ℕ → ℕ) (a h L : ℕ) :
    PathTagAt mem a h L (readPathTag mem a h L) ↔
      Num.Valid mem a h L ∧ Num.Valid mem (a + L) h L := by
  constructor
  · intro ht
    exact ⟨ht.1.1, ht.2.1⟩
  · rintro ⟨hf, hd⟩
    exact ⟨⟨hf, rfl⟩, ⟨hd, rfl⟩⟩

end MinCostFlow.MinRatio
