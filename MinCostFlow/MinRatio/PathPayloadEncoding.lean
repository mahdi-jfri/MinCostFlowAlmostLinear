module

public import MinCostFlow.MinRatio.PathPayloadLayout
import WordRAM.Memory
import WordRAM.Entry

/-!
# Encoding the path payload's operation arguments and answers

The Section 6 tree contract exchanges tags, edge values, and path summaries
in the fixed-point layouts. These encodings give actual word lists for
all three. Every numeric block uses `Num.encodeLimbs`, and decoding is
exact when its integer fits the chosen range. The list lengths give the
space needed for each argument or answer. No machine running time is
claimed for these mathematical encodings.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Encode the two integer coordinates of a lazy path tag. -/
def encodePathTag (h L : ℕ) (tag : PathTag) : List ℕ :=
  Num.encodeLimbs h L tag.flow ++ Num.encodeLimbs h L tag.detector

/-- Encode a vertex marker or an edge's direction and four integer blocks. -/
def encodePathEdge (h L : ℕ) : Option PathEdgeValue → List ℕ
  | none => [0]
  | some v => 1 :: (if v.forward then 1 else 0) ::
      (Num.encodeLimbs h L v.gradient ++ (Num.encodeLimbs h L v.length ++
        (Num.encodeLimbs h L v.flow ++ Num.encodeLimbs h L v.detector)))

/-- Encode the signed gradient, length, and optional maximum detector. -/
def encodePathSummary (h L : ℕ) (summary : PathSummary) : List ℕ :=
  Num.encodeLimbs h L summary.gradient ++ (Num.encodeLimbs h L summary.length ++
    (match summary.detector with
    | none => [0]
    | some z => 1 :: Num.encodeLimbs h L z))

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- A lazy tag has two fixed-size blocks. -/
theorem encodePathTag_length (h L : ℕ) (tag : PathTag) :
    (encodePathTag h L tag).length = 2 * L := by simp [encodePathTag, two_mul]

/-- An edge value has two header words and four numeric blocks. -/
theorem encodePathEdge_some_length (h L : ℕ) (value : PathEdgeValue) :
    (encodePathEdge h L (some value)).length = 2 + 4 * L := by
  simp only [encodePathEdge, List.length_cons, List.length_append, Num.encodeLimbs_length]
  omega

/-- A vertex marker fits within the reserved edge-value space as well. -/
theorem encodePathEdge_length_le (h L : ℕ) (value : Option PathEdgeValue) :
    (encodePathEdge h L value).length ≤ 2 + 4 * L := by
  cases value with
  | none => simp only [encodePathEdge, List.length_singleton]; omega
  | some v => exact le_of_eq (encodePathEdge_some_length h L v)

/-- Every summary fits within three blocks and its detector tag. -/
theorem encodePathSummary_length_le (h L : ℕ) (summary : PathSummary) :
    (encodePathSummary h L summary).length ≤ 3 * L + 1 := by
  cases hd : summary.detector <;>
    simp only [encodePathSummary, hd, List.length_append, Num.encodeLimbs_length,
      List.length_cons, List.length_nil] <;> omega

/-- Storing the tag encoding gives exactly its two payload coordinates. -/
theorem pathTagAt_of_listAt {mem : ℕ → ℕ} {a h L : ℕ} {tag : PathTag}
    (he : ListAt mem a (encodePathTag h L tag))
    (hf : Num.Fits h L tag.flow) (hd : Num.Fits h L tag.detector) :
    PathTagAt mem a h L tag := by
  rcases listAt_append.mp he with ⟨hfWords, hdWords⟩
  simp only [Num.encodeLimbs_length] at hdWords
  exact ⟨PathIntAt.of_encoding hfWords hf, PathIntAt.of_encoding hdWords hd⟩

/-- Storing an edge encoding recovers its complete four-field payload. -/
theorem pathEdgeAt_of_listAt {mem : ℕ → ℕ} {a h L : ℕ} {value : PathEdgeValue}
    (he : ListAt mem a (encodePathEdge h L (some value)))
    (hg : Num.Fits h L value.gradient) (hl : Num.Fits h L value.length)
    (hf : Num.Fits h L value.flow) (hd : Num.Fits h L value.detector) :
    PathEdgeAt mem a h L (some value) := by
  rcases listAt_cons.mp he with ⟨htag, he⟩
  rcases listAt_cons.mp he with ⟨hdir, he⟩
  rcases listAt_append.mp he with ⟨hgWords, he⟩
  simp only [Num.encodeLimbs_length] at he
  rcases listAt_append.mp he with ⟨hlWords, he⟩
  simp only [Num.encodeLimbs_length] at he
  rcases listAt_append.mp he with ⟨hfWords, hdWords⟩
  simp only [Num.encodeLimbs_length] at hdWords
  have hfAddr : a + 1 + 1 + L + L = a + 2 + 2 * L := by omega
  have hdAddr : a + 1 + 1 + L + L + L = a + 2 + 3 * L := by omega
  rw [hfAddr] at hfWords
  rw [hdAddr] at hdWords
  exact ⟨htag, hdir, PathIntAt.of_encoding hgWords hg, PathIntAt.of_encoding hlWords hl,
    PathIntAt.of_encoding hfWords hf, PathIntAt.of_encoding hdWords hd⟩

/-- Storing the absent detector still preserves gradient and length. -/
theorem pathSummaryAt_none_of_listAt {mem : ℕ → ℕ} {a h L : ℕ} {gradient length : ℤ}
    (he : ListAt mem a (encodePathSummary h L ⟨gradient, length, none⟩))
    (hg : Num.Fits h L gradient) (hl : Num.Fits h L length) :
    PathSummaryAt mem a h L ⟨gradient, length, none⟩ := by
  rcases listAt_append.mp he with ⟨hgWords, he⟩
  simp only [Num.encodeLimbs_length] at he
  rcases listAt_append.mp he with ⟨hlWords, htag⟩
  simp only [Num.encodeLimbs_length] at htag
  have haddr : a + L + L = a + 2 * L := by omega
  rw [haddr] at htag
  exact ⟨PathIntAt.of_encoding hgWords hg, PathIntAt.of_encoding hlWords hl,
    listAt_singleton.mp htag⟩

/-- A present detector is stored along with its two path sums. -/
theorem pathSummaryAt_some_of_listAt {mem : ℕ → ℕ} {a h L : ℕ} {gradient length detector : ℤ}
    (he : ListAt mem a (encodePathSummary h L ⟨gradient, length, some detector⟩))
    (hg : Num.Fits h L gradient) (hl : Num.Fits h L length) (hd : Num.Fits h L detector) :
    PathSummaryAt mem a h L ⟨gradient, length, some detector⟩ := by
  rcases listAt_append.mp he with ⟨hgWords, he⟩
  simp only [Num.encodeLimbs_length] at he
  rcases listAt_append.mp he with ⟨hlWords, he⟩
  simp only [Num.encodeLimbs_length] at he
  have haddr : a + L + L = a + 2 * L := by omega
  rw [haddr] at he
  rcases listAt_cons.mp he with ⟨htag, hdWords⟩
  exact ⟨PathIntAt.of_encoding hgWords hg, PathIntAt.of_encoding hlWords hl, htag,
    PathIntAt.of_encoding hdWords hd⟩

/-- Every fitting tag has an actual memory layout. -/
theorem exists_pathTagAt (h L : ℕ) (tag : PathTag)
    (hf : Num.Fits h L tag.flow) (hd : Num.Fits h L tag.detector) :
    ∃ mem, PathTagAt mem 0 h L tag := by
  exact ⟨_, pathTagAt_of_listAt (listAt_initMem _) hf hd⟩

/-- Every fitting edge value has an actual memory layout. -/
theorem exists_pathEdgeAt (h L : ℕ) (value : PathEdgeValue)
    (hg : Num.Fits h L value.gradient) (hl : Num.Fits h L value.length)
    (hf : Num.Fits h L value.flow) (hd : Num.Fits h L value.detector) :
    ∃ mem, PathEdgeAt mem 0 h L (some value) := by
  exact ⟨_, pathEdgeAt_of_listAt (listAt_initMem _) hg hl hf hd⟩

end MinCostFlow.MinRatio
