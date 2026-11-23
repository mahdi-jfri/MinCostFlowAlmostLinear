module

public import MinCostFlow.MinRatio.PathPayloadLayout
import MinCostFlow.MinRatio.PathPayloadEncoding
import WordRAM.Entry

/-!
# Numeric range conditions for the path-tree contract

The computational model (page 7) uses a fixed number of limbs for each
number. The conditions here say exactly that the integer payload fields
fit that format. They assert no forest or cycle-quality property.
Every fitting payload has a concrete encoding in the specified layout,
and every payload stored in that layout satisfies the same range condition.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Both coordinates of a lazy tag fit the chosen integer format. -/
def PathTagFits (h L : ℕ) (tag : PathTag) : Prop :=
  Num.Fits h L tag.flow ∧ Num.Fits h L tag.detector

/-- All four integer fields fit. Vertex markers have no integer fields. -/
def PathEdgeFits (h L : ℕ) : Option PathEdgeValue → Prop
  | none => True
  | some v => Num.Fits h L v.gradient ∧ Num.Fits h L v.length ∧
      Num.Fits h L v.flow ∧ Num.Fits h L v.detector

/-- The two path sums and any present detector fit their blocks. -/
def PathSummaryFits (h L : ℕ) (summary : PathSummary) : Prop :=
  Num.Fits h L summary.gradient ∧ Num.Fits h L summary.length ∧
    match summary.detector with
    | none => True
    | some z => Num.Fits h L z

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- Strict headroom on both sides of the signed range allows a reversal
without changing the number of limbs. -/
theorem pathEdgeFits_reverse_of_headroom {h L : ℕ} {value : PathEdgeValue}
    (hf : PathEdgeFits h L (some value))
    (hg : -(Num.capacity h L : ℤ) < 2 * value.gradient)
    (hv : -(Num.capacity h L : ℤ) < 2 * value.flow) :
    PathEdgeFits h L (some value.reverse) := by
  obtain ⟨⟨_, hg'⟩, hl, ⟨_, hv'⟩, hd⟩ := hf
  exact ⟨⟨by change -(Num.capacity h L : ℤ) ≤ 2 * -value.gradient; omega,
      by change 2 * -value.gradient < (Num.capacity h L : ℤ); omega⟩, hl,
    ⟨by change -(Num.capacity h L : ℤ) ≤ 2 * -value.flow; omega,
      by change 2 * -value.flow < (Num.capacity h L : ℤ); omega⟩, hd⟩

/-- A stored tag satisfies its numeric range conditions. -/
theorem PathTagAt.fits {mem : ℕ → ℕ} {a h L : ℕ} {tag : PathTag}
    (ht : PathTagAt mem a h L tag) : PathTagFits h L tag :=
  ⟨ht.1.fits, ht.2.fits⟩

/-- A stored edge or vertex satisfies its numeric range conditions. -/
theorem PathEdgeAt.fits {mem : ℕ → ℕ} {a h L : ℕ} {value : Option PathEdgeValue}
    (hv : PathEdgeAt mem a h L value) : PathEdgeFits h L value := by
  cases value with
  | none => trivial
  | some v =>
    rcases hv with ⟨_, _, hg, hl, hf, hd⟩
    exact ⟨hg.fits, hl.fits, hf.fits, hd.fits⟩

/-- A stored summary satisfies its numeric range conditions. -/
theorem PathSummaryAt.fits {mem : ℕ → ℕ} {a h L : ℕ} {summary : PathSummary}
    (hs : PathSummaryAt mem a h L summary) : PathSummaryFits h L summary := by
  rcases summary with ⟨gradient, length, detector⟩
  rcases hs with ⟨hg, hl, hd⟩
  cases detector with
  | none => exact ⟨hg.fits, hl.fits, trivial⟩
  | some z => exact ⟨hg.fits, hl.fits, hd.2.fits⟩

/-- Every fitting tag has a concrete layout. -/
theorem exists_pathTagAt_of_fits {h L : ℕ} {tag : PathTag} (ht : PathTagFits h L tag) :
    ∃ mem, PathTagAt mem 0 h L tag := exists_pathTagAt h L tag ht.1 ht.2

/-- Every fitting vertex or edge value has a concrete layout. -/
theorem exists_pathEdgeAt_of_fits {h L : ℕ} {value : Option PathEdgeValue}
    (hv : PathEdgeFits h L value) : ∃ mem, PathEdgeAt mem 0 h L value := by
  cases value with
  | none => exact ⟨fun _ => 0, rfl⟩
  | some v => exact exists_pathEdgeAt h L v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2

/-- Every fitting summary has a concrete layout, including an absent detector. -/
theorem exists_pathSummaryAt_of_fits {h L : ℕ} {summary : PathSummary}
    (hs : PathSummaryFits h L summary) : ∃ mem, PathSummaryAt mem 0 h L summary := by
  rcases summary with ⟨gradient, length, detector⟩
  cases detector with
  | none =>
    exact ⟨_, pathSummaryAt_none_of_listAt (WordRAM.listAt_initMem _) hs.1 hs.2.1⟩
  | some z =>
    exact ⟨_, pathSummaryAt_some_of_listAt (WordRAM.listAt_initMem _) hs.1 hs.2.1 hs.2.2⟩

end MinCostFlow.MinRatio
