module

public import MinCostFlow.HierPaths.LayoutEncode
public import WordRAM.DataStructure

/-!
# The memory layout of the path data structure

The data structure keeps everything in one block that starts at its handle `b`. The block is a
list of sections in the form of `csrList` (`HierPaths/LayoutEncode.lean`): first the start of
each section relative to the data part, then the sections one after the other. So a program finds
section `i` by reading the word at `b + i` (`listAt_section`).

The sections, in order (`sections`):

0. the header: `n`, `m`, the numbers of terminals, connectors and pairs, `x`, `b`, the leaf depth,
   `ξ`, `κ`, `lam`, `phiNum`, `phiDen`, `M`, and the number of deleted edges;
1. – 5. the tables `owner` (per terminal), `endA`, `endB`, `desig`, `pairOf` (per connector);
6. – 8. the lists `revList` (per edge), `termConns` (per terminal), `pairConns` (per pair), each in
   `csrList` form;
9. the support array of each vertex, each entry in three words (`entryWords`);
10. – 11. the vertices and the edges of the walk of each connector;
12. the pair index of siblings: for each depth `j` below the leaf depth, the table of
   `pairIdx j Y Z` over the children `Y` at depth `j + 1` and the positions `z` of `Z` among the
   children of the parent of `Y`;
13. – 17. the dynamic bits: directly failed and globally lost terminals, ineligible connectors,
   deleted edges, and the pruned set `Vhat`;
18. – 19. the loss counters `own` and `sum`, per depth and group;
20. – 21. the support cursors (per vertex) and the pair cursors (per pair);
22. the position array that loop erasure uses, all zero between calls;
23. the stack of `GetPath`, all zero between calls, with `stackWords` words per level.

The lengths of all sections depend only on the static part, so `Delete` and `GetPath` change the
block in place. The concrete state is a `HierModel` with a `ModelState`. Memory holds the abstract
state `s` as this concrete state when the block is in memory, the model state has `s` as its
abstract part, and the model relation `HierModel.Rel` holds (`hierRep`). The model potential
`B_d · t − 2E` of `HierPaths/PotentialBound.lean` is scaled to pay for RAM instructions. Both
depend only on the cells of the block (`hierRep_local`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- A list of sections in memory: the start of each section, then the sections. -/
def layoutList (bs : List (List ℕ)) : List ℕ :=
  csrList bs.length fun i => bs.getD i []

/-- The words of a table `f 0, …, f (len - 1)`. -/
def tabList (len : ℕ) (f : ℕ → ℕ) : List ℕ := (List.range len).map f

/-- The number of words per level of the stack of `GetPath`. -/
def stackWords : ℕ := 8

/-- The concrete state of the path data structure: the whole model with its state. -/
structure HierConcrete where
  /-- The static part of the model. -/
  H : HierModel
  /-- The model state. -/
  ms : ModelState

namespace HierConcrete

variable (x : HierConcrete)

/-- The number of vertices. -/
def n : ℕ := x.ms.abs.G.n

/-- The number of edges. -/
def m : ℕ := x.ms.abs.G.m

/-- The leaf depth of the hierarchy. -/
def depth : ℕ := leafDepth x.H.A.x x.H.A.b

/-- The header. -/
def header : List ℕ :=
  [x.n, x.m, x.H.A.C.numTerm, x.H.A.C.numConn, x.H.A.numPairs, x.H.A.x, x.H.A.b, x.depth,
    x.H.ξ, x.H.κ, x.H.lam, x.ms.abs.phiNum, x.ms.abs.phiDen, x.ms.abs.M, x.ms.st.deleted.card]

/-- The pair index table at depth `j`: entry `Y * br + z` is `pairIdx j Y Z` for the child `Z`
at position `z` among the children of the parent of `Y`, where `br` is the number of
children. -/
def pairIdxTable (j : ℕ) : List ℕ :=
  let br := branching x.H.A.x x.H.A.b j
  tabList (numGroups x.H.A.x x.H.A.b (j + 1) * br) fun i =>
    x.H.pairIdx j (i / br) (i / br / br * br + i % br)

/-- The sections of the block. -/
def sections : List (List ℕ) :=
  let A := x.H.A
  let C := A.C
  let st := x.ms.st
  [ x.header,
    tabList C.numTerm C.owner,
    tabList C.numConn C.endA,
    tabList C.numConn C.endB,
    tabList C.numConn C.desig,
    tabList C.numConn A.pairOf,
    csrList x.m A.revList,
    csrList C.numTerm A.termConns,
    csrList A.numPairs A.pairConns,
    csrList x.n fun w => (C.supportArray w).flatMap entryWords,
    csrList C.numConn fun c => (C.walk c).verts,
    csrList C.numConn fun c => (C.walk c).edges,
    csrList x.depth x.pairIdxTable,
    bitsList C.numTerm fun t => decide (t ∈ st.loss.failed),
    bitsList C.numTerm fun t => decide (t ∈ st.loss.glob),
    bitsList C.numConn fun c => decide (c ∈ st.inelig),
    bitsList x.m fun e => decide (e ∈ st.deleted),
    bitsList x.n fun w => decide (w ∈ x.ms.abs.Vhat),
    csrList (x.depth + 1) fun j => tabList (numGroups A.x A.b j) (st.loss.own j),
    csrList (x.depth + 1) fun j => tabList (numGroups A.x A.b j) (st.loss.sum j),
    tabList x.n st.supCur,
    tabList A.numPairs st.pairCur,
    List.replicate x.n 0,
    List.replicate ((x.depth + 2) * stackWords) 0 ]

/-- The words of the block. -/
def encode : List ℕ := layoutList x.sections

/-- The potential: `B_d · t − 2E` with `t` the number of deleted edges and `E` the event count. -/
def potential : ℕ := x.H.A.potential x.n x.H.ξ x.H.κ x.H.lam x.ms.st

end HierConcrete

/-- Convert model event charges to Word-RAM instruction charges. -/
def hierPhiScale : ℕ := 4096

/-- The representation of the path data structure for the hierarchy parameter `a`. -/
def hierRep (a : ℕ) : DSRep PathDSAbsState where
  τ := HierConcrete
  rep b s x mem := x.ms.abs = s ∧ x.H.Rel a x.ms ∧ ListAt mem b x.encode
  phi _ x _ := hierPhiScale * x.potential
  foot b x c := b ≤ c ∧ c < b + x.encode.length

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

public section

@[simp] theorem length_tabList (len : ℕ) (f : ℕ → ℕ) : (tabList len f).length = len := by
  simp [tabList]

/-- Reading an entry of a table. -/
theorem listAt_tabList {mem : ℕ → ℕ} {a len : ℕ} {f : ℕ → ℕ} (h : ListAt mem a (tabList len f))
    {i : ℕ} (hi : i < len) : mem (a + i) = f i := by
  have := h i (by simpa using hi)
  simpa [tabList] using this

/-- Section `i` of a block starts at the offset stored in word `i`, after the `bs.length + 1`
offsets. -/
theorem listAt_section {mem : ℕ → ℕ} {b : ℕ} {bs : List (List ℕ)} (h : ListAt mem b (layoutList bs))
    {i : ℕ} (hi : i < bs.length) :
    ListAt mem (b + (bs.length + 1) + mem (b + i)) (bs.getD i []) := by
  rw [csrList_offset h hi.le]
  exact listAt_csrList_get h hi

@[simp] theorem HierConcrete.length_sections (x : HierConcrete) : x.sections.length = 24 := rfl

/-- The representation is local: the block and the potential depend only on the cells of the
block. -/
theorem hierRep_local (a : ℕ) : (hierRep a).Local := by
  intro b s x mem mem' hfoot
  refine ⟨?_, rfl⟩
  rintro ⟨hs, hrel, hl⟩
  refine ⟨hs, hrel, listAt_congr (fun i hi => hfoot _ ⟨by omega, by omega⟩) hl⟩

end

end MinCostFlow.HierPaths
