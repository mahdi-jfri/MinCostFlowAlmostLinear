module

public import MinCostFlow.Bundle.Ordered
public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs

/-!
# Orders of ends in memory

The sparse-core tool with orders (`SparseCoreTool.initOrd`, `updateOrd`, `rot`) takes the order of
the ends at each vertex of its input graph, and returns the order at each vertex of each output
graph. This file fixes how a machine program receives and returns these orders.

* An end `x = (e, side)` is stored as the word `endKey x = 2 e + (0 if tail, 1 if head)`
  (`Bundle.endKey`); `endOfKey` reads it back.
* A whole order (`OrdListAt`) is a count `r` followed by `r` records `[v, len, keys…]`, one for
  each listed vertex. A vertex that has no record has the empty order. The initialization reads
  its input order in this form, and the readout of an output order writes it.
* A change of order (`OrdEditsAt`) is a count followed by edit records. An update receives the
  order after its batch as edits of the stored order, and returns for each branch the edits of
  its output order. Reading a whole order at every update would cost the size of the graph.

The edits (`OrdEdit`) act on the lists: drop the two ends of an edge, move the ends of a set
(or of its complement) from one vertex to the end of the list of another vertex, keeping their
order, insert an end before a given end (or at the back), and rotate a list to start at a given
end. `applyOrdEdits` applies them in order. Only definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- The end stored as the word `a`; the inverse of `endKey`. -/
def endOfKey (a : ℕ) : End := (a / 2, decide (a % 2 = 0))

/-! ## Whole orders -/

/-- The records `[v, len, keys…]` of `count` vertices from address `a`. -/
def readOrdRecords (mem : ℕ → ℕ) : ℕ → ℕ → List (ℕ × List End)
  | 0, _ => []
  | count + 1, a =>
    (mem a, (readList mem (a + 2) (mem (a + 1))).map endOfKey) ::
      readOrdRecords mem count (a + 2 + mem (a + 1))

/-- The order given by a list of records: the list of the first record of each vertex, and the
empty list at a vertex with no record. -/
def ordOfRecords (recs : List (ℕ × List End)) (v : ℕ) : List End :=
  ((recs.find? fun p => p.1 == v).map Prod.snd).getD []

/-- The number of words of a list of records. -/
def ordRecordsWords (recs : List (ℕ × List End)) : ℕ :=
  (recs.map fun p => 2 + p.2.length).sum

/-- The records of the whole order stored at `a`. -/
def readOrdRecordsAt (mem : ℕ → ℕ) (a : ℕ) : List (ℕ × List End) :=
  readOrdRecords mem (mem a) (a + 1)

/-- The whole order stored at `a`. -/
def readOrd (mem : ℕ → ℕ) (a : ℕ) : ℕ → List End :=
  ordOfRecords (readOrdRecordsAt mem a)

/-- Memory holds the order `ord` at `a` in `words` words: a count and one record per listed
vertex, with no vertex listed twice. -/
def OrdListAt (mem : ℕ → ℕ) (a : ℕ) (ord : ℕ → List End) (words : ℕ) : Prop :=
  ((readOrdRecordsAt mem a).map Prod.fst).Nodup ∧ readOrd mem a = ord ∧
    words = 1 + ordRecordsWords (readOrdRecordsAt mem a)

/-- The number of words of the order `ord` written with one record for each vertex of `V`. -/
def ordWordsOn (V : Finset ℕ) (ord : ℕ → List End) : ℕ :=
  1 + V.sum fun v => 2 + (ord v).length

/-! ## Edits of orders -/

/-- One edit of an order of ends. `moveEnds v v' sel false` moves the ends of `sel` at `v` to the
back of the list at `v'`; `moveEnds v v' sel true` moves the ends at `v` that are not in `sel`.
`insertBefore v x y` puts `x` before `y` at `v`, or at the back when `y = none` or `y` is not at
`v`. `rotateTo v y` makes the list at `v` start at `y` (no change when `y` is not at `v`). -/
inductive OrdEdit
  | dropEdge (e : ℕ)
  | moveEnds (v v' : ℕ) (sel : Finset End) (complement : Bool)
  | insertBefore (v : ℕ) (x : End) (y : Option End)
  | rotateTo (v : ℕ) (y : End)

/-- Insert `x` before `y` in `xs`, or at the back. -/
def insertBeforeList (x : End) (y : Option End) (xs : List End) : List End :=
  match y with
  | none => xs ++ [x]
  | some y => xs.take (xs.idxOf y) ++ x :: xs.drop (xs.idxOf y)

/-- Rotate `xs` to start at `y`; no change when `y ∉ xs`. -/
def rotateToList (y : End) (xs : List End) : List End :=
  if y ∈ xs then xs.drop (xs.idxOf y) ++ xs.take (xs.idxOf y) else xs

/-- The ends of `xs` that a move takes. -/
def movedBy (sel : Finset End) (complement : Bool) (x : End) : Bool :=
  if complement then !decide (x ∈ sel) else decide (x ∈ sel)

/-- Apply one edit. -/
def applyOrdEdit (ord : ℕ → List End) : OrdEdit → ℕ → List End
  | .dropEdge e => fun u => (ord u).filter fun x => x.1 != e
  | .moveEnds v v' sel c => fun u =>
    if u = v then (ord v).filter fun x => !movedBy sel c x
    else if u = v' then ord v' ++ (ord v).filter (movedBy sel c)
    else ord u
  | .insertBefore v x y => Function.update ord v (insertBeforeList x y (ord v))
  | .rotateTo v y => Function.update ord v (rotateToList y (ord v))

/-- Apply a list of edits in order. -/
def applyOrdEdits (ord : ℕ → List End) (edits : List OrdEdit) : ℕ → List End :=
  edits.foldl applyOrdEdit ord

/-- The encoding size of an edit: one, plus the size of the set of a move. -/
def OrdEdit.enc : OrdEdit → ℕ
  | .moveEnds _ _ sel _ => 1 + sel.card
  | _ => 1

/-- The encoding size of a list of edits. -/
def ordEditsEnc (edits : List OrdEdit) : ℕ := (edits.map OrdEdit.enc).sum

/-- Read one edit record at `a`: the edit and its number of words. Tag `0` is `dropEdge`
(`[0, e]`), tags `1` and `2` are `moveEnds` with the listed set or its complement
(`[tag, v, v', len, keys…]`), tag `3` is `insertBefore` (`[3, v, key x, 0 or key y + 1]`), and
every other tag is `rotateTo` (`[tag, v, key y]`). -/
def decodeOrdEdit (mem : ℕ → ℕ) (a : ℕ) : OrdEdit × ℕ :=
  if mem a = 0 then (.dropEdge (mem (a + 1)), 2)
  else if mem a = 1 ∨ mem a = 2 then
    (.moveEnds (mem (a + 1)) (mem (a + 2))
      ((readList mem (a + 4) (mem (a + 3))).map endOfKey).toFinset (decide (mem a = 2)),
      4 + mem (a + 3))
  else if mem a = 3 then
    (.insertBefore (mem (a + 1)) (endOfKey (mem (a + 2)))
      (if mem (a + 3) = 0 then none else some (endOfKey (mem (a + 3) - 1))), 4)
  else (.rotateTo (mem (a + 1)) (endOfKey (mem (a + 2))), 3)

/-- Read `count` edit records from `a`: the edits and their numbers of words. -/
def decodeOrdEdits (mem : ℕ → ℕ) : ℕ → ℕ → List OrdEdit × List ℕ
  | 0, _ => ([], [])
  | count + 1, a =>
    let d := decodeOrdEdit mem a
    let rest := decodeOrdEdits mem count (a + d.2)
    (d.1 :: rest.1, d.2 :: rest.2)

/-- The edits stored at `a` (a count, then the records). -/
def readOrdEdits (mem : ℕ → ℕ) (a : ℕ) : List OrdEdit :=
  (decodeOrdEdits mem (mem a) (a + 1)).1

/-- Memory holds the edits `edits` at `a` in `words` words, and the words are at most five times
the encoding size, plus one. -/
def OrdEditsAt (mem : ℕ → ℕ) (a : ℕ) (edits : List OrdEdit) (words : ℕ) : Prop :=
  readOrdEdits mem a = edits ∧ words = 1 + ((decodeOrdEdits mem (mem a) (a + 1)).2).sum ∧
    words ≤ 5 * ordEditsEnc edits + 1

/-! ## Ordered batches -/

/-- The orders `ord` before and `ord'` after the batch `U` are rotations of the graphs before and
after it, and the batch is ordered with split bound two. This is
one step of `OrderedUpTo`. -/
def OrderedBatch (G : MGraph) (U : List Update) (ord ord' : ℕ → List End) : Prop :=
  ∃ (ρ : Rotation G) (σ : Rotation (G.applyBatch U)),
    ρ.order = ord ∧ σ.order = ord' ∧ RotationBatch 2 U ρ σ

/-- The order `ord` is the order of a rotation of `G`. -/
def IsRotationOrder (G : MGraph) (ord : ℕ → List End) : Prop :=
  ∃ ρ : Rotation G, ρ.order = ord

end MinCostFlow.SparseCore.Program
