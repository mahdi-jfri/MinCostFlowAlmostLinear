module

public import MinCostFlow.SparseCore.Program.ContractOrder
public import WordRAM.DataStructure
public import Mathlib.Data.Nat.Log

/-!
# The contract of the order store

The sparse-core program keeps an order of ends at each vertex of its input graph and of each
output graph. The order store is the piece that keeps one such order. Its abstract state is the order `ord : ℕ → List End`.

Operations:
* `0` edit `[handle, edits, words, heap]`: apply the edits stored at `edits` (`OrdEditsAt`).
* `1` list `[handle, v, heap]`: write the list at `v` at `heap` (a length and then the keys).
* `2` next `[handle, v, key, heap]`: write at `heap` the key of the end after the end `key`
  in the cyclic list at `v`.

A program keeps each list as a balanced or splay sequence, with a table from end keys to nodes,
and a table from vertices to sequences. Moving a set of ends sorts them by position, which is why
an edit costs a factor `log (eCap + 2)` more than its words. Moving the complement of a set at `v`
moves the listed ends to a new sequence and gives the old sequence to `v'`. Only definitions are
here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- The words of an end list written at `a`: its length and then its keys. -/
def EndListAt (mem : ℕ → ℕ) (a : ℕ) (xs : List End) : Prop :=
  mem a = xs.length ∧ ∀ i < xs.length, mem (a + 1 + i) = endKey (xs.getD i (0, true))

/-- Every edit of `edits` names vertices below `vCap` and edges below `eCap`. -/
def OrdEditsWithin (vCap eCap : ℕ) (edits : List OrdEdit) : Prop :=
  ∀ edit ∈ edits, match edit with
    | .dropEdge e => e < eCap
    | .moveEnds v v' sel _ => v < vCap ∧ v' < vCap ∧ ∀ x ∈ sel, x.1 < eCap
    | .insertBefore v x y => v < vCap ∧ x.1 < eCap ∧ ∀ y' ∈ y, y'.1 < eCap
    | .rotateTo v y => v < vCap ∧ y.1 < eCap

/-- The order `ord` has no repeated end, names only vertices below `vCap` and edges below
`eCap`. -/
def OrdWithin (vCap eCap : ℕ) (ord : ℕ → List End) : Prop :=
  (∀ v, (ord v).Nodup) ∧ (∀ v, vCap ≤ v → ord v = []) ∧ ∀ v, ∀ x ∈ ord v, x.1 < eCap

/-- The log factor of one step of the order store. -/
def ordStoreLog (eCap : ℕ) : ℕ := Nat.log 2 (eCap + 2) + 1

/-- The order store. Initialization `[ord, heap]` reads a whole order (`OrdListAt`). The cost
constant `mul` is free of the input. -/
def ordStoreContract (vCap eCap mul : ℕ) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (ℕ → List End) where
  initPre args mem := ∃ ord heap words, args = [ord, heap] ∧
    OrdListAt mem ord (readOrd mem ord) words ∧ ord + words ≤ heap ∧
    OrdWithin vCap eCap (readOrd mem ord)
  initPost args mem s _ := s = readOrd mem (args.getD 0 0)
  initCost args mem := mul * (1 + ordRecordsWords (readOrdRecordsAt mem (args.getD 0 0))) *
    ordStoreLog eCap
  initSpace args _ := allocation 3 args
  pre i s args mem := match i with
    | 0 => ∃ handle edits words heap, args = [handle, edits, words, heap] ∧
        OrdEditsAt mem edits (readOrdEdits mem edits) words ∧ edits + words ≤ heap ∧
        OrdEditsWithin vCap eCap (readOrdEdits mem edits) ∧
        OrdWithin vCap eCap (applyOrdEdits s (readOrdEdits mem edits))
    | 1 => ∃ handle v heap, args = [handle, v, heap] ∧ v < vCap
    | 2 => ∃ handle v key heap, args = [handle, v, key, heap] ∧ v < vCap ∧
        endOfKey key ∈ s v
    | _ => False
  post i s args mem s' mem' := match i with
    | 0 => s' = applyOrdEdits s (readOrdEdits mem (args.getD 1 0))
    | 1 => s' = s ∧ EndListAt mem' (args.getD 2 0) (s (args.getD 1 0))
    | 2 => s' = s ∧
        let xs := s (args.getD 1 0)
        mem' (args.getD 3 0) =
          endKey (xs.getD ((xs.idxOf (endOfKey (args.getD 2 0)) + 1) % xs.length) (0, true))
    | _ => False
  cost i s args _ := match i with
    | 0 => mul * (args.getD 2 0 + 1) * ordStoreLog eCap
    | 1 => mul * ((s (args.getD 1 0)).length + 1)
    | 2 => mul * ordStoreLog eCap
    | _ => 0
  space i s args _ := match i with
    | 0 => allocation 0 args
    | 1 => 1 + (s (args.getD 1 0)).length
    | 2 => 1
    | _ => 0

end MinCostFlow.SparseCore.Program
