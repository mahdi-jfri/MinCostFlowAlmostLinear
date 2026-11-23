module

public import MinCostFlow.SparseCore.Program.OrdStoreContract
public import WordRAM.DataStructure

/-!
# The tour operations that the output step uses

The output step of a branch (piece P7) changes the output graph `S_cur` by the batch `U_S`
(`buildUSOrd`), and it must return edits that turn the old output order into the new one. The
output order at a core vertex `r` is the core rotation list at `r` restricted to the edges of
`S_cur` (`BundleTreeState.outOrder`). The core rotation lists are kept by the tour structure of
piece P2, whose contract (`tourContract`) can also mark a set of ends. P7 keeps the ends
of `S_cur` marked. Then the new place of an inserted end `x` is just before the first marked end
after `x` in its list, and the tour finds that end in one step.

This file states the four tour operations that P7 uses, as a small interface. A module meeting it
is a parameter of P7. The abstract state `OutTourAbs` is the part of the tour state that P7 reads:
the core rotation lists `cord` (in the tour contract, `coreTour ord rf r` at each root `r`, and
`[]` elsewhere) and the marked ends.

1. `nextMarked [tourH, key, h]` (tour contract operation `8`): for an end `x` in the list
   `cord v`, writes `0` when no end of `cord v` is marked, and `1 + endKey y` when `y` is the
   first marked end after `x` in the cyclic list, where `x` itself comes last (so `y = x` when
   `x` is the only marked end). Cost `mul · log`. For an unmarked `x` this is the first marked
   end after `x` (`nextMarked_of_not_mem`).
2. `setMark [tourH, key, flag, h]` (operation `7`): marks (`flag = 1`) or unmarks (`flag = 0`) an
   end of a list. Cost `mul · log`.
3. `firstMarked [tourH, r, h]`: writes `0` when no end of `cord r` is marked, and `1 + endKey y`
   for the first marked end `y` of `cord r`. Cost `mul · log`. The tour contract does not have
   this operation. It is the first entry of operation `9` (`listMarked`), and a splay tree finds
   it in one search. It is needed because the output list at `r` must start where the model's
   list starts, and that start can move when the tour of `r` changes.
4. `listMarked [tourH, r, h]` (operation `9`): writes `(cord r).filter (· ∈ marked)` in
   `EndListAt` form. Cost `mul · (length + 1) · log`.

Every operation follows the calling convention of `WordRAM.DataStructure` (the last argument is
the heap pointer, a call writes only its footprint and new cells), and may change the concrete
state (a splay tree rotates on a search). The log factor is `ordStoreLog eCap`, which is the
factor `tourLog eCap` of the tour contract.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

@[expose] public section

/-- The part of the tour state that the output step reads: the core rotation list at each vertex
and the marked ends. -/
structure OutTourAbs where
  cord : ℕ → List End
  marked : Finset End

/-- The first end after `x` in the cyclic list `t` that meets `P`, or `none`. The end `x` itself
is not counted. -/
def cycNextWith (t : List End) (P : End → Bool) (x : End) : Option End :=
  (afterEnd x t).find? P

/-- The word that codes an optional end: `0` for `none` and `1 + endKey y` for `some y`. -/
def optEndWord : Option End → ℕ
  | none => 0
  | some y => 1 + endKey y

/-- The first marked end after `x` in the cyclic list `cord v`, where `x` itself comes last. -/
noncomputable def OutTourAbs.nextMarked (s : OutTourAbs) (v : ℕ) (x : End) : Option End :=
  open Classical in (afterEnd x (s.cord v) ++ [x]).find? fun z => decide (z ∈ s.marked)

/-- For an unmarked end `x`, `nextMarked` is the first marked end after `x`. -/
theorem OutTourAbs.nextMarked_of_not_mem (s : OutTourAbs) (v : ℕ) {x : End}
    (hx : x ∉ s.marked) :
    s.nextMarked v x = open Classical in cycNextWith (s.cord v) (fun z => decide (z ∈ s.marked)) x := by
  classical
  unfold OutTourAbs.nextMarked cycNextWith
  rw [List.find?_append]
  cases (afterEnd x (s.cord v)).find? (fun z => decide (z ∈ s.marked)) with
  | some y => rfl
  | none => simp [hx]

/-- The marked ends of the list at `r`, in order. -/
noncomputable def OutTourAbs.markedList (s : OutTourAbs) (r : ℕ) : List End :=
  open Classical in (s.cord r).filter fun z => decide (z ∈ s.marked)

/-- Mark (`flag = 1`) or unmark the end `x`. -/
noncomputable def OutTourAbs.setMark (s : OutTourAbs) (x : End) (flag : ℕ) : OutTourAbs :=
  open Classical in
  { s with marked := if flag = 1 then insert x s.marked else s.marked.erase x }

/-- Input-independent constants of a tour module: the cost multiplier and the heap space of a
query and of a list of length `len`. -/
structure OutTourSpec where
  mul : ℕ
  querySpace : ℕ
  listSpace : ℕ → ℕ
  querySpace_ge : 1 ≤ querySpace
  listSpace_ge : ∀ len, 1 + len ≤ listSpace len
  listSpace_mono : ∀ a b, a ≤ b → listSpace a ≤ listSpace b

/-- Procedures `nextMarkedIdx`, `setMarkIdx`, `firstMarkedIdx` and `listMarkedIdx` of program `p`
(at word size `w`, with caps `vCap` and `eCap`) meet the four tour operations of this file on the
representation `rep`, with the constants of `S`. -/
structure OutTourAt (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program)
    (nextMarkedIdx setMarkIdx firstMarkedIdx listMarkedIdx : ℕ) where
  rep : DSRep OutTourAbs
  rep_local : rep.Local
  nextMarked_runs : ∀ (tourH key v h : ℕ) (s : OutTourAbs) (tx : rep.τ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → key < 2 * eCap → key < 2 ^ w → v < vCap → h < 2 ^ w →
      endOfKey key ∈ s.cord v →
      rep.rep tourH s tx mem → (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.querySpace < 2 ^ w →
      ∃ body, p.procs[nextMarkedIdx]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, key, h] mem pos) o st' c ∧
        rep.rep tourH s tx' st'.mem ∧
        st'.mem h = optEndWord (s.nextMarked v (endOfKey key)) ∧
        h + 1 ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h S.querySpace mem o.value tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤ S.mul * ordStoreLog eCap + rep.phi tourH tx mem
  setMark_runs : ∀ (tourH key flag v h : ℕ) (s : OutTourAbs) (tx : rep.τ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → key < 2 * eCap → key < 2 ^ w → flag ≤ 1 → v < vCap → h < 2 ^ w →
      endOfKey key ∈ s.cord v →
      rep.rep tourH s tx mem → (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.querySpace < 2 ^ w →
      ∃ body, p.procs[setMarkIdx]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, key, flag, h] mem pos) o st' c ∧
        rep.rep tourH (s.setMark (endOfKey key) flag) tx' st'.mem ∧
        rep.Respects (rep.foot tourH tx) h S.querySpace mem o.value tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤ S.mul * ordStoreLog eCap + rep.phi tourH tx mem
  firstMarked_runs : ∀ (tourH r h : ℕ) (s : OutTourAbs) (tx : rep.τ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → r < vCap → h < 2 ^ w →
      rep.rep tourH s tx mem → (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.querySpace < 2 ^ w →
      ∃ body, p.procs[firstMarkedIdx]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, r, h] mem pos) o st' c ∧
        rep.rep tourH s tx' st'.mem ∧
        st'.mem h = optEndWord (s.markedList r).head? ∧
        h + 1 ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h S.querySpace mem o.value tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤ S.mul * ordStoreLog eCap + rep.phi tourH tx mem
  listMarked_runs : ∀ (tourH r h : ℕ) (s : OutTourAbs) (tx : rep.τ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → r < vCap → h < 2 ^ w →
      rep.rep tourH s tx mem → (∀ a, rep.foot tourH tx a → a < h) →
      ZeroFrom mem h → h + S.listSpace (s.markedList r).length < 2 ^ w →
      ∃ body, p.procs[listMarkedIdx]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, r, h] mem pos) o st' c ∧
        rep.rep tourH s tx' st'.mem ∧
        EndListAt st'.mem h (s.markedList r) ∧
        h + 1 + (s.markedList r).length ≤ o.value ∧
        rep.Respects (rep.foot tourH tx) h (S.listSpace (s.markedList r).length) mem o.value
          tourH tx' st'.mem ∧
        c + rep.phi tourH tx' st'.mem ≤
          S.mul * ((s.markedList r).length + 1) * ordStoreLog eCap + rep.phi tourH tx mem

end

end MinCostFlow.SparseCore.Program
