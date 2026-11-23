module

public import MinCostFlow.SparseCore.Program.TourMath
public import MinCostFlow.SparseCore.Program.OrdStoreContract

/-!
# The contract of the core rotation tour data structure

This file defines `tourContract`, the `WordRAM.DataStructure` specification for piece P2. Its abstract state `TourAbs` holds:

* an order of ends `ord : ℕ → List End`,
* a rooted forest `rf : RootedForest`, and
* an optional subset `marked : Finset End` of live open ends (initially empty; used e.g. to track
  `S_cur` for next-marked and restricted-tour queries).

For every core vertex `r ∈ rf.R`, `coreTour ord rf r` equals `(coreRotation ρ hG hF).order r`
(`coreTour_eq_coreRotation`).

Operations:
* `0` `applyEdits [handle, edits, words, heap]`: apply `OrdEditsAt` to `ord` (splitting `rf` on
  `moveEnds`), cost `O((words + 1) · log)`.
* `1` `cut [handle, e, newRoot, heap]`: remove forest edge `e` and add `newRoot` to `rf.R`, cost
  `O(log)`.
* `2` `link [handle, e, dropRoot, heap]`: add open edge `e` to `rf.F` and erase `dropRoot` from
  `rf.R`, cost `O(log)`.
* `3` `changeRoot [handle, oldRoot, newRoot, heap]`: move root from `oldRoot` to `newRoot` in the
  same forest component, cost `O(log)`.
* `4` `listTour [handle, r, heap]`: write `coreTour ord rf r` at `heap` (`EndListAt`), cost
  `O((|tour| + 1) · log)`.
* `5` `adjacent [handle, keyX, keyY, heap]`: write `1` at `heap` iff `keyY` immediately follows
  `keyX` in the cyclic core tour of its component, else `0`, cost `O(log)`.
* `6` `nextOpen [handle, keyX, heap]`: write the key of the cyclic successor of `keyX` in its
  core tour, cost `O(log)`.
* `7` `setMark [handle, keyX, flag, heap]`: insert (`flag = 1`) or erase (`flag = 0`) `keyX` in
  `marked`, cost `O(log)`.
* `8` `nextMarked [handle, keyX, heap]`: write `1 + keyY` for the first marked end cyclically
  after `keyX` in its component (or `0` if none), cost `O(log)`.
* `9` `listMarked [handle, r, heap]`: write `(coreTour ord rf r).filter (· ∈ marked)` at `heap`,
  exact space `1 + |out|`, cost `O((|out| + 1) · log)`.
* `10` `rootOf [handle, keyX, heap]`: write the root `r ∈ rf.R` of `keyX`'s component at `heap`,
  exact space `1`, cost `O(log)`.
* `11` `firstMarked [handle, r, heap]`: write `0` or `1 + endKey y` for the first marked end in
  `coreTour ord rf r`, cost `O(log)`.
* `12` `lenCoreTour [handle, r, heap]`: write `(coreTour ord rf r).length` at `heap`, exact space
  `1`, cost `O(log)`.
* `13` `vertOwner [handle, keyX, heap]`: write `ordSrc ord (endOfKey keyX)` at `heap`, exact space
  `1`, cost `O(1)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program

/-- Abstract state of the core rotation tour data structure: an order of ends `ord`, a rooted
forest `rf`, and a subset `marked` of live open ends. -/
structure TourAbs where
  ord : ℕ → List End
  rf : RootedForest
  marked : Finset End

/-- Validity invariant on `TourAbs` within vertex cap `vCap` and edge cap `eCap`. -/
structure TourValid (vCap eCap : ℕ) (s : TourAbs) : Prop where
  ordWithin : OrdWithin vCap eCap s.ord
  compat : OrdForestCompat s.ord s.rf.F
  roots_sub : s.rf.R ⊆ s.rf.F.V
  verts_lt : ∀ v ∈ s.rf.F.V, v < vCap
  unique_root : ∀ v ∈ s.rf.F.V, ∃! r, r ∈ s.rf.R ∧ s.rf.F.Connected v r
  marked_open : ∀ x ∈ s.marked, (∃ v, x ∈ s.ord v) ∧ x.1 ∉ s.rf.F.E

/-- Any valid graph with rotation `ρ` and rooted spanning forest `rf` within `(vCap, eCap)` gives
a valid `TourAbs` with empty `marked` set. -/
theorem tourValid_of_rotation {vCap eCap : ℕ} {G : MGraph} {rf : RootedForest}
    (ρ : Rotation G) (hG : G.IsValid) (hF : rf.IsRootedSpanningForestOf G)
    (hord : OrdWithin vCap eCap ρ.order) (hV : ∀ v ∈ G.V, v < vCap) :
    TourValid vCap eCap ⟨ρ.order, rf, ∅⟩ where
  ordWithin := hord
  compat := ordForestCompat_of_rotation ρ hG hF
  roots_sub := hF.2.1.symm ▸ hF.2.2.1
  verts_lt := fun v hv => hV v (hF.2.1 ▸ hv)
  unique_root := fun v hv => hF.2.2.2.1 v (hF.2.1 ▸ hv)
  marked_open := fun _ hx => (Finset.notMem_empty _ hx).elim

/-- The log factor of one step of the tour data structure. -/
def tourLog (eCap : ℕ) : ℕ := Nat.log 2 (eCap + 2) + 1

/-- Read a length-prefixed list of natural numbers at address `a`. -/
def readNatList (mem : ℕ → ℕ) (a : ℕ) : List ℕ :=
  readList mem (a + 1) (mem a)

/-- Build the initial `RootedForest` from an order-records list, a forest-edge list, and a root
list. Every vertex with nonempty order or listed as a root belongs to `F.V`. -/
noncomputable def initTourForest (recs : List (ℕ × List End)) (es rs : List ℕ) : RootedForest :=
  let ord := ordOfRecords recs
  let V := ((recs.filter fun p => !p.2.isEmpty).map Prod.fst).toFinset ∪ rs.toFinset
  { F :=
      { V := V
        E := es.toFinset
        tail := fun e => ordSrc ord (e, true)
        head := fun e => ordSrc ord (e, false) }
    R := rs.toFinset }

/-- Effect of one `OrdEdit` on `TourAbs`. A `moveEnds` edit splits the forest vertex `v` into `v`
and `v'` along the moved ends and adds a root on the side that no longer holds `rf.root v`. -/
noncomputable def tourApplyEdit (s : TourAbs) : OrdEdit → TourAbs
  | .dropEdge e =>
    { ord := applyOrdEdit s.ord (.dropEdge e)
      rf := s.rf
      marked := s.marked.filter fun x => x.1 != e }
  | .insertBefore v x y =>
    { ord := applyOrdEdit s.ord (.insertBefore v x y)
      rf := s.rf
      marked := s.marked }
  | .rotateTo v y =>
    { ord := applyOrdEdit s.ord (.rotateTo v y)
      rf := s.rf
      marked := s.marked }
  | .moveEnds v v' sel c =>
    open Classical in
    let moved := ((s.ord v).filter (movedBy sel c)).toFinset
    let St := (moved.filter fun x => x.2).image Prod.fst
    let Sh := (moved.filter fun x => !x.2).image Prod.fst
    let F' := s.rf.F.applyUpdate (.split v v' St Sh)
    let r := s.rf.root v
    let newRoot := if F'.Connected v r then v' else v
    { ord := applyOrdEdit s.ord (.moveEnds v v' sel c)
      rf := ⟨F', insert newRoot s.rf.R⟩
      marked := s.marked }

/-- Effect of a list of `OrdEdit`s on `TourAbs`. -/
noncomputable def tourApplyEdits (s : TourAbs) (edits : List OrdEdit) : TourAbs :=
  edits.foldl tourApplyEdit s

/-- Precondition for a single `OrdEdit` on a valid `TourAbs`. -/
def TourEditValid (vCap eCap : ℕ) (s : TourAbs) : OrdEdit → Prop
  | .dropEdge e => e < eCap ∧ e ∉ s.rf.F.E
  | .insertBefore v x y =>
    v < vCap ∧ v ∈ s.rf.F.V ∧ x.1 < eCap ∧ x.1 ∉ s.rf.F.E ∧ (∀ u, x ∉ s.ord u) ∧
      ∀ y' ∈ y, y'.1 < eCap
  | .rotateTo v y => v < vCap ∧ y.1 < eCap
  | .moveEnds v v' sel _ =>
    v < vCap ∧ v' < vCap ∧ v ≠ v' ∧ v ∈ s.rf.F.V ∧ v' ∉ s.rf.F.V ∧ s.ord v' = [] ∧
      ∀ x ∈ sel, x.1 < eCap

/-- Step-by-step validity of a list of `OrdEdit`s on `TourAbs`. -/
def TourEditsValid (vCap eCap : ℕ) : TourAbs → List OrdEdit → Prop
  | _, [] => True
  | s, e :: es => TourEditValid vCap eCap s e ∧ TourEditsValid vCap eCap (tourApplyEdit s e) es

/-- Cut forest edge `e` and make `newRoot` the root of the newly detached component. -/
def tourCut (s : TourAbs) (e newRoot : ℕ) : TourAbs :=
  { s with rf := ⟨eraseForestEdge s.rf.F e, insert newRoot s.rf.R⟩ }

/-- Link open edge `e` (connecting two distinct forest components) into `rf.F` and erase
`dropRoot` from `rf.R`, unmarking both ends of `e`. -/
noncomputable def tourLink (s : TourAbs) (e dropRoot : ℕ) : TourAbs :=
  { ord := s.ord
    rf := ⟨addForestEdge s.rf.F e (ordSrc s.ord (e, true)) (ordSrc s.ord (e, false)),
      s.rf.R.erase dropRoot⟩
    marked := s.marked.filter fun x => x.1 != e }

/-- Move a component root from `oldRoot` to `newRoot`. -/
def tourChangeRoot (s : TourAbs) (oldRoot newRoot : ℕ) : TourAbs :=
  { s with rf := ⟨s.rf.F, insert newRoot (s.rf.R.erase oldRoot)⟩ }

/-- Toggle membership of end `x` in `s.marked`. -/
def tourSetMark (s : TourAbs) (x : End) (flag : ℕ) : TourAbs :=
  if flag = 1 then { s with marked := insert x s.marked }
  else { s with marked := s.marked.erase x }

/-- Cyclic successor of open end `x` in its component's `coreTour`. -/
noncomputable def tourNextOpen (s : TourAbs) (x : End) : End :=
  cycNext (coreTour s.ord s.rf (s.rf.root (ordSrc s.ord x))) x

/-- Whether `y` immediately follows `x` in the cyclic core tour of `x`'s component. -/
noncomputable def tourAdjacent (s : TourAbs) (x y : End) : Prop :=
  s.rf.root (ordSrc s.ord x) = s.rf.root (ordSrc s.ord y) ∧ tourNextOpen s x = y

/-- First marked end strictly after `x` (wrapping around to `x` if `x` is the only marked end) in
`x`'s component's full tour, or `none` if no end in that component is marked. -/
noncomputable def tourNextMarked (s : TourAbs) (x : End) : Option End :=
  open Classical in
  if hF : s.rf.F.IsForest then
    let L := rotateToList x (fullTour s.ord s.rf.F hF (s.rf.root (ordSrc s.ord x)))
    (L.tail ++ [x]).find? fun z => decide (z ∈ s.marked)
  else none

/-- The list of marked ends in `coreTour s.ord s.rf r`. -/
noncomputable def tourMarkedList (s : TourAbs) (r : ℕ) : List End :=
  open Classical in
  (coreTour s.ord s.rf r).filter fun x => decide (x ∈ s.marked)

/-- The core rotation tour data structure (piece P2).
Initialization `[vCap, eCap, ordPtr, forestEdgesPtr, rootsPtr, heap]` reads a whole order
(`OrdListAt`), a list of distinct forest edges, and a list of distinct roots. Every constant `mul`
is free of the input. -/
noncomputable def tourContract (vCap eCap mul : ℕ) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure TourAbs where
  initPre args mem :=
    ∃ ordPtr fePtr rsPtr heap ordWords,
      args = [vCap, eCap, ordPtr, fePtr, rsPtr, heap] ∧
      OrdListAt mem ordPtr (readOrd mem ordPtr) ordWords ∧
      ordPtr + ordWords ≤ heap ∧
      fePtr + 1 + mem fePtr ≤ heap ∧
      rsPtr + 1 + mem rsPtr ≤ heap ∧
      (readNatList mem fePtr).Nodup ∧
      (readNatList mem rsPtr).Nodup ∧
      TourValid vCap eCap
        ⟨readOrd mem ordPtr,
          initTourForest (readOrdRecordsAt mem ordPtr) (readNatList mem fePtr)
            (readNatList mem rsPtr), ∅⟩
  initPost args mem s _ :=
    s = ⟨readOrd mem (args.getD 2 0),
      initTourForest (readOrdRecordsAt mem (args.getD 2 0))
        (readNatList mem (args.getD 3 0)) (readNatList mem (args.getD 4 0)), ∅⟩
  initCost args mem :=
    mul * (1 + ordRecordsWords (readOrdRecordsAt mem (args.getD 2 0)) +
      mem (args.getD 3 0) + mem (args.getD 4 0)) * tourLog eCap
  initSpace args _ := allocation 14 args
  pre i s args mem := match i with
    | 0 => ∃ handle edits words heap, args = [handle, edits, words, heap] ∧
        OrdEditsAt mem edits (readOrdEdits mem edits) words ∧ edits + words ≤ heap ∧
        TourEditsValid vCap eCap s (readOrdEdits mem edits)
    | 1 => ∃ handle e newRoot heap, args = [handle, e, newRoot, heap] ∧
        e ∈ s.rf.F.E ∧ newRoot < vCap ∧ newRoot ∈ s.rf.F.V ∧ newRoot ∉ s.rf.R ∧
        (∀ v ∈ s.rf.F.V, ∃! r, r ∈ insert newRoot s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    | 2 => ∃ handle e dropRoot heap, args = [handle, e, dropRoot, heap] ∧
        e < eCap ∧ e ∉ s.rf.F.E ∧
        (∃ u, (e, true) ∈ s.ord u) ∧ (∃ v, (e, false) ∈ s.ord v) ∧
        ¬ s.rf.F.Connected (ordSrc s.ord (e, true)) (ordSrc s.ord (e, false)) ∧
        (dropRoot = s.rf.root (ordSrc s.ord (e, true)) ∨
          dropRoot = s.rf.root (ordSrc s.ord (e, false)))
    | 3 => ∃ handle oldRoot newRoot heap, args = [handle, oldRoot, newRoot, heap] ∧
        oldRoot ∈ s.rf.R ∧ newRoot < vCap ∧ newRoot ∈ s.rf.F.V ∧ s.rf.F.Connected oldRoot newRoot
    | 4 => ∃ handle r heap, args = [handle, r, heap] ∧ r < vCap
    | 5 => ∃ handle keyX keyY heap, args = [handle, keyX, keyY, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u) ∧ (endOfKey keyX).1 ∉ s.rf.F.E ∧
        (∃ v, endOfKey keyY ∈ s.ord v) ∧ (endOfKey keyY).1 ∉ s.rf.F.E
    | 6 => ∃ handle keyX heap, args = [handle, keyX, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u) ∧ (endOfKey keyX).1 ∉ s.rf.F.E
    | 7 => ∃ handle keyX flag heap, args = [handle, keyX, flag, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u) ∧ (endOfKey keyX).1 ∉ s.rf.F.E ∧ flag ≤ 1
    | 8 => ∃ handle keyX heap, args = [handle, keyX, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u)
    | 9 => ∃ handle r heap, args = [handle, r, heap] ∧ r < vCap
    | 10 => ∃ handle keyX heap, args = [handle, keyX, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u)
    | 11 => ∃ handle r heap, args = [handle, r, heap] ∧ r < vCap
    | 12 => ∃ handle r heap, args = [handle, r, heap] ∧ r < vCap
    | 13 => ∃ handle keyX heap, args = [handle, keyX, heap] ∧
        (∃ u, endOfKey keyX ∈ s.ord u)
    | _ => False
  post i s args mem s' mem' := match i with
    | 0 => s' = tourApplyEdits s (readOrdEdits mem (args.getD 1 0))
    | 1 => s' = tourCut s (args.getD 1 0) (args.getD 2 0)
    | 2 => s' = tourLink s (args.getD 1 0) (args.getD 2 0)
    | 3 => s' = tourChangeRoot s (args.getD 1 0) (args.getD 2 0)
    | 4 => s' = s ∧ EndListAt mem' (args.getD 2 0) (coreTour s.ord s.rf (args.getD 1 0))
    | 5 => s' = s ∧
        open Classical in
        mem' (args.getD 3 0) =
          if tourAdjacent s (endOfKey (args.getD 1 0)) (endOfKey (args.getD 2 0)) then 1 else 0
    | 6 => s' = s ∧
        mem' (args.getD 2 0) = endKey (tourNextOpen s (endOfKey (args.getD 1 0)))
    | 7 => s' = tourSetMark s (endOfKey (args.getD 1 0)) (args.getD 2 0)
    | 8 => s' = s ∧
        mem' (args.getD 2 0) = match tourNextMarked s (endOfKey (args.getD 1 0)) with
          | none => 0
          | some y => 1 + endKey y
    | 9 => s' = s ∧ EndListAt mem' (args.getD 2 0) (tourMarkedList s (args.getD 1 0))
    | 10 => s' = s ∧
        mem' (args.getD 2 0) = s.rf.root (ordSrc s.ord (endOfKey (args.getD 1 0)))
    | 11 => s' = s ∧
        mem' (args.getD 2 0) = match (tourMarkedList s (args.getD 1 0)).head? with
          | none => 0
          | some y => 1 + endKey y
    | 12 => s' = s ∧
        mem' (args.getD 2 0) = (coreTour s.ord s.rf (args.getD 1 0)).length
    | 13 => s' = s ∧
        mem' (args.getD 2 0) = ordSrc s.ord (endOfKey (args.getD 1 0))
    | _ => False
  cost i s args _ := match i with
    | 0 => mul * (args.getD 2 0 + 1) * tourLog eCap
    | 1 | 2 | 3 | 5 | 6 | 7 | 8 | 10 | 11 | 12 => mul * tourLog eCap
    | 13 => mul
    | 4 => mul * ((coreTour s.ord s.rf (args.getD 1 0)).length + 1) * tourLog eCap
    | 9 => mul * ((tourMarkedList s (args.getD 1 0)).length + 1) * tourLog eCap
    | _ => 0
  space i s args _ := match i with
    | 0 => allocation 0 args
    | 1 | 2 | 3 | 7 => 2
    | 4 => 3 + (coreTour s.ord s.rf (args.getD 1 0)).length
    | 5 | 6 | 8 | 11 => 3
    | 9 => 1 + (tourMarkedList s (args.getD 1 0)).length
    | 10 | 12 | 13 => 1
    | _ => 0

/-- Non-vacuity witness for `tourContract`: the empty graph on vertex `0` meets `initPre`. -/
theorem tourContract_initPre_nonempty {vCap eCap mul : ℕ}
    {allocation : ℕ → List ℕ → ℕ} (hv : 0 < vCap) :
    let mem : ℕ → ℕ := fun a =>
      if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 1 else if a = 3 then 0 else 0
    (tourContract vCap eCap mul allocation).initPre [vCap, eCap, 0, 1, 2, 4] mem := by
  intro mem
  refine ⟨0, 1, 2, 4, 1, rfl, ?_, by decide, by simp [mem], by simp [mem], ?_, ?_, ?_⟩
  · refine ⟨by simp [readOrdRecordsAt, readOrdRecords, mem], rfl,
      by simp [readOrdRecordsAt, readOrdRecords, ordRecordsWords, mem]⟩
  · simp [readNatList, readList, mem]
  · simp [readNatList, readList, mem]
  · have hrecs : readOrdRecordsAt mem 0 = [] := by simp [readOrdRecordsAt, readOrdRecords, mem]
    have hfe : readNatList mem 1 = [] := by simp [readNatList, readList, mem]
    have hrs : readNatList mem 2 = [0] := by simp [readNatList, readList, mem]
    rw [hrecs, hfe, hrs]
    refine ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by simp [readOrd, hrecs, ordOfRecords] at h⟩,
      ⟨fun _ => List.nodup_nil, fun _ _ _ h => by simp [readOrd, hrecs, ordOfRecords] at h,
        ⟨fun _ h => by simp [initTourForest] at h, fun P ⟨hne, _, _, hw⟩ => by
          cases hw with
          | nil => exact hne rfl
          | cons he _ _ => simp [initTourForest] at he⟩,
        fun _ h => by simp [readOrd, hrecs, ordOfRecords] at h,
        fun _ h => by simp [initTourForest] at h⟩,
      by simp [initTourForest],
      fun v hv' => by simp [initTourForest] at hv'; subst hv'; exact hv,
      fun v hv' => by
        simp [initTourForest] at hv'; subst hv'
        exact ⟨0, ⟨by simp [initTourForest], connected_refl _ 0⟩,
          fun r hr => by simp [initTourForest] at hr; exact hr.1⟩,
      fun _ h => (Finset.notMem_empty _ h).elim⟩

end MinCostFlow.SparseCore.Program
