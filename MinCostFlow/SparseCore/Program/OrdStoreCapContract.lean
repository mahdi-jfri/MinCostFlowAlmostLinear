module

public import MinCostFlow.SparseCore.Program.OrdStoreContract
import Mathlib.Tactic

/-!
# Capacity-parameterized contract for the order store

`OrdStoreContract.lean` defines `ordStoreContract` with `init` arguments `[ord, heap]` and
`OrdWithin` without cross-vertex uniqueness. Implementing an order store with a vertex-to-root table
and an end-key-to-node table (so that operation `1` runs in `O(|s v| + 1)` time and operations
`0`/`2` run in `O(log (eCap + 2))` amortized time) requires:

1. passing `vCap` and `eCap` to initialization (`args = [vCap, eCap, ord, heap]`) so the
   initialization procedure and `allocation 3 args` know the table sizes;
2. cross-vertex uniqueness (`OrdUniqueWithin`: each end appears in at most one vertex's list),
   which holds for every rotation of a graph (`IsRotationOrder G ord`); and
3. per-edit preservation of `OrdUniqueWithin` along an edit batch (`OrdEditsUniqueWithin`).

This file states the minimal corrected contract `ordStoreCapContract` and proves basic helper
lemmas on `endKey`, `endOfKey`, `readOrd`, and `decodeOrdEdits`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- `ord` satisfies `OrdWithin vCap eCap` and every end appears in at most one vertex's list. -/
def OrdUniqueWithin (vCap eCap : ℕ) (ord : ℕ → List End) : Prop :=
  OrdWithin vCap eCap ord ∧ ∀ u v x, x ∈ ord u → x ∈ ord v → u = v

/-- Every prefix of `edits` preserves `OrdUniqueWithin vCap eCap` starting from `s`. -/
def OrdEditsUniqueWithin (vCap eCap : ℕ) (s : ℕ → List End) (edits : List OrdEdit) : Prop :=
  ∀ k ≤ edits.length, OrdUniqueWithin vCap eCap (applyOrdEdits s (edits.take k))

/-- Capacity-parameterized order-store contract. Identical to `ordStoreContract` except that
initialization takes `[vCap, eCap, ord, heap]` and requires `OrdUniqueWithin`, and operation `0`
requires `OrdEditsUniqueWithin`. -/
def ordStoreCapContract (vCap eCap mul : ℕ) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (ℕ → List End) where
  initPre args mem := ∃ ord heap words, args = [vCap, eCap, ord, heap] ∧
    OrdListAt mem ord (readOrd mem ord) words ∧ ord + words ≤ heap ∧
    OrdUniqueWithin vCap eCap (readOrd mem ord)
  initPost args mem s _ := s = readOrd mem (args.getD 2 0)
  initCost args mem := mul * (1 + ordRecordsWords (readOrdRecordsAt mem (args.getD 2 0))) *
    ordStoreLog eCap
  initSpace args _ := allocation 3 args
  pre i s args mem := match i with
    | 0 => ∃ handle edits words heap, args = [handle, edits, words, heap] ∧
        OrdEditsAt mem edits (readOrdEdits mem edits) words ∧ edits + words ≤ heap ∧
        OrdEditsWithin vCap eCap (readOrdEdits mem edits) ∧
        OrdEditsUniqueWithin vCap eCap s (readOrdEdits mem edits)
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

/-! ### Basic lemmas on `endKey` and `endOfKey` -/

theorem endKey_endOfKey (a : ℕ) : endKey (endOfKey a) = a := by
  unfold endKey endOfKey
  dsimp only
  by_cases h : a % 2 = 0
  · simp [h]; omega
  · simp [h]; omega

theorem endOfKey_endKey (x : End) : endOfKey (endKey x) = x := by
  rcases x with ⟨e, b⟩
  cases b
  · simp [endKey, endOfKey]; omega
  · simp [endKey, endOfKey]

theorem endOfKey_injective : Function.Injective endOfKey := by
  intro a b h
  have := congrArg endKey h
  simpa [endKey_endOfKey] using this

theorem endKey_lt_two_mul {eCap : ℕ} {x : End} (hx : x.1 < eCap) : endKey x < 2 * eCap := by
  rcases x with ⟨e, b⟩
  cases b <;> simp [endKey] at hx ⊢ <;> omega

theorem key_lt_two_mul_of_endOfKey {eCap k : ℕ} (hk : (endOfKey k).1 < eCap) :
    k < 2 * eCap := by
  simpa [endKey_endOfKey] using endKey_lt_two_mul hk

theorem endOfKey_fst (a : ℕ) : (endOfKey a).1 = a / 2 := rfl

theorem endOfKey_fst_ne_iff (a e : ℕ) :
    (endOfKey a).1 ≠ e ↔ a ≠ 2 * e ∧ a ≠ 2 * e + 1 := by
  simp only [endOfKey_fst]
  omega

/-! ### Helper lemmas on `OrdUniqueWithin` and `applyOrdEdits` -/

theorem OrdUniqueWithin.nodup {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) (v : ℕ) : (ord v).Nodup :=
  h.1.1 v

theorem OrdUniqueWithin.eq_nil_of_ge {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) {v : ℕ} (hv : vCap ≤ v) : ord v = [] :=
  h.1.2.1 v hv

theorem OrdUniqueWithin.v_lt_of_mem {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) {v : ℕ} {x : End} (hx : x ∈ ord v) : v < vCap := by
  by_contra hge
  have hnil := h.eq_nil_of_ge (Nat.le_of_not_lt hge)
  rw [hnil] at hx
  exact List.not_mem_nil hx

theorem OrdUniqueWithin.edge_lt {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) {v : ℕ} {x : End} (hx : x ∈ ord v) : x.1 < eCap :=
  h.1.2.2 v x hx

theorem OrdUniqueWithin.key_lt {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) {v : ℕ} {x : End} (hx : x ∈ ord v) :
    endKey x < 2 * eCap :=
  endKey_lt_two_mul (h.edge_lt hx)

theorem OrdUniqueWithin.unique_v {vCap eCap : ℕ} {ord : ℕ → List End}
    (h : OrdUniqueWithin vCap eCap ord) {u v : ℕ} {x : End}
    (hu : x ∈ ord u) (hv : x ∈ ord v) : u = v :=
  h.2 u v x hu hv

theorem OrdEditsUniqueWithin.head {vCap eCap : ℕ} {s : ℕ → List End} {e : OrdEdit}
    {es : List OrdEdit} (h : OrdEditsUniqueWithin vCap eCap s (e :: es)) :
    OrdUniqueWithin vCap eCap s ∧ OrdUniqueWithin vCap eCap (applyOrdEdit s e) := by
  refine ⟨?_, ?_⟩
  · simpa [applyOrdEdits] using h 0 (Nat.zero_le _)
  · simpa [applyOrdEdits] using h 1 (by simp)

theorem OrdEditsUniqueWithin.tail {vCap eCap : ℕ} {s : ℕ → List End} {e : OrdEdit}
    {es : List OrdEdit} (h : OrdEditsUniqueWithin vCap eCap s (e :: es)) :
    OrdEditsUniqueWithin vCap eCap (applyOrdEdit s e) es := by
  intro k hk
  have h1 := h (k + 1) (by simp; omega)
  simpa [applyOrdEdits, List.take_succ_cons] using h1

theorem OrdEditsUniqueWithin.final {vCap eCap : ℕ} {s : ℕ → List End} {edits : List OrdEdit}
    (h : OrdEditsUniqueWithin vCap eCap s edits) :
    OrdUniqueWithin vCap eCap (applyOrdEdits s edits) := by
  simpa [List.take_length] using h edits.length (le_refl _)

/-- When `insertBefore v x y` preserves `OrdUniqueWithin`, `x` is not currently in any vertex's
list. -/
theorem insertBefore_not_mem_of_unique {vCap eCap : ℕ} {s : ℕ → List End} {v : ℕ} {x : End}
    {y : Option End}
    (hpost : OrdUniqueWithin vCap eCap (applyOrdEdit s (.insertBefore v x y))) :
    ∀ u, x ∉ s u := by
  intro u hxu
  have hx_in_v : x ∈ applyOrdEdit s (.insertBefore v x y) v := by
    simp only [applyOrdEdit, Function.update_self]
    cases y with
    | none => simp [insertBeforeList]
    | some y' => simp [insertBeforeList]
  by_cases huv : u = v
  · subst huv
    have hnd := hpost.nodup u
    simp only [applyOrdEdit, Function.update_self] at hnd
    cases y with
    | none =>
      simp only [insertBeforeList, List.nodup_append, List.nodup_singleton] at hnd
      exact hnd.2.2 x hxu x (List.mem_singleton_self x) rfl
    | some y' =>
      simp only [insertBeforeList] at hnd
      have hsplit : s u = (s u).take ((s u).idxOf y') ++ (s u).drop ((s u).idxOf y') :=
        (List.take_append_drop _ _).symm
      rw [hsplit, List.mem_append] at hxu
      rw [List.nodup_append] at hnd
      rcases hxu with h1 | h2
      · exact hnd.2.2 x h1 x List.mem_cons_self rfl
      · exact (List.nodup_cons.mp hnd.2.1).1 h2
  · have hx_in_u : x ∈ applyOrdEdit s (.insertBefore v x y) u := by
      simpa [applyOrdEdit, Function.update_of_ne huv] using hxu
    exact huv (hpost.unique_v hx_in_u hx_in_v)

/-! ### Helper lemmas on `readOrdRecords` and `decodeOrdEdits` -/

theorem readOrdRecords_length (mem : ℕ → ℕ) :
    ∀ count a, (readOrdRecords mem count a).length = count
  | 0, _ => rfl
  | count + 1, a => by simp [readOrdRecords, readOrdRecords_length mem count]

theorem readList_length (mem : ℕ → ℕ) (a n : ℕ) : (readList mem a n).length = n := by
  simp [readList]

theorem readList_getElem (mem : ℕ → ℕ) (a n i : ℕ) (hi : i < (readList mem a n).length) :
    (readList mem a n)[i]'hi = mem (a + i) := by
  simp [readList]

theorem ordRecordsWords_ge_two_mul :
    ∀ recs : List (ℕ × List End), 2 * recs.length ≤ ordRecordsWords recs
  | [] => by simp [ordRecordsWords]
  | r :: rs => by
    have ih := ordRecordsWords_ge_two_mul rs
    simp only [ordRecordsWords, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem decodeOrdEdit_words_ge_two (mem : ℕ → ℕ) (a : ℕ) : 2 ≤ (decodeOrdEdit mem a).2 := by
  unfold decodeOrdEdit
  split_ifs <;> omega

theorem decodeOrdEdits_length (mem : ℕ → ℕ) :
    ∀ count a, (decodeOrdEdits mem count a).1.length = count ∧
      (decodeOrdEdits mem count a).2.length = count
  | 0, _ => ⟨rfl, rfl⟩
  | count + 1, a => by
    have ih := decodeOrdEdits_length mem count (a + (decodeOrdEdit mem a).2)
    simp only [decodeOrdEdits, List.length_cons, ih.1, ih.2, and_self]

theorem decodeOrdEdits_words_ge_two_mul (mem : ℕ → ℕ) :
    ∀ count a, 2 * count ≤ ((decodeOrdEdits mem count a).2).sum
  | 0, _ => by simp [decodeOrdEdits]
  | count + 1, a => by
    have h1 := decodeOrdEdit_words_ge_two mem a
    have h2 := decodeOrdEdits_words_ge_two_mul mem count (a + (decodeOrdEdit mem a).2)
    simp only [decodeOrdEdits, List.sum_cons]
    omega

theorem ordOfRecords_cons_of_nodup {v : ℕ} {xs : List End} {recs : List (ℕ × List End)}
    (hnd : ((v, xs) :: recs).map Prod.fst |>.Nodup) :
    ordOfRecords ((v, xs) :: recs) = Function.update (ordOfRecords recs) v xs := by
  funext u
  by_cases huv : u = v
  · subst huv
    simp [ordOfRecords]
  · simp [ordOfRecords, Function.update_of_ne huv, beq_false_of_ne (Ne.symm huv)]

theorem ordOfRecords_nil : ordOfRecords [] = fun _ => [] := rfl

end MinCostFlow.SparseCore.Program
