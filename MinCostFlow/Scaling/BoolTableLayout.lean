module

public import WordRAM.Layout
public import Mathlib.Data.List.OfFn
import WordRAM.Memory
import WordRAM.Entry

/-!
# Stored traversal flags

Label propagation records reached vertices, and cycle extraction records
vertices on the current path. Both use a one-word Boolean table with false
stored as zero and true as one. This file proves initialization, point
updates, and memory-frame preservation for that layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- One zero/one word per vertex. -/
def BoolTableAt {n : ℕ} (mem : ℕ → ℕ) (a : ℕ) (flags : Fin n → Bool) : Prop :=
  ∀ v, mem (a+v.val) = (flags v).toNat

/-- A contiguous list of flag words provides the per-vertex layout. -/
theorem boolTableAt_of_listAt {n : ℕ} (flags : Fin n → Bool) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (List.ofFn (fun v => (flags v).toNat))) : BoolTableAt mem a flags := by
  intro v
  have h := hat v.val (by simpa only [List.length_ofFn] using v.isLt)
  rw [List.getElem_ofFn] at h
  exact h

/-- The per-vertex layout determines the contiguous array of flag words. -/
theorem BoolTableAt.listAt {n : ℕ} {mem : ℕ → ℕ} {a : ℕ} {flags : Fin n → Bool}
    (hat : BoolTableAt mem a flags) : ListAt mem a (List.ofFn (fun v => (flags v).toNat)) := by
  intro i hi
  have hi' : i < n := by simpa only [List.length_ofFn] using hi
  simpa only [List.getElem_ofFn] using hat ⟨i, hi'⟩

/-- Preserving all old cells below a table's end preserves all its flags. -/
theorem BoolTableAt.of_agree_below {n : ℕ} {mem mem' : ℕ → ℕ} {a heap : ℕ}
    {flags : Fin n → Bool} (hat : BoolTableAt mem a flags) (hend : a+n ≤ heap)
    (hframe : ∀ x < heap, mem' x = mem x) : BoolTableAt mem' a flags := by
  intro v
  have hv := v.isLt
  exact (hframe _ (by omega)).trans (hat v)

/-- Replacing one flag word and preserving the other old cells updates
exactly that vertex's Boolean value. -/
theorem BoolTableAt.update {n : ℕ} {mem mem' : ℕ → ℕ} {a heap : ℕ}
    {flags : Fin n → Bool} (hat : BoolTableAt mem a flags) (v : Fin n) (value : Bool)
    (hend : a+n ≤ heap) (hcell : mem' (a+v.val) = value.toNat)
    (hframe : ∀ x < heap, x ≠ a+v.val → mem' x = mem x) :
    BoolTableAt mem' a (Function.update flags v value) := by
  intro u
  by_cases huv : u = v
  · subst u
    simpa only [Function.update_self] using hcell
  · rw [Function.update_of_ne huv]
    have hu := u.isLt
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    exact (hframe _ (by omega) (by omega)).trans (hat u)

/-- A zero tail provides the all-false initial traversal flags. -/
theorem boolTableAt_false {n : ℕ} {mem : ℕ → ℕ} {a : ℕ} (hzero : ZeroFrom mem a) :
    BoolTableAt mem a (fun _ : Fin n => false) := by
  intro v
  exact hzero _ (by omega)

/-- Preserving a flag table's own range preserves all flags independently
of writes elsewhere in memory. -/
theorem BoolTableAt.of_agree {n : ℕ} {mem mem' : ℕ → ℕ} {a : ℕ}
    {flags : Fin n → Bool} (hat : BoolTableAt mem a flags)
    (hframe : ∀ x, a ≤ x → x < a+n → mem' x = mem x) : BoolTableAt mem' a flags := by
  intro v
  have hv := v.isLt
  exact (hframe _ (by omega) (by omega)).trans (hat v)

/-- Every finite Boolean vector has its canonical stored layout and zero tail. -/
theorem exists_boolTableAt {n : ℕ} (flags : Fin n → Bool) :
    ∃ mem, BoolTableAt mem 0 flags ∧ ZeroFrom mem n := by
  refine ⟨initMem (List.ofFn (fun v => (flags v).toNat)),
    boolTableAt_of_listAt flags _ 0 (listAt_initMem _), ?_⟩
  simpa only [List.length_ofFn] using zeroFrom_initMem (List.ofFn (fun v => (flags v).toNat))

end MinCostFlow.Scaling.Machine
