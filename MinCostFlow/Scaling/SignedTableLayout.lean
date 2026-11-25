module

public import MinCostFlow.Num.SignedPair
public import WordRAM.Memory
public import WordRAM.Entry

/-!
# Stored signed demand tables

The lower-capacity reduction keeps one canonical signed pair per vertex.
This layout uses the statement's `encodeSignedPair`, with two consecutive cells
per entry. Copying the input demand block initializes it. Updating one pair
changes exactly one vertex value, which also justifies sequential updates
when an input edge is a loop.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- One canonical sign/magnitude pair per vertex. -/
def SignedTableAt {n : ℕ} (mem : ℕ → ℕ) (a : ℕ) (s : Fin n → ℤ) : Prop :=
  ∀ v, ListAt mem (a + 2 * v.val) (encodeSignedPair (s v))

/-- The contiguous signed-integer encoding exposes each complete pair. -/
theorem integers_pair_at (zs : List ℤ) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zs.flatMap encodeSignedPair)) (v : Fin zs.length) :
    ListAt mem (a + 2 * v.val) (encodeSignedPair (zs.getD v.val 0)) := by
  induction zs generalizing a with
  | nil => exact Fin.elim0 v
  | cons z zs ih =>
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (encodeSignedPair z) at hhead
    change ListAt mem (a + 2) (zs.flatMap encodeSignedPair) at htail
    obtain ⟨i, hi⟩ := v
    cases i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] using hhead
    | succ i =>
      have hi' : i < zs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hh := ih (a + 2) htail ⟨i, hi'⟩
      simpa only [List.getD_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh

/-- A contiguous encoding of a vertex-indexed vector realizes the table layout. -/
theorem signedTableAt_of_listAt {n : ℕ} (s : Fin n → ℤ) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a ((List.ofFn s).flatMap encodeSignedPair)) : SignedTableAt mem a s := by
  intro v
  have hv : v.val < (List.ofFn s).length := by simpa only [List.length_ofFn] using v.isLt
  have hh := integers_pair_at (List.ofFn s) mem a hat ⟨v.val, hv⟩
  have he : (List.ofFn s).getD v.val 0 = s v := by
    rw [List.getD_eq_getElem _ _ hv, List.getElem_ofFn]
  rwa [he] at hh

/-- The per-vertex signed table layout determines its contiguous encoding. -/
theorem SignedTableAt.listAt {n : ℕ} {mem : ℕ → ℕ} {a : ℕ} {s : Fin n → ℤ}
    (hat : SignedTableAt mem a s) : ListAt mem a ((List.ofFn s).flatMap encodeSignedPair) := by
  induction n generalizing a with
  | zero => exact listAt_nil _ _
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons]
    apply listAt_append.mpr
    refine ⟨hat 0, ?_⟩
    have htail : SignedTableAt mem (a + 2) (fun v : Fin n => s v.succ) := by
      intro v
      simpa only [Fin.val_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hat v.succ
    exact ih htail

/-- Replacing one stored pair and preserving every other old cell updates
exactly one entry of the signed demand vector. -/
theorem SignedTableAt.update {n : ℕ} {mem mem' : ℕ → ℕ} {a heap : ℕ}
    {s : Fin n → ℤ} (hat : SignedTableAt mem a s) (v : Fin n) (z : ℤ)
    (hend : a + 2 * n ≤ heap)
    (hcell : ListAt mem' (a + 2 * v.val) (encodeSignedPair z))
    (hframe : ∀ x < heap, x ≠ a + 2 * v.val → x ≠ a + 2 * v.val + 1 → mem' x = mem x) :
    SignedTableAt mem' a (Function.update s v z) := by
  intro u
  by_cases huv : u = v
  · subst u
    simpa only [Function.update_self] using hcell
  · rw [Function.update_of_ne huv]
    have hne : u.val ≠ v.val := fun he => huv (Fin.ext he)
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    have hu := u.isLt
    have hv := v.isLt
    rw [hframe _ (by omega) (by rcases hi' with rfl | rfl <;> omega)
      (by rcases hi' with rfl | rfl <;> omega)]
    exact hat u i hi

/-- Preserving memory below a table's end preserves all its signed entries. -/
theorem SignedTableAt.of_agree_below {n : ℕ} {mem mem' : ℕ → ℕ} {a heap : ℕ}
    {s : Fin n → ℤ} (hat : SignedTableAt mem a s) (hend : a + 2 * n ≤ heap)
    (hframe : ∀ x < heap, mem' x = mem x) : SignedTableAt mem' a s := by
  intro v
  apply (hat v).of_agree_below (h₀ := heap)
  · change a + 2 * v.val + 2 ≤ heap
    have hv := v.isLt
    omega
  · exact hframe

/-- Preserving just the signed table's own cells preserves its values,
even when other cells below its end are changed. -/
theorem SignedTableAt.of_agree {n : ℕ} {mem mem' : ℕ → ℕ} {a : ℕ}
    {s : Fin n → ℤ} (hat : SignedTableAt mem a s)
    (hframe : ∀ x, a ≤ x → x < a+2*n → mem' x = mem x) : SignedTableAt mem' a s := by
  intro v i hi
  have hv := v.isLt
  have hi' : i < 2 := hi
  exact (hframe _ (by omega) (by omega)).trans (hat v i hi)

/-- The table's representation and zero tail can hold together for every
integer vector. -/
theorem exists_signedTableAt {n : ℕ} (s : Fin n → ℤ) :
    ∃ mem, SignedTableAt mem 0 s ∧ ZeroFrom mem (2 * n) := by
  refine ⟨initMem ((List.ofFn s).flatMap encodeSignedPair),
    signedTableAt_of_listAt s _ 0 (listAt_initMem _), ?_⟩
  simpa only [flatMap_encodeSignedPair_length, List.length_ofFn] using
    zeroFrom_initMem ((List.ofFn s).flatMap encodeSignedPair)

end MinCostFlow.Scaling.Machine
