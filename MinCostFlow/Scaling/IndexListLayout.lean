module

public import WordRAM.Layout
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic
import WordRAM.Memory

/-!
# Stored immutable lists of edge indices

The label and cycle traversals store adjacency lists, pending edges, and
path stacks. Zero denotes an empty list. A nonempty node stores its edge
index followed by the tail pointer. Nodes lie in a specified memory range,
so changing vertex tables outside that range preserves every represented
list. Fresh cons nodes preserve old lists without a disjointness condition
on lists that share a tail.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A null pointer or a chain of two-word edge-index nodes in `[lo,bound)`.
The node's first word is the index and its second word is the tail pointer. -/
inductive IndexListAt {m : ℕ} (mem : ℕ → ℕ) (lo bound : ℕ) : ℕ → List (Fin m) → Prop
  | nil : IndexListAt mem lo bound 0 []
  | cons {ptr tail : ℕ} {e : Fin m} {es : List (Fin m)}
      (hpositive : 0 < ptr) (hlower : lo ≤ ptr) (hupper : ptr+2 ≤ bound)
      (hvalue : mem ptr = e.val) (hnext : mem (ptr+1) = tail)
      (htail : IndexListAt mem lo bound tail es) : IndexListAt mem lo bound ptr (e :: es)

/-- Empty lists have exactly the null pointer. -/
theorem indexListAt_nil_iff {m : ℕ} {mem : ℕ → ℕ} {lo bound ptr : ℕ} :
    IndexListAt (m := m) mem lo bound ptr [] ↔ ptr = 0 := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil

/-- A represented immutable list has null pointer exactly when it is empty. -/
theorem IndexListAt.pointer_zero_iff {m : ℕ} {mem : ℕ → ℕ} {lo bound ptr : ℕ}
    {es : List (Fin m)} (hat : IndexListAt mem lo bound ptr es) : ptr=0 ↔ es=[] := by
  constructor
  · intro hp
    cases hat with
    | nil => rfl
    | cons hpositive _ _ _ _ _ => omega
  · intro he
    exact indexListAt_nil_iff.mp (he ▸ hat)

/-- A nonempty list exposes its head index, tail pointer, and node bounds. -/
theorem indexListAt_cons_iff {m : ℕ} {mem : ℕ → ℕ} {lo bound ptr : ℕ}
    {e : Fin m} {es : List (Fin m)} :
    IndexListAt mem lo bound ptr (e :: es) ↔
      0 < ptr ∧ lo ≤ ptr ∧ ptr+2 ≤ bound ∧ mem ptr = e.val ∧
      ∃ tail, mem (ptr+1) = tail ∧ IndexListAt mem lo bound tail es := by
  constructor
  · intro h
    cases h with
    | cons hp hl hu hv hn ht => exact ⟨hp, hl, hu, hv, _, hn, ht⟩
  · rintro ⟨hp, hl, hu, hv, tail, hn, ht⟩
    exact .cons hp hl hu hv hn ht

/-- Every list pointer is at most its storage bound, including null. -/
theorem IndexListAt.pointer_le {m : ℕ} {mem : ℕ → ℕ} {lo bound ptr : ℕ}
    {es : List (Fin m)} (hat : IndexListAt mem lo bound ptr es) : ptr ≤ bound := by
  cases hat with
  | nil => exact Nat.zero_le _
  | cons _ _ hupper _ _ _ => omega

/-- Enlarging the allowed node range preserves a list representation. -/
theorem IndexListAt.mono {m : ℕ} {mem : ℕ → ℕ} {lo bound ptr lo' bound' : ℕ}
    {es : List (Fin m)} (hat : IndexListAt mem lo bound ptr es)
    (hlower : lo' ≤ lo) (hupper : bound ≤ bound') : IndexListAt mem lo' bound' ptr es := by
  induction hat with
  | nil => exact .nil
  | cons hp hl hu hv hn ht ih => exact .cons hp (hlower.trans hl) (hu.trans hupper) hv hn ih

/-- Preserving cells in the node range preserves all represented indices
and pointers, even when cells outside that range are changed. -/
theorem IndexListAt.of_agree {m : ℕ} {mem mem' : ℕ → ℕ} {lo bound ptr : ℕ}
    {es : List (Fin m)} (hat : IndexListAt mem lo bound ptr es)
    (hframe : ∀ x, lo ≤ x → x < bound → mem' x = mem x) :
    IndexListAt mem' lo bound ptr es := by
  induction hat with
  | nil => exact .nil
  | cons hp hl hu hv hn ht ih =>
    refine .cons hp hl hu ((hframe _ hl (by omega)).trans hv) ?_ ih
    exact (hframe _ (by omega) (by omega)).trans hn

/-- Every finite edge-index list has a concrete representation above address
zero with a fresh zero tail. Repeated edge indices are allowed. -/
theorem exists_indexListAt {m : ℕ} (es : List (Fin m)) :
    ∃ mem bound ptr, 1 ≤ bound ∧ IndexListAt mem 1 bound ptr es ∧ ZeroFrom mem bound := by
  induction es with
  | nil => exact ⟨fun _ => 0, 1, 0, le_rfl, .nil, fun _ _ => rfl⟩
  | cons e es ih =>
    obtain ⟨mem, bound, ptr, hbound, hat, hzero⟩ := ih
    let mem' := Function.update (Function.update mem bound e.val) (bound+1) ptr
    have hframe : ∀ x, 1 ≤ x → x < bound → mem' x = mem x := by
      intro x _ hx
      exact (Function.update_of_ne (by omega : x ≠ bound+1) _ _).trans
        (Function.update_of_ne (by omega : x ≠ bound) _ _)
    have htail : IndexListAt mem' 1 (bound+2) ptr es :=
      (hat.of_agree hframe).mono le_rfl (by omega)
    refine ⟨mem', bound+2, bound, by omega,
      .cons (by omega) hbound le_rfl ?_ ?_ htail, ?_⟩
    · exact (Function.update_of_ne (by omega : bound ≠ bound+1) _ _).trans
        (Function.update_self _ _ _)
    · exact Function.update_self _ _ _
    · intro x hx
      dsimp only [mem']
      rw [Function.update_of_ne (by omega : x ≠ bound+1), Function.update_of_ne (by omega : x ≠ bound)]
      exact hzero x (by omega)

/-- Two arbitrary lists can be represented in the same memory with one
fresh zero tail, including when both lists are nonempty. -/
theorem exists_two_indexListsAt {m : ℕ} (es rest : List (Fin m)) :
    ∃ mem bound ptr tail, 1 ≤ bound ∧ IndexListAt mem 1 bound ptr es ∧
      IndexListAt mem 1 bound tail rest ∧ ZeroFrom mem bound := by
  induction es with
  | nil =>
    obtain ⟨mem, bound, tail, hbound, hat, hzero⟩ := exists_indexListAt rest
    exact ⟨mem, bound, 0, tail, hbound, .nil, hat, hzero⟩
  | cons e es ih =>
    obtain ⟨mem, bound, ptr, tail, hbound, hat, hrest, hzero⟩ := ih
    let mem' := Function.update (Function.update mem bound e.val) (bound+1) ptr
    have hframe : ∀ x, 1 ≤ x → x < bound → mem' x = mem x := by
      intro x _ hx
      exact (Function.update_of_ne (by omega : x ≠ bound+1) _ _).trans
        (Function.update_of_ne (by omega : x ≠ bound) _ _)
    have htail : IndexListAt mem' 1 (bound+2) ptr es :=
      (hat.of_agree hframe).mono le_rfl (by omega)
    have hrest' : IndexListAt mem' 1 (bound+2) tail rest :=
      (hrest.of_agree hframe).mono le_rfl (by omega)
    refine ⟨mem', bound+2, bound, tail, by omega,
      .cons (by omega) hbound le_rfl ?_ ?_ htail, hrest', ?_⟩
    · exact (Function.update_of_ne (by omega : bound ≠ bound+1) _ _).trans (Function.update_self _ _ _)
    · exact Function.update_self _ _ _
    · intro x hx
      dsimp only [mem']
      rw [Function.update_of_ne (by omega : x ≠ bound+1), Function.update_of_ne (by omega : x ≠ bound)]
      exact hzero x (by omega)

/-- A list can be placed after any reserved prefix while keeping that prefix
zero and leaving a fresh zero tail after its nodes. -/
theorem exists_indexListAt_above {m : ℕ} (lo : ℕ) (es : List (Fin m)) :
    ∃ mem bound ptr, lo ≤ bound ∧ 0 < bound ∧ IndexListAt mem lo bound ptr es ∧
      (∀ x < lo, mem x = 0) ∧ ZeroFrom mem bound := by
  induction es with
  | nil => exact ⟨fun _ => 0, lo+1, 0, by omega, by omega, .nil, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons e es ih =>
    obtain ⟨mem, bound, ptr, hbound, hpositive, hat, hprefix, hzero⟩ := ih
    let mem' := Function.update (Function.update mem bound e.val) (bound+1) ptr
    have hframe : ∀ x, lo ≤ x → x < bound → mem' x = mem x := by
      intro x _ hx
      exact (Function.update_of_ne (by omega : x ≠ bound+1) _ _).trans
        (Function.update_of_ne (by omega : x ≠ bound) _ _)
    have htail : IndexListAt mem' lo (bound+2) ptr es :=
      (hat.of_agree hframe).mono le_rfl (by omega)
    refine ⟨mem', bound+2, bound, by omega, by omega,
      .cons hpositive hbound le_rfl ?_ ?_ htail, ?_, ?_⟩
    · exact (Function.update_of_ne (by omega : bound ≠ bound+1) _ _).trans (Function.update_self _ _ _)
    · exact Function.update_self _ _ _
    · intro x hx
      dsimp only [mem']
      rw [Function.update_of_ne (by omega : x ≠ bound+1), Function.update_of_ne (by omega : x ≠ bound)]
      exact hprefix x hx
    · intro x hx
      dsimp only [mem']
      rw [Function.update_of_ne (by omega : x ≠ bound+1), Function.update_of_ne (by omega : x ≠ bound)]
      exact hzero x (by omega)

end MinCostFlow.Scaling.Machine
