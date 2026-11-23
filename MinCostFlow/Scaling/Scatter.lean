module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Basic

/-!
# Restoring vector coordinates by table writes

The instance reductions of Appendix C of Chen et al., arXiv:2203.00671v2,
retain original edge indices when they remove inactive slots. To restore a
flow, initialize a zero table and scatter the retained coordinate-value pairs.
This file proves the table-write loop's lookup rules and its linear work count.
-/

@[expose] public section
namespace MinCostFlow.Scaling
namespace Scatter
variable {α β : Type} [DecidableEq α]

/-- Write coordinate-value pairs to a table in their listed order. -/
def write (s : α → β) (entries : List (α × β)) : α → β :=
  entries.foldl (fun t entry => Function.update t entry.1 entry.2) s

/-- A coordinate absent from the write list is unchanged. -/
theorem unchanged (s : α → β) (entries : List (α × β)) (x : α)
    (h : ∀ entry ∈ entries, entry.1 ≠ x) : write s entries x = s x := by
  induction entries generalizing s with
  | nil => rfl
  | cons entry entries ih =>
    change write (Function.update s entry.1 entry.2) entries x = _
    rw [ih]
    · exact Function.update_of_ne (h entry List.mem_cons_self).symm _ _
    · intro a ha
      exact h a (List.mem_cons_of_mem _ ha)

/-- When keys are distinct, a listed coordinate gets exactly its listed value. -/
theorem lookup (s : α → β) (entries : List (α × β))
    (hnd : (entries.map Prod.fst).Nodup) (x : α) (b : β)
    (hmem : (x, b) ∈ entries) : write s entries x = b := by
  induction entries generalizing s with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons entry entries ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hmem with he | he
    · subst entry
      change write (Function.update s x b) entries x = b
      rw [unchanged]
      · exact Function.update_self _ _ _
      · intro entry hentry hkey
        apply hn.1
        apply List.mem_map.mpr
        exact ⟨entry, hentry, hkey⟩
    · exact ih (Function.update s entry.1 entry.2) hn.2 he

/-- The write loop with four counted operations per pair: read key, read value,
write the table cell, and advance the loop. -/
def withWork : (α → β) → List (α × β) → (α → β) × ℕ
  | s, [] => (s, 0)
  | s, entry :: entries =>
      let r := withWork (Function.update s entry.1 entry.2) entries
      (r.1, 4 + r.2)

/-- Recording work leaves the table-write result unchanged. -/
theorem withWork_value (s : α → β) (entries : List (α × β)) :
    (withWork s entries).1 = write s entries := by
  induction entries generalizing s with
  | nil => rfl
  | cons entry entries ih => exact ih (Function.update s entry.1 entry.2)

/-- The scatter loop has an exact linear operation count. -/
theorem withWork_work (s : α → β) (entries : List (α × β)) :
    (withWork s entries).2 = 4 * entries.length := by
  induction entries generalizing s with
  | nil => rfl
  | cons entry entries ih =>
    change 4 + (withWork (Function.update s entry.1 entry.2) entries).2 = _
    rw [ih, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- Applying a value map commutes with the table-write loop. This lets the
integer reconstruction be compared with real-valued correctness statements. -/
theorem map_write {γ : Type} (f : β → γ) (s : α → β) (entries : List (α × β)) :
    (fun x => f (write s entries x)) =
      write (fun x => f (s x)) (entries.map (fun entry => (entry.1, f entry.2))) := by
  induction entries generalizing s with
  | nil => rfl
  | cons entry entries ih =>
    change (fun x => f (write (Function.update s entry.1 entry.2) entries x)) =
      write (Function.update (fun x => f (s x)) entry.1 (f entry.2))
        (entries.map (fun entry => (entry.1, f entry.2)))
    rw [ih]
    congr 1
    funext x
    by_cases h : x = entry.1
    · subst x
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]

end Scatter
end MinCostFlow.Scaling
