module

public import MinCostFlow.Scaling.LabelStateLayout
import WordRAM.Memory

/-!
# Reading the propagated labels as an output table

The traversal state already stores canonical signed pairs for its labels.
Restricting a routing graph's labels to the old vertices keeps the same
addresses, because `castSucc` preserves each vertex index. A pointer stored
before this table can expose it to the enclosing dual-extraction procedure
without copying its entries.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A represented traversal state contains its exact signed label table. -/
theorem LabelStateAt.labels {J : Circulation} {mem : ℕ → ℕ} {base bound : ℕ}
    {s : Circulation.LabelState J} (hat : LabelStateAt mem base bound s) :
    SignedTableAt mem (labelLabels base) s.labels := by
  obtain ⟨ptr,_,_,hlabels,_,_⟩ := hat
  exact hlabels

/-- Restricting labels to the old vertices of a one-vertex extension is an
address-preserving view of the same signed table. -/
theorem SignedTableAt.castSucc {n : ℕ} {mem : ℕ → ℕ} {a : ℕ} {f : Fin (n+1) → ℤ}
    (hat : SignedTableAt mem a f) : SignedTableAt mem a (fun v : Fin n => f v.castSucc) := by
  intro v
  exact hat v.castSucc

/-- Writing an output pointer before a label table preserves all its pairs. -/
theorem SignedTableAt.store_before {n : ℕ} {mem : ℕ → ℕ} {a dst value : ℕ} {f : Fin n → ℤ}
    (hat : SignedTableAt mem a f) (hbefore : dst < a) :
    SignedTableAt (Function.update mem dst value) a f := by
  apply hat.of_agree
  intro x hx _
  exact Function.update_of_ne (by omega : x ≠ dst) _ _

end MinCostFlow.Scaling.Machine
