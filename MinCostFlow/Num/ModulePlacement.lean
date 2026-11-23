module

public import WordRAM.Contract

/-!
# Linking arithmetic modules

An arithmetic procedure often links several already verified modules. These two
lemmas extract their placements from a concatenated body list, keeping the common
`Program.HasAt` interface unchanged.
-/

public section
namespace MinCostFlow.Num
open WordRAM

/-- The first part of a concatenated arithmetic module has the same base. -/
theorem hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (hp : p.HasAt b (xs ++ ys)) : p.HasAt b xs := by
  intro i hi
  have h := hp i (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_left hi] using h

/-- The second part starts immediately after the first part. -/
theorem hasAt_append_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (hp : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := by
  intro i hi
  have h := hp (xs.length + i) (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Nat.add_assoc] using h

end MinCostFlow.Num
