module

public import WordRAM.Contract
import WordRAM.Memory

/-!
# Placing the reduction's procedure modules

The circulation reductions assemble a header writer and several scans at
consecutive procedure indices. These helper lemmas split the shared
`Program.HasAt` condition along that list, so each scan uses exactly its
proved index. A concrete program containing the list realizes all of the
placement conditions at once.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A prefix of an installed module remains installed at the same base. -/
theorem hasAt_append_left {P : Program} {b : ℕ} {left right : List Stmt}
    (hp : P.HasAt b (left ++ right)) : P.HasAt b left := by
  intro i hi
  have h := hp i (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_left hi] using h

/-- A suffix is installed immediately after the prefix. -/
theorem hasAt_append_right {P : Program} {b : ℕ} {left right : List Stmt}
    (hp : P.HasAt b (left ++ right)) : P.HasAt (b + left.length) right := by
  intro i hi
  have h := hp (left.length + i) (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_right (by omega : left.length ≤ left.length + i),
    Nat.add_sub_cancel_left, Nat.add_assoc] using h

/-- Removing one installed entry advances the procedure base by one. -/
theorem hasAt_tail {P : Program} {b : ℕ} {body : Stmt} {rest : List Stmt}
    (hp : P.HasAt b (body :: rest)) : P.HasAt (b + 1) rest := by
  intro i hi
  have h := hp (i + 1) (by simp only [List.length_cons]; omega)
  have he : b + (i + 1) = b + 1 + i := by omega
  rw [he] at h
  simpa only [List.getElem_cons_succ] using h

/-- All bodies of a finite module occur at the advertised indices in the
program whose procedure list is that module. -/
theorem hasAt_self (bodies : List Stmt) : (Program.mk bodies).HasAt 0 bodies := by
  intro i hi
  simpa only [Nat.zero_add] using List.getElem?_eq_getElem hi

end MinCostFlow.Scaling.Machine
