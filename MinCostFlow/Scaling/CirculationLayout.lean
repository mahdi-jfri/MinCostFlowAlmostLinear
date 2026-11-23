module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Memory
import WordRAM.Entry

/-!
# Indexed access to the shared circulation layout

The traversals load an edge's endpoints and cost from its saved edge index.
The solver layout has a two-word header and exactly five words per edge.
This file proves that indexing rule directly from the stored list, as well
as the header lookup. No new circulation encoding is introduced.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The first two stored circulation words are its dimensions. -/
theorem solver_header_at (J : Circulation) {mem : ℕ → ℕ} {a : ℕ}
    (hat : ListAt mem a J.solverWords) : mem a = J.n ∧ mem (a+1) = J.m := by
  have hn := hat 0 (by rw [J.solverWords_length]; omega)
  have hm := hat 1 (by rw [J.solverWords_length]; omega)
  simpa only [Circulation.solverWords, Nat.add_zero, List.getElem_cons_zero,
    List.getElem_cons_succ] using And.intro hn hm

/-- Uniform five-word records expose the selected stored edge. -/
theorem solverEdgeRecords_at (J : Circulation) (es : List (Fin J.m))
    {mem : ℕ → ℕ} {a : ℕ} (hat : ListAt mem a (es.flatMap J.solverEdgeWords))
    (i : Fin es.length) :
    ListAt mem (a+5*i.val) (J.solverEdgeWords (es[i.val]'i.isLt)) := by
  induction es generalizing a with
  | nil => exact Fin.elim0 i
  | cons e es ih =>
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using hhead
    | succ i =>
      have hi' : i < es.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have h := ih htail ⟨i, hi'⟩
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

/-- A saved edge index addresses its record at `graph+2+5*index`. -/
theorem solver_edge_at (J : Circulation) {mem : ℕ → ℕ} {a : ℕ}
    (hat : ListAt mem a J.solverWords) (e : Fin J.m) :
    ListAt mem (a+2+5*e.val) (J.solverEdgeWords e) := by
  have hedge := (listAt_cons.mp (listAt_cons.mp hat).2).2
  change ListAt mem (a+1+1) ((List.finRange J.m).flatMap J.solverEdgeWords) at hedge
  have hi : e.val < (List.finRange J.m).length := by simpa only [List.length_finRange] using e.isLt
  have h := solverEdgeRecords_at J (List.finRange J.m) hedge ⟨e.val, hi⟩
  have he : (List.finRange J.m)[e.val]'hi = e := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  rw [he] at h
  have haddr : a+1+1+5*e.val = a+2+5*e.val := by omega
  rwa [haddr] at h

/-- Canonical circulation memory realizes the indexed record layout. -/
theorem solver_edge_at_canonical (J : Circulation) (e : Fin J.m) :
    ListAt (initMem J.solverWords) (2+5*e.val) (J.solverEdgeWords e) := by
  simpa only [Nat.zero_add] using solver_edge_at J (listAt_initMem J.solverWords) e

end MinCostFlow.Scaling.Machine
