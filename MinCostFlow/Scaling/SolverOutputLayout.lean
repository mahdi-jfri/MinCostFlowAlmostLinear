module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Memory
import WordRAM.Entry

/-!
# Reading the solver's unsigned output as a stored array

The solver contract identifies its output by `readSolverFlow`. The outer
adapter needs the corresponding contiguous unsigned array for erasing dummy
slots. Equality with the read function determines every stored magnitude,
so no additional solver-output condition is required.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The solver's output equality implies the exact unsigned table layout. -/
theorem solverOutput_listAt (J : Circulation) {mem : ℕ → ℕ} {heap : ℕ}
    {f : Fin J.m → ℤ} (hread : J.readSolverFlow mem heap = f) :
    ListAt mem heap (List.ofFn (fun e => (f e).toNat)) := by
  intro i hi
  have hi' : i < J.m := by simpa only [List.length_ofFn] using hi
  have he := congrFun hread ⟨i, hi'⟩
  change ((mem (heap+i) : ℕ) : ℤ) = f ⟨i, hi'⟩ at he
  have hn := congrArg Int.toNat he
  simpa only [Int.toNat_natCast, List.getElem_ofFn] using hn

/-- A contiguous unsigned table reads back to its nonnegative integral
vector, independently of any feasibility or optimality property. -/
theorem solverOutput_read_eq (J : Circulation) {mem : ℕ → ℕ} {heap : ℕ}
    {f : Fin J.m → ℤ} (hf : ∀ e,0≤f e)
    (hat : ListAt mem heap (List.ofFn (fun e => (f e).toNat))) :
    J.readSolverFlow mem heap=f := by
  funext e
  have h := hat e.val (by simpa only [List.length_ofFn] using e.isLt)
  rw [List.getElem_ofFn] at h
  change (mem (heap+e.val) : ℤ)=f e
  rw [h]
  exact Int.toNat_of_nonneg (hf e)

/-- Every nonnegative integer vector realizes the output equality and table
layout together in canonical output memory. -/
theorem exists_solverOutput_eq (J : Circulation) (f : Fin J.m → ℤ)
    (hf : ∀ e, 0 ≤ f e) :
    ∃ mem, J.readSolverFlow mem 0 = f ∧ ListAt mem 0 (List.ofFn (fun e => (f e).toNat)) := by
  let mem := initMem (List.ofFn (fun e => (f e).toNat))
  have hat : ListAt mem 0 (List.ofFn (fun e => (f e).toNat)) := listAt_initMem _
  refine ⟨mem, ?_, hat⟩
  funext e
  have hh := hat e.val (by simpa only [List.length_ofFn] using e.isLt)
  simp only [List.getElem_ofFn, Nat.zero_add] at hh
  change (mem (0+e.val) : ℤ) = f e
  rw [Nat.zero_add, hh]
  exact Int.toNat_of_nonneg (hf e)

end MinCostFlow.Scaling.Machine
