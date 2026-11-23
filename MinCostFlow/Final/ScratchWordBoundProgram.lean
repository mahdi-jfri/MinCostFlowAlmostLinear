module

public import MinCostFlow.Scaling.SolverContract
public import WordRAM.LinkDefs
public import WordRAM.Layout
import WordRAM.Link
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Computing the canonical guest word bound

The solver scratch policy chooses the guest word multiplier.
This procedure computes its power-of-two word bound from the stored input,
using WordRAM's proved scan and doubling loop. It reads memory without
changing it. The wrapper can therefore compute its relocation parameter
from the actual circulation instead of accepting it from an external oracle.
-/

@[expose] public section
namespace MinCostFlow.Final
open Scaling
open WordRAM

/-- Arguments `[source,inputLength]`, returning the canonical guest word bound. -/
def scratchWordBoundBody (multiplier : ℕ) : Stmt :=
  computeWordSizeStmt multiplier 0 1 2 3 4 5 6 ;; .ret (.reg 3)

/-- The word-bound computation occupies one procedure slot. -/
def scratchWordBoundModule (multiplier : ℕ) : List Stmt := [scratchWordBoundBody multiplier]

/-- The host has room for the scan and the doubled guest bound used by the
shared word-size procedure. -/
def scratchWordBoundContract (w multiplier : ℕ) (J : Circulation) : Contract where
  pre args mem := ∃ a, args = [a, J.solverWords.length] ∧
    ListAt mem a J.solverWords ∧ a + J.solverWords.length < 2 ^ w ∧
    2 ^ (wordSize multiplier J.solverWords + 1) + 2 ≤ 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = 2 ^ wordSize multiplier J.solverWords
  cost _ _ := 40 * (J.solverWords.length + wordSize multiplier J.solverWords + 1) + 5

/-- Computing the guest word bound has no random instructions. -/
theorem scratchWordBoundBody_noRand (multiplier : ℕ) : (scratchWordBoundBody multiplier).NoRand := by
  cases multiplier <;> simp only [scratchWordBoundBody, computeWordSizeStmt, Stmt.NoRand, and_self]

/-- The shared scan and doubling loop return exactly the bound used by
the scratch policy, with explicit cost and unchanged memory. -/
theorem scratchWordBound_meetsContract {w b multiplier : ℕ} {p : Program}
    (hp : p.HasAt b (scratchWordBoundModule multiplier)) (J : Circulation) :
    MeetsContract w p b (scratchWordBoundContract w multiplier J) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  obtain ⟨a, rfl, hat, hend, hbound⟩ := hpre
  have hW : 2 ^ wordSize multiplier J.solverWords < 2 ^ w := by
    have hp : 0 < 2 ^ wordSize multiplier J.solverWords := Nat.two_pow_pos _
    rw [Nat.pow_succ] at hbound
    omega
  have ht : Triple w p (fun st => st = startState [a, J.solverWords.length] mem pos)
      (computeWordSizeStmt multiplier 0 1 2 3 4 5 6)
      (normalPost fun st => st.mem = mem ∧ st.regs 3 = 2 ^ wordSize multiplier J.solverWords)
      (fun _ => 40 * (J.solverWords.length + wordSize multiplier J.solverWords + 1)) := by
    intro st ω' hst
    subst st
    obtain ⟨st', cost, hr, _, hW', hm, _, _, hc⟩ :=
      Link.computeWordSize_runs (p := p) (ω := ω') (c := multiplier)
        (aReg := 0) (lenReg := 1) (wReg := 2) (WReg := 3)
        (tmp1 := 4) (tmp2 := 5) (tmp3 := 6) (by decide)
        (show (startState [a, J.solverWords.length] mem pos).regs 0 = a by rfl)
        (show (startState [a, J.solverWords.length] mem pos).regs 1 = J.solverWords.length by rfl)
        hat hend hbound
    exact ⟨.normal, st', cost, hr, ⟨hm, hW'⟩, hc⟩
  apply runs_start_le
  unfold scratchWordBoundBody
  refine runs_seq_triple_le ht rfl ?_
  intro st ⟨hmem, hreg⟩
  refine runs_ret_le (v := 2 ^ wordSize multiplier J.solverWords) ?_ ?_ ?_
  · simpa only [hreg] using (Expr.eval_reg (w := w) (st := st) 3)
  · exact ⟨hmem, rfl⟩
  · simp only [scratchWordBoundContract, Expr.size_reg]
    omega

/-- A concrete memory and sufficiently large host width satisfy all
preconditions for every circulation encoding. -/
theorem exists_scratchWordBound_pre (multiplier : ℕ) (J : Circulation) :
    ∃ w, (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
      (scratchWordBoundContract w multiplier J).pre [0, J.solverWords.length]
        (initMem J.solverWords) := by
  let w := wordSize 1 [J.solverWords.length + 2 ^ (wordSize multiplier J.solverWords + 1) + 3]
  have hlarge : J.solverWords.length + 2 ^ (wordSize multiplier J.solverWords + 1) + 3 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  have hp : 0 < 2 ^ (wordSize multiplier J.solverWords + 1) := Nat.two_pow_pos _
  refine ⟨w, ?_, 0, rfl, listAt_initMem J.solverWords, by omega, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> omega

end MinCostFlow.Final
