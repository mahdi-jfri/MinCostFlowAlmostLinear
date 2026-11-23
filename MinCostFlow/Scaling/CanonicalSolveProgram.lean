module

public import MinCostFlow.Scaling.CanonicalWrapperModule
public import MinCostFlow.Scaling.CanonicalWordBoundProgram
import WordRAM.Tactic
import WordRAM.Entry

/-!
# A canonical solve from a circulation address

This entry reads the circulation's edge count, computes its encoded length
and canonical guest word bound, and calls the proved copying and relocation
wrapper. Its output is exactly the function `canonicalSolver` used by the
scaling model. Neither the guest width nor the solver's choice of an optimum
is supplied as an additional mathematical oracle.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,heap]`, with entries for guest-bound computation and
the canonical wrapper. The unsigned output starts at the old heap. -/
def canonicalSolveBody (bound wrapper : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.bin .add (.const 2) (.bin .mul (.const 5) (.reg 2))) ;;
  .call 4 bound [.reg 0, .reg 3] ;;
  .call 5 wrapper [.reg 0, .reg 3, .reg 4, .reg 1] ;;
  .ret (.reg 5)

/-- The complete canonical solve returns the model function with fresh-heap
framing and the costs of guest setup, copying, and the solver itself. -/
def canonicalSolveContract (w : ℕ) (Q : Program) (f : ℕ)
    (T : ℕ → ℕ → ℕ) (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, h] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ h ∧
      2 ^ (wordSize 5 J.solverWords + 1) + 2 ≤ 2 ^ w)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) = canonicalSolver Q f T hproc J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      80 * J.solverWords.length + 40 * wordSize 5 J.solverWords + Q.regBound + 300)
    (fun _ _ => 1 + 2 ^ wordSize 5 J.solverWords)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ wordSize 5 J.solverWords }

/-- Canonical entry setup has no random instructions. -/
theorem canonicalSolveBody_noRand (bound wrapper : ℕ) :
    (canonicalSolveBody bound wrapper).NoRand := by
  simp only [canonicalSolveBody, Stmt.NoRand, and_self]

/-- The executable canonical entry computes exactly `canonicalSolver` on
bounded circulations, at the stated setup and solver cost. -/
theorem canonicalSolve_meetsContract
    {w entry bound wrapper : ℕ} {Q P : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation)
    (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hentry : P.procs[entry]? = some (canonicalSolveBody bound wrapper))
    (hbound : P.HasAt bound canonicalWordBoundModule)
    (hwrap : P.HasAt wrapper (canonicalWrapperModule Q f wrapper)) :
    MeetsContract w P entry (canonicalSolveContract w Q f T hproc J) := by
  let guestWidth := wordSize 5 J.solverWords
  have hin := canonicalInput_wordSize T J hc hu
  have hkB := canonicalWordBound_meetsContract (w := w) hbound J
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hdoubled⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  change 2 ^ (guestWidth + 1) + 2 ≤ 2 ^ w at hdoubled
  have hw : guestWidth ≤ w := by
    have hW : 2 ^ guestWidth < 2 ^ w := by omega
    exact Nat.le_of_lt (Nat.pow_lt_pow_iff_right (by decide : 1 < 2) |>.mp hW)
  have hkW := canonicalWrapperModule_meetsContract (hproc guestWidth) hdet J hin hwrap hw
  have hsize := J.solverWords_length
  have hlen : J.solverWords.length < 2 ^ guestWidth :=
    hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have h5m : 5 * J.m < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by
    have hlen2 : 2 < 2 ^ guestWidth := by omega
    have hp : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
    rw [Nat.pow_succ] at hdoubled
    omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  apply runs_start_le
  unfold canonicalSolveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.solverWords.length) (by
    conv_rhs => rw [hsize]
    apply Expr.eval_add (Expr.eval_const htwo)
      (Expr.eval_mul (Expr.eval_const hfive) ?_ h5m) (hsize ▸ hl)
    simp only [Expr.eval_reg, Function.update_self]) ?_
  refine runs_seq_call_le hkB (vs := [a, J.solverWords.length]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a, rfl, hat, by omega, hdoubled⟩
  · intro W memB posB hpostB
    obtain ⟨hmemB, hW⟩ := hpostB
    change memB = mem at hmemB
    subst memB
    change W = 2 ^ guestWidth at hW
    have hWword : W < 2 ^ w := by omega
    refine runs_seq_call_le hkW (vs := [a, J.solverWords.length, W, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · rw [hW]
      exact ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩
    · intro out memW posW hpostW
      rw [hW] at hpostW
      have hptr := hpostW.2
      change out = heap + 1 + 2 ^ guestWidth at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + (1 + 2 ^ guestWidth) ∧
          (∀ x < heap, memW x = mem x) ∧ ZeroFrom memW out ∧
          J.readSolverFlow memW heap = canonicalSolver Q f T hproc J) ∧
          out = heap + 1 + 2 ^ guestWidth
        rw [canonicalSolver_eq]
        exact hpostW
      · simp only [canonicalSolveContract, heapContract, canonicalWordBoundContract,
          canonicalWrapperContract, Expr.size_load, Expr.size_bin, Expr.size_reg,
          Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- The complete entry's argument, fresh-memory, and doubled-bound
preconditions hold together on a concrete memory for every circulation. -/
theorem exists_canonicalSolve_pre (Q : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w, MeetsContract w Q f (solverContract w T solverScratch)) (J : Circulation) :
    ∃ w, (∀ a ∈ [0, J.solverWords.length], a < 2 ^ w) ∧
      (canonicalSolveContract w Q f T hproc J).pre [0, J.solverWords.length]
        (initMem J.solverWords) := by
  let W := 2 ^ wordSize 5 J.solverWords
  let w := wordSize 1 [J.solverWords.length + 2 * W + 10]
  have hlarge : J.solverWords.length + 2 * W + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  have hp : 0 < W := Nat.two_pow_pos _
  refine ⟨w, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · refine ⟨⟨0, J.solverWords.length, rfl, listAt_initMem J.solverWords,
      by omega, ?_⟩, zeroFrom_initMem J.solverWords, ?_⟩
    · rw [Nat.pow_succ]
      change W * 2 + 2 ≤ 2 ^ w
      omega
    · change J.solverWords.length + (1 + W) < 2 ^ w
      omega

end MinCostFlow.Scaling.Machine
