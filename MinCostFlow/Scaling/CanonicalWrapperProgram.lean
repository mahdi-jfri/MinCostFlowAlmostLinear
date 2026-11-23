module

public import MinCostFlow.Scaling.CanonicalPrepareProgram
public import MinCostFlow.Scaling.CanonicalCallExpressions
import WordRAM.Tactic

/-!
# The canonical solver wrapper

The outer scaling loops call this wrapper instead of calling a solver in
an arbitrary machine context. It copies the circulation to a fresh canonical
guest region, passes the relocation registers, runs the solver, and copies
the unsigned integral flow back to the old heap. The reserved guest block
remains scratch space. Its cost is the relocated solver cost plus linear
input and output copying and the fixed call-argument setup.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,inputLength,guestWordBound,heap]`. -/
def canonicalWrapperBody (Q : Program) (prepare solver copy : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 6 prepare [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .assign 4 (.bin .add (.reg 3) (.const 1)) ;;
  .call 7 solver (canonicalCallExprs Q) ;;
  .call 8 copy [.bin .add (.reg 4) (.reg 1), .reg 3, .reg 5] ;;
  .ret (.reg 6)

/-- Exact canonical output at the old heap, with the entire guest region
reserved as scratch. The guest width is supplied through its word bound. -/
def canonicalWrapperContract (w guestWidth : ℕ) (Q : Program) (f : ℕ)
    (T : ℕ → ℕ → ℕ) (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, J.solverWords.length, 2 ^ guestWidth, h] ∧
      ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h)
    (fun args _ mem' => J.readSolverFlow mem' (heapArg args) =
      canonicalSolverAt guestWidth Q f T hproc J)
    (fun _ _ => (Q.regBound + 6) * T J.n J.m +
      40 * J.solverWords.length + Q.regBound + 200)
    (fun _ _ => 1 + 2 ^ guestWidth)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ guestWidth }

/-- The wrapper body itself uses no random instruction. -/
theorem canonicalWrapperBody_noRand (Q : Program) (prepare solver copy : ℕ) :
    (canonicalWrapperBody Q prepare solver copy).NoRand := by
  simp only [canonicalWrapperBody, Stmt.NoRand, and_self]

/-- The executable wrapper computes the fixed canonical model function,
with exact heap framing and an explicit cost for every call and copy. -/
theorem canonicalWrapper_meetsContract
    {guestWidth w b prepare copy entry : ℕ} {Q P : Program} {f : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : MeetsContract guestWidth Q f (solverContract guestWidth T solverScratch))
    (hdet : Q.IsDeterministic) (J : Circulation) (hin : CanonicalInput guestWidth T J)
    (hentry : P.procs[entry]? =
      some (canonicalWrapperBody Q prepare (b + 1 + f) copy))
    (hprepare : P.HasAt prepare (canonicalPrepareModule prepare))
    (hcopy : P.HasAt copy [copyWords])
    (hmodule : ∀ k body, Q.procs[k]? = some body →
      P.procs[b + 1 + k]? = some (relocStmt Q.regBound b body))
    (hw : guestWidth ≤ w) :
    MeetsContract w P entry (canonicalWrapperContract w guestWidth Q f T hproc J) := by
  have hkP := canonicalPrepare_meetsContract (w := w) hprepare guestWidth J
  have hkC := copyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have houtput := hin.output_fits
  have hlen := hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have hW : 2 ^ guestWidth < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have hbase : heap + 1 < 2 ^ w := by omega
  have hsource : heap + 1 + J.solverWords.length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hfour : 4 ≤ 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have hh := hat 1 (by rw [hsize]; omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ,
      List.getElem_cons_zero] using hh
  have hkS := canonicalCall_meetsContract hproc hdet J hin hmodule hw
    (by omega : heap + 1 + 2 ^ guestWidth ≤ 2 ^ w) hfour
  apply runs_start_le
  unfold canonicalWrapperBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a, J.solverWords.length, 2 ^ guestWidth, heap])
    (by eval_expr) ?_ ?_ ?_
  · exact hwords
  · exact ⟨⟨a, heap, rfl, hat, hend, hlen⟩, hzero, hspace⟩
  · intro finalHeap memP posP hpostP
    obtain ⟨⟨_, _, hframeP, hzeroP, hcanonical⟩, hptr⟩ := hpostP
    change finalHeap = heap + 1 + 2 ^ guestWidth at hptr
    change (∀ x < heap, memP x = mem x) at hframeP
    change ZeroFrom memP finalHeap at hzeroP
    change (∀ i < 2 ^ guestWidth,
      memP (heap + 1 + i) = initMem J.solverWords i) at hcanonical
    have hfinal : finalHeap < 2 ^ w := by omega
    refine runs_seq_assign_le (v := heap + 1) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := canonicalCallArgs Q J guestWidth heap) ?_ ?_ ?_ ?_
    · apply canonicalCallExprs_eval
      · simp [startState]
      · simp
      · simp [startState]
      · exact hl
    · exact canonicalCallArgs_words hin hw (by omega)
    · exact ⟨rfl, hcanonical⟩
    · intro _ memS posS hpostS
      obtain ⟨hflow, hframeS⟩ := hpostS
      change J.readSolverFlow memS (heap + 1 + J.solverWords.length) =
        canonicalSolverAt guestWidth Q f T hproc J at hflow
      change (∀ x, x < heap + 1 ∨ heap + 1 + 2 ^ guestWidth ≤ x →
        memS x = memP x) at hframeS
      refine runs_seq_call_le hkC (vs := [heap + 1 + J.solverWords.length, heap, J.m])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨heap + 1 + J.solverWords.length, heap, J.m, rfl, hone,
          by omega, by omega, Or.inl (by omega)⟩
      · intro _ memC posC hpostC
        obtain ⟨src, dst, len, hargs, _, hcopied, hframeC⟩ := hpostC
        have hs : src = heap + 1 + J.solverWords.length := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
          simpa only [List.getD_cons_zero] using hh.symm
        have hd : dst = heap := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        have hl' : len = J.m := by
          have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
        subst src; subst dst; subst len
        change (∀ i < J.m, memC (heap + i) =
          memS (heap + 1 + J.solverWords.length + i)) at hcopied
        change (∀ x, x < heap ∨ heap + J.m ≤ x → memC x = memS x) at hframeC
        refine runs_ret_le (v := finalHeap) (by eval_expr) ?_ ?_
        · change (heap ≤ finalHeap ∧ finalHeap ≤ heap + (1 + 2 ^ guestWidth) ∧
            (∀ x < heap, memC x = mem x) ∧ ZeroFrom memC finalHeap ∧
            J.readSolverFlow memC heap = canonicalSolverAt guestWidth Q f T hproc J) ∧
            finalHeap = heap + 1 + 2 ^ guestWidth
          refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, hptr⟩
          · intro x hx
            exact (hframeC x (Or.inl hx)).trans
              ((hframeS x (Or.inl (by omega))).trans (hframeP x hx))
          · intro x hx
            exact (hframeC x (Or.inr (by omega))).trans
              ((hframeS x (Or.inr (by omega))).trans (hzeroP x hx))
          · rw [← hflow]
            funext e
            exact congrArg (fun v : ℕ => (v : ℤ)) (hcopied e.val e.isLt)
        · simp only [canonicalWrapperContract, heapContract, canonicalPrepareContract,
            canonicalCallContract, copyWordsContract, canonicalCallExprs_size,
            argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega

end MinCostFlow.Scaling.Machine
