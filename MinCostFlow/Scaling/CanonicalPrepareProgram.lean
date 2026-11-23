module

public import MinCostFlow.Scaling.CanonicalCallContract
public import WordRAM.CopyWords
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Preparing fresh memory for a canonical solver call

A deterministic solver may read unused memory, so a relocated canonical
call needs the encoded input followed by zeros in its entire guest region.
This procedure copies only the input to fresh memory. Reserving the guest
region does not require writing its zero tail. Its cost is linear in the
input length, even when the reserved address range is much larger.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,inputLength,guestWordBound,heap]`. The copied input
starts at `heap+1`. The return value reserves the whole guest region. -/
def canonicalPrepareBody (copy : ℕ) : Stmt :=
  .call 4 copy [.reg 0, .bin .add (.reg 3) (.const 1), .reg 1] ;;
  .ret (.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 2))

/-- Preparation and the shared contiguous copy procedure. -/
def canonicalPrepareModule (b : ℕ) : List Stmt :=
  [canonicalPrepareBody (b + 1), copyWords]

/-- The canonical region contains the input followed by zero words. -/
def canonicalPrepareContract (w guestWidth : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, J.solverWords.length, 2 ^ guestWidth, h] ∧
      ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h ∧
      J.solverWords.length < 2 ^ guestWidth)
    (fun args _ mem' => ∀ i < 2 ^ guestWidth,
      mem' (heapArg args + 1 + i) = initMem J.solverWords i)
    (fun _ _ => 20 * J.solverWords.length + 50)
    (fun _ _ => 1 + 2 ^ guestWidth)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 1 + 2 ^ guestWidth }

/-- Neither the preparation body nor the copy procedure reads random bits. -/
theorem canonicalPrepareModule_noRand (b : ℕ) :
    ∀ body ∈ canonicalPrepareModule b, body.NoRand := by
  simp only [canonicalPrepareModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  constructor
  · simp only [canonicalPrepareBody, Stmt.NoRand, and_self]
  · simp only [copyWords, forRange, forUp, Stmt.NoRand, and_self]

/-- The input is copied exactly, its unused guest memory remains zero, and
reservation costs only linear time in the input length. -/
theorem canonicalPrepare_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (canonicalPrepareModule b)) (guestWidth : ℕ) (J : Circulation) :
    MeetsContract w p b (canonicalPrepareContract w guestWidth J) := by
  have hcopy : p.HasAt (b + 1) [copyWords] := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [canonicalPrepareModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [canonicalPrepareModule])
  have hk := copyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hlen⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (1 + 2 ^ guestWidth) < 2 ^ w at hspace
  have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hl : J.solverWords.length < 2 ^ w := by omega
  have hW : 2 ^ guestWidth < 2 ^ w := by omega
  have hbase : heap + 1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hret : heap + 1 + 2 ^ guestWidth < 2 ^ w := by omega
  apply runs_start_le
  unfold canonicalPrepareBody
  refine runs_seq_call_le hk (vs := [a, heap + 1, J.solverWords.length]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨a, heap + 1, J.solverWords.length, rfl, hone, by omega, by omega,
      Or.inr (by omega)⟩
  · intro _ mem' pos' hpost
    obtain ⟨src, dst, len, hargs, _, hcopied, hframe⟩ := hpost
    have hs : src = a := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 0 0) hargs
      simpa only [List.getD_cons_zero] using hh.symm
    have hd : dst = heap + 1 := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 1 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
    have hl' : len = J.solverWords.length := by
      have hh := congrArg (fun xs : List ℕ => xs.getD 2 0) hargs
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
    subst src; subst dst; subst len
    change (∀ i < J.solverWords.length, mem' (heap + 1 + i) = mem (a + i)) at hcopied
    change (∀ x, x < heap + 1 ∨ heap + 1 + J.solverWords.length ≤ x →
      mem' x = mem x) at hframe
    refine runs_ret_le (v := heap + 1 + 2 ^ guestWidth) (by eval_expr) ?_ ?_
    · change (heap ≤ heap + 1 + 2 ^ guestWidth ∧
        heap + 1 + 2 ^ guestWidth ≤ heap + (1 + 2 ^ guestWidth) ∧
        (∀ x < heap, mem' x = mem x) ∧
        ZeroFrom mem' (heap + 1 + 2 ^ guestWidth) ∧
        (∀ i < 2 ^ guestWidth, mem' (heap + 1 + i) = initMem J.solverWords i)) ∧
        heap + 1 + 2 ^ guestWidth = heap + 1 + 2 ^ guestWidth
      refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, rfl⟩
      · intro x hx
        exact hframe x (Or.inl (by omega))
      · intro x hx
        exact (hframe x (Or.inr (by omega))).trans (hzero x (by omega))
      · intro i _
        by_cases hi : i < J.solverWords.length
        · rw [hcopied i hi, hat i hi]
          simp only [initMem, List.getD_eq_getElem _ _ hi]
        · rw [hframe _ (Or.inr (by omega)), hzero _ (by omega)]
          simp only [initMem, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
    · simp only [canonicalPrepareContract, heapContract, copyWordsContract,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega

/-- Every admissible canonical input has a concrete fresh-memory preparation
whose argument words and allocation bounds all hold together. -/
theorem exists_canonicalPrepare_pre {guestWidth : ℕ} {T : ℕ → ℕ → ℕ}
    (J : Circulation) (hin : CanonicalInput guestWidth T J) :
    ∃ w, (∀ a ∈ [0, J.solverWords.length, 2 ^ guestWidth, J.solverWords.length],
      a < 2 ^ w) ∧
      (canonicalPrepareContract w guestWidth J).pre
        [0, J.solverWords.length, 2 ^ guestWidth, J.solverWords.length]
        (initMem J.solverWords) := by
  let w := wordSize 1 [J.solverWords.length + 1 + 2 ^ guestWidth + 2]
  have hlarge : J.solverWords.length + 1 + 2 ^ guestWidth + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  have hpositive : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
  refine ⟨w, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · refine ⟨⟨0, J.solverWords.length, rfl, listAt_initMem J.solverWords,
      by omega, hin.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self))⟩,
      zeroFrom_initMem J.solverWords, ?_⟩
    change J.solverWords.length + (1 + 2 ^ guestWidth) < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
