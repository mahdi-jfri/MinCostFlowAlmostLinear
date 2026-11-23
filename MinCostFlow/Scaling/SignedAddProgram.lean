module

public import MinCostFlow.Scaling.SignedAdditionFacts
public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Constant-cost addition of two input integers

The flow-to-circulation reductions add signed demands and capacities. Their
values fit in one word in magnitude, so the statement's sign/magnitude pair
needs no multiword arithmetic. This procedure adds two canonical pairs,
handles cancellation explicitly, allocates `encodeInt (x+y)`, and returns
the new heap pointer. It uses no random instructions and costs at most 80.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Write a selected sign and magnitude through the shared pair writer. -/
def signedAddFinish (writer : ℕ) (sign magnitude : Expr) : Stmt :=
  .call 5 writer [sign, magnitude, .reg 4] ;; .ret (.reg 5)

/-- Arguments are the two canonical signed pairs followed by the heap. -/
def signedAddBody (writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.reg 2))
    (signedAddFinish writer (.reg 0) (.bin .add (.reg 1) (.reg 3)))
    (.cond (.bin .lt (.reg 1) (.reg 3))
      (signedAddFinish writer (.reg 2) (.bin .sub (.reg 3) (.reg 1)))
      (.cond (.bin .eq (.reg 1) (.reg 3))
        (signedAddFinish writer (.const 0) (.const 0))
        (signedAddFinish writer (.reg 0) (.bin .sub (.reg 1) (.reg 3)))))

/-- Addition followed by its two-word writer. -/
def signedAddModule (b : ℕ) : List Stmt := [signedAddBody (b + 1), wordPairBody]

/-- Canonical integer addition, assuming the sum of the two magnitudes fits. -/
def signedAddContract (w : ℕ) (x y : ℤ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args =
      [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, heap] ∧
      x.natAbs + y.natAbs < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (x + y)))
    (fun _ _ => 80) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 2 }

/-- Both addition procedures are deterministic. -/
theorem signedAddModule_noRand (b : ℕ) : ∀ body ∈ signedAddModule b, body.NoRand := by
  simp only [signedAddModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [signedAddBody, signedAddFinish, Stmt.NoRand, and_self], wordPairBody_noRand⟩

/-- Signed addition returns the exact canonical result with the shared heap
frame, two allocated words, and constant cost on every random tape. -/
theorem signedAdd_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedAddModule b)) (x y : ℤ) :
    MeetsContract w p b (signedAddContract w x y) := by
  have hwriter : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, signedAddModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [signedAddModule])
  have hk := wordPair_meetsContract (w := w) hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hmagnitudes⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hxword : x.natAbs < 2 ^ w := by omega
  have hyword : y.natAbs < 2 ^ w := by omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := hwords _ (List.mem_cons_self)
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w :=
    hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  have hhword : heap < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold signedAddBody
  wram_step
  · have hsign : (if x < 0 then 1 else 0 : ℕ) = if y < 0 then 1 else 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_add_same_sign x y hsign
    unfold signedAddFinish
    refine runs_seq_call_le hk (vs := [if x < 0 then 1 else 0, x.natAbs + y.natAbs, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (x + y))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [signedAddContract, heapContract, wordPairContract, Expr.size_bin,
          Expr.size_reg, argsSize_cons, argsSize_nil]
        omega
  · have hsign : (if x < 0 then 1 else 0 : ℕ) ≠ if y < 0 then 1 else 0 := by simpa [startState] using hcond
    wram_step
    · have hlt : x.natAbs < y.natAbs := by simpa [startState] using hcond
      have hencoding := encodeInt_add_second_larger x y hsign hlt
      unfold signedAddFinish
      refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
      · intro out mem' pos' hpost
        have hptr := hpost.2
        change out = heap + 2 at hptr
        have houtword : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
            ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (x + y))) ∧ out = heap + 2
          rw [hencoding]
          exact hpost
        · simp only [signedAddContract, heapContract, wordPairContract, Expr.size_bin,
            Expr.size_reg, argsSize_cons, argsSize_nil]
          omega
    · have hnlt : ¬x.natAbs < y.natAbs := by simpa [startState] using hcond
      wram_step
      · have heq : x.natAbs = y.natAbs := by simpa [startState] using hcond
        have hencoding := encodeInt_add_cancel x y hsign heq
        unfold signedAddFinish
        refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
        · intro out mem' pos' hpost
          have hptr := hpost.2
          change out = heap + 2 at hptr
          have houtword : out < 2 ^ w := by omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
              ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (x + y))) ∧ out = heap + 2
            rw [hencoding]
            exact hpost
          · simp only [signedAddContract, heapContract, wordPairContract, Expr.size_bin,
              Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
            omega
      · have hneq : x.natAbs ≠ y.natAbs := by simpa [startState] using hcond
        have hlt : y.natAbs < x.natAbs := by omega
        have hencoding := encodeInt_add_first_larger x y hsign hlt
        unfold signedAddFinish
        refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
        · intro out mem' pos' hpost
          have hptr := hpost.2
          change out = heap + 2 at hptr
          have houtword : out < 2 ^ w := by omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
              ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (x + y))) ∧ out = heap + 2
            rw [hencoding]
            exact hpost
          · simp only [signedAddContract, heapContract, wordPairContract, Expr.size_bin,
              Expr.size_reg, argsSize_cons, argsSize_nil]
            omega

/-- The signed-addition premises hold together for every two integers at a
sufficiently large word size and a fresh zero heap. -/
theorem exists_signedAdd_pre (x y : ℤ) :
    ∃ w, (∀ a ∈ [if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, 0], a < 2 ^ w) ∧
      (signedAddContract w x y).pre
        [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, 0] (fun _ => 0) := by
  let input := [1, x.natAbs, y.natAbs, x.natAbs + y.natAbs + 3]
  let w := wordSize 1 input
  have hbig : x.natAbs + y.natAbs + 3 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  refine ⟨w, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · split <;> omega
    · omega
    · omega
  · refine ⟨⟨0, rfl, by omega⟩, (fun _ _ => rfl), ?_⟩
    change 0 + 2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
