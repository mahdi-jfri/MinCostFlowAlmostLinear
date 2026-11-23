module

public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic

/-!
# Negating a one-word-magnitude signed integer

The lower-capacity and residual reductions in Appendix C negate signed
integers. The canonical zero pair stays zero. For a nonzero magnitude,
negation flips the sign bit and keeps the magnitude. This procedure writes
the result to two fresh words, costs at most 50, and has no random instruction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Negation flips the sign bit only for a nonzero input. -/
theorem encodeInt_neg_nonzero (x : ℤ) (hx : x.natAbs ≠ 0) :
    encodeInt (-x) = [1 - (if x < 0 then 1 else 0), x.natAbs] := by
  by_cases hn : x < 0
  · have hp : ¬-x < 0 := by omega
    simp only [encodeInt, hn, hp, ↓reduceIte, Nat.sub_self, Int.natAbs_neg]
  · have hp : -x < 0 := by omega
    simp only [encodeInt, hn, hp, ↓reduceIte, Nat.sub_zero, Int.natAbs_neg]

/-- Arguments `[sign,magnitude,heap]`, with a shared pair-writing entry. -/
def signedNegateBody (writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.call 3 writer [.const 0, .const 0, .reg 2] ;; .ret (.reg 3))
    (.call 3 writer [.bin .sub (.const 1) (.reg 0), .reg 1, .reg 2] ;; .ret (.reg 3))

/-- Negation and its two-word writer. -/
def signedNegateModule (b : ℕ) : List Stmt := [signedNegateBody (b + 1), wordPairBody]

/-- The input pair is the statement's canonical encoding. -/
def signedNegateContract (w : ℕ) (x : ℤ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [if x < 0 then 1 else 0, x.natAbs, heap])
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (-x)))
    (fun _ _ => 50) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 2 }

/-- Neither negation procedure reads random bits. -/
theorem signedNegateModule_noRand (b : ℕ) : ∀ body ∈ signedNegateModule b, body.NoRand := by
  simp only [signedNegateModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [signedNegateBody, Stmt.NoRand, and_self], wordPairBody_noRand⟩

/-- Signed negation returns the canonical negative with exact two-word
allocation and constant cost, including the zero case. -/
theorem signedNegate_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedNegateModule b)) (x : ℤ) :
    MeetsContract w p b (signedNegateContract w x) := by
  have hwriter : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, signedNegateModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [signedNegateModule])
  have hk := wordPair_meetsContract (w := w) hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hm : x.natAbs < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hs : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := hwords _ (List.mem_cons_self)
  have hh : heap < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold signedNegateBody
  wram_step
  · have hmag : x.natAbs = 0 := by simpa [startState] using hcond
    have hx : x = 0 := by omega
    have hencoding : encodeInt (-x) = [0, 0] := by rw [hx]; rfl
    refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨0, 0, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (-x))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [signedNegateContract, heapContract, wordPairContract, Expr.size_bin,
          Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega
  · have hmag : x.natAbs ≠ 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_neg_nonzero x hmag
    refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, mem' a = mem a) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (-x))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [signedNegateContract, heapContract, wordPairContract, Expr.size_bin,
          Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Scaling.Machine
