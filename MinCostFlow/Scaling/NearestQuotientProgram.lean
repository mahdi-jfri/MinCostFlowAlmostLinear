module

public import MinCostFlow.Scaling.CostLoopModel
public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Integer rounding for the cost-scaling loop

Definition C.6 of Chen et al., arXiv:2203.00671v2, rounds reduced residual
costs. The integer model uses `nearestQuotient`: add half the positive
denominator to the magnitude, divide, and restore the sign. This procedure
computes that exact function and writes its canonical signed pair, including
zero produced by rounding a small negative input. It allocates two words,
has no random instructions, and costs at most 100 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A zero rounded magnitude has canonical zero sign. -/
theorem encodeInt_nearestQuotient_zero (z : ℤ) (d : ℕ)
    (hq : (z.natAbs + d / 2) / d = 0) : encodeInt (nearestQuotient z d) = [0, 0] := by
  simp only [nearestQuotient, hq, Nat.cast_zero, neg_zero, ite_self]
  rfl

/-- A nonzero rounded magnitude retains the original sign. -/
theorem encodeInt_nearestQuotient_nonzero (z : ℤ) (d : ℕ)
    (hq : (z.natAbs + d / 2) / d ≠ 0) :
    encodeInt (nearestQuotient z d) =
      [if z < 0 then 1 else 0, (z.natAbs + d / 2) / d] := by
  let q := (z.natAbs + d / 2) / d
  have hqp : 0 < q := Nat.pos_of_ne_zero hq
  by_cases hz : z < 0
  · have hneg : -(q : ℤ) < 0 := by omega
    change encodeInt (if z < 0 then -(q : ℤ) else (q : ℤ)) = _
    simp only [hz, ↓reduceIte, encodeInt, hneg, Int.natAbs_neg, Int.natAbs_natCast]
    rfl
  · have hn : ¬(q : ℤ) < 0 := by omega
    change encodeInt (if z < 0 then -(q : ℤ) else (q : ℤ)) = _
    simp only [hz, ↓reduceIte, encodeInt, hn, Int.natAbs_natCast]
    rfl

/-- Arguments `[sign,magnitude,denominator,heap]`. -/
def nearestQuotientBody (writer : ℕ) : Stmt :=
  .assign 4 (.bin .div (.bin .add (.reg 1) (.bin .div (.reg 2) (.const 2))) (.reg 2)) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.call 5 writer [.const 0, .const 0, .reg 3] ;; .ret (.reg 5))
    (.call 5 writer [.reg 0, .reg 4, .reg 3] ;; .ret (.reg 5))

/-- Exact signed rounding followed by its canonical pair writer. -/
def nearestQuotientModule (b : ℕ) : List Stmt := [nearestQuotientBody (b + 1), wordPairBody]

/-- The model uses positive denominators. The adjusted magnitude must fit
as well as the supplied argument words. -/
def nearestQuotientContract (w : ℕ) (z : ℤ) (d : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [if z < 0 then 1 else 0, z.natAbs, d, heap] ∧
      0 < d ∧ z.natAbs + d / 2 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (nearestQuotient z d)))
    (fun _ _ => 100) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 2 }

/-- Both exact rounding procedures have no random instructions. -/
theorem nearestQuotientModule_noRand (b : ℕ) :
    ∀ body ∈ nearestQuotientModule b, body.NoRand := by
  simp only [nearestQuotientModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [nearestQuotientBody, Stmt.NoRand, and_self], wordPairBody_noRand⟩

/-- The procedure computes exactly the integer cost-rounding function,
with canonical zero, exact allocation, and constant machine cost. -/
theorem nearestQuotient_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (nearestQuotientModule b)) (z : ℤ) (d : ℕ) :
    MeetsContract w p b (nearestQuotientContract w z d) := by
  have hwriter : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [nearestQuotientModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [nearestQuotientModule])
  have hk := wordPair_meetsContract (w := w) hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hd, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hz : z.natAbs < 2 ^ w := by omega
  have hdword : d < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  have hdhalf : d / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hdword
  have hqword : (z.natAbs + d / 2) / d < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hsum
  have hsword : (if z < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hh : heap < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold nearestQuotientBody
  wram_step
  wram_step
  · have hq : (z.natAbs + d / 2) / d = 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_nearestQuotient_zero z d hq
    refine runs_seq_call_le hk (vs := [0, 0, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨0, 0, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (nearestQuotient z d))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [nearestQuotientContract, heapContract, wordPairContract,
          Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega
  · have hq : (z.natAbs + d / 2) / d ≠ 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_nearestQuotient_nonzero z d hq
    refine runs_seq_call_le hk
      (vs := [if z < 0 then 1 else 0, (z.natAbs + d / 2) / d, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (nearestQuotient z d))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [nearestQuotientContract, heapContract, wordPairContract,
          Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- Every integer and positive denominator have simultaneous witnesses for all arithmetic and
allocation premises together at a sufficiently large width. -/
theorem exists_nearestQuotient_pre (z : ℤ) (d : ℕ) (hd : 0 < d) :
    ∃ w, (∀ x ∈ [if z < 0 then 1 else 0, z.natAbs, d, 0], x < 2 ^ w) ∧
      (nearestQuotientContract w z d).pre
        [if z < 0 then 1 else 0, z.natAbs, d, 0] (fun _ => 0) := by
  let w := wordSize 1 [z.natAbs + d + 10]
  have hlarge : z.natAbs + d + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  have hh := Nat.div_le_self d 2
  refine ⟨w, ?_, ⟨0, rfl, hd, by omega⟩, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · omega
    · omega
  · change 0 + 2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
