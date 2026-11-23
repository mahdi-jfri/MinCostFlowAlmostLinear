module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.EqualityFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Equality of signed fixed-point numbers

A scan compares corresponding limbs and stops at the first difference. Uniqueness of
valid encodings makes this a test of signed integer equality, and hence of fixed-point
equality at a shared precision. The procedure allocates nothing and preserves all memory.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L]`; the remaining limbs are checked by a recursive call. -/
def equalBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 1))
    (.cond (.bin .eq (.load (.reg 0)) (.load (.reg 1)))
      (.call 3 b [.bin .add (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1),
        .bin .sub (.reg 2) (.const 1)] ;; .ret (.reg 3))
      (.ret (.const 0)))

/-- A module for equality at entry `b`. -/
def equalModule (b : ℕ) : List Stmt := [equalBody b]

/-- Return one exactly when the signed integers agree. Cost at most `23 * L + 6`. -/
def equalContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d L, args = [a, d, L] ∧ a + L < 2 ^ w ∧ d + L < 2 ^ w ∧
    Valid mem a h L ∧ Valid mem d h L
  post args mem v mem' := mem' = mem ∧ v =
    if intVal mem (args.getD 0 0) h (args.getD 2 0) =
      intVal mem (args.getD 1 0) h (args.getD 2 0) then 1 else 0
  cost args _ := 23 * args.getD 2 0 + 6

/-- The equality procedure uses no random bits. -/
theorem equalBody_noRand (b : ℕ) : (equalBody b).NoRand := by
  simp [equalBody, Stmt.NoRand]

/-- Equality has a linear cost and preserves all memory. -/
theorem equal_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (equalModule b)) : MeetsContract w p b (equalContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a, d, L, rfl, ha, hd, hva, hvd⟩
  change L = k at hk
  subst k
  apply runs_start_le
  unfold equalBody
  wram_step
  · have hz : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 1 = if intVal mem a h 0 = intVal mem d h 0 then 1 else 0
      simp [intVal, unsignedVal]
    · simp only [equalContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hta := (valid_succ.mp hva).2
    have htd := (valid_succ.mp hvd).2
    wram_step
    · have he : mem a = mem d := by simpa [startState] using hcond
      refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
      · wram_words
      · change (∃ a' d' L', [a + 1, d + 1, M + 1 - 1] = [a', d', L'] ∧
          a' + L' < 2 ^ w ∧ d' + L' < 2 ^ w ∧ Valid mem a' h L' ∧ Valid mem d' h L') ∧
          M + 1 - 1 < M + 1
        exact ⟨⟨a + 1, d + 1, M, by simp, by omega, by omega, hta, htd⟩, by omega⟩
      · intro v mem' pos' hpst
        rcases hpst with ⟨hmem, hv⟩
        subst mem'
        change v = if intVal mem (a + 1) h M = intVal mem (d + 1) h M then 1 else 0 at hv
        have hvword : v < 2 ^ w := by split_ifs at hv <;> omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change mem = mem ∧ v = if intVal mem a h (M + 1) = intVal mem d h (M + 1) then 1 else 0
          refine ⟨rfl, ?_⟩
          simpa only [intVal_eq_succ_iff hva hvd, he, true_and] using hv
        · simp only [equalContract, Contract.below, List.getD_cons_zero, List.getD_cons_succ,
            Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
            argsSize_cons, argsSize_nil]
          omega
    · have he : mem a ≠ mem d := by simpa [startState] using hcond
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 0 = if intVal mem a h (M + 1) = intVal mem d h (M + 1) then 1 else 0
        have hne : intVal mem a h (M + 1) ≠ intVal mem d h (M + 1) :=
          fun h => he ((intVal_eq_succ_iff hva hvd).mp h).1
        simp only [ite_eq_right hne, and_self]
      · simp only [equalContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
        omega

end MinCostFlow.Num
