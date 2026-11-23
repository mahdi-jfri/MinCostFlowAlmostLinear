module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.OrderFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Comparing unsigned limb blocks

The procedure visits limbs from highest to lowest. A strict inequality ends the scan.
Equal limbs are dropped by reducing the length. It returns a Boolean word, changes no
memory, and costs at most `41*L + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L]`; equal top limbs recurse with length `L-1`. -/
def unsignedLessBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.cond (.bin .lt
      (.load (.bin .add (.reg 0) (.bin .sub (.reg 2) (.const 1))))
      (.load (.bin .add (.reg 1) (.bin .sub (.reg 2) (.const 1)))))
      (.ret (.const 1))
      (.cond (.bin .lt
        (.load (.bin .add (.reg 1) (.bin .sub (.reg 2) (.const 1))))
        (.load (.bin .add (.reg 0) (.bin .sub (.reg 2) (.const 1)))))
        (.ret (.const 0))
        (.call 3 b [.reg 0, .reg 1, .bin .sub (.reg 2) (.const 1)] ;; .ret (.reg 3))))

/-- The unsigned less-than helper. -/
def unsignedLessModule (b : ℕ) : List Stmt := [unsignedLessBody b]

/-- A Boolean unsigned comparison on two valid blocks of the same length. -/
def unsignedLessContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d L, args = [a, d, L] ∧ a + L < 2 ^ w ∧ d + L < 2 ^ w ∧
    Valid mem a h L ∧ Valid mem d h L
  post args mem v mem' := mem' = mem ∧ v =
    if unsignedVal mem (args.getD 0 0) h (args.getD 2 0) <
      unsignedVal mem (args.getD 1 0) h (args.getD 2 0) then 1 else 0
  cost args _ := 41 * args.getD 2 0 + 6

/-- The comparison does not read random bits. -/
theorem unsignedLessBody_noRand (b : ℕ) : (unsignedLessBody b).NoRand := by
  simp [unsignedLessBody, Stmt.NoRand]

/-- The unsigned comparison meets its read-only contract in linear time. -/
theorem unsignedLess_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (unsignedLessModule b)) :
    MeetsContract w p b (unsignedLessContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a, d, L, rfl, ha, hd, hva, hvd⟩
  change L = k at hk
  subst k
  apply runs_start_le
  unfold unsignedLessBody
  wram_step
  · have hz : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 0 = if unsignedVal mem a h 0 < unsignedVal mem d h 0 then 1 else 0
      simp [unsignedVal]
    · simp only [unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    wram_step
    · have ht : mem (a + M) < mem (d + M) := by simpa [startState] using hcond
      have hout := unsignedVal_lt_of_top_lt hva hvd ht
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 1 = if unsignedVal mem a h (M + 1) < unsignedVal mem d h (M + 1) then 1 else 0
        simp only [ite_eq_left hout, and_self]
      · simp only [unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
        omega
    · have ht : ¬ mem (a + M) < mem (d + M) := by simpa [startState] using hcond
      wram_step
      · have ht' : mem (d + M) < mem (a + M) := by simpa [startState] using hcond
        have hout := unsignedVal_lt_of_top_lt hvd hva ht'
        have hnot : ¬ unsignedVal mem a h (M + 1) < unsignedVal mem d h (M + 1) := by omega
        refine runs_ret_le (by eval_expr) ?_ ?_
        · change mem = mem ∧ 0 = if unsignedVal mem a h (M + 1) < unsignedVal mem d h (M + 1) then 1 else 0
          simp only [ite_eq_right hnot, and_self]
        · simp only [unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ,
            Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
          omega
      · have ht' : ¬ mem (d + M) < mem (a + M) := by simpa [startState] using hcond
        have heq : mem (a + M) = mem (d + M) := by omega
        refine runs_seq_call_le ih (vs := [a, d, M])
          (by eval_expr; simp [Expr.eval, BinOp.eval, startState, hw, show M < 2 ^ w by omega]) (by wram_words) ?_ ?_
        · change (∃ a' d' L', [a, d, M] = [a', d', L'] ∧
            a' + L' < 2 ^ w ∧ d' + L' < 2 ^ w ∧ Valid mem a' h L' ∧ Valid mem d' h L') ∧ M < M + 1
          exact ⟨⟨a, d, M, rfl, by omega, by omega,
            fun i hi => hva i (by omega), fun i hi => hvd i (by omega)⟩, by omega⟩
        · intro v mem' pos' hpost
          rcases hpost with ⟨hmem, hv⟩
          subst mem'
          change v = if unsignedVal mem a h M < unsignedVal mem d h M then 1 else 0 at hv
          have hvword : v < 2 ^ w := by split_ifs at hv <;> omega
          refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
          · change mem = mem ∧ v = if unsignedVal mem a h (M + 1) < unsignedVal mem d h (M + 1) then 1 else 0
            refine ⟨rfl, ?_⟩
            simpa only [unsignedVal_lt_iff_of_top_eq heq] using hv
          · simp only [unsignedLessContract, Contract.below, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
              Expr.size_load, argsSize_cons, argsSize_nil]
            omega

end MinCostFlow.Num
