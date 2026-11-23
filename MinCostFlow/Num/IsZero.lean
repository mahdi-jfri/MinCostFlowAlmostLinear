module

public import MinCostFlow.Num.Representation
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Testing a stored integer for zero

Two's complement has just one zero encoding. A scan can therefore stop at the first
nonzero limb. The procedure returns one for zero and zero otherwise, leaves all memory
unchanged, and costs at most `19 * L + 6`. It allocates no memory.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L]`. Entry `b` is used to scan the remaining limbs. -/
def isZeroBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 1))
    (.cond (.bin .eq (.load (.reg 0)) (.const 0))
      (.call 2 b [.bin .add (.reg 0) (.const 1), .bin .sub (.reg 1) (.const 1)] ;;
        .ret (.reg 2))
      (.ret (.const 0)))

/-- The zero-test procedure at index `b`. -/
def isZeroModule (b : ℕ) : List Stmt := [isZeroBody b]

/-- A read-only zero test on a valid limb block. -/
def isZeroContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L, args = [a, L] ∧ a + L < 2 ^ w ∧ Valid mem a h L
  post args mem v mem' := mem' = mem ∧
    v = if intVal mem (args.getD 0 0) h (args.getD 1 0) = 0 then 1 else 0
  cost args _ := 19 * args.getD 1 0 + 6

/-- The zero test uses no random bits. -/
theorem isZeroBody_noRand (b : ℕ) : (isZeroBody b).NoRand := by
  simp [isZeroBody, Stmt.NoRand]

/-- A zero test has a linear worst-case cost, independent of its random tape. -/
theorem isZero_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (isZeroModule b)) : MeetsContract w p b (isZeroContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a, L, rfl, hb, hv⟩
  change L = k at hk
  subst k
  have ha : a < 2 ^ w := hwords a (by simp)
  have hL : L < 2 ^ w := hwords L (by simp)
  apply runs_start_le
  unfold isZeroBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 1 = if intVal mem a h 0 = 0 then 1 else 0
      simp [intVal, unsignedVal]
    · simp only [isZeroContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hnonzero : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
    obtain ⟨hhead, htail⟩ := valid_succ.mp hv
    wram_step
    · have hz : mem a = 0 := by simpa [startState] using hcond
      refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
      · wram_words
      · change (∃ a' L', [a + 1, M + 1 - 1] = [a', L'] ∧
          a' + L' < 2 ^ w ∧ Valid mem a' h L') ∧ M + 1 - 1 < M + 1
        exact ⟨⟨a + 1, M, by simp, by omega, htail⟩, by omega⟩
      · intro v mem' pos' hpst
        rcases hpst with ⟨hmem, hvout⟩
        subst mem'
        change v = if intVal mem (a + 1) h M = 0 then 1 else 0 at hvout
        have hvword : v < 2 ^ w := by split_ifs at hvout <;> omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change mem = mem ∧ v = if intVal mem a h (M + 1) = 0 then 1 else 0
          refine ⟨rfl, ?_⟩
          simp only [intVal_eq_zero_iff hv, unsignedVal, hz, zero_add,
            mul_eq_zero, or_iff_right (ne_of_gt (base_pos h)),
            ← intVal_eq_zero_iff htail]
          exact hvout
        · simp only [isZeroContract, Contract.below, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
            Expr.size_load, argsSize_cons, argsSize_nil]
          omega
    · have hn : mem a ≠ 0 := by simpa [startState] using hcond
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 0 = if intVal mem a h (M + 1) = 0 then 1 else 0
        have hvn : intVal mem a h (M + 1) ≠ 0 := by
          intro hz
          have hu := (intVal_eq_zero_iff hv).mp hz
          exact hn (by unfold unsignedVal at hu; omega)
        simp only [ite_eq_right hvn, and_self]
      · simp only [isZeroContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
        omega

end MinCostFlow.Num
