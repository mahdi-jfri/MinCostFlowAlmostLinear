module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.IsZero
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Three-way sign of a fixed-point number

First read the sign bit. A negative block returns code two immediately. Otherwise a
zero scan distinguishes zero (code zero) from positive (code one). The procedure
preserves all memory and has a linear worst-case cost.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L]`. Codes are zero = 0, positive = 1, negative = 2. -/
def signBody (neg zeroEntry : ℕ) : Stmt :=
  .call 2 neg [.reg 0, .reg 1] ;;
  .cond (.reg 2) (.ret (.const 2))
    (.call 3 zeroEntry [.reg 0, .reg 1] ;;
     .cond (.reg 3) (.ret (.const 0)) (.ret (.const 1)))

/-- The public sign entry, the sign-bit test, and the recursive zero scan. -/
def signModule (b h : ℕ) : List Stmt :=
  [signBody (b + 1) (b + 2), isNegativeBody h, isZeroBody (b + 2)]

/-- The sign code of the stored signed integer. -/
def signContract (w h : ℕ) : Contract where
  pre := (isZeroContract w h).pre
  post args mem v mem' := mem' = mem ∧ v =
    if intVal mem (args.getD 0 0) h (args.getD 1 0) < 0 then 2 else
      if intVal mem (args.getD 0 0) h (args.getD 1 0) = 0 then 0 else 1
  cost args _ := 19 * args.getD 1 0 + 33

/-- Every body of the sign module is deterministic. -/
theorem signModule_noRand (b h : ℕ) : ∀ s ∈ signModule b h, s.NoRand := by
  simp only [signModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨by simp [signBody, Stmt.NoRand], isNegativeBody_noRand _, isZeroBody_noRand _⟩

/-- The sign module meets its read-only contract at cost at most `19 * L + 33`. -/
theorem sign_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (signModule b h)) : MeetsContract w p b (signContract w h) := by
  have hneg : p.HasAt (b + 1) (isNegativeModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [signModule, isNegativeModule] using hp 1 (by simp [signModule])
  have hzero : p.HasAt (b + 2) (isZeroModule (b + 2)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [signModule, isZeroModule] using hp 2 (by simp [signModule])
  have hb2 : 1 < base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide : 1 < (2 : ℕ))
  have hw2 : 2 < 2 ^ w := by omega
  have hn := isNegative_meetsContract hh hw hb hneg
  have hz := isZero_meetsContract (h := h) hw hzero
  have hentry : p.procs[b]? = some (signBody (b + 1) (b + 2)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, rfl, hbound, hv⟩ := hpre
  apply runs_start_le
  unfold signBody
  refine runs_seq_call_le hn (by eval_expr) hwords ?_ ?_
  · exact ⟨a, L, rfl, hbound, hv⟩
  · intro v mem' pos' hpst
    rcases hpst with ⟨he, hvout⟩
    subst mem'
    change v = if intVal mem a h L < 0 then 1 else 0 at hvout
    refine runs_cond_le (by eval_expr) ?_ ?_
    · intro hvn
      have hneg : intVal mem a h L < 0 := by
        by_contra he
        simp [he] at hvn
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 2 = if intVal mem a h L < 0 then 2 else _
        simp only [ite_eq_left hneg, and_self]
      · simp only [signContract, isNegativeContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega
    · intro hvz
      have hnonneg : ¬ intVal mem a h L < 0 := by
        intro he
        simp [he] at hvz
      refine runs_seq_call_le hz (by eval_expr) hwords ?_ ?_
      · exact ⟨a, L, rfl, hbound, hv⟩
      · intro u mem' pos'' hpzero
        rcases hpzero with ⟨he, huout⟩
        subst mem'
        change u = if intVal mem a h L = 0 then 1 else 0 at huout
        refine runs_cond_le (by eval_expr) ?_ ?_
        · intro hun
          have heq : intVal mem a h L = 0 := by
            by_contra he
            simp [he] at hun
          refine runs_ret_le (by eval_expr) ?_ ?_
          · change mem = mem ∧ 0 = if intVal mem a h L < 0 then 2 else
              if intVal mem a h L = 0 then 0 else 1
            simp only [ite_eq_right hnonneg, ite_eq_left heq, and_self]
          · simp only [signContract, isNegativeContract, isZeroContract,
              List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_const,
              argsSize_cons, argsSize_nil]
            omega
        · intro huz
          have hne : intVal mem a h L ≠ 0 := by
            intro he
            simp [he] at huz
          refine runs_ret_le (by eval_expr) ?_ ?_
          · change mem = mem ∧ 1 = if intVal mem a h L < 0 then 2 else
              if intVal mem a h L = 0 then 0 else 1
            simp only [ite_eq_right hnonneg, ite_eq_right hne, and_self]
          · simp only [signContract, isNegativeContract, isZeroContract,
              List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_const,
              argsSize_cons, argsSize_nil]
            omega

end MinCostFlow.Num
