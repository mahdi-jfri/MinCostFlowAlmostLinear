module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.SignFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Constant-time sign-bit test

The empty block is zero. For a nonempty block the procedure compares its highest limb
with half the base. This reads only one cell and costs at most thirteen machine steps.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L]`; return one for negative and zero for nonnegative. -/
def isNegativeBody (h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.ret (.bin .lt (.const (base h / 2 - 1))
      (.load (.bin .add (.reg 0) (.bin .sub (.reg 1) (.const 1))))))

/-- The sign-bit module at entry `b`. -/
def isNegativeModule (_b h : ℕ) : List Stmt := [isNegativeBody h]

/-- Test negativity without changing memory or allocating. -/
def isNegativeContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L, args = [a, L] ∧ a + L < 2 ^ w ∧ Valid mem a h L
  post args mem v mem' := mem' = mem ∧
    v = if intVal mem (args.getD 0 0) h (args.getD 1 0) < 0 then 1 else 0
  cost _ _ := 13

/-- Reading the sign bit uses no randomness. -/
theorem isNegativeBody_noRand (h : ℕ) : (isNegativeBody h).NoRand := by
  simp [isNegativeBody, Stmt.NoRand]

/-- The sign-bit test meets its read-only contract in constant time. -/
theorem isNegative_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (isNegativeModule b h)) :
    MeetsContract w p b (isNegativeContract w h) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, L, rfl, hbound, hv⟩
  have hhalf : 0 < base h / 2 := by
    have hp := base_pos h
    have he := base_eq_two_mul_half hh
    omega
  have hthreshold : base h / 2 - 1 < 2 ^ w :=
    lt_of_le_of_lt (le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _)) hb
  apply runs_start_le
  unfold isNegativeBody
  wram_step
  · have hz : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 0 = if intVal mem a h 0 < 0 then 1 else 0
      simp [intVal, unsignedVal]
    · simp only [isNegativeContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ (if base h / 2 - 1 < mem (a + (M + 1 - 1)) then 1 else 0) =
        if intVal mem a h (M + 1) < 0 then 1 else 0
      have he : (base h / 2 - 1 < mem (a + M)) ↔ intVal mem a h (M + 1) < 0 := by
        rw [intVal_neg_iff_top hh hv]
        omega
      simp only [Nat.add_sub_cancel, he, and_self]
    · simp only [isNegativeContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
      omega

end MinCostFlow.Num
