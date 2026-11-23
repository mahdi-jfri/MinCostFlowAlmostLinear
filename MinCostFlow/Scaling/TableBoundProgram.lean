module

public import WordRAM.Layout
import WordRAM.Tactic

/-!
# A machine scan of an unsigned strided table

The demand rejection step of Appendix C reads demand magnitudes and compares
them with `m*U`. The table scanner below visits one unsigned word per row.
It stops at the first value exceeding the bound. Its function uses the same
finite recursion, and its procedure preserves all memory and uses no random
instructions. The explicit body cost is at most `24*length+8`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Check each of `length` words at spacing `stride`, starting at `a`. -/
def tableBoundCheck (mem : ℕ → ℕ) (a stride : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | length + 1, bound => decide (mem a ≤ bound) && tableBoundCheck mem (a + stride) stride length bound

/-- The scan tests exactly the pointwise bound on the strided table. -/
theorem tableBoundCheck_iff (mem : ℕ → ℕ) (a stride length bound : ℕ) :
    tableBoundCheck mem a stride length bound = true ↔
      ∀ i < length, mem (a + stride * i) ≤ bound := by
  induction length generalizing a with
  | zero => simp [tableBoundCheck]
  | succ length ih =>
    rw [tableBoundCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro h i hi
      cases i with
      | zero => simpa only [Nat.mul_zero, Nat.add_zero] using h.1
      | succ i =>
        have hh := h.2 i (by omega)
        simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · intro h
      refine ⟨by simpa only [Nat.mul_zero, Nat.add_zero] using h 0 (Nat.zero_lt_succ _), ?_⟩
      intro i hi
      have hh := h (i + 1) (by omega)
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- Arguments `[a, length, stride, bound]`; recurse on the remaining rows. -/
def tableBoundBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 1))
    (.cond (.bin .lt (.reg 3) (.load (.reg 0))) (.ret (.const 0))
      (.call 4 b [.bin .add (.reg 0) (.reg 2),
        .bin .sub (.reg 1) (.const 1), .reg 2, .reg 3] ;; .ret (.reg 4)))

/-- The table scan occupies one procedure slot. -/
def tableBoundModule (b : ℕ) : List Stmt := [tableBoundBody b]

/-- Read-only contract for a table whose addresses and stored values fit. -/
def tableBoundContract (w : ℕ) : Contract where
  pre args mem := ∃ a length stride bound,
    args = [a, length, stride, bound] ∧ a + stride * length < 2 ^ w ∧
      ∀ i < length, mem (a + stride * i) < 2 ^ w
  post args mem v mem' := mem' = mem ∧
    v = if tableBoundCheck mem (args.getD 0 0) (args.getD 2 0) (args.getD 1 0) (args.getD 3 0)
      then 1 else 0
  cost args _ := 24 * args.getD 1 0 + 8

/-- The scan never reads random bits. -/
theorem tableBoundBody_noRand (b : ℕ) : (tableBoundBody b).NoRand := by
  simp only [tableBoundBody, Stmt.NoRand, and_self]

/-- The recursive table scanner computes its Boolean model, preserves memory,
and costs at most `24*length+8` on every random tape. -/
theorem tableBound_meetsContract {w b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (tableBoundModule b)) : MeetsContract w p b (tableBoundContract w) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  obtain ⟨a, length, stride, bound, rfl, hend, hvals⟩ := hpre
  change length = k at hk
  subst k
  have ha : a < 2 ^ w := hwords a (by simp)
  have hl : length < 2 ^ w := hwords length (by simp)
  have hs : stride < 2 ^ w := hwords stride (by simp)
  have hb : bound < 2 ^ w := hwords bound (by simp)
  apply runs_start_le
  unfold tableBoundBody
  wram_step
  · have hz : length = 0 := by simpa [startState] using hcond
    subst length
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 1 = if tableBoundCheck mem a stride 0 bound then 1 else 0
      exact ⟨rfl, rfl⟩
    · simp only [tableBoundContract, List.getD_cons_succ, List.getD_cons_zero,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : length ≠ 0 := by simpa [startState] using hcond
    obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hhead : mem a < 2 ^ w := by simpa only [Nat.mul_zero, Nat.add_zero] using hvals 0 (Nat.zero_lt_succ L)
    change a + stride * (L + 1) < 2 ^ w at hend
    have hadd : a + stride < 2 ^ w := by
      have hle : stride ≤ stride * (L + 1) := by rw [Nat.mul_succ]; omega
      omega
    have htailend : a + stride + stride * L < 2 ^ w := by
      rw [Nat.mul_succ] at hend
      omega
    have htail : ∀ i < L, mem (a + stride + stride * i) < 2 ^ w := by
      intro i hi
      have hh := hvals (i + 1) (by omega)
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    wram_step
    · have hfail : bound < mem a := by simpa [startState] using hcond
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 0 = if tableBoundCheck mem a stride (L + 1) bound then 1 else 0
        simp only [tableBoundCheck, decide_eq_false (Nat.not_le.mpr hfail), Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, and_self]
      · simp only [tableBoundContract, List.getD_cons_succ, List.getD_cons_zero,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
        omega
    · have hpass : mem a ≤ bound := by
        have hh : ¬bound < mem a := by simpa [startState] using hcond
        exact Nat.le_of_not_gt hh
      refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
      · wram_words
      · change (∃ a' length' stride' bound',
          [a + stride, L + 1 - 1, stride, bound] = [a', length', stride', bound'] ∧
          a' + stride' * length' < 2 ^ w ∧
          ∀ i < length', mem (a' + stride' * i) < 2 ^ w) ∧ L + 1 - 1 < L + 1
        exact ⟨⟨a + stride, L, stride, bound, by simp, htailend, htail⟩, by omega⟩
      · intro v mem' pos' hpost
        obtain ⟨hm, hv⟩ := hpost
        subst mem'
        change v = if tableBoundCheck mem (a + stride) stride L bound then 1 else 0 at hv
        have hvword : v < 2 ^ w := by split at hv <;> omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change mem = mem ∧ v = if tableBoundCheck mem a stride (L + 1) bound then 1 else 0
          refine ⟨rfl, ?_⟩
          simpa only [tableBoundCheck, hpass, decide_true, Bool.true_and] using hv
        · simp only [tableBoundContract, Contract.below, List.getD_cons_succ, List.getD_cons_zero,
            Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.Scaling.Machine
