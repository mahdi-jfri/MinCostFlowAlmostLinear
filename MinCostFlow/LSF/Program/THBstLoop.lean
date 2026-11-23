module

public import MinCostFlow.LSF.Program.THDepthMath
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The search loop

`thBstBody` is one step of the balanced search `bstIdx` over a segment `[lo, lo + len)` of the
chain array at `arrPtr`, looking for position `lo + j`. Registers: `14 = above`, `15 = lo`,
`16 = len`, `17 = j`, `18 = d` (the depth so far), `19 = [j ≠ len / 2]` (the loop flag),
`22 = len / 2`, `23 = [j < len / 2]`. A step moves to the left or the right half with no branch
and adds one to `d` (`bstIdx_step`). The loop stops when `j = len / 2` (`bstIdx_stop`), and then
`above` and `d` are the result of the search. The segment halves at each step, so the loop runs
`O(log len)` steps (`thBst_loop`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step of the search. -/
def thBstBody : Stmt :=
  .assign 22 (.bin .div (.reg 16) (.const 2)) ;;
  .assign 23 (.bin .lt (.reg 17) (.reg 22)) ;;
  .assign 14 (.load (.bin .add (.reg 7) (.bin .add (.reg 15) (.reg 22)))) ;;
  .assign 17 (.bin .add (.bin .mul (.reg 23) (.reg 17))
    (.bin .mul (.bin .sub (.const 1) (.reg 23)) (.bin .sub (.bin .sub (.reg 17) (.reg 22)) (.const 1)))) ;;
  .assign 15 (.bin .add (.reg 15) (.bin .mul (.bin .sub (.const 1) (.reg 23))
    (.bin .add (.reg 22) (.const 1)))) ;;
  .assign 16 (.bin .add (.bin .mul (.reg 23) (.reg 22))
    (.bin .mul (.bin .sub (.const 1) (.reg 23)) (.bin .sub (.bin .sub (.reg 16) (.reg 22)) (.const 1)))) ;;
  .assign 18 (.bin .add (.reg 18) (.const 1)) ;;
  .assign 19 (.bin .sub (.const 1) (.bin .eq (.reg 17) (.bin .div (.reg 16) (.const 2))))

/-- The registers the search loop changes. -/
def BstReg (i : ℕ) : Prop := (14 ≤ i ∧ i ≤ 19) ∨ i = 22 ∨ i = 23

/-- The state of the search loop. `a = (above, lo, len, j, d)`. -/
def BstInv (n arrPtr : ℕ) (M R0 : ℕ → ℕ) (R : ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ × ℕ) (st : State) :
    Prop :=
  st.mem = M ∧ (∀ i, ¬ BstReg i → st.regs i = R0 i) ∧
  st.regs 14 = a.1 ∧ st.regs 15 = a.2.1 ∧ st.regs 16 = a.2.2.1 ∧ st.regs 17 = a.2.2.2.1 ∧
  st.regs 18 = a.2.2.2.2 ∧ st.regs 19 = (if a.2.2.2.1 = a.2.2.1 / 2 then 0 else 1) ∧
  (bstIdx a.1 (fun s => M (arrPtr + s)) a.2.1 a.2.2.1 a.2.2.2.1).1 = R.1 ∧
  a.2.2.2.2 + (bstIdx a.1 (fun s => M (arrPtr + s)) a.2.1 a.2.2.1 a.2.2.2.1).2 = R.2 ∧
  (a.2.2.2.1 < a.2.2.1 ∨ (a.2.2.1 = 0 ∧ a.2.2.2.1 = 0)) ∧
  a.2.1 + a.2.2.1 ≤ n ∧ a.1 < n ∧ a.2.2.2.2 + a.2.2.1 ≤ n

/-- The state after the search loop. -/
def BstDone (n : ℕ) (M R0 : ℕ → ℕ) (R : ℕ × ℕ) (st : State) : Prop :=
  st.mem = M ∧ (∀ i, ¬ BstReg i → st.regs i = R0 i) ∧ st.regs 14 = R.1 ∧ st.regs 18 = R.2 ∧
  R.1 < n ∧ R.2 ≤ n

/-- The cost of the search loop on a segment of length `len`. -/
def bstLoopCost (len : ℕ) : ℕ := 120 * Nat.log 2 (2 * len) + 4

private lemma sel_eq'' {c a a' : ℕ} (P : Prop) [Decidable P] (hc : c = if P then 1 else 0) :
    c * a + (1 - c) * a' = if P then a else a' := by
  subst hc; split_ifs <;> simp

private lemma log_two_mul_lt {len len' : ℕ} (h0 : len ≠ 0) (h : 2 * len' ≤ len) :
    Nat.log 2 (2 * len') + 1 ≤ Nat.log 2 (2 * len) := by
  have h1 : Nat.log 2 (2 * len) = Nat.log 2 len + 1 := by
    rw [Nat.mul_comm]; exact Nat.log_mul_base (by decide) h0
  have h2 : Nat.log 2 (2 * len') ≤ Nat.log 2 len := Nat.log_mono_right h
  omega

theorem thBst_loop {w : ℕ} {p : Program} {n arrPtr : ℕ} {M R0 : ℕ → ℕ} {R : ℕ × ℕ}
    (hR7 : R0 7 = arrPtr) (hM : ∀ s < n, M (arrPtr + s) < n) (hw : arrPtr + n + 4 < 2 ^ w)
    (a : ℕ × ℕ × ℕ × ℕ × ℕ) :
    Triple w p (BstInv n arrPtr M R0 R a) (.loop (.reg 19) thBstBody)
      (normalPost (BstDone n M R0 R)) (fun _ => bstLoopCost a.2.2.1) := by
  classical
  refine Triple.loop_inv (Inv := BstInv n arrPtr M R0 R) (condVal := fun st => st.regs 19)
    (fun a => a.2.2.1) (fun a => bstLoopCost a.2.2.1) ?_ ?_ ?_ a
  · intro a st _; eval_expr
  · rintro ⟨ab, lo, len, j, d⟩ st ⟨hmem, hfr, h14, h15, h16, h17, h18, h19, hR1, hR2, hjl, hll, hab,
      hdl⟩ h0
    dsimp only at *
    rw [h19] at h0
    have hj : j = len / 2 := by by_contra h; rw [if_neg h] at h0; omega
    rw [bstIdx_stop ab _ lo len j hj] at hR1 hR2
    dsimp only at hR1 hR2
    refine ⟨⟨hmem, hfr, by rw [h14, hR1], by rw [h18]; omega, by rw [← hR1]; exact hab,
      by omega⟩, ?_⟩
    simp only [bstLoopCost, Expr.size_reg]; omega
  · rintro ⟨ab, lo, len, j, d⟩ st ⟨hmem, hfr, h14, h15, h16, h17, h18, h19, hR1, hR2, hjl, hll, hab,
      hdl⟩ h0
    dsimp only at *
    rw [h19] at h0
    have hj : j ≠ len / 2 := by intro h; rw [if_pos h] at h0; omega
    have hlen0 : len ≠ 0 := by intro h; rcases hjl with h' | ⟨_, h'⟩ <;> omega
    have hjlt : j < len := by rcases hjl with h' | ⟨h', _⟩ <;> omega
    have r7 : st.regs 7 = arrPtr := by
      rw [hfr 7 (by simp [BstReg])]; exact hR7
    set m := len / 2 with hm
    have hmlt : m < len := Nat.div_lt_self (by omega) (by decide)
    set cc := (if j < m then 1 else 0) with hcc
    have hcc1 : cc ≤ 1 := by rw [hcc]; split_ifs <;> omega
    set ab' := M (arrPtr + (lo + m)) with hab'
    have hab'n : ab' < n := hM _ (by omega)
    set j' := (if j < m then j else j - m - 1) with hj'
    set lo' := (if j < m then lo else lo + m + 1) with hlo'
    set len' := (if j < m then m else len - m - 1) with hlen'
    have hj'v : cc * j + (1 - cc) * (j - m - 1) = j' := sel_eq'' _ hcc
    have hlo'v : lo + (1 - cc) * (m + 1) = lo' := by
      rw [hlo', hcc]; split_ifs <;> simp; omega
    have hlen'v : cc * m + (1 - cc) * (len - m - 1) = len' := sel_eq'' _ hcc
    have hstep := bstIdx_step ab (fun s => M (arrPtr + s)) lo len j hlen0 hj
    refine ⟨100, ?_⟩
    intro s ω' hs; subst s
    refine runs_start_le ?_
    unfold thBstBody
    have hbnd : cc * j ≤ n ∧ (1 - cc) * (j - m - 1) ≤ n ∧ cc * m ≤ n ∧
        (1 - cc) * (len - m - 1) ≤ n ∧ (1 - cc) * (m + 1) ≤ n := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc1 with h | h <;> simp [h] <;> omega
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbnd
    refine runs_seq_assign_le (v := m) (by eval_expr) ?_
    refine runs_seq_assign_le (v := cc) (by eval_expr) ?_
    refine runs_seq_assign_le (v := ab') (by
      have : st.mem (arrPtr + (lo + m)) < n := by rw [hmem]; exact hab'n
      rw [hab', ← hmem]
      eval_expr) ?_
    refine runs_seq_assign_le (v := j') (by
      rw [← hj'v]
      have : cc * j + (1 - cc) * (j - m - 1) < 2 ^ w := by rw [hj'v, hj']; split_ifs <;> omega
      eval_expr) ?_
    refine runs_seq_assign_le (v := lo') (by
      rw [← hlo'v]
      have : lo + (1 - cc) * (m + 1) < 2 ^ w := by rw [hlo'v, hlo']; split_ifs <;> omega
      eval_expr) ?_
    refine runs_seq_assign_le (v := len') (by
      rw [← hlen'v]
      have : cc * m + (1 - cc) * (len - m - 1) < 2 ^ w := by rw [hlen'v, hlen']; split_ifs <;> omega
      eval_expr) ?_
    refine runs_seq_assign_le (v := d + 1) (by eval_expr) ?_
    have hnew : bstIdx ab (fun s => M (arrPtr + s)) lo len j =
        ((bstIdx ab' (fun s => M (arrPtr + s)) lo' len' j').1,
          (bstIdx ab' (fun s => M (arrPtr + s)) lo' len' j').2 + 1) := by
      rw [hstep, hj', hlo', hlen']; split_ifs <;> rfl
    rw [hnew] at hR1 hR2
    dsimp only at hR1 hR2
    have hj'l : j' < len' ∨ (len' = 0 ∧ j' = 0) := by
      rw [hj', hlen']; split_ifs <;> omega
    have hlenlt : len' < len := by rw [hlen']; split_ifs <;> omega
    have hll' : lo' + len' ≤ n := by rw [hlo', hlen']; split_ifs <;> omega
    have h2len : 2 * len' ≤ len := by rw [hlen']; split_ifs <;> omega
    have hfv : 1 - (if j' = len' / 2 then 1 else 0) = if j' = len' / 2 then 0 else 1 := by
      split_ifs <;> rfl
    refine runs_assign_le (v := 1 - (if j' = len' / 2 then 1 else 0)) (by eval_expr)
      ⟨(ab', lo', len', j', d + 1), ⟨?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, hR1, by dsimp only; omega, hj'l, hll', hab'n, by dsimp only; omega⟩,
        by dsimp only; exact hlenlt, ?_⟩ ?_
    · exact hmem
    · intro i hi
      simp only [BstReg] at hi
      simp only [Function.update_of_ne (show i ≠ 19 by omega), Function.update_of_ne (show i ≠ 18 by omega),
        Function.update_of_ne (show i ≠ 16 by omega), Function.update_of_ne (show i ≠ 15 by omega),
        Function.update_of_ne (show i ≠ 17 by omega), Function.update_of_ne (show i ≠ 14 by omega),
        Function.update_of_ne (show i ≠ 23 by omega), Function.update_of_ne (show i ≠ 22 by omega)]
      exact hfr i (by simp only [BstReg]; omega)
    all_goals try (simp; done)
    all_goals first
      | (simp only [Function.update_self]; exact hfv)
      | (dsimp only
         have := log_two_mul_lt hlen0 h2len
         simp only [bstLoopCost, Expr.size_reg]; omega)
      | (simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega)

end

end MinCostFlow.LSF.Program
