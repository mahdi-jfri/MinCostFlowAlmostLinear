module

public import MinCostFlow.HierPaths.BoundsProgBlocks

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The first part of the evaluator of `Γ`: the four integers

`gammaFront` reads `M` in register `1` and computes `X = ⌈log₂(8M + 8)⌉` (register `5`),
`j = ⌈X^{1/3}⌉` (register `9`), `R = ⌈(X^2)^{1/3}⌉` (register `10`) and `⌈log₂(X + 2)⌉`
(register `11`), with the blocks of `BoundsProgBlocks.lean`. It keeps registers `0` and `2`
and the memory. Its cost is linear in `log₂(8M + 7)`, `j` and `R`, all of which are `O(X)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Expander

/-- The four integers `X, j, R, ⌈log₂(X + 2)⌉` in registers `5, 9, 10, 11`. -/
def gammaFront : Stmt :=
  .assign 20 (.bin .add (.bin .mul (.const 8) (.reg 1)) (.const 8)) ;;
  clogBlock ;;
  .assign 5 (.reg 21) ;;
  .assign 20 (.reg 5) ;;
  cbrtBlock ;;
  .assign 9 (.reg 21) ;;
  .assign 20 (.bin .mul (.reg 5) (.reg 5)) ;;
  cbrtBlock ;;
  .assign 10 (.reg 21) ;;
  .assign 20 (.bin .add (.reg 5) (.const 2)) ;;
  clogBlock ;;
  .assign 11 (.reg 21)

lemma gammaFront_noRand : gammaFront.NoRand := by
  simp [gammaFront, clogBlock_noRand, cbrtBlock_noRand, Stmt.NoRand]

lemma ceilRoot_sq_le_self (X : ℕ) (hX : 1 ≤ X) : ceilRoot 2 (X ^ 2) ≤ X :=
  ceilRoot_le (Nat.pow_le_pow_right hX (by norm_num))

theorem gammaFront_triple {w d M h : ℕ} {p : Program} (h8M : 8 * M + 8 < 2 ^ w)
    (hX3 : bigX M ^ 3 < 2 ^ w) (h4 : 4 ≤ 2 ^ w) (st₀ : State)
    (hr0 : st₀.regs 0 = d) (hr1 : st₀.regs 1 = M) (hr2 : st₀.regs 2 = h) :
    Triple w p (fun st => st = st₀) gammaFront
      (normalPost fun st' => st'.regs 0 = d ∧ st'.regs 2 = h ∧ st'.regs 9 = bigJ M ∧
        st'.regs 10 = ceilRoot 2 (bigX M ^ 2) ∧ st'.regs 11 = Nat.clog 2 (bigX M + 2) ∧
        st'.mem = st₀.mem ∧ st'.pos = st₀.pos)
      (fun _ => 13 * (Nat.log 2 (8 * M + 7) + 1) + 13 * (Nat.log 2 (bigX M + 1) + 1) +
        19 * bigJ M + 19 * ceilRoot 2 (bigX M ^ 2) + 200) := by
  have h1w : 1 < 2 ^ w := by omega
  have hX1 : 3 ≤ bigX M := three_le_xOf M
  have hXX : bigX M * bigX M ≤ bigX M ^ 3 := by
    rw [show bigX M ^ 3 = bigX M * bigX M * bigX M by ring]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hXw : bigX M < 2 ^ w := lt_of_le_of_lt (by nlinarith) hX3
  have hjX : bigJ M ≤ bigX M := ceilRoot_le_self 2 (bigX M)
  have hX2 : bigX M + 2 ≤ bigX M * bigX M := by nlinarith
  have hX2w : bigX M + 2 < 2 ^ w := by omega
  have hRX : ceilRoot 2 (bigX M ^ 2) ≤ bigX M := ceilRoot_sq_le_self _ (by omega)
  have hj3 : bigJ M ^ 3 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_left hjX 3) hX3
  have hR3 : ceilRoot 2 (bigX M ^ 2) ^ 3 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_left hRX 3) hX3
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 8 * M + 8) (Expr.eval_add (Expr.eval_mul (Expr.eval_const
    (by omega)) (Expr.eval_reg_of_eq hr1) (by omega)) (Expr.eval_const (by omega)) h8M) ?_
  refine runs_seq_triple_le (clogBlock_triple (n := 8 * M + 8) (by omega) h8M h4 _ ?a1) rfl ?_
  case a1 => simp
  intro s1 ⟨h1_21, hm1, hp1, hreg1⟩
  refine runs_seq_assign_le (v := bigX M) (Expr.eval_reg_of_eq h1_21) ?_
  refine runs_seq_assign_le (v := bigX M) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_triple_le (cbrtBlock_triple (n := bigX M) (by omega) hXw hj3 h4 _ ?a2) rfl ?_
  case a2 => simp
  intro s2 ⟨h2_21, hm2, hp2, hreg2⟩
  have h2_5 : s2.regs 5 = bigX M := by rw [hreg2 5 (by decide) (by decide) (by decide) (by decide)]; simp
  refine runs_seq_assign_le (v := bigJ M) (Expr.eval_reg_of_eq h2_21) ?_
  refine runs_seq_assign_le (v := bigX M ^ 2) (Expr.eval_eq_of_eq (Expr.eval_mul
    (x := bigX M) (y := bigX M)
    (Expr.eval_reg_of_eq (by simp [h2_5])) (Expr.eval_reg_of_eq (by simp [h2_5]))
    (by nlinarith)) (by ring)) ?_
  refine runs_seq_triple_le (cbrtBlock_triple (n := bigX M ^ 2) (by nlinarith) (by nlinarith) hR3
    h4 _ ?a3) rfl ?_
  case a3 => simp
  intro s3 ⟨h3_21, hm3, hp3, hreg3⟩
  have h3_5 : s3.regs 5 = bigX M := by
    rw [hreg3 5 (by decide) (by decide) (by decide) (by decide)]; simp [h2_5]
  refine runs_seq_assign_le (v := ceilRoot 2 (bigX M ^ 2)) (Expr.eval_reg_of_eq h3_21) ?_
  refine runs_seq_assign_le (v := bigX M + 2) (Expr.eval_add (x := bigX M) (y := 2)
    (Expr.eval_reg_of_eq (by simp [h3_5]))
    (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_triple_le (clogBlock_triple (n := bigX M + 2) (by omega) (by omega) h4 _ ?a4)
    rfl ?_
  case a4 => simp
  intro s4 ⟨h4_21, hm4, hp4, hreg4⟩
  refine runs_assign_le (v := Nat.clog 2 (bigX M + 2)) (Expr.eval_reg_of_eq h4_21) ?_ ?_
  · have k0 : s4.regs 0 = d := by
      rw [hreg4 0 (by decide) (by decide) (by decide)]; simp only [Function.update_apply]; simp
      rw [hreg3 0 (by decide) (by decide) (by decide) (by decide)]; simp
      rw [hreg2 0 (by decide) (by decide) (by decide) (by decide)]; simp
      rw [hreg1 0 (by decide) (by decide) (by decide)]; simp [hr0]
    have k2 : s4.regs 2 = h := by
      rw [hreg4 2 (by decide) (by decide) (by decide)]; simp only [Function.update_apply]; simp
      rw [hreg3 2 (by decide) (by decide) (by decide) (by decide)]; simp
      rw [hreg2 2 (by decide) (by decide) (by decide) (by decide)]; simp
      rw [hreg1 2 (by decide) (by decide) (by decide)]; simp [hr2]
    have k9 : s4.regs 9 = bigJ M := by
      rw [hreg4 9 (by decide) (by decide) (by decide)]; simp only [Function.update_apply]; simp
      rw [hreg3 9 (by decide) (by decide) (by decide) (by decide)]; simp
    have k10 : s4.regs 10 = ceilRoot 2 (bigX M ^ 2) := by
      rw [hreg4 10 (by decide) (by decide) (by decide)]; simp
    refine ⟨by simp [k0], by simp [k2], by simp [k9], by simp [k10], by simp, ?_, ?_⟩
    · simp only; rw [hm4, hm3, hm2, hm1]
    · simp only; rw [hp4, hp3, hp2, hp1]
  · simp only [Expr.size]
    have : Nat.log 2 (8 * M + 8 - 1) = Nat.log 2 (8 * M + 7) := by congr 1
    have : Nat.log 2 (bigX M + 2 - 1) = Nat.log 2 (bigX M + 1) := by congr 1
    have : ceilRoot 2 (bigX M) = bigJ M := rfl
    omega

end MinCostFlow.HierPaths
