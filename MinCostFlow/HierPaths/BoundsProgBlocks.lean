module

public import MinCostFlow.HierPaths.Params
public import MinCostFlow.HierPaths.BoundsProgLoops

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two blocks of the evaluator of `Γ`: `⌈log₂ n⌉` and `⌈n^{1/3}⌉`

The evaluator of `Γ` (`BoundsProg.lean`) needs `X = ⌈log₂(8M + 8)⌉`, `⌈log₂(X + 2)⌉`,
`j = ⌈X^{1/3}⌉` and `⌈X^{2/3}⌉ = ⌈(X^2)^{1/3}⌉`. Both blocks below read register `20` and write
register `21`, and change only their scratch registers besides.

* `clogBlock` uses `⌈log₂ n⌉ = ⌊log₂(n - 1)⌋ + 1` for `n ≥ 2` (`clog_eq_log_pred`), and counts
  halvings of `n - 1`.
* `cbrtBlock` uses `⌈n^{1/3}⌉ = ⌊(n - 1)^{1/3}⌋ + 1` for `n ≥ 1`, and finds the floor root by
  counting up from zero and comparing cubes, in `⌈n^{1/3}⌉` rounds.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Expander

/-- `⌈log₂ n⌉ = ⌊log₂(n - 1)⌋ + 1` for `n ≥ 2`. -/
lemma clog_eq_log_pred {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (n - 1)
    omega
  · have h1 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
    have h2 : Nat.log 2 (n - 1) < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
    omega

/-- The floor of the cube root of `n - 1` is `⌈n^{1/3}⌉ - 1`, for `n ≥ 1`. -/
lemma ceilRoot_pred_spec {n : ℕ} (hn : 1 ≤ n) :
    (ceilRoot 2 n - 1) ^ 3 ≤ n - 1 ∧ n - 1 < (ceilRoot 2 n - 1 + 1) ^ 3 := by
  have hc : 1 ≤ ceilRoot 2 n := by
    by_contra h0
    have h00 : ceilRoot 2 n = 0 := by omega
    have := le_ceilRoot_pow 2 n
    rw [h00] at this
    simp at this
    omega
  have h1 : (ceilRoot 2 n - 1) ^ 3 < n := pow_lt_of_lt_ceilRoot (by omega)
  have h2 : n ≤ ceilRoot 2 n ^ 3 := le_ceilRoot_pow 2 n
  rw [Nat.sub_add_cancel hc]
  omega

/-- The cube expression `(reg r * reg r) * reg r`. -/
def pow3Expr (r : ℕ) : Expr := .bin .mul (.bin .mul (.reg r) (.reg r)) (.reg r)

@[simp] lemma pow3Expr_size (r : ℕ) : (pow3Expr r).size = 5 := by simp [pow3Expr, Expr.size]

lemma pow3Expr_eval {w r x : ℕ} {st : State} (hr : st.regs r = x) (hx3 : x ^ 3 < 2 ^ w) :
    (pow3Expr r).eval w st = some (x ^ 3) := by
  have hx2 : x * x < 2 ^ w := by
    have : x * x ≤ x ^ 3 := by
      rcases x with _ | x'
      · simp
      · nlinarith [show (x' + 1) ^ 3 = ((x' + 1) * (x' + 1)) * (x' + 1) by ring]
    omega
  have hx3' : x * x * x = x ^ 3 := by ring
  simpa only [pow3Expr, hx3'] using
    Expr.eval_mul (Expr.eval_mul (Expr.eval_reg_of_eq hr) (Expr.eval_reg_of_eq hr) hx2)
      (Expr.eval_reg_of_eq hr) (by rw [hx3']; exact hx3)

/-- `reg 21 := ⌈log₂(reg 20)⌉`, with scratch registers `3` and `4`. -/
def clogBlock : Stmt :=
  .assign 3 (.bin .sub (.reg 20) (.const 1)) ;;
  .assign 4 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 3))
    (.assign 3 (.bin .div (.reg 3) (.const 2)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .assign 21 (.bin .add (.reg 4) (.const 1))

lemma clogBlock_noRand : clogBlock.NoRand := by simp [clogBlock, Stmt.NoRand]

theorem clogBlock_triple {w n : ℕ} {p : Program} (hn : 2 ≤ n) (hnw : n < 2 ^ w)
    (h4 : 4 ≤ 2 ^ w) (st₀ : State) (hr20 : st₀.regs 20 = n) :
    Triple w p (fun st => st = st₀) clogBlock
      (normalPost fun st' => st'.regs 21 = Nat.clog 2 n ∧ st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧ ∀ r, r ≠ 3 → r ≠ 4 → r ≠ 21 → st'.regs r = st₀.regs r)
      (fun _ => 13 * (Nat.log 2 (n - 1) + 1) + 20) := by
  have h1w : 1 < 2 ^ w := by omega
  have hlog_le : Nat.log 2 (n - 1) ≤ n - 1 := Nat.log_le_self 2 _
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := n - 1)
    (Expr.eval_sub (Expr.eval_reg_of_eq hr20) (Expr.eval_const h1w) hnw) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le (log2Loop_triple' (w := w) (p := p) 3 4 (n - 1) (by decide)
    (by omega) h4 (by omega) _ ?h3 ?h4) rfl ?_
  case h3 => simp
  case h4 => simp
  intro st3 ⟨h34, hm3, hp3, hreg3⟩
  have hv : Nat.log 2 (n - 1) + 1 < 2 ^ w := by omega
  refine runs_assign_le (v := Nat.log 2 (n - 1) + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq h34) (Expr.eval_const h1w) hv) ?_ ?_
  · refine ⟨by simp [clog_eq_log_pred hn], hm3, hp3, fun r h3 h4' h21 => ?_⟩
    simp only [Function.update_of_ne h21]
    rw [hreg3 r h3 h4']
    simp [Function.update_of_ne h3, Function.update_of_ne h4']
  · simp only [Expr.size]
    omega

/-- `reg 21 := ⌈(reg 20)^{1/3}⌉`, with scratch registers `3`, `6` and `8`. -/
def cbrtBlock : Stmt :=
  .assign 6 (.bin .sub (.reg 20) (.const 1)) ;;
  .assign 8 (.const 0) ;;
  .assign 3 (.const 1) ;;
  rootLoop 8 3 6 (pow3Expr 3) ;;
  .assign 21 (.bin .add (.reg 8) (.const 1))

lemma cbrtBlock_noRand : cbrtBlock.NoRand := by
  simp [cbrtBlock, rootLoop_noRand, Stmt.NoRand]

theorem cbrtBlock_triple {w n : ℕ} {p : Program} (hn : 1 ≤ n) (hnw : n < 2 ^ w)
    (hcw : ceilRoot 2 n ^ 3 < 2 ^ w) (h4 : 4 ≤ 2 ^ w) (st₀ : State) (hr20 : st₀.regs 20 = n) :
    Triple w p (fun st => st = st₀) cbrtBlock
      (normalPost fun st' => st'.regs 21 = ceilRoot 2 n ∧ st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧ ∀ r, r ≠ 3 → r ≠ 6 → r ≠ 8 → r ≠ 21 → st'.regs r = st₀.regs r)
      (fun _ => 19 * ceilRoot 2 n + 20) := by
  have h1w : 1 < 2 ^ w := by omega
  have hspec := ceilRoot_pred_spec hn
  have hc1 : 1 ≤ ceilRoot 2 n := by
    by_contra h0
    have h00 : ceilRoot 2 n = 0 := by omega
    have := le_ceilRoot_pow 2 n
    rw [h00] at this; simp at this; omega
  have hcpred : ceilRoot 2 n - 1 + 1 = ceilRoot 2 n := Nat.sub_add_cancel hc1
  have hclt : ceilRoot 2 n < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_self_pow (by decide) _) hcw
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := n - 1)
    (Expr.eval_sub (Expr.eval_reg_of_eq hr20) (Expr.eval_const h1w) hnw) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const h1w) ?_
  refine runs_seq_triple_le (rootLoop_triple (w := w) (p := p) 8 3 6 3 (n - 1)
    (ceilRoot 2 n - 1) (pow3Expr 3)
    (by decide) (by norm_num) hspec
    (fun st hst => pow3Expr_eval rfl (lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 3) hcw))
    (by omega) (by rw [hcpred]; exact hcw) _ ?h8 ?h3 ?h6) rfl ?_
  case h8 => simp
  case h3 => simp
  case h6 => simp
  intro st3 ⟨h38, hm3, hp3, hreg3⟩
  refine runs_assign_le (v := ceilRoot 2 n)
    (Expr.eval_eq_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h38) (Expr.eval_const h1w)
      (by omega)) hcpred) ?_ ?_
  · refine ⟨by simp, hm3, hp3, fun r h3 h6 h8 h21 => ?_⟩
    simp only [Function.update_of_ne h21]
    rw [hreg3 r h8 h3]
    simp [Function.update_of_ne h3, Function.update_of_ne h6, Function.update_of_ne h8]
  · simp only [Expr.size, pow3Expr_size]
    omega

end MinCostFlow.HierPaths
