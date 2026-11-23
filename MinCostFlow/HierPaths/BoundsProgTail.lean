module

public import MinCostFlow.HierPaths.Params
public import WordRAM.Logic

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The last block of the evaluator of `Γ`: the product

Given `d`, `j = ⌈X^{1/3}⌉`, `R = ⌈X^{2/3}⌉` and `v = ⌈log₂(X + 2)⌉` in registers `0`, `9`, `10`
and `11`, `gammaTail a` computes in register `7`
`(j + 2)^4 · (2^{1+R} + 1)^4 · (1 + (2 + d)^4)^2 · 2^e` with `e = 12 + 2(j + 1) + a j v (2j + 2)`,
by squaring and multiplying, and one shift for each power of two. This number is `Γ` (`gammaHP`)
(`gammaHP_eq_tailVal`), since `4^{j+1} = 2^{2(j+1)}` and `U_X^{2j+2} = 2^{a j v (2j+2)}`. Every
intermediate value is at most the result, so the block runs when the result fits in a word.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The exponent `e = 12 + 2(j + 1) + a j v (2j + 2)` of the power of two in `Γ`. -/
def tailExp (a j v : ℕ) : ℕ := 12 + 2 * (j + 1) + a * j * v * (2 * j + 2)

/-- The value the tail computes, in its order of computation. -/
def tailVal (a d j R v : ℕ) : ℕ :=
  (j + 2) * (j + 2) * ((j + 2) * (j + 2)) *
    ((2 ^ (1 + R) + 1) * (2 ^ (1 + R) + 1) * ((2 ^ (1 + R) + 1) * (2 ^ (1 + R) + 1))) *
    ((1 + (2 + d) * (2 + d) * ((2 + d) * (2 + d))) * (1 + (2 + d) * (2 + d) * ((2 + d) * (2 + d)))) *
    2 ^ tailExp a j v

/-- `Γ` is the value of the tail at `j = bigJ M`, `R = ⌈X^{2/3}⌉` and `v = ⌈log₂(X + 2)⌉`. -/
lemma gammaHP_eq_tailVal (a d M : ℕ) :
    gammaHP a d M = tailVal a d (bigJ M) (ceilRoot 2 (bigX M ^ 2)) (Nat.clog 2 (bigX M + 2)) := by
  unfold gammaHP tailVal tailExp bigKB bigUX
  rw [← pow_mul, show 4 ^ (bigJ M + 1) = 2 ^ (2 * (bigJ M + 1)) by rw [pow_mul]; norm_num,
    pow_add, pow_add]
  ring

/-- The tail: computes `tailVal a d j R v` in register `7`, stores it at `h` and `h + 1`, stores
`1` at `h + 2`, and returns `h + 3`. -/
def gammaTail (a : ℕ) : Stmt :=
  .assign 12 (.bin .add (.reg 9) (.const 2)) ;;
  .assign 12 (.bin .mul (.reg 12) (.reg 12)) ;;
  .assign 12 (.bin .mul (.reg 12) (.reg 12)) ;;
  .assign 13 (.bin .add (.bin .shiftLeft (.const 1) (.bin .add (.const 1) (.reg 10))) (.const 1)) ;;
  .assign 13 (.bin .mul (.reg 13) (.reg 13)) ;;
  .assign 13 (.bin .mul (.reg 13) (.reg 13)) ;;
  .assign 14 (.bin .add (.const 2) (.reg 0)) ;;
  .assign 14 (.bin .mul (.reg 14) (.reg 14)) ;;
  .assign 14 (.bin .mul (.reg 14) (.reg 14)) ;;
  .assign 14 (.bin .add (.const 1) (.reg 14)) ;;
  .assign 14 (.bin .mul (.reg 14) (.reg 14)) ;;
  .assign 15 (.bin .mul (.bin .mul (.const a) (.reg 9)) (.reg 11)) ;;
  .assign 15 (.bin .mul (.reg 15) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 2))) ;;
  .assign 15 (.bin .add (.bin .add (.const 12) (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))))
    (.reg 15)) ;;
  .assign 15 (.bin .shiftLeft (.const 1) (.reg 15)) ;;
  .assign 7 (.bin .mul (.reg 12) (.reg 13)) ;;
  .assign 7 (.bin .mul (.reg 7) (.reg 14)) ;;
  .assign 7 (.bin .mul (.reg 7) (.reg 15)) ;;
  .store (.reg 2) (.reg 7) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 7) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.const 1) ;;
  .ret (.bin .add (.reg 2) (.const 3))

lemma gammaTail_noRand (a : ℕ) : (gammaTail a).NoRand := by simp [gammaTail, Stmt.NoRand]

private lemma le_mul_of_one_le' {x y : ℕ} (hy : 1 ≤ y) : x ≤ x * y := Nat.le_mul_of_pos_right x hy

private lemma le_mul_of_one_le'' {x y : ℕ} (hy : 1 ≤ y) : x ≤ y * x := Nat.le_mul_of_pos_left x hy

lemma shiftLeft_one (n : ℕ) : 1 <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, one_mul]

/-- The tail runs and writes `[tailVal, tailVal, 1]` at `h`, when `tailVal` and `h + 3` fit in a
word and `j, v ≥ 1`. -/
theorem gammaTail_runs {w a d j R v h : ℕ} {p : Program} (ω : ℕ → Bool) (st : State)
    (hj : 1 ≤ j) (hv : 1 ≤ v) (hP : tailVal a d j R v < 2 ^ w) (hh : h + 3 < 2 ^ w)
    (hr0 : st.regs 0 = d) (hr2 : st.regs 2 = h) (hr9 : st.regs 9 = j) (hr10 : st.regs 10 = R)
    (hr11 : st.regs 11 = v) :
    ∃ o st' c, Runs w p ω (gammaTail a) st o st' c ∧
      (o = .returned (h + 3) ∧ st'.mem = Function.update (Function.update (Function.update st.mem
        h (tailVal a d j R v)) (h + 1) (tailVal a d j R v)) (h + 2) 1) ∧ c ≤ 200 := by
  set s1 := j + 2
  set s2 := s1 * s1
  set s3 := s2 * s2
  set k1 := 2 ^ (1 + R) + 1
  set k2 := k1 * k1
  set k3 := k2 * k2
  set t1 := 2 + d
  set t2 := t1 * t1
  set t3 := t2 * t2
  set t4 := 1 + t3
  set t5 := t4 * t4
  set u1 := a * j * v
  set u2 := u1 * (2 * j + 2)
  set e := tailExp a j v
  set E := 2 ^ e
  set P := tailVal a d j R v
  have hPdef : P = s3 * k3 * t5 * E := rfl
  have he : e = 12 + 2 * (j + 1) + u2 := rfl
  have hs1 : 1 ≤ s1 := by omega
  have hs2 : 1 ≤ s2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hs3 : 1 ≤ s3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hk1 : 2 ≤ k1 := by have : 1 ≤ 2 ^ (1 + R) := Nat.one_le_two_pow; omega
  have hk2 : 1 ≤ k2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hk3 : 1 ≤ k3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht1 : 1 ≤ t1 := by omega
  have ht2 : 1 ≤ t2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht3 : 1 ≤ t3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht5 : 1 ≤ t5 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have heE : e < E := Nat.lt_two_pow_self
  -- every intermediate value is at most `P`
  have hg1 : s3 * k3 ≤ P := by
    rw [hPdef]; exact le_trans (le_mul_of_one_le' ht5) (le_mul_of_one_le' hE)
  have hg2 : s3 * k3 * t5 ≤ P := by rw [hPdef]; exact le_mul_of_one_le' hE
  have hs3P : s3 ≤ P := le_trans (le_mul_of_one_le' hk3) hg1
  have hk3P : k3 ≤ P := le_trans (le_mul_of_one_le'' hs3) hg1
  have ht5P : t5 ≤ P := le_trans (le_mul_of_one_le'' (Nat.one_le_iff_ne_zero.mpr (by positivity)))
    hg2
  have hEP : E ≤ P := by rw [hPdef]; exact le_mul_of_one_le'' (Nat.one_le_iff_ne_zero.mpr
    (by positivity))
  have hs2P : s2 ≤ P := le_trans (le_mul_of_one_le' hs2) hs3P
  have hs1P : s1 ≤ P := le_trans (le_mul_of_one_le' hs1) hs2P
  have hk2P : k2 ≤ P := le_trans (le_mul_of_one_le' hk2) hk3P
  have hk1P : k1 ≤ P := le_trans (le_mul_of_one_le' (by omega)) hk2P
  have ht4P : t4 ≤ P := le_trans (le_mul_of_one_le' (by omega)) ht5P
  have ht3P : t3 ≤ P := le_trans (by omega) ht4P
  have ht2P : t2 ≤ P := le_trans (le_mul_of_one_le' ht2) ht3P
  have ht1P : t1 ≤ P := le_trans (le_mul_of_one_le' ht1) ht2P
  have hu2e : u2 ≤ e := by omega
  have hu1u2 : u1 ≤ u2 := le_mul_of_one_le' (by omega)
  have hajv : a * j ≤ u1 := le_mul_of_one_le' hv
  have ha : a ≤ a * j := le_mul_of_one_le' hj
  have hPw := hP
  have hlt : ∀ x, x ≤ P → x < 2 ^ w := fun x hx => lt_of_le_of_lt hx hPw
  have h2w : 12 < 2 ^ w := hlt 12 (by
    have : 12 ≤ e := by omega
    omega)
  have hR1 : 1 + R < 2 ^ w := hlt _ (by
    have : 1 + R < 2 ^ (1 + R) := Nat.lt_two_pow_self
    omega)
  have hpowR : 1 <<< (1 + R) = 2 ^ (1 + R) := shiftLeft_one _
  have hpowe : 1 <<< e = E := shiftLeft_one _
  have h1w : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := s1) (Expr.eval_add (x := j) (y := 2) (Expr.eval_reg_of_eq hr9)
    (Expr.eval_const (by omega)) (hlt _ hs1P)) ?_
  refine runs_seq_assign_le (v := s2) (Expr.eval_mul (x := s1) (y := s1)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hs2P)) ?_
  refine runs_seq_assign_le (v := s3) (Expr.eval_mul (x := s2) (y := s2)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hs3P)) ?_
  refine runs_seq_assign_le (v := k1) (Expr.eval_eq_of_eq (Expr.eval_add
    (Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_add (Expr.eval_const h1w)
      (Expr.eval_reg_of_eq (by simp [hr10])) hR1) (by rw [hpowR]; exact hlt _ (by omega)))
    (Expr.eval_const h1w) (by rw [hpowR]; exact hlt _ hk1P)) (by rw [hpowR])) ?_
  refine runs_seq_assign_le (v := k2) (Expr.eval_mul (x := k1) (y := k1)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hk2P)) ?_
  refine runs_seq_assign_le (v := k3) (Expr.eval_mul (x := k2) (y := k2)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hk3P)) ?_
  refine runs_seq_assign_le (v := t1) (Expr.eval_add (x := 2) (y := d) (Expr.eval_const (by omega))
    (Expr.eval_reg_of_eq (by simp [hr0])) (hlt _ ht1P)) ?_
  refine runs_seq_assign_le (v := t2) (Expr.eval_mul (x := t1) (y := t1)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ ht2P)) ?_
  refine runs_seq_assign_le (v := t3) (Expr.eval_mul (x := t2) (y := t2)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ ht3P)) ?_
  refine runs_seq_assign_le (v := t4) (Expr.eval_add (x := 1) (y := t3) (Expr.eval_const h1w)
    (Expr.eval_reg_of_eq (by simp)) (hlt _ ht4P)) ?_
  refine runs_seq_assign_le (v := t5) (Expr.eval_mul (x := t4) (y := t4)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ ht5P)) ?_
  refine runs_seq_assign_le (v := u1) (Expr.eval_mul (x := a * j) (y := v)
    (Expr.eval_mul (Expr.eval_const (hlt _ (by omega))) (Expr.eval_reg_of_eq (by simp [hr9]))
      (hlt _ (by omega)))
    (Expr.eval_reg_of_eq (by simp [hr11])) (hlt _ (by omega))) ?_
  refine runs_seq_assign_le (v := u2) (Expr.eval_mul (x := u1) (y := 2 * j + 2)
    (Expr.eval_reg_of_eq (by simp))
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr9]))
      (hlt _ (by omega))) (Expr.eval_const (by omega)) (hlt _ (by omega)))
    (hlt _ (by omega))) ?_
  refine runs_seq_assign_le (v := e) (Expr.eval_add (x := 12 + 2 * (j + 1)) (y := u2)
    (Expr.eval_add (Expr.eval_const h2w) (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr9])) (Expr.eval_const h1w) (hlt _ (by omega)))
      (hlt _ (by omega))) (hlt _ (by omega)))
    (Expr.eval_reg_of_eq (by simp)) (hlt _ (by omega))) ?_
  refine runs_seq_assign_le (v := E) (Expr.eval_eq_of_eq (Expr.eval_shiftLeft (Expr.eval_const h1w)
    (Expr.eval_reg_of_eq (by simp)) (by rw [hpowe]; exact hlt _ hEP)) hpowe) ?_
  refine runs_seq_assign_le (v := s3 * k3) (Expr.eval_mul
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hg1)) ?_
  refine runs_seq_assign_le (v := s3 * k3 * t5) (Expr.eval_mul
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ hg2)) ?_
  refine runs_seq_assign_le (v := P) (Expr.eval_mul (x := s3 * k3 * t5) (y := E)
    (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (hlt _ le_rfl)) ?_
  refine runs_seq_store_le (x := h) (v := P) (Expr.eval_reg_of_eq (by simp [hr2]))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := h + 1) (v := P) (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2]))
    (Expr.eval_const h1w) (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := h + 2) (v := 1) (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2]))
    (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const h1w) ?_
  refine runs_ret_le (v := h + 3) (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2]))
    (Expr.eval_const (by omega)) hh) ⟨rfl, rfl⟩ ?_
  simp only [Expr.size]
  omega

end MinCostFlow.HierPaths
