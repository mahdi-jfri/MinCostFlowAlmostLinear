module

public import MinCostFlow.LowStretch.ProgClusterSet13
public import MinCostFlow.LowStretch.ProgPreLoop

/-!
# The tables of the tests of the petal searches

The petal searches read two tables (`PW.Ok.hsq`, `PW.Ok.hP2`): `P2[q] = 2 ^ λ(q)` with
`λ(q) = 2 ^ (L - q)`, and `SQ[q] = bw / (λ(q - 1) + 3)`, for `1 ≤ q ≤ L`. The setup writes both
with the table loop `tabP` (`args = [L + 2, DST, L, bw]`, index in register `15`), using the
expressions `p2E` and `sqE` below. Here we show what they evaluate to (`p2E_eval`, `sqE_eval`).
The copy `NXT` of the parents, the table `AS` with `AS[i] = i / 2` and the table `EXP` of the
exponents of the active entries are written the same way (`cpE`, `halfE`, `expE`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `1 <<< (1 <<< (L - i))`, with `L` in register `2` and `i` in register `15`. -/
def p2E : Expr :=
  .bin .shiftLeft (.const 1) (.bin .shiftLeft (.const 1) (.bin .sub (.reg 2) (.reg 15)))

/-- `bw / ((1 <<< (L - (i - 1))) + 3)`, with `L`, `bw`, `i` in registers `2`, `3`, `15`. -/
def sqE : Expr :=
  .bin .div (.reg 3) (.bin .add (.bin .shiftLeft (.const 1)
    (.bin .sub (.reg 2) (.bin .sub (.reg 15) (.const 1)))) (.const 3))

theorem two_pow_lt_two_pow_two_pow (k : ℕ) : 2 ^ k < 2 ^ 2 ^ k :=
  Nat.pow_lt_pow_right (by norm_num) (Nat.lt_two_pow_self)

/-- The value of `p2E`: `2 ^ 2 ^ (L - i)`. -/
theorem p2E_eval {w : ℕ} {st : State} {Lb i : ℕ} (h2 : st.regs 2 = Lb) (h15 : st.regs 15 = i)
    (hw : 2 ^ 2 ^ Lb < 2 ^ w) : p2E.eval w st = some (2 ^ 2 ^ (Lb - i)) := by
  have hle : 2 ^ 2 ^ (Lb - i) ≤ 2 ^ 2 ^ Lb :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hle' : 2 ^ (Lb - i) ≤ 2 ^ Lb := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := two_pow_lt_two_pow_two_pow Lb
  have h4 := two_pow_lt_two_pow_two_pow (Lb - i)
  have h5 : Lb - i < 2 ^ (Lb - i) := Nat.lt_two_pow_self
  have hs := Expr.eval_bin (w := w) (st := st) (op := .sub) (Expr.eval_reg_of_eq h2)
    (Expr.eval_reg_of_eq h15) (by simp only [BinOp.eval]; omega)
  have hi := Expr.eval_bin (w := w) (op := .shiftLeft) (Expr.eval_const (k := 1) (by omega)) hs
    (by simp only [BinOp.eval, Nat.one_shiftLeft]; omega)
  have ho := Expr.eval_bin (w := w) (op := .shiftLeft) (Expr.eval_const (k := 1) (by omega)) hi
    (by simp only [BinOp.eval, Nat.one_shiftLeft]; omega)
  simpa [p2E, BinOp.eval, Nat.one_shiftLeft] using ho

/-- The value of `sqE`: `bw / (2 ^ (L - (i - 1)) + 3)`. -/
theorem sqE_eval {w : ℕ} {st : State} {Lb bw i : ℕ} (h2 : st.regs 2 = Lb) (h3 : st.regs 3 = bw)
    (h15 : st.regs 15 = i) (hi : i ≤ Lb + 1) (hw : 2 ^ Lb + 3 < 2 ^ w) (hbw : bw < 2 ^ w) :
    sqE.eval w st = some (bw / (2 ^ (Lb - (i - 1)) + 3)) := by
  have hle' : 2 ^ (Lb - (i - 1)) ≤ 2 ^ Lb := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : Lb < 2 ^ Lb := Nat.lt_two_pow_self
  have h6 : Lb - (i - 1) < 2 ^ (Lb - (i - 1)) := Nat.lt_two_pow_self
  have h1 := Expr.eval_bin (w := w) (st := st) (op := .sub) (Expr.eval_reg_of_eq h15)
    (Expr.eval_const (k := 1) (by omega)) (by simp only [BinOp.eval]; omega)
  have hs := Expr.eval_bin (w := w) (op := .sub) (Expr.eval_reg_of_eq h2) h1
    (by simp only [BinOp.eval]; omega)
  have hl := Expr.eval_bin (w := w) (op := .shiftLeft) (Expr.eval_const (k := 1) (by omega)) hs
    (by simp only [BinOp.eval, Nat.one_shiftLeft]; omega)
  have ha := Expr.eval_bin (w := w) (op := .add) hl (Expr.eval_const (k := 3) (by omega))
    (by simp only [BinOp.eval, Nat.one_shiftLeft]; omega)
  have hd := Expr.eval_bin (w := w) (op := .div) (Expr.eval_reg_of_eq h3) ha
    (by simp only [BinOp.eval]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hbw)
  simpa [sqE, BinOp.eval, Nat.one_shiftLeft] using hd

/-- The table of `p2E` holds `2 ^ λ(q)`. -/
theorem p2_eq (P : Par) (q : ℕ) : 2 ^ 2 ^ (P.L - q) = 2 ^ Cl.lam P q := rfl

/-- The table of `sqE` holds the slack `sq q`. -/
theorem sq_eq (G : PG) (P : Par) (c : Cl) (q : ℕ) :
    c.bw G P / (2 ^ (P.L - (q - 1)) + 3) = c.sq G P q := rfl

/-! ### The copy of the parents and the tables of the entries -/

/-- `SRC[i]`, with `SRC` in register `2`: the copy `NXT` of the parents. -/
def cpE : Expr := .load (.bin .add (.reg 2) (.reg 15))

/-- `i / 2`: the table `AS`. -/
def halfE : Expr := .bin .div (.reg 15) (.const 2)

/-- `EXPg[ACT[2 i]]`, with `EXPg` and `ACT` in registers `2` and `3`: the table `EXP` of the
exponents of the active entries. -/
def expE : Expr :=
  .load (.bin .add (.reg 2) (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 15)))))

theorem cpE_eval {w : ℕ} {st : State} {SRC i : ℕ} (h2 : st.regs 2 = SRC) (h15 : st.regs 15 = i)
    (hw : SRC + i < 2 ^ w) : cpE.eval w st = some (st.mem (SRC + i)) :=
  Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq h15) hw) rfl

theorem halfE_eval {w : ℕ} {st : State} {i : ℕ} (h15 : st.regs 15 = i) (hw : 2 < 2 ^ w)
    (hi : i < 2 ^ w) : halfE.eval w st = some (i / 2) := by
  have hd : i / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hi
  have := Expr.eval_bin (w := w) (st := st) (op := .div) (Expr.eval_reg_of_eq h15)
    (Expr.eval_const (k := 2) hw) (by simp only [BinOp.eval]; exact hd)
  simpa [halfE, BinOp.eval] using this

theorem expE_eval {w : ℕ} {st : State} {EXPg ACT i : ℕ} (h2 : st.regs 2 = EXPg)
    (h3 : st.regs 3 = ACT) (h15 : st.regs 15 = i) (hw1 : 2 < 2 ^ w) (hw : ACT + 2 * i < 2 ^ w)
    (hw2 : EXPg + st.mem (ACT + 2 * i) < 2 ^ w) :
    expE.eval w st = some (st.mem (EXPg + st.mem (ACT + 2 * i))) := by
  have hm := Expr.eval_bin (w := w) (st := st) (op := .mul) (Expr.eval_const (k := 2) (by omega))
    (Expr.eval_reg_of_eq h15) (by simp only [BinOp.eval]; omega)
  have hl := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3) hm
    (by simp only [BinOp.eval]; omega)) rfl
  exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2) hl hw2) (by simp [BinOp.eval])

end MinCostFlow.LowStretch
