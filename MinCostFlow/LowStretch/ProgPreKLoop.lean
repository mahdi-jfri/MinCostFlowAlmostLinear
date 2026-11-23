module

public import MinCostFlow.LowStretch.ProgPreLoop

/-!
# Two table loops of the preprocessing

* `tabP eMin` with `args = [m, TL, IN]` writes the smaller end of each pair to `TL`
  (`minSpec`). The machine has no minimum, so it computes `a - (a - b)`.
* `tabP eKey` with `args = [c, KEYS, OUT, EXP, m]` writes the sort key `EXP[q] · m + q` of the
  pair `q = OUT[j]` to `KEYS + j` (`keySpec`). Sorting the keys sorts the pairs by exponent, and
  `q` is the key modulo `m`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The first end of pair `i`, with `IN` in register `2` and `i` in register `15`. -/
def eEnd0 : Expr := .load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 15)))

/-- The second end of pair `i`. -/
def eEnd1 : Expr := .load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 15))) (.const 1))

/-- The smaller end: `a - (a - b)`. -/
def eMin : Expr := .bin .sub eEnd0 (.bin .sub eEnd0 eEnd1)

/-- What `tabP eMin` needs. -/
def minPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ M DST IN, args = [M, DST, IN] ∧ IN + 3 * M + 2 ≤ DST ∧ DST < 2 ^ w ∧
    ∀ i < M, mem (IN + 3 * i) < 2 ^ w

/-- What `tabP eMin` writes. -/
def minF (args : List ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ :=
  min (mem (args.getD 2 0 + 3 * i)) (mem (args.getD 2 0 + 3 * i + 1))

theorem minSpec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP eMin]) :
    MeetsContract w p b (tabC w eMin (minPre w) minF) := by
  refine tabP_spec hp (fun args mem hpre st hR hi hfr => ?_)
  obtain ⟨M, DST, IN, rfl, l1, hD, hlt⟩ := hpre
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hi hfr ⊢
  have h2 : st.regs 2 = IN := hR 2 (by norm_num)
  obtain ⟨i, h15⟩ : ∃ i, st.regs 15 = i := ⟨_, rfl⟩
  rw [h15] at hi ⊢
  have ha : st.mem (IN + 3 * i) = mem (IN + 3 * i) := hfr _ (Or.inl (by omega))
  have e0 : eEnd0.eval w st = some (mem (IN + 3 * i)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h15) (by omega))
      (by omega)) ha
  have e1 : eEnd1.eval w st = some (mem (IN + 3 * i + 1)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h2)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h15) (by omega))
      (by omega)) (Expr.eval_const (by omega)) (by omega)) (hfr _ (Or.inl (by omega)))
  have hx := hlt i hi
  have e2 := Expr.eval_bin (op := .sub) e0 e1 (by simp; omega)
  have e3 := Expr.eval_bin (op := .sub) e0 e2 (by simp; omega)
  unfold eMin; rw [e3]; unfold minF
  simp only [List.getD_cons_zero, List.getD_cons_succ, BinOp.eval_sub]
  congr 1; omega

/-- The pair `OUT[j]`, with `OUT` in register `2` and `j` in register `15`. -/
def eOut : Expr := .load (.bin .add (.reg 2) (.reg 15))

/-- The sort key `EXP[q] · m + q` of `q = OUT[j]`, with `EXP` and `m` in registers `3` and `4`. -/
def eKey : Expr := .bin .add (.bin .mul (.load (.bin .add (.reg 3) eOut)) (.reg 4)) eOut

/-- What `tabP eKey` needs. -/
def keyPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ c KEYS OUT EXP m, args = [c, KEYS, OUT, EXP, m] ∧ OUT + c ≤ KEYS ∧ EXP + m ≤ KEYS ∧
    KEYS < 2 ^ w ∧ m < 2 ^ w ∧
    ∀ j < c, mem (OUT + j) < m ∧ mem (EXP + mem (OUT + j)) * m + mem (OUT + j) < 2 ^ w

/-- What `tabP eKey` writes. -/
def keyF (args : List ℕ) (mem : ℕ → ℕ) (j : ℕ) : ℕ :=
  mem (args.getD 3 0 + mem (args.getD 2 0 + j)) * args.getD 4 0 + mem (args.getD 2 0 + j)

theorem keySpec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP eKey]) :
    MeetsContract w p b (tabC w eKey (keyPre w) keyF) := by
  refine tabP_spec hp (fun args mem hpre st hR hi hfr => ?_)
  obtain ⟨c, KEYS, OUT, EXP, m, rfl, l1, l2, hK, hm, hlt⟩ := hpre
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hi hfr ⊢
  have h2 : st.regs 2 = OUT := hR 2 (by norm_num)
  have h3 : st.regs 3 = EXP := hR 3 (by norm_num)
  have h4 : st.regs 4 = m := hR 4 (by norm_num)
  obtain ⟨j, h15⟩ : ∃ j, st.regs 15 = j := ⟨_, rfl⟩
  rw [h15] at hi ⊢
  obtain ⟨hq, hk⟩ := hlt j hi
  have ha : st.mem (OUT + j) = mem (OUT + j) := hfr _ (Or.inl (by omega))
  have hb : st.mem (EXP + mem (OUT + j)) = mem (EXP + mem (OUT + j)) := hfr _ (Or.inl (by omega))
  have e0 : eOut.eval w st = some (mem (OUT + j)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq h15)
      (by omega)) ha
  have e1 := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3) e0 (by omega)) hb
  have hle : mem (EXP + mem (OUT + j)) * m ≤ mem (EXP + mem (OUT + j)) * m + mem (OUT + j) :=
    Nat.le_add_right _ _
  have e2 := Expr.eval_mul e1 (Expr.eval_reg_of_eq h4) (by omega)
  have e3 := Expr.eval_add e2 e0 hk
  unfold eKey; rw [e3]; rfl

end MinCostFlow.LowStretch
