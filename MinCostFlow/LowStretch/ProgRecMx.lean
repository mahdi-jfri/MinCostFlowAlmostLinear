module

public import MinCostFlow.LowStretch.ProgPreLoop2

/-!
# The largest word of an array

`mxP` with `args = [M, A0]` returns the largest of the words `A0[0], …, A0[M - 1]` (`0` if
`M = 0`) and changes no memory (`mxP_spec`). The root of the recursion uses it for the largest
rounded weight.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The body of `mxP`: `x := A0[i]`; if `W < x` then `W := x`. -/
def mxB : Stmt :=
  .seq (.assign 3 (.load (.bin .add (.reg 1) (.reg 15))))
  (.cond (.bin .lt (.reg 2) (.reg 3)) (.assign 2 (.reg 3)) .nop)

/-- `mxP` with `args = [M, A0]`. -/
def mxP : Stmt :=
  .seq (forRange 15 (.const 0) (.reg 0) mxB) (.ret (.reg 2))

theorem mxP_noRand : mxP.NoRand := by simp [mxP, mxB, forRange, forUp, Stmt.NoRand]

/-- The contract of `mxP`. -/
def mxC (w : ℕ) : Contract where
  pre args mem := ∃ M A0, args = [M, A0] ∧ A0 + M + 1 < 2 ^ w ∧ ∀ j < M, mem (A0 + j) < 2 ^ w
  post args mem v mem' := mem' = mem ∧ (∀ j < args.getD 0 0, mem (args.getD 1 0 + j) ≤ v) ∧
    (v = 0 ∨ ∃ j < args.getD 0 0, v = mem (args.getD 1 0 + j))
  cost args _ := 30 * args.getD 0 0 + 20

theorem mxP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [mxP]) :
    MeetsContract w p b (mxC w) := by
  intro args mem pos ω _ hpre
  obtain ⟨M, A0, rfl, hbd, hwt⟩ := hpre
  have hproc : p.procs[b]? = some mxP := hp 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun i st => st.regs 0 = M ∧ st.regs 1 = A0 ∧ st.regs 15 = i ∧
    st.mem = mem ∧ (∀ j < i, mem (A0 + j) ≤ st.regs 2) ∧
    (st.regs 2 = 0 ∨ ∃ j < i, st.regs 2 = mem (A0 + j))
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := mxB) (P := fun st => st = startState [M, A0] mem pos) (Inv := I) 20 0 M
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      exact ⟨Expr.eval_const (by omega), rfl, rfl, by simp, rfl, fun _ h => absurd h (by omega),
        Or.inl (by simp [startState])⟩)
    (fun _ _ _ _ hI => hI.2.2.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq hI.1)
    (fun i _ hi st ω hI => by
      obtain ⟨h0, h1, h15, hm, hle, hor⟩ := hI
      have ha : (Expr.bin .add (.reg 1) (.reg 15)).eval w st = some (A0 + i) :=
        Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq h15) (by omega)
      have hx := Expr.eval_load_of_eq ha (show st.mem (A0 + i) = mem (A0 + i) by rw [hm])
      refine runs_start_le (runs_seq_assign_le hx ?_)
      set x := mem (A0 + i) with hx'
      have hxw : x < 2 ^ w := hwt i hi
      have hc := Expr.eval_bin (op := .lt) (st := { st with regs := Function.update st.regs 3 x })
        (Expr.eval_reg_of_eq (r := 2) (v := st.regs 2) (by simp))
        (Expr.eval_reg_of_eq (r := 3) (v := x) (by simp))
        (show (if _ < x then 1 else 0) < 2 ^ w by split_ifs <;> omega)
      refine runs_cond_le hc (fun hv => ?_) (fun hv => ?_)
      · have hlt : st.regs 2 < x := by
          by_contra h; exact hv (by simp [BinOp.eval, h])
        refine runs_assign_le (Expr.eval_reg_of_eq (r := 3) (v := x) (by simp)) ?_
          (by simp only [Expr.size]; omega)
        refine ⟨⟨by simp [h0], by simp [h1],
          by simp, by simp [hm], fun j hj => ?_, Or.inr ⟨i, by omega, by simp [hx']⟩⟩,
          by simp [h15]⟩
        simp only [Function.update_apply]
        simp only [show (2 : ℕ) ≠ 15 by omega, ite_true, ite_false]
        rcases Nat.lt_or_ge j i with hj' | hj'
        · have := hle j hj'; omega
        · rw [show j = i by omega]
      · have hge : x ≤ st.regs 2 := by
          by_contra h; push Not at h
          simp [BinOp.eval, h] at hv
        refine runs_nop_le ⟨⟨by simp [h0],
          by simp [h1], by simp, by simp [hm], fun j hj => ?_, ?_⟩,
          by simp [h15]⟩ (by simp only [Expr.size]; omega)
        · simp only [Function.update_apply]
          simp only [show (2 : ℕ) ≠ 15 by omega, show (2 : ℕ) ≠ 3 by omega, ite_false]
          rcases Nat.lt_or_ge j i with hj' | hj'
          · exact hle j hj'
          · rw [show j = i by omega]; exact hge
        · simp only [Function.update_apply]
          simp only [show (2 : ℕ) ≠ 15 by omega, show (2 : ℕ) ≠ 3 by omega, ite_false]
          rcases hor with h | ⟨j, hj, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, he⟩)
  refine ⟨mxP, hproc, ?_⟩
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, -, hm, hle, hor⟩ := hI
  refine runs_ret_le (Expr.eval_reg w 2 st) ⟨hm, hle, hor⟩ ?_
  simp only [Expr.size, mxC, List.getD_cons_zero]
  omega

end MinCostFlow.LowStretch
