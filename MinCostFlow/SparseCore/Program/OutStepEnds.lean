module

public import MinCostFlow.SparseCore.Program.OutStepSplit

/-!
# The first and the last part of the output step

The output step starts with `osSetup`, which reads the caps of the stored graph, puts the
fixed addresses of the step in registers (`SRegs`), and sets the two record pointers and the two
counts. It ends with `osFinal`, which writes the two counts in front of the batch and the edits,
writes the four words at `h`, and returns the heap pointer. This file proves both parts
(`osSetup_runs`, `osFinal_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}

/-- **The setup of the output step.** -/
theorem osSetup_runs {st : State} {A : OSArgs} {G : MGraph}
    (h0 : st.regs 0 = A.outH) (h1 : st.regs 1 = A.tourH) (h2 : st.regs 2 = A.delPtr)
    (h3 : st.regs 3 = A.splitPtr) (h4 : st.regs 4 = A.insPtr) (h5 : st.regs 5 = A.rotPtr)
    (h6 : st.regs 6 = A.h) (hout : st.mem A.outH = A.g) (hG : DynGraphAt st.mem A.g vCap eCap G)
    (hR : A.R = (vCap + 1) * (eCap + 1) * 16) (ht0 : A.t0 < 2 ^ w)
    (hgh : A.g + dynGraphSize vCap eCap ≤ A.h) :
    ∃ st' c, Runs w p ω osSetup st .normal st' c ∧ st'.mem = st.mem ∧ SRegs st' A vCap eCap ∧
      st'.regs 7 = A.t0 ∧ st'.regs 14 = A.h + 5 ∧ st'.regs 16 = A.e0 + 1 ∧
      st'.regs 17 = 0 ∧ st'.regs 18 = 0 ∧ c ≤ 200 := by
  have hvc : st.mem A.g = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec : st.mem (A.g + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hRv : (vCap + 1) * (eCap + 1) ≤ A.R := by rw [hR]; omega
  have hv1 : vCap + 1 ≤ (vCap + 1) * (eCap + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have he1 : eCap + 1 ≤ (vCap + 1) * (eCap + 1) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨_, _, runs_seq_normal (runs_assign_of (r := 10) (v := A.g) ?_)
    (runs_seq_normal (runs_assign_of (r := 11) (v := vCap) ?_)
    (runs_seq_normal (runs_assign_of (r := 12) (v := eCap) ?_)
    (runs_seq_normal (runs_assign_of (r := 13) (v := A.R) ?_)
    (runs_seq_normal (runs_assign_of (r := 14) (v := A.h + 5) ?_)
    (runs_seq_normal (runs_assign_of (r := 15) (v := A.e0) ?_)
    (runs_seq_normal (runs_assign_of (r := 16) (v := A.e0 + 1) ?_)
    (runs_seq_normal (runs_assign_of (r := 7) (v := A.t0) ?_)
    (runs_seq_normal (runs_assign_of (r := 17) (v := 0) ?_)
    (runs_seq_normal (runs_assign_of (r := 18) (v := 0) ?_)
    (runs_seq_normal (runs_assign_of (r := 19) (v := dgEPresBase A.g vCap) ?_)
    (runs_seq_normal (runs_assign_of (r := 23) (v := dgExtToIntBase A.g vCap) ?_)
    (runs_seq_normal (runs_assign_of (r := 24) (v := dgIncHeadBase A.g vCap) ?_)
      (runs_assign_of (r := 25) (v := dgHeNextBase A.g vCap eCap) ?_))))))))))))), rfl,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Expr.eval_load_of_eq (Expr.eval_reg_of_eq h0) hout
  · exact Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hvc
  · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) hec
  · rw [hR]
    exact Expr.eval_mul (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega)
  · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [h6])) (Expr.eval_const (by omega))
      (by omega)
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h6]))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)
  · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)
  · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [OSArgs.e0]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)
  · exact Expr.eval_const (by omega)
  · exact Expr.eval_const (by omega)
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)
  · exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
      (by omega)
  all_goals simp [Function.update_apply, h0, h1, h2, h3, h4, h5, h6]

/-- **The end of the output step**: the two counts, the four words at `h`, and the return of
the heap pointer. -/
theorem osFinal_runs {st : State} {A : OSArgs} {bp ep nU nE : ℕ}
    (h6 : st.regs 6 = A.h) (h14 : st.regs 14 = bp)
    (h15 : st.regs 15 = A.e0) (h16 : st.regs 16 = ep) (h17 : st.regs 17 = nU)
    (h18 : st.regs 18 = nE) (hbp : A.h + 5 ≤ bp) (hbe : bp ≤ A.e0) (hep : A.e0 + 1 ≤ ep)
    (hw : ep < 2 ^ w) (hnU : nU < 2 ^ w) :
    ∃ st' c, Runs w p ω osFinal st (.returned (st.regs 7)) st' c ∧
      st'.mem = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st.mem (A.h + 4) nU) A.e0 nE) A.h (A.h + 4))
        (A.h + 1) (bp - (A.h + 4))) (A.h + 2) A.e0) (A.h + 3) (ep - A.e0) ∧ c ≤ 60 := by
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  obtain ⟨st₁, hr₁, hm₁, hg₁⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .bin .add (.reg 6) (.const 4)) (e := .reg 17) (st := st) (x := A.h + 4) (v := nU)
    (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq h17)
  obtain ⟨st₂, hr₂, hm₂, hg₂⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .reg 15) (e := .reg 18) (st := st₁) (x := A.e0) (v := nE)
    (Expr.eval_reg_of_eq (by rw [hg₁, h15])) (Expr.eval_reg_of_eq (by rw [hg₁, h18]))
  obtain ⟨st₃, hr₃, hm₃, hg₃⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .reg 6) (e := .bin .add (.reg 6) (.const 4)) (st := st₂) (x := A.h) (v := A.h + 4)
    (Expr.eval_reg_of_eq (by rw [hg₂, hg₁, h6]))
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₂, hg₁, h6])) (Expr.eval_const (by omega))
      (by omega))
  obtain ⟨st₄, hr₄, hm₄, hg₄⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .bin .add (.reg 6) (.const 1)) (e := .bin .sub (.reg 14) (.bin .add (.reg 6) (.const 4)))
    (st := st₃) (x := A.h + 1) (v := bp - (A.h + 4))
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₃, hg₂, hg₁, h6])) (Expr.eval_const (by omega))
      (by omega))
    (Expr.eval_sub (Expr.eval_reg_of_eq (by rw [hg₃, hg₂, hg₁, h14]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₃, hg₂, hg₁, h6]))
        (Expr.eval_const (by omega)) (by omega)) (by omega))
  obtain ⟨st₅, hr₅, hm₅, hg₅⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .bin .add (.reg 6) (.const 2)) (e := .reg 15) (st := st₄) (x := A.h + 2) (v := A.e0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, hg₂, hg₁, h6]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, hg₂, hg₁, h15]))
  obtain ⟨st₆, hr₆, hm₆, hg₆⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .bin .add (.reg 6) (.const 3)) (e := .bin .sub (.reg 16) (.reg 15)) (st := st₅)
    (x := A.h + 3) (v := ep - A.e0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, hg₂, hg₁, h6]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_sub (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, hg₂, hg₁, h16]))
      (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, hg₂, hg₁, h15])) hw)
  have hret := step_ret (w := w) (p := p) (ω := ω) (st := st₆) (e := .reg 7) (v := st.regs 7)
    (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, hg₃, hg₂, hg₁]))
  refine ⟨st₆, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
    (runs_seq_normal hr₄ (runs_seq_normal hr₅ (runs_seq_normal hr₆ hret))))), ?_, ?_⟩
  · rw [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁]
  · simp only [Expr.size]; omega

end MinCostFlow.SparseCore.Program
