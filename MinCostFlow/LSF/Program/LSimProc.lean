module

public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.Machine.WideWord.LSSTProgramBase

/-!
# The limb count of the `[AN19]` simulation

The call of the low-stretch tree program needs `L_sim ≥ lsstLSimMin c_AN n m L h`. The program
computes this number at run time from `m` and `L`. The constants `c_AN` and `h` are fixed by the
program, so they may appear in its code.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.WideWord

@[expose] public section

/-- Args: `[m, L]`. Returns `max (kWidthOf m L) (w'Max c n m L h)`. -/
def lsimProc (bLog c h : ℕ) : Stmt :=
  .call 2 bLog [.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 2)] ;;
  .assign 3 (.bin .add (.bin .add (.reg 1) (.reg 2)) (.const 3)) ;;
  .call 4 bLog [.bin .add (.bin .mul (.const 16) (.reg 0)) (.const 6)] ;;
  .assign 5 (.bin .mul (.const c)
    (.bin .add (.bin .add (.reg 4) (.bin .mul (.reg 3) (.const h))) (.const 3))) ;;
  .cond (.bin .lt (.reg 3) (.reg 5)) (.ret (.reg 5)) (.ret (.reg 3))

lemma lsimProc_noRand (bLog c h : ℕ) : (lsimProc bLog c h).NoRand := by
  simp [lsimProc, Stmt.NoRand]

/-- The contract of `lsimProc`. -/
def lsimContract (w c h : ℕ) : Contract where
  pre args _ := ∃ m L, args = [m, L] ∧ 16 * m + 6 < 2 ^ w ∧ 16 < 2 ^ w ∧ c < 2 ^ w ∧
    h < 2 ^ w ∧ kWidthOf m L < 2 ^ w ∧
    Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3 < 2 ^ w ∧ w'Max c 0 m L h < 2 ^ w
  post args mem ret mem' := ∃ m L, args = [m, L] ∧ mem' = mem ∧
    ∀ n, ret = lsstLSimMin c n m L h
  cost args _ := 40 * Nat.log 2 (16 * args.getD 0 0 + 6) + 100

theorem lsim_meetsContract {w c h : ℕ} {p : Program} {b bLog : ℕ}
    (hp : p.procs[b]? = some (lsimProc bLog c h))
    (hLog : MeetsContract w p bLog log2Contract) :
    MeetsContract w p b (lsimContract w c h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m, L, rfl, hm, hw16, hc, hh, hKw, hIn, hW⟩ := hpre
  have r0 : (startState [m, L] mem pos).regs 0 = m := rfl
  have r1 : (startState [m, L] mem pos).regs 1 = L := rfl
  have hl1 : Nat.log 2 (4 * m + 2) ≤ Nat.log 2 (16 * m + 6) := Nat.log_mono_right (by omega)
  have hK : kWidthOf m L = L + Nat.log 2 (4 * m + 2) + 3 := by unfold kWidthOf; omega
  have hW' : w'Max c 0 m L h = c * (Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3) := by
    unfold w'Max; rw [show 6 + 16 * m = 16 * m + 6 by omega]
  have hKh : kWidthOf m L * h < 2 ^ w := by omega
  have hW2 : c * (Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3) < 2 ^ w := hW' ▸ hW
  refine runs_start_le ?_
  unfold lsimProc
  refine runs_seq_call_le (vs := [4 * m + 2]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨4 * m + 2, rfl, by omega⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨x₁, hx₁, hm₁, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₁
  subst hx₁
  refine runs_seq_assign_le (v := kWidthOf m L) (by rw [hK]; eval_expr <;> omega) ?_
  refine runs_seq_call_le (vs := [16 * m + 6]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨16 * m + 6, rfl, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨x₂, hx₂, hm₂, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₂
  subst hx₂
  refine runs_seq_assign_le (v := w'Max c 0 m L h) (by rw [hW']; eval_expr <;> omega) ?_
  have e1 : ∀ n, w'Max c n m L h = c * (Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3) := by
    intro n; unfold w'Max; rw [show 6 + 16 * m = 16 * m + 6 by omega]
  refine runs_cond_le (by eval_expr) (fun hv => ?_) (fun hv => ?_)
  · refine runs_ret_le (by eval_expr) ?_ ?_
    · dsimp only
      subst hm₁ hm₂
      refine ⟨m, L, rfl, rfl, fun n => ?_⟩
      simp only [lsstLSimMin, Outcome.value, e1]
      by_cases hlt : L + Nat.log 2 (4 * m + 2) + 3 <
          c * (Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3)
      · rw [max_eq_right (by omega)]
      · simp [hlt] at hv
    · simp only [lsimContract, Expr.size, argsSize, List.getD_cons_zero, log2Contract,
        List.getD_cons_zero]
      omega
  · refine runs_ret_le (by eval_expr) ?_ ?_
    · dsimp only
      subst hm₁ hm₂
      refine ⟨m, L, rfl, rfl, fun n => ?_⟩
      simp only [lsstLSimMin, Outcome.value, e1]
      by_cases hlt : L + Nat.log 2 (4 * m + 2) + 3 <
          c * (Nat.log 2 (16 * m + 6) + kWidthOf m L * h + 3)
      · simp [hlt] at hv
      · rw [max_eq_left (by omega)]; omega
    · simp only [lsimContract, Expr.size, argsSize, List.getD_cons_zero, log2Contract,
        List.getD_cons_zero]
      omega

end

end MinCostFlow.LSF.Program
