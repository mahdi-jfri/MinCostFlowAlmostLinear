module

public import MinCostFlow.LSF.Program.Utils

/-!
# The block width of the stretch pass

`wstrProc` works with blocks of `LB` limbs. Its sums are weighted depths times `2 (D + 1)`, with
`D = hldDepthBound n`, so `LB` must exceed the width `L_w` of the stretch arrays by about
`log₂ n + log₂ D` bits. `wstrLBProc` computes `wstrLB n D L_w = L_w + log₂ (n + 1) + log₂ (D + 2) + 6`
at run time and returns it, so that a call sequence can pass it on in a register. `wstrLB_cap` gives the bound that the stretch pass needs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- The block width of the stretch pass. -/
def wstrLB (n D Lw : ℕ) : ℕ := Lw + Nat.log 2 (n + 1) + Nat.log 2 (D + 2) + 6

/-- Args: `[n, D, Lw]`. Returns `wstrLB n D Lw`. -/
def wstrLBProc (bLog : ℕ) : Stmt :=
  .call 4 bLog [.bin .add (.reg 0) (.const 1)] ;;
  .call 5 bLog [.bin .add (.reg 1) (.const 2)] ;;
  .ret (.bin .add (.bin .add (.bin .add (.reg 2) (.reg 4)) (.reg 5)) (.const 6))

lemma wstrLBProc_noRand (bLog : ℕ) : (wstrLBProc bLog).NoRand := by
  simp [wstrLBProc, Stmt.NoRand]

/-- The contract of `wstrLBProc`. -/
def wstrLBContract (w : ℕ) : Contract where
  pre args _ := ∃ n D Lw, args = [n, D, Lw] ∧ 16 ≤ 2 ^ w ∧
    n + 1 < 2 ^ w ∧ D + 2 < 2 ^ w ∧ wstrLB n D Lw < 2 ^ w
  post args mem ret mem' := ∃ n D Lw, args = [n, D, Lw] ∧ ret = wstrLB n D Lw ∧ mem' = mem
  cost args _ := 20 * Nat.log 2 (args.getD 0 0 + 1) + 20 * Nat.log 2 (args.getD 1 0 + 2) + 100

/-- With `1 ≤ h`, a block of `wstrLB n D Lw` limbs holds `16 (n + 1) (D + 2)` numbers below
`2 ^ (h Lw)`. -/
lemma wstrLB_cap {h n D Lw : ℕ} (hh : 1 ≤ h) :
    16 * (n + 1) * (D + 2) * 2 ^ (h * Lw) ≤ 2 ^ (h * wstrLB n D Lw) := by
  have hn := Nat.lt_pow_succ_log_self (b := 2) (by decide) (n + 1)
  have hD := Nat.lt_pow_succ_log_self (b := 2) (by decide) (D + 2)
  have hsplit : h * wstrLB n D Lw =
      h * Lw + h * ((Nat.log 2 (n + 1) + 1) + (Nat.log 2 (D + 2) + 1) + 4) := by
    unfold wstrLB; ring
  have hle : (Nat.log 2 (n + 1) + 1) + (Nat.log 2 (D + 2) + 1) + 4 ≤
      h * ((Nat.log 2 (n + 1) + 1) + (Nat.log 2 (D + 2) + 1) + 4) := Nat.le_mul_of_pos_left _ hh
  calc 16 * (n + 1) * (D + 2) * 2 ^ (h * Lw)
      ≤ 2 ^ 4 * 2 ^ (Nat.log 2 (n + 1) + 1) * 2 ^ (Nat.log 2 (D + 2) + 1) * 2 ^ (h * Lw) := by
        gcongr
        all_goals first | norm_num | exact hn.le | exact hD.le
    _ = 2 ^ ((Nat.log 2 (n + 1) + 1) + (Nat.log 2 (D + 2) + 1) + 4) * 2 ^ (h * Lw) := by
        rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ (h * ((Nat.log 2 (n + 1) + 1) + (Nat.log 2 (D + 2) + 1) + 4)) * 2 ^ (h * Lw) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hle)
    _ = 2 ^ (h * wstrLB n D Lw) := by rw [hsplit, pow_add, mul_comm]

theorem wstrLB_meetsContract {w : ℕ} {p : Program} {b bLog : ℕ}
    (hp : p.procs[b]? = some (wstrLBProc bLog))
    (hLog : MeetsContract w p bLog log2Contract) :
    MeetsContract w p b (wstrLBContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, D, Lw, rfl, hw16, hn, hD, hLB⟩ := hpre
  have r0 : (startState [n, D, Lw] mem pos).regs 0 = n := rfl
  have r1 : (startState [n, D, Lw] mem pos).regs 1 = D := rfl
  have r2 : (startState [n, D, Lw] mem pos).regs 2 = Lw := rfl
  have hLB' : wstrLB n D Lw = Lw + Nat.log 2 (n + 1) + Nat.log 2 (D + 2) + 6 := rfl
  refine runs_start_le ?_
  unfold wstrLBProc
  refine runs_seq_call_le (vs := [n + 1]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨n + 1, rfl, by omega⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨x₁, hx₁, hm₁, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₁
  subst hx₁
  try dsimp only at hm₁
  subst hm₁
  refine runs_seq_call_le (vs := [D + 2]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨D + 2, rfl, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨x₂, hx₂, hm₂, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₂
  subst hx₂
  try dsimp only at hm₂
  subst hm₂
  refine runs_ret_le (v := wstrLB n D Lw) (by rw [hLB']; eval_expr <;> omega)
    ⟨n, D, Lw, rfl, rfl, rfl⟩ ?_
  simp only [wstrLBContract, Expr.size, argsSize, log2Contract, List.getD_cons_zero,
    List.getD_cons_succ]
  omega

end

end MinCostFlow.LSF.Program
