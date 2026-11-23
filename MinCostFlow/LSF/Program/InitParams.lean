module

public import MinCostFlow.LSF.Program.DecompDegSpec
public import MinCostFlow.LSF.Program.Layout

/-!
# Three numbers the init driver needs

The passes of the initialization take three numbers that depend on `n = |V(G₀)|` and on `k`: the
depth bound `D = hldDepthBound n` of `T_H` (for the upward closure), the number of levels
`logCap = auxLogCap n` of the binary-lifting tables, and the weight threshold
`θ = 4 k (D + 1)` of the decomposition `W_T` (`decompThetaNat`). `initParamsProc` computes them
with two calls of `log2Stmt` and writes them at `outPtr`, `outPtr + 1`, `outPtr + 2`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- Args: `[n, k, outPtr]`. Registers: `3 = log n`, `4 = log (n + 1)`, `5 = D`. -/
def initParamsProc (bLog : ℕ) : Stmt :=
  .call 3 bLog [.reg 0] ;;
  .call 4 bLog [.bin .add (.reg 0) (.const 1)] ;;
  .assign 5 (.bin .mul (.bin .add (.reg 3) (.const 1)) (.bin .add (.reg 3) (.const 2))) ;;
  .store (.reg 2) (.reg 5) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 4) (.const 1)) ;;
  .store (.bin .add (.reg 2) (.const 2))
    (.bin .mul (.bin .mul (.const 4) (.reg 1)) (.bin .add (.reg 5) (.const 1))) ;;
  .ret (.const 0)

lemma initParamsProc_noRand (bLog : ℕ) : (initParamsProc bLog).NoRand := by
  simp [initParamsProc, Stmt.NoRand]

/-- The contract of `initParamsProc`. -/
def initParamsContract (w : ℕ) : Contract where
  pre args _ := ∃ n k outPtr, args = [n, k, outPtr] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ n ∧ 1 ≤ k ∧
    n + 1 < 2 ^ w ∧ outPtr + 3 < 2 ^ w ∧ 3 * (4 * k * (hldDepthBound n + 1)) < 2 ^ w
  post args mem ret mem' := ∃ n k outPtr, args = [n, k, outPtr] ∧ ret = 0 ∧
    mem' outPtr = hldDepthBound n ∧ mem' (outPtr + 1) = auxLogCap n ∧
    mem' (outPtr + 2) = 4 * k * (hldDepthBound n + 1) ∧
    ∀ a, a < outPtr ∨ outPtr + 3 ≤ a → mem' a = mem a
  cost args _ := 20 * Nat.log 2 (args.getD 0 0) + 20 * Nat.log 2 (args.getD 0 0 + 1) + 100

/-- The weight threshold of `W_T` is the third number. -/
lemma decompThetaNat_eq (G₀ : MGraph) (k : ℕ) :
    decompThetaNat G₀ k = 4 * k * (hldDepthBound G₀.n + 1) := rfl

theorem initParams_meetsContract {w : ℕ} {p : Program} {b bLog : ℕ}
    (hp : p.procs[b]? = some (initParamsProc bLog))
    (hLog : MeetsContract w p bLog log2Contract) :
    MeetsContract w p b (initParamsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, k, outPtr, rfl, hw16, hn, hk, hnw, how, hθ⟩ := hpre
  have r0 : (startState [n, k, outPtr] mem pos).regs 0 = n := rfl
  have r1 : (startState [n, k, outPtr] mem pos).regs 1 = k := rfl
  have r2 : (startState [n, k, outPtr] mem pos).regs 2 = outPtr := rfl
  have hD : hldDepthBound n + 1 ≤ 4 * k * (hldDepthBound n + 1) := by
    have : 1 ≤ 4 * k := by omega
    nlinarith
  have hDw : hldDepthBound n + 1 < 2 ^ w := by omega
  have h4k : 4 * k ≤ 4 * k * (hldDepthBound n + 1) := Nat.le_mul_of_pos_right (4 * k) (Nat.succ_pos _)
  have hLn : Nat.log 2 n + 2 ≤ hldDepthBound n := by
    unfold hldDepthBound; nlinarith
  have hL1 : Nat.log 2 (n + 1) ≤ n := Nat.lt_succ_iff.mp (Nat.log_lt_self 2 (by omega))
  refine runs_start_le ?_
  unfold initParamsProc
  refine runs_seq_call_le (vs := [n]) hLog (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    (by intro v hv; simp at hv; subst hv; omega) ⟨n, rfl, hn⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨x₁, heq₁, hm₁, hv₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  subst heq₁ hm₁ hv₁
  refine runs_seq_call_le (vs := [n + 1]) hLog (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    (by intro v hv; simp at hv; subst hv; omega) ⟨n + 1, rfl, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨x₂, heq₂, hm₂, hv₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  subst heq₂ hm₂ hv₂
  have hDdef : (Nat.log 2 n + 1) * (Nat.log 2 n + 2) = hldDepthBound n := rfl
  have hprod : (Nat.log 2 n + 1) * (Nat.log 2 n + 2) < 2 ^ w := by rw [hDdef]; omega
  have hθ' : 4 * k * ((Nat.log 2 n + 1) * (Nat.log 2 n + 2) + 1) < 2 ^ w := by rw [hDdef]; omega
  have h4kw : 4 * k < 2 ^ w := by omega
  refine runs_seq_assign_le (v := (Nat.log 2 n + 1) * (Nat.log 2 n + 2)) (by eval_expr <;> omega) ?_
  refine runs_seq_store_le (x := outPtr) (v := (Nat.log 2 n + 1) * (Nat.log 2 n + 2))
    (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + 1) (v := auxLogCap n) (by eval_expr)
    (by unfold auxLogCap; eval_expr <;> omega) ?_
  refine runs_seq_store_le (x := outPtr + 2)
    (v := 4 * k * ((Nat.log 2 n + 1) * (Nat.log 2 n + 2) + 1)) (by eval_expr)
    (by eval_expr <;> omega) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, k, outPtr, rfl, rfl, ?_, ?_, ?_, fun a ha => ?_⟩ ?_
  · simp [Function.update_apply, hDdef]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hDdef]
  · simp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  · simp only [initParamsContract, List.getD_cons_zero, argsSize, Expr.size_const, Expr.size_reg,
      Expr.size_bin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, log2Contract,
      List.getD_cons_zero]
    omega

end

end MinCostFlow.LSF.Program
