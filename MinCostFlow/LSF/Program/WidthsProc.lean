module

public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.Machine.WideWord.LSSTWeightsBase

/-!
# The limb widths of the tree phase

The copies use blocks of `K_w = kWidthOf m0 L_in` limbs, the numbers `q_nat` use `K_q = K_w + 6`
limbs, and the order `π` sums `m0` numbers of `K_q` limbs in blocks of `K` limbs. `widthsProc`
computes the three widths at run time and writes them to memory. The width `K` is
`K_q + log₂ (m0 + 1) + 1`, so a sum of `m0` numbers below `2 ^ (h K_q)` is below `2 ^ (h K)`
(`widthK_sum_lt`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.WideWord

@[expose] public section

/-- The width of the sums of `m0` numbers of `K_q` limbs. -/
def widthK (m0 L_in : ℕ) : ℕ := kWidthOf m0 L_in + 6 + Nat.log 2 (m0 + 1) + 1

/-- Args: `[m0, L_in, outPtr]`. Writes `K_w`, `K_q`, `K` at `outPtr`, `outPtr + 1`, `outPtr + 2`. -/
def widthsProc (bLog : ℕ) : Stmt :=
  .call 3 bLog [.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 2)] ;;
  .assign 4 (.bin .add (.bin .add (.reg 1) (.reg 3)) (.const 3)) ;;
  .store (.reg 2) (.reg 4) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 4) (.const 6)) ;;
  .call 5 bLog [.bin .add (.reg 0) (.const 1)] ;;
  .store (.bin .add (.reg 2) (.const 2))
    (.bin .add (.bin .add (.bin .add (.reg 4) (.const 6)) (.reg 5)) (.const 1)) ;;
  .ret (.const 0)

lemma widthsProc_noRand (bLog : ℕ) : (widthsProc bLog).NoRand := by
  simp [widthsProc, Stmt.NoRand]

/-- The contract of `widthsProc`. -/
def widthsContract (w : ℕ) : Contract where
  pre args _ := ∃ m0 L_in outPtr, args = [m0, L_in, outPtr] ∧ 16 ≤ 2 ^ w ∧
    4 * m0 + 2 < 2 ^ w ∧ outPtr + 2 < 2 ^ w ∧ widthK m0 L_in < 2 ^ w
  post args mem ret mem' := ∃ m0 L_in outPtr, args = [m0, L_in, outPtr] ∧ ret = 0 ∧
    mem' outPtr = kWidthOf m0 L_in ∧ mem' (outPtr + 1) = kWidthOf m0 L_in + 6 ∧
    mem' (outPtr + 2) = widthK m0 L_in ∧
    ∀ a, a < outPtr ∨ outPtr + 3 ≤ a → mem' a = mem a
  cost args _ := 20 * Nat.log 2 (4 * args.getD 0 0 + 2) + 20 * Nat.log 2 (args.getD 0 0 + 1) + 100

/-- A sum of `m0` numbers below `2 ^ (h K_q)` is below `2 ^ (h K)`, when `1 ≤ h`. -/
lemma widthK_sum_lt {h m0 L_in : ℕ} (hh : 1 ≤ h) {f : ℕ → ℕ}
    (hf : ∀ t < m0, f t < 2 ^ (h * (kWidthOf m0 L_in + 6))) :
    ∑ t ∈ Finset.range m0, f t < 2 ^ (h * widthK m0 L_in) := by
  set Kq := kWidthOf m0 L_in + 6
  have hsum : ∑ t ∈ Finset.range m0, f t ≤ m0 * 2 ^ (h * Kq) := by
    calc ∑ t ∈ Finset.range m0, f t ≤ ∑ _t ∈ Finset.range m0, 2 ^ (h * Kq) :=
          Finset.sum_le_sum fun t ht => (hf t (Finset.mem_range.mp ht)).le
      _ = m0 * 2 ^ (h * Kq) := by simp
  have hm : m0 < 2 ^ (Nat.log 2 (m0 + 1) + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (m0 + 1)
    omega
  have hpow : 2 ^ (Nat.log 2 (m0 + 1) + 1) ≤ 2 ^ (h * (Nat.log 2 (m0 + 1) + 1)) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ hh)
  have hK : h * widthK m0 L_in = h * Kq + h * (Nat.log 2 (m0 + 1) + 1) := by
    unfold widthK; ring
  rw [hK, pow_add]
  calc ∑ t ∈ Finset.range m0, f t ≤ m0 * 2 ^ (h * Kq) := hsum
    _ < 2 ^ (h * (Nat.log 2 (m0 + 1) + 1)) * 2 ^ (h * Kq) := by
        apply Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
    _ = 2 ^ (h * Kq) * 2 ^ (h * (Nat.log 2 (m0 + 1) + 1)) := by ring

theorem widths_meetsContract {w : ℕ} {p : Program} {b bLog : ℕ}
    (hp : p.procs[b]? = some (widthsProc bLog))
    (hLog : MeetsContract w p bLog log2Contract) :
    MeetsContract w p b (widthsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, L_in, outPtr, rfl, hw16, hm, hout, hK⟩ := hpre
  have r0 : (startState [m0, L_in, outPtr] mem pos).regs 0 = m0 := rfl
  have r1 : (startState [m0, L_in, outPtr] mem pos).regs 1 = L_in := rfl
  have r2 : (startState [m0, L_in, outPtr] mem pos).regs 2 = outPtr := rfl
  have hKw : kWidthOf m0 L_in = L_in + Nat.log 2 (4 * m0 + 2) + 3 := by unfold kWidthOf; omega
  have hKK : widthK m0 L_in = kWidthOf m0 L_in + 6 + Nat.log 2 (m0 + 1) + 1 := rfl
  refine runs_start_le ?_
  unfold widthsProc
  refine runs_seq_call_le (vs := [4 * m0 + 2]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨4 * m0 + 2, rfl, by omega⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨x₁, hx₁, hm₁, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₁
  subst hx₁
  try dsimp only at hm₁
  subst hm₁
  refine runs_seq_assign_le (v := kWidthOf m0 L_in) (by rw [hKw]; eval_expr <;> omega) ?_
  refine runs_seq_store_le (x := outPtr) (v := kWidthOf m0 L_in) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + 1) (v := kWidthOf m0 L_in + 6)
    (by eval_expr <;> omega) (by eval_expr <;> omega) ?_
  have hm1 : m0 + 1 < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [m0 + 1]) hLog
    (evalArgs_cons (by eval_expr <;> omega) (evalArgs_nil _ _))
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; omega)
    ⟨m0 + 1, rfl, by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨x₂, hx₂, hm₂, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₂
  subst hx₂
  try dsimp only at hm₂
  subst hm₂
  refine runs_seq_store_le (x := outPtr + 2) (v := widthK m0 L_in)
    (by eval_expr <;> omega) (by rw [hKK]; eval_expr <;> omega) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, L_in, outPtr, rfl, rfl, ?_, ?_, ?_, ?_⟩ ?_
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · intro a ha
    simp only [Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp only [widthsContract, Expr.size, argsSize, log2Contract, List.getD_cons_zero]
    omega

end

end MinCostFlow.LSF.Program
