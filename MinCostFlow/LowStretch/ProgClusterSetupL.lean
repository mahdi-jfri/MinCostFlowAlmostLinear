module

public import MinCostFlow.LowStretch.ProgClusterSetupPre

/-!
# The setup of a cluster: the number of buckets

`setupP` computes `L = pL n` with two calls of `log2P`: register `26` gets `⌊log₂ (n + 2)⌋`,
register `27` gets `⌊log₂ (2 r₂₆ + 4)⌋`, and register `28` gets `r₂₇ + 1`. Since
`pa n = ⌊log₂ (n + 2)⌋ + 1`, the value `2 r₂₆ + 4` is `2 pa n + 2`, so `r₂₈ = pL n`
(`suL_runs`). Each call costs `O(log log n)`, at most `50 (pL n + 2)`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The first part of `suB`: the two calls of `log2P` and the assignment of `L`. -/
def suLog (I : SuIdx) (s : Stmt) : Stmt :=
  .seq (.call 26 I.lg [.bin .add (.reg 3) (.const 2)])
  (.seq (.call 27 I.lg [.bin .add (mulC 2 26) (.const 4)])
  (.seq (.assign 28 (.bin .add (.reg 27) (.const 1))) s))

theorem suB_eq (I : SuIdx) : suB I = suLog I (.seq (.call 23 I.dr [.reg 13, .reg 14, .reg 15,
    .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, suDc, .reg 16, .reg 17, .reg 11, .reg 12, .reg 21])
    (suMid I)) := rfl

/-- `log₂ (pa n) + 2 ≤ pL n`, so the first call costs at most `50 pL n`. -/
theorem log_pa_le (n : ℕ) : Nat.log 2 (Nat.log 2 (n + 2) + 1) + 2 ≤ pL n := by
  unfold pL pa
  have h1 : 2 ^ Nat.log 2 (Nat.log 2 (n + 2) + 1) ≤ Nat.log 2 (n + 2) + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (Nat.log 2 (Nat.log 2 (n + 2) + 1) + 1) ≤ 2 * (Nat.log 2 (n + 2) + 1) + 2 := by
    rw [pow_succ]; omega
  have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2
  omega

/-- **The number of buckets.** From registers that hold the loads of `V`, the two calls of
`log2P` and the assignment leave `pL n` in register `28`, at a cost of at most
`100 pL n + 200`. -/
theorem two_mul_le_two_pow_add (k : ℕ) : 2 * k ≤ 2 ^ k + 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]; omega

/-- `2 log₂ x ≤ x + 2`. -/
theorem two_mul_log_le (x : ℕ) : 2 * Nat.log 2 x ≤ x + 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    have := two_mul_le_two_pow_add (Nat.log 2 x)
    omega

theorem evalArgs_one {w : ℕ} {st : State} {e : Expr} {v : ℕ} (he : e.eval w st = some v) :
    evalArgs w st [e] = some [v] := by
  simp [evalArgs, he]

theorem suL_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hLg : MeetsContract w p I.lg (log2C w)) {V : SuV} {st : State} (hR : V.Regs st)
    (hw : 2 ≤ w) (hn : V.n + 2 ^ 20 < 2 ^ w) {s : Stmt} {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ st' : State, V.Regs st' → st'.mem = st.mem → st'.regs 28 = pL V.n →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ k + 100 * pL V.n + 200 + c ≤ T) :
    ∃ o st' c, Runs w p ω (suLog I s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have h3 : st.regs 3 = V.n := hR 3 (by norm_num)
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have hl1 := two_mul_log_le (V.n + 2)
  have hl2 : Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4) ≤ 2 * Nat.log 2 (V.n + 2) + 4 :=
    Nat.log_le_self 2 _
  have hpL : Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4) + 1 = pL V.n := by
    unfold pL pa; congr 2
  have c1 := log_pa_le V.n
  have c2 : Nat.log 2 (Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4) + 1) ≤ pL V.n := by
    rw [hpL]; exact Nat.log_le_self 2 _
  refine runs_seq_call_le hLg (vs := [V.n + 2])
    (evalArgs_one (Expr.eval_add (Expr.eval_reg_of_eq h3) (Expr.eval_const (by omega))
      (by omega))) (by simp; omega) ⟨_, rfl, by omega, by omega, hw⟩
    (fun v1 mem1 pos1 hp1 => ?_)
  obtain ⟨hv1, hm1⟩ := hp1
  change v1 = Nat.log 2 (V.n + 2) at hv1
  subst hv1 hm1
  refine runs_seq_call_le hLg (vs := [2 * Nat.log 2 (V.n + 2) + 4])
    (evalArgs_one (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (v := Nat.log 2 (V.n + 2)) (by simp)) (by omega))
      (Expr.eval_const (by omega)) (by omega)))
    (by simp; omega) ⟨_, rfl, by omega, by omega, hw⟩ (fun v2 mem2 pos2 hp2 => ?_)
  obtain ⟨hv2, hm2⟩ := hp2
  change v2 = Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4) at hv2
  subst hv2 hm2
  refine runs_seq_assign_le (Expr.eval_add
    (Expr.eval_reg_of_eq (v := Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4)) (by simp))
    (Expr.eval_const (by omega)) (by omega)) ?_
  obtain ⟨o, st', c, h1, h2, h4⟩ := hrest ⟨st.mem, Function.update (Function.update
      (Function.update st.regs 26 (Nat.log 2 (V.n + 2))) 27
      (Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4))) 28
      (Nat.log 2 (2 * Nat.log 2 (V.n + 2) + 4) + 1), pos2⟩
    (fun r hr => by
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hR r hr) rfl
    (by simp only [Function.update_self]; exact hpL)
  refine ⟨o, st', c, h1, h2, ?_⟩
  simp only [log2C, log2Cost, argsSize, Expr.size, mulC, List.getD_cons_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

end MinCostFlow.LowStretch
