module

public import MinCostFlow.LowStretch.ProgResetA
public import MinCostFlow.LowStretch.ProgChildOneB
public import MinCostFlow.LowStretch.ProgLog

/-!
# The reset of a child: the new threshold

The first six steps of `rsB` compute `S = max(Δ, μ, 4B|X|)` (two saturating steps), the quotient
`S / 4B|X|`, its logarithm (`log2P`) and the new threshold `x = 2 ^ log₂ (S / 4B|X|)`
(`rsThr_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace RsV

variable (V : RsV)

/-- The size `S = max(Δ, μ, 4B|X|)` of the reset rule. -/
def S : ℕ := max (max V.Δ V.μ) (4 * V.B * V.sz)

/-- The logarithm of the new threshold. -/
def lx : ℕ := Nat.log 2 (V.S / (4 * V.B * V.sz))

/-- The new threshold. -/
def x : ℕ := 2 ^ V.lx

theorem x_le_S (h : 1 ≤ 4 * V.B * V.sz) : V.x ≤ V.S := by
  have h1 : V.x ≤ V.S / (4 * V.B * V.sz) := Nat.pow_log_le_self 2 (by
    have : 4 * V.B * V.sz ≤ V.S := le_max_right _ _
    exact (Nat.div_pos this (by omega)).ne')
  exact h1.trans (Nat.div_le_self _ _)

end RsV

/-- **The new threshold.** From the registers after the loads, the six steps put `log₂ (S / 4B|X|)`
in register `36` and the threshold `x` in register `37`. -/
theorem rsThr_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {V : RsV} {st : State}
    (flg : MeetsContract w p I.lg (log2C w)) (hR : V.Regs st)
    (hΔ : V.Δ < 2 ^ w) (hμ : V.μ < 2 ^ w) (hb : 4 * V.B * V.sz < 2 ^ w)
    (hb1 : 1 ≤ 4 * V.B * V.sz) (hw : 2 ≤ w) {s : Stmt} {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ st' : State, st'.mem = st.mem → (∀ r < 33, st'.regs r = st.regs r) →
      st'.regs 33 = 4 * V.B * V.sz → st'.regs 36 = V.lx → st'.regs 37 = V.x →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧
        k + 100 + log2Cost (V.S / (4 * V.B * V.sz)) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.seq (.assign 33 (.bin .mul (mulC 4 13) (.reg 4)))
      (.seq (.assign 34 (.bin .add (.reg 3) (.bin .sub (.reg 5) (.reg 3))))
      (.seq (.assign 34 (.bin .add (.reg 34) (.bin .sub (.reg 33) (.reg 34))))
      (.seq (.assign 35 (.bin .div (.reg 34) (.reg 33)))
      (.seq (.call 36 I.lg (rgs [35]))
      (.seq (.assign 37 (.bin .shiftLeft (.const 1) (.reg 36))) s))))))
      st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have h3 : st.regs 3 = V.Δ := hR 3 (by norm_num)
  have h4 : st.regs 4 = V.sz := hR 4 (by norm_num)
  have h5 : st.regs 5 = V.μ := hR 5 (by norm_num)
  have h13 : st.regs 13 = V.B := hR 13 (by norm_num)
  have hS : V.S < 2 ^ w := by unfold RsV.S; omega
  have hS1 : 4 * V.B * V.sz ≤ V.S := le_max_right _ _
  have hS2 : V.S = V.Δ + (V.μ - V.Δ) + (4 * V.B * V.sz - (V.Δ + (V.μ - V.Δ))) := by
    unfold RsV.S; omega
  have hB4 : 4 * V.B < 2 ^ w := by
    have : 4 * V.B ≤ 4 * V.B * V.sz := Nat.le_mul_of_pos_right _ (by
      rcases Nat.eq_zero_or_pos V.sz with h | h
      · rw [h] at hb1; simp at hb1
      · exact h)
    omega
  have h4w : 4 < 2 ^ w := by
    rcases Nat.eq_zero_or_pos V.B with h | h
    · rw [h] at hb1; simp at hb1
    · omega
  refine runs_seq_assign_le (v := 4 * V.B * V.sz) (by unfold mulC; eval_expr) ?_
  refine runs_seq_assign_le (v := V.Δ + (V.μ - V.Δ)) (by eval_expr) ?_
  refine runs_seq_assign_le (v := V.S) (by rw [hS2]; eval_expr) ?_
  have hq : 1 ≤ V.S / (4 * V.B * V.sz) := (Nat.one_le_div_iff (by omega)).mpr hS1
  have hql : V.S / (4 * V.B * V.sz) < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hS
  refine runs_seq_assign_le (v := V.S / (4 * V.B * V.sz)) (by eval_expr) ?_
  refine runs_seq_callR_le (vs := [V.S / (4 * V.B * V.sz)]) flg (by simp) (by simpa using hql)
    ⟨_, rfl, hq, hql, hw⟩ ?_
  intro v M' q hpost
  obtain ⟨hv, hM'⟩ := hpost
  simp only [List.getD_cons_zero] at hv
  have hx : V.x < 2 ^ w := lt_of_le_of_lt (V.x_le_S hb1) hS
  have hsh : 1 <<< V.lx = V.x := by rw [Nat.shiftLeft_eq, one_mul]; rfl
  refine runs_seq_assign_le (v := V.x) (by
    rw [← hsh]
    exact Expr.eval_shiftLeft (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp [hv]; rfl)) (by rw [hsh]; exact hx)) ?_
  refine runs_exists_mono (hrest _ (by simp [hM']) (fun r hr => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
    (by simp) (by simp [hv]; rfl) (by simp)) ?_
  simp only [Expr.size, mulC, List.length_cons, List.length_nil, log2C, List.getD_cons_zero]
  omega

end MinCostFlow.LowStretch
