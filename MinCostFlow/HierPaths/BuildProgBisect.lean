module

public import MinCostFlow.HierPaths.BuildProgBisectMath
public import WordRAM.Tactic

/-!
# Padding the smaller side in the game round

The scan takes a membership bit per child vertex. It sets the bits of the first
missing vertices until the smaller side has reached half the child size.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The address of vertex `r3` in the mask starting at `r0`. -/
def buildCutBitAddr : Expr := .bin .add (.reg 0) (.reg 3)

/-- Read the old bit, write its disjunction with the quota test, and decrement the
quota only if the vertex was outside the smaller side. -/
def buildPadStep : Stmt :=
  .seq (.assign 4 (.load buildCutBitAddr))
    (.seq (.store buildCutBitAddr (.bin .or (.reg 4) (.bin .lt (.const 0) (.reg 2))))
      (.assign 2 (.bin .sub (.reg 2) (.bin .sub (.const 1) (.reg 4)))))

/-- Args are the mask base, the child size, and the initial padding quota. -/
def buildPadHalfProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1) buildPadStep) (.ret (.const 0))

/-- The procedure changes the mask of the smaller side to that of the padded side. -/
def buildPadHalfContract (w s : ℕ) (C : Finset ℕ) : Contract where
  pre args mem := ∃ base, args = [base, s, s / 2 - C.card] ∧ base + s < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ i < s, mem (base + i) = if i ∈ C then 1 else 0
  post args mem _ mem' := ∃ base, args = [base, s, s / 2 - C.card] ∧
    (∀ i < s, mem' (base + i) = if i ∈ padHalf s C then 1 else 0) ∧
    ∀ j, (j < base ∨ base + s ≤ j) → mem' j = mem j
  cost _ _ := 40 * s + 12

theorem buildPadHalfProc_noRand : buildPadHalfProc.NoRand := by
  simp [buildPadHalfProc, buildPadStep, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private def padInv (mem : ℕ → ℕ) (base s : ℕ) (C : Finset ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 1 = s ∧ st.regs 2 = cutQuota s C i ∧ st.regs 3 = i ∧
  (∀ j < i, st.mem (base + j) = if j ∈ padHalf s C then 1 else 0) ∧
  (∀ j, (j < base ∨ base + i ≤ j) → st.mem j = mem j)

private theorem buildPad_step {w base s i : ℕ} {C : Finset ℕ} {mem : ℕ → ℕ} (p : Program)
    (hs : base + s < 2 ^ w) (hw : 1 < 2 ^ w) (hi : i < s)
    (hBits : ∀ j < s, mem (base + j) = if j ∈ C then 1 else 0) :
    Triple w p (padInv mem base s C i) buildPadStep
      (normalPost fun st => padInv mem base s C (i + 1) { st with regs := Function.update st.regs 3 (i + 1) }
        ∧ st.regs 3 = i) (fun _ => 28) := by
  intro st ω ⟨h0, h1, h2, h3, hWritten, hFrame⟩
  have hAddr : base + i < 2 ^ w := by omega
  have hQuota : cutQuota s C i < 2 ^ w := by
    have hq : cutQuota s C i ≤ s := (Nat.sub_le ..).trans
      ((Nat.sub_le ..).trans (Nat.div_le_self ..))
    omega
  have hOld : st.mem (base + i) = if i ∈ C then 1 else 0 :=
    (hFrame _ (Or.inr (Nat.le_refl _))).trans (hBits i hi)
  refine runs_start_le ?_
  unfold buildPadStep
  refine runs_seq_assign_le (v := if i ∈ C then 1 else 0) ?_ ?_
  · simp [Expr.eval, buildCutBitAddr, h0, h3, hAddr, hOld]
  let bit := if i ∈ padHalf s C then 1 else 0
  refine runs_seq_store_le (x := base + i) (v := bit) ?_ ?_ ?_
  · simp [Expr.eval, buildCutBitAddr, Function.update, h0, h3, hAddr]
  · rw [show bit = (if i ∈ C ∨ 0 < cutQuota s C i then 1 else 0) by
      simp only [bit, mem_padHalf_iff_quota hi]]
    by_cases hC : i ∈ C <;> by_cases hq : 0 < cutQuota s C i <;>
      simp [Expr.eval, Function.update, h2, hC, hq, hw]
  refine runs_assign_le (v := cutQuota s C (i + 1)) ?_ ?_ ?_
  · rw [cutQuota_succ]
    have hSub : cutQuota s C i - 1 < 2 ^ w := (Nat.sub_le ..).trans_lt hQuota
    by_cases hC : i ∈ C <;>
      simp [Expr.eval, Function.update, h2, hC, hw, hQuota, hSub]
  · refine ⟨⟨by simpa using h0, by simpa using h1, by simp, by simp, ?_, ?_⟩, by simpa using h3⟩
    · intro j hj
      change Function.update st.mem (base + i) bit (base + j) = _
      by_cases hji : j = i
      · subst j
        simp [bit]
      · rw [Function.update_of_ne (by omega)]
        exact hWritten j (by omega)
    · intro j hj
      change Function.update st.mem (base + i) bit j = mem j
      rw [Function.update_of_ne (by omega)]
      exact hFrame j (by omega)
  · simp [buildCutBitAddr, Expr.size]

/-- The linear scan pads the smaller side as in the child game model. -/
theorem buildPadHalfProc_meetsContract {w s : ℕ} {C : Finset ℕ} {p : Program} {f : ℕ}
    (hf : p.procs[f]? = some buildPadHalfProc) :
    MeetsContract w p f (buildPadHalfContract w s C) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨base, rfl, hs, hw, hBits⟩ := hPre
  have hLoop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := buildPadStep) (P := fun st => st = startState [base, s, s / 2 - C.card] mem pos)
    (Inv := padInv mem base s C) 28 0 s (Nat.zero_le _) hw (fun _ => by omega)
    (fun st h => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _), ?_⟩
      exact ⟨rfl, rfl, (cutQuota_zero ..).symm, rfl,
        fun j hj => False.elim (Nat.not_lt_zero j hj), fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun i _ hi => buildPad_step p hs hw hi hBits)
  refine runs_start_le ?_
  unfold buildPadHalfProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st hInv
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨base, rfl, hInv.2.2.2.2.1, hInv.2.2.2.2.2⟩ ?_
  simp [buildPadHalfContract, Expr.size]
  omega

end MinCostFlow.HierPaths
