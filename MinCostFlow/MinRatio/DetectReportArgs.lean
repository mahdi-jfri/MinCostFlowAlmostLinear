module

public import WordRAM.Logic

/-!
# Preparing the ready slot's report arguments

The proof of Theorem 5.1 (pages 29–30) resets the ready slot to the
negative of its threshold. A slot-indexed table gives the address
of that threshold. The replacement starts beyond the reserved
PointRead workspace.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Read the threshold pointer and select the end of the read
workspace. Registers 13 and 14 hold that end and the table base. -/
@[expose] def detectReportArgs : Stmt :=
  .assign 9 (.load (.bin .add (.reg 14) (.reg 3))) ;;
  .assign 11 (.reg 13)

/-- Preparing the two arguments contains no random statements. -/
theorem detectReportArgs_noRand : detectReportArgs.NoRand := by
  simp [detectReportArgs, Stmt.NoRand]

/-- The setup reads one table word and preserves the tree, report,
and all registers except the threshold address and heap arguments. -/
theorem detectReportArgs_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {table slot top : ℕ}
    (htableReg : st.regs 14 = table) (hslotReg : st.regs 3 = slot)
    (htopReg : st.regs 13 = top) (hword : table + slot < 2 ^ w) :
    ∃ out, Runs w p ω detectReportArgs st .normal out 8 ∧
      out.regs 9 = st.mem (table + slot) ∧ out.regs 11 = top ∧
      (∀ r, r ≠ 9 → r ≠ 11 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 9 (st.mem (table + slot)) }
  let out := { mid with regs := Function.update mid.regs 11 top }
  have hfirst : Runs w p ω (.assign 9 (.load (.bin .add (.reg 14) (.reg 3)))) st .normal mid 5 := by
    refine runs_assign_iff.mpr ⟨st.mem (table + slot), ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, htableReg, hslotReg, hword]
  have hsecond : Runs w p ω (.assign 11 (.reg 13)) mid .normal out 2 := by
    refine runs_assign_iff.mpr ⟨top, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, mid, Function.update_of_ne, htopReg]
  refine ⟨out, ?_, by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 5, 2, hfirst, hsecond, by decide⟩)
  · intro r h₉ h₁₁
    simp [out, mid, Function.update_of_ne, h₉, h₁₁]

/-- After a report, adopt its heap and advance the report cursor by one. -/
@[expose] def detectReportAdvance : Stmt :=
  .assign 1 (.reg 12) ;;
  .assign 8 (.bin .add (.reg 8) (.const 1))

/-- The loop advances without modifying the tree, its report, or the
registers that hold the table bases and other fixed parameters. -/
theorem detectReportAdvance_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {heap cursor : ℕ} (hh : st.regs 12 = heap) (hc : st.regs 8 = cursor)
    (hw : cursor + 1 < 2 ^ w) :
    ∃ out, Runs w p ω detectReportAdvance st .normal out 7 ∧
      out.regs 1 = heap ∧ out.regs 8 = cursor + 1 ∧
      (∀ r, r ≠ 1 → r ≠ 8 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 1 heap }
  let out := { mid with regs := Function.update mid.regs 8 (cursor + 1) }
  have hfirst : Runs w p ω (.assign 1 (.reg 12)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hone : 1 < 2 ^ w := (Nat.le_add_left _ _).trans_lt hw
  have hsecond : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨cursor + 1,
      by simp [Expr.eval, mid, Function.update_of_ne, hc, hone, hw], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r h₁ h₈
  simp [out, mid, Function.update_of_ne, h₁, h₈]

/-- Set the search and read workspace bounds from two reserved sizes. -/
@[expose] def detectWorkspaceArgs : Stmt :=
  .assign 4 (.bin .add (.reg 1) (.reg 15)) ;;
  .assign 13 (.bin .add (.reg 4) (.reg 16))

/-- Compute both workspace ends and keep the rest of the caller state. -/
theorem detectWorkspaceArgs_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {heap searchSpace readSpace : ℕ}
    (hh : st.regs 1 = heap) (hs : st.regs 15 = searchSpace) (hr : st.regs 16 = readSpace)
    (hw : heap + searchSpace + readSpace < 2 ^ w) :
    ∃ out, Runs w p ω detectWorkspaceArgs st .normal out 9 ∧
      out.regs 4 = heap + searchSpace ∧ out.regs 13 = heap + searchSpace + readSpace ∧
      (∀ r, r ≠ 4 → r ≠ 13 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 4 (heap + searchSpace) }
  let out := { mid with regs := Function.update mid.regs 13 (heap + searchSpace + readSpace) }
  have hsum : heap + searchSpace < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 4 (.bin .add (.reg 1) (.reg 15))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh, hs, hsum], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 13 (.bin .add (.reg 4) (.reg 16))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne, hr, hw], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r h₄ h₁₃
  simp [out, mid, Function.update_of_ne, h₄, h₁₃]

end MinCostFlow.MinRatio
