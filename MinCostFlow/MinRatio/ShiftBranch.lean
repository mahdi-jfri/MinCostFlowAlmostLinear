module

public import WordRAM.Logic

/-!
# Selecting the next branch for Shift

Algorithm 1 (page 20) advances the selected branch modulo the number
of branches. The restarted spanner and the next level both use this
new branch.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Register 0 addresses the branch cell and register 1 holds the
branch count. Leave the new branch in register 2 for the restart. -/
@[expose] def shiftBranch : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 2 (.bin .mod (.bin .add (.reg 2) (.const 1)) (.reg 1)) ;;
  .store (.reg 0) (.reg 2)

/-- The branch-advance instructions contain no randomness. -/
theorem shiftBranch_noRand : shiftBranch.NoRand := by
  simp [shiftBranch, Stmt.NoRand]

/-- The first step of Algorithm 1 Shift (page 20) updates one cell
and records the chosen branch for the upcoming restart call. -/
theorem shiftBranch_runs {w addr branch count : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (ha : st.regs 0 = addr) (hk : st.regs 1 = count)
    (hb : st.mem addr = branch) (hbranch : branch < count) (hword : count < 2 ^ w) :
    ∃ out, Runs w p ω shiftBranch st .normal out 14 ∧
      out.mem = Function.update st.mem addr ((branch + 1) % count) ∧
      out.regs 2 = (branch + 1) % count ∧
      (∀ r, r ≠ 2 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let first := { st with regs := Function.update st.regs 2 branch }
  let second := { first with regs := Function.update first.regs 2 ((branch + 1) % count) }
  let out := { second with mem := Function.update second.mem addr ((branch + 1) % count) }
  have hone : 1 < 2 ^ w := by omega
  have hsucc : branch + 1 < 2 ^ w := by omega
  have hmod : (branch + 1) % count < 2 ^ w :=
    (Nat.mod_lt _ (by omega)).trans hword
  have hfirst : Runs w p ω (.assign 2 (.load (.reg 0))) st .normal first 3 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, ha, hb], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω
      (.assign 2 (.bin .mod (.bin .add (.reg 2) (.const 1)) (.reg 1))) first .normal second 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, first, Function.update_of_ne, hk, hone, hsucc, hmod],
      rfl, rfl, rfl⟩
  have hstore : Runs w p ω (.store (.reg 0) (.reg 2)) second .normal out 3 :=
    runs_store_iff.mpr ⟨addr, _, by simp [Expr.eval, second, first, Function.update_of_ne, ha],
      by simp [Expr.eval, second], rfl, rfl, rfl⟩
  refine ⟨out, ?_, rfl, by simp [out, second], ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨first, 3, 10, hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second, 6, 3, hsecond, hstore, rfl⟩), rfl⟩)
  · intro r hr
    simp [out, second, first, Function.update_of_ne, hr]

end MinCostFlow.MinRatio
