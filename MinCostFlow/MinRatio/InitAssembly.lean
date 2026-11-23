module

public import MinCostFlow.MinRatio.InitParameterEntry

/-!
# Init graph metadata

Read the vertex bound and capacities of the packed Init graph.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Read the vertex bound and graph capacities from the packed Init
graph in register 69. These words are used by the per-level layouts. -/
@[expose] def loadMinRatioInitGraphSizes : Stmt :=
  .assign 92 (.load (.bin .add (.reg 69) (.const 2))) ;;
  .assign 93 (.load (.reg 69)) ;;
  .assign 94 (.load (.bin .add (.reg 69) (.const 1)))

/-- The graph metadata loads preserve the prepared Init parameters
and read the capacities of the actual graph layout. -/
theorem loadMinRatioInitGraphSizes_runs {w graph vc ec : ℕ} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hg : st.regs 69 = graph)
    (hat : DynSpanner.Program.DynGraphAt st.mem graph vc ec G)
    (hroom : graph + 2 < 2 ^ w) :
    ∃ out, Runs w p ω loadMinRatioInitGraphSizes st .normal out 15 ∧
      out.regs 92 = G.n ∧ out.regs 93 = vc ∧ out.regs 94 = ec ∧
      (∀ r, r ≠ 92 → r ≠ 93 → r ≠ 94 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let s1 := { st with regs := Function.update st.regs 92 G.n }
  let s2 := { s1 with regs := Function.update s1.regs 93 vc }
  let out := { s2 with regs := Function.update s2.regs 94 ec }
  have hv : st.mem graph = vc := hat.2.2.2.1
  have he : st.mem (graph + 1) = ec := hat.2.2.2.2.1
  have hn : st.mem (graph + 2) = G.n := hat.2.2.2.2.2.1
  have hr1 : Runs w p ω (.assign 92 (.load (.bin .add (.reg 69) (.const 2)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hg, hn, hroom, show 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 93 (.load (.reg 69))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hg, hv], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 94 (.load (.bin .add (.reg 69) (.const 1)))) s2 .normal out 5 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s2, s1, hg, he, show 1 < 2 ^ w by omega,
        show graph + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 5, 9, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, 5, hr2, hr3, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out],
    fun r h92 h93 h94 => by simp [out, s2, s1, Function.update_of_ne, h92, h93, h94], rfl, rfl⟩

end MinCostFlow.MinRatio
