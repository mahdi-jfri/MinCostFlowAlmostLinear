module

public import MinCostFlow.SparseCore.Program.ReadLib

import WordRAM.Tactic

/-!
# Deleting an edge from the tree `T`

When the input batch deletes an edge `e` of `G`, `tViewUpdate` deletes `e` from the tree `T` as
well, leaving the frozen part unchanged (`frozenT_step_delete`, `ReadTree.lean`).
`delFrzStmt` (`[tPtr, frzPtr, e]`) deletes `e` from the tree block at `tPtr` via `dgDeleteEdge`
(ignoring `frzPtr`, keeping the three-argument interface of `updOneStmt`). It costs at most `700`
(`delFrz_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- `[tPtr, frzPtr, e]`: delete `e` from the graph at `tPtr` (if present). -/
def delFrzStmt (L : ReadLib) : Stmt :=
  .call 4 (L.edge + dgIdxDeleteEdge) [.reg 0, .reg 2] ;;
  .ret (.const 0)

theorem delFrzStmt_noRand (L : ReadLib) : (delFrzStmt L).NoRand := by
  simp [delFrzStmt, Stmt.NoRand]

/-- Contract of `delFrzStmt` for the tree `T` (caps `vCap`, `tCap`): deletes `e` from `T` in place
and leaves all memory outside the block of `T` unchanged. -/
def delFrzContract (w vCap tCap : ℕ) (T : MGraph) : Contract where
  pre args mem := ∃ tPtr frzPtr e, args = [tPtr, frzPtr, e] ∧
    16 ≤ 2 ^ w ∧ tPtr + dynGraphSize vCap tCap < 2 ^ w ∧
    DynGraphAt mem tPtr vCap tCap T
  post args mem ret mem' := ∃ tPtr frzPtr e, args = [tPtr, frzPtr, e] ∧ ret = 0 ∧
    DynGraphAt mem' tPtr vCap tCap (T.applyUpdate (.delete e)) ∧
    ∀ a, (a < tPtr ∨ tPtr + dynGraphSize vCap tCap ≤ a) → mem' a = mem a
  cost _ _ := 700

/-- `delFrzStmt` meets `delFrzContract`. -/
theorem delFrz_meetsContract {w : ℕ} {p : Program} {L : ReadLib} {f vCap tCap : ℕ}
    {T : MGraph} (hL : L.Has p) (hp : p.procs[f]? = some (delFrzStmt L)) :
    MeetsContract w p f (delFrzContract w vCap tCap T) := by
  refine meetsContract_of_runs hp ?_
  rintro args mem pos ω hargs ⟨tPtr, frzPtr, e, rfl, hw16, hT1, hT⟩
  have htw : tPtr < 2 ^ w := hargs _ (by simp)
  have hew : e < 2 ^ w := hargs _ (by simp)
  apply runs_start_le
  refine runs_seq_call_le (dgDeleteEdge_meetsContract (vCap := vCap) (eCap := tCap) (G := T)
      hL.2.1 hL.1) (vs := [tPtr, e]) (by eval_expr) (by wram_words)
    ⟨tPtr, e, rfl, hw16, hT1, hT⟩ ?_
  rintro r1 mem1 pos1 ⟨_, _, hEq1, -, hT1', hfr1⟩
  simp only [List.cons.injEq, and_true] at hEq1
  obtain ⟨rfl, rfl⟩ := hEq1
  have hT_del : DynGraphAt mem1 tPtr vCap tCap (T.applyUpdate (.delete e)) := by
    by_cases heT : e ∈ T.E
    · simpa [heT] using hT1'
    · simp only [heT, ↓reduceIte] at hT1'
      refine DynGraphAt.congr_ends (G₁ := T) (G₂ := T.applyUpdate (.delete e))
        rfl (Finset.erase_eq_of_notMem heT).symm (fun _ _ => ⟨rfl, rfl⟩) hT1'
  refine runs_ret_le (v := 0) (by eval_expr) ⟨tPtr, frzPtr, e, rfl, rfl, hT_del, hfr1⟩ ?_
  simp only [delFrzContract, dgDeleteEdgeContract, argsSize, Expr.size]
  omega

end MinCostFlow.SparseCore.Program.Read
