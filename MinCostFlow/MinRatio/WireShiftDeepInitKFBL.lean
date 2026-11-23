module

public import MinCostFlow.MinRatio.WireShiftDeepPhases
import WordRAM.Tactic

/-!
# Phase 0 of the deep shift under the layout contract

The init of a sparse-core level under `sparseCoreOrdMachineContractKFBL` reads the depth of the
module from register `98` (`ordCoreInitStmtKFBL`). The solver header keeps the depth at
`handle + 17`. So Phase 0 of the deep shift must load it, which `shiftDeepInitRegs` does not do.
* `shiftDeepInitRegsKFBL`: `shiftDeepInitRegs`, then register `98` gets `mem[handle + 17]`.
* `shiftDeepInitRegsKFBL_runs`: the result of `shiftDeepInitRegs_runs`, and register `98` holds
  the depth.

`shiftDeepInitRegs` stays as it is, since the chain core uses it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- Phase 0 of the deep shift under `KFBL`: `shiftDeepInitRegs`, then the depth from
`handle + 17` (register `73` holds `handle`) into register `98`. -/
@[expose] def shiftDeepInitRegsKFBL : Stmt :=
  shiftDeepInitRegs ;;
  .assign 98 (.load (.bin .add (.reg 73) (.const 17)))

theorem shiftDeepInitRegsKFBL_noRand : shiftDeepInitRegsKFBL.NoRand := by
  simp [shiftDeepInitRegsKFBL, shiftDeepInitRegs_noRand, Stmt.NoRand]

/-- Execute `shiftDeepInitRegsKFBL`: the result of `shiftDeepInitRegs_runs`, and register `98`
holds the depth stored at `handle + 17`. -/
theorem shiftDeepInitRegsKFBL_runs {w root i heap0 handle table d k depth pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hH : mem root = handle) (hTab : mem (root + 1) = table)
    (hD : mem (handle + 11) = d) (hK : mem (handle + 12) = k)
    (hDepth : mem (handle + 17) = depth)
    (hiLt : i < d) (hRoot1W : root + 1 < 2 ^ w) (hH12W : handle + 12 < 2 ^ w)
    (hBrBaseW : handle + 18 + (d + 1) < 2 ^ w)
    (hMetaW : table + (d + 1) + 1 + d < 2 ^ w)
    (hHeapW : heap0 + 2 * (d - i + 1) < 2 ^ w) (hw17 : 17 < 2 ^ w) :
    let cnt := d - i + 1
    let handleBase := handle + 18
    let branchBase := handleBase + (d + 1)
    let lvlMTable := table + (d + 1) + 1
    let levelMeta := lvlMTable + d
    ∃ out c,
      Runs w p ω shiftDeepInitRegsKFBL (startState [root, i, heap0] mem pos) .normal out c ∧
      c ≤ 86 ∧ out.mem = mem ∧
      out.regs 70 = root ∧ out.regs 71 = i ∧ out.regs 72 = heap0 ∧
      out.regs 73 = handle ∧ out.regs 74 = table ∧ out.regs 75 = d ∧ out.regs 76 = k ∧
      out.regs 77 = handleBase ∧ out.regs 78 = branchBase ∧ out.regs 79 = cnt ∧
      out.regs 80 = heap0 ∧ out.regs 81 = heap0 + cnt ∧
      out.regs 82 = lvlMTable ∧ out.regs 83 = levelMeta ∧
      out.regs 4 = heap0 + 2 * cnt ∧ out.regs 98 = depth := by
  obtain ⟨s, c, r, hc, hmem, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82,
      h83, h4⟩ :=
    shiftDeepInitRegs_runs (p := p) (ω := ω) (pos := pos) (heap0 := heap0) hH hTab hD hK hiLt
      hRoot1W hH12W hBrBaseW hMetaW hHeapW hw17
  let out := { s with regs := Function.update s.regs 98 depth }
  have rD : Runs w p ω (.assign 98 (.load (.bin .add (.reg 73) (.const 17)))) s .normal out 5 :=
    runs_assign_iff.mpr ⟨depth, by
      simp [Expr.eval, BinOp.eval, h73, show handle + 17 < 2 ^ w by omega, hw17, hmem, hDepth],
      rfl, rfl, rfl⟩
  have hk (r : ℕ) (hr : r ≠ 98) : out.regs r = s.regs r := Function.update_of_ne hr _ _
  exact ⟨out, c + 5 + 1, runs_seq_iff.mpr (Or.inr ⟨s, c, 5, r, rD, rfl⟩), by omega, hmem,
    (hk 70 (by decide)).trans h70, (hk 71 (by decide)).trans h71,
    (hk 72 (by decide)).trans h72, (hk 73 (by decide)).trans h73,
    (hk 74 (by decide)).trans h74, (hk 75 (by decide)).trans h75,
    (hk 76 (by decide)).trans h76, (hk 77 (by decide)).trans h77,
    (hk 78 (by decide)).trans h78, (hk 79 (by decide)).trans h79,
    (hk 80 (by decide)).trans h80, (hk 81 (by decide)).trans h81,
    (hk 82 (by decide)).trans h82, (hk 83 (by decide)).trans h83,
    (hk 4 (by decide)).trans h4, by simp [out]⟩

end MinCostFlow.MinRatio
