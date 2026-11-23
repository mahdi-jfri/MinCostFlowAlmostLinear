module

public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
public import MinCostFlow.MinRatio.OrdCoreOps
import WordRAM.Tactic

/-!
# The three sparse-core readouts under the layout contract (`WireCoreReadKFBL`)

The readouts of a sparse-core level are op `3` (the sparsifier graph), op `2` (the forest of the
active branch and its stretch tables) and op `5` (the order of the active branch). Under the
contract `sparseCoreOrdMachineContractK`, the solver needed a separate hypothesis
(`OrdCoreReadoutLayout`) to know where the returned objects lie. That hypothesis is false,
since it quantifies over every memory and not only the one a readout leaves. The contract
`sparseCoreOrdMachineContractKFBL` puts these layout facts into the posts of ops `2`, `3` and `5`,
and `SparseCoreReadoutFootAt` adds the two facts that a post cannot state, since they mention the
footprint or the returned heap pointer.

This file runs the three readout statements of `OrdCoreOps.lean` from `SparseCoreReadoutFootAt`,
and returns the layout facts with the results of the `K` versions (`WireCoreOpsK.lean`):
* `ordCoreReadGraphKFBL_runs` (op `3`): the caps of the returned graph are at most the caps of the
  level, and the graph ends at or below the heap pointer of the call;
* `ordCoreReadLSFKFBL_runs` (op `2`): the forest and the stretch tables end at or below the heap
  pointer of the call, and every cell of the forest is in the footprint or in the new space;
* `ordCoreReadOrdKFBL_runs` (op `5`): the order list starts at `heap + 1`, ends at or below the
  returned heap pointer, and its words fit a word.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {P : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

/-- Execute `ordCoreReadGraphStmt` (op `3`) under `SparseCoreReadoutFootAt`: the results of
`ordCoreReadGraphK_runs`, and the layout of the returned graph (caps at most `(vCap, eCap)`, and
the graph ends at or below `heap`). -/
theorem ordCoreReadGraphKFBL_runs {branch handle heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 1 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadGraphStmt (op 3)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.mem heap) vc ec (tool.S a.st branch) ∧
        vc = vCap ∧ ec = eCap ∧ out.mem heap + dynGraphSize vc ec ≤ heap) ∧
      R.Respects (R.foot handle x) heap 1 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 4 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hgraph, hrespect, hcost⟩ :=
    hFootAt.op3_runs handle a x [handle, branch, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, heap, rfl, hj⟩ hfoot hz hroom
  obtain ⟨vc, ec, hdg, hvc, hec, hend, -⟩ := hgraph
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil] at hdg hend
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 4] = some [handle, branch, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hp]
  have hcall : Runs w p ω (ordCoreReadGraphStmt (op 3)) st .normal out (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 3 + c + 1, y, hcall, by simp [out], hrep', ⟨vc, ec, hdg, hvc, hec, hend⟩,
    hrespect, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-- Execute `ordCoreReadLSFStmt` (op `2`) under `SparseCoreReadoutFootAt`: the results of
`ordCoreReadLSFK_runs`, the layout of the forest and of the stretch tables (they end at or below
`heap`), and the place of the forest's cells (in the footprint, or in the new space). -/
theorem ordCoreReadLSFKFBL_runs {branch handle graph heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 5 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      out.mem (heap + 4) ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
      (∃ vc ec, LSFAt out.mem heap vc ec fmt.limbBits (out.mem (heap + 4)) fmt.precision a.G.E
          (tool.lsfs a.st branch) ∧
        out.mem (heap + 1) + dynGraphSize vc ec ≤ heap ∧
        (∀ addr, out.mem (heap + 1) ≤ addr → addr < out.mem (heap + 1) + dynGraphSize vc ec →
          R.foot handle y addr ∨ (heap ≤ addr ∧ addr < ret))) ∧
      out.mem (heap + 3) + 2 ≤ heap ∧
      (∀ e ∈ a.G.E,
        out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap) ∧
      (∀ e ∈ a.G.E,
        out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap) ∧
      R.Respects (R.foot handle x) heap 5 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hFootAt.op2_runs handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨vc, ec, hLw, hlsf, hfEnd, hfIn, hst, hnum, hden, _⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hLw hlsf hfEnd hfIn hst hnum hden
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', hLw,
    ⟨vc, ec, hlsf, hfEnd, hfIn⟩, hst, fun e he => (hnum e he).1, fun e he => (hden e he).1,
    hrespect, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-- Execute `ordCoreReadOrdStmt` (op `5`) under `SparseCoreReadoutFootAt`: the results of
`ordCoreReadOrdK_runs`, and the layout of the order list (it starts at `heap + 1`, ends at or below
the returned heap pointer, and its words fit a word). -/
theorem ordCoreReadOrdKFBL_runs {branch handle heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + (1 + ordRotWords a branch) < 2 ^ w) :
    ∃ (out : State) (ret words cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadOrdStmt (op 5)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 9 = out.mem heap ∧
      R.rep handle a y out.mem ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) words ∧
      words ≤ ordRotWords a branch ∧
      out.regs 9 = heap + 1 ∧ out.regs 9 + words ≤ ret ∧
      (∀ j < words, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      R.Respects (R.foot handle x) heap (1 + ordRotWords a branch) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N + 8 +
          R.phi handle x st.mem ∧
      (∀ r, r ≠ 5 → r ≠ 9 → out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hFootAt.op5_runs handle a x [handle, branch, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, heap, rfl, hj⟩ hfoot hz hroom
  obtain ⟨words, hordAt, hwordsLe, hstart, hend, hfit⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hordAt hwordsLe hstart hend hfit hcost
  let mid := { after with regs := Function.update st.regs 5 o.value }
  let out := { mid with regs := Function.update mid.regs 9 (after.mem heap) }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 4] = some [handle, branch, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hp]
  have hcall : Runs w p ω (.call 5 (op 5) [.reg 3, .reg 2, .reg 4]) st .normal mid (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have hload : Runs w p ω (.assign 9 (.load (.reg 4))) mid .normal out 3 :=
    runs_assign_iff.mpr ⟨after.mem heap, by simp [Expr.eval, mid, Function.update_of_ne, hp],
      rfl, rfl, rfl⟩
  have h9 : out.regs 9 = after.mem heap := by simp [out]
  refine ⟨out, o.value, words, (3 + c + 1) + 3 + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 3 + c + 1, 3, hcall, hload, rfl⟩),
    by simp [out, mid, Function.update_of_ne], h9, hrep',
    by rw [h9]; exact hordAt, hwordsLe, by rw [h9]; exact hstart, by rw [h9]; exact hend,
    by rw [h9]; exact hfit, hrespect, ?_, ?_⟩
  · simp only [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
      sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
    change ((3 + c + 1) + 3 + 1) + R.phi handle y after.mem ≤ _
    omega
  · intro r hr5 hr9
    simp [out, mid, Function.update_of_ne hr5, Function.update_of_ne hr9]

end Execution

end MinCostFlow.MinRatio
