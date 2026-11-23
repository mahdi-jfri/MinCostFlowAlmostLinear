module

public import MinCostFlow.MinRatio.WireInitLinkBaseK
public import MinCostFlow.MinRatio.WireCoreReadKFBL

/-!
# The two core readouts of the linking loop under the layout contract (`WireInitLinkBaseKFBL`)

The loop of `initLinkChainForests` (`InitPathTreeEdges.lean`) reads, at each level, the active
forest by op `2` and the next graph by op `3`. `run_core_readForestK` and `run_core_readGraphK`
(`WireInitLinkBaseK.lean`) run these two calls under `sparseCoreOrdMachineContractK`, and the loop
takes the layout of the results from `OrdCoreReadoutLayout`.

This file runs the same two calls from `SparseCoreReadoutFootAt`, the companion of
`sparseCoreOrdMachineContractKFBL`, and returns the layout facts with the results:
* `run_core_readForestKFBL` (op `2`): the forest ends at or below the heap pointer of the call,
  and each of its cells is in the footprint or in the new space;
* `run_core_readGraphKFBL` (op `3`): the caps of the next graph are at most the caps of the level,
  the graph ends at or below the heap pointer of the call, and each of its cells is in the
  footprint or in the new space.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

/-- The op `2` call of the linking loop under `SparseCoreReadoutFootAt`: the results of
`run_core_readForestK`, and the layout of the forest. -/
theorem run_core_readForestKFBL {w L depth coreHandle branch curGraph curHeap vc ec
    capExp levelTable branchTable i k M N : ℕ} {fmt : Num.Format w}
    {T : SparseCoreRestartTool} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {G0 : MGraph} {a : SparseCoreOrdAbs T} {x : Rcore.τ}
    (hFour : fmt.limbBits = 4)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth T G0 k M N vc ec capExp P alloc Rcore p opCore)
    (hrep : Rcore.rep coreHandle a x st.mem)
    (hfoot : ∀ addr, Rcore.foot coreHandle x addr → addr < curHeap)
    (hbr : branch < k)
    (hinput : SparseCoreOrdInput T k M N a.st a.G a.ord a.n)
    (hGi : DynGraphAt st.mem curGraph vc ec a.G)
    (hGiBelow : curGraph + dynGraphSize vc ec ≤ curHeap)
    (h3 : st.regs 3 = curHeap) (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h32 : st.regs 32 = i) (h34 : st.regs 34 = curGraph)
    (hchAt : st.mem (levelTable + i) = coreHandle)
    (hbrAt : st.mem (branchTable + i) = branch)
    (hchW : levelTable + i < 2 ^ w) (hbrW : branchTable + i < 2 ^ w)
    (hhandleW : coreHandle < 2 ^ w) (hbrValW : branch < 2 ^ w) (hcgW : curGraph < 2 ^ w)
    (hz : ZeroFrom st.mem curHeap) (hroom : curHeap + 5 < 2 ^ w) :
    ∃ out ret cost y fv fe Lw,
      Runs w p ω (.call 3 (opCore 2) [.load (.bin .add (.reg 29) (.reg 32)),
        .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3]) st .normal out cost ∧
      out.regs 3 = ret ∧ (∀ r ≠ 3, out.regs r = st.regs r) ∧
      Rcore.rep coreHandle a y out.mem ∧
      LSFAt out.mem curHeap fv fe 4 Lw fmt.precision a.G.E (T.lsfs a.st branch) ∧
      out.mem (curHeap + 1) + dynGraphSize fv fe ≤ curHeap ∧
      (∀ addr, out.mem (curHeap + 1) ≤ addr → addr < out.mem (curHeap + 1) + dynGraphSize fv fe →
        Rcore.foot coreHandle y addr ∨ (curHeap ≤ addr ∧ addr < ret)) ∧
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 5 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 11 + P.readout + Rcore.phi coreHandle x st.mem := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] =
      some [coreHandle, branch, curGraph, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h34, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ v ∈ [coreHandle, branch, curGraph, curHeap], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hr, hrep', hpost, hresp, hc⟩ :=
    hFootAt.op2_runs coreHandle a x [coreHandle, branch, curGraph, curHeap] st.mem st.pos ω
      hwords rfl hrep ⟨hinput, coreHandle, branch, curGraph, curHeap, rfl, hbr, hGi, hGiBelow⟩
      hfoot hz hroom
  obtain ⟨fv, fe, -, hlsf, hfEnd, hfIn, -⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil,
    hFour] at hlsf hfEnd hfIn
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 10 + c + 1, y, fv, fe, after.mem (curHeap + 4),
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hlsf, hfEnd, hfIn, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ P.readout + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

/-- The op `3` call of the linking loop under `SparseCoreReadoutFootAt`: the results of
`run_core_readGraphK`, and the layout of the next graph (caps at most `(vc, ec)`). -/
theorem run_core_readGraphKFBL {w L depth coreHandle branch curHeap vc ec
    capExp levelTable branchTable i k M N : ℕ} {fmt : Num.Format w}
    {T : SparseCoreRestartTool} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {G0 : MGraph} {a : SparseCoreOrdAbs T} {x : Rcore.τ}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth T G0 k M N vc ec capExp P alloc Rcore p opCore)
    (hrep : Rcore.rep coreHandle a x st.mem)
    (hfoot : ∀ addr, Rcore.foot coreHandle x addr → addr < curHeap)
    (hbr : branch < k)
    (hinput : SparseCoreOrdInput T k M N a.st a.G a.ord a.n)
    (h3 : st.regs 3 = curHeap) (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h32 : st.regs 32 = i)
    (hchAt : st.mem (levelTable + i) = coreHandle)
    (hbrAt : st.mem (branchTable + i) = branch)
    (hchW : levelTable + i < 2 ^ w) (hbrW : branchTable + i < 2 ^ w)
    (hhandleW : coreHandle < 2 ^ w) (hbrValW : branch < 2 ^ w)
    (hz : ZeroFrom st.mem curHeap) (hroom : curHeap + 1 < 2 ^ w) :
    ∃ out ret cost y gv ge,
      Runs w p ω (.call 3 (opCore 3) [.load (.bin .add (.reg 29) (.reg 32)),
        .load (.bin .add (.reg 30) (.reg 32)), .reg 3]) st .normal out cost ∧
      out.regs 3 = ret ∧ (∀ r ≠ 3, out.regs r = st.regs r) ∧
      Rcore.rep coreHandle a y out.mem ∧
      DynGraphAt out.mem (out.mem curHeap) gv ge (T.S a.st branch) ∧
      gv = vc ∧ ge = ec ∧ out.mem curHeap + dynGraphSize gv ge ≤ curHeap ∧
      (∀ addr, out.mem curHeap ≤ addr → addr < out.mem curHeap + dynGraphSize gv ge →
        Rcore.foot coreHandle y addr ∨ (curHeap ≤ addr ∧ addr < ret)) ∧
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 1 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 10 + P.readout + Rcore.phi coreHandle x st.mem := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 3] =
      some [coreHandle, branch, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ v ∈ [coreHandle, branch, curHeap], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hr, hrep', hpost, hresp, hc⟩ :=
    hFootAt.op3_runs coreHandle a x [coreHandle, branch, curHeap] st.mem st.pos ω
      hwords rfl hrep ⟨hinput, coreHandle, branch, curHeap, rfl, hbr⟩ hfoot hz hroom
  obtain ⟨gv, ge, hdg, hgv, hge, hgEnd, hgIn⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hdg hgEnd hgIn
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 9 + c + 1, y, gv, ge,
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hdg, hgv, hge, hgEnd, hgIn, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ P.readout + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

end MinCostFlow.MinRatio
