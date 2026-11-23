module

public import MinCostFlow.MinRatio.WireInitReadoutK
public import MinCostFlow.MinRatio.InitPathTreeChainHelpers
public import MinCostFlow.LastLevelProgram.Readout
import MinCostFlow.MinRatio.InitPathTreeEdges
import Mathlib.Tactic.Ring

/-!
# K-contract chain spanning-forest insertion into the Section 6 path tree (`WireInitLinkK`)

Proves `initLinkChainForestsK_runs` for the existing deterministic statement
`initLinkChainForests (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind` (`InitPathTreeEdges.lean`)
under `sparseCoreOrdMachineContractK`, `OrdCoreReadoutLayout`, `lastLevelRepresentation`, and
`pathTreeMachineContract`:
1. Links every edge of `chain.toTreeChain.chainTree` into the Section 6 path tree with exact
   `InitPathTreeInv`;
2. Preserves `OrdInitChainCoresK` (all `C.d` ordered sparse-core levels and the terminal
   `lastLevelRepresentation`);
3. Bounds total allocated space by `6 * C.d + 4 + m * linkSpace`;
4. Bounds `cost + Rtree.phi + ∑ i : Fin C.d, Rcore.phi` by
   `C.d * (2 * P.readout + 75) + m * (pathTreeBudget treeConst L G.n + 96) + 140` plus the
   incoming potentials.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

/-- Space budget of `initLinkChainForests` across all `d + 1` levels. -/
@[expose] def initLinkChainSpace (d m linkSpace : ℕ) : ℕ :=
  6 * d + 4 + m * linkSpace

/-- Fixed step budget of `initLinkChainForests` (excluding incoming potentials). -/
@[expose] def initLinkChainCost (d m treeConst L n readout : ℕ) : ℕ :=
  d * (2 * readout + 80) + m * (pathTreeBudget treeConst L n + 96) + 140

theorem run_core_readForestK {w L initCore coreHandle branch curGraph curHeap vc ec
    capExp levelTable branchTable i k M N : ℕ} {fmt : Num.Format w}
    {T : SparseCoreRestartTool} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {G0 : MGraph} {a : SparseCoreOrdAbs T} {x : Rcore.τ}
    (hFour : fmt.limbBits = 4)
    (himpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractK fmt L T G0 k M N vc ec capExp P alloc))
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
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 5 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 11 + P.readout + Rcore.phi coreHandle x st.mem := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] =
      some [coreHandle, branch, curGraph, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h34, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ v ∈ [coreHandle, branch, curGraph, curHeap], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  have hpre : (sparseCoreOrdMachineContractK fmt L T G0 k M N vc ec capExp P alloc).pre 2 a
      [coreHandle, branch, curGraph, curHeap] st.mem :=
    ⟨hinput, coreHandle, branch, curGraph, curHeap, rfl, hbr, hGi, hGiBelow⟩
  obtain ⟨body, hbody, o, after, c, hr, a', y, hrep', hpost, hresp, hc⟩ :=
    himpl.2.2 2 coreHandle a x [coreHandle, branch, curGraph, curHeap] st.mem st.pos ω
      hwords rfl hrep hpre hfoot hz hroom
  obtain ⟨ha', fv, fe, _, hlsf⟩ := hpost
  subst ha'
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil,
    hFour] at hlsf
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 10 + c + 1, y, fv, fe, after.mem (curHeap + 4),
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hlsf, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ P.readout + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

theorem run_core_readGraphK {w L initCore coreHandle branch curHeap vc ec
    capExp levelTable branchTable i k M N : ℕ} {fmt : Num.Format w}
    {T : SparseCoreRestartTool} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {G0 : MGraph} {a : SparseCoreOrdAbs T} {x : Rcore.τ}
    (himpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractK fmt L T G0 k M N vc ec capExp P alloc))
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
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 1 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 10 + P.readout + Rcore.phi coreHandle x st.mem := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 3] =
      some [coreHandle, branch, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ v ∈ [coreHandle, branch, curHeap], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  have hpre : (sparseCoreOrdMachineContractK fmt L T G0 k M N vc ec capExp P alloc).pre 3 a
      [coreHandle, branch, curHeap] st.mem :=
    ⟨hinput, coreHandle, branch, curHeap, rfl, hbr⟩
  obtain ⟨body, hbody, o, after, c, hr, a', y, hrep', hpost, hresp, hc⟩ :=
    himpl.2.2 3 coreHandle a x [coreHandle, branch, curHeap] st.mem st.pos ω
      hwords rfl hrep hpre hfoot hz hroom
  obtain ⟨ha', gv, ge, hdg⟩ := hpost
  subst ha'
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil] at hdg
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 9 + c + 1, y, gv, ge,
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hdg, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ P.readout + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

private theorem activeLSF_card_prefix_sum {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) :
    ∀ k ≤ C.d + 1,
      ((Finset.range k).biUnion fun j => (C.activeLSF j).F.F.E).card =
        ∑ j ∈ Finset.range k, (C.activeLSF j).F.F.m := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← initChain_prefix_union k,
      Finset.card_union_of_disjoint (initChain_prefix_disjoint hH (by omega)),
      ih (by omega), Finset.sum_range_succ]
    rfl

theorem activeLSF_sum_le_m {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) :
    ∑ j ∈ Finset.range (C.d + 1), (C.activeLSF j).F.F.m ≤ G.m := by
  rw [← activeLSF_card_prefix_sum hH (C.d + 1) le_rfl]
  have hsub := C.chainTree_isSubgraph hH (C.forestsAreSubgraphs_of_holds hH)
  rw [hH.1] at hsub
  exact Finset.card_le_card hsub.2.1

/-- Loop invariant after linking active forests of levels `0 .. i - 1`. The current graph has the
caps `(G.n, ec0)`, as every level of the sparse core does. -/
structure InitChainLoopInvK {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (Rterm : DSRep (ℕ × (ℕ → LSF)))
    (Rtree : DSRep PathTreeState)
    (chain : ChainState T C) (treeHandle rootBase levelTable branchTable
      slots names slotThresholds edgeRecords edgeThresholds m ec0 L heap linkSpace capLimit : ℕ)
    (G : MGraph) (val : ℕ → PathEdgeValue) (B : ℤ) (recPtr thPtr : ℕ → ℕ)
    (extraStatic : ℕ → Prop) (initMem : ℕ → ℕ)
    (i : ℕ) (curSt : State) (curHeap : ℕ) (curS : PathTreeState)
    (curXTree : Rtree.τ) (curSlot curName : ℕ → ℕ)
    (curXCore : ℕ → Rcore.τ) (curXTerm : Rterm.τ) : Prop where
  r32 : curSt.regs 32 = i
  r31 : curSt.regs 31 = C.d
  r0 : curSt.regs 0 = treeHandle
  r3 : curSt.regs 3 = curHeap
  r9 : curSt.regs 9 = dgETailSlotBase rootBase G.n ec0
  r10 : curSt.regs 10 = dgEHeadSlotBase rootBase G.n ec0
  r11 : curSt.regs 11 = dgIntToExtBase rootBase G.n
  r19 : curSt.regs 19 = slots
  r20 : curSt.regs 20 = names
  r22 : curSt.regs 22 = edgeRecords
  r23 : curSt.regs 23 = edgeThresholds
  r24 : curSt.regs 24 = slotThresholds
  r29 : curSt.regs 29 = levelTable
  r30 : curSt.regs 30 = branchTable
  heapLo : heap ≤ curHeap
  heapHi : curHeap ≤ heap + 6 * i +
    (∑ j ∈ Finset.range i, (chain.toTreeChain.activeLSF j).F.F.m) * linkSpace
  zeroFrom : ZeroFrom curSt.mem curHeap
  staticEq : ∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
    C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a → curSt.mem a = initMem a
  curG : ∃ vc ec, vc = G.n ∧ ec = ec0 ∧ vc + ec + 2 ≤ capLimit ∧
    DynGraphAt curSt.mem (curSt.regs 34) vc ec (chain.G i) ∧
    curSt.regs 34 + dynGraphSize vc ec ≤ curHeap
  treeInv : InitPathTreeInv Rtree treeHandle G chain.toTreeChain.chainTree val B
    slots names slotThresholds m thPtr
    ((Finset.range i).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
    curS curXTree curSlot curName curHeap curSt.mem
  treeOut : ∀ a, Rtree.foot treeHandle curXTree a →
    OutsideInitSlotTables slots names slotThresholds m G.n a ∧
    ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
      C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a
  cores : OrdInitChainCoresK Rcore Rterm Rtree chain treeHandle levelTable branchTable
    rootBase edgeRecords edgeThresholds slots names slotThresholds m L curHeap G recPtr
    extraStatic curXCore curXTerm curXTree curSt.mem


end MinCostFlow.MinRatio
