module

public import MinCostFlow.MinRatio.InitPathTreeEdges

/-!
# Helper invariants and readout wrappers for `initLinkChainForests`

Defines the read-only address region `InitChainStaticAddr`, the pairwise-disjoint
core/terminal representation invariant `InitChainCoresAt`, the per-level loop
invariant `InitChainLoopInv`, and single-call wrappers for reading a level's
active LSF (`op_core 2`, `op_last 0`) and next level graph (`op_core 3`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Static read-only addresses needed throughout `initLinkChainForests`:
the root graph, descriptor tables, initial edge record/threshold tables, and
initial `PathEdgeAt` records for tree edges. -/
@[expose] def InitChainStaticAddr (rootBase levelTable branchTable edgeRecords edgeThresholds
    d m L : ℕ) (G T : MGraph) (recPtr : ℕ → ℕ) (extraStatic : ℕ → Prop) (a : ℕ) : Prop :=
  (rootBase ≤ a ∧ a < rootBase + dynGraphSize G.n G.m) ∨
  (levelTable ≤ a ∧ a ≤ levelTable + d) ∨
  (branchTable ≤ a ∧ a ≤ branchTable + d) ∨
  (edgeRecords ≤ a ∧ a < edgeRecords + m) ∨
  (edgeThresholds ≤ a ∧ a < edgeThresholds + m) ∨
  (∃ e ∈ T.E, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L)) ∨
  extraStatic a

/-- Disjointness and representation invariant for all `C.d` sparse-core levels
and the terminal last-level data structure during `initLinkChainForests`. -/
@[expose] def InitChainCoresAt {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep T.State) (Rterm : DSRep (ℕ × (ℕ → LSF))) (Rtree : DSRep PathTreeState)
    (chain : ChainState T C) (treeHandle levelTable branchTable
      rootBase edgeRecords edgeThresholds slots names slotThresholds m L heap : ℕ)
    (G : MGraph) (recPtr : ℕ → ℕ) (extraStatic : ℕ → Prop)
    (xCore : ℕ → Rcore.τ) (xTerm : Rterm.τ) (xTree : Rtree.τ) (mem : ℕ → ℕ) : Prop :=
  let Ttree := chain.toTreeChain.chainTree
  (∀ i < C.d,
    mem (branchTable + i) = chain.bran i ∧
    Rcore.rep (mem (levelTable + i)) (chain.scState i) (xCore i) mem ∧
    (∀ a, Rcore.foot (mem (levelTable + i)) (xCore i) a →
      a < heap ∧
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧
      ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
      ¬ Rtree.foot treeHandle xTree a ∧
      (∀ j < C.d, j ≠ i → ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a) ∧
      ¬ Rterm.foot (mem (levelTable + C.d)) xTerm a)) ∧
  mem (branchTable + C.d) = chain.lastBran ∧
  Rterm.rep (mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) xTerm mem ∧
  (∀ a, Rterm.foot (mem (levelTable + C.d)) xTerm a →
    a < heap ∧
    OutsideInitSlotTables slots names slotThresholds m G.n a ∧
    ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
    ¬ Rtree.foot treeHandle xTree a ∧
    (∀ j < C.d, ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a))

/-- Loop invariant after processing levels `0 .. i - 1` of `initLinkChainForests`. -/
@[expose] def InitChainLoopInv {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep T.State) (Rterm : DSRep (ℕ × (ℕ → LSF))) (Rtree : DSRep PathTreeState)
    (chain : ChainState T C) (treeHandle rootBase levelTable branchTable
      slots names slotThresholds edgeRecords edgeThresholds m L heap levelSpace : ℕ)
    (G : MGraph) (val : ℕ → PathEdgeValue) (B : ℤ) (recPtr thPtr : ℕ → ℕ)
    (extraStatic : ℕ → Prop)
    (initMem : ℕ → ℕ) (i : ℕ) (curSt : State) (curHeap : ℕ) (curS : PathTreeState)
    (curXTree : Rtree.τ) (curSlot curName : ℕ → ℕ)
    (curXCore : ℕ → Rcore.τ) (curXTerm : Rterm.τ) : Prop :=
  let Ttree := chain.toTreeChain.chainTree
  curSt.regs 32 = i ∧ curSt.regs 31 = C.d ∧
  curSt.regs 0 = treeHandle ∧ curSt.regs 3 = curHeap ∧
  curSt.regs 9 = dgETailSlotBase rootBase G.n G.m ∧
  curSt.regs 10 = dgEHeadSlotBase rootBase G.n G.m ∧
  curSt.regs 11 = dgIntToExtBase rootBase G.n ∧
  curSt.regs 19 = slots ∧ curSt.regs 20 = names ∧
  curSt.regs 22 = edgeRecords ∧ curSt.regs 23 = edgeThresholds ∧
  curSt.regs 24 = slotThresholds ∧
  curSt.regs 29 = levelTable ∧ curSt.regs 30 = branchTable ∧
  heap ≤ curHeap ∧ curHeap ≤ heap + i * levelSpace ∧
  ZeroFrom curSt.mem curHeap ∧
  (∀ a, InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds
    C.d m L G Ttree recPtr extraStatic a → curSt.mem a = initMem a) ∧
  (∃ vc ec, DynGraphAt curSt.mem (curSt.regs 34) vc ec (chain.G i) ∧
    curSt.regs 34 + dynGraphSize vc ec ≤ curHeap) ∧
  InitPathTreeInv Rtree treeHandle G Ttree val B slots names slotThresholds m thPtr
    ((Finset.range i).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E)
    curS curXTree curSlot curName curHeap curSt.mem ∧
  (∀ a, Rtree.foot treeHandle curXTree a →
    OutsideInitSlotTables slots names slotThresholds m G.n a ∧
    ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a) ∧
  InitChainCoresAt Rcore Rterm Rtree chain treeHandle levelTable branchTable
    rootBase edgeRecords edgeThresholds slots names slotThresholds m L curHeap G recPtr extraStatic
    curXCore curXTerm curXTree curSt.mem

theorem initChain_prefix_union {C : TreeChain} (i : ℕ) :
    (Finset.range i).biUnion (fun j => (C.activeLSF j).F.F.E) ∪ (C.activeLSF i).F.F.E =
    (Finset.range (i + 1)).biUnion (fun j => (C.activeLSF j).F.F.E) := by
  rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]

theorem initChain_prefix_disjoint {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {i : ℕ} (hi : i ≤ C.d) :
    Disjoint ((Finset.range i).biUnion (fun j => (C.activeLSF j).F.F.E))
      (C.activeLSF i).F.F.E := by
  rw [Finset.disjoint_biUnion_left]
  intro j hj
  exact C.activeLSF_E_disjoint hH (C.forestsAreSubgraphs_of_holds hH) (Finset.mem_range.mp hj) hi

theorem activeLSF_subset_chainTree {C : TreeChain} {i : ℕ} (hi : i ≤ C.d) :
    (C.activeLSF i).F.F.E ⊆ C.chainTree.E := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), he⟩

theorem run_core_readForest {w L initCore coreHandle branch curGraph curHeap vc ec
    levelTable branchTable i : ℕ} {fmt : Num.Format w} {T : SparseCoreRestartTool}
    {C : ChainParams} {costs : SparseCoreMachineCosts} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep T.State} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {Mcap Ncap : ℕ} {G0 Gi : MGraph} {s : T.State} {x : Rcore.τ}
    (himpl : Rcore.Implements w p initCore opCore
      (sparseCoreMachineContract fmt L T G0 C.k Mcap Ncap vc ec costs alloc))
    (hrep : Rcore.rep coreHandle s x st.mem)
    (hfoot : ∀ a, Rcore.foot coreHandle x a → a < curHeap)
    (hbr : branch < C.k)
    (hinput : SparseCoreInput T.toSparseCoreTool T.restart C.k s Gi)
    (hGi : DynGraphAt st.mem curGraph vc ec Gi)
    (hGiBelow : curGraph + dynGraphSize vc ec ≤ curHeap)
    (h3 : st.regs 3 = curHeap) (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h32 : st.regs 32 = i) (h34 : st.regs 34 = curGraph)
    (hchAt : st.mem (levelTable + i) = coreHandle)
    (hbrAt : st.mem (branchTable + i) = branch)
    (hchW : levelTable + i < 2 ^ w) (hbrW : branchTable + i < 2 ^ w)
    (hhandleW : coreHandle < 2 ^ w) (hbrValW : branch < 2 ^ w)
    (hcgW : curGraph < 2 ^ w)
    (hz : ZeroFrom st.mem curHeap)
    (hroom : curHeap + 4 < 2 ^ w) :
    ∃ out ret cost y fv fe,
      Runs w p ω (.call 3 (opCore 2) [.load (.bin .add (.reg 29) (.reg 32)),
        .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3]) st .normal out cost ∧
      out.regs 3 = ret ∧ (∀ r ≠ 3, out.regs r = st.regs r) ∧
      Rcore.rep coreHandle s y out.mem ∧
      LSFAt out.mem curHeap fv fe fmt.limbBits L fmt.precision
        (readNamedGraph st.mem curGraph vc ec).E (T.lsfs s branch) ∧
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 4 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 11 + 64 + Rcore.phi coreHandle x st.mem + 1 := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] =
      some [coreHandle, branch, curGraph, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h34, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ a ∈ [coreHandle, branch, curGraph, curHeap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre : (sparseCoreMachineContract fmt L T G0 C.k Mcap Ncap vc ec costs alloc).pre 2 s
      [coreHandle, branch, curGraph, curHeap] st.mem :=
    ⟨coreHandle, branch, curGraph, curHeap, Gi, rfl, hbr, ⟨hinput, hGi⟩, hGiBelow⟩
  obtain ⟨body, hbody, o, after, c, hr, s', y, hrep', hpost, hresp, hc⟩ :=
    himpl.2.2 2 coreHandle s x [coreHandle, branch, curGraph, curHeap] st.mem st.pos ω
      hwords rfl hrep hpre hfoot hz (show curHeap + 4 < 2 ^ w from hroom)
  obtain ⟨hs', fv, fe, hlsf⟩ := hpost
  subst hs'
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 10 + c + 1, y, fv, fe,
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hlsf, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ 64 + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

theorem run_core_readGraph {w L initCore coreHandle branch curHeap vc ec
    levelTable branchTable i : ℕ} {fmt : Num.Format w}
    {T : SparseCoreRestartTool} {C : ChainParams}
    {costs : SparseCoreMachineCosts} {alloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep T.State} {opCore : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {Mcap Ncap : ℕ} {G0 Gi : MGraph} {s : T.State} {x : Rcore.τ}
    (himpl : Rcore.Implements w p initCore opCore
      (sparseCoreMachineContract fmt L T G0 C.k Mcap Ncap vc ec costs alloc))
    (hrep : Rcore.rep coreHandle s x st.mem)
    (hfoot : ∀ a, Rcore.foot coreHandle x a → a < curHeap)
    (hbr : branch < C.k)
    (hinput : SparseCoreInput T.toSparseCoreTool T.restart C.k s Gi)
    (h3 : st.regs 3 = curHeap) (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h32 : st.regs 32 = i)
    (hchAt : st.mem (levelTable + i) = coreHandle)
    (hbrAt : st.mem (branchTable + i) = branch)
    (hchW : levelTable + i < 2 ^ w) (hbrW : branchTable + i < 2 ^ w)
    (hhandleW : coreHandle < 2 ^ w) (hbrValW : branch < 2 ^ w)
    (hz : ZeroFrom st.mem curHeap)
    (hroom : curHeap + 1 < 2 ^ w) :
    ∃ out ret cost y gv ge,
      Runs w p ω (.call 3 (opCore 3) [.load (.bin .add (.reg 29) (.reg 32)),
        .load (.bin .add (.reg 30) (.reg 32)), .reg 3]) st .normal out cost ∧
      out.regs 3 = ret ∧ (∀ r ≠ 3, out.regs r = st.regs r) ∧
      Rcore.rep coreHandle s y out.mem ∧
      DynGraphAt out.mem (out.mem curHeap) gv ge (T.S s branch) ∧
      Rcore.Respects (Rcore.foot coreHandle x) curHeap 1 st.mem ret coreHandle y out.mem ∧
      cost + Rcore.phi coreHandle y out.mem ≤ 10 + 64 + Rcore.phi coreHandle x st.mem + 1 := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 3] =
      some [coreHandle, branch, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h32, h3, hchW, hbrW, hchAt, hbrAt]
  have hwords : ∀ a ∈ [coreHandle, branch, curHeap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre : (sparseCoreMachineContract fmt L T G0 C.k Mcap Ncap vc ec costs alloc).pre 3 s
      [coreHandle, branch, curHeap] st.mem :=
    ⟨coreHandle, branch, curHeap, Gi, rfl, hbr, hinput⟩
  obtain ⟨body, hbody, o, after, c, hr, s', y, hrep', hpost, hresp, hc⟩ :=
    himpl.2.2 3 coreHandle s x [coreHandle, branch, curHeap] st.mem st.pos ω
      hwords rfl hrep hpre hfoot hz (show curHeap + 1 < 2 ^ w from hroom)
  obtain ⟨hs', gv, ge, hdg⟩ := hpost
  subst hs'
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 9 + c + 1, y, gv, ge,
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hdg, hresp, ?_⟩
  change c + Rcore.phi coreHandle y after.mem ≤ 64 + Rcore.phi coreHandle x st.mem at hc
  dsimp only [out]; omega

theorem run_last_readForest {w L initLast lastHandle branch curHeap vc ec
    lastMult stretchP levelTable branchTable d : ℕ} {fmt : Num.Format w}
    {lastTool : LastLevelTool} {Gd : MGraph} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rterm : DSRep (ℕ × (ℕ → LSF))} {opLast : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {s : ℕ × (ℕ → LSF)} {x : Rterm.τ}
    (himpl : Rterm.Implements w p initLast opLast
      (lastLevelRuntimeMachineContract fmt L lastTool Gd vc ec lastMult stretchP lastAlloc))
    (hrep : Rterm.rep lastHandle s x st.mem)
    (hfoot : ∀ a, Rterm.foot lastHandle x a → a < curHeap)
    (hbr : branch < s.1)
    (h3 : st.regs 3 = curHeap) (h29 : st.regs 29 = levelTable) (h30 : st.regs 30 = branchTable)
    (h31 : st.regs 31 = d)
    (hlhAt : st.mem (levelTable + d) = lastHandle)
    (hbrAt : st.mem (branchTable + d) = branch)
    (hlhW : levelTable + d < 2 ^ w) (hbrW : branchTable + d < 2 ^ w)
    (hhandleW : lastHandle < 2 ^ w) (hbrValW : branch < 2 ^ w)
    (hz : ZeroFrom st.mem curHeap)
    (hroom : curHeap + 4 < 2 ^ w) :
    ∃ out ret cost y,
      Runs w p ω (.call 3 (opLast 0) [.load (.bin .add (.reg 29) (.reg 31)),
        .load (.bin .add (.reg 30) (.reg 31)), .reg 3]) st .normal out cost ∧
      out.regs 3 = ret ∧ (∀ r ≠ 3, out.regs r = st.regs r) ∧
      Rterm.rep lastHandle s y out.mem ∧
      LSFAt out.mem curHeap vc ec fmt.limbBits L fmt.precision Gd.E (s.2 branch) ∧
      Rterm.Respects (Rterm.foot lastHandle x) curHeap 4 st.mem ret lastHandle y out.mem ∧
      cost + Rterm.phi lastHandle y out.mem ≤ 10 + 64 + Rterm.phi lastHandle x st.mem + 1 := by
  have hargs : evalArgs w st [.load (.bin .add (.reg 29) (.reg 31)),
      .load (.bin .add (.reg 30) (.reg 31)), .reg 3] =
      some [lastHandle, branch, curHeap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h29, h30, h31, h3, hlhW, hbrW, hlhAt, hbrAt]
  have hwords : ∀ a ∈ [lastHandle, branch, curHeap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre : (lastLevelRuntimeMachineContract fmt L lastTool Gd vc ec lastMult stretchP lastAlloc).pre
      0 s [lastHandle, branch, curHeap] st.mem :=
    ⟨rfl, lastHandle, branch, curHeap, rfl, hbr⟩
  obtain ⟨body, hbody, o, after, c, hr, s', y, hrep', hpost, hresp, hc⟩ :=
    himpl.2.2 0 lastHandle s x [lastHandle, branch, curHeap] st.mem st.pos ω
      hwords rfl hrep hpre hfoot hz (show curHeap + 4 < 2 ^ w from hroom)
  obtain ⟨_, hs', hlsf⟩ := hpost
  subst hs'
  let ret := o.value
  let out := { after with regs := Function.update st.regs 3 ret }
  refine ⟨out, ret, 9 + c + 1, y,
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hr, rfl, by cases o <;> rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, Function.update_of_ne hr],
    hrep', hlsf, hresp, ?_⟩
  change c + Rterm.phi lastHandle y after.mem ≤ 64 + Rterm.phi lastHandle x st.mem at hc
  dsimp only [out]; omega

end MinCostFlow.MinRatio
