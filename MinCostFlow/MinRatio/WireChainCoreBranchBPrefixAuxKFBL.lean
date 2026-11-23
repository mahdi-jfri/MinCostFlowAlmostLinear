module

public import MinCostFlow.MinRatio.WireChainCoreZeroInsKFBL
public import MinCostFlow.MinRatio.WireChainCorePreAux
public import MinCostFlow.MinRatio.WireChainCoreBatch
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Tools for the start of Branch B (`WireChainCoreBranchBPrefixAuxKFBL`)

Branch B of the chain-update core starts with the first sync of the path tree, which cuts the
deleted names of the batch that are on the tree. The emitter of the cuts tests the slot of each
deleted name. A batch may refresh an edge twice: it then deletes the old name, inserts a fresh
name, deletes that fresh name, and inserts another. The slot of a fresh name is not known, so the
core first writes `0` at the slots of the inserted names, and the emitter skips them.

This file gives the facts that this step needs.
- `batchDeletedEdges_mem_or_inserted`: in a valid batch, a deleted name is an edge of the start
  graph or a name that the batch inserts.
- `batchDeletedEdges_filter`: the deleted names of a batch that lie in a set, as a filter of the
  list of deleted names (the form that the sync needs) and as the `filterMap` of
  `translateBatch_oldId_facts`.
- `wireZeroInsStmt_runs`: the run of the call that writes `0` at the slots of the inserted names.
- `branchB_batchWords_lt`: the words of the batch of internal updates fit in a machine word, since
  each is a tag, the length of the batch, a name below the table size or a vertex of the root
  graph.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- In a valid batch, each deleted name is an edge of the start graph or is inserted by the batch.
A deletion removes an edge of the current graph, and the only edges that the current graph has
beyond those of the start graph are inserted ones. -/
theorem batchDeletedEdges_mem_or_inserted :
    ∀ (G : MGraph) (U : List Update), G.BatchIsValid U →
      ∀ e ∈ batchDeletedEdges U, e ∈ G.E ∨ e ∈ batchInsertedEdges U
  | _, [], _, e, he => by simp [batchDeletedEdges] at he
  | G, .insert e' x y :: rest, hV, e, he => by
      simp only [batchDeletedEdges] at he
      rcases batchDeletedEdges_mem_or_inserted _ rest hV.2 e he with h | h
      · simp only [MGraph.applyUpdate, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact Or.inr (by simp [batchInsertedEdges])
        · exact Or.inl h
      · exact Or.inr (by simp [batchInsertedEdges, h])
  | G, .delete e' :: rest, hV, e, he => by
      simp only [batchDeletedEdges, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl hV.1
      · rcases batchDeletedEdges_mem_or_inserted _ rest hV.2 e he with h | h
        · simp only [MGraph.applyUpdate, Finset.mem_erase] at h
          exact Or.inl h.2
        · exact Or.inr (by simpa [batchInsertedEdges] using h)
  | G, .split v v' St Sh :: rest, hV, e, he => by
      simp only [batchDeletedEdges] at he
      rcases batchDeletedEdges_mem_or_inserted _ rest hV.2 e he with h | h
      · exact Or.inl (by simpa [MGraph.applyUpdate] using h)
      · exact Or.inr (by simpa [batchInsertedEdges] using h)

/-- The deleted names of a batch that lie in `S`, as a filter of `batchDeletedEdges` and as a
`filterMap` over the batch. -/
theorem batchDeletedEdges_filter (S : Finset ℕ) : ∀ U : List Update,
    (batchDeletedEdges U).filter (fun e => decide (e ∈ S)) =
      U.filterMap (fun u => match u with
        | .delete ei => if ei ∈ S then some ei else none
        | _ => none)
  | [] => rfl
  | .insert _ _ _ :: rest => by
      simp [batchDeletedEdges, batchDeletedEdges_filter S rest]
  | .delete e :: rest => by
      by_cases h : e ∈ S <;>
        simp [batchDeletedEdges, h, batchDeletedEdges_filter S rest]
  | .split _ _ _ _ :: rest => by
      simp [batchDeletedEdges, batchDeletedEdges_filter S rest]

/-- Write `0` at the slots of the inserted names of the batch at `reg 87`; the slot table is word
`6` of the root directory (`reg 70`). -/
@[expose] def wireZeroInsStmt (zeroIns : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 70) (.const 6))) ;;
  .call 14 zeroIns [.reg 87, .reg 15]

theorem wireZeroInsStmt_noRand (zeroIns : ℕ) : (wireZeroInsStmt zeroIns).NoRand := by
  simp [wireZeroInsStmt, Stmt.NoRand]

/-- The run of `wireZeroInsStmt`: the slots of the inserted names become `0`, no other word
changes, and only `reg 14` and `reg 15` change. -/
theorem wireZeroInsStmt_runs {w root uIntBuf slots totalWords zeroIns : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State} {G : MGraph} {U : List Update}
    (hProc : p.procs[zeroIns]? = some wireZeroInsertSlotsBody)
    (hSmall : SmallBatchAt st.mem uIntBuf G U totalWords)
    (hEdgeOnly : ∀ u ∈ U, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < totalWords, st.mem (uIntBuf + j) < 2 ^ w)
    (hSlotLt : ∀ e ∈ batchInsertedEdges U, slots + e < uIntBuf)
    (hRoom : uIntBuf + totalWords < 2 ^ w) (hw : 6 < 2 ^ w)
    (hRegs : st.regs 70 = root ∧ st.regs 87 = uIntBuf) (hSlotsAt : st.mem (root + 6) = slots)
    (hRootW : root + 6 < 2 ^ w) :
    ∃ out cost, Runs w p ω (wireZeroInsStmt zeroIns) st .normal out cost ∧
      cost ≤ 50 * U.length + 45 ∧
      (∀ r, r ≠ 14 → r ≠ 15 → out.regs r = st.regs r) ∧
      (∀ e ∈ batchInsertedEdges U, out.mem (slots + e) = 0) ∧
      (∀ a, (∀ e ∈ batchInsertedEdges U, a ≠ slots + e) → out.mem a = st.mem a) := by
  obtain ⟨hr70, hr87⟩ := hRegs
  let s1 := { st with regs := Function.update st.regs 15 slots }
  have r1 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 70) (.const 6)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨slots, by
      simp [Expr.eval, BinOp.eval, hr70, show 6 < 2 ^ w by omega, hRootW, hSlotsAt],
      rfl, rfl, rfl⟩
  obtain ⟨outZ, cZ, rZ, hcZ, hZero, hFrZ⟩ :=
    wireZeroInsertSlotsBody_runs (w := w) (slots := slots) (p := p) (ω := ω) (pos := s1.pos)
      hSmall hEdgeOnly hBatchW hSlotLt hRoom (by omega)
  let s2 : State := { regs := Function.update s1.regs 14 0, mem := outZ.mem, pos := outZ.pos }
  have r2 : Runs w p ω (.call 14 zeroIns [.reg 87, .reg 15]) s1 .normal s2 (2 + cZ + 1) :=
    runs_call_iff.mpr ⟨[uIntBuf, slots], wireZeroInsertSlotsBody, .returned 0, outZ, cZ,
      by simp [evalArgs, Expr.eval, s1, hr87], hProc, rZ, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
  refine ⟨s2, 5 + (2 + cZ + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1, r2, rfl⟩),
    by omega, fun r h14 h15 => ?_, hZero, hFrZ⟩
  simp [s2, s1, Function.update_of_ne h14, Function.update_of_ne h15]

/-- The words of the batch of internal updates at `uIntBuf` fit in a machine word. Each word is the
length of the batch, a tag, a name below the size of the name tables, or a vertex of the root
graph, and the name tables and the root graph lie below `uIntBuf`. -/
theorem branchB_batchWords_lt
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec root uIntBuf bW g l : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hRef : RefreshBatch model.extG U)
    (hTrNfLe :
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.1 ≤
        tok.intCap)
    (hBatchMem : IPM.Machine.BatchAt mem uIntBuf
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2)
    (hSmallMem : SmallBatchAt mem uIntBuf (model.chain.G 0)
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2 bW)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUW : uIntBuf < 2 ^ w) (hLenW : U.length < 2 ^ w) :
    ∀ t < bW, mem (uIntBuf + t) < 2 ^ w := by
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set U_int := tr.2.2.2.2
  set G0 := model.chain.G 0
  obtain ⟨_, _, _, _, hFreshInv, _, _, ⟨_, hIntCapPos, _, _⟩, _, _, _, _, _, _, _, _, _, _,
    hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, _, _, _, _, _, _, _, _, _, _, _, hT12, _, _, _, _, _, _, hT20, _⟩ := hTags0
  obtain ⟨_, hRootG0, _, _, _⟩ := hWire0
  obtain ⟨_, _, _, _, _, _, _, _, _, hBatchCaps, _, _, _, _, _⟩ := hModelInv
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  obtain ⟨_, _, hEdgeInt, _, _⟩ := refreshBatch_edge_dichotomy hFreshInv hRef
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    cases u with
    | insert _ _ _ | delete _ => trivial
    | split _ _ _ _ => exact hRef.2.2 _ hu
  have hULenEq : U_int.length = U.length :=
    translateBatch_length_eq U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
  obtain ⟨_, _, hRangeAll, _, _⟩ :=
    translateBatch_oldId_facts U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFreshInv hRef.1 hEdgeU
  obtain ⟨_, _, hG0Valid, _, _, _, _⟩ :=
    translateBatch_preserves U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFreshInv hRef.1
  have hThrEnd : tok.edgeThresholds + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT12 (tok.intCap - 1) (by omega)]; decide); omega
  have hRGEnd : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ uIntBuf := by
    have hpos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
    have := htagLt (by
      rw [hT20 (tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1) (by omega)
        (by omega)]; decide)
    omega
  have hDgSz : 4 + 7 * model.extG.n + 9 * tok.rootECap =
      dynGraphSize model.extG.n tok.rootECap := rfl
  have hBatchLenEq : (batchWords U_int).length = bW :=
    smallBatchAt_batchWords_len_eq hSmallMem hEdgeInt
  intro t ht
  rw [hBatchMem t (hBatchLenEq.symm ▸ ht)]
  set x := (batchWords U_int)[t]'(hBatchLenEq.symm ▸ ht)
  have hMemB : x ∈ batchWords U_int := List.getElem_mem _
  simp only [batchWords, List.mem_cons, List.mem_flatMap] at hMemB
  rcases hMemB with hLen | ⟨u, hu, hwu⟩
  · rw [hLen, hULenEq]; exact hLenW
  · have hCapU := hBatchCaps u hu
    have hEU := hEdgeInt u hu
    have hR := hRangeAll u hu
    have hIV := batchIsValid_insert_vert_lt U_int G0 hG0Valid hEdgeInt hRootG0.2.1 u hu
    cases hU : u with
    | insert ei u' v' =>
      rw [hU] at hCapU hIV hwu
      simp only [UpdateWithinCaps] at hCapU
      simp only [updateWords, List.mem_cons, List.not_mem_nil, or_false] at hwu
      rcases hwu with h | h | h | h <;> (rw [h]; omega)
    | delete ei =>
      rw [hU] at hR hwu
      have hR' : ei < tr.2.2.2.1 := hR
      simp only [updateWords, List.mem_cons, List.not_mem_nil, or_false] at hwu
      rcases hwu with h | h <;> (rw [h]; omega)
    | split _ _ _ _ => rw [hU] at hEU; exact hEU.elim

end MinCostFlow.MinRatio
