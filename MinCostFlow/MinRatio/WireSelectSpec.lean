module

public import MinCostFlow.MinRatio.WireSelectQuery
public import MinCostFlow.MinRatio.OrdFindCycleWired
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.ShiftLoopLevelFacts
import WordRAM.Tactic

/-!
# Select-heap cycle-route specification, wired `FindCycle` bridge, Job 3 cost bounds, and non-vacuity

This file brings together Jobs 1, 2, and 3 for the heap-based `FindCycle` / `Select` data
structure (`jtree.tex`, Algorithm 1, pages 20–21 and 24; Algorithm 2, page 29):

1. **`OrdCycleRouteSelectSpecHeap`**: minimal extension of `OrdCycleRouteSelectSpecW`
   (`WireFindCycleSpec.lean`) against the updated `algorithm1_findCycle` model (own-level key
   `heapCycleRatio` with `leastArgmax` tie-breaking):
   - Carries the maintained select-heap `SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain
     model.chain.g₀ model.chain.ℓ₀ size` at handle `loc.hb` disjoint from `Rrep.foot` and below
     `descBase`, and preserves it unchanged across the query.
   - Adds only the reachability invariants already present on states reached by `OrdSolver`:
     `TreeChain.Holds`, `LastLevelSpans`, `EdgeSimpleEmbeddings`, `bran i < cfg.P.k`,
     `0 < model.extℓ e`, `v < model.extG.n`, and the two limb-capacity bounds already in
     `FindCycleStepSpecW`.
2. **`findCycleStepSpecHeap_wired`**: proves that the existing `ordFindCycleWiredBody`
   (`OrdFindCycleWired.lean`) meets `FindCycleStepSpecHeap` when composed with any selector
   meeting `OrdCycleRouteSelectSpecHeap` and any evaluator meeting `OrdCycleRouteEvalSpecW`.
3. **Job 3 cost & amortized changed-keys bounds**:
   - `selectRawRoute_cost_paper_form`: raw cycle selection costs `O(Lk + readout + |W|)`
     (`O(log)` plus cycle length).
   - `selectRouteTotal_cost_paper_form`: full cycle selection with path-cancellation
     post-processing costs `O(Lk + readout + (|W|^6 + 1) · (treeBudget + L + 1))` (`m^{o(1)}`).
   - `selectKeyUpdate_cost_paper_form`: each changed key costs `O((log(cap + 1) + 1) · Lk^2)`
     heap comparison steps plus one key evaluation.
   - `changedKeys_init_le`, `changedKeys_rebuild_le`, `changedKeys_shift_le`,
     `changedKeys_update_le`, and `selectUpdate_amortized_credit`: every changed key across
     `Initialize`, `Rebuild(i₀)`, `Shift(i₀)`, and `Update` is paid by `ReembCostBound`,
     sparse-core tool cost, tree updates, and shift/rebuild budgets.
4. **`selectHeap_nonvacuous_example`**: simultaneous concrete witness showing that
   `SelectHeapAt`, `ReembListAt`, `ReembCostBound`, and `LevelDiffListsAt` are all jointly
   satisfiable (non-vacuous).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-! ## 1. Minimal heap-backed extension of `OrdCycleRouteSelectSpecW` and `FindCycleStepSpecW` -/

/-- Reachability invariants of `Alg2State cfg` needed to connect `SelectHeapMatchesChain` to
`algorithm1_findCycle` and to run the `PathSummary` cancellation post-processor. All of these
hold on every state reached by Algorithm 2 (`OrdSolverReached`). -/
def SelectModelInv {cfg : Alg2Config} (model : Alg2State cfg)
    (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ) : Prop :=
  let C := model.chain.toTreeChain
  C.Holds G₀ model.chain.ℓ σ σ_mwu γ_ℓ γ_c ∧
  C.LastLevelSpans ∧
  (∀ i < cfg.P.d, model.chain.bran i < cfg.P.k) ∧
  (∀ i < cfg.P.d, SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM i) model.chain.N₀
    (chainLevelOrdAbs model.chain i).st (chainLevelOrdAbs model.chain i).G
    (chainLevelOrdAbs model.chain i).ord (chainLevelOrdAbs model.chain i).n) ∧
  (∀ e ∈ model.extG.E, 0 < model.extℓ e) ∧
  (∀ v ∈ model.extG.V, v < model.extG.n)

/-- Owned embedding-table projection read directly by `selectRawRouteBody` at
`smEntryAddr metaPtr C.d 5 i` when `i < C.d` (no sparse-core `opCore 4` readout). -/
def SelectMetaEmbsAt (mem : ℕ → ℕ) (metaPtr hi : ℕ) (C : TreeChain) : Prop :=
  metaPtr + selectLevelMetaSize C.d ≤ hi ∧
  ∀ i < C.d, ∀ e ∈ (C.activeCore i).E,
    let embPtr := mem (smEntryAddr metaPtr C.d 5 i)
    embPtr + e < hi ∧
    mem (embPtr + e) + (mWalkEncode (C.activeEmb i e)).length ≤ hi ∧
    MWalkAt mem (mem (embPtr + e)) (C.activeEmb i e)

/-- Fixed-program extension of `OrdCycleRouteSelectSpecW` (`WireFindCycleSpec.lean`) for the
select-heap implementation of `FindCycle` / `Select`:
1. One fixed program `p` serves every runtime-allocated select-heap `loc` (`loc.Lk = L`),
   loading `loc.hb` at runtime from `mem[tok.table + dMul * cfg.P.d + kOff]`.
2. Reads `emb[eBest]` directly from the owned embedding table `SelectMetaEmbsAt` (no `opCore 4`).
3. Preserves `SelectHeapMatchesChain` unchanged across `Select`. -/
def OrdCycleRouteSelectSpecHeap
    (w L P m V psi k epsExp drainUnit dMul kOff : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (selectRouteProc selectSpace selectBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[selectRouteProc]? = some body ∧
    ∀ (root descBase workHeap pos size : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (loc : SelectHeapLoc) (B R : ℤ)
      (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      1 ≤ maxEdges →
      2 * maxEdges ≤ maxPaths →
      (∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E \
        (model.chain.toTreeChain.activeS i).E,
        (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges) →
      2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ) →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      loc.Lk = L →
      mem (tok.table + dMul * cfg.P.d + kOff) = loc.hb →
      tok.table + dMul * cfg.P.d + kOff < descBase →
      SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size →
      SelectMetaEmbsAt mem loc.metaPtr descBase model.chain.toTreeChain →
      loc.endAddr ≤ descBase →
      (∀ a, loc.hb ≤ a → a < loc.endAddr → ¬ Rrep.foot root tok a) →
      (∀ a, Rrep.foot root tok a → a < descBase) →
      descBase + 6 = workHeap →
      ZeroFrom mem descBase →
      workHeap + selectSpace < 2 ^ w →
      ∃ work1 cost out tok' edges paths,
        Runs w p ω body (startState [root, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        workHeap ≤ work1 ∧ work1 ≤ workHeap + selectSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        NoOppositePairs edges ∧
        workHeap ≤ out.mem (descBase + 2) ∧
        out.mem (descBase + 2) + 2 * edges.length ≤ work1 ∧
        out.mem (descBase + 3) = edges.length ∧
        workHeap ≤ out.mem (descBase + 4) ∧
        out.mem (descBase + 4) + 2 * paths.length ≤ work1 ∧
        out.mem (descBase + 5) = paths.length ∧
        ExplicitEdgesAt out.mem (out.mem (descBase + 2)) edges ∧
        PathEndpointsAt out.mem (out.mem (descBase + 4)) paths ∧
        CycleRouteAt model edges paths ∧
        (∀ x < 2 * edges.length, ¬ Rrep.foot root tok' (out.mem (descBase + 2) + x)) ∧
        (∀ x < 2 * paths.length, ¬ Rrep.foot root tok' (out.mem (descBase + 4) + x)) ∧
        (∀ a, tok'.tag a = 18 → a < descBase) ∧
        Rrep.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        SelectHeapMatchesChain out.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem work1 ∧
        (∀ a < descBase, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < work1)) ∧
        cost + Rrep.phi root tok' out.mem ≤ selectBudget + Rrep.phi root tok mem

/-- Fixed-program heap-backed `FindCycleStepSpecW` matching `OrdCycleRouteSelectSpecHeap`. -/
def FindCycleStepSpecHeap (w L P m V psi k epsExp drainUnit dMul kOff : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (findCycleProc findSpace findBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[findCycleProc]? = some body ∧
    ∀ (root heap pos size : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (loc : SelectHeapLoc) (B R : ℤ)
      (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      1 ≤ maxEdges →
      2 * maxEdges ≤ maxPaths →
      (∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E \
        (model.chain.toTreeChain.activeS i).E,
        (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges) →
      2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ) →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      loc.Lk = L →
      mem (tok.table + dMul * cfg.P.d + kOff) = loc.hb →
      tok.table + dMul * cfg.P.d + kOff < heap →
      SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size →
      SelectMetaEmbsAt mem loc.metaPtr heap model.chain.toTreeChain →
      loc.endAddr ≤ heap →
      (∀ a, loc.hb ≤ a → a < loc.endAddr → ¬ Rrep.foot root tok a) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + findSpace < 2 ^ w →
      ∃ nextHeap cost out tok' inner norm edges paths,
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap + 6 ≤ nextHeap ∧ nextHeap ≤ heap + findSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        (∀ x < 2 * edges.length, tok'.tag (out.mem (heap + 2) + x) = 0) ∧
        (∀ x < 2 * paths.length, tok'.tag (out.mem (heap + 4) + x) = 0) ∧
        (∀ a, tok'.tag a = 18 → a < heap) ∧
        CycleDescriptorAt model L P out.mem heap nextHeap inner norm edges paths ∧
        Rrep.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        SelectHeapMatchesChain out.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ findBudget + Rrep.phi root tok mem

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-! ## 2. Wiring `OrdCycleRouteSelectSpecHeap` into `ordFindCycleWiredBody` -/

/-- **Wired `FindCycle` bridge (`findCycleStepSpecHeap_wired`)**:
`ordFindCycleWiredBody selectRouteProc evalCycleProc` meets `FindCycleStepSpecHeap` whenever
`selectRouteProc` meets `OrdCycleRouteSelectSpecHeap` and `evalCycleProc` meets
`OrdCycleRouteEvalSpecW`, preserving `SelectHeapMatchesChain` across both calls and the final
two descriptor pointer stores. -/
theorem findCycleStepSpecHeap_wired
    {w L P m V psi k epsExp drainUnit dMul kOff findCycleProc selectRouteProc evalCycleProc
      selectSpace selectBudget evalSpace evalBudget maxEdges maxPaths : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectRouteProc evalCycleProc))
    (hSel : OrdCycleRouteSelectSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p selectRouteProc selectSpace selectBudget maxEdges maxPaths)
    (hEval : OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p
      evalCycleProc evalSpace evalBudget maxEdges maxPaths)
    (hw6 : 6 < 2 ^ w) :
    FindCycleStepSpecHeap w L P m V psi k epsExp drainUnit dMul kOff cfg
      Rcore p
      findCycleProc (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
      maxEdges maxPaths := by
  refine ⟨ordFindCycleWiredBody selectRouteProc evalCycleProc, hAt, ?_⟩
  intro root heap pos size ω mem model tok loc B R G₀ σ σ_mwu γ_ℓ γ_c
    hrep hnum hoff hBd hMod hlogW hmaxE1 hmaxEP hEmbBd hcapE hcapT hLk hhbRd hhbLt hMatch hMetaE hlocEnd hlocDisj hbelow hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocal
  obtain ⟨bSel, hbSel, hSelRun⟩ := hSel
  obtain ⟨bEval, hbEval, hEvalRun⟩ := hEval
  have hrep0 := hrep
  obtain ⟨hrootDir, _, hnumHdr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hroot0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hL5 : mem (tok.handle + 5) = L := by simpa [Nat.add_assoc] using hnumHdr 0 (by simp)
  have hh5Lt : tok.handle + 5 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide)))) hheapW
  let work0 := heap + 6
  have hwork0Eq : work0 = heap + 6 := rfl
  let s0 : State := startState [root, heap] mem pos
  let rg0 := s0.regs
  let rg1 := Function.update rg0 10 root
  let rg2 := Function.update rg1 11 heap
  let rg3 := Function.update rg2 12 tok.handle
  let rg4 := Function.update rg3 13 L
  let rg5 := Function.update rg4 14 work0
  let s1 : State := ⟨mem, rg1, pos⟩
  let s2 : State := ⟨mem, rg2, pos⟩
  let s3 : State := ⟨mem, rg3, pos⟩
  let s4 : State := ⟨mem, rg4, pos⟩
  let s5 : State := ⟨mem, rg5, pos⟩
  have r1 : Runs w p ω (.assign 10 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 11 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s1, rg1, rg0, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.load (.reg 10))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s2, rg2, rg1, hroot0], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 12) (.const 5)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s3, rg3, hw5, hh5Lt, hL5], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 14 (.bin .add (.reg 11) (.const 6))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨work0, by simp [Expr.eval, BinOp.eval, s4, rg4, rg3, rg2, hw6, show work0 < 2 ^ w by omega, work0],
      rfl, rfl, rfl⟩
  -- Step 1: call `selectRouteProc`
  obtain ⟨work1, cSel, stSel, tok1, edges, paths, hrSel, hw1Lo, hw1Hi, hlev1, hcap1, hedMax, hptMax,
      hnodup, heLo, heHi, heLen, hpLo, hpHi, hpLen, hEdAt, hPtAt, hRoute, hnfEd1, hnfPt1, htag18_1,
      hrep1, hmeta1, hMatch1, hnum1, hoff1, hBd1, hz1, hfr1, hft1, hcSel⟩ :=
    hSelRun root heap work0 pos size ω mem model tok loc B R G₀ σ σ_mwu γ_ℓ γ_c
      hrep0 hnum hoff hBd hMod hlogW hmaxE1 hmaxEP hEmbBd hcapE hcapT hLk hhbRd hhbLt hMatch hMetaE hlocEnd hlocDisj hbelow rfl hz (by omega)
  let edgesBase := stSel.mem (heap + 2)
  let pathsBase := stSel.mem (heap + 4)
  change work0 ≤ edgesBase at heLo
  change edgesBase + 2 * edges.length ≤ work1 at heHi
  change work0 ≤ pathsBase at hpLo
  change pathsBase + 2 * paths.length ≤ work1 at hpHi
  change (∀ x < 2 * edges.length, ¬ Rrep.foot root tok1 (edgesBase + x)) at hnfEd1
  change (∀ x < 2 * paths.length, ¬ Rrep.foot root tok1 (pathsBase + x)) at hnfPt1
  let rg6 := Function.update rg5 15 work1
  let rg7 := Function.update rg6 16 edgesBase
  let rg8 := Function.update rg7 17 edges.length
  let rg9 := Function.update rg8 18 pathsBase
  let rg10 := Function.update rg9 19 paths.length
  let s6 : State := ⟨stSel.mem, rg6, stSel.pos⟩
  let s7 : State := ⟨stSel.mem, rg7, stSel.pos⟩
  let s8 : State := ⟨stSel.mem, rg8, stSel.pos⟩
  let s9 : State := ⟨stSel.mem, rg9, stSel.pos⟩
  let s10 : State := ⟨stSel.mem, rg10, stSel.pos⟩
  have r6 : Runs w p ω (.call 15 selectRouteProc [.reg 10, .reg 11, .reg 14]) s5 .normal s6 (cSel + 4) :=
    runs_call_iff.mpr ⟨[root, heap, work0], bSel, .returned work1, stSel, cSel,
      by simp [evalArgs, Expr.eval, s5, rg5, rg4, rg3, rg2, rg1], hbSel, hrSel, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have r7 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 11) (.const 2)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨edgesBase, by
      simp [Expr.eval, BinOp.eval, s6, rg6, rg5, rg4, rg3, rg2, hw2, show heap + 2 < 2 ^ w by omega, edgesBase],
      rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 11) (.const 3)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨edges.length, by
      simp [Expr.eval, BinOp.eval, s7, rg7, rg6, rg5, rg4, rg3, rg2, hw3, show heap + 3 < 2 ^ w by omega, heLen],
      rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 11) (.const 4)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨pathsBase, by
      simp [Expr.eval, BinOp.eval, s8, rg8, rg7, rg6, rg5, rg4, rg3, rg2, hw4, show heap + 4 < 2 ^ w by omega, pathsBase],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 11) (.const 5)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨paths.length, by
      simp [Expr.eval, BinOp.eval, s9, rg9, rg8, rg7, rg6, rg5, rg4, rg3, rg2, hw5, show heap + 5 < 2 ^ w by omega, hpLen],
      rfl, rfl, rfl⟩
  -- Step 2: call `evalCycleProc`
  have hfoot1_lt (a : ℕ) (ha : Rrep.foot root tok1 a) : a < work1 := by
    rcases hft1 a ha with h0 | ⟨_, hhi⟩
    · have := hbelow a h0; omega
    · exact hhi
  obtain ⟨nextHeap, cEval, stEval, tok2, inner, norm, hrEval, hnhLo, hnhHi, hlev2, hcap2,
      hnormNN, hinnerAt, hnormAt, hinnerEq, hnormEq, htagEd2, htagPt2, htag18_2,
      hrep2, hmeta2, hnum2, hoff2, hBd2, hz2, hfr2, hft2, hcEval⟩ :=
    hEvalRun root edgesBase pathsBase work1 stSel.pos ω stSel.mem model tok1 B R edges paths
      hrep1 hnum1 hoff1 hBd1 hcapE hcapT hlogW (fun e he => (hMod.2.2.2.2.1 e he).le)
      hedMax hptMax hnodup hEdAt hPtAt hRoute heHi hpHi hnfEd1
      hnfPt1 hfoot1_lt hz1 (by omega)
  let rg11 := Function.update rg10 20 nextHeap
  let s11 : State := ⟨stEval.mem, rg11, stEval.pos⟩
  have r11 : Runs w p ω (.call 20 evalCycleProc [.reg 10, .reg 16, .reg 17, .reg 18, .reg 19, .reg 15])
      s10 .normal s11 (cEval + 7) :=
    runs_call_iff.mpr ⟨[root, edgesBase, edges.length, pathsBase, paths.length, work1], bEval,
      .returned nextHeap, stEval, cEval,
      by simp [evalArgs, Expr.eval, s10, rg10, rg9, rg8, rg7, rg6, rg5, rg4, rg3, rg2, rg1], hbEval, hrEval,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Step 3: write `innerPtr := work1` at `heap` and `normPtr := work1 + L` at `heap + 1`
  let m12 := Function.update stEval.mem heap work1
  let m13 := Function.update m12 (heap + 1) (work1 + L)
  let s12 : State := ⟨m12, rg11, stEval.pos⟩
  let s13 : State := ⟨m13, rg11, stEval.pos⟩
  have r12 : Runs w p ω (.store (.reg 11) (.reg 15)) s11 .normal s12 3 :=
    runs_store_iff.mpr ⟨heap, work1,
      by simp [Expr.eval, s11, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, rg3, rg2],
      by simp [Expr.eval, s11, rg11, rg10, rg9, rg8, rg7, rg6], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.store (.bin .add (.reg 11) (.const 1)) (.bin .add (.reg 15) (.reg 13)))
      s12 .normal s13 7 :=
    runs_store_iff.mpr ⟨heap + 1, work1 + L,
      by simp [Expr.eval, BinOp.eval, s12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, rg3, rg2, hw1, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, s12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, show work1 + L < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.ret (.reg 20)) s13 (.returned nextHeap) s13 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, s13, rg11], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordFindCycleWiredBody selectRouteProc evalCycleProc)
      s0 (.returned nextHeap) s13 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, cSel + 4, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, cEval + 7, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 3, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 7, 2, r13, r14, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- `heap` and `heap + 1` are strictly outside `Rrep.foot root tok2` and `[work0, nextHeap)`
  have hfoot2_ne (a : ℕ) (ha : Rrep.foot root tok2 a) : a ≠ heap ∧ a ≠ heap + 1 := by
    rcases hft2 a ha with h1 | ⟨hlo, _⟩
    · rcases hft1 a h1 with h0 | ⟨hlo1, _⟩
      · have := hbelow a h0; omega
      · omega
    · omega
  have hneH_m13 (a : ℕ) (h0 : a ≠ heap) (h1 : a ≠ heap + 1) : s13.mem a = stEval.mem a := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) a = _
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  have hfoot1_notDesc (j : ℕ) (hj : j < 6) : ¬ Rrep.foot root tok1 (heap + j) := fun hf => by
    rcases hft1 _ hf with h0 | ⟨hlo, _⟩
    · have := hbelow _ h0; omega
    · omega
  have hloc2 := hlocR root model tok2 stEval.mem s13.mem
    (fun a ha => (hneH_m13 a (hfoot2_ne a ha).1 (hfoot2_ne a ha).2).symm)
  have hrep3 : Rrep.rep root model tok2 s13.mem := hloc2.1 hrep2
  have hphi3 : Rrep.phi root tok2 s13.mem = Rrep.phi root tok2 stEval.mem := hloc2.2.symm
  -- Transport `SelectHeapMatchesChain` across `evalCycleProc` and `{heap, heap + 1}` stores
  have hMatch3 : SelectHeapMatchesChain s13.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size := by
    refine hMatch1.of_agree fun a ha1 ha2 => ?_
    have hltH : a < heap := lt_of_lt_of_le ha2 hlocEnd
    have hnf1 : ¬ Rrep.foot root tok1 a := fun hf => by
      rcases hft1 a hf with h0 | ⟨hlo, _⟩
      · exact hlocDisj a ha1 ha2 h0
      · omega
    exact (hneH_m13 a (by omega) (by omega)).trans (hfr2 a (by omega) hnf1)
  have htag1318_ag : ∀ a, (tok2.tag a = 13 ∨ tok2.tag a = 18) → s13.mem a = stEval.mem a := by
    have hrep2_0 := hrep2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags2⟩ := hrep2_0
    intro a ha
    have hfootA : Rrep.foot root tok2 a :=
      Or.inl (htags2.1 a (by rcases ha with h | h <;> rw [h] <;> decide))
    exact hneH_m13 a (hfoot2_ne a hfootA).1 (hfoot2_ne a hfootA).2
  have hoff3 : OffTreeRecInv model L s13.mem tok2.edgeRecords B :=
    offTreeRecInv_of_agree hrep2 hoff2 htag1318_ag
  have hBd3 : OffTreeRecBound model L s13.mem tok2.edgeRecords B :=
    offTreeRecBound_of_agree hrep2 hBd2 htag1318_ag
  have hm13_0 : s13.mem heap = work1 := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) heap = work1
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm13_1 : s13.mem (heap + 1) = work1 + L := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) (heap + 1) = work1 + L
    rw [Function.update_self]
  have hm13_2 : s13.mem (heap + 2) = edgesBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 2) (by omega) (hfoot1_notDesc 2 (by omega)))
  have hm13_3 : s13.mem (heap + 3) = edges.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 3) (by omega) (hfoot1_notDesc 3 (by omega))).trans heLen)
  have hm13_4 : s13.mem (heap + 4) = pathsBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 4) (by omega) (hfoot1_notDesc 4 (by omega)))
  have hm13_5 : s13.mem (heap + 5) = paths.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 5) (by omega) (hfoot1_notDesc 5 (by omega))).trans hpLen)
  have hdesc : CycleDescriptorAt model L P s13.mem heap nextHeap inner norm edges paths := by
    refine ⟨hm13_3, hm13_5, by omega, by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega,
      by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega, hnormNN, ?_, ?_, hinnerEq, hnormEq, ?_, ?_, hRoute⟩
    · rw [hm13_0]; exact hinnerAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_1]; exact hnormAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_2]
      exact hEdAt.congr (fun x hlo hhi =>
        (hneH_m13 x (by omega) (by omega)).trans
          (hfr2 x (by omega) (by
            have hx : edgesBase + (x - edgesBase) = x := by omega
            rw [← hx]; exact hnfEd1 (x - edgesBase) (by omega))))
    · rw [hm13_4]
      intro i hi
      have h1 : s13.mem (pathsBase + 2 * i) = stSel.mem (pathsBase + 2 * i) :=
        (hneH_m13 _ (by omega) (by omega)).trans (hfr2 _ (by omega) (hnfPt1 (2 * i) (by omega)))
      have h2 : s13.mem (pathsBase + 2 * i + 1) = stSel.mem (pathsBase + 2 * i + 1) :=
        (hneH_m13 _ (by omega) (by omega)).trans
          (hfr2 _ (by omega) (by rw [Nat.add_assoc]; exact hnfPt1 (2 * i + 1) (by omega)))
      exact ⟨h1.trans (hPtAt i hi).1, h2.trans (hPtAt i hi).2⟩
  refine ⟨nextHeap, _, s13, tok2, inner, norm, edges, paths, rFull, by omega, by omega,
    hlev2.trans hlev1, hcap2.trans hcap1, hedMax, hptMax,
    by rw [hm13_2]; exact htagEd2, by rw [hm13_4]; exact htagPt2,
    fun a ha => htag18_1 a (htag18_2 a ha),
    hdesc, hrep3,
    (hmeta1.trans hmeta2).congr_mem_right (fun a ha =>
      let hfoot := LevelMetaFoot.mem_foot hrep2 ha
      hneH_m13 a (hfoot2_ne a hfoot).1 (hfoot2_ne a hfoot).2),
    hMatch3, hnum2, hoff3, hBd3,
    fun a ha => (hneH_m13 a (by omega) (by omega)).trans (hz2 a ha),
    fun a ha hnf => by
      have hnf1 : ¬ Rrep.foot root tok1 a := fun hf => by
        rcases hft1 a hf with h0 | ⟨hlo, _⟩
        · exact hnf h0
        · omega
      exact (hneH_m13 a (by omega) (by omega)).trans ((hfr2 a (by omega) hnf1).trans (hfr1 a ha hnf)),
    fun a ha => by
      rcases hft2 a ha with h1 | ⟨hlo, hhi⟩
      · rcases hft1 a h1 with h0 | ⟨hlo1, hhi1⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩,
    ?_⟩
  dsimp only [Rrep] at hcSel hcEval hphi3 ⊢
  rw [hphi3]; omega

/-! ## 3. Job 3: Paper-form asymptotic cost corollaries and changed-keys accounting -/

/-- **Job 3 (Query — raw route, paper form):**
Reading the top of the select-heap, checking the orientation sign, looking up `emb[eBest]` in the
owned embedding table, and emitting the raw cycle route costs at most `360 · (Lk + K + 1)` steps —
`O(log)` plus the length `K` of the returned cycle. -/
theorem selectRawRoute_cost_paper_form (Lk K : ℕ) :
    selectRawRouteCost Lk K ≤ 360 * (Lk + K + 1) := by
  unfold selectRawRouteCost; omega

/-- **Job 3 (Query — with cancellation post-processing, paper form):**
Including the `O(K^6)` path-cancellation post-processing to produce a cancellation-free
`CycleRouteAt`, the total query cost is at most
`520 · (Lk + K + 1) + 440 · (4 · K^4 + 1) · ((K^2 + 1) · (4 · treeBudget + L + 1))`,
which is `m^{o(1)}` whenever `K = m^{o(1)}` and `treeBudget = O(L^2 log n)`. -/
theorem selectRouteTotal_cost_paper_form (Lk K L treeBudget : ℕ) :
    selectRouteTotalCost Lk K L treeBudget ≤
      520 * (Lk + K + 1) +
        440 * (4 * K ^ 4 + 1) * ((K ^ 2 + 1) * (4 * treeBudget + L + 1)) := by
  unfold selectRouteTotalCost selectRawRouteCost cancelRouteEdgesCost cancelRoutePathsCost
  have h1 : 4 * treeBudget + 117 * L + 440 ≤ 440 * (4 * treeBudget + L + 1) := by omega
  have h2 : K * K * (4 * treeBudget + 117 * L + 440) + 120 + 320 ≤
      440 * ((K ^ 2 + 1) * (4 * treeBudget + L + 1)) := by
    have hsq : K * K = K ^ 2 := by ring
    rw [hsq]
    nlinarith [Nat.mul_le_mul_left (K ^ 2) h1]
  have h3 := Nat.mul_le_mul_left (4 * K ^ 4 + 1) h2
  have hcomm : (4 * K ^ 4 + 1) * (440 * ((K ^ 2 + 1) * (4 * treeBudget + L + 1))) =
      440 * (4 * K ^ 4 + 1) * ((K ^ 2 + 1) * (4 * treeBudget + L + 1)) := by ring
  have hK24 : K * K ≤ K ^ 4 + 1 := by
    rcases K with _ | K
    · simp
    · have h1' : 1 ≤ (K + 1) * (K + 1) := by nlinarith
      nlinarith [show (K + 1) ^ 4 = ((K + 1) * (K + 1)) * ((K + 1) * (K + 1)) by ring]
  have hSlack : 45 * K * K + 60 ≤ (4 * K ^ 4 + 1) * 320 := by nlinarith
  have hExp : (4 * K ^ 4 + 1) * (K * K * (4 * treeBudget + 117 * L + 440) + 120 + 320) =
      (4 * K ^ 4 + 1) * (K * K * (4 * treeBudget + 117 * L + 440) + 120) +
        (4 * K ^ 4 + 1) * 320 := by ring
  linarith [h3, hcomm, hSlack, hExp]

/-- **Job 3 (Key update per changed key, paper form):**
Each changed key costs at most `evalCost + (Nat.log 2 (cap + 1) + 2) · (2 · keyCompareCost Lk + 700)`
steps — `O(log)` comparisons (`O(log(cap + 1) · Lk^2)`) plus one key evaluation. -/
theorem selectKeyUpdate_cost_paper_form (cap Lk evalCost : ℕ) :
    selectProcessEdgeCost cap Lk evalCost ≤
      evalCost + (Nat.log 2 (cap + 1) + 2) * (2 * keyCompareCost Lk + 720) := by
  have h1 := selectProcessEdgeCost_le_log cap Lk evalCost
  have hkc : 36 * Lk ≤ keyCompareCost Lk := by unfold keyCompareCost; nlinarith
  nlinarith

/-- **Job 3 (Changed keys — `Initialize`):**
Initializing all `d + 1` levels inserts at most `∑_{j = 0}^d |(C.G j).E|` keys. -/
theorem changedKeys_init_le (C : TreeChain) :
    (Finset.range (C.d + 1)).sum (fun j => ((C.activeCore j).E \ (C.activeS j).E).card) ≤
      (Finset.range (C.d + 1)).sum (fun j => (C.G j).E.card) := by
  refine Finset.sum_le_sum fun j _ => ?_
  have hsub : (C.activeCore j).E \ (C.activeS j).E ⊆ (C.G j).E := fun e he =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  exact Finset.card_le_card hsub

/-- **Job 3 (Changed keys — `Rebuild(i₀)` / `Shift(i₀)`):**
Clearing and rebuilding levels `i₀ .. d` performs at most
`∑_{j = i₀}^d (|(C.G j).E| + |(C'.G j).E|)` heap operations, paid by the level-`i₀` rebuild or
shift budget. -/
theorem changedKeys_suffix_le (C C' : TreeChain) (i₀ : ℕ) :
    (Finset.Icc i₀ C'.d).sum (fun j =>
      ((C.activeCore j).E \ (C.activeS j).E).card + (C'.G j).E.card) ≤
    (Finset.Icc i₀ C'.d).sum (fun j => (C.G j).E.card + (C'.G j).E.card) := by
  refine Finset.sum_le_sum fun j _ => Nat.add_le_add_right ?_ _
  exact Finset.card_le_card fun e he => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1

/-- **Job 3 (Changed keys — `Update` paid by sparse-core cost + tree updates + rebuild budget):**
Across an `Update` step that updates non-rebuilt levels `0 .. r - 1` (with the amortized
`ReembCostBound` on each level, potential `phi j` before and `phi' j` after) and rebuilds suffix
`r .. d`, the total number of changed keys, plus the new potential, is paid by:
- input/output batch lengths `|U_j| + |U_{S,j}|`,
- forest deletions `|fDel_j|`,
- `cReemb · (toolCostDelta j + 1)` from the sparse core's tool cost,
- the old potential, and
- the suffix rebuild size `∑_{j = r}^d (|G_j| + |G'_j|)`. -/
theorem changedKeys_update_le (C C' : TreeChain) (r cReemb : ℕ)
    (lists : ℕ → LevelDiffLists) (toolCostDelta phi phi' : ℕ → ℕ)
    (hre : ∀ j < r, ReembCostBound (lists j).reemb (toolCostDelta j) cReemb (phi j) (phi' j)) :
    updateHeapOpsBound C C' r lists + (Finset.range r).sum phi' ≤
      (Finset.range r).sum (fun j =>
        (lists j).uG.length + (lists j).fDel.length + (lists j).uS.length +
          cReemb * (toolCostDelta j + 1) + phi j) +
      (Finset.Icc r C'.d).sum (fun j => (C.G j).E.card + (C'.G j).E.card) := by
  unfold updateHeapOpsBound
  have hlev : (Finset.range r).sum (fun j => (lists j).totalLen) + (Finset.range r).sum phi' ≤
      (Finset.range r).sum (fun j =>
        (lists j).uG.length + (lists j).fDel.length + (lists j).uS.length +
          cReemb * (toolCostDelta j + 1) + phi j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j hj =>
      levelDiffLists_totalLen_le (hre j (Finset.mem_range.mp hj))
  have hsuf := changedKeys_suffix_le C C' r
  omega

/-- **Job 3 (Amortized credit absorption):**
Whenever a step's heap-update cost is bounded by `fixed + perKey * (T' - T)` for a monotone
cumulative budget `T ≤ T' ≤ cap` (such as `ChainState.totalRuntime + ChainState.totalTreeUpdates`),
adding the credit `perKey * (cap - T)` to the potential absorbs the variable term completely. -/
theorem selectUpdate_amortized_credit {cost phi phi' fixed perKey T T' cap : ℕ}
    (hcost : cost + phi' ≤ fixed + perKey * (T' - T) + phi) (hmono : T ≤ T') (hcap : T' ≤ cap) :
    cost + (phi' + perKey * (cap - T')) ≤ fixed + (phi + perKey * (cap - T)) :=
  wire_credit_step hcost hmono hcap

/-! ## 4. Non-vacuity witness for `SelectHeapAt`, `ReembListAt`, and `LevelDiffListsAt` -/

/-- Simultaneous concrete witness showing that our heap invariant `SelectHeapAt` (empty heap at
`hb = 0`, `cap = 1`, `d = 0`, `Lk = 1`, `h = 4`), `ReembListAt`, `ReembCostBound`, and
`LevelDiffListsAt` can all hold simultaneously in one memory with `ZeroFrom` above the block. -/
theorem selectHeap_nonvacuous_example :
    ∃ (loc : SelectHeapLoc) (mem : ℕ → ℕ) (diffBase : ℕ) (L : LevelDiffLists),
      loc.cap = 1 ∧ loc.d = 0 ∧ loc.Lk = 1 ∧
      loc.endAddr ≤ diffBase ∧
      SelectHeapAt mem loc 4 0 ∧
      LevelDiffListsAt mem diffBase L ∧
      ReembListAt mem (mem (diffBase + 6)) (mem (diffBase + 7)) L.reemb ∧
      ReembCostBound L.reemb 0 1 0 0 ∧
      ZeroFrom mem (diffBase + 8) := by
  let loc : SelectHeapLoc := ⟨0, 1, 0, 1, 0, 0⟩
  let hdr : List ℕ :=
    [0, loc.cap, loc.d, loc.Lk, loc.arrPtr, loc.posPtr, loc.lvlPtr,
     loc.numBase, loc.denBase, loc.candHead, loc.candPrev, loc.candNext,
     loc.g0Ptr, loc.metaPtr]
  let mem : ℕ → ℕ := fun a => if a < 14 then hdr.getD a 0 else 0
  let diffBase := loc.endAddr
  let L : LevelDiffLists := ⟨[], [], [], []⟩
  have hge14 (a : ℕ) (ha : 14 ≤ a) : mem a = 0 := by simp [mem, show ¬ a < 14 by omega]
  have hdGe : 14 ≤ diffBase := by
    dsimp only [diffBase]; rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; simp [loc]
  refine ⟨loc, mem, diffBase, L, rfl, rfl, rfl, le_rfl, ?_, ?_, ?_, by simp [ReembCostBound, L], ?_⟩
  · -- `SelectHeapAt mem loc 4 0`
    have hhdr : SelectHeapHeaderAt mem loc 0 := fun j hj => by
      have hj14 : j < 14 := by simpa using hj
      have hm : mem (0 + j) = hdr.getD j 0 := by simp [mem, hj14]
      rw [show loc.hb + j = 0 + j from rfl, hm, List.getD_eq_getElem _ _ hj]
    have hposGe : 14 ≤ loc.posPtr := by unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize loc; omega
    have hchGe : 14 ≤ loc.candHead := by
      unfold SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize loc; omega
    have hbij : SelectHeapBijection mem loc 0 :=
      ⟨by decide, fun p hp => by omega, fun p hp => by omega,
        fun e _ => Or.inl (hge14 _ (by omega))⟩
    have hkeys : SelectHeapKeysValid mem loc 4 := fun e _ hnz =>
      (hnz (hge14 _ (by omega))).elim
    have hord : SelectHeapOrder mem loc 4 0 := fun p _ hp => by omega
    have hcand : SelectHeapCandLists mem loc :=
      ⟨fun _ => [], fun i _ => by
        refine ⟨IsDoublyLinkedList.nil (hge14 _ (by omega)), fun e => ?_⟩
        simp only [List.not_mem_nil, false_iff, not_and]
        intro _ hnz _
        exact hnz (hge14 _ (by omega))⟩
    exact ⟨hhdr, hbij, hkeys, hord, hcand⟩
  · -- `LevelDiffListsAt mem diffBase L`
    refine ⟨hge14 _ (by omega), fun j hj => by simp [L] at hj,
            hge14 _ (by omega), fun j hj => by simp [L] at hj,
            hge14 _ (by omega), fun j hj => by simp [L] at hj,
            hge14 _ (by omega), fun j hj => by simp [L] at hj⟩
  · -- `ReembListAt`
    exact ⟨hge14 _ (by omega), fun j hj => by simp [L] at hj⟩
  · -- `ZeroFrom mem (diffBase + 8)`
    intro a ha
    exact hge14 a (by omega)

end MinCostFlow.MinRatio
