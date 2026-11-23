module

public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.WireChainCoreAlgebra
public import MinCostFlow.MinRatio.WireChainCoreBatch
public import MinCostFlow.MinRatio.WireChainCoreFilter
public import MinCostFlow.MinRatio.WireChainCoreRefreshLoop
public import MinCostFlow.MinRatio.WireChainCoreLens
public import MinCostFlow.MinRatio.WireChainCoreReady
public import MinCostFlow.MinRatio.WireChainCoreCompact
public import MinCostFlow.MinRatio.WireShiftDeepSteps
public import MinCostFlow.MinRatio.RebuildGuard
public import MinCostFlow.MinRatio.OrdSortedEnds
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# Shared operations, Phase 0 init, and envelopes for `ordChainUpdateCoreBody` (`WireChainCoreOps`)

Provides:
1. `emptyMGraph` and `dynGraphAt_empty_of_zero`: zero-word empty `DynGraphAt` for Branch A sync.
2. `UpdateCoreOpsHyp`: implementation-level readout placement, space, and cost domination envelopes
   for sparse-core ops `0, 2, 3, 5`, `init`, and `lastInit` across both Branch A and Branch B.
3. `updateCoreInitRegs` and `updateCoreInitRegs_runs`: Phase 0 register initialization (`regs 70..95`)
   and reservation of `oldPtrs`, `newPtrs`, `emptyPtrs`, and `emptyGraphPtr`.
4. `collectCopyLSFForestsLoop` and `collectCopyLSFForestsLoop_runs`: copies every level `0..d-1`'s
   active LSF forest via `copyGraphFromHeader` so in-place op-`0` updates cannot overwrite `oldPtrs`.
5. `wireZeroUpdCountLoop` and `wireZeroUpdCountLoop_runs`: zeroes `updCount[first..d-1]` after a
   periodic suffix rebuild.
6. `wireFillEmptyPtrsLoop` and `wireFillEmptyPtrsLoop_runs`: fills `emptyPtrs[0..d]` with
   `emptyGraphPtr`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-! ### 1. Empty graph helper -/

/-- Canonical empty `MGraph` with `V = ∅` and `E = ∅`. -/
@[expose] def emptyMGraph : MGraph :=
  { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

/-- Any 4 zero words represent `emptyMGraph` with capacities `(0, 0)`. -/
theorem dynGraphAt_empty_of_zero {mem : ℕ → ℕ} {a : ℕ}
    (h0 : mem a = 0) (h1 : mem (a + 1) = 0) (h2 : mem (a + 2) = 0) (h3 : mem (a + 3) = 0) :
    DynGraphAt mem a 0 0 emptyMGraph := by
  refine ⟨fun _ he => by simp [emptyMGraph] at he, fun _ hv => by simp [emptyMGraph] at hv,
    fun _ he => by simp [emptyMGraph] at he,
    by simpa [dgVCapOff] using h0, by simpa [dgECapOff] using h1,
    by simpa [dgNOff, MGraph.n, emptyMGraph] using h2,
    by simpa [dgMOff, MGraph.m, emptyMGraph] using h3,
    fun _ hv => by omega,
    ⟨[], by simp [MGraph.n, emptyMGraph], List.nodup_nil, fun _ => by simp [emptyMGraph],
      fun _ hj => by simp at hj, fun _ hi => by simp at hi⟩,
    fun _ hv => by simp [emptyMGraph] at hv,
    fun _ hv => by simp [emptyMGraph] at hv,
    fun _ he => by omega,
    ⟨[], by simp [MGraph.m, emptyMGraph], List.nodup_nil, fun _ => by simp [emptyMGraph],
      fun _ hj => by simp at hj, fun _ hi => by simp at hi⟩,
    fun _ he => by simp [emptyMGraph] at he,
    ⟨fun _ => [], fun _ hs => by omega⟩⟩

/-! ### 2. Operational placement, space, and cost domination hypotheses -/

/-- Implementation-level readout placement, space, and cost domination hypotheses for
`ordChainUpdateCoreBody` across both Branch A (level-0 rebuild) and Branch B (level update loop). -/
structure UpdateCoreOpsHyp
    {w L P m capExp lastMul intCapMax forestEdgeCap drainUnit : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (dgCap ecCap : ℕ) (levelSpace levelCost updStepSpace updStepCost : ℕ → ℕ)
    (lastSpace termUpdSpace termUpdCost : ℕ) : Prop where
  /-- Op `0` (`update`) `BranchOutAt` child batch/edits placement inside `[h, ret)`. -/
  op0Placement : ∀ (handle : ℕ) (y : Rcore.τ) (mem : ℕ → ℕ) (h ret k j : ℕ)
    (oldGraphs : ℕ → MGraph) (batches : ℕ → List Update) (oldRot newRot : ℕ → ℕ → List End),
    BranchOutAt mem h k oldGraphs batches oldRot newRot → j < k →
    let base := h + 1 + 4 * j
    let bPtr := mem base
    let bW := mem (base + 1)
    let ePtr := mem (base + 2)
    let eW := mem (base + 3)
    h + 1 + 4 * j + 3 < ret ∧
    h ≤ bPtr ∧ bPtr + bW ≤ ret ∧ h ≤ ePtr ∧ ePtr + eW ≤ ret ∧
    (∀ t < bW, mem (bPtr + t) < 2 ^ w) ∧ (∀ t < eW, mem (ePtr + t) < 2 ^ w) ∧
    (∀ t < bW, ¬ Rcore.foot handle y (bPtr + t)) ∧
    (∀ t < eW, ¬ Rcore.foot handle y (ePtr + t)) ∧
    (decodeBatch mem bPtr (oldGraphs j)).1 = batches j
  /-- Op `2` (`readLSF`) forest & stretch pointer placement and graph-size cap. -/
  op2Placement : ∀ (G : MGraph) (handle : ℕ) (x : Rcore.τ) (mem : ℕ → ℕ)
    (h ret vcF ecF Lw : ℕ) (forest : LSF),
    LSFAt mem h vcF ecF 4 Lw fmt.precision G.E forest →
    h ≤ ret → ret ≤ h + 5 →
    mem (h + 1) + dynGraphSize vcF ecF ≤ ret ∧
    dynGraphSize vcF ecF ≤ dgCap ∧
    (∀ a, mem (h + 1) ≤ a → a < mem (h + 1) + dynGraphSize vcF ecF → Rcore.foot handle x a ∨ h ≤ a) ∧
    mem (h + 3) + 2 ≤ ret ∧
    (∀ e ∈ G.E, mem (mem (h + 3)) + e * Lw + Lw ≤ ret ∧ mem (mem (h + 3) + 1) + e * Lw + Lw ≤ ret) ∧
    (∀ e ∈ G.E,
      (Rcore.foot handle x (mem (mem (h + 3)) + e * Lw) ∨ h ≤ mem (mem (h + 3)) + e * Lw) ∧
      (∀ a, mem (mem (h + 3)) + e * Lw ≤ a → a < mem (mem (h + 3)) + e * Lw + Lw →
        Rcore.foot handle x a ∨ h ≤ a) ∧
      (Rcore.foot handle x (mem (mem (h + 3) + 1) + e * Lw) ∨ h ≤ mem (mem (h + 3) + 1) + e * Lw) ∧
      (∀ a, mem (mem (h + 3) + 1) + e * Lw ≤ a → a < mem (mem (h + 3) + 1) + e * Lw + Lw →
        Rcore.foot handle x a ∨ h ≤ a))
  /-- Op `3` (`readGraph`) pointer placement and size caps. -/
  op3Placement : ∀ (H : MGraph) (m1 : ℕ → ℕ) (h0 h1 rawGraph vcH ecH : ℕ),
    DynGraphAt m1 rawGraph vcH ecH H → h0 ≤ h1 → h1 ≤ h0 + 1 →
    rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ dynGraphSize vcH ecH ≤ dgCap ∧ ecH ≤ ecCap
  /-- Op `5` (`readOrd`) output placement inside `[heapFloor, h)` with in-range words. -/
  op5Placement : ∀ (ord : ℕ → List End) (mem : ℕ → ℕ) (oPtr oWords heapFloor h : ℕ),
    OrdListAt mem oPtr ord oWords → ZeroFrom mem h → heapFloor ≤ h →
    heapFloor ≤ oPtr ∧ oPtr + oWords ≤ h ∧ (∀ t < oWords, mem (oPtr + t) < 2 ^ w)
  /-- Rotation-order word length bound from a valid `DynGraphAt` of the level's input graph. -/
  ordRotCap : ∀ (a : SparseCoreOrdAbs cfg.T) (j vc ec : ℕ) (m : ℕ → ℕ) (raw : ℕ),
    j < cfg.P.k → DynGraphAt m raw vc ec a.G → ordRotWords a j ≤ dgCap
  /-- Suffix level rebuild allocation envelope for `j ∈ [first, d)`. -/
  levelSpaceDom : ∀ (next : ChainState cfg.T cfg.P) (j gB lB oB h : ℕ),
    j < cfg.P.d →
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)
    allocation j 6 [gB, lB, lB, oB, cfg.P.k, next.lvlM j, next.N₀, h] + 7 + dgCap + ecCap * L +
      (next.G (j + 1)).m * wireCoreLenEdgeSpace (max L LwMax) +
      ordRotWords (chainLevelOrdAbs next j) 0 ≤ levelSpace j
  /-- Terminal level rebuild allocation envelope. -/
  lastSpaceDom : ∀ (gB lB h : ℕ),
    lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace
  /-- Non-rebuild level-`idx` update step allocation envelope (op `0` + op `2` + coreLen batch update). -/
  updStepSpaceDom : ∀ (idx coreH gB bPtr bW ePtr eW lB h nextULen : ℕ) (lvlM N0 : ℕ),
    idx < cfg.P.d →
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (lvlM + N0 + 2) + 1)
    allocation idx 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 5 +
      nextULen * wireCoreLenEdgeSpace (max L LwMax) ≤ updStepSpace idx
  /-- Non-empty terminal level-`d` update allocation envelope (readout + `coreLen` + `lastInit`). -/
  termUpdSpaceDom : ∀ (lastM lvlMd N0 ordW : ℕ),
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (lvlMd + N0 + 2) + 1)
    7 + dgCap + ecCap * L + lastM * wireCoreLenEdgeSpace (max L LwMax) + ordW + lastSpace ≤
      termUpdSpace
  /-- Per-level rebuild cost domination for `ordRebuildSuffixProgramKStore_runs`. -/
  levelCostDom : ∀ (next : ChainState cfg.T cfg.P) (first j vcH ecH oWords : ℕ),
    first ≤ j → j < cfg.P.d →
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)
    dynGraphSize vcH ecH ≤ dgCap →
    (first < j → oWords ≤ ordRotWords (chainLevelOrdAbs next (j - 1)) 0) →
    Psc.mul * (cfg.T.cost (next.scState j) + (next.G j).n + (next.G j).m + oWords + 1) +
      Psc.mul * (ordRotWords (chainLevelOrdAbs next j) 0 + 1) *
        SparseCore.bundleLogFactor (next.lvlM j) next.N₀ +
      2 * Psc.readout + 17 * dynGraphSize vcH ecH +
      (next.G (j + 1)).m * (wireCoreLenEdgeCost (max L LwMax) + 30) + 265 ≤ levelCost j
  /-- Total space budget domination for Branch A (level-0 rebuild). -/
  spaceTotalBranchA : ∀ (n rootECap uLen mNew : ℕ),
    n ≤ cfg.N₀ → rootECap ≤ intCapMax → mNew ≤ intCapMax →
    3 * (cfg.P.d + 1) + 4 + cfg.P.d * (5 + dgCap) +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) +
      (3 * L + uLen * wireRefreshOneSpace L) +
      (2 * intCapMax) + wireCompactLevel0Space n rootECap L mNew +
      (1 + 4 * n + 2 * rootECap) +
      (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) ≤ coreSpace uLen
  /-- Total space budget domination for Branch B (update loop, possibly interior rebuild). -/
  spaceTotalBranchB : ∀ (uLen : ℕ),
    3 * (cfg.P.d + 1) + 4 + cfg.P.d * (5 + dgCap) +
      (2 * uLen + uLen * wireTreeSyncEditSpace L) +
      (3 * L + uLen * wireRefreshOneSpace L) +
      (Finset.range cfg.P.d).sum updStepSpace + (1 + dgCap) +
      (Finset.range cfg.P.d).sum levelSpace + termUpdSpace + 5 * cfg.P.d +
      (3 * intCapMax + 4 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L) ≤ coreSpace uLen
  /-- Total non-tree-update cost domination for Branch A (level-0 rebuild). -/
  costTotalBranchA : ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (rootECap : ℕ),
    rootECap ≤ intCapMax →
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let n := model.extG.n
    let mNew := (modelPre.chain.G 0).m
    cfg.P.d * (Psc.readout + 17 * dgCap + 110) +
      2 * (230 * (cfg.P.d + 1) + 85 * forestEdgeCap + 300) +
      forestEdgeCap * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 35) +
      (150 * intCapMax + 150 * n + 150 * m + 400) +
      wireCompactLevel0Cost n rootECap intCapMax L mNew +
      (150 * rootECap + 60 * n + 120) +
      (Finset.range cfg.P.d).sum (fun j => levelCost j + 9) +
      lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) +
      cfg.P.d * (Psc.readout + 48) + 20 * cfg.P.d + (100 * mNew + mNew * drainUnit + 100) + 3000 ≤
      coreFixed U.length + toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime)
  /-- Non-rebuild level-`idx` non-`T.cost` step cost envelope (op `0` log factor + `dgApplyBatch` +
  optional op `2` + `wireUpdateCoreLenFromBatchBody`). -/
  updStepCostDom : ∀ (idx bW eW nextULen lvlM N0 : ℕ),
    idx < cfg.P.d →
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (lvlM + N0 + 2) + 1)
    Psc.mul * ((cfg.P.k + 1) * (bW + eW + 1) * SparseCore.bundleLogFactor lvlM N0) +
      670 * bW + Psc.readout +
      nextULen * (wireCoreLenEdgeCost (max L LwMax) + 60) + 250 ≤ updStepCost idx
  /-- Interior rebuild preparation cost envelope (level-`idx` `dgApplyBatch` + op `5` readOrd on `idx - 1`). -/
  interiorPrepCostDom : ∀ (idx bW ordW lvlM N0 : ℕ),
    0 < idx → idx < cfg.P.d →
    670 * bW + Psc.mul * (ordW + 1) * SparseCore.bundleLogFactor lvlM N0 + 180 ≤ updStepCost idx
  /-- Non-empty terminal level-`d` readout + `coreLen` cost envelope (excluding `lastMul * L.cost`). -/
  termUpdCostDom : ∀ (lastM lvlMd N0 ordW : ℕ),
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (lvlMd + N0 + 2) + 1)
    2 * Psc.readout + 17 * dgCap + lastM * (wireCoreLenEdgeCost (max L LwMax) + 30) +
      Psc.mul * (ordW + 1) * SparseCore.bundleLogFactor lvlMd N0 + 300 ≤ termUpdCost
  /-- Total non-tree-update cost domination for Branch B across its 3 outcomes:
  (1) interior rebuild at `0 < i₀ < d`, (2) non-empty terminal rebuild at `d`,
  (3) empty terminal step at `d`. -/
  costTotalBranchB : ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ),
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let fixedB :=
      cfg.P.d * (Psc.readout + 17 * dgCap + 110) +
      (64 * U.length + 40) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 35) +
      cfg.P.d * (Psc.readout + 48) +
      (230 * (cfg.P.d + 1) + 85 * forestEdgeCap + 300) +
      (70 * forestEdgeCap + 25) +
      (130 * U.length + U.length * drainUnit + 100) + 50 * cfg.P.d + 3000
    let rhs := coreFixed U.length + toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime)
    (∀ i₀, 0 < i₀ → i₀ < cfg.P.d →
      modelPre.chain.rebuildCount i₀ = model.chain.rebuildCount i₀ + 1 →
      fixedB + Psc.mul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
        (Finset.range (i₀ + 1)).sum updStepCost +
        (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
        lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) + 20 * cfg.P.d + 300 ≤ rhs) ∧
    (modelPre.chain.curLastRebuilds = model.chain.curLastRebuilds + 1 →
      fixedB + Psc.mul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
        (Finset.range cfg.P.d).sum updStepCost + termUpdCost +
        lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) + 300 ≤ rhs) ∧
    (fixedB + Psc.mul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
        (Finset.range cfg.P.d).sum updStepCost + 300 ≤ rhs)

/-! ### 3. Phase 0: `updateCoreInitRegs` -/

/-- Phase 0: decode `[root, uIntBuf, editsPtr, editWords, g, l, heap]` (`regs 0..6`) and solver
header addresses into permanent high registers `70..95`, reserving `oldPtrs`, `newPtrs`,
`emptyPtrs`, and 4-word `emptyGraphPtr` at `[heap, heap + 3 * (d + 1) + 4)`. -/
@[expose] def updateCoreInitRegs : Stmt :=
  .assign 70 (.reg 0) ;;
  .assign 71 (.const 0) ;;
  .assign 72 (.reg 6) ;;
  .assign 87 (.reg 1) ;;
  .assign 88 (.reg 2) ;;
  .assign 89 (.reg 3) ;;
  .assign 90 (.reg 4) ;;
  .assign 91 (.reg 5) ;;
  .assign 73 (.load (.reg 70)) ;;
  .assign 74 (.load (.bin .add (.reg 70) (.const 1))) ;;
  .assign 84 (.load (.bin .add (.reg 70) (.const 2))) ;;
  .assign 75 (.load (.bin .add (.reg 73) (.const 11))) ;;
  .assign 76 (.load (.bin .add (.reg 73) (.const 12))) ;;
  .assign 94 (.load (.bin .add (.reg 73) (.const 5))) ;;
  .assign 95 (.load (.bin .add (.reg 73) (.const 8))) ;;
  .assign 77 (.bin .add (.reg 73) (.const 18)) ;;
  .assign 78 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 79 (.bin .add (.reg 75) (.const 1)) ;;
  .assign 80 (.reg 72) ;;
  .assign 81 (.bin .add (.reg 80) (.reg 79)) ;;
  .assign 92 (.bin .add (.reg 81) (.reg 79)) ;;
  .assign 93 (.bin .add (.reg 92) (.reg 79)) ;;
  .assign 4 (.bin .add (.reg 93) (.const 4)) ;;
  .assign 82 (.bin .add (.bin .add (.reg 74) (.reg 79)) (.const 1)) ;;
  .assign 83 (.bin .add (.reg 82) (.reg 75)) ;;
  .assign 86 (.bin .add (.reg 84) (.bin .mul (.const 2) (.reg 79))) ;;
  .assign 85 (.bin .add (.reg 86) (.reg 79))

theorem updateCoreInitRegs_noRand : updateCoreInitRegs.NoRand := by
  simp [updateCoreInitRegs, Stmt.NoRand]

/-- Execute `updateCoreInitRegs`, populating `regs 70..95` and `reg 4 = heap + 3 * (d + 1) + 4`
without modifying memory. -/
theorem updateCoreInitRegs_runs
    {w root uIntBuf editsPtr editWords g l heap handle table levelsEnd d k L P pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hRoot0 : mem root = handle) (hRoot1 : mem (root + 1) = table)
    (hRoot2 : mem (root + 2) = levelsEnd)
    (hH5 : mem (handle + 5) = L) (hH8 : mem (handle + 8) = P)
    (hH11 : mem (handle + 11) = d) (hH12 : mem (handle + 12) = k)
    (hRootW : root + 2 < 2 ^ w) (hHandleW : handle + 18 + (d + 1) < 2 ^ w)
    (hTableW : solverLevelMetaAddr table d < 2 ^ w) (hSchedW : levelsEnd + 3 * (d + 1) < 2 ^ w)
    (hHeapW : heap + 3 * (d + 1) + 4 < 2 ^ w) (hw18 : 18 < 2 ^ w) :
    let cnt := d + 1
    let handleBase := handle + 18
    let branchBase := handleBase + cnt
    let lvlMTable := solverLvlMAddr table d
    let levelMeta := solverLevelMetaAddr table d
    let rebuildCountBase := levelsEnd + 2 * cnt
    let updCountBase := levelsEnd + 3 * cnt
    let heapStart := heap + 3 * cnt + 4
    ∃ out c,
      Runs w p ω updateCoreInitRegs
        (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) .normal out c ∧
      c ≤ 170 ∧ out.mem = mem ∧
      out.regs 70 = root ∧ out.regs 71 = 0 ∧ out.regs 72 = heap ∧
      out.regs 73 = handle ∧ out.regs 74 = table ∧ out.regs 75 = d ∧ out.regs 76 = k ∧
      out.regs 77 = handleBase ∧ out.regs 78 = branchBase ∧ out.regs 79 = cnt ∧
      out.regs 80 = heap ∧ out.regs 81 = heap + cnt ∧
      out.regs 82 = lvlMTable ∧ out.regs 83 = levelMeta ∧
      out.regs 84 = levelsEnd ∧ out.regs 85 = updCountBase ∧ out.regs 86 = rebuildCountBase ∧
      out.regs 87 = uIntBuf ∧ out.regs 88 = editsPtr ∧ out.regs 89 = editWords ∧
      out.regs 90 = g ∧ out.regs 91 = l ∧
      out.regs 92 = heap + 2 * cnt ∧ out.regs 93 = heap + 3 * cnt ∧
      out.regs 94 = L ∧ out.regs 95 = P ∧ out.regs 4 = heapStart := by
  dsimp only
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw8 : 8 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw12 : 12 < 2 ^ w := by omega
  let s0 := startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos
  have go {r v c : ℕ} {e : Expr} {tail : Stmt} {s out : State}
      (hv : e.eval w s = some v)
      (ht : Runs w p ω tail { s with regs := Function.update s.regs r v } .normal out c) :
      Runs w p ω (.assign r e ;; tail) s .normal out ((e.size + 1) + c + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c, runs_assign_iff.mpr ⟨v, hv, rfl, rfl, rfl⟩, ht, rfl⟩)
  have rAll := go (s := s0) (r := 70) (e := .reg 0) (v := root) (by simp [Expr.eval, s0, startState])
    (go (r := 71) (e := .const 0) (v := 0) (by simp [Expr.eval, hw0])
    (go (r := 72) (e := .reg 6) (v := heap) (by simp [Expr.eval, s0, startState])
    (go (r := 87) (e := .reg 1) (v := uIntBuf) (by simp [Expr.eval, s0, startState])
    (go (r := 88) (e := .reg 2) (v := editsPtr) (by simp [Expr.eval, s0, startState])
    (go (r := 89) (e := .reg 3) (v := editWords) (by simp [Expr.eval, s0, startState])
    (go (r := 90) (e := .reg 4) (v := g) (by simp [Expr.eval, s0, startState])
    (go (r := 91) (e := .reg 5) (v := l) (by simp [Expr.eval, s0, startState])
    (go (r := 73) (e := .load (.reg 70)) (v := handle) (by simp [Expr.eval, s0, startState, hRoot0])
    (go (r := 74) (e := .load (.bin .add (.reg 70) (.const 1))) (v := table)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw1, show root + 1 < 2 ^ w by omega, hRoot1])
    (go (r := 84) (e := .load (.bin .add (.reg 70) (.const 2))) (v := levelsEnd)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw2, show root + 2 < 2 ^ w by omega, hRoot2])
    (go (r := 75) (e := .load (.bin .add (.reg 73) (.const 11))) (v := d)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw11, show handle + 11 < 2 ^ w by omega, hH11])
    (go (r := 76) (e := .load (.bin .add (.reg 73) (.const 12))) (v := k)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw12, show handle + 12 < 2 ^ w by omega, hH12])
    (go (r := 94) (e := .load (.bin .add (.reg 73) (.const 5))) (v := L)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw5, show handle + 5 < 2 ^ w by omega, hH5])
    (go (r := 95) (e := .load (.bin .add (.reg 73) (.const 8))) (v := P)
      (by simp [Expr.eval, BinOp.eval, s0, startState, hw8, show handle + 8 < 2 ^ w by omega, hH8])
    (go (r := 77) (e := .bin .add (.reg 73) (.const 18)) (v := handle + 18)
      (by simp [Expr.eval, BinOp.eval, hw18, show handle + 18 < 2 ^ w by omega])
    (go (r := 78) (e := .bin .add (.reg 77) (.bin .add (.reg 75) (.const 1))) (v := handle + 18 + (d + 1))
      (by simp [Expr.eval, BinOp.eval, hw1, show d + 1 < 2 ^ w by omega, show handle + 18 + (d + 1) < 2 ^ w by omega])
    (go (r := 79) (e := .bin .add (.reg 75) (.const 1)) (v := d + 1)
      (by simp [Expr.eval, BinOp.eval, hw1, show d + 1 < 2 ^ w by omega])
    (go (r := 80) (e := .reg 72) (v := heap) (by simp [Expr.eval])
    (go (r := 81) (e := .bin .add (.reg 80) (.reg 79)) (v := heap + (d + 1))
      (by simp [Expr.eval, BinOp.eval, show heap + (d + 1) < 2 ^ w by omega])
    (go (r := 92) (e := .bin .add (.reg 81) (.reg 79)) (v := heap + 2 * (d + 1))
      (by simp [Expr.eval, BinOp.eval, show heap + (d + 1) + (d + 1) = heap + 2 * (d + 1) by omega,
        show heap + 2 * (d + 1) < 2 ^ w by omega])
    (go (r := 93) (e := .bin .add (.reg 92) (.reg 79)) (v := heap + 3 * (d + 1))
      (by simp [Expr.eval, BinOp.eval, show heap + 2 * (d + 1) + (d + 1) = heap + 3 * (d + 1) by omega,
        show heap + 3 * (d + 1) < 2 ^ w by omega])
    (go (r := 4) (e := .bin .add (.reg 93) (.const 4)) (v := heap + 3 * (d + 1) + 4)
      (by simp [Expr.eval, BinOp.eval, hw4, show heap + 3 * (d + 1) + 4 < 2 ^ w by omega])
    (go (r := 82) (e := .bin .add (.bin .add (.reg 74) (.reg 79)) (.const 1)) (v := solverLvlMAddr table d)
      (by simp [Expr.eval, BinOp.eval, hw1, solverLvlMAddr, solverN0Addr,
        show table + (d + 1) < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega,
        show table + (d + 1) + 1 < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega])
    (go (r := 83) (e := .bin .add (.reg 82) (.reg 75)) (v := solverLevelMetaAddr table d)
      (by simp [Expr.eval, BinOp.eval, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr,
        show table + (d + 1) + 1 + d < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega])
    (go (r := 86) (e := .bin .add (.reg 84) (.bin .mul (.const 2) (.reg 79))) (v := levelsEnd + 2 * (d + 1))
      (by simp [Expr.eval, BinOp.eval, hw2, show 2 * (d + 1) < 2 ^ w by omega,
        show levelsEnd + 2 * (d + 1) < 2 ^ w by omega])
    ((runs_assign_iff (r := 85) (e := .bin .add (.reg 86) (.reg 79))).mpr
      ⟨levelsEnd + 3 * (d + 1), by simp [Expr.eval, BinOp.eval,
        show levelsEnd + 2 * (d + 1) + (d + 1) = levelsEnd + 3 * (d + 1) by omega,
        show levelsEnd + 3 * (d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩))))))))))))))))))))))))))
  refine ⟨_, _, rAll, by simp [Expr.size], rfl, ?_⟩
  simp

/-! ### 4. Zeroing `updCount[first..d-1]` (`wireZeroUpdCountLoop`) -/

/-- Zero `updCount[reg 20 .. reg 75)` stored at `mem[reg 85 + j]`. -/
@[expose] def wireZeroUpdCountLoop : Stmt :=
  forRange 19 (.reg 20) (.reg 75)
    (.store (.bin .add (.reg 85) (.reg 19)) (.const 0))

theorem wireZeroUpdCountLoop_noRand : wireZeroUpdCountLoop.NoRand := by
  simp [wireZeroUpdCountLoop, forRange, forUp, Stmt.NoRand]

/-- Execute `wireZeroUpdCountLoop`, setting `mem[updCountBase + j] = 0` for `first ≤ j < d`. -/
theorem wireZeroUpdCountLoop_runs {w first d updCountBase : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State}
    (h20 : st.regs 20 = first) (h75 : st.regs 75 = d) (h85 : st.regs 85 = updCountBase)
    (hLe : first ≤ d) (hW : updCountBase + d < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireZeroUpdCountLoop st .normal out cost ∧
      cost ≤ 15 * (d - first) + 15 ∧
      (∀ j, first ≤ j → j < d → out.mem (updCountBase + j) = 0) ∧
      (∀ a, (a < updCountBase + first ∨ updCountBase + d ≤ a) → out.mem a = st.mem a) ∧
      (∀ r ≠ 19, out.regs r = st.regs r) := by
  let Inv (j : ℕ) (s : State) : Prop :=
    first ≤ j ∧ j ≤ d ∧ s.regs 19 = j ∧ (∀ r ≠ 19, s.regs r = st.regs r) ∧
    (∀ k, first ≤ k → k < j → s.mem (updCountBase + k) = 0) ∧
    ∀ a, (a < updCountBase + first ∨ updCountBase + d ≤ a) → s.mem a = st.mem a
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 19) (lo := .reg 20) (hi := .reg 75)
    (P := fun s => s = st) (Inv := Inv) 6 first d hLe hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by simp [Expr.eval, h20], le_rfl, hLe, by simp, fun r hr => by simp [Function.update_of_ne hr],
        fun _ h1 h2 => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.2.1 75 (by decide)).trans h75])
    (fun j hlo hhi s ω' ⟨_, _, hjr, hregs, hzero, hfr⟩ => by
      let t1 := { s with mem := Function.update s.mem (updCountBase + j) 0 }
      have rt1 : Runs w p ω' (.store (.bin .add (.reg 85) (.reg 19)) (.const 0)) s .normal t1 5 :=
        runs_store_iff.mpr ⟨updCountBase + j, 0,
          by simp [Expr.eval, BinOp.eval, (hregs 85 (by decide)).trans h85, hjr,
            show updCountBase + j < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      refine ⟨.normal, t1, 5, rt1, ⟨⟨by omega, by omega, by simp,
        fun r hr => by simp [t1, Function.update_of_ne hr, hregs r hr],
        fun k hk1 hk2 => by
          by_cases hkj : k = j
          · subst hkj; simp [t1]
          · simp [t1, Function.update_of_ne (by omega : updCountBase + k ≠ updCountBase + j), hzero k hk1 (by omega)],
        fun a ha => by simp [t1, Function.update_of_ne (by rcases ha with h | h <;> omega : a ≠ updCountBase + j),
          hfr a ha]⟩, by simp [t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, out, c, r, h, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    obtain ⟨_, _, _, hregs, hzero, hfr⟩ := h
    simp only [Expr.size] at hc
    exact ⟨out, c, r, by omega, hzero, hfr, hregs⟩

/-! ### 6. Filling `emptyPtrs[0..d]` (`wireFillEmptyPtrsLoop`) -/

/-- Fill `mem[reg 92 + j] := reg 93` (`emptyGraphPtr`) for `j = 0 .. reg 79 - 1`. -/
@[expose] def wireFillEmptyPtrsLoop : Stmt :=
  forRange 19 (.const 0) (.reg 79)
    (.store (.bin .add (.reg 92) (.reg 19)) (.reg 93))

theorem wireFillEmptyPtrsLoop_noRand : wireFillEmptyPtrsLoop.NoRand := by
  simp [wireFillEmptyPtrsLoop, forRange, forUp, Stmt.NoRand]

/-- Execute `wireFillEmptyPtrsLoop`, storing `emptyGraphPtr` into `emptyPtrs[0..cnt-1]`. -/
theorem wireFillEmptyPtrsLoop_runs {w emptyPtrs emptyGraphPtr cnt : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State}
    (h79 : st.regs 79 = cnt) (h92 : st.regs 92 = emptyPtrs) (h93 : st.regs 93 = emptyGraphPtr)
    (hW : emptyPtrs + cnt < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireFillEmptyPtrsLoop st .normal out cost ∧
      cost ≤ 15 * cnt + 15 ∧
      (∀ j < cnt, out.mem (emptyPtrs + j) = emptyGraphPtr) ∧
      (∀ a, (a < emptyPtrs ∨ emptyPtrs + cnt ≤ a) → out.mem a = st.mem a) ∧
      (∀ r ≠ 19, out.regs r = st.regs r) := by
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ cnt ∧ s.regs 19 = j ∧ (∀ r ≠ 19, s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (emptyPtrs + k) = emptyGraphPtr) ∧
    ∀ a, (a < emptyPtrs ∨ emptyPtrs + cnt ≤ a) → s.mem a = st.mem a
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 79)
    (P := fun s => s = st) (Inv := Inv) 6 0 cnt (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r hr => by simp [Function.update_of_ne hr], fun _ hk => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 79 (by decide)).trans h79])
    (fun j _ hj s ω' ⟨_, hjr, hregs, hfill, hfr⟩ => by
      let t1 := { s with mem := Function.update s.mem (emptyPtrs + j) emptyGraphPtr }
      have rt1 : Runs w p ω' (.store (.bin .add (.reg 92) (.reg 19)) (.reg 93)) s .normal t1 5 :=
        runs_store_iff.mpr ⟨emptyPtrs + j, emptyGraphPtr,
          by simp [Expr.eval, BinOp.eval, (hregs 92 (by decide)).trans h92, hjr,
            show emptyPtrs + j < 2 ^ w by omega],
          by simp [Expr.eval, (hregs 93 (by decide)).trans h93], rfl, rfl, rfl⟩
      refine ⟨.normal, t1, 5, rt1, ⟨⟨by omega, by simp,
        fun r hr => by simp [t1, Function.update_of_ne hr, hregs r hr],
        fun k hk => by
          by_cases hkj : k = j
          · subst hkj; simp [t1]
          · simp [t1, Function.update_of_ne (by omega : emptyPtrs + k ≠ emptyPtrs + j), hfill k (by omega)],
        fun a ha => by simp [t1, Function.update_of_ne (by rcases ha with h | h <;> omega : a ≠ emptyPtrs + j),
          hfr a ha]⟩, by simp [t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, out, c, r, h, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    obtain ⟨_, _, hregs, hfill, hfr⟩ := h
    simp only [Expr.size] at hc
    exact ⟨out, c, r, by omega, hfill, hfr, hregs⟩

/-! ### 6. Shared batch-decoding and `ordLoadBranchOut` register helpers -/

private theorem decodeUpdate_of_agree {mem₁ mem₂ : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update}
    (hU : UpdateAt mem₁ a G u len) (hag : ∀ t < len, mem₂ (a + t) = mem₁ (a + t)) :
    decodeUpdate mem₂ a G = decodeUpdate mem₁ a G := by
  cases u with
  | insert e x y =>
    obtain ⟨rfl, hL⟩ := hU
    have h0 : mem₂ a = mem₁ a := by simpa using hag 0 (by omega)
    have h1 := hag 1 (by omega); have h2 := hag 2 (by omega); have h3 := hag 3 (by omega)
    have hm0 : mem₁ a = 0 := by simpa using hL 0 (by simp)
    simp only [decodeUpdate, h0, hm0, ↓reduceIte, h1, h2, h3]
  | delete e =>
    obtain ⟨rfl, hL⟩ := hU
    have h0 : mem₂ a = mem₁ a := by simpa using hag 0 (by omega)
    have h1 := hag 1 (by omega)
    have hm0 : mem₁ a = 1 := by simpa using hL 0 (by simp)
    simp only [decodeUpdate, h0, hm0, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, h1]
  | split v v' St Sh =>
    rcases hU with ⟨Lt, Lh, _, _, _, _, rfl, hL⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hL⟩
    all_goals
      have h0 : mem₂ a = mem₁ a := by simpa using hag 0 (by omega)
      have h1 : mem₂ (a + 1) = mem₁ (a + 1) := hag 1 (by omega)
      have h2 : mem₂ (a + 2) = mem₁ (a + 2) := hag 2 (by omega)
      have h3 : mem₂ (a + 3) = mem₁ (a + 3) := hag 3 (by omega)
      have h4 : mem₂ (a + 4) = mem₁ (a + 4) := hag 4 (by omega)
      have hkt : mem₁ (a + 3) = Lt.length := by
        have := hL 3 (by simp)
        simpa [List.getElem_append] using this
      have hkh : mem₁ (a + 4) = Lh.length := by
        have := hL 4 (by simp)
        simpa [List.getElem_append] using this
      have hLt : readList mem₂ (a + 5) Lt.length = readList mem₁ (a + 5) Lt.length :=
        readList_of_agree (fun x hx1 hx2 => by
          have := hag (x - a) (by omega)
          rwa [show a + (x - a) = x by omega] at this)
      have hLh : readList mem₂ (a + 5 + Lt.length) Lh.length =
          readList mem₁ (a + 5 + Lt.length) Lh.length :=
        readList_of_agree (fun x hx1 hx2 => by
          have := hag (x - a) (by omega)
          rwa [show a + (x - a) = x by omega] at this)
      simp only [decodeUpdate, h0, h1, h2, h3, h4, hkt, hkh, hLt, hLh]

private theorem decodeUpdate_snd_of_updateAt {mem : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update}
    (hU : UpdateAt mem a G u len) : (decodeUpdate mem a G).2 = len := by
  cases u with
  | insert e x y =>
    obtain ⟨rfl, hL⟩ := hU
    have hm0 : mem a = 0 := by simpa using hL 0 (by simp)
    simp [decodeUpdate, hm0]
  | delete e =>
    obtain ⟨rfl, hL⟩ := hU
    have hm0 : mem a = 1 := by simpa using hL 0 (by simp)
    simp [decodeUpdate, hm0]
  | split v v' St Sh =>
    rcases hU with ⟨Lt, Lh, _, _, _, _, rfl, hL⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hL⟩
    · have hm0 : mem a = 2 := by simpa using hL 0 (by simp)
      have hkt : mem (a + 3) = Lt.length := by
        have := hL 3 (by simp); simpa [List.getElem_append] using this
      have hkh : mem (a + 4) = Lh.length := by
        have := hL 4 (by simp); simpa [List.getElem_append] using this
      simp [decodeUpdate, hm0, hkt, hkh]
    · have hm0 : mem a = 3 := by simpa using hL 0 (by simp)
      have hkt : mem (a + 3) = Lt.length := by
        have := hL 3 (by simp); simpa [List.getElem_append] using this
      have hkh : mem (a + 4) = Lh.length := by
        have := hL 4 (by simp); simpa [List.getElem_append] using this
      simp [decodeUpdate, hm0, hkt, hkh]

private theorem decodeBatchBody_of_agree {mem₁ mem₂ : ℕ → ℕ} :
    ∀ {a wTot : ℕ} {G : MGraph} {U : List Update},
      BatchBodyAt mem₁ a G U wTot →
      (decodeBatchBody mem₁ U.length a G).1 = U →
      (∀ t < wTot, mem₂ (a + t) = mem₁ (a + t)) →
      (decodeBatchBody mem₂ U.length a G).1 = U
  | _, _, _, [], _, _, _ => rfl
  | a, wTot, G, u :: us, hB, hDec, hag => by
    obtain ⟨len, hlen, hU, hRest⟩ := hB
    have hdu := decodeUpdate_of_agree hU (fun t ht => hag t (lt_of_lt_of_le ht hlen))
    have hsnd := decodeUpdate_snd_of_updateAt hU
    simp only [List.length_cons, decodeBatchBody] at hDec ⊢
    rw [hdu]
    injection hDec with hHd hTl
    rw [hHd, hsnd] at hTl ⊢
    exact congrArg (u :: ·) (decodeBatchBody_of_agree hRest hTl (fun t ht => by
      simpa [Nat.add_assoc] using hag (len + t) (by omega)))

/-- If `mem₂` agrees with `mem₁` on `[a, a + wTot)` of a `BatchAt`, `decodeBatch` is unchanged. -/
theorem decodeBatch_of_agree {mem₁ mem₂ : ℕ → ℕ} {a wTot : ℕ} {G : MGraph} {U : List Update}
    (hB : BatchAt mem₁ a G U wTot)
    (hDec : (decodeBatch mem₁ a G).1 = U)
    (hag : ∀ t < wTot, mem₂ (a + t) = mem₁ (a + t)) :
    (decodeBatch mem₂ a G).1 = U := by
  obtain ⟨hw1, hlen, hBody⟩ := hB
  have h0 : mem₂ a = U.length := (by simpa using hag 0 (by omega) : mem₂ a = mem₁ a).trans hlen
  unfold decodeBatch at hDec ⊢
  rw [hlen] at hDec; rw [h0]
  exact decodeBatchBody_of_agree hBody hDec (fun t ht => by
    simpa [Nat.add_assoc] using hag (1 + t) (by omega))

/-- For an edge-only batch (no `.split` updates), `decodeBatch` recovers `U` from `BatchAt`. -/
theorem decodeBatch_eq_of_noSplit {mem : ℕ → ℕ} {a wTot : ℕ} {G : MGraph} {U : List Update}
    (hB : BatchAt mem a G U wTot)
    (hNoSplit : ∀ u ∈ U, match u with | .split _ _ _ _ => False | _ => True) :
    (decodeBatch mem a G).1 = U := by
  suffices ∀ {a' w' : ℕ} {G' : MGraph} {U' : List Update},
      BatchBodyAt mem a' G' U' w' →
      (∀ u ∈ U', match u with | .split _ _ _ _ => False | _ => True) →
      (decodeBatchBody mem U'.length a' G').1 = U' by
    obtain ⟨_, hlen, hBody⟩ := hB
    unfold decodeBatch; rw [hlen]; exact this hBody hNoSplit
  intro a' w' G' U'
  induction U' generalizing a' w' G' with
  | nil => intro _ _; rfl
  | cons u us ih =>
    intro hBody hNS
    obtain ⟨len, _, hU, hRest⟩ := hBody
    have hNSU := hNS u List.mem_cons_self
    cases u with
    | insert e x y =>
      obtain ⟨rfl, hL⟩ := hU
      have hm0 : mem a' = 0 := by simpa using hL 0 (by simp)
      have hm1 : mem (a' + 1) = e := by simpa using hL 1 (by simp)
      have hm2 : mem (a' + 2) = x := by simpa using hL 2 (by simp)
      have hm3 : mem (a' + 3) = y := by simpa using hL 3 (by simp)
      simp only [List.length_cons, decodeBatchBody, decodeUpdate, hm0, ↓reduceIte, hm1, hm2, hm3]
      exact congrArg _ (ih hRest (fun v hv => hNS v (List.mem_cons_of_mem _ hv)))
    | delete e =>
      obtain ⟨rfl, hL⟩ := hU
      have hm0 : mem a' = 1 := by simpa using hL 0 (by simp)
      have hm1 : mem (a' + 1) = e := by simpa using hL 1 (by simp)
      simp only [List.length_cons, decodeBatchBody, decodeUpdate, hm0, show (1 : ℕ) ≠ 0 by decide,
        ↓reduceIte, hm1]
      exact congrArg _ (ih hRest (fun v hv => hNS v (List.mem_cons_of_mem _ hv)))
    | split _ _ _ _ => exact False.elim hNSU

/-- Exact register values loaded into `regs 10..13` by `ordLoadBranchOutStmt`. -/
theorem ordLoadBranchOut_regs_eq {w branchOutAddr j c : ℕ} {p : Program} {ω : ℕ → Bool}
    {st out : State}
    (hr : Runs w p ω ordLoadBranchOutStmt st .normal out c)
    (hb : st.regs 2 = j) (hp : st.regs 4 = branchOutAddr)
    (hroom : branchOutAddr + 1 + 4 * j + 3 < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let base := branchOutAddr + 1 + 4 * j
    out.regs 10 = st.mem base ∧ out.regs 11 = st.mem (base + 1) ∧
    out.regs 12 = st.mem (base + 2) ∧ out.regs 13 = st.mem (base + 3) := by
  dsimp only
  rcases runs_seq_iff.mp hr with ⟨_, _, _, h, _⟩ | ⟨sa, _, _, ha, hrest, _⟩
  · cases h
  · rcases runs_seq_iff.mp hrest with ⟨_, _, _, h, _⟩ | ⟨sb, _, _, hb', hrest2, _⟩
    · cases h
    · rcases runs_seq_iff.mp hrest2 with ⟨_, _, _, h, _⟩ | ⟨sc, _, _, hc, hrest3, _⟩
      · cases h
      · rcases runs_seq_iff.mp hrest3 with ⟨_, _, _, h, _⟩ | ⟨sd, _, _, hd, he, _⟩
        · cases h
        · obtain ⟨v1, hv1, _, rfl, _⟩ := runs_assign_iff.mp ha
          obtain ⟨v2, hv2, _, rfl, _⟩ := runs_assign_iff.mp hb'
          obtain ⟨v3, hv3, _, rfl, _⟩ := runs_assign_iff.mp hc
          obtain ⟨v4, hv4, _, rfl, _⟩ := runs_assign_iff.mp hd
          obtain ⟨v5, hv5, _, rfl, _⟩ := runs_assign_iff.mp he
          have hv1' : v1 = branchOutAddr + 1 + 4 * j := by
            have := hv1
            simp [Expr.eval, BinOp.eval, hp, hb, show 1 < 2 ^ w by omega, hw4,
              show branchOutAddr + 1 < 2 ^ w by omega, show 4 * j < 2 ^ w by omega,
              show branchOutAddr + 1 + 4 * j < 2 ^ w by omega] at this
            exact this.symm
          subst hv1'
          have hv2' : v2 = st.mem (branchOutAddr + 1 + 4 * j) := by
            have := hv2; simp [Expr.eval] at this; exact this.symm
          subst hv2'
          have hv3' : v3 = st.mem (branchOutAddr + 1 + 4 * j + 1) := by
            have := hv3
            simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega,
              show branchOutAddr + 1 + 4 * j + 1 < 2 ^ w by omega] at this
            exact this.symm
          subst hv3'
          have hv4' : v4 = st.mem (branchOutAddr + 1 + 4 * j + 2) := by
            have := hv4
            simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega,
              show branchOutAddr + 1 + 4 * j + 2 < 2 ^ w by omega] at this
            exact this.symm
          subst hv4'
          have hv5' : v5 = st.mem (branchOutAddr + 1 + 4 * j + 3) := by
            have := hv5
            simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega,
              show branchOutAddr + 1 + 4 * j + 3 < 2 ^ w by omega] at this
            exact this.symm
          subst hv5'
          simp [Function.update_of_ne]

end MinCostFlow.MinRatio
