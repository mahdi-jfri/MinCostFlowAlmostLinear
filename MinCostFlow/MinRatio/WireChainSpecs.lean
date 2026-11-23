module

public import MinCostFlow.MinRatio.OrdChainRefreshWiredBase
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.WireChainAlgebra
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve

/-!
# Corrected specs of the three chain steps

`OrdChainUpdateCoreSpec` (`OrdChainRefreshWiredBase.lean`), `ShiftTermChainSyncSpec` and
`ShiftDeepChainSyncSpec` (`ShiftLevelWired.lean`) bound the cost of a step by a fixed budget.
No fixed budget pays for the work these steps do in the worst case.
* A call into the sparse-core module costs `P.mul` times the rise of the tool cost
  (`sparseCoreOrdMachineContractK`, operations `0` and `1`, and its initialization). A restart or a
  rebuild of a level raises the tool cost by `Õ(M_i)`. The paper bounds the tool cost only in
  total over a run (Lemma 5.17, page 23; the run time of Theorem 5.1, page 30).
* The path tree must follow the changes of the chain tree `T^𝒢` (Theorem 5.1, pages 29–30). A
  shift or a rebuild can change many of its edges at once. The paper bounds the number of these
  changes, too, only in total over a run (Lemma 5.11, page 20).

The corrected specs state the cost as a fixed part plus `toolMul` times the rise of the chain's
cumulative runtime `ChainState.totalRuntime` (retired tool costs plus the active ones; it never
falls) plus `treeMul` times the rise of `ChainState.totalTreeUpdates` (the number of edge changes
of `T^𝒢` so far). A credit `toolMul · (cap - totalRuntime) + treeMul · (cap' - totalTreeUpdates)` in
the solver potential then pays for both (`wire_credit_step`).

The other changes, the same in the three specs:
* the hypothesis `WireCapFacts` (the cap and limb conditions of the sparse-core contract at every
  level), since the steps call the sparse-core module;
* the shift specs also take `bran j < k` at every level `j < d`, and the bound `OffTreeRecBound` on
  the off-tree records; these hold on every reached state, and the specs ask them only of the
  state of the call;
* the conclusions keep `levelsEnd` and the capacity `intCap` of the name tables (a level-`0`
  rebuild renames the live names to `0, …, |E| - 1`, below the old `nextFresh`, so it needs no
  larger table), and give `OffTreeRecBound` after the step.
The rest of each statement is that of the existing spec.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

/-- **The corrected chain update.** It is `OrdChainUpdateCoreSpec` with the hypothesis
`WireCapFacts`, the conclusions `tok'.levelsEnd = tok.levelsEnd`, `tok'.intCap = tok.intCap` and
`OffTreeRecBound`, and the cost
`coreFixed |U| + toolMul · Δ totalRuntime + treeMul · Δ totalTreeUpdates` in place of
`coreBudget |U|`. -/
@[expose] def OrdChainUpdateCoreSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (ordChainCoreProc : ℕ) (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[ordChainCoreProc]? = some body ∧
    ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      DynSpanner.Program.SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
      OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
      (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
      editsPtr + editWords = heap →
      RefreshBatch model.extG U →
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root modelPre tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv modelPre L out.mem tok'.edgeRecords B' ∧
        OffTreeRecBound modelPre L out.mem tok'.edgeRecords B' ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          coreFixed U.length +
            toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- **The corrected terminal shift sync.** It is `ShiftTermChainSyncSpec` with the hypotheses
`OffTreeRecBound`, `WireCapFacts` and `bran j < k`, the conclusions `tok'.intCap = tok.intCap` and
`OffTreeRecBound`, and the cost `termFixed + toolMul · Δ totalRuntime + treeMul · Δ totalTreeUpdates`
in place of `termBudget`. -/
@[expose] def ShiftTermChainSyncSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftTermChainProc : ℕ) (termSpace termFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftTermChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      Rrep.rep root model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + termSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        Rrep.rep root model' tok' out.mem ∧
        PreservesLevelMeta tok tok' mem0 out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          termFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- Extended terminal shift sync contract with the reached-state forest/capacity
preconditions proved for `shiftTermChainBody` in `WireShiftTerm.lean`. -/
@[expose] def ShiftTermChainSyncSpecWExt
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftTermChainProc : ℕ) (termSpace termFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftTermChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
      let newLastF := (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F
      Rrep.rep root model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      model.chain.lastBran < model.chain.lastK →
      model.chain.lastK < 2 ^ w →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      model'.chain.toTreeChain.chainTree.IsForest →
      model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E →
      model'.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E →
      Disjoint
        ((Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
        (oldLastF.E ∪ newLastF.E) →
      oldLastF.m + newLastF.m ≤ lastTreeCap →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + termSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        Rrep.rep root model' tok' out.mem ∧
        PreservesLevelMeta tok tok' mem0 out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          termFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- **The corrected deep shift sync.** It is `ShiftDeepChainSyncSpec` with the hypotheses
`OffTreeRecBound`, `WireCapFacts` and `bran j < k`, the conclusions `tok'.intCap = tok.intCap` and
`OffTreeRecBound`, and the cost `deepFixed + toolMul · Δ totalRuntime + treeMul · Δ totalTreeUpdates`
in place of `deepBudget`. -/
@[expose] def ShiftDeepChainSyncSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftDeepChainProc : ℕ) (deepSpace deepFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftDeepChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      Rrep.rep root model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + deepSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        Rrep.rep root model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- Address of the stored `N₀` word right after `table[0..d]`. -/
@[expose] def solverN0Addr (table d : ℕ) : ℕ :=
  table + (d + 1)

/-- Base address of the stored `lvlM[0..d)` array. -/
@[expose] def solverLvlMAddr (table d : ℕ) : ℕ :=
  solverN0Addr table d + 1

/-- Base address of the `2 * d` per-level `(ℓ_j, G_j)` metadata pointers. -/
@[expose] def solverLevelMetaAddr (table d : ℕ) : ℕ :=
  solverLvlMAddr table d + d

/-- Address of the select-heap base pointer right after `levelMeta[0..2 * d)`. -/
@[expose] def solverSelectHeapAddr (table d : ℕ) : ℕ :=
  solverLevelMetaAddr table d + 2 * d

/-- Address of the select-blocks base pointer right after `solverSelectHeapAddr`. -/
@[expose] def solverSelectBlocksAddr (table d : ℕ) : ℕ :=
  solverSelectHeapAddr table d + 1

/-- Base address of the 18-word solver header (`handle`) right after the level-metadata and
select-pointer region (`table + (4 * d + 4)`). -/
@[expose] def solverHandleAddr (table d : ℕ) : ℕ :=
  solverSelectBlocksAddr table d + 1

/-- Per-level chain metadata (`N₀`, `lvlM` array, per-level `(G_j, ℓ_j)` pointers, and the two
select-region base pointers) stored right after the rebuild threshold table at `table + (d + 1)`
and tagged in `tok.tag` above `20 + d` (except level `0`'s graph, which aliases `tok.rootGraph`
with tag `20`) so they lie inside `tok.owned` and are disjoint from all other `SolverTagsAt`
regions (`1..19`, `21 + i`).
Layout right after `table[0..d]`:
- `solverN0Addr table d = table + (d + 1)` (1 word holding `model.chain.N₀`, tag `21 + d`)
- `solverLvlMAddr table d = table + (d + 1) + 1` (`d` words holding `model.chain.lvlM[0..d)`, tag `21 + d`)
- `solverLevelMetaAddr table d = table + (d + 1) + 1 + d` (`2 * d` words of `(ℓ_j, G_j)` pointers, tag `22 + d`)
- `solverSelectHeapAddr table d = levelMeta + 2 * d` (1 word holding the select-heap base, tag `21 + d`)
- `solverSelectBlocksAddr table d = levelMeta + 2 * d + 1` (1 word holding the select-blocks base, tag `21 + d`)
- `solverHandleAddr table d = table + (4 * d + 4)` (18-word header `handle`, tag `2`)
Live per-level `EdgeValuesAt` blocks and level `1..d-1` `DynGraphAt` blocks carry tag `23 + d`,
while level `0`'s `DynGraphAt` carries tag `20`. -/
@[expose] def SolverLevelMetaAt {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (P _V : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let n0Cell := solverN0Addr tok.table d
  let lvlMTable := solverLvlMAddr tok.table d
  let levelMeta := solverLevelMetaAddr tok.table d
  (mem n0Cell = model.chain.N₀ ∧ tok.tag n0Cell = 21 + d ∧
    tok.tag (solverSelectHeapAddr tok.table d) = 21 + d ∧
    tok.tag (solverSelectBlocksAddr tok.table d) = 21 + d) ∧
  (∀ j < d, tok.owned (tok.coreHandle j)) ∧
  (∀ j < d, mem (lvlMTable + j) = model.chain.lvlM j) ∧
  (∀ j < d, tok.tag (lvlMTable + j) = 21 + d) ∧
  (∀ j < 2 * d, tok.tag (levelMeta + j) = 22 + d) ∧
  (∀ j < d, ∃ vc ec,
    DynSpanner.Program.DynGraphAt mem (mem (levelMeta + d + j)) vc ec (model.chain.G j) ∧
    EdgeValuesAt mem (mem (levelMeta + j)) 4 L P (model.chain.G j).E
      (model.chain.toTreeChain.chainLen model.chain.ℓ j) ∧
    tok.owned (mem (levelMeta + j)) ∧
    (∀ a, mem (levelMeta + j) ≤ a → a < mem (levelMeta + j) + ec * L →
      tok.tag a = 23 + d) ∧
    (∀ a, mem (levelMeta + d + j) ≤ a →
      a < mem (levelMeta + d + j) + DynSpanner.Program.dynGraphSize vc ec →
      tok.tag a = if j = 0 then 20 else 23 + d))

/-- Reached-state algebraic and numeric invariants for a non-terminal deep shift `i < d` from
`model` to `model' = alg2LoopShiftStep cfg model i`. -/
@[expose] def ShiftDeepModelInv (w L P wordExp stretchPrec : ℕ) {cfg : Alg2Config}
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) : Prop :=
  let model' := alg2LoopShiftStep cfg model i
  let d := cfg.P.d
  (model.chain.lastBran < model.chain.lastK ∧ 0 < model'.chain.lastK) ∧
  (∀ j, i.val ≤ j → j < d →
    SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
      (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
      (model.chain.updCount j)) ∧
  cfg.T.cost (model.chain.scState i.val) ≤ cfg.T.cost (model'.chain.scState i.val) ∧
  (model'.chain.G (i.val + 1)).E ⊆ (model.chain.G i.val).E ∧
  (∀ e ∈ (model'.chain.G (i.val + 1)).E,
    ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
      model'.chain.toTreeChain.chainLen model.chain.ℓ (i.val + 1) e) ∧
  (∀ j, i.val + 1 ≤ j → j < d →
    (model'.chain.G j).m ≤ model'.chain.lvlM j ∧
    (model'.chain.G j).n ≤ model'.chain.N₀ ∧
    model'.chain.lvlM j < 2 ^ w ∧
    (model'.chain.lvlM j + model'.chain.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w ∧
    IsRotationOrder (model'.chain.G j) (model'.chain.levelOrd j) ∧
    (∀ e ∈ (model'.chain.G j).E, 0 < model'.chain.toTreeChain.chainLen model'.chain.ℓ j e) ∧
    (model'.chain.G (j + 1)).E ⊆ (model'.chain.G j).E ∧
    (∀ e ∈ (model'.chain.G (j + 1)).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
        model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1) e)) ∧
  cfg.L.build (model'.chain.G d)
    (fun e => if e ∈ (model'.chain.G d).E then
      model'.chain.toTreeChain.chainLen model'.chain.ℓ d e else 0) =
    cfg.L.build (model'.chain.G d) (model'.chain.toTreeChain.chainLen model'.chain.ℓ d) ∧
  (∀ e ∈ (model'.chain.G d).E, 0 < model'.chain.toTreeChain.chainLen model'.chain.ℓ d e) ∧
  (∀ e ∈ (model'.chain.G d).E,
    2 * (2 : ℝ) ^ stretchPrec *
      lastLevelStretchBound (model'.chain.G d)
        (model'.chain.toTreeChain.chainLen model'.chain.ℓ d) e <
      Num.capacity 4 L) ∧
  model'.chain.toTreeChain.chainTree.IsForest ∧
  model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E ∧
  model'.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E ∧
  (∀ j, i.val ≤ j → j < d →
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ (model.chain.G 0).E ∧
    (cfg.T.lsfs (model'.chain.scState j) (model'.chain.bran j)).F.F.E ⊆ (model.chain.G 0).E) ∧
  (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ (model.chain.G 0).E ∧
  (model'.chain.lastLSFs model'.chain.lastBran).F.F.E ⊆ (model.chain.G 0).E ∧
  Disjoint
    ((Finset.range i.val).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
    (graphListEdgeUnion (chainSuffixForests model.chain i.val) ∪
      graphListEdgeUnion (chainSuffixForests model'.chain i.val))

/-- Extended deep shift sync contract with `SolverLevelMetaAt` (maintained across the step) and
the reached-state forest/chain/capacity preconditions proved for `shiftDeepChainBody` in
`WireShiftDeep.lean`. -/
@[expose] def ShiftDeepChainSyncSpecWExt
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftDeepChainProc : ℕ) (deepSpace deepFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftDeepChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      ShiftDeepModelInv w L P wordExp stretchPrec model i →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + deepSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- Reached-state algebraic and numeric invariants for a periodic suffix rebuild starting at
level `first < cfg.P.d` during `Chain.Ordered.updateLoop`. -/
@[expose] def UpdateRebuildModelInv (w L P wordExp stretchPrec : ℕ) {cfg : Alg2Config}
    (st : ChainState cfg.T cfg.P) (first : ℕ) (Gstart : MGraph) (ℓstart gstart : ℕ → ℝ)
    (extraEnc : ℕ) : Prop :=
  let d := cfg.P.d
  let stWithLG : ChainState cfg.T cfg.P := { st with ℓ := ℓstart, g := gstart }
  let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stWithLG first Gstart extraEnc).1
  st.rebuildCount first + 1 < 2 ^ w ∧
  0 < next.lastK ∧
  (∀ j, first ≤ j → j < d →
    (next.G j).m ≤ next.lvlM j ∧
    (next.G j).n ≤ next.N₀ ∧
    next.lvlM j < 2 ^ w ∧
    (next.lvlM j + next.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w ∧
    IsRotationOrder (next.G j) (next.levelOrd j) ∧
    (∀ e ∈ (next.G j).E, 0 < next.toTreeChain.chainLen next.ℓ j e) ∧
    (next.G (j + 1)).E ⊆ (next.G j).E ∧
    (∀ e ∈ (next.G (j + 1)).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
        next.toTreeChain.chainLen next.ℓ (j + 1) e)) ∧
  cfg.L.build (next.G d)
    (fun e => if e ∈ (next.G d).E then next.toTreeChain.chainLen next.ℓ d e else 0) =
    cfg.L.build (next.G d) (next.toTreeChain.chainLen next.ℓ d) ∧
  (∀ e ∈ (next.G d).E, 0 < next.toTreeChain.chainLen next.ℓ d e) ∧
  (∀ e ∈ (next.G d).E,
    2 * (2 : ℝ) ^ stretchPrec *
      lastLevelStretchBound (next.G d) (next.toTreeChain.chainLen next.ℓ d) e <
      Num.capacity 4 L)

/-- Recursive reached-state invariant mirroring `Chain.Ordered.updateLoop` level by level on
`rem = cfg.P.d - idx`, carrying sparse-core preconditions, batch validity/capacity bounds,
unchanged-edge core-length stability, and suffix-rebuild or terminal-rebuild numeric bounds. -/
@[expose] def UpdateLoopModelInv (w L P wordExp stretchPrec : ℕ) {cfg : Alg2Config}
    (vcOf ecOf : ℕ → ℕ) (origLen : ℕ → ℕ → ℝ) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → ChainState cfg.T cfg.P → MGraph → List Update → ℕ → (ℕ → List End) → Prop
  | 0, _, st, curG, curU, _, _ =>
    (curU = [] → curG.E = (st.G cfg.P.d).E) ∧
    (curU ≠ [] →
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = cfg.P.d then curG else st.G j }
      let ℓd := Cpartial.chainLen ℓ' cfg.P.d
      0 < (cfg.L.build curG ℓd).1 ∧
      cfg.L.build curG (fun e => if e ∈ curG.E then ℓd e else 0) = cfg.L.build curG ℓd ∧
      (∀ e ∈ curG.E, 0 < ℓd e) ∧
      (∀ e ∈ curG.E,
        2 * (2 : ℝ) ^ stretchPrec * lastLevelStretchBound curG ℓd e < Num.capacity 4 L) ∧
      (0 < cfg.P.d →
        SparseCoreOrdInput cfg.T cfg.P.k (st.lvlM (cfg.P.d - 1)) st.N₀
          (st.scState (cfg.P.d - 1)) (st.G (cfg.P.d - 1))
          (st.levelOrd (cfg.P.d - 1)) (st.updCount (cfg.P.d - 1)) ∧
        curG = cfg.T.S (st.scState (cfg.P.d - 1)) (st.bran (cfg.P.d - 1)) ∧
        curG.E ⊆ (st.G (cfg.P.d - 1)).E ∧
        (∀ e ∈ curG.E,
          ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = ℓd e)))
  | rem + 1, idx, st, curG, curU, curEnc, oldOrd =>
    st.updCount idx + curU.length < 2 ^ w ∧
    (st.G idx).BatchIsValid curU ∧
    DynSpanner.Program.BatchWithinCaps (vcOf idx) (ecOf idx) curU ∧
    curG = (st.G idx).applyBatch curU ∧
    (∀ e ∈ curG.E, e < ecOf idx) ∧
    if intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length then
      UpdateRebuildModelInv w L P wordExp stretchPrec st idx
        (Chain.Ordered.rebuildStartGraph idx curG)
        (Chain.Ordered.rebuildStartFn idx curG ℓ')
        (Chain.Ordered.rebuildStartFn idx curG g') curEnc ∧
      (0 < idx →
        SparseCoreOrdInput cfg.T cfg.P.k (st.lvlM (idx - 1)) st.N₀
          (st.scState (idx - 1)) (st.G (idx - 1))
          (st.levelOrd (idx - 1)) (st.updCount (idx - 1)))
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
        (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
          st.scState st.bran idx)
      let sc' := updRes.1
      let nextG := cfg.T.S sc' (st.bran idx)
      let nextU := updRes.2 (st.bran idx)
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      let fiChanges := diffTreeChanges (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E
        (cfg.T.lsfs sc' (st.bran idx)).F.F.E
      let stNext : ChainState cfg.T cfg.P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEnc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      SparseCoreOrdInput cfg.T cfg.P.k (st.lvlM idx) st.N₀
        (st.scState idx) (st.G idx) oldOrd (st.updCount idx) ∧
      SparseCore.Program.OrderedBatch (st.G idx) curU oldOrd
        (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
          st.scState st.bran idx) ∧
      ((st.updCount idx + curU.length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold cfg.P.k (st.lvlM idx) st.N₀ ∧
      cfg.T.cost (st.scState idx) ≤ cfg.T.cost sc' ∧
      (∀ e ∈ curG.E, 0 < ℓi e) ∧
      (idx + 1 < cfg.P.d →
        st.G (idx + 1) = cfg.T.S (st.scState idx) (st.bran idx) ∧
        (∀ u ∈ nextU, match u with
          | .insert e _ _ =>
            e ∈ curG.E ∧ e < ecOf idx ∧ e < ecOf (idx + 1) ∧
            ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
              coreLen (cfg.T.lsfs sc' (st.bran idx)) ℓi e
          | _ => True) ∧
        (∀ e ∈ nextG.E, (∀ u ∈ nextU, ¬ Update.Inserts e u) →
          e ∈ (st.G (idx + 1)).E ∧
          coreLen (cfg.T.lsfs sc' (st.bran idx)) ℓi e = origLen (idx + 1) e)) ∧
      UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf origLen ℓ' g' rem (idx + 1)
        stNext nextG nextU 0 (cfg.T.rot (st.scState idx) (st.bran idx))

/-- Reached-state algebraic, numeric, forest, and capacity invariants for `ordChainUpdateCoreBody`
transitioning from `model` to `modelPre = alg2PreResetState cfg model U gVec lVec`. -/
@[expose] def UpdateCoreModelInv (w L P m epsExp wordExp stretchPrec : ℕ) {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update)
    (mem0 : ℕ → ℕ) (g l : ℕ) (B : ℤ) : Prop :=
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch U_int
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let ℓ' := fun e' => lVec (tr.2.2.1 e')
  let g' := fun e' => gVec (tr.2.2.1 e')
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let st0 : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
  let levelMeta := solverLevelMetaAddr tok.table cfg.P.d
  (0 < cfg.P.d ∧ 0 < m) ∧
  (model.chain.N₀ = cfg.N₀ ∧ model.extG.n ≤ cfg.N₀ ∧ tok.rootECap ≤ tok.intCap) ∧
  (∀ ei ∈ G0.E, model.chain.ℓ ei = model.extℓ (model.intToExt ei)) ∧
  ((∀ j < m * L, ¬ tok.owned (g + j) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok (g + j) ∧
      ∀ r < cfg.P.d, ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (g + j)) ∧
   (∀ j < m * L, ¬ tok.owned (l + j) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok (l + j) ∧
      ∀ r < cfg.P.d, ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (l + j))) ∧
  (∀ j < cfg.P.d, (modelPre.chain.G j).IsValid) ∧
  (4 ∣ P ∧ epsExp ≤ P ∧ P - epsExp + 1 < 4 * L ∧ cfg.ε = ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P) ∧
  (model.chain.lastBran < model.chain.lastK ∧ 0 < modelPre.chain.lastK) ∧
  (∀ j < cfg.P.d,
    SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
      (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
      (model.chain.updCount j)) ∧
  (mem0 (levelMeta + cfg.P.d + 0) = tok.rootGraph ∧
   ∃ vcOf ecOf : ℕ → ℕ,
    (∀ j < cfg.P.d,
      DynSpanner.Program.DynGraphAt mem0 (mem0 (levelMeta + cfg.P.d + j)) (vcOf j) (ecOf j)
        (model.chain.G j) ∧
      EdgeValuesAt mem0 (mem0 (levelMeta + j)) 4 L P (model.chain.G j).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ j) ∧
      tok.owned (mem0 (levelMeta + j)) ∧
      (∀ a, mem0 (levelMeta + j) ≤ a → a < mem0 (levelMeta + j) + ecOf j * L →
        tok.tag a = 23 + cfg.P.d) ∧
      (∀ a, mem0 (levelMeta + cfg.P.d + j) ≤ a →
        a < mem0 (levelMeta + cfg.P.d + j) + DynSpanner.Program.dynGraphSize (vcOf j) (ecOf j) →
        tok.tag a = (if j = 0 then 20 else 23 + cfg.P.d) ∧
        ∀ r < cfg.P.d,
          (a < mem0 (levelMeta + r) ∨ mem0 (levelMeta + r) + ecOf r * L ≤ a) ∧
          (r ≠ j → a < mem0 (levelMeta + cfg.P.d + r) ∨
            mem0 (levelMeta + cfg.P.d + r) + DynSpanner.Program.dynGraphSize (vcOf r) (ecOf r) ≤ a))) ∧
    (∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
      mem0 (levelMeta + j₁) + ecOf j₁ * L ≤ mem0 (levelMeta + j₂) ∨
      mem0 (levelMeta + j₂) + ecOf j₂ * L ≤ mem0 (levelMeta + j₁)) ∧
    UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g' cfg.P.d 0 st0 G0' U_int
      (G0.batchEnc U_int) (st0.levelOrd 0)) ∧
  DynSpanner.Program.BatchWithinCaps model.extG.n tok.rootECap U_int ∧
  (∀ e ∈ G0'.E, e < tok.rootECap ∧ e < tok.intCap) ∧
  G0'.m ≤ tok.rootECap ∧ G0'.m ≤ tok.intCap ∧
  -- Refreshed-edge numeric & fit bounds
  (∀ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int →
    let e := tr.2.2.1 ei_old
    let gNew := Num.intVal mem0 (g + e * L) 4 L
    let lNew := Num.intVal mem0 (l + e * L) 4 L
    let thrNew := detectorThreshold P cfg.ε (lVec e)
    Num.Valid mem0 (g + e * L) 4 L ∧
    Num.Valid mem0 (l + e * L) 4 L ∧
    (gNew : ℝ) / (2 : ℝ) ^ P = gVec e ∧
    (lNew : ℝ) / (2 : ℝ) ^ P = lVec e ∧
    0 < lNew ∧
    |gNew| ≤ B ∧ |lNew| ≤ B ∧
    Num.Fits 4 L (-thrNew) ∧ Num.Fits 4 L thrNew ∧
    ∀ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e →
      |acc - thrNew| ≤ B ∧ Num.Fits 4 L acc ∧ Num.Fits 4 L (acc - thrNew)) ∧
  -- Forest inclusion and validity invariants
  modelPre.chain.toTreeChain.chainTree.IsForest ∧
  model.chain.toTreeChain.chainTree.E ⊆ G0.E ∧
  modelPre.chain.toTreeChain.chainTree.E ⊆ (modelPre.chain.G 0).E ∧
  (∀ j < cfg.P.d,
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ G0.E ∧
    (cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j)).F.F.E ⊆ (modelPre.chain.G 0).E) ∧
  (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ G0.E ∧
  (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.E ⊆ (modelPre.chain.G 0).E

/-- Extended ordered chain-update contract with `SolverLevelMetaAt` (maintained across the step)
and reached-state numeric, forest, and capacity preconditions for `ordChainUpdateCoreBody`. -/
@[expose] def OrdChainUpdateCoreSpecWExt
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (ordChainCoreProc : ℕ) (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[ordChainCoreProc]? = some body ∧
    ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
      (U : List Update) (B R : ℤ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      B ≤ B_bound → R ≤ R_bound →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ ei, model.nextFresh ≤ ei → ei < tok.intCap → mem0 (tok.inOffReady + ei) = 0) →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      DynSpanner.Program.SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2
        (editsPtr - cfg.P.d - uIntBuf) →
      OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
      (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
      editsPtr + editWords = heap →
      RefreshBatch model.extG U →
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root modelPre tok' out.mem ∧
        SolverLevelMetaAt P V modelPre tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv modelPre L out.mem tok'.edgeRecords B' ∧
        OffTreeRecBound modelPre L out.mem tok'.edgeRecords B' ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          coreFixed U.length +
            toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

end MinCostFlow.MinRatio
