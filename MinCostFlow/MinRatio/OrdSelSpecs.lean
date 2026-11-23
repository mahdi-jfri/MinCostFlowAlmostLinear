module

public import MinCostFlow.MinRatio.SolverSelectState
public import MinCostFlow.MinRatio.SolverSelectRegionInv
public import MinCostFlow.MinRatio.WireInitSpec
public import MinCostFlow.MinRatio.OrdSolverRepFullKFBL
public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.SolverTreeBudgetInv

/-!
# Select-aware specifications for the solver bodies (`OrdSelSpecs`)

Defines the select-aware contracts needed to prove `DSRep.Implements` for `solverStateRepSel`
(wrapped with `SolverLevelCapsInv` and `DeepInv` in `solverStateRepSelKFBL`), one per solver body
that builds or mutates the select region:

* `SolverInitStepSpecSel` (`Init`): establishes `solverStateRepSel.rep`, `SolverLevelCapsInv`,
  the tree budget `SolverTreeBudgetInv` at `updateCount = 0`, `Rsel.Respects`, and the full init
  cost bound including `K * sg.reembPot`, matching `solverInitWiredSel_runs`
  (`SelectInitWired.lean`).
* `OrdChainUpdateCoreSpecWKFBLSel` and `ChainRefreshStepSpecWKFBLSel` (`Update` chain core and
  refresh): maintain `SolverLevelCapsInv`, `SolverSelectInv`, and
  `sg.reembPot = chainReembPot pot modelPre.chain`, charging `K * Δ chainReembPot` into the
  combined potential `Rrep.phi + K * sg.reembPot`. Both run at the tree budget `B, R` they are
  given and give it back.
* `ShiftTermChainSyncSpecWExtKFBLSel` (terminal shift `i = d`): maintains `SolverLevelCapsInv`,
  `SolverSelectInv`, and `sg.reembPot = chainReembPot pot model'.chain`.
* `ShiftDeepChainSyncSpecWExtKFBLSel` (non-terminal shift `i < d`): maintains `SolverLevelCapsInv`,
  `SolverSelectInv`, and `sg.reembPot = chainReembPot pot model'.chain`, with
  `K * Δ chainReembPot` absorbed by `toolMul * Δ totalRuntime`.
* `ShiftLevelStepSpecWKFBLSel`: wired level-shift contract combining the terminal and deep shift
  select-aware specs.

Every spec that changes the select state also takes and gives `SolverSelectRegionInv`
(`SolverSelectRegionInv.lean`): the owned blocks layout with slot size `slot` and terminal
precision `pLast`, the potential bound `SelectPhiBoundedAt` with `N = 2 m + 2` and `M_g = 2 ^ E`,
and the gradient bound `|g e| ≤ 2 ^ E` on level `0`. A body that rebuilds a level writes free
slots of the blocks in place and needs both bounds to show that its values fit, so these facts
must hold before it runs and must be restored after it.

Non-level-changing operations (`Query`, `Detect`, `Eval`, `FindCycle` via `FindCycleStepSpecHeap`,
`Update` prep, good-cycle apply, and fail output) already preserve both `SolverLevelCapsInv` and
`SolverSelectInv` (see `SolverSelectPreserve.lean`), and they
keep `SolverSelectRegionInv` by `SolverSelectRegionInv.preserve_of_levelMeta`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program DynSpanner.Program

/-! ## 1. Init (`SolverInitStepSpecSel`, discharged directly by `solverInitWiredSel_runs`) -/

/-- Modular contract for the select-aware `Init` procedure (`solverInitWiredSelBody` in
`SelectInitWired.lean`), matching `solverInitWiredSel_runs` directly: establishes
`solverStateRepSel.rep`, `SolverLevelCapsInv`, `SolverSelectRegionInv`, `Rsel.Respects`, and the
full init cost bound against `OrdSolverContractEnvelopeFullCredit`. -/
@[expose] def SolverInitStepSpecSel {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp unit toolMul treeMul dMul kOff K pLast slot : ℕ)
    (pot : cfg.T.State → ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc : ℕ) (initSpace initBudget : ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rsel := solverStateRepSel cfg (1 / (2 : ℝ) ^ k) G L P m V psi k epsExp
    (detectOffTreeDrainUnit L) unit toolMul treeMul dMul kOff Rcore K pot
  ∃ body, p.procs[initProc]? = some body ∧
    ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) →
      minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + initSpace < 2 ^ w →
      ∃ (finalHeap cost : ℕ) (out : State) (tok : Rsel.τ),
        Runs w p ω body (startState args mem pos) (.returned finalHeap) out cost ∧
        let s0 := (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).init G
          (readVector mem (args.getD 1 0) F.fmt.limbBits L P m)
          (readVector mem (args.getD 2 0) F.fmt.limbBits L P m)
        MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G
          F.fmt.limbBits L P s0 ∧
        Rsel.rep (heapArg args) s0 tok out.mem ∧
        SolverLevelCapsInv P V G.n (initTargetCap cfg G) s0 tok.1.1.1 out.mem ∧
        SolverLevelLayoutAt G.n (initTargetCap cfg G) tok.1.1.1 out.mem ∧
        SolverSelectRegionInv G L P m F.rangeExponent pLast slot G.n (initTargetCap cfg G) s0
          ((solverStateRepFull cfg (1 / (2 : ℝ) ^ k) G L P m V psi k epsExp
            (detectOffTreeDrainUnit L) unit toolMul treeMul Rcore).foot (heapArg args) tok.1)
          tok.1.1.1 tok.2 out.mem ∧
        SolverTreeBudgetInv G P F.rangeExponent 0 s0 tok.1.1.1 out.mem ∧
        Rsel.Respects (fun _ => False) (heapArg args) initSpace mem finalHeap (heapArg args) tok
          out.mem ∧
        cost + Rsel.phi (heapArg args) tok out.mem ≤
          initBudget +
            unit * ((cfg.P.d + 1) *
              Nat.floor ((10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1))) +
            toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
            treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0)

/-! ## 2. `Update` chain core (`OrdChainUpdateCoreSpecWKFBLSel` and `ChainRefreshStepSpecWKFBLSel`) -/

/-- **Select-aware chain-update core spec.**
Extends `OrdChainUpdateCoreSpecWKFBL` with the reached-state invariants available at `Update`
(`OrdSolverReached`, `DeepInv`, `ShiftLoopChainInv` before and after, `MinRatioStateFits`,
`SolverTreeNumericInv`, `tok.intCap = initTargetCap cfg G`, `gVec`/`lVec` range and
agreement), plus `SolverSelectInv` and `sg.reembPot = chainReembPot pot model.chain`.
Postcondition restores `SolverLevelCapsInv`, `SolverSelectInv`, `sg'.reembPot`, frame/foot over
`Rrep.foot ∨ sg.owned`, and the amortized cost bound including `K * sg'.reembPot`.

The input arrays `g` and `l` lie off `Rrep.foot ∨ sg.owned`. The core reads them after the level
cores and the select part have written their cells, and the contract of `Update` places the
caller's arrays only below `heap`, so they could meet the footprint. `Update` meets the premise
since it hands on the copies that it makes above `heap` (`copyInsertedStmt`).

The core runs at the tree budget `B, R` that the caller holds, and gives back the same budget. The
caller holds `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound` at `B ≥ B₀ = 2^(P + 2E + 2)`
and the fit. It also gives the facts that bound the refreshed records: the stored gradients and
lengths are in range, the flows are at most `2^E` (the `pre` of `Update`), and every accumulator
is below its threshold (the state is a `Detect` output). With these, the refreshed values of
`UpdateCoreModelInv` are at most `B₀`. The program does not depend on the budget, so
`OrdChainUpdateCoreSpecWExtKFBL` at `B_bound := B`, `R_bound := R` gives this spec. -/
@[expose] def OrdChainUpdateCoreSpecWKFBLSel
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff K pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (ordChainCoreProc : ℕ) (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[ordChainCoreProc]? = some body ∧
    ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
      (sg : SelectGhost) (U : List Update) (B R : ℤ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
        (LevelMetaFoot tok) sg mem0 →
      sg.reembPot = chainReembPot pot model.chain →
      SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg
        mem0 →
      OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model →
      DeepInv model.chain →
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G 4 L P model →
      SolverTreeNumericInv P model tok →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      treeBudgetBase P E ≤ B →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E ∧
        (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, |model.flow e| ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
        model.extℓ e * model.detectAccum e < cfg.ε) →
      tok.intCap = initTargetCap cfg G →
      tok.intCap ≤ intCapMax →
      2 * (model.chain.G 0).n ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      Chain.Ordered.ShiftLoopChainInv cfg modelPre.chain →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      (∀ e ∈ model.extG.E, |gVec e| ≤ (2 : ℝ) ^ E ∧
        (2 : ℝ) ^ (-(E : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e ∧ lVec e = model.extℓ e) →
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
      (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      (∀ j < m * L, ¬ (Rrep.foot root tok (g + j) ∨ sg.owned (g + j)) ∧
        ¬ (Rrep.foot root tok (l + j) ∨ sg.owned (l + j))) →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      (∀ u ∈ U, ∀ e, u.Inserts e →
        Num.Valid mem0 (g + e * L) 4 L ∧ Num.Valid mem0 (l + e * L) 4 L) →
      (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
      SolverLevelLayoutAt vCap eCap tok mem0 →
      ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore) (sg' : SelectGhost),
        Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.rootECap = tok.rootECap ∧ tok'.table = tok.table ∧
        Rrep.rep root modelPre tok' out.mem ∧
        SolverLevelMetaAt P V modelPre tok' out.mem ∧
        SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table modelPre (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot modelPre.chain ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap modelPre (Rrep.foot root tok') tok' sg'
          out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv modelPre L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound modelPre L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem + K * sg'.reembPot ≤
          coreFixed U.length +
            toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0 + K * sg.reembPot

/-- Wired select-aware chain-refresh contract for `ordChainRefreshWiredBody`. It takes the same
premises as `OrdChainUpdateCoreSpecWKFBLSel`, which it calls, among them that `g` and `l` lie off
`Rrep.foot ∨ sg.owned`, and it keeps the tree budget `B, R` as the core does. -/
@[expose] def ChainRefreshStepSpecWKFBLSel
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff K pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (chainRefreshProc : ℕ) (refreshSpace refreshFixed : ℕ → ℕ) (toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[chainRefreshProc]? = some body ∧
    ∀ (root uIntBuf g l quotaBase heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (U : List Update)
      (B R : ℤ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let model1 := alg2PreLoopState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
        (LevelMetaFoot tok) sg mem0 →
      sg.reembPot = chainReembPot pot model.chain →
      SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg
        mem0 →
      OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model →
      DeepInv model.chain →
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G 4 L P model →
      SolverTreeNumericInv P model tok →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      treeBudgetBase P E ≤ B →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E ∧
        (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, |model.flow e| ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
        model.extℓ e * model.detectAccum e < cfg.ε) →
      tok.intCap = initTargetCap cfg G →
      tok.intCap ≤ intCapMax →
      2 * (model.chain.G 0).n ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      Chain.Ordered.ShiftLoopChainInv cfg model1.chain →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      (∀ e ∈ model.extG.E, |gVec e| ≤ (2 : ℝ) ^ E ∧
        (2 : ℝ) ^ (-(E : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ E) →
      (∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e ∧ lVec e = model.extℓ e) →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      DynSpanner.Program.SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (heap - uIntBuf) →
      RefreshBatch model.extG U →
      (∀ x ∈ batchWords U, x < 2 ^ w) →
      2 * (model.nextFresh + U.length) + 1 < 2 ^ w →
      (∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w) →
      (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      (∀ j < m * L, ¬ (Rrep.foot root tok (g + j) ∨ sg.owned (g + j)) ∧
        ¬ (Rrep.foot root tok (l + j) ∨ sg.owned (l + j))) →
      quotaBase + cfg.P.d + 1 < uIntBuf →
      (∀ i ≤ cfg.P.d + 1, ¬ (Rrep.foot root tok (quotaBase + i) ∨ sg.owned (quotaBase + i))) →
      uIntBuf ≤ heap →
      ZeroFrom mem heap →
      heap + refreshSpace U.length < 2 ^ w →
      (∀ u ∈ U, ∀ e, u.Inserts e →
        Num.Valid mem0 (g + e * L) 4 L ∧ Num.Valid mem0 (l + e * L) 4 L) →
      SolverLevelLayoutAt vCap eCap tok mem0 →
      ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore) (sg' : SelectGhost),
        Runs w p ω body (startState [root, uIntBuf, g, l, quotaBase, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + refreshSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.rootECap = tok.rootECap ∧ tok'.table = tok.table ∧
        Rrep.rep root model1 tok' out.mem ∧
        SolverLevelMetaAt P V model1 tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model1 tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model1 (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot model1.chain ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap model1 (Rrep.foot root tok') tok' sg'
          out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model1 L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model1 L out.mem tok'.edgeRecords B ∧
        (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i) ∧
        out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) →
          (a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem + K * sg'.reembPot ≤
          refreshFixed U.length +
            toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0 + K * sg.reembPot

/-! ## 3. Terminal shift (`ShiftTermChainSyncSpecWExtKFBLSel`) -/

/-- **Select-aware terminal shift sync spec.**
Extends `ShiftTermChainSyncSpecWExtKFBL` with `ShiftLoopChainInv`, `DeepInv`, `SolverSelectInv`,
and `sg.reembPot = chainReembPot pot model.chain`, rebuilding level `d` in the select region and
restoring `SolverSelectInv` and `sg'.reembPot = chainReembPot pot model'.chain` (`= sg.reembPot`). -/
@[expose] def ShiftTermChainSyncSpecWExtKFBLSel
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap vCap eCap
      dMul kOff K E pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftTermChainProc : ℕ) (termSpace termFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftTermChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      SolverLevelLayoutAt vCap eCap tok mem0 →
      SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
        (LevelMetaFoot tok) sg mem0 →
      sg.reembPot = chainReembPot pot model.chain →
      SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg
        mem0 →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      DeepInv model.chain →
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
        ((model.chain.lastLSFs model.chain.lastBran).F.F.E ∪
          (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E) →
      ((model.chain.lastLSFs model.chain.lastBran).F.F.E.card +
        (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E.card ≤
          lastTreeCap) →
      (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < heap) →
      ZeroFrom mem heap →
      heap + termSpace < 2 ^ w →
      ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore) (sg' : SelectGhost),
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model' (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot model'.chain ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap model' (Rrep.foot root tok') tok' sg'
          out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem + K * sg'.reembPot ≤
          termFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0 + K * sg.reembPot

/-! ## 4. Deep shift (`ShiftDeepChainSyncSpecWExtKFBLSel`) and wired `ShiftLevelStepSpecWKFBLSel` -/

/-- **Select-aware deep shift sync spec.**
Extends `ShiftDeepChainSyncSpecWExtKFBL` with `ShiftLoopChainInv`, `DeepInv`, `SolverSelectInv`,
and `sg.reembPot = chainReembPot pot model.chain`, rebuilding the select suffix `i .. d` and
restoring `SolverSelectInv` and `sg'.reembPot = chainReembPot pot model'.chain` (with
`K * (sg'.reembPot - sg.reembPot) ≤ K * Δ totalRuntime` absorbed into `toolMul * Δ totalRuntime`). -/
@[expose] def ShiftDeepChainSyncSpecWExtKFBLSel
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap dMul kOff K E pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftDeepChainProc : ℕ) (deepSpace deepFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftDeepChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      SolverLevelLayoutAt vCap eCap tok mem0 →
      SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
        (LevelMetaFoot tok) sg mem0 →
      sg.reembPot = chainReembPot pot model.chain →
      SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg
        mem0 →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      DeepInv model.chain →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      ShiftDeepModelInv w L P wordExp stretchPrec model i →
      ShiftDeepModelInvKFBL model i →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < heap) →
      ZeroFrom mem heap →
      heap + deepSpace < 2 ^ w →
      ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore) (sg' : SelectGhost),
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model' (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot model'.chain ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap model' (Rrep.foot root tok') tok' sg'
          out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem + K * sg'.reembPot ≤
          deepFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0 + K * sg.reembPot

/-- Wired select-aware level-shift contract for `shiftLevelWiredBody`. -/
@[expose] def ShiftLevelStepSpecWKFBLSel
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap dMul kOff K E pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftLevelProc shiftSpace shiftFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftLevelProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      (model.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
      (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
      model.passes i + 1 < 2 ^ w →
      Rrep.rep root model tok mem →
      SolverLevelMetaAt P V model tok mem →
      SolverLevelCapsAt vCap eCap model tok mem →
      SolverLevelLayoutAt vCap eCap tok mem →
      SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
        (LevelMetaFoot tok) sg mem →
      sg.reembPot = chainReembPot pot model.chain →
      SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg
        mem →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      DeepInv model.chain →
      (i.val < cfg.P.d → ShiftDeepModelInv w L P wordExp stretchPrec model i) →
      tok.intCap ≤ intCapMax →
      2 * (model.chain.G 0).n ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < heap) →
      ZeroFrom mem heap →
      heap + shiftSpace < 2 ^ w →
      ∃ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore) (sg' : SelectGhost),
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model' (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot model'.chain ∧
        SolverSelectRegionInv G L P m E pLast slot vCap eCap model' (Rrep.foot root tok') tok' sg'
          out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem + K * sg'.reembPot ≤
          shiftFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem + K * sg.reembPot

end MinCostFlow.MinRatio
