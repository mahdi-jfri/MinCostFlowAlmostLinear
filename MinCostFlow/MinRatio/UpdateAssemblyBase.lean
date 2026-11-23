module

public import MinCostFlow.MinRatio.UpdateIntTablesGrow
public import MinCostFlow.MinRatio.FreshBatchRefresh
public import MinCostFlow.MinRatio.UpdateCycleLoop
public import MinCostFlow.MinRatio.UpdateGoodApply
public import MinCostFlow.MinRatio.UpdateFailOutput
public import MinCostFlow.Num.Subtract
public import MinCostFlow.MinRatio.UpdateCopyInserted
import WordRAM.Tactic

/-!
# Definitions and helper contracts for end-to-end `Update` assembly

Defines:
1. `alg2PreLoopState`: the exact pre-loop state of `Chain.Ordered.algorithm2_updateWith` after
   `translateBatch`, `Chain.Ordered.algorithm1_update`, and `firstRebuiltLevel` pass reset.
2. `ChainRefreshStepSpec`: modular contract for the chain-update, periodic rebuild,
   LCT tree-edit fold, detector refresh, and shift-quota table refresh subroutine.
3. `GoodCycleNumericBridge`: connects the accepted `CycleDescriptorAt` from
   `updateCycleLoopBody` to the numeric, connectivity, and accounting hypotheses of
   `updateGoodApplyBody_runs`.
4. `solverUpdatePrefix` and `solverUpdateBody`: the fixed deterministic Word-RAM
   entry procedure for `minRatioMachineContractWithV` operation 0 (`Update`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- The pre-loop `Alg2State` produced by `Chain.Ordered.algorithm2_updateWith` right before entering
`Chain.Ordered.algorithm2_loopWith`. After a rebuild of level `0` its name maps are the renamed
ones (`Chain.Ordered.level0E2I`). -/
@[expose] noncomputable def alg2PreLoopState (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) : Alg2State cfg :=
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let extG' := tr.1
  let e2i' := tr.2.1
  let i2e' := tr.2.2.1
  let nf' := tr.2.2.2.1
  let U_int := tr.2.2.2.2
  let ch1 := (Chain.Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain U_int
    (fun e' => gVec (i2e' e')) (fun e' => lVec (i2e' e'))).1
  let (branD1, passes1) :=
    match firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount with
    | none => (model.branD, model.passes)
    | some iStar =>
      (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else model.passes j)
  let ren := Chain.Ordered.level0Rebuilt cfg.P.d model.chain.rebuildCount ch1.rebuildCount
  let G₀' := (model.chain.G 0).applyBatch U_int
  { model with
    chain := ch1
    branD := branD1
    passes := passes1
    extG := extG'
    extToInt := Chain.Ordered.level0E2I ren G₀' e2i'
    intToExt := Chain.Ordered.level0I2E ren G₀' i2e'
    nextFresh := Chain.Ordered.level0NF ren G₀' nf'
    extℓ := lVec
    extg := gVec
    lctUpdateOps := model.lctUpdateOps + U.length
    largeBatchEnc := model.largeBatchEnc + largeBatchEncCap cfg.P U_int
    updateCount := model.updateCount + 1 }

/-- `alg2PreLoopState` preserves `BranchesLtK`. -/
theorem branchesLtK_preLoop {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} (hbr : BranchesLtK cfg model) :
    BranchesLtK cfg (alg2PreLoopState cfg model U gVec lVec) := by
  dsimp only [BranchesLtK, alg2PreLoopState]
  refine ⟨algorithm1_update_bran cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _ hbr.1, ?_⟩
  cases firstRebuiltLevel cfg.P.d model.chain.rebuildCount _ with
  | none => exact hbr.2
  | some _ => exact cfg.P.hk

/-- The gradient (or length) vector that `Update` hands to the chain refresh. `Update` copies the
caller's entries at the edges that the batch inserts (`copyInsertedStmt`), and `copied` is the
vector read from that copy. On a live edge that the batch does not insert, the caller's value is
the one the solver stored before (`ordAlg2_detectedWith_agree`), so the vector takes the stored
value `stored` there. Elsewhere it takes the copy. -/
@[expose] noncomputable def updateOverlay (E : Finset ℕ) (U : List Update)
    (copied stored : ℕ → ℝ) : ℕ → ℝ :=
  open Classical in fun e => if e ∈ E ∧ ¬ ∃ u ∈ U, u.Inserts e then stored e else copied e

/-- The vector handed on equals the caller's vector `v` when `v` agrees with the stored vector
on the live edges that the batch does not insert, and the copy agrees with `v` everywhere else. -/
theorem updateOverlay_eq {E : Finset ℕ} {U : List Update} {copied stored v : ℕ → ℝ}
    (hstored : ∀ e ∈ E, ¬ (∃ u ∈ U, u.Inserts e) → v e = stored e)
    (hcopied : ∀ e, ¬ (e ∈ E ∧ ¬ ∃ u ∈ U, u.Inserts e) → copied e = v e) :
    updateOverlay E U copied stored = v := by
  classical
  funext e
  unfold updateOverlay
  split_ifs with h
  · exact (hstored e h.1 h.2).symm
  · exact hcopied e h

/-- Modular contract for the chain-refresh subroutine
`chainRefreshProc [root, uIntBuf, g, l, quotaBase, heap]`.
Consumes the freshly translated internal batch at `uIntBuf` (with updated `FreshTablesAt`
in memory), executes `Chain.Ordered.algorithm1_update` (including periodic rebuilds), resets pass counts,
applies tree edits and detector threshold refreshes, and writes `shiftQuotaWord` at
`quotaBase[0..d]` and `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊` at `quotaBase[d + 1]`. -/
@[expose] def ChainRefreshStepSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (chainRefreshProc : ℕ) (refreshSpace refreshBudget : ℕ → ℕ) (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[chainRefreshProc]? = some body ∧
    ∀ (root uIntBuf g l quotaBase heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let model1 := alg2PreLoopState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
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
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      quotaBase + cfg.P.d + 1 < uIntBuf →
      (∀ i ≤ cfg.P.d + 1, ¬ Rrep.foot root tok (quotaBase + i)) →
      uIntBuf ≤ heap →
      ZeroFrom mem heap →
      heap + refreshSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, g, l, quotaBase, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + refreshSpace U.length ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root model1 tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv model1 L out.mem tok'.edgeRecords B' ∧
        (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i) ∧
        out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → (a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) →
          out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ refreshBudget U.length + Rrep.phi root tok mem0

/-- Credit-bearing contract for the chain-refresh subroutine
`chainRefreshProc [root, uIntBuf, g, l, quotaBase, heap]`, allowing its cost to charge `toolMul`
times the rise of `totalRuntime` and `treeMul` times the rise of `totalTreeUpdates`. -/
@[expose] def ChainRefreshStepSpecCredit (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (chainRefreshProc : ℕ) (refreshSpace refreshFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[chainRefreshProc]? = some body ∧
    ∀ (root uIntBuf g l quotaBase heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let model1 := alg2PreLoopState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
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
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      quotaBase + cfg.P.d + 1 < uIntBuf →
      (∀ i ≤ cfg.P.d + 1, ¬ Rrep.foot root tok (quotaBase + i)) →
      uIntBuf ≤ heap →
      ZeroFrom mem heap →
      heap + refreshSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, g, l, quotaBase, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + refreshSpace U.length ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root model1 tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv model1 L out.mem tok'.edgeRecords B' ∧
        (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i) ∧
        out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → (a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) →
          out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          refreshFixed U.length +
            toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

theorem ChainRefreshStepSpec.toCredit {w L P m V psi k epsExp drainUnit : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    {chainRefreshProc : ℕ} {refreshSpace refreshBudget : ℕ → ℕ} {B_bound R_bound : ℤ}
    (h : ChainRefreshStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p chainRefreshProc
      refreshSpace refreshBudget B_bound R_bound) :
    ChainRefreshStepSpecCredit w L P m V psi k epsExp drainUnit cfg Rcore p chainRefreshProc
      refreshSpace refreshBudget 0 0 B_bound R_bound := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun root uIntBuf g l qB heap pos ω mem0 mem model tok U
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 => ?_⟩
  obtain ⟨nh, c, out, tok', B', R', hr, hl, hh, hB, hR, hrep, hnum, hoff, hq, hpsi, hz, hfr, hft, hc⟩ :=
    hrun root uIntBuf g l qB heap pos ω mem0 mem model tok U
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  exact ⟨nh, c, out, tok', B', R', hr, hl, hh, hB, hR, hrep, hnum, hoff, hq, hpsi, hz, hfr, hft,
    by simpa using hc⟩

/-- Wired credit-bearing chain-refresh contract matching `OrdChainUpdateCoreSpecW`: extends
`ChainRefreshStepSpecCredit` with the `WireCapFacts` premise and the `tok'.levelsEnd`,
`tok'.intCap`, and `OffTreeRecBound` conclusions. -/
@[expose] def ChainRefreshStepSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (chainRefreshProc : ℕ) (refreshSpace refreshFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[chainRefreshProc]? = some body ∧
    ∀ (root uIntBuf g l quotaBase heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let model1 := alg2PreLoopState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      WireCapFacts capExp limbMul L capLimit model →
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
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      quotaBase + cfg.P.d + 1 < uIntBuf →
      (∀ i ≤ cfg.P.d + 1, ¬ Rrep.foot root tok (quotaBase + i)) →
      uIntBuf ≤ heap →
      ZeroFrom mem heap →
      heap + refreshSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R',
        Runs w p ω body (startState [root, uIntBuf, g, l, quotaBase, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + refreshSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root model1 tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv model1 L out.mem tok'.edgeRecords B' ∧
        OffTreeRecBound model1 L out.mem tok'.edgeRecords B' ∧
        (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i) ∧
        out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → (a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) →
          out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          refreshFixed U.length +
            toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- Conditional `MeetsContract` specification matching `explicitEdgeRouteUpdate_meetsContract`. -/
@[expose] def ExplicitRouteUpdateSpec (w L : ℕ) (p : Program) (explicitRouteUpdate : ℕ) : Prop :=
  ∀ edgesBase edgeRecords dst multPtr edges address old mult,
    multPtr + L ≤ dst →
    dst + edges.length + 2 < 2 ^ w →
    (∀ e ∈ edges.map Prod.fst, e < 2 ^ w) →
    (∀ e ∈ edges.map Prod.fst, address e + 2 + 4 * L ≤ min edgesBase (min dst multPtr)) →
    (∀ e ∈ edges.map Prod.fst, ∀ f ∈ edges.map Prod.fst, e ≠ f →
      address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e) →
    (∀ e ∈ edges.map Prod.fst,
      let n := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
      Num.Fits 4 L n ∧ Num.Fits 4 L (mult * n) ∧ Num.Fits 4 L |mult * n| ∧
        Num.Fits 4 L ((old e).flow + mult * n) ∧ Num.Fits 4 L ((old e).detector + |mult * n|)) →
    MeetsContract w p explicitRouteUpdate
      (explicitEdgeRouteUpdateContract w 4 L edgesBase edgeRecords dst multPtr edges address old mult)

/-- Numeric, connectivity, and accounting bridge from an accepted `CycleDescriptorAt`
produced by `updateCycleLoopBody` to the hypotheses of `updateGoodApplyBody_runs` and
`MinRatioStateFits`. -/
@[expose] def GoodCycleNumericBridge {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp drainUnit : ℕ) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T))
    (maxEdges maxPaths : ℕ) (B_bound R_bound : ℤ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∀ (root eta outHeap curDesc nextHeap : ℕ) (mem : ℕ → ℕ)
    (modelLoop : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ)
    (request inner norm : ℤ) (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)),
    let Δ := liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1
    let mult := pathMultiplier P request (-inner)
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    F.fmt.limbBits = 4 →
    modelLoop.extG = G →
    MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P modelLoop →
    (∀ e ∈ G.E, |modelLoop.flow e| ≤ (2 : ℝ) ^ F.rangeExponent) →
    (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (1 / (2 : ℝ) ^ k) * cfg.α →
    5 * F.rangeExponent + Nat.size m + 30 ≤ P →
    (∀ e ∈ G.E,
      |modelLoop.extg e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
      (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ modelLoop.extℓ e ∧
      modelLoop.extℓ e ≤ (2 : ℝ) ^ F.rangeExponent) →
    Rrep.rep root modelLoop tok mem →
    PathTreeNumericInv tok.tree tok.trees B R →
    OffTreeRecInv modelLoop L mem tok.edgeRecords B →
    B ≤ B_bound → R ≤ R_bound →
    CycleDescriptorAt modelLoop L P mem curDesc nextHeap inner norm edges paths →
    edges.length ≤ maxEdges → paths.length ≤ maxPaths →
    (∀ a, tok.tag a = 18 → a < curDesc) →
    (∀ a, Rrep.foot root tok a → a < nextHeap ∧ (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a)) →
    modelLoop.extG.inner modelLoop.extg Δ / modelLoop.extG.lnorm modelLoop.extℓ Δ ≤
      -((1 / (2 : ℝ) ^ k) * cfg.α) →
    PathIntAt mem eta 4 L request →
    (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (request : ℝ) / (2 : ℝ) ^ P →
    (request : ℝ) / (2 : ℝ) ^ P ≤ (2 : ℝ) ^ F.rangeExponent →
    2 * G.n + 1 < 2 ^ w →
    Nat.log 2 (2 * G.n + 1) ≤ 4 * L →
    Nat.size m ≤ F.rangeExponent + 8 →
    maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
    2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P))) <
      (Num.capacity 4 L : ℤ) →
    B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P) < (Num.capacity 4 L : ℤ) →
    0 < tok.intCap ∧
    2 * tok.tree.n + 1 < 2 ^ w ∧
    Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * L ∧
    0 < -inner ∧ Num.Fits 4 L (-inner) ∧
    (2 : ℝ) * (((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ) ∧
    Num.Fits 4 L mult ∧ Num.Fits 4 L |mult| ∧
    (∀ q ∈ paths, q.1 < tok.tree.n ∧ q.2 < tok.tree.n ∧
      pathTreeConnected tok.tree (q.1 + 1) (q.2 + 1)) ∧
    2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) *
      ((B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult)) +
        (R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult))) <
      (Num.capacity 4 L : ℤ) ∧
    B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult) ≤
      B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P) ∧
    R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult) ≤
      R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P) ∧
    MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| } ∧
    ∃ (address : ℕ → ℕ) (old : ℕ → PathEdgeValue),
      (∀ ei ∈ edges.map Prod.fst, ei < tok.intCap ∧
        mem (tok.edgeRecords + ei) = address ei ∧
        PathEdgeAt mem (address ei) 4 L (some (old ei)) ∧
        (∀ x < 2 + 4 * L, tok.tag (address ei + x) = 18) ∧
        address ei + 2 + 4 * L ≤ mem (curDesc + 2)) ∧
      (∀ e ∈ edges.map Prod.fst, ∀ f ∈ edges.map Prod.fst, e ≠ f →
        address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e) ∧
      (∀ e ∈ edges.map Prod.fst,
        let n := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
        Num.Fits 4 L n ∧ Num.Fits 4 L (mult * n) ∧ Num.Fits 4 L |mult * n| ∧
          Num.Fits 4 L ((old e).flow + mult * n) ∧ Num.Fits 4 L ((old e).detector + |mult * n|)) ∧
      (∀ (mem' : ℕ → ℕ) (trees' : List AuxTree) (depth' : ℕ → ℕ),
        let s' := applyPathsFold tok.tree (PathTag.ofFlow mult) paths
        LctInvWith pathPayload s' trees' tok.free depth' →
        (∀ ei ∈ edges.map Prod.fst,
          PathEdgeAt mem' (address ei) 4 L (some (updatedOffTreeVal edges old mult ei)) ∧
          (0 ≤ (updatedOffTreeVal edges old mult ei).detector →
            mem' (tok.inOffReady + ei) = 1)) →
        (∀ a < nextHeap, (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a) →
          (∀ ei ∈ edges.map Prod.fst, a < address ei + 2 + 2 * L ∨ address ei + 2 + 4 * L ≤ a) →
          tok.tag a ≠ 1 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → mem' a = mem a) →
        (∀ j < tok.intCap, mem (tok.inOffReady + j) = 1 → mem' (tok.inOffReady + j) = 1) →
        (∀ j < tok.intCap, j ∉ edges.map Prod.fst → mem' (tok.inOffReady + j) = mem (tok.inOffReady + j)) →
        SolverEdgeAccountsAt
          { modelLoop with
            flow := fun e => modelLoop.flow e + inc e
            detectAccum := fun e => modelLoop.detectAccum e + |inc e| }
          L P mem' tok.slots tok.names tok.slotThresholds tok.edgeThresholds tok.edgeRecords
          tok.inOffReady tok.intCap s' trees' ∧
        TreeEditNamedSlots s' trees' modelLoop.chain.toTreeChain.chainTree
          (fun f => mem' (tok.slots + f)) (fun k => mem' (tok.names + k)) ∧
        SolverEdgeOrientInv L P modelLoop mem' tok.slots tok.edgeRecords s' trees')

/-- Prefix of `solverUpdateBody`: loads header parameters (`L`, `P`, `d`, `qExp = epsExp - 7`)
and computes scratch layout pointers (`descOut`, `quotaBase`, `zeroBlock`, `workHeap0`, `batchCopyLen`). -/
@[expose] def solverUpdatePrefix : Stmt :=
  .assign 6 (.load (.reg 0)) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.const 5))) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 8))) ;;
  .assign 9 (.load (.bin .add (.reg 6) (.const 11))) ;;
  .assign 11 (.bin .sub (.load (.bin .add (.reg 6) (.const 16))) (.const 7)) ;;
  .assign 12 (.load (.reg 1)) ;;
  .assign 13 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 2) (.reg 7))) ;;
  .assign 14 (.bin .add (.reg 13) (.const 2)) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.reg 9) (.const 2))) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 7)) ;;
  .assign 18 (.bin .add (.bin .mul (.const 4) (.reg 12)) (.const 1))

/-- Preparation prefix of `solverUpdateBody`: loads header parameters, copies `eta` and
`batch` above `heap`, copies the entries of `g` and `l` at the inserted edges above them
(`copyInsertedStmt`), grows internal tables, copies `batch` above `inverse`, and runs
`freshBatchEntry` to produce the translated internal batch. -/
@[expose] def solverUpdatePrepBody (growTables copyWords freshBatch : ℕ) : Stmt :=
  solverUpdatePrefix ;;
  .assign 31 (.reg 16) ;;
  .call 30 copyWords [.reg 4, .reg 31, .reg 7] ;;
  .assign 32 (.bin .add (.bin .add (.reg 31) (.reg 7)) (.reg 18)) ;;
  .call 30 copyWords [.reg 1, .reg 32, .reg 18] ;;
  copyInsertedStmt copyWords ;;
  .call 16 growTables [.reg 0, .reg 12, .reg 16] ;;
  .assign 17 (.reg 16) ;;
  .call 30 copyWords [.reg 32, .reg 17, .reg 18] ;;
  .assign 16 (.bin .add (.reg 17) (.reg 18)) ;;
  .assign 19 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 20 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 21 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 18 (.reg 16) ;;
  .call 16 freshBatch [.reg 17, .reg 19, .reg 20, .reg 21, .reg 18]

/-- Fixed deterministic Word-RAM entry procedure for `minRatioMachineContractWithV`
operation 0 (`Update`).
Arguments: `[root, batch, g, l, eta, heap]` (`reg 0 .. reg 5`).
Writes `AnswerAt` at `heap`, `2 * L`-limb `actual` at `heap + 1`, updates the solver
state, and returns the new free heap pointer. -/
@[expose] def solverUpdateBody (growTables copyWords freshBatch chainRefresh cycleLoop
    subtract goodApply failOut : ℕ) : Stmt :=
  solverUpdatePrepBody growTables copyWords freshBatch ;;
  .call 16 chainRefresh [.reg 0, .reg 18, .reg 41, .reg 42, .reg 14, .reg 16] ;;
  .assign 10 (.load (.bin .add (.reg 14) (.bin .add (.reg 9) (.const 1)))) ;;
  .call 16 cycleLoop [.reg 0, .reg 14, .reg 10, .reg 11, .reg 13, .reg 16] ;;
  .assign 22 (.load (.reg 13)) ;;
  .cond (.reg 22)
    (.assign 23 (.load (.bin .add (.reg 13) (.const 1))) ;;
     .assign 24 (.load (.reg 23)) ;;
     .assign 25 (.load (.bin .add (.reg 23) (.const 2))) ;;
     .assign 26 (.load (.bin .add (.reg 23) (.const 3))) ;;
     .assign 27 (.load (.bin .add (.reg 23) (.const 4))) ;;
     .assign 28 (.load (.bin .add (.reg 23) (.const 5))) ;;
     .assign 29 (.bin .add (.reg 16) (.reg 7)) ;;
     .call 16 subtract [.reg 15, .reg 24, .reg 7, .reg 16] ;;
     .call 16 goodApply [.reg 0, .reg 31, .reg 29, .reg 25, .reg 26, .reg 27, .reg 28, .reg 5, .reg 16] ;;
     .ret (.reg 16))
    (.call 30 failOut [.reg 31, .reg 7, .reg 8, .reg 5] ;;
     .ret (.reg 16))

theorem solverUpdateBody_noRand (growTables copyWords freshBatch chainRefresh cycleLoop
    subtract goodApply failOut : ℕ) :
    (solverUpdateBody growTables copyWords freshBatch chainRefresh cycleLoop
      subtract goodApply failOut).NoRand := by
  have := copyInsertedStmt_noRand copyWords
  simp [solverUpdateBody, solverUpdatePrepBody, solverUpdatePrefix, Stmt.NoRand, this]

/-- Every fixed-graph refresh batch uses at most `4 * U.length + 1` words. -/
theorem batchWords_length_le_of_refresh {G : MGraph} {U : List Update}
    (hU : RefreshBatch G U) : (batchWords U).length ≤ 4 * U.length + 1 := by
  suffices h : ∀ xs : List Update,
      (∀ u ∈ xs, match u with | .split _ _ _ _ => False | _ => True) →
      (xs.flatMap updateWords).length ≤ 4 * xs.length by
    have h1 := h U fun u hu => by
      have := hU.2.2 u hu; cases u with
      | split _ _ _ _ => exact this
      | delete _ => trivial
      | insert _ _ _ => trivial
    simp only [batchWords, List.length_cons]; omega
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons u us ih =>
    intro hrec
    have hu := hrec u List.mem_cons_self
    have htail := ih (fun v hv => hrec v (List.mem_cons_of_mem _ hv))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    cases u with
    | split _ _ _ _ => exact False.elim hu
    | delete _ => simp only [updateWords, List.length_cons, List.length_nil]; omega
    | insert _ _ _ => simp only [updateWords, List.length_cons, List.length_nil]; omega

/-- Disjointness of `FreshBatchRegions` directly from `SolverTagsAt` tags 6, 7, 8 and
`batchCopy` placed above the solver footprint. -/
theorem freshBatchRegions_separated_of_solver {cfg : Alg2Config}
    {L P m V psi qExp epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {root batchCopy output : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi qExp epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi qExp epsExp drainUnit Rcore).foot root tok a →
      a < batchCopy)
    (hmPos : 0 < m) (hcapPos : 0 < tok.intCap) :
    FreshBatchRegions.Separated
      { forward := tok.forward, inverse := tok.inverse, counter := tok.freshCounter,
        externalCap := m, internalCap := tok.intCap, input := batchCopy + 1, output := output } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, _, _, _, _, _, t6, t7, t8, _⟩ := htags
  have hlt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < batchCopy :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  dsimp only [FreshBatchRegions.Separated]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hlt (t7 (m - 1) (by omega)) (by decide); omega
  · have := hlt (t8 (tok.intCap - 1) (by omega)) (by decide); omega
  · have := hlt t6 (by decide); omega
  · by_contra h; push Not at h
    by_cases hfi : tok.forward ≤ tok.inverse
    · have h7 := t7 (tok.inverse - tok.forward) (by omega)
      have h8 := t8 0 (by omega)
      rw [Nat.add_sub_of_le hfi] at h7; rw [Nat.add_zero] at h8
      exact absurd (h7.symm.trans h8) (by decide)
    · have h7 := t7 0 (by omega)
      have h8 := t8 (tok.forward - tok.inverse) (by omega)
      rw [Nat.add_zero] at h7; rw [Nat.add_sub_of_le (by omega)] at h8
      exact absurd (h7.symm.trans h8) (by decide)
  · by_contra h; push Not at h
    have h7 := t7 (tok.freshCounter - tok.forward) (by omega)
    rw [Nat.add_sub_of_le h.1] at h7
    exact absurd (t6.symm.trans h7) (by decide)
  · by_contra h; push Not at h
    have h8 := t8 (tok.freshCounter - tok.inverse) (by omega)
    rw [Nat.add_sub_of_le h.1] at h8
    exact absurd (t6.symm.trans h8) (by decide)

/-- The `PathIntAt` representation of `0` on `L` zero words. -/
theorem pathIntAt_zero_of_zeroFrom {mem : ℕ → ℕ} {a L : ℕ}
    (hz : ∀ j < L, mem (a + j) = 0) : PathIntAt mem a 4 L 0 := by
  refine ⟨fun j hj => by rw [hz j hj]; decide, ?_⟩
  have hu : Num.unsignedVal mem a 4 L = 0 := by
    induction L generalizing a with
    | zero => rfl
    | succ n ih =>
      simp only [Num.unsignedVal]
      have h0 : mem a = 0 := by simpa using hz 0 (Nat.zero_lt_succ n)
      have htail : ∀ j < n, mem (a + 1 + j) = 0 := fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hz (j + 1) (by omega)
      rw [h0, ih htail]; simp
  unfold Num.intVal Num.signedVal
  rw [hu]
  simp [Num.capacity, Num.base]

/-- Whenever `Chain.Ordered.algorithm2_loopWith` returns `some Δ`, `Δ` is the lifted candidate cycle of
the final chain state and satisfies the loop acceptance inequality. -/
theorem algorithm2_loopWith_some_spec (cfg : Alg2Config) (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) (Δ : ℕ → ℝ) :
    let res := Chain.Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    res.2.2.2.2 = some Δ →
    Δ = liftEdgeFn extG e2i (algorithm1_findCycle res.1).1 ∧
    extG.inner g' Δ / extG.lnorm ℓ' Δ ≤ -(κ * cfg.α) := by
  suffices h : ∀ N ch branD passes lctOps,
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ N →
      let res := Chain.Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      res.2.2.2.2 = some Δ →
      Δ = liftEdgeFn extG e2i (algorithm1_findCycle res.1).1 ∧
      extG.inner g' Δ / extG.lnorm ℓ' Δ ≤ -(κ * cfg.α) from
    h _ ch branD passes lctOps le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ch branD passes lctOps hN res
    dsimp only [res]
    rw [Chain.Ordered.algorithm2_loopWith]
    dsimp only
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
    · rw [dite_eq_left hGood]
      intro hsome
      have hΔ : liftEdgeFn extG e2i (algorithm1_findCycle ch).1 = Δ := Option.some.inj hsome
      exact ⟨hΔ.symm, hΔ ▸ hGood⟩
    · rw [dite_eq_right hGood]
      split
      · intro hsome; cases hsome
      · rename_i i _
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left hCap]
          have hlt := Chain.Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          exact ih (N - 1) (by omega) _ _ _ _ (by omega)
        · rw [dite_eq_right hCap]
          intro hsome; cases hsome

/-- A `RefreshBatch` encoded by `BatchAt` is uniquely determined by memory: no other
`List Update` can share the same `batchWords` at the same address. -/
theorem batchAt_unique_of_refresh {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U U' : List Update}
    (hU : RefreshBatch G U) (h1 : BatchAt mem a U) (h2 : BatchAt mem a U') : U' = U := by
  obtain ⟨hlen1, hbody1⟩ := listAt_cons.mp h1
  obtain ⟨hlen2, hbody2⟩ := listAt_cons.mp h2
  have hlenEq : U'.length = U.length := hlen2.symm.trans hlen1
  suffices h : ∀ (b : ℕ) (xs ys : List Update),
      (∀ u ∈ xs, match u with | .split _ _ _ _ => False | _ => True) →
      ys.length = xs.length →
      ListAt mem b (xs.flatMap updateWords) →
      ListAt mem b (ys.flatMap updateWords) → ys = xs by
    exact h (a + 1) U U' (fun u hu => by
      have := hU.2.2 u hu
      cases u with
      | split _ _ _ _ => exact this
      | insert _ _ _ => trivial
      | delete _ => trivial) hlenEq hbody1 hbody2
  intro b xs
  induction xs generalizing b with
  | nil =>
    intro ys _ hlen _ _
    exact List.eq_nil_of_length_eq_zero hlen
  | cons x xs ih =>
    intro ys hns hlen hb1 hb2
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hx := hns x List.mem_cons_self
      have hxs : ∀ u ∈ xs, match u with | .split _ _ _ _ => False | _ => True :=
        fun u hu => hns u (List.mem_cons_of_mem _ hu)
      have hlen' : ys.length = xs.length := by simpa using hlen
      rw [List.flatMap_cons] at hb1 hb2
      obtain ⟨hxw, hxsW⟩ := listAt_append.mp hb1
      obtain ⟨hyw, hysW⟩ := listAt_append.mp hb2
      have htag : (updateWords y)[0]! = (updateWords x)[0]! := by
        have h0x : mem b = (updateWords x)[0]! := by
          cases x with
          | split _ _ _ _ => exact False.elim hx
          | insert e u v => simpa [updateWords] using hxw 0 (by simp [updateWords])
          | delete e => simpa [updateWords] using hxw 0 (by simp [updateWords])
        have h0y : mem b = (updateWords y)[0]! := by
          cases y with
          | split _ _ _ _ => simpa [updateWords] using hyw 0 (by simp [updateWords])
          | insert e u v => simpa [updateWords] using hyw 0 (by simp [updateWords])
          | delete e => simpa [updateWords] using hyw 0 (by simp [updateWords])
        exact h0y.symm.trans h0x
      cases x with
      | split _ _ _ _ => exact False.elim hx
      | insert ex ux vx =>
        cases y with
        | insert ey uy vy =>
          have h1e : ey = ex :=
            (by simpa [updateWords] using hyw 1 (by simp [updateWords]) : mem (b + 1) = ey).symm.trans
              (by simpa [updateWords] using hxw 1 (by simp [updateWords]))
          have h2u : uy = ux :=
            (by simpa [updateWords] using hyw 2 (by simp [updateWords]) : mem (b + 2) = uy).symm.trans
              (by simpa [updateWords] using hxw 2 (by simp [updateWords]))
          have h3v : vy = vx :=
            (by simpa [updateWords] using hyw 3 (by simp [updateWords]) : mem (b + 3) = vy).symm.trans
              (by simpa [updateWords] using hxw 3 (by simp [updateWords]))
          subst h1e; subst h2u; subst h3v
          have htail := ih (b + 4) ys hxs hlen'
            (by simpa [updateWords] using hxsW) (by simpa [updateWords] using hysW)
          rw [htail]
        | delete _ => simp [updateWords] at htag
        | split _ _ _ _ => simp [updateWords] at htag
      | delete ex =>
        cases y with
        | delete ey =>
          have h1e : ey = ex :=
            (by simpa [updateWords] using hyw 1 (by simp [updateWords]) : mem (b + 1) = ey).symm.trans
              (by simpa [updateWords] using hxw 1 (by simp [updateWords]))
          subst h1e
          have htail := ih (b + 2) ys hxs hlen'
            (by simpa [updateWords] using hxsW) (by simpa [updateWords] using hysW)
          rw [htail]
        | insert _ _ _ => simp [updateWords] at htag
        | split _ _ _ _ => simp [updateWords] at htag

end MinCostFlow.MinRatio
