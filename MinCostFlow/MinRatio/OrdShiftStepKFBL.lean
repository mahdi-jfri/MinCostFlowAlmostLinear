module

public import MinCostFlow.MinRatio.OrdShiftStepSpecW
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.MinRatio.ShiftTermFacts
public import MinCostFlow.MinRatio.ShiftDeepModelFacts
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.SolverLevelCapsInv
public import MinCostFlow.MinRatio.OrdChainRefreshWired
public import MinCostFlow.MinRatio.UpdateAssemblyBase

/-!
# Wired credit-bearing level-shift contract with `KFBL` deep shift (`OrdShiftStepKFBL`)

Defines `ShiftLevelStepSpecWKFBL`, upgrading `ShiftLevelStepSpecW` to thread
`SolverLevelMetaAt P V`, `SolverLevelCapsAt vCap eCap`, `tok.table`, `tok.rootECap`, and the
select-region directory pointers (`solverSelectHeapAddr`, `solverSelectBlocksAddr`) across
`shiftLevelWiredBody`, and proves `shiftLevelStepSpecWKFBL_wired` from:
* `ShiftTermChainSyncSpecWExt` extended with level-metadata, level-cap, and select-pointer
  preservation (`ShiftTermChainSyncSpecWExtKFBL`);
* `ShiftDeepChainSyncSpecWExtKFBL` (`WireShiftDeepSpecKFBL.lean`);
* `shiftDeepModelInvKFBL_of_loopInv` and the tight `2 * (model.chain.G 0).n` suffix-forest edge
  bound `shiftDeep_forestEdgeSum_le_two_G0_n` (`ShiftDeepModelFacts.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

/-- Terminal-shift sync contract extending `ShiftTermChainSyncSpecWExt` with preservation of
`SolverLevelMetaAt`, `SolverLevelCapsAt`, `tok.table`, `tok.rootECap`, and the select-region
directory pointers (`solverSelectHeapAddr`, `solverSelectBlocksAddr`). -/
@[expose] def ShiftTermChainSyncSpecWExtKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftTermChainProc : ℕ) (termSpace termFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftTermChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
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
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + termSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
          mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
        out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
          mem0 (solverSelectBlocksAddr tok.table cfg.P.d) ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          termFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem0

/-- Wired credit-bearing level-shift contract for `shiftLevelWiredBody` under the `KFBL` layout
contract: extends `ShiftLevelStepSpecW` with `SolverLevelMetaAt`, `SolverLevelCapsAt`,
`ShiftDeepModelInv`, `tok.intCap ≤ intCapMax`, and `2 * (model.chain.G 0).n ≤ forestEdgeCap`,
preserving `SolverLevelMetaAt`, `SolverLevelCapsAt`, `tok.table`, `tok.rootECap`, and the
select-region directory pointers. -/
@[expose] def ShiftLevelStepSpecWKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftLevelProc shiftSpace shiftFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftLevelProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
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
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      (i.val < cfg.P.d → ShiftDeepModelInv w L P wordExp stretchPrec model i) →
      tok.intCap ≤ intCapMax →
      2 * (model.chain.G 0).n ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + shiftSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
          mem (solverSelectHeapAddr tok.table cfg.P.d) ∧
        out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
          mem (solverSelectBlocksAddr tok.table cfg.P.d) ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelMetaAt P V model' tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          shiftFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem

/-- Discharges `ShiftLevelStepSpecWKFBL` for `shiftLevelWiredBody` from
`ShiftTermChainSyncSpecWExtKFBL` (at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`) and
`ShiftDeepChainSyncSpecWExtKFBL`. Discharges `ShiftDeepModelInvKFBL` via
`shiftDeepModelInvKFBL_of_loopInv` and the suffix-forest edge bound via
`shiftDeep_forestEdgeSum_le_two_G0_n`. -/
theorem shiftLevelStepSpecWKFBL_wired
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap shiftLevelProc shiftTermChainProc shiftDeepChainProc
      termSpace termFixed deepSpace deepFixed toolMul treeMul : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hV : cfg.ValidOrdNoHidden)
    (hTerm : ShiftTermChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      (2 * levelM cfg.TP cfg.P cfg.P.d) vCap eCap cfg Rcore p shiftTermChainProc
      termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p shiftDeepChainProc
      deepSpace deepFixed toolMul treeMul)
    (hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) :
    ShiftLevelStepSpecWKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p shiftLevelProc
      (max termSpace deepSpace) (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
      toolMul treeMul := by
  obtain ⟨bTerm, hbTerm, hTermRun⟩ := hTerm
  obtain ⟨bDeep, hbDeep, hDeepRun⟩ := hDeep
  refine ⟨shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc, hAt, ?_⟩
  intro root heap pos i ω mem model tok B R
  dsimp only
  intro hAcc hBranchLt hBrAll hQuotaW hPassW hrep hMeta hCaps hLoopInv hDeepModel hIntCap hFEdge
    hlogW hcapTree hnum hoff hbd hCap hbelow hz hroom
  let model' := alg2LoopShiftStep cfg model i
  let Δ := toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
    treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates)
  obtain ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hrep', hnum', hoff', hz', hfr, hft, hc,
      ⟨hintCap, htbl, hrecap, hsh, hsb, hMeta', hCaps', hbd'⟩⟩ :=
    shiftLevelWiredBody_runs_gen (termSpace := termSpace) (termBudget := termFixed + Δ)
      (deepSpace := deepSpace) (deepBudget := deepFixed + Δ)
      (Q := fun tok' mem' =>
        tok'.intCap = tok.intCap ∧
        tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
        mem' (solverSelectHeapAddr tok.table cfg.P.d) =
          mem (solverSelectHeapAddr tok.table cfg.P.d) ∧
        mem' (solverSelectBlocksAddr tok.table cfg.P.d) =
          mem (solverSelectBlocksAddr tok.table cfg.P.d) ∧
        SolverLevelMetaAt P V model' tok' mem' ∧
        SolverLevelCapsAt vCap eCap model' tok' mem' ∧
        OffTreeRecBound model' L mem' tok'.edgeRecords B)
      hbTerm hbDeep
      (fun hiEq posIn memIn htag hsched hzIn hrmIn => by
        obtain ⟨f1, f2, f5, f6, f7, f8, f9⟩ := shiftTerm_reached_facts_1_to_9 hV hLoopInv hrep hbelow
          (lt_of_le_of_lt (Nat.le_add_right heap _) hroom)
        obtain ⟨nh, c, o, t', r, lo, hi, lv, ic, tbl, rcap, sh, sb, rep, meta', caps', num, off,
            bd, z', fr, ft, hc⟩ :=
          hTermRun root heap posIn ω mem memIn model tok B R hrep hMeta hCaps htag hsched hnum hoff
            hbd hCap hBrAll f1 f2 hlogW hcapTree f5 f6 f7 f8 f9 hbelow hzIn hrmIn
        have hΔeq : Δ = toolMul * ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalRuntime -
              model.chain.totalRuntime) +
            treeMul * ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalTreeUpdates -
              model.chain.totalTreeUpdates) := by
          dsimp only [Δ, model']; rw [hiEq]
        refine ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, ?_,
          ic, tbl, rcap, sh, sb, ?_, ?_, ?_⟩
        · rw [hΔeq]; omega
        · dsimp only [model']; rw [hiEq]; exact meta'
        · dsimp only [model']; rw [hiEq]; exact caps'
        · dsimp only [model']; rw [hiEq]; exact bd)
      (fun hiD posIn memIn htag hsched hzIn hrmIn => by
        have hK : ShiftDeepModelInvKFBL model i := shiftDeepModelInvKFBL_of_loopInv hV hLoopInv hiD
        have hSum := (shiftDeep_forestEdgeSum_le_two_G0_n hV hLoopInv hiD).1.trans hFEdge
        obtain ⟨nh, c, o, t', r, lo, hi, lv, ic, tbl, rcap, sh, sb, rep, meta', caps', _hlay, num, off,
            bd, z', fr, ft, hc⟩ :=
          hDeepRun root heap posIn i ω mem memIn model tok B R hiD hrep hMeta hCaps htag hsched
            hnum hoff hbd hCap hBrAll (hDeepModel hiD) hK hIntCap hSum hlogW hcapTree hbelow hzIn
            hrmIn
        refine ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, ?_,
          ic, tbl, rcap, sh, sb, meta', caps', bd⟩
        dsimp only [Δ, model'] at hc ⊢; omega)
      hw17 hdW hkW hAcc hBranchLt hQuotaW hPassW hrep hbelow hz hroom
  refine ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hintCap, htbl, hrecap, hsh, hsb, hrep', hMeta',
    hCaps', hnum', hoff', hbd', hz', hfr, hft, ?_⟩
  have hmax : max (termFixed + Δ) (deepFixed + Δ) = max termFixed deepFixed + Δ := by omega
  rw [hmax] at hc
  dsimp only [Δ, model'] at hc ⊢
  omega

/-- A terminal shift (`i = Fin.last cfg.P.d`) does not change `N₀`, `lvlM`, or any non-terminal
level `j < cfg.P.d` (`G`, `scState`, `bran`, `ℓ`). -/
private theorem alg2LoopShiftStep_last_levels_kfbl (cfg : Alg2Config) (model : Alg2State cfg) :
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    model'.chain.N₀ = model.chain.N₀ ∧
    (∀ j < cfg.P.d, model'.chain.lvlM j = model.chain.lvlM j) ∧
    (∀ j < cfg.P.d, model'.chain.G j = model.chain.G j) ∧
    (∀ j < cfg.P.d, model'.chain.scState j = model.chain.scState j) ∧
    (∀ j < cfg.P.d, model'.chain.bran j = model.chain.bran j) ∧
    model'.chain.ℓ = model.chain.ℓ := by
  dsimp only [alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hnot : ¬ (Fin.last cfg.P.d).val < cfg.P.d := by simp
  rw [dif_neg hnot]
  exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- `ShiftTermChainSyncSpecWExt` (which already exports `PreservesLevelMeta`) directly implies
`ShiftTermChainSyncSpecWExtKFBL` at any caps `(vCap, eCap)`. -/
theorem shiftTermChainSyncSpecWExt_to_KFBL
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap vCap eCap
      shiftTermChainProc termSpace termFixed toolMul treeMul : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    (hTerm : ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      lastTreeCap cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul) :
    ShiftTermChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      lastTreeCap vCap eCap cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul := by
  obtain ⟨body, hbody, hRun⟩ := hTerm
  refine ⟨body, hbody, ?_⟩
  intro root heap pos ω mem0 mem model tok B R
  dsimp only
  intro hrep hMeta hCaps hMemEq hSched' hnum hoff hBd hCapF hBr hLastBranLt hLastKW hLogW hCapT
    hNewForest hOldSub hNewSub hDisjPref hLastCap hbelow hz hroom
  obtain ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hintCap, hrep', hPres, hnum', hoff', hBd', hz',
      hfr, hft, hc⟩ :=
    hRun root heap pos ω mem0 mem model tok B R hrep hMemEq hSched' hnum hoff hBd hCapF hBr
      hLastBranLt hLastKW hLogW hCapT hNewForest hOldSub hNewSub hDisjPref hLastCap hbelow hz hroom
  obtain ⟨hN0, hM, hG, hSc, hBrEq, hℓ⟩ := alg2LoopShiftStep_last_levels_kfbl cfg model
  have hCapsInv' : SolverLevelCapsInv P V vCap eCap (alg2LoopShiftStep cfg model (Fin.last cfg.P.d))
      tok' out.mem :=
    hPres.to_capsInv ⟨hMeta, hCaps⟩ hN0 hM hG hSc hBrEq hℓ
  have hTagSH : tok.tag (solverSelectHeapAddr tok.table cfg.P.d) = 21 + cfg.P.d := hMeta.1.2.2.1
  have hTagSB : tok.tag (solverSelectBlocksAddr tok.table cfg.P.d) = 21 + cfg.P.d := hMeta.1.2.2.2
  exact ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hintCap, hPres.tableEq, hPres.rootECapEq,
    (hPres.metaEq _ (Or.inr (Or.inl hTagSH))).2,
    (hPres.metaEq _ (Or.inr (Or.inl hTagSB))).2,
    hrep', hCapsInv'.1, hCapsInv'.2, hnum', hoff', hBd', hz', hfr, hft, hc⟩

/-- Discharges `ShiftLevelStepSpecWKFBL` for `shiftLevelWiredBody` directly from
`ShiftTermChainSyncSpecWExt` (at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`) and
`ShiftDeepChainSyncSpecWExtKFBL`. -/
theorem shiftLevelStepSpecWKFBL_wired_of_termExt
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap shiftLevelProc shiftTermChainProc shiftDeepChainProc
      termSpace termFixed deepSpace deepFixed toolMul treeMul : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hV : cfg.ValidOrdNoHidden)
    (hTerm : ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      (2 * levelM cfg.TP cfg.P cfg.P.d) cfg Rcore p shiftTermChainProc
      termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p shiftDeepChainProc
      deepSpace deepFixed toolMul treeMul)
    (hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) :
    ShiftLevelStepSpecWKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p shiftLevelProc
      (max termSpace deepSpace) (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
      toolMul treeMul :=
  shiftLevelStepSpecWKFBL_wired hAt hV (shiftTermChainSyncSpecWExt_to_KFBL hTerm) hDeep hw17 hdW hkW

/-- Ordered chain-update core contract extending `OrdChainUpdateCoreSpecW` with maintenance of
`SolverLevelMetaAt P V` and `SolverLevelCapsAt vCap eCap`. -/
@[expose] def OrdChainUpdateCoreSpecWKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap : ℕ)
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
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
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
        SolverLevelMetaAt P V modelPre tok' out.mem ∧
        SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
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

/-- Wired credit-bearing chain-refresh contract extending `ChainRefreshStepSpecW` with maintenance
of `SolverLevelMetaAt P V` and `SolverLevelCapsAt vCap eCap`. -/
@[expose] def ChainRefreshStepSpecWKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap : ℕ)
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
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
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
        SolverLevelMetaAt P V model1 tok' out.mem ∧
        SolverLevelCapsAt vCap eCap model1 tok' out.mem ∧
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

private theorem offTreeRecBound_preReset_to_preLoop_kfbl {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} {L : ℕ} {mem : ℕ → ℕ} {edgeRecords : ℕ} {B : ℤ}
    (h : OffTreeRecBound (alg2PreResetState cfg model U gVec lVec) L mem edgeRecords B) :
    OffTreeRecBound (alg2PreLoopState cfg model U gVec lVec) L mem edgeRecords B := h

/-- Discharges `ChainRefreshStepSpecWKFBL` for `ordChainRefreshWiredBody` from
`OrdChainUpdateCoreSpecWKFBL` and `ShiftQuotaWriterSpec`. -/
theorem chainRefreshStepSpecWKFBL_wired
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap chainRefreshProc
      ordEditsProc ordChainCoreProc shiftQuotaWriterProc quotaBudget toolMul treeMul : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {B_bound R_bound : ℤ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[chainRefreshProc]? =
      some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc))
    (hEditsAt : p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody)
    (hCore : OrdChainUpdateCoreSpecWKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      vCap eCap cfg Rcore p ordChainCoreProc coreSpace coreFixed toolMul treeMul B_bound R_bound)
    (hQuota : ShiftQuotaWriterSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftQuotaWriterProc quotaBudget)
    (hw11 : 11 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) :
    ChainRefreshStepSpecWKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit vCap eCap
      cfg Rcore p chainRefreshProc
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreFixed uLen + quotaBudget + 120 * uLen + 62 * (cfg.P.d + 1) + 240)
      toolMul treeMul B_bound R_bound := by
  obtain ⟨bCore, hbCore, hCoreRun⟩ := hCore
  refine ⟨ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc, hAt, ?_⟩
  intro root uIntBuf g l quotaBase heap pos ω mem0 mem model tok U
  dsimp only
  intro hrep0 hMeta0 hCaps0 hCap htags0 hfreshTab hnfCap hbatchInt hsmallInt hRefreshU hwordsU
    hKeyW hQuotaW hfootLt hgEnd hlEnd hqEnd hqOut huLeH hz hroom
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let model1 := alg2PreLoopState cfg model U gVec lVec
  let coreBud := coreFixed U.length +
    toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
    treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates)
  obtain ⟨nextHeap, cost, out, tok', B', R', memCore, hr, hlo, hhi, hB, hR, hrep, hnum, hoff,
      hq, hpsi, hz', hfr, hft, hc, hrepCore, ⟨hlev, hintCap, hMetaCore, hCapsCore, hbdCore⟩, hag, _⟩ :=
    ordChainRefreshWiredBody_runs_gen (coreSpace := coreSpace U.length) (coreBudget := coreBud)
      (Q := fun tok' memC B' _ =>
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        SolverLevelMetaAt P V modelPre tok' memC ∧
        SolverLevelCapsAt vCap eCap modelPre tok' memC ∧
        OffTreeRecBound modelPre L memC tok'.edgeRecords B')
      (extraFoot := fun _ => False)
      hlocal hEditsAt hbCore
      (fun memIn posIn _ htagI hfrI hbaI hsmI hordI hedW hzI hrmI => by
        obtain ⟨nh, c, o, t', B', R', r, lo, hi, lv, ic, hB, hR, rep, meta', caps', num, off, bd,
            z', fr, ft, hc⟩ :=
          hCoreRun root uIntBuf (heap + cfg.P.d)
            (1 + batchOrdPayloadWords (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2)
            g l _ posIn ω mem0 memIn model tok U
            hrep0 hMeta0 hCaps0 hCap htagI hfrI hnfCap hbaI hsmI hordI hedW rfl hRefreshU hfootLt
            hgEnd hlEnd (by omega) hzI hrmI
        exact ⟨nh, c, o, t', B', R', r, lo, hi, hB, hR, rep, num, off, z',
          fun a ha hnf _ => fr a ha hnf, ft, hc, lv, ic, meta', caps', bd⟩)
      hQuota hw11 hdW hrep0 htags0 hfreshTab hbatchInt hsmallInt hRefreshU hwordsU hKeyW
      hQuotaW hfootLt (fun _ h => False.elim h) hqEnd hqOut huLeH hz hroom
  have hbdOut : OffTreeRecBound model1 L out.mem tok'.edgeRecords B' :=
    offTreeRecBound_preReset_to_preLoop_kfbl (offTreeRecBound_of_agree hrepCore hbdCore fun a ha =>
      hag a (by rcases ha with h | h <;> omega) (by rcases ha with h | h <;> omega))
  have hCapsInvOut : SolverLevelCapsInv P V vCap eCap model1 tok' out.mem := by
    have hPres : PreservesLevelMeta tok' tok' memCore out.mem :=
      (PreservesLevelMeta.refl tok' memCore).congr_mem_right fun a ht =>
        hag a (by rcases ht with h | h | h | h <;> omega)
          (by rcases ht with h | h | h | h <;> omega)
    exact hPres.to_capsInv ⟨hMetaCore, hCapsCore⟩ rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) rfl
  refine ⟨nextHeap, cost, out, tok', B', R', hr, hlo, hhi, hlev, hintCap, hB, hR, hrep,
    hCapsInvOut.1, hCapsInvOut.2, hnum, hoff, hbdOut, hq, hpsi, hz',
    fun a ha hnf hnotQ => hfr a ha hnf (by decide) hnotQ, hft, ?_⟩
  dsimp only [coreBud, model1, modelPre, gVec, lVec, alg2PreLoopState, alg2PreResetState] at hc ⊢
  omega

/-- Credit-bearing execution of `updateCycleLoopBody` under the `KFBL` layout contract: uses
`ShiftLevelStepSpecWKFBL` and threads `SolverLevelCapsInv P V vCap eCap` and `DeepInv`. -/
theorem updateCycleLoopBody_runs_credit_kfbl
    {w L P m U V psi k qHdr epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec
      intCapMax forestEdgeCap vCap eCap findCycleProc updateQualityProc shiftCheckProc
      shiftLevelProc findSpace findBudget maxEdges maxPaths shiftSpace shiftBudget
      toolMul treeMul root quotaBase descOut heap pos : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ} {lctOps : ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T) (hV : cfg.ValidOrdNoHidden)
    (hα : cfg.α = Num.IPM.alphaPrime m U / 8)
    (hFind : FindCycleStepSpecW w L P m V psi qHdr epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      findCycleProc findSpace findBudget maxEdges maxPaths)
    (hQual : ∀ inner norm, MeetsContract w p updateQualityProc
      (updateQualityFromNormContract w 4 m U k P inner norm))
    (hCheck : p.procs[shiftCheckProc]? = some shiftCheckBody)
    (hShift : ShiftLevelStepSpecWKFBL w L P m V psi qHdr epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p
      shiftLevelProc shiftSpace shiftBudget toolMul treeMul)
    (hFEdgeCap : 2 * cfg.N₀ ≤ forestEdgeCap)
    (hDeepShift : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch → DeepInv ch →
      ∀ i ≤ cfg.P.d, DeepInv (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i).1)
    (hDeepToModel : ∀ (m0 : Alg2State cfg) (i : Fin (cfg.P.d + 1)), i.val < cfg.P.d →
      Chain.Ordered.ShiftLoopChainInv cfg m0.chain → DeepInv m0.chain →
      ShiftDeepModelInv w L P wordExp stretchPrec m0 i)
    (hw11 : 11 < 2 ^ w) (h5L1W : 5 * L + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hqW : k + Num.IPM.alphaExponent m U + 3 < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (hrep : (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hDeep : DeepInv model.chain)
    (hIntCap : tok.intCap ≤ intCapMax)
    (hLoopInv : Chain.Ordered.ShiftLoopChainInv cfg model.chain)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit model)
    (hcapEval : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapTree : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hlenNN : ∀ e ∈ model.extG.E, 0 ≤ model.extℓ e)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hqBelow : quotaBase + cfg.P.d < heap)
    (hquotas : ∀ i ≤ cfg.P.d, mem (quotaBase + i) =
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i)
    (hquotasW : ∀ i ≤ cfg.P.d,
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w)
    (hBr : BranchesLtK cfg model)
    (hqOut : ∀ i ≤ cfg.P.d, ¬ (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok (quotaBase + i))
    (hdescBelow : descOut + 1 < heap)
    (hdescOut0 : ¬ (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok descOut)
    (hdescOut1 : ¬ (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok (descOut + 1))
    (hz : ZeroFrom mem heap)
    (hroom : heap + (loopStepBound cfg model + 1) *
      cycleLoopIterSpace L findSpace shiftSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore
    let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
      model.extg model.extℓ model.chain model.branD model.passes lctOps
    let modelEnd : Alg2State cfg :=
      { model with
        chain := loopRes.1
        branD := loopRes.2.1
        passes := loopRes.2.2.1 }
    ∃ ret cost out tokEnd,
      Runs w p ω (updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc)
        (startState [root, quotaBase, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊,
          k + Num.IPM.alphaExponent m U + 3, descOut, heap] mem pos)
        (.returned ret) out cost ∧
      heap ≤ ret ∧ ret ≤ heap + (loopStepBound cfg model + 1) * cycleLoopIterSpace L findSpace shiftSpace ∧
      out.mem descOut = (if loopRes.2.2.2.2.isSome then 1 else 0) ∧
      Rrep.rep root modelEnd tokEnd out.mem ∧
      SolverLevelCapsInv P V vCap eCap modelEnd tokEnd out.mem ∧
      DeepInv modelEnd.chain ∧
      tokEnd.intCap = tok.intCap ∧
      PathTreeNumericInv tokEnd.tree tokEnd.trees B R ∧
      OffTreeRecInv modelEnd L out.mem tokEnd.edgeRecords B ∧
      (loopRes.2.2.2.2.isSome →
        ∃ inner norm edges paths,
          CycleDescriptorAt modelEnd L P out.mem (out.mem (descOut + 1)) ret inner norm edges paths ∧
          edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
          (∀ x < 2 * edges.length, tokEnd.tag (out.mem (out.mem (descOut + 1) + 2) + x) = 0) ∧
          (∀ x < 2 * paths.length, tokEnd.tag (out.mem (out.mem (descOut + 1) + 4) + x) = 0) ∧
          (∀ a, tokEnd.tag a = 18 → a < out.mem (descOut + 1)) ∧
          heap ≤ out.mem (descOut + 1) ∧ out.mem (descOut + 1) + 6 ≤ ret) ∧
      ZeroFrom out.mem ret ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → a ≠ descOut → a ≠ descOut + 1 → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tokEnd a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + Rrep.phi root tokEnd out.mem +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        (N + 1) * cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 80 +
        Rrep.phi root tok mem +
        toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates := by
  obtain ⟨bS, hbS, hS⟩ := hShift
  let Inv : Alg2State cfg → SolverToken cfg L Rcore → (ℕ → ℕ) → Prop :=
    fun stM t mem => SolverLevelCapsInv P V vCap eCap stM t mem ∧ DeepInv stM.chain ∧ t.intCap ≤ intCapMax
  have hInvFind : ∀ stM t t' mem mem',
      (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root stM t mem →
      Inv stM t mem → PreservesLevelMeta t t' mem mem' → t'.intCap = t.intCap → Inv stM t' mem' := by
    intro stM t t' mem mem' _ ⟨hC, hD, hI⟩ hPres hEq
    exact ⟨hPres.to_capsInv hC rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl, hD, hEq ▸ hI⟩
  have hInvMem : ∀ stM t mem mem',
      (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root stM t mem →
      Inv stM t mem →
      (∀ a, (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root t a →
        mem' a = mem a) →
      Inv stM t mem' := by
    intro stM t mem mem' hrep' ⟨hC, hD, hI⟩ hag
    have hPres : PreservesLevelMeta t t mem mem' :=
      (PreservesLevelMeta.refl t mem).congr_mem_right fun a ht =>
        hag a (LevelMetaFoot.mem_foot hrep' ht)
    exact ⟨hPres.to_capsInv hC rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl, hD, hI⟩
  obtain ⟨ret, c, out, tokEnd, hr, hlo, hhi, hdesc, hrep', ⟨hCapsEnd, hDeepEnd, _⟩, hcap', hnum',
      hoff', hsome, hz', hfr', hft', hc'⟩ :=
    updateCycleLoopBody_runs_credit_gen hlocalCore Inv hInvFind hInvMem hMono hV hα hFind hQual
      hCheck ⟨bS, hbS, fun r h pos i ω mem stM t B R h1 h2 h3 h4 h5 h6 ⟨hC, hD, hI⟩ hLoop h7 h8 h9
          h10 h11 h12 h13 h14 h15 => by
        have hFEdge : 2 * (stM.chain.G 0).n ≤ forestEdgeCap := by
          have hn : (stM.chain.G 0).n ≤ cfg.N₀ := hLoop.1.hG0n
          omega
        obtain ⟨nh, c, o, t', hr, hlo, hhi, hl, hi, _, _, _, _, hrep', hM', hC', hn', ho', hb',
            hz', hfr', hft', hc'⟩ :=
          hS r h pos i ω mem stM t B R h1 h2 h3 h4 h5 h6 hC.1 hC.2 hLoop
            (fun hiD => hDeepToModel stM i hiD hLoop hD) hI hFEdge h7 h8 h9 h10 h11 h12 h13 h14 h15
        have hD' : DeepInv (alg2LoopShiftStep cfg stM i).chain :=
          hDeepShift stM.chain hLoop hD i.val (Nat.lt_succ_iff.mp i.isLt)
        exact ⟨nh, c, o, t', hr, hlo, hhi, hl, hi, hrep', ⟨⟨hM', hC'⟩, hD', hi ▸ hI⟩, hn', ho',
          hb', hz', hfr', hft', hc'⟩⟩
      hw11 h5L1W hdW hqW hpsiLimW hrep ⟨hCaps, hDeep, hIntCap⟩ hLoopInv hnum hoff hBd hCapFacts
      hcapEval hcapTree hlogW hlenNN hbelow hqBelow hquotas hquotasW hBr hqOut hdescBelow hdescOut0
      hdescOut1 hz hroom
  exact ⟨ret, c, out, tokEnd, hr, hlo, hhi, hdesc, hrep', hCapsEnd, hDeepEnd, hcap', hnum', hoff',
    hsome, hz', hfr', hft', hc'⟩

end MinCostFlow.MinRatio
