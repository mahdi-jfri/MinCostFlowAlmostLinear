module

public import MinCostFlow.Final.AssemblyDryRunSCCoreAdapters
import MinCostFlow.Final.AssemblyDryRunSCCoreSelectAcct
import MinCostFlow.Final.AssemblyDryRunSCCoreSelectFits
import MinCostFlow.Final.AssemblyDryRunSCDeepSelectFits
import MinCostFlow.Final.AssemblyDryRunSCDeepUpdate
import MinCostFlow.Final.WireSelectDryFits
import MinCostFlow.MinRatio.SelectRebuildNoRoom
import MinCostFlow.MinRatio.SelectUpdateLevelNoRoom
import MinCostFlow.MinRatio.WireSelectEvalKeyBridge
import MinCostFlow.MinRatio.SelectPhiFill
import MinCostFlow.MinRatio.SelectMetaTableWrite
import MinCostFlow.MinRatio.SelectCoreLenFill
import MinCostFlow.MinRatio.SelectCoreList
import MinCostFlow.MinRatio.SelectEmbCopy
import MinCostFlow.MinRatio.SelectUpdateG0One
import MinCostFlow.MinRatio.SelectGraphRefill
import MinCostFlow.MinRatio.SelectNonRebuiltOps
import MinCostFlow.MinRatio.SelectUpdateNonRebuilt
import MinCostFlow.MinRatio.SelectRegionSkeleton
import MinCostFlow.DynSpanner.Program.DynGraphRefill
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import Mathlib.Tactic

/-!
# Select-aware `Update` wrapper proof (`AssemblyDryRunSCCoreSelectProof`)

Proves the unconditional two-size select-aware `Update` wrapper `dryCoreSel_hWrap` for
`dryCoreSelectCode innerCoreCode` (`Final/AssemblyDryRunSCCoreSelectCode.lean`) inside
`dryLinkedProgramSel` with `dryCoreSelectSizes Psc innerSz` (`Final/WireCoreSelectSizes.lean`),
together with the end-to-end corollary `dryCoreSel_hCoreSel_of_ext` combining `dryCoreSel_hWrap`
with Adapters 1–4 (`Final/AssemblyDryRunSCCoreAdapters.lean`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Opaque-program core of the select-aware `Update` wrapper (`hWrap`) -/

set_option maxHeartbeats 1200000 in
private theorem dryCoreSelectCode_hWrap_body
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e)
    {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    ∀ (limbMul intCapMax forestEdgeCap : ℕ) (PscP : SparseCoreOrdParams)
      (allocation : ℕ → List ℕ → ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
      (p : Program) (b c coreEntry bBatch bHeap bPhi bEval : ℕ) (op : ℕ → ℕ)
      (innerSpace innerFixed coreSpace coreFixed : ℕ → ℕ)
      (innerToolMul innerTreeMul toolMul treeMul K : ℕ) (innerBody : Stmt),
      Rcore.Local →
      10 ≤ w → 16 < 2 ^ w → 0 < F.limbs → F.limbs < 2 ^ w →
      dryLastStretchP J ≤ 40 * F.rangeExponent →
      dryLastStretchP J < 2 ^ w →
      cfg.P.k < 2 ^ w →
      0 < initTargetCap cfg G →
      initTargetCap cfg G ≤ selectHeapCap cfg G I.m →
      p.procs[b]? = some (ordChainUpdateCoreSelBody coreEntry c) →
      p.procs[coreEntry]? = some innerBody →
      p.procs[c]? = some (selectUpdatePostCoreBody (c + 1) (c + 3) (c + 7) (c + 13) (c + 16) (c + 22)) →
      p.procs[c + 3]? = some (selUpdateG0Body (c + 4) (c + 6)) →
      p.procs[c + 7]? = some (selectUpdateFPhiLenLoopBody (c + 7) (c + 8)) →
      p.procs[c + 8]? = some (selectUpdateFPhiLenLevelBody (bBatch + dgIdxApplyBatch) (c + 9)
        (c + 10) (c + 6) (c + 11)) →
      p.procs[c + 11]? = some (selCoreLenFillBody (c + 12)) →
      p.procs[c + 13]? = some (selectUpdateEmbLoopBody (c + 13) (c + 14)) →
      p.procs[c + 14]? = some (selectUpdateEmbLevelBody (op 4) (c + 15)) →
      p.procs[c + 15]? = some (selEmbUpdateFromListBody (c + 6) (c + 20) (c + 21)) →
      p.procs[c + 16]? = some (selectUpdateSuffixBlocksBody (c + 17) (op 3) (c + 19) (c + 30)) →
      p.procs[c + 17]? = some (selectInitInteriorLoopBody (c + 17) (c + 18)) →
      p.procs[c + 18]? = some (selectFillInteriorLevelBody (op 2) (op 4) (c + 29)
        (c + 11) (c + 20) (c + 21)) →
      p.procs[c + 19]? = some (selectFillLastLevelBody (c + 29) (c + 11)) →
      p.procs[c + 21]? = some (selEmbCopyBody (bHeap + 12)) →
      p.procs[c + 22]? = some (selectUpdateHeapPhaseBody (c + 23) (c + 25)) →
      p.procs[c + 23]? = some (selectUpdateHeapPrefixLoopBody (c + 23) (c + 24)) →
      p.procs[c + 24]? = some (selectUpdateLevelBody (c + 27)) →
      p.procs[c + 25]? = some (selectRebuildSuffixBody (c + 25) (c + 26)) →
      p.procs[c + 26]? = some (selectRebuildLevelBody (bHeap + 21) (c + 27)) →
      p.procs[c + 27]? = some (selectProcessListBody (c + 27) (c + 28)) →
      p.procs[c + 28]? = some (selectProcessEdgeBody bEval (bHeap + 18) (bHeap + 20)) →
      p.procs[c + 30]? = some (selectPhiLoopBody (c + 30) (bPhi + 16)) →
      p.HasAt bHeap (selectHeapOpsModule bHeap 4) →
      p.HasAt bPhi (selectPhiFillModule bPhi 4) →
      p.HasAt bEval (evalKeyModule bEval 4) →
      (∀ B metaBase lvlMeta,
        MeetsContract w p (c + 1) (selTableWriteContract w B metaBase lvlMeta (dryLastStretchP J))) →
      (∀ val : ℤ, MeetsContract w p (c + 4) (selCopyG0OneContract w (initTargetCap cfg G) val)) →
      (∀ L' : List ℕ, MeetsContract w p (c + 6) (selFilterPresentContract w L')) →
      (∀ (G0 F0 : MGraph) (U0 : List Update) (uW : ℕ),
        MeetsContract w p (bBatch + dgIdxApplyBatch)
          (dgApplyBatchContract w G.n (initTargetCap cfg G) G0 F0 U0 uW)) →
      (∀ (F0 : MGraph) (fDel : List ℕ),
        MeetsContract w p (c + 9) (dgDeleteEdgeListContract w G.n (initTargetCap cfg G) F0 fDel)) →
      (∀ (G0 : MGraph) (U0 : List Update) (uW : ℕ) (φ0 : ℕ → ℝ),
        MeetsContract w p (c + 10) (selBatchCopySplitsContract w G.n F.fmt.precision G0 U0 uW φ0)) →
      MeetsContract w p (c + 12) (selCoreLenEdgeContract w F.fmt.precision) →
      (∀ eL : List ℕ,
        MeetsContract w p (c + 11) (selCoreLenFillContract w F.fmt.precision (initTargetCap cfg G) eL)) →
      (∀ vcF ecF (Fold Fnew : MGraph),
        MeetsContract w p (c + 29) (dgCopyRefillContract w G.n (initTargetCap cfg G) vcF ecF Fold Fnew)) →
      (∀ eL : List ℕ, MeetsContract w p (c + 20) (selFilterAbsentContract w eL)) →
      (∀ j < cfg.P.d, ∀ G' : MGraph, G'.n ≤ G'.m + 1 → G'.m ≤ I.m →
        SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G' cfg.P.k
          (levelM cfg.TP cfg.P j) cfg.N₀ G.n (initTargetCap cfg G)
          dryCapExp PscP allocation Rcore p op) →
      selectProcessEdgeCost (selectHeapCap cfg G I.m) F.limbs
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) + (18 * drySlot I.m + 160) + 80 ≤ K →
      (∀ u, innerSpace u +
        selectUpdatePostCoreSpaceBound cfg.P.d G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m)
          F.limbs dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs) (innerSpace u) = coreSpace u) →
      (∀ u, innerFixed u +
        selectUpdatePostCoreFixedBound PscP.readout cfg.P.d F.limbs dryCapExp
          (levelM cfg.TP cfg.P 0) cfg.N₀ (drySlot I.m) K 1 cfg.P.d
          (levelM cfg.TP cfg.P cfg.P.d) + 40 = coreFixed u) →
      innerToolMul +
        selectUpdatePostCoreToolMulBound cfg.P.d F.limbs dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
          (drySlot I.m) K 1 10 ≤ toolMul →
      innerTreeMul + selectUpdatePostCoreTreeMulBound (drySlot I.m) K ≤ treeMul →
      (∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
        (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
        (sg : SelectGhost) (U : List Update) (B R : ℤ),
        UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
          (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
          (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace
          root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
        (∀ u ∈ U, ∀ e, u.Inserts e →
          Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧ Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
        (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
        SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
        OrdChainCoreExtPost w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
          G.n (initTargetCap cfg G) cfg (dryReembFn J) Rcore p innerSpace innerFixed
          innerToolMul innerTreeMul B R innerBody root uIntBuf editsPtr editWords g l heap pos ω
          mem0 mem model tok U) →
      (∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
        (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
        (sg : SelectGhost) (U : List Update) (B R : ℤ),
        UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
          (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
          (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace
          root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
        (∀ u ∈ U, ∀ e, u.Inserts e →
          Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧ Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
        (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
        SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
        ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
          Runs w p ω innerBody (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
            (.returned nextHeap) out cost →
          tok'.table = tok.table →
          SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem) →
      OrdChainUpdateCoreSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2 K
        (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore p b
        coreSpace coreFixed toolMul treeMul := by
  intro I V k F cfg G limbMul intCapMax forestEdgeCap PscP allocation Rcore p b c coreEntry
    bBatch bHeap bPhi bEval op innerSpace innerFixed coreSpace coreFixed
    innerToolMul innerTreeMul toolMul treeMul K innerBody
    hlocalCore hw10 hw16 hLpos hLkW hpLastLe hpLastW hkW heCapPos heCapLeHeap
    hEntryAt hCoreAt hPostAt hG0At hFPLLoopAt hFPLLvlAt hCoreLenAt hEmbLoopAt hEmbLvlAt hEmbUpdAt
    hSufBlkAt hInitIntAt hFillIntAt hFillLastAt hEmbCopyAt hHeapPhaseAt hHeapPrefAt hUpdLvlAt
    hRebSufAt hRebLvlAt hProcListAt hProcEdgeAt hPhiLoopAt hHeapMod hPhiMod hEvalMod
    hTableWrite hCopyOne hFilterPres hDgBatch hDelList hSplits hCoreLenEdge hCoreLen
    hDgCopy hFilterAbs hFootAtAll hK hSpaceEq hFixEq hToolMulLe hTreeMulLe hCorePostAll hCoreDisjAll
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed (dryDepth J) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  refine ⟨ordChainUpdateCoreSelBody coreEntry c, hEntryAt, ?_⟩
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok sg U B R
  dsimp only
  intro hRep0 hMeta0 hCaps0 hSelInv0 hReembPot0 hRegInv0 hReach hGrid0 hStateFits hTreeN
    hNum0 hOffInv0 hOffBd0 hB0 hFitTree hExtGLRng hFlowRng hDetRng hICap hICapMax hForCap
    hLogW hShift0 hShift1 hCapFacts hBr hGLRng hAgree hTags0 hFreshTab hnfCap hBatchInt
    hSmallInt hOrdEdits hEdWordsW hEdEnd hRef hFootLt hgEnd hlEnd hVecOff huLeEd hzHeap hRoom
    hglValid0 hRebW0 hLay0
  let Rrep := solverStateRep cfg F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
    (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) Rcore
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 F.limbs F.fmt.precision I.m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 F.limbs F.fmt.precision I.m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  have hPrem : UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace
      root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R :=
    ⟨hRep0, hMeta0, hCaps0, hSelInv0, hReembPot0, hRegInv0, hReach, hGrid0, hStateFits, hTreeN,
      hNum0, hOffInv0, hOffBd0, hB0, hFitTree, hExtGLRng, hFlowRng, hDetRng, hICap, hICapMax,
      hForCap, hLogW, hShift0, hShift1, hCapFacts, hBr, hGLRng, hAgree, hTags0, hFreshTab, hnfCap,
      hBatchInt, hSmallInt, hOrdEdits, hEdWordsW, hEdEnd, hRef, hFootLt, hgEnd, hlEnd, hVecOff,
      huLeEd, hzHeap, hRoom⟩
  have hCorePost := hCorePostAll root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok
    sg U B R hPrem hglValid0 hRebW0 hLay0
  obtain ⟨⟨Bblk, hBslot, hBlkInv0⟩, hPhiBd0, hg0⟩ := hRegInv0
  have hcapEq : sg.loc.cap = selectHeapCap cfg G I.m := hBlkInv0.2.2.2.2.1
  have hOwnEq : sg.owned = fun a => sg.loc.hb ≤ a ∧ a < Bblk.endAddr := hBlkInv0.2.2.2.2.2.2.1
  have hBreg : SelectRegion sg.loc.hb sg.loc Bblk sg.loc.metaPtr := hBlkInv0.2.2.2.2.2.1
  have hsbLtEnd : sg.loc.hb < Bblk.endAddr := by
    obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hBreg.bounds
    have h2 : sg.loc.hb < sg.loc.endAddr := by
      rw [sg.loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    omega
  have hEndLtU : Bblk.endAddr ≤ uIntBuf := by
    have hlt := hFootLt (Bblk.endAddr - 1) (Or.inr (by rw [hOwnEq]; omega))
    omega
  have hHeapW : heap < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hRoom
  have hSlotW : drySlot I.m < 2 ^ w := by
    rw [← hBslot]
    have hBe : Bblk.eCap = initTargetCap cfg G := hBlkInv0.2.2.1
    have h1 : Bblk.slot ≤ Bblk.eCap * Bblk.slot := Nat.le_mul_of_pos_left _ (by rw [hBe]; exact heCapPos)
    have h2 : Bblk.eCap * Bblk.slot ≤ Bblk.levelSize := by unfold SelectBlocksLoc.levelSize; omega
    have h3 : Bblk.levelSize ≤ (Bblk.d + 1) * Bblk.levelSize := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h4 : Bblk.endAddr = Bblk.base + selectBlocksSize Bblk.d Bblk.vCap Bblk.eCap Bblk.Lk Bblk.slot :=
      Bblk.endAddr_eq
    unfold selectBlocksSize at h4
    have h5 : (Bblk.d + 1) * Bblk.levelSize = (Bblk.d + 1) *
        (dynGraphSize Bblk.vCap Bblk.eCap + Bblk.vCap * Bblk.Lk + Bblk.eCap * Bblk.Lk + Bblk.eCap +
          Bblk.eCap * Bblk.slot) := rfl
    omega
  -- Reached-state model facts & post-update `DryChainLenGridInv`
  have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh :=
    hRep0.2.2.2.2.1
  obtain ⟨hExtG, hgOld, hℓOld⟩ := dryReached_extG_g_ℓ J hJn hJm hCap1 hReach
  have hLenWithin : IPM.LengthsWithin G F.rangeExponent lVec :=
    fun e he => (hGLRng e (hExtG.symm ▸ he)).2
  have hDyadic : IsDyadicGrid G F.fmt.precision lVec := by
    intro e he
    have heExt : e ∈ model.extG.E := hExtG.symm ▸ he
    by_cases hIns : ∃ u ∈ U, u.Inserts e
    · have hlEq : lVec e = readVector mem0 l 4 F.limbs F.fmt.precision I.m e := by
        dsimp only [lVec, updateOverlay]; rw [ite_eq_right (fun h => h.2 hIns)]
      have heM : e < I.m := hRep0.2.2.2.2.2.2.1 e heExt
      refine ⟨Num.intVal mem0 (l + e * F.limbs) 4 F.limbs, ?_⟩
      rw [hlEq]; simp [readVector, heM, Num.fixVal]
    · push Not at hIns
      have hlEq : lVec e = model.extℓ e := (hAgree e heExt hIns).2
      have hL := hFresh.hLeft e heExt
      have hMem0 : model.extToInt e ∈ (model.chain.G 0).E :=
        hFresh.hE ▸ Finset.mem_image_of_mem model.extToInt heExt
      have hℓ0 : model.chain.ℓ (model.extToInt e) = model.extℓ e := by
        rw [hℓOld (model.extToInt e) hMem0, hL]
      obtain ⟨q, hq⟩ := (hGrid0.2.2.1 0 (Nat.zero_le _)).2 (model.extToInt e) hMem0
      exact ⟨q, hq.trans (hℓ0.trans hlEq.symm)⟩
  have hGrid1 : DryChainLenGridInv J modelPre.chain :=
    (dryChainLenGridInv_preLoop_of_reached J hJn hJm hCap1 hReach hGrid0
      (hExtG ▸ hRef) hLenWithin hDyadic (fun e he => hAgree e (hExtG.symm ▸ he))).1
  -- Post-update `SelectModelInv` and gradient bounds/fits
  have hInv1 := hShift1.1
  have hTH1 := hInv1.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP hVcfg.hMWU
    hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk
  have hLvlM1 : ∀ j, modelPre.chain.lvlM j = levelM cfg.TP cfg.P j := fun j => congrFun hInv1.hLvlM j
  have hN01 : modelPre.chain.N₀ = cfg.N₀ := hInv1.hN0
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hPreExtG : modelPre.extG = model.extG := hTr.1.trans hRef.2.1
  obtain ⟨_, _, _, _, _, hModOld'⟩ := hBlkInv0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hModNewEx : ∃ σ' σ'_mwu γ'_ℓ γ'_c,
      SelectModelInv modelPre (modelPre.chain.G 0) σ' σ'_mwu γ'_ℓ γ'_c :=
    ⟨_, _, _, _, hTH1.1, hTH1.2.1, hInv1.hBran,
      fun j hj => by
        rw [hLvlM1 j, hN01]
        exact levelHistory_sparseCoreOrdInput (Classical.choice (hInv1.hHist j hj)),
      fun e he => lt_of_lt_of_le (by positivity) (hGLRng e (hPreExtG ▸ he)).2.1,
      fun v hv => by rw [hPreExtG] at hv ⊢; exact hModOld'.2.2.2.2.2 v hv⟩
  obtain ⟨σ', σ'_mwu, γ'_ℓ, γ'_c, hModNew⟩ := hModNewEx
  have hgBoundNew : ∀ e ∈ (modelPre.chain.G 0).E, |modelPre.chain.g e| ≤ (2 : ℝ) ^ F.rangeExponent :=
    update_g_bound_at_modelPre hFresh hRef (fun e he => (hGLRng e he).1)
  have hgEqNew : ∀ e ∈ (modelPre.chain.G 0).E, modelPre.chain.g e = modelPre.extg (modelPre.intToExt e) :=
    update_g_eq_extg_modelPre
  have hPE4L : F.fmt.precision + F.rangeExponent + 2 ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
      ipmQualityRangeExponent, ipmQualityErrorBits]; omega
  have hgFitNew : ∀ e ∈ (modelPre.chain.G 0).E, ∀ z : ℤ,
      (z : ℝ) / (2 : ℝ) ^ F.fmt.precision = modelPre.chain.g e →
      Num.Fits 4 F.limbs z ∧ Num.Fits 4 F.limbs (-z) := fun e he z hz =>
    update_g_fits_modelPre hPE4L (hgBoundNew e he) z hz
  have hG0n1 : (modelPre.chain.G 0).n ≤ 2 * I.m + 2 := hGrid1.2.1
  have hℓPos1 : ∀ e ∈ (modelPre.chain.G 0).E, 0 < modelPre.chain.ℓ e := fun e he => by
    have hlt := (hGrid1.2.2.1 0 (Nat.zero_le _)).1 e he
    have h0 : modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ 0 e = modelPre.chain.ℓ e := rfl
    rw [h0] at hlt; exact lt_of_lt_of_le (by positivity) hlt.1
  -- Vertex and edge capacity bounds across all levels `j ≤ cfg.P.d`
  have hdPos : 0 < cfg.P.d := cfg.P.hd
  have hG0VEq : (modelPre.chain.G 0).V = (model.chain.G 0).V := by
    have hEdgeU : ∀ u ∈ (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2,
        IsEdgeUpdate u := translateBatch_isEdgeUpdate _ _ _ _ _ fun u hu => by
      have hns := hRef.2.2 u hu
      cases u with | insert _ _ _ => trivial | delete _ => trivial | split _ _ _ _ => exact absurd hns id
    have hAppV : ∀ {UL : List Update} {H : MGraph}, (∀ u ∈ UL, IsEdgeUpdate u) → (H.applyBatch UL).V = H.V := by
      intro UL; induction UL with
      | nil => intro _ _; rfl
      | cons u rest ih =>
        intro H hE
        have h1 : (H.applyUpdate u).V = H.V := by
          have hu := hE u List.mem_cons_self
          cases u <;> simp [IsEdgeUpdate, MGraph.applyUpdate] at hu ⊢
        exact (ih (fun x hx => hE x (List.mem_cons_of_mem _ hx))).trans h1
    rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
        (fun e' => gVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e'))
        (fun e' => lVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e')) with
      ⟨_, hG0', _⟩ | ⟨_, hG0', _⟩
    · have h1 : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch _).compact := hG0'
      rw [h1]; exact hAppV hEdgeU
    · have h1 : modelPre.chain.G 0 = (model.chain.G 0).applyBatch _ := hG0'
      rw [h1]; exact hAppV hEdgeU
  have hG0ELtCap : ∀ e ∈ (modelPre.chain.G 0).E, e < initTargetCap cfg G := by
    intro e he
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
        (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
      ⟨_, hG0', _⟩ | ⟨_, hG0', _⟩
    · have h1 : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := hG0'
      rw [h1] at he
      have hlt : e < ((model.chain.G 0).applyBatch tr.2.2.2.2).E.card := by simpa [MGraph.compact] using he
      have hcard : ((model.chain.G 0).applyBatch tr.2.2.2.2).E.card ≤ tr.2.2.2.1 :=
        (Finset.card_le_card fun x hx => Finset.mem_range.mpr (hTr.2.1.hLtFresh x hx)).trans (by simp [tr])
      have hnf' : tr.2.2.2.1 ≤ initTargetCap cfg G := hICap ▸ hnfCap
      omega
    · have h1 : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0'
      rw [h1] at he
      exact lt_of_lt_of_le (hTr.2.1.hLtFresh e he) (hICap ▸ hnfCap)
  have hOldEcapAll : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.G j).E, e < initTargetCap cfg G :=
    fun j hj e he => (hCaps0 0 hdPos).2.2.1 e (chainInv_G_E_subset_G0 hVcfg hShift0.1 j hj he)
  have hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (modelPre.chain.G j).V, v < G.n := fun j hj v hv => by
    have hB1 := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hVcfg.hTP hVcfg.hγM₀ hVcfg.hγk hInv1 j hj
    exact (hCaps0 0 hdPos).2.1 v (hG0VEq ▸ hB1.2.1 hv)
  have hEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E, e < initTargetCap cfg G :=
    fun j hj e he => hG0ELtCap e (chainInv_G_E_subset_G0 hVcfg hInv1 j hj he)
  have hOldEcap : ∀ j ≤ cfg.P.d, (model.chain.G j).m ≤ initTargetCap cfg G := fun j hj =>
    (Finset.card_le_card fun e he => Finset.mem_range.mpr (hOldEcapAll j hj e he)).trans (by simp)
  have hNewVcap : ∀ j ≤ cfg.P.d, (modelPre.chain.G j).n ≤ G.n := fun j hj =>
    (Finset.card_le_card fun v hv => Finset.mem_range.mpr (hVcap j hj v hv)).trans (by simp)
  have hNewEcap : ∀ j ≤ cfg.P.d, (modelPre.chain.G j).m ≤ initTargetCap cfg G := fun j hj =>
    (Finset.card_le_card fun e he => Finset.mem_range.mpr (hEcap j hj e he)).trans (by simp)
  have hLwMaxW : ordLevelLwMax F.limbs dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀ < 2 ^ w := by
    have h1 := lwMax_le_postCoreSpace (d := cfg.P.d) (vCap := G.n) (cap := selectHeapCap cfg G I.m)
      (L := F.limbs) (capExp := dryCapExp) (M₀ := levelM cfg.TP cfg.P 0) (N₀ := cfg.N₀)
      (evalSpace := evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (coreSp := innerSpace U.length) heCapPos
    have h2 := hSpaceEq U.length
    omega
  -- Per-level readout foot, embedding, and state-dependent select helper contracts
  have hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T (modelPre.chain.G j) cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ G.n (initTargetCap cfg G) dryCapExp PscP
        allocation Rcore p op := by
    intro j hj
    have hGn : (modelPre.chain.G j).n ≤ (modelPre.chain.G j).m + 1 := hShift1.levels_n_le hVcfg j hj.le
    have hGm : (modelPre.chain.G j).m ≤ I.m :=
      (Finset.card_le_card (chainInv_G_E_subset_G0 hVcfg hInv1 j hj.le)).trans hGrid1.1
    rw [hLvlM1 j, hN01]
    exact hFootAtAll j hj (modelPre.chain.G j) hGn hGm
  have hEmbBd : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
      (modelPre.chain.toTreeChain.activeEmb j e).length ≤ dryMaxEmbLen I.m := fun j hj e he =>
    (progTool_embLen_le_dryMaxEmbLen_of_shiftLoop J hJn hJm hCap1 hShift1 j hj e he).1
  have hEmbSlot : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
      (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ drySlot I.m := fun j hj e he => by
    rw [mWalkEncode_length]; unfold drySlot; have := hEmbBd j hj e he; omega
  have hHeapC := selectHeapOpsModule_meetsContracts (w := w) (h := 4) (by decide) hw10 hHeapMod sg.loc
  have hEmbCopy : ∀ j < cfg.P.d, ∀ eL : List ℕ,
      MeetsContract w p (c + 21) (selEmbCopyContract w eL (modelPre.chain.toTreeChain.activeEmb j)) :=
    fun _ _ _ => selEmbCopy_meetsContract hEmbCopyAt hHeapC.2.1
  have hEmbUpd : ∀ j < cfg.P.d, ∀ L' : List ℕ,
      MeetsContract w p (c + 15) (selEmbUpdateFromListContract w G.n (initTargetCap cfg G)
        (modelPre.chain.G j) (modelPre.chain.toTreeChain.activeLSF j).F.F L'
        (modelPre.chain.toTreeChain.activeEmb j)) :=
    fun j hj L' => selEmbUpdateFromList_meetsContract hEmbUpdAt (hFilterPres L') hFilterAbs (hEmbCopy j hj)
  have hPhiFill : ∀ (Bblk' : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p (bPhi + 16) (selectPhiFillContract w 4 F.fmt.precision
        (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J))
        modelPre.chain.toTreeChain (modelPre.chain.G 0) modelPre.chain.g modelPre.chain.ℓ
        σ' σ'_mwu γ'_ℓ γ'_c φ) :=
    fun _ _ _ _ => selectPhiFillModule_meetsContract (w := w) (h := 4) (by decide) hw10 hPhiMod
  have hCandFit : CandidateKeysFit 4 F.fmt.precision (dryLastStretchP J) F.limbs
      modelPre.chain.toTreeChain modelPre.chain.g modelPre.chain.ℓ :=
    dry_candidateKeysFit_of_shiftLoop J hJn hJm hCap1 hShift1 hGrid1 hpLastLe
      (M_g := (2 : ℝ) ^ F.rangeExponent) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show F.rangeExponent ≤ 40 * F.rangeExponent by omega)) hgBoundNew
  have hProcEdge : ∀ (Bblk' : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      Bblk'.Lk = F.limbs →
      MeetsContract w p (c + 28) (selectProcessEdgeContract w 4 F.fmt.precision sg.loc
        (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J))
        modelPre.chain.toTreeChain modelPre.chain.g modelPre.chain.ℓ φ
        (fun j => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1))
        (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)) := by
    intro Bblk' metaBase solverG φ hMLk
    have h1 := selectProcessEdge_meetsContract_evalKey
      (loc := sg.loc) (mloc := selectMlocOf Bblk' metaBase solverG (dryLastStretchP J))
      (C := modelPre.chain.toTreeChain) (G := modelPre.chain.G 0) (g := modelPre.chain.g)
      (ℓ := modelPre.chain.ℓ) (φ := φ)
      (coreLen := fun j => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1))
      (maxEmbLen := dryMaxEmbLen I.m)
      hProcEdgeAt hEvalMod (by decide) hw10 hModNew.1 hModNew.2.1 hℓPos1
      (fun lvl hlvl e he => hEmbBd lvl hlvl e (Finset.mem_sdiff.mp he).1)
      (by rw [show (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J)).Lk = F.limbs from hMLk]; exact hCandFit)
      hHeapC.2.2.2.2.2.2.2.1 hHeapC.2.2.2.2.2.2.2.2.2.1
    rw [show (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J)).Lk = F.limbs from hMLk] at h1
    exact h1
  have hUpdLvl : ∀ (Bblk' : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ)
      (DL : LevelDiffLists),
      Bblk'.Lk = F.limbs →
      MeetsContract w p (c + 24) (selectUpdateLevelNoRoomContract w 4 F.fmt.precision sg.loc
        (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J))
        modelPre.chain.toTreeChain modelPre.chain.g modelPre.chain.ℓ φ
        (fun j => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1))
        DL (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)) :=
    fun Bblk' metaBase solverG φ _ hMLk =>
      selectUpdateLevel_meetsContract_noRoom hUpdLvlAt fun _ =>
        selectProcessList_meetsContract_noRoom hProcListAt (hProcEdge Bblk' metaBase solverG φ hMLk)
  have hRebSuf : ∀ (Bblk' : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      Bblk'.Lk = F.limbs →
      MeetsContract w p (c + 25) (selectRebuildSuffixNoRoomContract w 4 F.fmt.precision sg.loc
        (selectMlocOf Bblk' metaBase solverG (dryLastStretchP J))
        modelPre.chain.toTreeChain (modelPre.chain.G 0) modelPre.chain.g modelPre.chain.ℓ
        σ' σ'_mwu γ'_ℓ γ'_c φ
        (fun j => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1))
        (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)) :=
    fun Bblk' metaBase solverG φ hMLk =>
      selectRebuildSuffix_meetsContract_noRoom hRebSufAt
        (selectRebuildLevel_meetsContract_noRoom hRebLvlAt hHeapC.2.2.2.2.2.2.2.2.2.2
          fun _ => selectProcessList_meetsContract_noRoom hProcListAt
            (hProcEdge Bblk' metaBase solverG φ hMLk))
  -- `PhiBd` step & fit invariants
  let PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop :=
    fun φ j => SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * I.m + 2) ((2 : ℝ) ^ F.rangeExponent) j
  have hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ r < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ r) →
      (∀ r < j, PhiBd φ r) →
      (∀ v ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
          (modelPre.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ j)
            ((modelPre.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ r < j + 1, PhiBd (Function.update φ j φj) r := by
    intro j hj φ φj hPot hBd hFill r hr
    by_cases hrj : r = j
    · subst hrj
      exact selectPhiBoundedAt_of_phiFill (by positivity) hModNew.1 hj hG0n1 hgBoundNew hPot hBd hFill
    · exact selectPhiBoundedAt_update_ne φj hrj (hBd r (by omega))
  have hFitPhi : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ r < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ' r) →
      (∀ r < j, PhiBd φ' r) →
      (∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 F.limbs F.fmt.precision modelPre.chain.toTreeChain modelPre.chain.g φ' j e) ∧
      ForestWalkFits 4 F.limbs F.fmt.precision (modelPre.chain.toTreeChain.activeLSF j).F.F
        (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ' j) :=
    fun j hj φ' _ hBd => dry_phiFillFits_of_shiftLoop J hJn hJm hCap1 hShift1 hG0n1 hj
      (M_g := (2 : ℝ) ^ F.rangeExponent) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show F.rangeExponent ≤ 80 * F.rangeExponent by omega))
      hgBoundNew hBd
  -- `hLinkFacts` callback via `dryCoreSel_hLinkFacts`
  have hV0Ne : (model.chain.G 0).V.Nonempty := by
    have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
    have h0 : 0 ∈ G.E := by simp [G, namedInstance, hImPos]
    have he : model.extToInt 0 ∈ (model.chain.G 0).E :=
      hFresh.hE ▸ Finset.mem_image_of_mem model.extToInt (hExtG.symm ▸ h0)
    have hVal0 := (hShift0.1.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP
      hVcfg.hMWU hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk).1.2.1
    exact ⟨(model.chain.G 0).tail (model.extToInt 0), (hVal0 (model.extToInt 0) he).1⟩
  have hPot0Sel : SelectPotInv model.chain.toTreeChain model.chain.g sg.φ :=
    (SelectRegionAt.of_solverSelectBlocksInv hBlkInv0).1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDepthPos : 1 ≤ dryDepth J := by
    unfold dryDepth Expander.chosenL
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (Real.log_pos (by
      have h2 : (1 : ℝ) < ((max (solverConnectedAugmented J).m
          (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) + 2 := by
        exact_mod_cast (show 1 < max (solverConnectedAugmented J).m
          (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 + 2 by omega)
      exact h2)) _)
  have hLinkFacts := fun (memCore : ℕ → ℕ) (midHeap firstReb : ℕ)
      (levelU levelUS : ℕ → List Update) (diffLists : ℕ → LevelDiffLists)
      (tok' : SolverToken cfg F.limbs Rcore)
      (hLink : UpdateCoreLevelLink model.chain modelPre.chain firstReb levelU levelUS)
      (hOut : UpdateCoreSelectOutAt w F.fmt.precision F.limbs dryCapExp G.n (initTargetCap cfg G)
        (dryReembFn J) (Rrep.foot root tok') memCore heap midHeap firstReb model.chain
        modelPre.chain levelU levelUS diffLists) =>
    dryCoreSel_hLinkFacts (pot := dryPot J) (reembFn := dryReembFn J)
      hT rfl rfl hVcfg hDepthPos dryImplHyp.2.2.2.1
      (fun b hb => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k b hb)
      hFresh hRef hV0Ne hgOld hℓOld hAgree hShift0 hShift1 hPot0Sel hPhiBd0
      hOldEcapAll hEcap hLink hOut
  -- Invoke `ordChainUpdateCoreSelBody_runs_of_corePost`
  have hRoom' : heap + (innerSpace U.length +
      selectUpdatePostCoreSpaceBound cfg.P.d G.n (initTargetCap cfg G) sg.loc.cap F.limbs dryCapExp
        (levelM cfg.TP cfg.P 0) cfg.N₀ (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
        (innerSpace U.length)) < 2 ^ w := by
    rw [hcapEq, hSpaceEq U.length]; exact hRoom
  have hBblkLk : Bblk.Lk = F.limbs := hBlkInv0.2.2.2.1
  obtain ⟨nextHeap, cost, out, tokFinal, sg', hrBody, hHeapLo, hHeapHi, hLevEq, hICapEq,
      hRECapEq, hTabEq, hRep', hMeta', hCaps', hLay', hSelInv', hPot', hReg', hTreeNum', hOffInv',
      hOffBd', hz', hFr', hFt', hCost'⟩ :=
    ordChainUpdateCoreSelBody_runs_of_corePost
      (w := w) (L := F.limbs) (P := F.fmt.precision) (E := F.rangeExponent) (m := I.m) (V := V)
      (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
      (drainUnit := detectOffTreeDrainUnit F.limbs) (capExp := dryCapExp)
      (vCap := G.n) (eCap := initTargetCap cfg G) (pLast := dryLastStretchP J)
      (slot := drySlot I.m) (K := K) (c := 1) (uWordsMul := 10)
      (evalSpace := evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (evalCost := evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (coreProc := coreEntry) (postCoreProc := c)
      (tableWriteProc := c + 1) (g0Proc := c + 3) (copyOne := c + 4) (filterPres := c + 6)
      (fPhiLenLoopProc := c + 7) (fPhiLenLvlProc := c + 8)
      (dgApplyBatch := bBatch + dgIdxApplyBatch) (delEdgeList := c + 9)
      (batchCopySplits := c + 10) (coreLenFill := c + 11) (coreLenEdge := c + 12)
      (embLoopProc := c + 13) (embLvlProc := c + 14) (embUpdateFromList := c + 15)
      (sufBlocksProc := c + 16) (initIntLoop := c + 17) (fillIntProc := c + 18)
      (dgCopyProc := c + 29) (filterAbs := c + 20) (embCopyProc := c + 21)
      (fillLast := c + 19) (phiLoop := c + 30) (phiFillProc := bPhi + 16)
      (heapPhaseProc := c + 22) (heapPrefLoop := c + 23) (updLvlProc := c + 24)
      (rebSufProc := c + 25)
      (innerSpace := innerSpace) (innerFixed := innerFixed) (uWordsFix := fun _ => cfg.P.d)
      (innerToolMul := innerToolMul) (innerTreeMul := innerTreeMul)
      (fmt := F.fmt) (cfg := cfg) (G := G) (G₀' := modelPre.chain.G 0)
      (σ' := σ') (σ'_mwu := σ'_mwu) (γ'_ℓ := γ'_ℓ) (γ'_c := γ'_c)
      (initialGraph := fun j => modelPre.chain.G j) (Psc := PscP) (allocation := allocation)
      (reembFn := dryReembFn J) (pot := dryPot J) (Rcore := Rcore) (p := p) (op := op)
      hVcfg.hTP hVcfg.hγk (dryPot_facts J) rfl rfl hlocalCore hw16 hw10 hLpos hLkW hpLastW hkW
      hSlotW hdPos heCapPos (hcapEq ▸ heCapLeHeap) (hcapEq ▸ hK)
      hCoreAt hCorePost
      (hCoreDisjAll root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok sg U B R hPrem
        hglValid0 hRebW0 hLay0)
      hPostAt hRep0 hReembPot0 ⟨⟨Bblk, hBslot, hBlkInv0⟩, hPhiBd0, hg0⟩
      hTags0 hFootLt (by omega)
      (dryCoreSel_updateCoreModelInvKFBL hVcfg hShift0 hShift1 hBr)
      hModNew hgBoundNew hgEqNew hgFitNew hVcap hEcap hOldEcap hNewVcap hNewEcap hLwMaxW
      (dryDeepSel_hLenFitInt J hJn hJm hCap1 hInv1 hGrid1)
      (dryCoreSel_hLenFitLast J hJn hJm hCap1 hShift1 hGrid1)
      hEmbSlot hPhiBdStep hFitPhi hLinkFacts
      (fun Bblk' metaBase => hTableWrite Bblk' metaBase (solverLevelMetaAddr tok.table cfg.P.d))
      hG0At hCopyOne hFilterPres hFPLLoopAt hFPLLvlAt hDgBatch hDelList hSplits hCoreLenAt
      hCoreLenEdge hCoreLen hEmbLoopAt hEmbLvlAt hEmbUpd hSufBlkAt hInitIntAt hFillIntAt
      hFillLastAt hPhiLoopAt hFootAt hDgCopy hFilterAbs hEmbCopy hPhiFill hHeapPhaseAt hHeapPrefAt
      (fun Bblk' metaBase solverG φ DL => by
        by_cases hlk : Bblk'.Lk = F.limbs
        · exact hUpdLvl Bblk' metaBase solverG φ DL hlk
        · refine meetsContract_of_runs hUpdLvlAt fun args mem' pos' ω' _ hpre => ?_
          obtain ⟨_, _, _, _, _, _, _, _, _, hLkEq, _⟩ := hpre
          exact absurd (hLkEq.trans (hBlkInv0.2.2.2.2.2.1.2.2.2.2.2.1.trans hBblkLk)) hlk)
      (fun Bblk' metaBase solverG φ => by
        by_cases hlk : Bblk'.Lk = F.limbs
        · exact hRebSuf Bblk' metaBase solverG φ hlk
        · refine meetsContract_of_runs hRebSufAt fun args mem' pos' ω' _ hpre => ?_
          obtain ⟨_, _, _, _, _, _, _, _, hLkEq, _⟩ := hpre
          exact absurd (hLkEq.trans (hBlkInv0.2.2.2.2.2.1.2.2.2.2.2.1.trans hBblkLk)) hlk)
      hRoom'
  refine ⟨nextHeap, cost, out, tokFinal, sg', hrBody, hHeapLo, ?_, hLevEq, hICapEq, hRECapEq,
    hTabEq, hRep', hMeta', hCaps', hLay', hSelInv', hPot', hReg', hTreeNum', hOffInv', hOffBd', hz',
    hFr', hFt', ?_⟩
  · rw [hcapEq, hSpaceEq U.length] at hHeapHi; exact hHeapHi
  · rw [hFixEq U.length] at hCost'
    have hM1 := Nat.mul_le_mul_right (modelPre.chain.totalRuntime - model.chain.totalRuntime) hToolMulLe
    have hM2 := Nat.mul_le_mul_right (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) hTreeMulLe
    exact hCost'.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add_left hM1 _) hM2) _) _)

/-! ## 2. Public unconditional `dryCoreSel_hWrap` and conditional `dryCoreSel_hCoreSel_of_ext` -/

/-- **Unconditional select-aware `Update` wrapper theorem (`dryCoreSel_hWrap`):**
for any inner chain-core sub-code `innerCoreCode` and size bundle `innerSz` (`hInnerSz`), inside
`dryLinkedProgramSel` with `openSz := (dryCoreSelectSizes Psc innerSz).toDryOpenSizes`, if the
inner core at `lay.ordChainCore + 1 + innerCoreCode.off` satisfies `OrdChainCoreExtPost` under
`UpdateCoreSelPremAt` (at `innerSz`), then `dryCoreSelectCode innerCoreCode` at
`lay.ordChainCore` satisfies `OrdChainUpdateCoreSpecWKFBLSel` with `s.coreSpace`,
`s.coreFixed`, `s.toolMul`, `s.treeMul`. -/
theorem dryCoreSel_hWrap (Psc : DrySparseCorePieces)
    (initCode innerCoreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (innerSz : DryCoreOpenSizes) (hInnerSz : DryCoreOpenSizeBounds innerSz)
    (initSel : DryInitSelectSizes) (hInitSelSz : DryInitSelectSizeBounds initSel)
    (shiftSel : DryShiftSelectSizes) (hShiftSel : DryShiftSelectSizeBounds shiftSel) :
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    let hSel := mkDrySelectRebuildSizeBounds hInitSelSz hShiftSel
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode) selectCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      ∀ (innerBody : Stmt),
        p.procs[lay.ordChainCore + 1 + innerCoreCode.off]? = some innerBody →
        (∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
            (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
            G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J) (drySlot I.m)
            cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
              Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          OrdChainCoreExtPost w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
            G.n (initTargetCap cfg G) cfg (dryReembFn J) Rcore p
            (innerSz.coreSpace source J) (innerSz.coreFixed source J)
            (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J)
            B R innerBody root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U) →
        (∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
            (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
            G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J) (drySlot I.m)
            cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
              Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
            Runs w p ω innerBody (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
              (.returned nextHeap) out cost →
            tok'.table = tok.table →
            SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem) →
        OrdChainUpdateCoreSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
          (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
          G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m)
          cfg G (dryPot J) (DryChainLenGridInv J) Rcore p lay.ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul := by
  intro coreSz hCoreSz openSz hOpen selSz hSel inner source J hJn hJm _hCost hCap hw
    I V k F cfg G limbMul Rcore s p lay w innerBody hInnerAt hCorePostAll hCoreDisjAll
  let W := dryWitnessUsed
  let coeff := dryAllocCoeffConcrete Psc openSz hOpen selSz hSel
  let deg := dryAllocDegConcrete Psc openSz hOpen selSz hSel
  let PscP := drySCParams Psc dryCapExp limbMul
  let b := lay.ordChainCore
  let c := b + 1 + innerCoreCode.len
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw10 : 10 ≤ w := by omega
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
      ipmQualityRangeExponent, ipmQualityErrorBits]; omega
  have hL4W : 4 * F.limbs + 2 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    omega
  have hLkW : F.limbs < 2 ^ w := by omega
  have hpLastLe : dryLastStretchP J ≤ 40 * F.rangeExponent := by
    have h1 := dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap1
    have hmono : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
    dsimp only [dryLastStretchP, F, ipmQualityMinRatioFormat, I, V, k, cfg] at h1 hmono ⊢
    omega
  have hpLastW : dryLastStretchP J < 2 ^ w := by
    have hE4L : 40 * F.rangeExponent ≤ 4 * F.limbs := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
        ipmQualityErrorBits]; omega
    omega
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly W) ≤ coeff :=
    (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hQuotaBoundW, _⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W)
      coeff deg hWordCoeff source J hJn hJm hCap1 hw
  have hkW : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have heCapPos : 0 < initTargetCap cfg G := by
    have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
    have hGm : G.m = I.m := namedInstance_m I
    unfold initTargetCap; omega
  have heCapLeHeap : initTargetCap cfg G ≤ selectHeapCap cfg G I.m := by
    have hGm : G.m = I.m := namedInstance_m I
    unfold initTargetCap selectHeapCap; rw [hGm]; omega
  obtain ⟨hEntryAt, _, hPostAt, hTabWAt, hTabRowAt, hG0At, hCopyOneAt, hNegCopyAt, hFilterPresAt,
      hFPLLoopAt, hFPLLvlAt, hDelListAt, hSplitsAt, hCoreLenAt, hCoreEdgeAt, hEmbLoopAt, hEmbLvlAt,
      hEmbUpdAt, hSufBlkAt, hInitIntAt, hFillIntAt, hFillLastAt, hFilterAbsAt, hEmbCopyAt,
      hHeapPhaseAt, hHeapPrefAt, hUpdLvlAt, hRebSufAt, hRebLvlAt, hProcListAt, hProcEdgeAt,
      hDgCopyAt, hPhiLoopAt, hWireEdgeAt, hDgRefMod, hSplitMod, hBatchMod, hHeapMod, hPhiMod,
      hEvalMod⟩ :=
    dryCoreSelectCode_hasAll Psc initCode innerCoreCode selectCode termCode deepCode selInitCode
  obtain ⟨hDgOpsMod, hDgEdgeMod⟩ := dgRefillModule_hasOpsEdge hDgRefMod
  have hOpsAt := dryLinkedProgramSel_ops_hasAt W Psc.sc inner selInitCode
  have hInitH := solverOpsProcs_initHelpers hw14 hOpsAt
  have hCopyLimbs : MeetsContract w p (c + 50 + 12) (copyLimbsToContract w) :=
    (selectHeapOpsModule_meetsContracts (w := w) (h := 4) (by decide) hw10 hHeapMod
      ⟨0, 0, 0, 0, 0, 0⟩).2.1
  have hCoreLenEdgeC : MeetsContract w p (c + 12) (selCoreLenEdgeContract w F.fmt.precision) :=
    selCoreLenEdge_meetsContract hCoreEdgeAt hInitH.2.2.2.2.2.1 hWireEdgeAt
      hInitH.2.2.2.2.1 hInitH.2.2.1 hInitH.2.2.2.2.2.2.1 hInitH.1
  exact dryCoreSelectCode_hWrap_body J hJn hJm hCap1 hw
    limbMul (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) PscP
    (drySCAlloc Psc dryCapExp limbMul J) Rcore p b c (b + 1 + innerCoreCode.off)
    (c + 47) (c + 50) (c + 72) (c + 89) lay.scOp
    (innerSz.coreSpace source J) (innerSz.coreFixed source J) s.coreSpace s.coreFixed
    (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) s.toolMul s.treeMul
    (selSz.keyCost source J) innerBody
    (drySCRep_local Psc coeff deg source J hw)
    hw10 hw16 hLpos hLkW hpLastLe hpLastW hkW heCapPos heCapLeHeap
    hEntryAt hInnerAt hPostAt hG0At hFPLLoopAt hFPLLvlAt hCoreLenAt hEmbLoopAt hEmbLvlAt hEmbUpdAt
    hSufBlkAt hInitIntAt hFillIntAt hFillLastAt hEmbCopyAt hHeapPhaseAt hHeapPrefAt hUpdLvlAt
    hRebSufAt hRebLvlAt hProcListAt hProcEdgeAt hPhiLoopAt hHeapMod hPhiMod hEvalMod
    (fun _ _ _ => selTableWrite_meetsContract hTabWAt (selTableRow_meetsContract hTabRowAt))
    (fun _ => selCopyG0One_meetsContract hCopyOneAt hCopyLimbs fun _ => selNegCopyTo_meetsContract hNegCopyAt)
    (fun _ => selFilterPresent_meetsContract hFilterPresAt)
    (fun _ _ _ _ => dgApplyBatch_meetsContract hBatchMod hDgEdgeMod hSplitMod hDgOpsMod)
    (fun _ _ => dgDeleteEdgeList_meetsContract hDelListAt fun _ => dgDeleteEdge_meetsContract hDgEdgeMod hDgOpsMod)
    (fun _ _ _ _ => selBatchCopySplits_meetsContract hSplitsAt hCopyLimbs)
    hCoreLenEdgeC
    (fun _ => selCoreLenFill_meetsContract hCoreLenAt hCoreLenEdgeC)
    (fun _ _ _ _ => dgCopyRefill_meetsContract hDgCopyAt fun _ _ => dgRefillModule_meetsContract hDgRefMod)
    (fun _ => selFilterAbsent_meetsContract hFilterAbsAt)
    (fun j hj G' hGn hGm =>
      (drySC_coreKFBL_sel Psc inner selInitCode coeff deg source J hJn hJm hCap1 hw j hj G' hGn hGm).2)
    (dryKeyCost_covers source J).2.2.2
    (fun _ => rfl) (fun _ => rfl)
    (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    hCorePostAll hCoreDisjAll

end MinCostFlow.Final.DryRun

end
