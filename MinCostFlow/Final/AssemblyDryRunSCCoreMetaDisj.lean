module

public import MinCostFlow.Final.AssemblyDryRunSCInnerEnv
public import MinCostFlow.Final.AssemblyDryRunSCInnerAsymp
public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectEnd
public import MinCostFlow.Final.AssemblyDryRunSCTermCode
public import MinCostFlow.MinRatio.WireChainCoreBodyAKFBL
public import MinCostFlow.MinRatio.WireChainCoreMetaDisjBranchB
import MinCostFlow.Final.AssemblyDryRunSCCoreMissing
import Mathlib.Tactic

/-!
# The disjointness clause of the core at the dry values (`AssemblyDryRunSCCoreMetaDisj`)

Proves the disjointness clause of the core — pairwise disjointness of the `levelMeta` graph and length blocks
(`SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem`) after every run of the inner
chain-core block `dryInnerCoreCodeOf mkBranchB hBNoRand` at the dry parameters — directly from
`UpdateCoreSelPremAt` together with the three start-state hypotheses `(hglValid, hRebW, hLay)`
of `OrdChainUpdateCoreSpecWKFBLSel` (`Final/AssemblyDryRunSCCoreSelectProof.lean:191`), using:
* `ordChainUpdateCoreBodyKFBL_metaDisj_A` (`MinRatio/WireChainCoreBodyAKFBL.lean`) when level `0`
  overflows (Branch A), and
* the premise `OrdChainCoreBranchBMetaDisjKFBL`
  (`MinRatio/WireChainCoreMetaDisjBranchB.lean`, proved by `branchB_metaDisj_end`) when
  level `0` does not overflow (Branch B).

* `dryInnerCore_metaDisj_of_branchB`: general form for any inner codes and select sizes.
* `dryInnerCore_metaDisj_dry`: instantiated at the exact dry codes and `dryInnerCoreCode` /
  `dryInnerCoreSizes Psc` of `DryCoreOpenParts` (`Final/Theorem11Parts.lean`).
* `DryInnerCoreBranchBMetaDisj`: the Branch B premise (`OrdChainCoreBranchBMetaDisjKFBL`)
  at the dry values.
* `dryInnerCore_openPart2`: proves verbatim the second conjunct of
  `DryCoreOpenParts Psc dryInnerCoreCode (dryInnerCoreSizes Psc) (dryInnerCoreSizeBounds Psc)`
  under its `let` bindings from `DryInnerCoreBranchBMetaDisj Psc`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **The disjointness clause of the core at the dry values (`dryInnerCore_metaDisj_of_branchB`):** for any
inner chain-core block `dryInnerCoreCodeOf mkBranchB hBNoRand` at `dryInnerCoreSizes Psc`,
every run from a start state meeting `UpdateCoreSelPremAt` and the three start-state hypotheses `(hglValid, hRebW, hLay)` ends in a state meeting
`SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem`, taking only Branch B
(`OrdChainCoreBranchBMetaDisjKFBL`) as a premise. -/
theorem dryInnerCore_metaDisj_of_branchB (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (initSel : DryInitSelectSizes) (hInitSelSz : DryInitSelectSizeBounds initSel)
    (shiftSel : DryShiftSelectSizes) (hShiftSel : DryShiftSelectSizeBounds shiftSel) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let innerSz := dryInnerCoreSizes Psc
    let hInnerSz := dryInnerCoreSizeBounds Psc
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    let hSel := mkDrySelectRebuildSizeBounds hInitSelSz hShiftSel
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode) selectCode termCode
      deepCode
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
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      let b := lay.ordChainCore + 1
      let ops := mrdsCycleBase
      let env0 := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
        lastWordConst Psc.sc solverTailBase
      let envIn : SolverInnerEnv := { env0 with innerBase := b }
      let coreBody := ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
          (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch)
          (b + 6) (lay.scOp 2) (solverTailBase + 11) (b + 7) (b + 8) lay.scInit (lay.scOp 3)
          (b + 9) (lay.scOp 5) lay.lastInit (b + 11))
        (mkBranchB envIn)
      OrdChainCoreBranchBMetaDisjKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
        limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
        (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
        cfg G Rcore p (innerSz.coreSpace source J) coreBody →
      ∀ (innerBody : Stmt),
        p.procs[lay.ordChainCore + 1 + innerCoreCode.off]? = some innerBody →
        ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
            limbMul (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J)
            (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J)
            (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
            Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
            Runs w p ω innerBody
              (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
              (.returned nextHeap) out cost →
            tok'.table = tok.table →
            SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem := by
  intro innerCoreCode innerSz hInnerSz coreSz hCoreSz openSz hOpen selSz hSel inner
    source J hJn hJm _hCost hCap hw I V k F cfg G limbMul PscP Rcore s p lay w b ops env0 envIn
    coreBody hB innerBody hInnerAt root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model
    tok sg U B R hPrem hglValid hRebW hLay nextHeap cost out tok' hRun htab
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  rw [hAll.1] at hInnerAt
  have hBodyEq : innerBody = coreBody := Option.some.inj (hInnerAt.symm.trans hAll.2.1)
  subst hBodyEq
  have hExtM := dryCoreSel_hA1 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  have hWordExpLe : PscP.wordExp ≤ 39 := by
    dsimp only [PscP]; rw [drySCParams_wordExp]; exact drySCWordExp_le_39 Psc
  have hMiss := dryCoreSel_missingHyps (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) PscP.wordExp (le_max_right _ _) hWordExpLe
    source J hJn hJm hCap1 hw hPrem hglValid hRebW hLay
  have hMI := dryCoreSel_hA2_of_missing J hJn hJm hCap1 hw hPrem hMiss
  have hMK := dryCoreSel_hA3 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  have hFC := dryCoreSel_hA4 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  obtain ⟨hRep0, hMeta0, hCaps0, _, _, _, _, _, _, _, hNum0, hOffInv0, hOffBd0, _, hCapT, _, _,
    _, hIntCapEq, hIntCapMax, _, hLogW, hShift, _, hWire, hBran, _, _, hMemEq, hFresh, hTrNf,
    hBatch, hSmall, hEdits, hEditsW, hEdHeap, hRef, hFootLt, hGLt, hLLt, _, hULe, hz0,
    hRoom⟩ := hPrem
  have hRoomIn : heap + innerSz.coreSpace source J U.length < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) heap) hRoom
  by_cases hFire : intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 +
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length
  · have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
        dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
      (le_max_right _ _).trans (le_max_left _ _)
    have hE := dryInnerCore_branchAEnvKFBL Psc initCode selectCode termCode deepCode selInitCode
      mkBranchB hBNoRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
    exact ordChainUpdateCoreBodyKFBL_metaDisj_A (reembFn := dryReembFn J) hE hRep0 hMeta0 hCaps0
      hNum0 hOffInv0 hOffBd0 hMI hMK hIntCapMax hFC hLogW hCapT hMemEq hFresh hTrNf hBatch hSmall
      hEdHeap hRef (fun a ha => hFootLt a (Or.inl ha)) hGLt hLLt hULe hz0 hRoomIn hFire hRun htab
  · exact hB root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R hRep0 hMeta0
      hCaps0 hLay.2 hIntCapEq hExtM hNum0 hOffInv0 hOffBd0 hShift hWire hBran hMI hMK hIntCapMax
      hFC hLogW hCapT hMemEq hFresh hTrNf hBatch hSmall hEdits hEditsW hEdHeap hRef
      (fun a ha => hFootLt a (Or.inl ha)) hGLt hLLt hULe hz0 hRoomIn hFire
      nextHeap cost out tok' hRun htab

/-- **The disjointness clause of the core at the exact dry codes of `DryCoreOpenParts`:** specialization of
`dryInnerCore_metaDisj_of_branchB` to `dryInnerCoreCode` and `dryInnerCoreSizes Psc`. -/
theorem dryInnerCore_metaDisj_dry (Psc : DrySparseCorePieces) :
    let innerCoreCode := dryInnerCoreCode
    let innerSz := dryInnerCoreSizes Psc
    let hInnerSz := dryInnerCoreSizeBounds Psc
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
    let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
      (dryShiftSelectSizeBounds Psc)
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc))
      (dryCoreSelectCode innerCoreCode) drySelectRouteCode dryTermSelectCode dryDeepSelectCode
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
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      let b := lay.ordChainCore + 1
      let ops := mrdsCycleBase
      let env0 := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
        lastWordConst Psc.sc solverTailBase
      let envIn : SolverInnerEnv := { env0 with innerBase := b }
      let coreBody := ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
          (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch)
          (b + 6) (lay.scOp 2) (solverTailBase + 11) (b + 7) (b + 8) lay.scInit (lay.scOp 3)
          (b + 9) (lay.scOp 5) lay.lastInit (b + 11))
        (dryInnerCoreBranchB envIn)
      OrdChainCoreBranchBMetaDisjKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
        limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
        (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
        cfg G Rcore p (innerSz.coreSpace source J) coreBody →
      ∀ (innerBody : Stmt),
        p.procs[lay.ordChainCore + 1 + innerCoreCode.off]? = some innerBody →
        ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
            limbMul (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J)
            (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J)
            (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
            Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
            Runs w p ω innerBody
              (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
              (.returned nextHeap) out cost →
            tok'.table = tok.table →
            SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem :=
  dryInnerCore_metaDisj_of_branchB Psc (dryInitCode (dryParamCode Psc)) drySelectRouteCode
    dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryInitSelectSizes Psc) (dryInitSelectSizeBounds Psc)
    (dryShiftSelectSizes Psc) (dryShiftSelectSizeBounds Psc)

/-- **The Branch B premise for the second part of `DryCoreOpenParts`:**
`OrdChainCoreBranchBMetaDisjKFBL` at the dry parameters, `dryInnerCoreCode`, and
`dryInnerCoreSizes Psc`. -/
@[expose] def DryInnerCoreBranchBMetaDisj (Psc : DrySparseCorePieces) : Prop :=
  let innerCoreCode := dryInnerCoreCode
  let innerSz := dryInnerCoreSizes Psc
  let hInnerSz := dryInnerCoreSizeBounds Psc
  let coreSz := dryCoreSelectSizes Psc innerSz
  let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
  let openSz := coreSz.toDryOpenSizes
  let hOpen := hCoreSz.toDryOpenSizeBounds
  let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
  let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
    (dryShiftSelectSizeBounds Psc)
  let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc))
    (dryCoreSelectCode innerCoreCode) drySelectRouteCode dryTermSelectCode dryDeepSelectCode
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
    let PscP := drySCParams Psc dryCapExp limbMul
    let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
    let lay := dryTailLay Psc.sc inner
    let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
    let b := lay.ordChainCore + 1
    let ops := mrdsCycleBase
    let env0 := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
      lastWordConst Psc.sc solverTailBase
    let envIn : SolverInnerEnv := { env0 with innerBase := b }
    let coreBody := ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
        (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch)
        (b + 6) (lay.scOp 2) (solverTailBase + 11) (b + 7) (b + 8) lay.scInit (lay.scOp 3)
        (b + 9) (lay.scOp 5) lay.lastInit (b + 11))
      (dryInnerCoreBranchB envIn)
    OrdChainCoreBranchBMetaDisjKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
      limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
      (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
      cfg G Rcore p (innerSz.coreSpace source J) coreBody

/-- **Second conjunct of `DryCoreOpenParts` at the dry values (`dryInnerCore_openPart2`):**
for every `Psc : DrySparseCorePieces`, from `DryInnerCoreBranchBMetaDisj Psc` as its only
premise, proves verbatim the second conjunct of
`DryCoreOpenParts Psc dryInnerCoreCode (dryInnerCoreSizes Psc) (dryInnerCoreSizeBounds Psc)`
under its `let` bindings. -/
theorem dryInnerCore_openPart2 (Psc : DrySparseCorePieces)
    (hB : DryInnerCoreBranchBMetaDisj Psc) :
    let innerCoreCode := dryInnerCoreCode
    let innerSz := dryInnerCoreSizes Psc
    let hInnerSz := dryInnerCoreSizeBounds Psc
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
    let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
      (dryShiftSelectSizeBounds Psc)
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc))
      (dryCoreSelectCode innerCoreCode) drySelectRouteCode dryTermSelectCode dryDeepSelectCode
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
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      ∀ (innerBody : Stmt),
        p.procs[lay.ordChainCore + 1 + innerCoreCode.off]? = some innerBody →
        ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
            limbMul (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J)
            (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J)
            (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
              Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
            Runs w p ω innerBody
              (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
              (.returned nextHeap) out cost →
            tok'.table = tok.table →
            SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem :=
  fun source J hJn hJm hCost hCap hw =>
    dryInnerCore_metaDisj_dry Psc source J hJn hJm hCost hCap hw
      (hB source J hJn hJm hCost hCap hw)

end MinCostFlow.Final.DryRun

end
