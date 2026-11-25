module

public import MinCostFlow.Final.AssemblyDryRunSCTermCode
public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectEnd
public import MinCostFlow.Final.AssemblyDryRunSCFirstInit

/-!
# Theorem 1.1 from two parts of the dry run (`Theorem11Parts`)

`theorem_1_1_of_parts` is Theorem 1.1 (page 2) from two parts of the dry run, taken as hypotheses.
It plugs into `theorem_1_1_skeleton_kfbl_sel_term`:
- the first phase of the init of a branch (`dryFirstInit`, `drySC_hFirstInit`);
- the wrapper of the chain core (`dryCoreSelectCode`, `dryCoreSelectSizes`,
  `dryCoreSel_hCoreSel_of_ext`).

Its hypotheses are these parts:
- the first phase of the step of a branch (`firstStep`, `C`, `hC`, `hFirstStep`), with the
  constants of the init (`hInitMul`, `hInitSpace`);
- the inner block of the chain core (`innerCoreCode`, `innerSz`, `hInnerSz`), its spec `hExt`
  (`OrdChainUpdateCoreSpecWExtKFBL` at every budget), and the disjointness clause of the core: after a run of
  the inner block, the level blocks are apart (`SolverLevelMetaDisjAt`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- The two parts of the chain core, at the sparse-core pieces `Psc`: the inner block
`innerCoreCode` meets `OrdChainUpdateCoreSpecWExtKFBL` at `innerSz` at every budget, and after a
run of the inner block the level blocks are apart (`SolverLevelMetaDisjAt`, the disjointness
clause of the core). -/
@[expose] def DryCoreOpenParts (Psc : DrySparseCorePieces) (innerCoreCode : SolverInnerSubCode)
    (innerSz : DryCoreOpenSizes) (hInnerSz : DryCoreOpenSizeBounds innerSz) : Prop :=
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
        (∀ Bb Rb : ℤ,
          OrdChainUpdateCoreSpecWExtKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
            limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
            (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
            cfg G (dryReembFn J) Rcore p (lay.ordChainCore + 1 + innerCoreCode.off)
            (innerSz.coreSpace source J) (innerSz.coreFixed source J)
            (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) Bb Rb) ∧
        (∀ (innerBody : Stmt),
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
              SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem)

/-- **Factored `DyadicWithVConcretePrograms` bundle from the parts of `DryCoreOpenParts` and
the first step of a branch.** -/
noncomputable def dryDyadicWithVBundle_parts
    (firstStep : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hInitMul : ∀ capExp limbMul, C.initMul capExp limbMul = dryFirstInitMul capExp limbMul)
    (hInitSpace : ∀ capExp, C.initSpace capExp = dryFirstInitSpace capExp)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep dryFirstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep dryFirstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JS : AsmBrCoreStepAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
              sparsifyImplUsed depth fmt.precision L_in capExp limbMul
              (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreS,
            JS.mul = C.stepMul capExp limbMul ∧
            JS.ysMul = C.stepYs capExp limbMul ∧
            JS.spaceP = C.stepSpace capExp)
    (innerCoreCode : SolverInnerSubCode)
    (innerSz : DryCoreOpenSizes) (hInnerSz : DryCoreOpenSizeBounds innerSz)
    (hParts : DryCoreOpenParts
      (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
        (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace))
      innerCoreCode innerSz hInnerSz) :
    DyadicWithVConcretePrograms :=
  dryDyadicWithVBundle_term firstStep dryFirstInit C hC hFirstStep
    (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)
    (dryCoreSelectCode innerCoreCode)
    (dryCoreSelectSizes (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)) innerSz)
    (dryCoreSelectSizeBounds (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)) hInnerSz)
    (fun source J hJn hJm hCost hCap hw =>
      dryCoreSel_hCoreSel_of_ext (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace))
        (dryInitCode (dryParamCode (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)))) innerCoreCode
        drySelectRouteCode dryTermSelectCode dryDeepSelectCode drySelInitCode innerSz hInnerSz
        (dryInitSelectSizes (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace))) (dryInitSelectSizeBounds (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)))
        (dryShiftSelectSizes (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace))) (dryShiftSelectSizeBounds (mkDrySparseCorePieces firstStep dryFirstInit C hC hFirstStep
      (drySC_hFirstInit dryCompCode dryCFS firstStep C hInitMul hInitSpace)))
        source J hJn hJm hCost hCap hw
        (hParts source J hJn hJm hCost hCap hw).1 (hParts source J hJn hJm hCost hCap hw).2)

end MinCostFlow.Final.DryRun
