module

public import MinCostFlow.Final.AssemblyDryRunSCRem
public import MinCostFlow.Final.AssemblyDryRunSCEnvelope
public import MinCostFlow.Final.AssemblyDryRunSCCompImpl
public import MinCostFlow.Statement.Main

/-!
# An assembly theorem for Theorem 1.1 (`Theorem11Skeleton`)

Proves the exact challenge statement `MinCostFlowStatement` (`MinCostFlow/Statement/Main.lean`,
matching `Comparator/Challenge.lean`) directly from `theorem_1_1_dry_run_sc_open`
(`Final/AssemblyDryRunSCCoreKFBL.lean`), discharging automatically:
* `DrySCInitOpenHyps.hInitSpaceLe` via `drySC_hInitSpaceLe_proved` at `dryCoreInitSpace`
  (`Final/AssemblyDryRunSCInitSpace.lean`);
* `rem : SolverInnerOpenNoParam` and `rem.IsDeterministic` via `dryInnerRem` and
  `dryInnerRem_isDeterministic` (`Final/AssemblyDryRunSCRem.lean`), with `evalCycleBody` and
  `shiftTermChainBody` installed concretely;
* `DrySCSolverHyps.hEval` (`OrdCycleRouteEvalSpecW`) via `drySC_hEval_proved`
  (`Final/AssemblyDryRunSCRem.lean`), leaving only two plain inequalities (`hEvalSpace`,
  `hEvalBudget`) on `sz`;
* `DrySCSolverHyps.hTerm` (`ShiftTermChainSyncSpecWExt` at `lastTreeCap = 2 * levelM cfg.TP cfg.P
  cfg.P.d`) via `drySC_hTermExt_proved` (`Final/AssemblyDryRunSCRem.lean`), leaving only three
  plain inequalities (`hTermSpace`, `hTermFixed`, `hTreeMul`) on `sz`.

Two theorems are provided:
* `theorem_1_1_skeleton`: takes the sparse-core first-phase pieces (`firstStep`,
  `firstInit`, `C`, `hC`, `hFirstStep`, `hFirstInit`, with P4 discharged unconditionally via
  `dryCompCode`, `dryCFS`, `dryCF_hyp` in `Final/AssemblyDryRunSCCompImpl.lean`), the three
  solver inner blocks (`coreCode`, `selectCode`, `deepCode`), `B` with the eight clauses of
  `InnerBoundsHyp B`, `sz`, the three Init size bounds (`hSpaceLe`, `hFixedLe`, `hMulLe`), the two
  Eval size bounds (`hEvalSpace`, `hEvalBudget`), the three Term size bounds (`hTermSpace`,
  `hTermFixed`, `hTreeMul`), the three other inner specs (`hCore`, `hSelect`, `hDeep`),
  `hCapBounds`, and `hEnv`.
* `theorem_1_1_skeleton_of_ineqs`: additionally replaces `hCapBounds` and `hEnv` with the plain
  inequality structures `DryCapSimpleBounds`, `DryEnvelopeIneqs`, and the `tok.offReadyCount ≤
  B.names I.m` reachability bound via `dryFixedPointCapBounds_of_bounds` and `drySC_hEnv_of_ineqs`.

The conclusion of `theorem_1_1_dry_run_sc_open` is definitionally `MinCostFlowStatement`, the
statement of `Comparator/Challenge.lean`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- Assembles `DrySparseCorePieces` from the unpacked first-phase branch hypotheses, instantiating
P4 unconditionally via `dryCompCode`, `dryCFS`, and `dryCF_hyp`. -/
def mkDrySparseCorePieces
    (firstStep firstInit : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
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
    (hFirstInit :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
              limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp) :
    DrySparseCorePieces where
  cf := dryCompCode
  firstStep := firstStep
  firstInit := firstInit
  CFS := dryCFS
  hCF := dryCF_hyp
  hBR := ⟨⟨C, hC, fun depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot =>
    ⟨hFirstStep depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot,
     hFirstInit depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot⟩⟩⟩

/-- **Theorem 1.1 (page 2) from the hypotheses of the assembly.**
Derives `MinCostFlowStatement` (`MinCostFlow/Statement/Main.lean`, `Comparator/Challenge.lean`)
from `theorem_1_1_dry_run_sc_open`, discharging P4 (`dryCompCode`, `dryCFS`, `dryCF_hyp`),
`hInitSpaceLe`, `rem` (`evalCycle` and `shiftTermChain` concrete), `rem.IsDeterministic`, and
`hEval` (`OrdCycleRouteEvalSpecW`) automatically. -/
theorem theorem_1_1_skeleton
    -- 1. Sparse-core branch first phases (step and init; P4 is proved in `dryCF_hyp`)
    (firstStep firstInit : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
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
    (hFirstInit :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
              limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp)
    -- 3. Three solver inner blocks as parameters (`eval` and `term` are concrete in `dryInnerRem`)
    (coreCode selectCode deepCode : SolverInnerSubCode)
    -- 4. Solver rate and space bounds (`OrdSolverInnerBounds` + 8 clauses of `InnerBoundsHyp`)
    (B : OrdSolverInnerBounds)
    (hLimbsSub : SubpolyNat B.limbs)
    (hVertsSub : SubpolyNat (fun M => Nat.log 2 (2 * B.verts M + 1)))
    (hInitBudgetSub : SubpolyNat (fun M => B.initBudget M / (M + 1)))
    (hUpdateRateSub : SubpolyNat B.updateRate)
    (hLimbsPoly : PolyNat B.limbs)
    (hNamesPoly : PolyNat B.names)
    (hInitSpacePoly : PolyNat B.initSpace)
    (hUpdateSpacePoly : PolyNat B.updateSpace)
    -- 5. Per-input inner sizes
    (sz : Circulation → Circulation → WiredInnerSizes)
    -- 6. Three Init size bounds (at `dryCoreInitSpace`; `hInitSpaceLe` is proved)
    (hSpaceLe :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d (dryParamSpace source J) dryCapExp
          (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
          (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
          (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
          (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1))
          cfg.N₀ ≤
        (sz source J).initSpace')
    (hFixedLe :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let limbMul := concreteReadout2LimbMul dryWitnessUsed
        initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d (dryParamCost source J) dryCapExp
          (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC
          (drySCParams Psc dryCapExp limbMul)
          (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
        (sz source J).initFixed)
    (hMulLe :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      ∀ source J,
        max (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).mul
          (dryLastMult J) ≤ (sz source J).toolMul)
    -- 7. Two plain size inequalities discharging `hEval` (`evalCycleBody_meets_spec`)
    (hEvalSpace :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleSpace F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalSpace)
    (hEvalBudget :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleBudget F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalBudget)
    -- 8. Four inner-level specs, capacity bounds, and contract envelope
    (hCore :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        OrdChainUpdateCoreSpecWKFBL
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) G.n (initTargetCap cfg G) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul s.B_bound s.R_bound)
    (hSelect :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        OrdCycleRouteSelectSpecW
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).selectRoute
          s.selectSpace s.selectBudget s.maxEdges s.maxPaths)
    (hTermSpace :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs) ≤
          (sz source J).termSpace)
    (hTermFixed :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J _ =>
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 ≤ (sz source J).termFixed)
    (hTreeMul :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤
          (sz source J).treeMul)
    (hDeep :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        ShiftDeepChainSyncSpecWExtKFBL
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
          ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size)
          (2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m))
          (2 * (cfg.P.d + 1) * I.n) G.n (initTargetCap cfg G) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).shiftDeepChain
          s.deepSpace s.deepFixed s.toolMul s.treeMul)
    (hCapBounds :
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) sz)
    (hEnv :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let hB : InnerBoundsHyp B :=
        ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
         ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10)
          (s.initSpace' + initWiredExtraSpace cfg (namedInstance I))
          (s.initFixed + initWiredExtraCost cfg (namedInstance I))
          (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
          (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
          s.maxEdges s.maxPaths s.toolMul s.treeMul
          (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
          (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
            62 * (cfg.P.d + 1) + 240)
          Rcore B.cycleRate (B.cycleAllocation I.n I.m)) :
    MinCostFlowStatement := by
  let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
  let rem := dryInnerRem coreCode selectCode deepCode
  let hB : InnerBoundsHyp B :=
    ⟨⟨hLimbsSub, hVertsSub, hInitBudgetSub, hUpdateRateSub⟩,
     ⟨hLimbsPoly, hNamesPoly, hInitSpacePoly, hUpdateSpacePoly⟩⟩
  let hOpen : DrySCInitOpenHyps Psc rem B hB sz :=
    { coreInitSpace := fun _ J => dryCoreInitSpace Psc J
      hInitSpaceLe := drySC_hInitSpaceLe_proved Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      hSpaceLe := hSpaceLe
      hFixedLe := hFixedLe
      hMulLe := hMulLe }
  let hS : DrySCSolverHyps Psc rem.toSolverInnerOpen B hB sz :=
    { hCore := hCore
      hSelect := hSelect
      hEval := drySC_hEval_proved Psc coreCode selectCode deepCode B hB sz hEvalSpace hEvalBudget
      hTerm := drySC_hTermExt_proved Psc coreCode selectCode deepCode B hB sz
        (fun _ J => let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
          2 * levelM cfg.TP cfg.P cfg.P.d)
        hTermSpace hTermFixed hTreeMul
      hDeep := hDeep
      hCapBounds := hCapBounds
      hEnv := hEnv }
  exact theorem_1_1_dry_run_sc_open Psc rem
    (dryInnerRem_isDeterministic coreCode selectCode deepCode) B hB sz hOpen hS

/-- Corollary of `theorem_1_1_skeleton` that additionally replaces `hCapBounds` and `hEnv` with
the plain arithmetic inequalities `DryCapSimpleBounds` and `DryEnvelopeIneqs` (plus the single
`tok.offReadyCount ≤ B.names I.m` reachability bound). -/
theorem theorem_1_1_skeleton_of_ineqs
    (Psc : DrySparseCorePieces)
    (coreCode selectCode deepCode : SolverInnerSubCode)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInitSize : DrySCInitSizeHyps Psc B hB sz)
    (hEvalSpace : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleSpace F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalSpace)
    (hEvalBudget : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleBudget F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalBudget)
    (hCore :
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        OrdChainUpdateCoreSpecWKFBL
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) G.n (initTargetCap cfg G) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul s.B_bound s.R_bound)
    (hSelect :
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        OrdCycleRouteSelectSpecW
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).selectRoute
          s.selectSpace s.selectBudget s.maxEdges s.maxPaths)
    (hTermSpace : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs) ≤
          (sz source J).termSpace)
    (hTermFixed : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J _ =>
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 ≤ (sz source J).termFixed)
    (hTreeMul : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤
          (sz source J).treeMul)
    (hDeep :
      let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
        let s := sz source J
        ShiftDeepChainSyncSpecWExtKFBL
          (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
          ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size)
          (2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m))
          (2 * (cfg.P.d + 1) * I.n) G.n (initTargetCap cfg G) cfg Rcore
          (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
          (dryTailLay Psc.sc openInner.toInnerCode).shiftDeepChain
          s.deepSpace s.deepFixed s.toolMul s.treeMul)
    (hCapSimple : DryCapSimpleBounds B hB sz)
    (hEnvIneqs : DryEnvelopeIneqs B hB sz)
    (hNames : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun _source J _hw =>
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m ≤ B.names I.m) :
    MinCostFlowStatement :=
  theorem_1_1_dry_run_sc_initSpace Psc (dryInnerRem coreCode selectCode deepCode)
    (dryInnerRem_isDeterministic coreCode selectCode deepCode) B hB sz hInitSize
    { hCore := hCore
      hSelect := hSelect
      hEval := drySC_hEval_proved Psc coreCode selectCode deepCode B hB sz hEvalSpace hEvalBudget
      hTerm := drySC_hTermExt_proved Psc coreCode selectCode deepCode B hB sz
        (fun _ J => let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
          2 * levelM cfg.TP cfg.P cfg.P.d)
        hTermSpace hTermFixed hTreeMul
      hDeep := hDeep
      hCapBounds := dryFixedPointCapBounds_of_bounds B hB sz hCapSimple
      hEnv := drySC_hEnv_of_ineqs Psc B hB sz hEnvIneqs hNames }

end MinCostFlow.Final.DryRun

end
