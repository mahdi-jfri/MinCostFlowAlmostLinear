module

public import MinCostFlow.Final.AssemblyDryRunSCInnerCode
public import MinCostFlow.Final.AssemblyDryRunSCInnerSizes
public import MinCostFlow.Final.AssemblyDryRunSCCoreFacts
public import MinCostFlow.Final.AssemblyDryRunSCCoreAdapters
public import MinCostFlow.MinRatio.WireChainCoreSpecProofKFBL
import MinCostFlow.Final.AssemblyDryRunSCDeepSelectCode
import MinCostFlow.Final.AssemblyDryRunSCSelInitTight
import MinCostFlow.Final.AssemblyDryRunSCInit
import MinCostFlow.Final.AssemblyDryRunSCRem
import Mathlib.Tactic

/-!
# Dry-run `BranchAEnvKFBL` and `OrdChainUpdateCoreSpecWExtKFBL` (`AssemblyDryRunSCInnerEnv`)

Constructs the chain-update core environment `BranchAEnvKFBL` and operational budget
`UpdateCoreOpsHypKFBL` at `dryLinkedProgramSel` and the dry parameters (`dryInnerCoreSizes Psc`),
and deduces the extended chain-core specification `OrdChainUpdateCoreSpecWExtKFBL` at
`lay.ordChainCore + 1 + innerCoreCode.off` with Branch B (`OrdChainCoreBranchBPostKFBL`) as the
only premise:

* `dryInnerCore_opsHypKFBL`: unconditionally proves `UpdateCoreOpsHypKFBL` at `dryInnerCoreSizes`.
* `dryInnerCore_branchAEnvKFBL`: unconditionally proves `BranchAEnvKFBL` for
  `dryInnerCoreCodeOf mkBranchB hBNoRand` inside `dryLinkedProgramSel` (for any allocation
  parameters `allocationCoefficient`, `allocationDegree` satisfying the dry word-size bound).
* `dryInnerCore_extSpec_of_branchB`: proves `OrdChainUpdateCoreSpecWExtKFBL` at
  `lay.ordChainCore + 1 + innerCoreCode.off` and `dryInnerCoreSizes Psc` from
  `ordChainUpdateCoreSpecWExtKFBL_of_branchB`, `dryInnerCore_branchAEnvKFBL`, the three dry
  parameter facts (`dryCore_hGSup`, `dryCore_hGM`, `dryCore_hM0Le`), and `hB`
  (`OrdChainCoreBranchBPostKFBL`) as its only premise.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Unconditional `UpdateCoreOpsHypKFBL` at the dry values -/

/-- Unconditional `UpdateCoreOpsHypKFBL` at the dry parameters and `dryInnerCoreSizes Psc`. -/
theorem dryInnerCore_opsHypKFBL (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    UpdateCoreOpsHypKFBL (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m)
      (capExp := dryCapExp) (capLimit := dryCapLimit W J) (fcap := dryDeepFCap J)
      (lastMul := dryLastMult J) (intCapMax := dryDeepIntCapMax J)
      (forestEdgeCap := dryDeepForestEdgeCap J) (drainUnit := detectOffTreeDrainUnit F.limbs)
      (edMul := drySCEdMul Psc dryCapExp limbMul) (mThresh := concreteEdgeThresholdWithLast W)
      (coreSpace := dryInnerCoreSpace Psc J) (coreFixed := dryInnerCoreFixed Psc J)
      (toolMul := dryInnerCoreToolMul Psc J) (fmt := F.fmt) (cfg := cfg) (G := G) (Psc := PscP)
      (allocation := drySCAlloc Psc dryCapExp limbMul J)
      (lastAlloc := fun _ _ => dryLastSpace J)
      (dryDeepLevelSpace Psc J)
      (updateCoreRebuildLevelCost F.limbs dryCapExp cfg PscP)
      (dryInnerCoreUpdStepSpace Psc J)
      (dryLastSpace J)
      (dryInnerCoreTermUpdSpace J)
      (dryInnerCoreStepCap J) where
  levelSpaceDom := fun next j gB lB grB oB h hj hFacts hNextM =>
    dryInnerCore_levelSpaceDom_guarded Psc J
      (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).fmt
      next j gB lB grB oB h hj hFacts hNextM
  lastSpaceDom := fun _ _ _ => le_rfl
  updStepSpaceDom := fun idx uLen coreH gB bPtr bW ePtr eW lB h nU uL _ hbW heW hnU huL =>
    dryInnerCore_updStepSpaceDom Psc J hJn hJm hCapPos idx uLen coreH gB bPtr bW ePtr eW lB h
      nU uL hbW heW hnU huL
  termUpdSpaceDom := dryInnerCore_termUpdSpaceDom J
  levelCostDom := fun next j _ => dryInnerCore_levelCostDom Psc J next j
  spaceTotalBranchA := fun n rootECap uLen mNew hn hroot hmNew =>
    dryInnerCore_spaceTotalBranchA Psc J n rootECap uLen mNew hn hroot hmNew
  spaceTotalBranchB := fun uLen => dryInnerCore_spaceTotalBranchB Psc J uLen
  costTotalBranchA := dryInnerCore_costTotalBranchA Psc J hJn hJm hCapPos hw
  costTotalBranchB := dryInnerCore_costTotalBranchB Psc J hJn hJm hCapPos hw

/-! ## 2. Unconditional `BranchAEnvKFBL` at `dryLinkedProgramSel` and the dry values -/

/-- Unconditional `BranchAEnvKFBL` at `dryLinkedProgramSel` and the dry values for any
inner chain-core block `dryInnerCoreCodeOf mkBranchB hBNoRand`. -/
theorem dryInnerCore_branchAEnvKFBL (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (allocationCoefficient allocationDegree : ℕ)
    (hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      allocationCoefficient)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    let Rcore := drySCRep Psc allocationCoefficient allocationDegree source J hw
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let w := dryWordSize W allocationCoefficient allocationDegree source
    let b := lay.ordChainCore + 1
    let ops := mrdsCycleBase
    BranchAEnvKFBL w F.limbs F.fmt.precision I.m dryCapExp (dryCapLimit W J)
      (dryDeepFCap J) (dryLastMult J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
      (detectOffTreeDrainUnit F.limbs) (drySCEdMul Psc dryCapExp limbMul)
      (concreteEdgeThresholdWithLast W) PscP.wordExp (dryLastStretchP J)
      G.n (initTargetCap cfg G)
      (b + 1) (ops + 81) (b + 2) (b + 3) (ops + 69) (b + 4) (ops + 20) (ops + 4) (b + 5)
      (ops + 16) (ops + 2) (ops + 6) ops (b + 34 + dgIdxApplyBatch) (b + 6)
      lay.scInit (solverTailBase + 11) (b + 7) (b + 8) (b + 34 + dgIdxInitFromLists)
      (b + 9) (b + 10) (ops + 17) (ops + 11) (ops + 22) lay.lastInit (b + 11)
      (dryInnerCoreSpace Psc J) (dryInnerCoreFixed Psc J) (dryInnerCoreToolMul Psc J)
      F.fmt cfg G PscP
      (dryDeepLevelSpace Psc J)
      (updateCoreRebuildLevelCost F.limbs dryCapExp cfg PscP)
      (dryInnerCoreUpdStepSpace Psc J)
      (dryLastSpace J)
      (dryInnerCoreTermUpdSpace J)
      (drySCAlloc Psc dryCapExp limbMul J) (fun _ _ => dryLastSpace J)
      Rcore p (dryPathTreeOp ops) lay.scOp lay.lastOp (dryInnerCoreStepCap J) := by
  intro W I V k F cfg G limbMul PscP Rcore innerCoreCode inner p lay w b ops
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw18 : 18 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 18 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hWidth : F.fmt.precision ≤ 4 * F.limbs := by
    change ipmQualityPrecision I.m V k ≤ 4 * ipmQualityLimbs I.m V k
    unfold ipmQualityLimbs; omega
  have hLPos : 0 < F.limbs := by
    change 0 < ipmQualityLimbs I.m V k
    unfold ipmQualityLimbs; omega
  have hImPos : 0 < I.m :=
    lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCapPos).1
  have hECapPos : 0 < initTargetCap cfg G := by
    unfold initTargetCap; rw [namedInstance_m]; omega
  have hL4W : 4 * F.limbs + 2 < 2 ^ w := by
    have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
      have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
        Nat.lt_size_self _
      calc 2 ^ 14 * ipmQualityParameterBound I.m V k
          < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
            Nat.mul_lt_mul_of_pos_left hsz (by decide)
        _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    omega
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W)
      allocationCoefficient allocationDegree hWordCoeff source J hJn hJm hCapPos hw
  have hN0W : cfg.N₀ < 2 ^ w :=
    lt_of_le_of_lt (by change 4 * cfg.P.M₀ ≤ 4 * cfg.P.M₀ + 3; omega) h4M3W
  have hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w := by
    have hM1 : 1 ≤ cfg.P.M₀ := le_trans (by decide : 1 ≤ 2)
      ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
    exact lt_of_le_of_lt ((chosenL_sq_le_four_mul_add_one hM1).trans
      (by change 4 * cfg.P.M₀ + 1 ≤ 4 * cfg.P.M₀ + 3; omega)) h4M3W
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
  have hdW : cfg.P.d < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h2b : 2 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase
      have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
      nlinarith
    have h1 : cfg.P.d < 2 ^ (cfg.P.d + 1) :=
      Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    have h2 : 2 ^ (cfg.P.d + 1) ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.pow_le_pow_left h2b _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact (h1.trans_le (h2.trans h3)).trans hQuotaBoundW
  have hInitOrdEq : ToolInitOrdEqOnE cfg.T := by
    have hT := concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
    rw [hT]
    intro k' M N G' ℓ₁ ℓ₂ g₁ g₂ ord hℓ
    exact sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _ k' M N G' ℓ₁ ℓ₂ g₁ g₂ ord hℓ
  have hOpsAt := dryLinkedProgramSel_ops_hasAt W Psc.sc inner selInitCode
  obtain ⟨hCopyC, hNegC, hMulC, hDivC, hSignC, hShiftC, hIntDivC, _⟩ :=
    solverOpsProcs_initHelpers hw14 hOpsAt
  obtain ⟨_, hAddC, _, hSubC, hIsNegC, hTreeImpl⟩ :=
    solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl hOpsAt
  obtain ⟨_, _, hPackP, _, _, hRefAccP, hRefOneP, hUpdLen0P, hCompP, hSortP, hCoreLenP,
    hEdgeP, hRebuildP, _⟩ :=
    dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
      mkBranchB hBNoRand
  exact
    { coreLocal := drySCRep_local Psc allocationCoefficient allocationDegree source J hw
      four := rfl
      prec := rfl
      width := hWidth
      lPos := hLPos
      eCapPos := hECapPos
      lW := by omega
      pW := by omega
      depthW := hDepthW
      dW := hdW
      kPos := cfg.P.hk
      kW := hkW
      nW := hN0W
      w18 := hw18
      capLim := dry_initTargetCap_le_capLimit J hJn hJm hCapPos
      initOrdEq := hInitOrdEq
      wordExpEq := rfl
      packP := hPackP
      refAccP := hRefAccP
      refOneP := hRefOneP
      updLen0P := hUpdLen0P
      treeImpl := hTreeImpl
      bindC := dryInnerCoreCodeOf_bindC Psc initCode selectCode termCode deepCode selInitCode
        mkBranchB hBNoRand w
      canonC := fun v => dryInnerCoreCodeOf_canonC Psc initCode selectCode termCode deepCode
        selInitCode mkBranchB hBNoRand hw14 v
      isNegC := hIsNegC
      shiftC := hShiftC
      divC := hDivC
      addC := hAddC
      subC := hSubC
      negC := hNegC
      copyC := hCopyC
      dgApplyC := fun G' U bW => dryInnerCoreCodeOf_dgApplyC Psc initCode selectCode termCode
        deepCode selInitCode mkBranchB hBNoRand w G.n (initTargetCap cfg G) G' U bW
      coreImpl := fun j hj H hH hHm =>
        drySC_coreKFBL_sel Psc inner selInitCode allocationCoefficient allocationDegree source J
          hJn hJm hCapPos hw j hj H hH hHm
      renP := dryInnerCoreCodeOf_renP Psc initCode selectCode termCode deepCode selInitCode
        mkBranchB hBNoRand
      compP := hCompP
      sortP := hSortP
      dgInitC := fun G' vL eTriples => dryInnerCoreCodeOf_dgInitC Psc initCode selectCode termCode
        deepCode selInitCode mkBranchB hBNoRand w G.n (initTargetCap cfg G) G' vL eTriples
      coreLenP := hCoreLenP
      edgeP := hEdgeP
      signC := hSignC
      mulC := hMulC
      intDivC := hIntDivC
      lastImpl := dryDeepSelectCode_hLastImpl_sel Psc inner selInitCode allocationCoefficient
        allocationDegree source J hJn hJm hCapPos hw
      ops := dryInnerCore_opsHypKFBL Psc J hJn hJm hCapPos hw
      rebuildP := hRebuildP }

/-! ## 3. `OrdChainUpdateCoreSpecWExtKFBL` at the dry values with `hB` as the only premise -/

/-- **Extended chain-core specification at the dry values (`dryInnerCore_extSpec_of_branchB`):**
for any `innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand`, proves
`OrdChainUpdateCoreSpecWExtKFBL` at `lay.ordChainCore + 1 + innerCoreCode.off` and
`dryInnerCoreSizes Psc` from `ordChainUpdateCoreSpecWExtKFBL_of_branchB`,
`dryInnerCore_branchAEnvKFBL`, and `dryCore_hGSup`/`dryCore_hGM`/`dryCore_hM0Le`, taking only
Branch B (`OrdChainCoreBranchBPostKFBL`) as a premise. -/
theorem dryInnerCore_extSpec_of_branchB (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (allocationCoefficient allocationDegree : ℕ)
    (hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      allocationCoefficient)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (Bb Rb : ℤ) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G := namedInstance I
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    let Rcore := drySCRep Psc allocationCoefficient allocationDegree source J hw
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let w := dryWordSize W allocationCoefficient allocationDegree source
    let b := lay.ordChainCore + 1
    let ops := mrdsCycleBase
    let env0 := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc solverTailBase
    let envIn : SolverInnerEnv := { env0 with innerBase := b }
    let innerSz := dryInnerCoreSizes Psc
    let coreBody := ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
        (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch) (b + 6)
        (lay.scOp 2) (solverTailBase + 11) (b + 7) (b + 8) lay.scInit (lay.scOp 3)
        (b + 9) (lay.scOp 5) lay.lastInit (b + 11))
      (mkBranchB envIn)
    OrdChainCoreBranchBPostKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit W J) PscP.wordExp (dryLastStretchP J)
      (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
      cfg G (dryReembFn J) Rcore p (innerSz.coreSpace source J) (innerSz.coreFixed source J)
      (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) Bb Rb coreBody →
    OrdChainUpdateCoreSpecWExtKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit W J) PscP.wordExp (dryLastStretchP J)
      (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
      cfg G (dryReembFn J) Rcore p (lay.ordChainCore + 1 + innerCoreCode.off)
      (innerSz.coreSpace source J) (innerSz.coreFixed source J)
      (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) Bb Rb := by
  intro W I V k F cfg G limbMul PscP Rcore innerCoreCode inner p lay w b ops env0 envIn innerSz
    coreBody hB
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  have hE := dryInnerCore_branchAEnvKFBL Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand allocationCoefficient allocationDegree hWordCoeff source J hJn hJm
    hCapPos hw
  rw [hAll.1]
  exact ordChainUpdateCoreSpecWExtKFBL_of_branchB hE hAll.2.1
    (dryCore_hGSup I) (dryCore_hGM I) (dryCore_hM0Le W J) hB

end MinCostFlow.Final.DryRun

end
