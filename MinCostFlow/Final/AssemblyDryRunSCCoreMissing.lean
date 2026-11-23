module

public import MinCostFlow.Final.AssemblyDryRunSCCoreAdapters
public import MinCostFlow.Final.AssemblyDryRunSCCoreLoopModel
public import MinCostFlow.MinRatio.SolverLevelLayout
import MinCostFlow.Final.AssemblyDryRunSCDeepUpdate
import Mathlib.Tactic

/-!
# The facts `CoreSelMissingHyps` at the start of the wrapper (`AssemblyDryRunSCCoreMissing`)

The wrapper of the chain core calls the inner block with the premises of the Sel core spec
(`OrdChainUpdateCoreSpecWKFBLSel`, `MinRatio/OrdSelSpecs.lean`). The adapter
`dryCoreSel_hA2_of_missing` needs, besides the list `UpdateCoreSelPremAt`, the three facts of
`CoreSelMissingHyps`. This file proves them, at the dry values, from `UpdateCoreSelPremAt` and the
last three premises of the Sel core spec:
- the layout of the level blocks (`SolverLevelLayoutAt`) is `CoreSelMetaDisjInv`, word for word;
- the limbs of `g` and `l` at the inserted edges are valid is
  `CoreSelVecValidInv`, word for word;
- `UpdateLoopModelInv` is `dryCoreSel_updateLoopModelInv`
  (`Final/AssemblyDryRunSCCoreLoopModel.lean`). Its inputs are conjuncts of
  `UpdateCoreSelPremAt`, the bound `rebuildCount i + 1 < 2 ^ w`, and the
  grid of lengths after the update. The grid comes from `dryChainLenGridInv_preLoop_of_reached`,
  whose input says that each new length lies on the grid of the format: an inserted edge reads its
  length from `l`, and an old edge keeps the length of the model.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **The facts `CoreSelMissingHyps` at the dry values.** On a start state of the wrapper
(`UpdateCoreSelPremAt`) where the last three premises of `OrdChainUpdateCoreSpecWKFBLSel` hold
(valid limbs of `g` and `l` at the inserted edges, the rebuild counts below `2 ^ w`, and the layout
of the level blocks), the three facts of `CoreSelMissingHyps` hold. -/
theorem dryCoreSel_missingHyps
    (allocationCoefficient allocationDegree wordExp : ℕ)
    (hSCWordCoeff : Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize
      dryWitnessUsed) ≤ allocationCoefficient)
    (hWordExpLe : wordExp ≤ 39)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    {limbMul intCapMax forestEdgeCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {coreSpace : ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap : ℕ} {mem0 mem : ℕ → ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J)
      (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).limbs
      Rcore}
    {sg : SelectGhost} {U : List Update} {B R : ℤ} :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace
      root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
    (∀ u ∈ U, ∀ e, u.Inserts e →
      Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧ Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
    (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
    SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
    CoreSelMissingHyps w F.fmt.precision wordExp (dryLastStretchP J) G.n (initTargetCap cfg G) g l
      model tok U mem0
      (updateOverlay model.extG.E U (readVector mem0 g 4 F.limbs F.fmt.precision I.m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 F.limbs F.fmt.precision I.m) model.extℓ) := by
  intro I V k F cfg G w hPrem hVecValid hRebW hLay
  -- The first two fields are the limb premise and the layout, word for word.
  refine ⟨hLay, hVecValid, ?_⟩
  obtain ⟨hRep0, _, _, _, _, _, hReach, hGrid0, _, _, _, _, _, _, _, _, _, _, hICap, _, _, _,
    hShift0, hShift1, _, _, hGLRng, hAgree, _, _, hnfCap, _, _, _, _, _, hRef, _⟩ := hPrem
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 F.limbs F.fmt.precision I.m)
    model.extℓ
  have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh := hRep0.2.2.2.2.1
  obtain ⟨hExtG, _, hℓOld⟩ := dryReached_extG_g_ℓ J hJn hJm hCap1 hReach
  -- The grid of lengths after the update: every new length is on the grid of the format.
  have hLenWithin : IPM.LengthsWithin G F.rangeExponent lVec :=
    fun e he => (hGLRng e (hExtG.symm ▸ he)).2
  have hDyadic : IsDyadicGrid G F.fmt.precision lVec := by
    intro e he
    have heExt : e ∈ model.extG.E := hExtG.symm ▸ he
    by_cases hIns : ∃ u ∈ U, u.Inserts e
    · -- An inserted edge reads its length from `l`.
      have hlEq : lVec e = readVector mem0 l 4 F.limbs F.fmt.precision I.m e := by
        dsimp only [lVec, updateOverlay]; rw [ite_eq_right (fun h => h.2 hIns)]
      have heM : e < I.m := hRep0.2.2.2.2.2.2.1 e heExt
      refine ⟨Num.intVal mem0 (l + e * F.limbs) 4 F.limbs, ?_⟩
      rw [hlEq]; simp [readVector, heM, Num.fixVal]
    · -- An old edge keeps the length of the model, which is on the grid by `DryChainLenGridInv`.
      push Not at hIns
      have hlEq : lVec e = model.extℓ e := (hAgree e heExt hIns).2
      have hL := hFresh.hLeft e heExt
      have hMem0 : model.extToInt e ∈ (model.chain.G 0).E :=
        hFresh.hE ▸ Finset.mem_image_of_mem model.extToInt heExt
      have hℓ0 : model.chain.ℓ (model.extToInt e) = model.extℓ e := by
        rw [hℓOld (model.extToInt e) hMem0, hL]
      obtain ⟨q, hq⟩ := (hGrid0.2.2.1 0 (Nat.zero_le _)).2 (model.extToInt e) hMem0
      exact ⟨q, hq.trans (hℓ0.trans hlEq.symm)⟩
  have hGrid1 := (dryChainLenGridInv_preLoop_of_reached J hJn hJm hCap1 hReach hGrid0
    (hExtG ▸ hRef) hLenWithin hDyadic (fun e he => hAgree e (hExtG.symm ▸ he))).1
  exact dryCoreSel_updateLoopModelInv allocationCoefficient allocationDegree wordExp hSCWordCoeff
    hWordExpLe source J hJn hJm hCap1 hw hFresh hExtG hℓOld hShift0 hShift1 hGrid0 hGrid1 hRef
    (hICap ▸ hnfCap) (fun e he => (hGLRng e he).2) (fun e he hNo => (hAgree e he hNo).2) hRebW

end MinCostFlow.Final.DryRun
