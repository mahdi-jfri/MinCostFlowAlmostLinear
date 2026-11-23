module

public import MinCostFlow.Final.AssemblyDryRunSC

/-!
# Handle-in-footprint property of the dry-run sparse-core representation (`AssemblyDryRunSCHandle`)

Proves that every handle `b` lies in its own footprint for the capacity-indexed dry-run
sparse-core representation `drySCRepAt` and its specialized instance `drySCRep`
(`Final/AssemblyDryRunSC.lean`), by transporting the exported `∀ b x, R.foot b x b` clause of
`drySC_bridged_exists` (coming from the header disjunct `[b, b + ASM_HDR_SIZE)` of `asmTopFoot`)
across the tool equality `concreteCirculationCfgWithLast_T_eq_progTool`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut MinCostFlow.Bundle Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private theorem dsRep_foot_self_cast_sc {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    (R : DSRep (SparseCoreOrdAbs T₂)) (hfoot : ∀ b x, R.foot b x b) :
    ∀ b x, (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).foot b x b := by
  subst h; exact hfoot

/-- Every handle `b` unconditionally lies in the footprint of `drySCRepAt`. -/
theorem drySCRepAt_handle_mem_foot_uncond (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree capExp limbMul vCap eCap : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    ∀ (b : ℕ)
      (x : (drySCRepAt Psc allocationCoefficient allocationDegree capExp limbMul vCap eCap
        source J hw).τ),
      (drySCRepAt Psc allocationCoefficient allocationDegree capExp limbMul vCap eCap
        source J hw).foot b x b := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
  let F := ipmQualityMinRatioFormat I.m V k hw
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth
        sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.2.2
    depth w F.fmt F.limbs (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  exact dsRep_foot_self_cast_sc hT _ (Classical.choose_spec hCap).1.2

/-- Every handle `b` unconditionally lies in the footprint of `drySCRep`. -/
theorem drySCRep_handle_mem_foot_uncond (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    ∀ (b : ℕ)
      (x : (drySCRep Psc allocationCoefficient allocationDegree source J hw).τ),
      (drySCRep Psc allocationCoefficient allocationDegree source J hw).foot b x b :=
  drySCRepAt_handle_mem_foot_uncond Psc allocationCoefficient allocationDegree dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) (namedInstance (solverConnectedAugmented J)).n
    (initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J)
      (namedInstance (solverConnectedAugmented J))) source J hw

/-- For every represented state of `drySCRep`, its handle `b` lies in its footprint. -/
theorem drySCRep_handle_mem_foot (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    ∀ (b : ℕ)
      (s : SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)
      (x : (drySCRep Psc allocationCoefficient allocationDegree source J hw).τ)
      (mem : ℕ → ℕ),
      (drySCRep Psc allocationCoefficient allocationDegree source J hw).rep b s x mem →
      (drySCRep Psc allocationCoefficient allocationDegree source J hw).foot b x b :=
  fun b _ x _ _ =>
    drySCRep_handle_mem_foot_uncond Psc allocationCoefficient allocationDegree source J hw b x

end MinCostFlow.Final.DryRun

end
