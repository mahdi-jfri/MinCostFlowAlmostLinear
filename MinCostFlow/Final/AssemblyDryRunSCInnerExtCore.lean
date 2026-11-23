module

public import MinCostFlow.Final.AssemblyDryRunSCSelInitTight
public import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
public import MinCostFlow.Final.AssemblyDryRunSCCoreAdapters
public import MinCostFlow.MinRatio.WireChainCoreAlgebra
import MinCostFlow.SparseCore.Program.AssemblyUpdateOutAux
import Mathlib.Tactic

/-!
# The sparse core of the dry run under the loop contract of Branch B (`AssemblyDryRunSCInnerExtCore`)

The loop of Branch B uses four facts on the sparse core at each level `j < d`: the contract
`sparseCoreOrdMachineContractKFRBL` with the re-embedding function `dryReembFn J`, the footprint
of the output of op `0` (`SparseCoreUpdateOutFootAt`), the place of the re-embedding lists
(`SparseCoreReembPlaceAt`), and the readout footprint (`SparseCoreReadoutFootAt`). It also uses
that `T.updateOrd` does not read its length and gradient arguments.

The file `AssemblyDryRunSCCoreKFBL.lean` proves the first three facts in the program
`dryLinkedProgram`. Here we prove them in `dryLinkedProgramSel`, the program of the dry run, by the
same argument: the sparse-core program sits at `lay.scBase` in `dryLinkedProgramSel`
(`dryLinkedProgramSel_sc_hasAt`), and each fact moves along this shift.

* `drySC_coreLoopFacts_sel`: the four facts at `drySCRep`, at every level and every graph `G` with
  `G.n ≤ G.m + 1` and `G.m ≤ I.m`.
* `dryTool_updateOrdEqOnE`: `ToolUpdateOrdEqOnE` for the tool of the dry run (by `rfl` once the
  tool is unfolded to the tool of the program).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private theorem kfrbl_cast_ext {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (reemb : ToolReembFn T₂) (R : DSRep (SparseCoreOrdAbs T₂))
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth T₂ reemb G k M N vCap eCap capExp P alloc)) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth T₁ (h ▸ reemb) G k M N vCap eCap capExp P
        alloc) := by
  subst h; exact himpl

private theorem updateOutFoot_cast_ext {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ} {edMul : ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreUpdateOutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc edMul R p
      op) :
    SparseCoreUpdateOutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc edMul
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

private theorem reembPlace_cast_ext {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hpl : SparseCoreReembPlaceAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReembPlaceAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hpl

/-- The four facts on the sparse core that the loop of Branch B uses, in `dryLinkedProgramSel`, at
the representation `drySCRep`, at every level `i < d` and every graph `G` with `G.n ≤ G.m + 1`
and `G.m ≤ I.m`: the contract `KFRBL` with `dryReembFn J`, `SparseCoreUpdateOutFootAt` with the
multiplier `drySCEdMul`, `SparseCoreReembPlaceAt`, and `SparseCoreReadoutFootAt`. -/
theorem drySC_coreLoopFacts_sel (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) (hGm_le : G.m ≤ (solverConnectedAugmented J).m) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    let R := drySCRep Psc allocationCoefficient allocationDegree source J hw
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    let vCap := (namedInstance I).n
    let eCap := initTargetCap cfg (namedInstance I)
    let PscP := drySCParams Psc dryCapExp limbMul
    let alloc := drySCAlloc Psc dryCapExp limbMul J
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source) p lay.scInit lay.scOp
        (sparseCoreOrdMachineContractKFRBL F.fmt F.limbs (dryDepth J) cfg.T (dryReembFn J) G
          cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp PscP alloc) ∧
      SparseCoreUpdateOutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp PscP alloc
        (drySCEdMul Psc dryCapExp limbMul) R p lay.scOp ∧
      SparseCoreReembPlaceAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp PscP alloc R p lay.scOp ∧
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp PscP alloc R p lay.scOp := by
  intro W I V k F cfg lay limbMul R p vCap eCap PscP alloc
  let M₀ := max I.m (concreteEdgeThresholdWithLast W)
  let depth := Expander.chosenL (M₀ ^ 2)
  have hlim := dry_initTargetCap_le_capLimit J hJn hJm hCapPos
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one cfg.P.hM₀
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap := concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le vCap eCap hlim
  have hInit : ∀ j < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k j :=
    fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : p.HasAt lay.scBase (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    dryLinkedProgramSel_sc_hasAt W Psc.sc inner selInitCode
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 dryCapExp limbMul))).2.2.2
    depth (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCapSpec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx))
    vCap eCap
  have hAll := (Classical.choose_spec hCapSpec).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) rfl hcap hdepth_le (chosenL_sq_le_bundleLogFactor cfg.P.hM₀ le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_k_le_capExp J i)
  have hBoth := drySC_coreKFBL_sel Psc inner selInitCode allocationCoefficient allocationDegree
    source J hJn hJm hCapPos hw i hi G hGn_le hGm_le
  refine ⟨?_, updateOutFoot_cast_ext hT _ (sparseCoreUpdateOutFootAt_shift hHas hAll.2.2.1),
    reembPlace_cast_ext hT _ (sparseCoreReembPlaceAt_shift hHas hAll.2.2.2), hBoth.2⟩
  exact kfrbl_cast_ext hT _ _ (dsRep_implements_shift hHas
    (hAll.1 (drySC_compInitFormatHyp J hJn hJm hCapPos hGm_le)))

/-- `T.updateOrd` of the tool of the dry run does not read its length and gradient arguments. -/
theorem dryTool_updateOrdEqOnE (J : Circulation) :
    ToolUpdateOrdEqOnE (concreteCirculationCfgWithLast dryWitnessUsed J).T :=
  fun _ _ _ _ _ _ _ => rfl

end MinCostFlow.Final.DryRun

end
