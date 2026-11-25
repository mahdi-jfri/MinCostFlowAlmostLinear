module

public import MinCostFlow.Final.AssemblyDryRunSCOpen
public import MinCostFlow.Final.AssemblyDryRunSCBranch
public import MinCostFlow.MinRatio.WireCoreForestCapKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreReembPlaceKFBL
import MinCostFlow.SparseCore.Program.AssemblyUpdateOutAux
import Mathlib.Tactic

/-!
# The sparse-core levels of the initial chain under the layout contract (`AssemblyDryRunSCCoreKFBL`)

The Init of the solver needs the sparse-core contract `sparseCoreOrdMachineContractKFBL` with the
depth `dryDepth J` and `SparseCoreReadoutFootAt` at every level of the initial chain
(`DrySCInitBridgeHyps.hCoreImplKFBL`, `Final/AssemblyDryRunSC.lean`). The representation is
`drySCRep`, which is `drySCRepAt … n m` at the caps `(n, m)` of the input graph.

This file proves that hypothesis, and states the dry run without it.
* `drySC_coreKFBL_level`: for every level `i < cfg.P.d`, every graph with `n ≤ m + 1` and every
  cap pair below `dryCapLimit`, `drySCRepAt … vc ec` meets `KFBL` and `SparseCoreReadoutFootAt`
  (from `drySCRepAt_implements_level` and `drySCRepAt_readoutFoot_level`).
* `drySC_hCoreImplKFBL_proved`: the same at the level graphs of the initial chain, for every input
  whose lengths lie in the range of the format. These graphs have `n ≤ m + 1`
  (`drySolver_init_level_n_le_m_add_one`).
* `DrySCInitOpenHyps.toBridgeHyps` and `theorem_1_1_dry_run_sc_open`: the dry run with the
  Init hypotheses `DrySCInitOpenHyps` (`Final/AssemblyDryRunSCOpen.lean`). The field
  `hCoreImplKFBL` is `drySC_hCoreImplKFBL_proved` at the caps `(n, m)`, which fit under the cap
  limit (`dry_inputCaps_le_capLimit`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## `KFRBL` (`progReemb`) and `SparseCoreUpdateOutFootAt` extraction for the dry run -/

/-- Input-independent edit-word multiplier `edMul` for `SparseCoreUpdateOutFootAt` extracted
from `drySC_bridged_exists Psc` at `(capExp, limbMul)`. -/
def drySCEdMul (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.2.2

/-- The concrete re-embedded-edge function `progReemb` transported along
`concreteCirculationCfgWithLast_T_eq_progTool` to `cfg.T`. -/
def drySCReemb (allocationCoefficient allocationDegree : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    ToolReembFn (concreteCirculationCfgWithLast dryWitnessUsed J).T :=
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth
        sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  hT ▸ progReemb (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth sparsifyImplUsed

private theorem dsRep_implements_kfrbl_cast_sc {w L depth capExp : ℕ} {fmt : Num.Format w}
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

private theorem updateOutFoot_cast_sc {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ} {edMul : ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreUpdateOutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc edMul R p
      op) :
    SparseCoreUpdateOutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc edMul
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

private theorem reembPlace_cast_sc {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hpl : SparseCoreReembPlaceAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReembPlaceAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hpl

/-- Per-level `KFRBL` `Implements` (with `drySCReemb`) in `dryLinkedProgram`, using the exact same
representation `drySCRepAt` as `drySCRepAt_implements_level`. -/
theorem drySCRepAt_implements_kfrbl_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
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
    (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw).Implements
      (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFRBL F.fmt F.limbs (dryDepth J) cfg.T
        (drySCReemb allocationCoefficient allocationDegree source J hw) G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) := by
  intro W I V k F cfg lay limbMul
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let depth := Expander.chosenL (M₀ ^ 2)
  have hM₀_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one hM₀_pos
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap : SparseCoreCapHyp dryCapExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap :=
    concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le vCap eCap hlim
  have hfmt : F.fmt.limbBits = 4 := rfl
  have hInit : ∀ j < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k j :=
    fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : (dryLinkedProgram W Psc.sc inner).HasAt lay.scBase
      (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    solverCycle_sparseCore_hasAt threshold A _ lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc inner _
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 dryCapExp limbMul))).2.2.2
    depth (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  have himpl0 := ((Classical.choose_spec hCap).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) hfmt hcap hdepth_le (chosenL_sq_le_bundleLogFactor hM₀_pos le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_k_le_capExp J i)).1 (drySC_compInitFormatHyp J hJn hJm hCapPos hGm_le)
  exact dsRep_implements_kfrbl_cast_sc hT _ _ (dsRep_implements_shift hHas himpl0)

/-- Per-level `SparseCoreUpdateOutFootAt` in `dryLinkedProgram` with input-independent multiplier
`drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)`. -/
theorem drySCRepAt_updateOutFoot_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    SparseCoreUpdateOutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCEdMul Psc dryCapExp limbMul)
      (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scOp := by
  intro W I V k F cfg lay limbMul
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let depth := Expander.chosenL (M₀ ^ 2)
  have hM₀_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one hM₀_pos
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap : SparseCoreCapHyp dryCapExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap :=
    concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le vCap eCap hlim
  have hfmt : F.fmt.limbBits = 4 := rfl
  have hInit : ∀ j < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k j :=
    fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : (dryLinkedProgram W Psc.sc inner).HasAt lay.scBase
      (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    solverCycle_sparseCore_hasAt threshold A _ lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc inner _
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 dryCapExp limbMul))).2.2.2
    depth (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  have hfoot0 := ((Classical.choose_spec hCap).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) hfmt hcap hdepth_le (chosenL_sq_le_bundleLogFactor hM₀_pos le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_k_le_capExp J i)).2.2.1
  exact updateOutFoot_cast_sc hT _ (sparseCoreUpdateOutFootAt_shift hHas hfoot0)

/-- Per-level `SparseCoreReembPlaceAt` in `dryLinkedProgram`: every branch's re-embedding list
emitted by op `0` lies inside `[heap, o.value)`. -/
theorem drySCRepAt_reembPlace_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    SparseCoreReembPlaceAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scOp := by
  intro W I V k F cfg lay limbMul
  let threshold := concreteEdgeThresholdWithLast W
  let M₀ := max I.m threshold
  let depth := Expander.chosenL (M₀ ^ 2)
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one cfg.P.hM₀
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap := concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le vCap eCap hlim
  have hInit : ∀ j < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k j :=
    fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj
  have hT := concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : (dryLinkedProgram W Psc.sc inner).HasAt lay.scBase
      (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    solverCycle_sparseCore_hasAt threshold (concreteQualityBudgetWithLast W) _ lastGuest
      ⌈max 1 lastCanonConst⌉₊ lastWordConst Psc.sc inner _
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 dryCapExp limbMul))).2.2.2
    depth (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  have hpl0 := ((Classical.choose_spec hCap).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) rfl hcap hdepth_le (chosenL_sq_le_bundleLogFactor cfg.P.hM₀ le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_k_le_capExp J i)).2.2.2
  exact reembPlace_cast_sc hT _ (sparseCoreReembPlaceAt_shift hHas hpl0)

/-- The `KFRBL` form of the sparse-core contract at one level of the dry run: `drySCRepAt` meets
`sparseCoreOrdMachineContractKFRBL` with `drySCReemb` and `SparseCoreReadoutFootAt`. -/
theorem drySC_coreKFRBL_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
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
    let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap
      source J hw
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source)
        (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
        (sparseCoreOrdMachineContractKFRBL F.fmt F.limbs (dryDepth J) cfg.T
          (drySCReemb allocationCoefficient allocationDegree source J hw) G cfg.P.k
          (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
          (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R
        (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  ⟨drySCRepAt_implements_kfrbl_level Psc inner allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le hGm_le,
    drySCRepAt_readoutFoot_level Psc inner allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le⟩

/-- Alias of `drySCRepAt_updateOutFoot_level` mirroring `drySC_coreKFRBL_level`. -/
theorem drySC_updateOutFoot_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap
      source J hw
    SparseCoreUpdateOutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCEdMul Psc dryCapExp limbMul) R (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  drySCRepAt_updateOutFoot_level Psc inner allocationCoefficient allocationDegree source J
    hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le

/-- The `KFBL` form of the sparse-core contract at one level of the dry run: for every level
`i < cfg.P.d`, every graph `G` with `G.n ≤ G.m + 1` and every cap pair with
`vCap + eCap + 2 ≤ dryCapLimit`, the representation `drySCRepAt … vCap eCap` meets
`sparseCoreOrdMachineContractKFBL` with the depth `dryDepth J`, and `SparseCoreReadoutFootAt`. -/
theorem drySC_coreKFBL_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
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
    let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap
      source J hw
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source)
        (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
        (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
          (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
          (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R
        (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  ⟨drySCRepAt_implements_level Psc inner allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le hGm_le,
    drySCRepAt_readoutFoot_level Psc inner allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le⟩

/-- Immediate corollary of `drySC_coreKFBL_level`: op `2`'s forest satisfies `SparseCoreForestCapAt`
with `fcap = dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)`. -/
theorem drySC_forestCap_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap
      source J hw
    SparseCoreForestCapAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) R
      (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  ⟨(drySCRepAt_readoutFoot_level Psc inner allocationCoefficient allocationDegree source J
      hJn hJm hCapPos hw i hi vCap eCap hlim G hGn_le).op2_runs⟩

/-- The `KFRBL` sparse-core contract at Init: for every dry-run input and every input lengths `ℓ₀`
in the range of the format, at every level `i < cfg.P.d` of the initial chain and every cap pair
with `vc + ec + 2 ≤ dryCapLimit`, the representation `drySCRepAt … vc ec` meets
`sparseCoreOrdMachineContractKFRBL` with `drySCReemb` and `SparseCoreReadoutFootAt`. -/
theorem drySC_hCoreImplKFRBL_proved (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
      let lay := dryTailLay Psc.sc openInner.toInnerCode
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vc ec
            source J hw
          R.Implements w p lay.scInit lay.scOp
              (sparseCoreOrdMachineContractKFRBL F.fmt F.limbs (dryDepth J) cfg.T
                (drySCReemb allocationCoefficient allocationDegree source J hw) (chain.G i)
                cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ vc ec dryCapExp
                (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
            SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T (chain.G i) cfg.P.k
              (levelM cfg.TP cfg.P i) cfg.N₀ vc ec dryCapExp
              (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R p
              lay.scOp := by
  intro source J hJn hJm hCost hCap hw I V k F cfg G w p lay limbMul ℓ₀ g₀ hLen chain i hi vc ec
    hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  have hnm : (chain.G i).n ≤ (chain.G i).m + 1 :=
    (drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le).2
  have hmle : (chain.G i).m ≤ I.m :=
    drySolver_init_level_m_le J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le
  exact drySC_coreKFRBL_level Psc openInner.toInnerCode allocationCoefficient allocationDegree
    source J hJn hJm hCap1 hw i hi vc ec hcap (chain.G i) hnm hmle

/-- `SparseCoreUpdateOutFootAt` on the level graphs of the initial chain at Init, with
input-independent multiplier `drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)`. -/
theorem drySC_hCoreUpdateOutFoot_proved (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
      let lay := dryTailLay Psc.sc openInner.toInnerCode
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vc ec
            source J hw
          SparseCoreUpdateOutFootAt F.fmt F.limbs (dryDepth J) cfg.T (chain.G i) cfg.P.k
            (levelM cfg.TP cfg.P i) cfg.N₀ vc ec dryCapExp
            (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
            (drySCEdMul Psc dryCapExp limbMul) R p lay.scOp := by
  intro source J hJn hJm hCost hCap hw I V k F cfg G p lay limbMul ℓ₀ g₀ hLen chain i hi vc ec
    hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  have hnm : (chain.G i).n ≤ (chain.G i).m + 1 :=
    (drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le).2
  exact drySC_updateOutFoot_level Psc openInner.toInnerCode allocationCoefficient allocationDegree
    source J hJn hJm hCap1 hw i hi vc ec hcap (chain.G i) hnm

/-- The sparse-core contract at Init (`hCoreImplKFBL`), derived as a corollary of
`drySC_hCoreImplKFRBL_proved` via `dsRep_implements_kfbl_of_kfrbl`. -/
theorem drySC_hCoreImplKFBL_proved (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
      let lay := dryTailLay Psc.sc openInner.toInnerCode
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          let R := drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vc ec
            source J hw
          R.Implements w p lay.scInit lay.scOp
              (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (dryDepth J) cfg.T (chain.G i)
                cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ vc ec dryCapExp
                (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
            SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T (chain.G i) cfg.P.k
              (levelM cfg.TP cfg.P i) cfg.N₀ vc ec dryCapExp
              (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R p
              lay.scOp := fun source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen i hi vc ec hcap =>
  let ⟨h1, h2⟩ := drySC_hCoreImplKFRBL_proved Psc openInner allocationCoefficient allocationDegree
    source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen i hi vc ec hcap
  ⟨dsRep_implements_kfbl_of_kfrbl h1, h2⟩

/-- The full Init bridge hypotheses from `DrySCInitOpenHyps`, with `hParam`, `hCoreImplKFBL`,
`hCoreLenFits`, `hLastStretchFits`, `hLastImpl` (with the allocation bound
`drySC_lastAllocLe_proved`) and `hLastSpaceLe` proved. -/
def DrySCInitOpenHyps.toBridgeHyps {Psc : DrySparseCorePieces} {rem : SolverInnerOpenNoParam}
    {B : OrdSolverInnerBounds} {hB : InnerBoundsHyp B}
    {sz : Circulation → Circulation → WiredInnerSizes}
    (H : DrySCInitOpenHyps Psc rem B hB sz) :
    DrySCInitBridgeHyps Psc rem.toSolverInnerOpen B hB sz where
  paramSpace := dryParamSpace
  paramCost := dryParamCost
  lastMult := fun _ J => dryLastMult J
  stretchP := fun _ J => dryLastStretchP J
  lastSpace := fun _ J => dryLastSpace J
  coreInitSpace := H.coreInitSpace
  lastAlloc := fun _ J _ _ => dryLastSpace J
  hParam := dryParamSetup_discharges_hParam Psc rem.toSolverInnerOpen B hB
    (SolverInnerOpenNoParam.dryParamProcs_hasAt Psc rem)
  hCoreImplKFBL := fun source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen i hi =>
    drySC_hCoreImplKFBL_proved Psc rem.toSolverInnerOpen _ _ source J hJn hJm hCost hCap hw
      ℓ₀ g₀ hLen i hi _ _ (dry_initTargetCap_le_capLimit J hJn hJm fun e => (hCap e).1)
  hLastImpl := drySC_hLastImpl_proved Psc rem.toSolverInnerOpen _ _ (fun _ J => dryLastSpace J)
    (drySC_lastAllocLe_proved _ _)
  hLastSpaceLe := fun _ _ _ => le_rfl
  hInitSpaceLe := H.hInitSpaceLe
  hCoreLenFits := drySC_hCoreLenFits_onGrid _ _
  hLastStretchFits := drySC_hLastStretchFits_Im _ _
  hSpaceLe := H.hSpaceLe
  hFixedLe := H.hFixedLe
  hMulLe := H.hMulLe

theorem drySCRep_local (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    (drySCRep Psc allocationCoefficient allocationDegree source J hw).Local :=
  drySCRepAt_local Psc allocationCoefficient allocationDegree dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) _ _ source J hw

/-- `drySCRep` satisfies `UpdateCoreCoreKFRBL` with `drySCReemb` at
`(vCap, eCap) = ((namedInstance I).n, initTargetCap cfg (namedInstance I))`. -/
theorem drySC_coreKFRBL (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
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
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    UpdateCoreCoreKFRBL F.fmt F.limbs I.m (namedInstance I).n (initTargetCap cfg (namedInstance I))
      dryCapExp cfg (drySCReemb allocationCoefficient allocationDegree source J hw)
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCRep Psc allocationCoefficient allocationDegree source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp :=
  fun i hi G hGn_le hGm_le =>
    drySC_coreKFRBL_level Psc inner allocationCoefficient allocationDegree source J hJn hJm hCapPos
      hw i hi (namedInstance (solverConnectedAugmented J)).n
      (initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J)
        (namedInstance (solverConnectedAugmented J)))
      (dry_initTargetCap_le_capLimit J hJn hJm hCapPos) G hGn_le hGm_le

/-- `drySCRep` satisfies `UpdateCoreOp0FootKFBL` with input-independent multiplier
`drySCEdMul Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)` at
`(vCap, eCap) = ((namedInstance I).n, initTargetCap cfg (namedInstance I))`. -/
theorem drySC_updateOutFoot (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
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
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    UpdateCoreOp0FootKFBL F.fmt F.limbs (namedInstance I).n (initTargetCap cfg (namedInstance I))
      dryCapExp cfg (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCEdMul Psc dryCapExp limbMul)
      (drySCRep Psc allocationCoefficient allocationDegree source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  fun i hi G hGn_le =>
    drySC_updateOutFoot_level Psc inner allocationCoefficient allocationDegree source J hJn hJm
      hCapPos hw i hi (namedInstance (solverConnectedAugmented J)).n
      (initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J)
        (namedInstance (solverConnectedAugmented J)))
      (dry_initTargetCap_le_capLimit J hJn hJm hCapPos) G hGn_le

/-- `drySCRep` satisfies `UpdateCoreReembPlaceKFBL` at
`(vCap, eCap) = ((namedInstance I).n, initTargetCap cfg (namedInstance I))`. -/
theorem drySC_reembPlace (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
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
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    UpdateCoreReembPlaceKFBL F.fmt F.limbs (namedInstance I).n (initTargetCap cfg (namedInstance I))
      dryCapExp cfg (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCRep Psc allocationCoefficient allocationDegree source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  fun i hi G hGn_le =>
    drySCRepAt_reembPlace_level Psc inner allocationCoefficient allocationDegree source J hJn hJm
      hCapPos hw i hi (namedInstance (solverConnectedAugmented J)).n
      (initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J)
        (namedInstance (solverConnectedAugmented J)))
      (dry_initTargetCap_le_capLimit J hJn hJm hCapPos) G hGn_le

/-- `drySCRep` meets `sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt` at
every level `i < cfg.P.d` and every graph `G` with `G.n ≤ G.m + 1`, with
`(vCap, eCap) = ((namedInstance I).n, initTargetCap cfg (namedInstance I))`. -/
theorem drySC_coreKFBL (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) (hGm : G.m ≤ (solverConnectedAugmented J).m) :
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
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source)
        (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
        (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
          (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
          (initTargetCap cfg (namedInstance I)) dryCapExp
          (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
        (initTargetCap cfg (namedInstance I)) dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R
        (dryLinkedProgram W Psc.sc inner) lay.scOp :=
  (drySC_coreKFRBL Psc inner allocationCoefficient allocationDegree source J hJn hJm hCapPos
    hw).toKFBL i hi G hGn_le hGm

end MinCostFlow.Final.DryRun

end
