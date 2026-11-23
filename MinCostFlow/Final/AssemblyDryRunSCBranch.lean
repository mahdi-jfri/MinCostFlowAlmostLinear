module

public import MinCostFlow.Final.AssemblyDryRunSC
import MinCostFlow.Final.AssemblyDryRunSCFitsCycle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Dry-run depth facts and per-depth branch instantiation (`AssemblyDryRunSCBranch`)

Complements `Final/AssemblyDryRunSC.lean` (whose `DrySparseCorePieces.hBR` directly takes
`ScBranchPiecesHyp` — fixed depth-free `HasAsmBrProcs` and per-depth `AsmBrPieces` — bridged into
`ScBranchModuleHyp` via `scBranchModuleHyp_of_pieces`, `asmBranchAt_value`, and
`asmBranchAt_value_readoutLayout`):

1. **Dry-run balancing depth (`dryDepth`, `dryDepth_unbounded`, `dry_hasAsmBrProcs_inhabited`):**
   `dryDepth J = Expander.chosenL (max (solverConnectedAugmented J).m threshold ^ 2)` is unbounded
   across valid dry-run circulations `J`, and because `HasAsmBrProcs` does not mention `depth`,
   a single finite program satisfies `HasAsmBrProcs` uniformly across all inputs `J`.
2. **Per-depth dry-run bridge directly from `AsmBrPieces` (`DrySparseCoreBranchAtDepth`,
   `drySCBranchWordExp_le_39`, `drySCRepAt_branch`, `drySCRepAt_branch_local`,
   `drySCRepAt_implements_level_of_branchValue`):**
   Explicit fixed-depth specialization at `depth = dryDepth J`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.Bundle Chain IPM IPM.Machine SparseCore SparseCore.Program
  Scaling Scaling.Machine MinRatio DynSpanner.Program

/-! ## Dry-run balancing depth and uniform `HasAsmBrProcs` -/

/-- The sparse-core balancing depth used by the second dry run on circulation `J`. -/
def dryDepth (J : Circulation) : ℕ :=
  Expander.chosenL (max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)

/-- `dryDepth J` is unbounded over valid dry-run circulations `J` (witnessed by `cycleCirculation`). -/
theorem dryDepth_unbounded (D : ℕ) :
    ∃ J : Circulation,
      J.n ≤ 2 * J.m + 1 ∧ 0 < J.m ∧ J.CostsBounded (J.m ^ 10) ∧
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) ∧
      D ≤ dryDepth J := by
  let N : ℕ := max 3 (Nat.ceil (Real.exp ((D : ℝ) ^ (24 : ℕ))))
  have hN3 : 3 ≤ N := le_max_left _ _
  let J := cycleCirculation N hN3
  obtain ⟨hJn, hJm, hCost, hCap⟩ := cycleCirculation_hyps hN3
  have hIm : N ≤ (solverConnectedAugmented J).m := (cycleCirculation_augmented_edges hN3).1
  refine ⟨J, hJn, hJm, hCost, hCap, ?_⟩
  have hM₀ : N ≤ max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) :=
    hIm.trans (le_max_left _ _)
  have hSq : N ≤ max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 := by
    calc N ≤ N * N := Nat.le_mul_self N
      _ = N ^ 2 := (sq N).symm
      _ ≤ max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 :=
          Nat.pow_le_pow_left hM₀ 2
  have hexp_le : Real.exp ((D : ℝ) ^ (24 : ℕ)) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 3 _))
  have hexp_lt : Real.exp ((D : ℝ) ^ (24 : ℕ)) <
      ((max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) + 2 := by
    have hSqR : (N : ℝ) ≤ ((max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hSq
    linarith
  have hlog_ge : (D : ℝ) ^ (24 : ℕ) ≤
      Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) + 2) := by
    have := Real.log_le_log (Real.exp_pos _) hexp_lt.le
    rwa [Real.log_exp] at this
  have hD_nn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hrpow : (D : ℝ) ≤
      Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) + 2) ^
        (1 / 24 : ℝ) := by
    calc (D : ℝ) = ((D : ℝ) ^ (24 : ℝ)) ^ (1 / 24 : ℝ) := by
            rw [← Real.rpow_mul hD_nn]; norm_num
      _ = ((D : ℝ) ^ (24 : ℕ)) ^ (1 / 24 : ℝ) := by
            rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2 : ℕ) : ℝ) + 2) ^
            (1 / 24 : ℝ) := Real.rpow_le_rpow (by positivity) hlog_ge (by norm_num)
  have hlow := Expander.chosenL_lower
    (max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
  have hDR : (D : ℝ) ≤ (dryDepth J : ℝ) := hrpow.trans hlow
  exact_mod_cast hDR

/-- A single finite program satisfies `HasAsmBrProcs` on `sparsifyImplUsed` (depth-free, serving
every `dryDepth J` across all dry-run inputs `J`). -/
theorem dry_hasAsmBrProcs_inhabited (fCFRoot : ℕ) :
    ∃ (p : Program) (bp : AsmBranchProcs) (I : AsmBrProcIdx),
      HasAsmBrProcs p bp sparsifyImplUsed fCFRoot I :=
  hasAsmBrProcs_inhabited sparsifyImplUsed fCFRoot

/-! ## Per-depth dry-run bridge directly from `AsmBrPieces` and `asmBranchAt_value` -/

/-- Concrete sparse-core pieces at a fixed balancing depth `depth`, packaging `ScBranchValueAtDepth`. -/
structure DrySparseCoreBranchAtDepth (depth : ℕ) where
  sc : SparseCoreCode
  hsc : sc.prog.IsDeterministic
  b : ℕ
  fCFInit : ℕ
  fCFBatch : ℕ
  fCFExport : ℕ
  fCFRoot : ℕ
  bp : AsmBranchProcs
  hp : HasAsmTopProcs sc.prog b fCFInit fCFBatch fCFExport bp
  hinit : sc.init = asmTopInitIdx b
  hop : sc.op = asmTopOpIdx b
  CFS : AsmCompFamilySpec
  hCF : ScCompFamilyHyp CFS dryLSFInitUsed sc.prog fCFInit fCFBatch fCFExport fCFRoot
  brVal : ScBranchValueAtDepth CFS dryLSFInitUsed sparsifyImplUsed depth
    sc.prog fCFInit fCFBatch fCFRoot bp

/-- Concrete `AsmBranchSpec` of `Psc` at `depth`. -/
def DrySparseCoreBranchAtDepth.brSpec {depth : ℕ} (Psc : DrySparseCoreBranchAtDepth depth) :
    AsmBranchSpec :=
  Psc.brVal.spec sparsifyPolyStretch_sparsifyImplUsed

/-- Word-size exponent of `Psc : DrySparseCoreBranchAtDepth depth` at `capExp`. -/
def drySCBranchWordExp {depth : ℕ} (Psc : DrySparseCoreBranchAtDepth depth) (capExp : ℕ) : ℕ :=
  asmTopWordExp Psc.CFS Psc.brSpec capExp

theorem drySCBranchWordExp_le_39 {depth : ℕ} (hdepth : 1 ≤ depth)
    (Psc : DrySparseCoreBranchAtDepth depth) :
    drySCBranchWordExp Psc dryCapExp ≤ 39 :=
  (asmTop_bridged_at_depth_of_branchValue (C_lsst := dryCLsstUsed) hdepth Psc.hp
    sparsifyPolyStretch_sparsifyImplUsed sparsifyImplUsed_γ_t Psc.hCF Psc.brVal).1

/-- Parameters extracted directly from `asmTopParams` and `Psc.brSpec`. -/
def drySCBranchParams {depth : ℕ} (Psc : DrySparseCoreBranchAtDepth depth) (capExp limbMul : ℕ) :
    SparseCoreOrdParams :=
  asmTopParams Psc.CFS Psc.brSpec capExp limbMul

/-- Allocation function extracted directly from `asmTopAlloc` and `Psc.brSpec`, parameterized by
logical `sizeParam`. -/
def drySCBranchAlloc {depth : ℕ} (Psc : DrySparseCoreBranchAtDepth depth) (capExp sizeParam : ℕ) :
    ℕ → List ℕ → ℕ :=
  asmTopAlloc Psc.CFS Psc.brSpec capExp sizeParam

private theorem dsRep_local_cast_branch {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    (R : DSRep (SparseCoreOrdAbs T₂)) (hloc : R.Local) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Local := by
  subst h; exact hloc

private theorem dsRep_implements_cast_branch {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₂ G k M N vCap eCap capExp P alloc)) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₁ G k M N vCap eCap capExp P alloc) := by
  subst h; exact himpl

private theorem readoutFoot_cast_branch {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreReadoutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReadoutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

/-- Capacity-indexed concrete `DSRep` extracted directly from `asmBranchAt_value` and `AsmBrPieces`
for circulation `J` (at `depth = dryDepth J`) and `(vCap, eCap)`. -/
def drySCRepAt_branch {allocationCoefficient allocationDegree capExp limbMul vCap eCap : ℕ}
    {source J : Circulation}
    (Psc : DrySparseCoreBranchAtDepth (dryDepth J))
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T) :=
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
  let F := ipmQualityMinRatioFormat I.m V k hw
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed (dryDepth J)
        sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hEx := ((asmTop_bridged_at_depth_of_branchValue (C_lsst := dryCLsstUsed)
    (Expander.one_le_chosenL _) Psc.hp sparsifyPolyStretch_sparsifyImplUsed
    sparsifyImplUsed_γ_t Psc.hCF Psc.brVal).2 capExp limbMul).2 w F.fmt F.limbs
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  let τ := Classical.choose hEx
  let phi := Classical.choose (Classical.choose_spec hEx)
  let foot := Classical.choose (Classical.choose_spec (Classical.choose_spec hEx))
  let hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  let rep := Classical.choose hCap
  hT ▸ (⟨τ, rep, phi, foot⟩ : DSRep (SparseCoreOrdAbs
    (sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed (dryDepth J)
      sparsifyImplUsed)))

/-- Locality of `drySCRepAt_branch`. -/
theorem drySCRepAt_branch_local {allocationCoefficient allocationDegree capExp limbMul vCap eCap : ℕ}
    {source J : Circulation} (Psc : DrySparseCoreBranchAtDepth (dryDepth J))
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    (drySCRepAt_branch (allocationCoefficient := allocationCoefficient)
      (allocationDegree := allocationDegree) (capExp := capExp) (limbMul := limbMul)
      (vCap := vCap) (eCap := eCap) (source := source) Psc hw).Local := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
  let F := ipmQualityMinRatioFormat I.m V k hw
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed (dryDepth J)
        sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hEx := ((asmTop_bridged_at_depth_of_branchValue (C_lsst := dryCLsstUsed)
    (Expander.one_le_chosenL _) Psc.hp sparsifyPolyStretch_sparsifyImplUsed
    sparsifyImplUsed_γ_t Psc.hCF Psc.brVal).2 capExp limbMul).2 w F.fmt F.limbs
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  exact dsRep_local_cast_branch hT _ (Classical.choose_spec hCap).1

/-- Per-level `Implements … KFBL` and `SparseCoreReadoutFootAt` in `dryLinkedProgram`, built
directly from `asmBranchAt_value`, `asmBranchAt_value_readoutLayout`, and `AsmBrPieces` (no
`ScBranchModuleHyp`, no readout-layout hypothesis). -/
theorem drySCRepAt_implements_level_of_branchValue
    {allocationCoefficient allocationDegree : ℕ} {source J : Circulation}
    (Psc : DrySparseCoreBranchAtDepth (dryDepth J)) (inner : SolverInnerCode)
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
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    let R := drySCRepAt_branch (allocationCoefficient := allocationCoefficient)
      (allocationDegree := allocationDegree) (capExp := dryCapExp) (limbMul := limbMul)
      (vCap := vCap) (eCap := eCap) (source := source) Psc hw
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCBranchParams Psc dryCapExp limbMul) (drySCBranchAlloc Psc dryCapExp (drySCSizeParam J))) ∧
    SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCBranchParams Psc dryCapExp limbMul) (drySCBranchAlloc Psc dryCapExp (drySCSizeParam J))
      R (dryLinkedProgram W Psc.sc inner) lay.scOp := by
  intro W I V k F cfg lay limbMul R
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  have hM₀_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hdepth_le : dryDepth J ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : dryDepth J ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one hM₀_pos
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
      dryCLsstUsed (dryDepth J) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : (dryLinkedProgram W Psc.sc inner).HasAt lay.scBase
      (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    solverCycle_sparseCore_hasAt threshold A _ lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc inner _
  have hEx := ((asmTop_bridged_at_depth_of_branchValue (C_lsst := dryCLsstUsed)
    (Expander.one_le_chosenL _) Psc.hp sparsifyPolyStretch_sparsifyImplUsed
    sparsifyImplUsed_γ_t Psc.hCF Psc.brVal).2 dryCapExp limbMul).2
    (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  obtain ⟨himpl0, hfoot0⟩ := (Classical.choose_spec hCap).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) hfmt hcap hdepth_le (chosenL_sq_le_bundleLogFactor hM₀_pos le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_compInitFormatHyp J hJn hJm hCapPos hGm_le) (drySC_k_le_capExp J i)
  have hInitEq : lay.scInit = lay.scBase + asmTopInitIdx Psc.b := by
    change lay.scBase + Psc.sc.init = _; rw [Psc.hinit]
  have hOpEq : lay.scOp = fun j => lay.scBase + asmTopOpIdx Psc.b j := by
    funext j; change lay.scBase + Psc.sc.op j = _; rw [Psc.hop]
  rw [hInitEq, hOpEq]
  exact ⟨dsRep_implements_cast_branch hT _ (dsRep_implements_shift hHas himpl0),
    readoutFoot_cast_branch hT _ (sparseCoreReadoutFootAt_shift hHas hfoot0)⟩

end MinCostFlow.Final.DryRun

end
