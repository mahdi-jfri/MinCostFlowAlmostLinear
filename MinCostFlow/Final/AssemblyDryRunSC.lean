module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.Final.AssemblyDryRunSCStretch
public import MinCostFlow.Final.AssemblyDryRunSCInit
public import MinCostFlow.Final.AssemblyDryRunSCCode
public import MinCostFlow.Final.AssemblyDryRunSCFormat
public import MinCostFlow.Final.AssemblyDryRunSCFitsBounds
public import MinCostFlow.Final.AssemblyDryRunSCDeepInv
public import MinCostFlow.Final.AssemblyDryRunSCSizeParam
public import MinCostFlow.SparseCore.Program.AssemblyBridgeBranch

/-!
# Second dry run of Theorem 1.1 routed through the sparse-core top-layer bridge (`AssemblyDryRunSC`)

Replaces the opaque `hSC : SparseCoreOrdProgramUniform` and `hWordExp : wordExp ≤ 39` hypotheses
of `Final/AssemblyDryRun.lean` with the concrete top-layer assembly (`AssemblyTop.lean` and
`AssemblyBridge.lean`) parameterized by `DrySparseCorePieces`, discharging `SparsifyPolyStretch`,
`γ_t = 1`, `drySCWordExp Psc 3 ≤ 39`, per-level `Implements`/`SparseCoreReadoutFootAt`,
`DrySparseCoreCapLevels`, `drySCWordBound_proved`, and `theorem_1_1_dry_run_sc`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut MinCostFlow.Bundle Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## Sparse-core piece hypotheses -/

/-- The piece hypotheses needed to instantiate the top-layer sparse-core bridge
`drySparseCoreCode_uniform_bridged_with_wordExp` on `dryCLsstUsed`, `dryLSFInitUsed`, and
`sparsifyImplUsed`: P4's deterministic code `cf : ScCompCode` and standalone specification
`ScCompFamilyHyp` on `⟨cf.procs⟩`, the deterministic first-phase sub-modules
`firstStep firstInit : ScSubCode`, and the branch's semantic pieces `ScBranchPiecesCodeHyp`
(with `sc`, `IsDeterministic`, `HasAsmTopProcs`, `I`, `HasAsmBrProcs`, and all concrete P2/P5/P6/P7/P10
procedure placements discharged automatically by `drySparseCoreCode`). -/
structure DrySparseCorePieces where
  cf : ScCompCode
  firstStep : ScSubCode
  firstInit : ScSubCode
  CFS : AsmCompFamilySpec
  hCF : ScCompFamilyHyp CFS dryLSFInitUsed ⟨cf.procs⟩ cf.fInit cf.fBatch cf.fExport cf.fRoot
  hBR : ScBranchPiecesCodeHyp CFS dryLSFInitUsed sparsifyImplUsed cf firstStep firstInit

/-- The single combined deterministic sparse-core program of `Psc`, built by `drySparseCoreCode`. -/
def DrySparseCorePieces.sc (Psc : DrySparseCorePieces) : SparseCoreCode :=
  drySparseCoreCode Psc.cf Psc.firstStep Psc.firstInit

/-- Automatic determinism of `Psc.sc.prog`. -/
theorem DrySparseCorePieces.hsc (Psc : DrySparseCorePieces) :
    Psc.sc.prog.IsDeterministic :=
  drySparseCoreCode_isDeterministic Psc.cf Psc.firstStep Psc.firstInit

/-! ## Bridged sparse-core witness extraction -/

theorem drySC_bridged_exists (Psc : DrySparseCorePieces) :
    ∃ wordExp : ℕ → ℕ, wordExp 3 ≤ 39 ∧
      ∀ capExp limbMul : ℕ, ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
        P.wordExp = wordExp capExp ∧ (∀ sizeParam, SparseCoreInitAllocBound (allocation sizeParam)) ∧
        SparseCoreUpdateRestartAllocBound allocation ∧ ∃ edMul : ℕ,
        ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ), 1 ≤ depth → fmt.precision ≤ 4 * L →
          ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
            ∀ (vCap eCap : ℕ),
              let T := sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth sparsifyImplUsed
              ∃ rep : ℕ → SparseCoreOrdAbs T → τ → (ℕ → ℕ) → Prop,
                let R : DSRep (SparseCoreOrdAbs T) := ⟨τ, rep, phi, foot⟩
                (R.Local ∧ ∀ b x, R.foot b x b) ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                  fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                  depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                  depth ≤ Expander.chosenL ((M + N) ^ 2) → M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                  (∀ j < k, IsValidLSFInitFor (dryLSFInitUsed L fmt.precision) dryCLsstUsed k j) →
                  G.n ≤ G.m + 1 → k ≤ (M + N + 2) ^ capExp →
                  (CompInitFormatHyp L fmt.precision k G.m →
                    R.Implements w Psc.sc.prog Psc.sc.init Psc.sc.op
                      (sparseCoreOrdMachineContractKFRBL fmt L depth T
                        (progReemb (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth sparsifyImplUsed)
                        G k M N vCap eCap capExp P (allocation sizeParam))) ∧
                  SparseCoreReadoutFootAt fmt L depth T G k M N vCap eCap capExp P
                    (allocation sizeParam) R Psc.sc.prog Psc.sc.op ∧
                  SparseCoreUpdateOutFootAt fmt L depth T G k M N vCap eCap capExp P
                    (allocation sizeParam) edMul R Psc.sc.prog Psc.sc.op ∧
                  SparseCoreReembPlaceAt fmt L depth T G k M N vCap eCap capExp P
                    (allocation sizeParam) R Psc.sc.prog Psc.sc.op :=
  drySparseCoreCode_uniform_bridged_kfrbl_outFoot Psc.cf Psc.firstStep Psc.firstInit Psc.hCF Psc.hBR

/-- Word-size exponent produced by the sparse-core bridge at `capExp`. -/
def drySCWordExp (Psc : DrySparseCorePieces) : ℕ → ℕ := Classical.choose (drySC_bridged_exists Psc)

/-- The bridged sparse-core word exponent satisfies `drySCWordExp Psc 3 ≤ 39`. -/
theorem drySCWordExp_le_39 (Psc : DrySparseCorePieces) : drySCWordExp Psc dryCapExp ≤ 39 :=
  (Classical.choose_spec (drySC_bridged_exists Psc)).1

/-- Bridged `SparseCoreOrdProgramUniformBridged` statement for `Psc.sc`. -/
theorem drySC_uniform_bridged (Psc : DrySparseCorePieces) :
    SparseCoreOrdProgramUniformBridged dryCLsstUsed dryLSFInitUsed sparsifyImplUsed
      Psc.sc.prog Psc.sc.init Psc.sc.op := fun capExp =>
  ⟨drySCWordExp Psc capExp, fun limbMul => by
    obtain ⟨P, a, h1, _, _, _, h2⟩ := (Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul
    refine ⟨P, a, h1, fun depth w fmt L hd hPL => ?_⟩
    obtain ⟨τ, phi, foot, hτ⟩ := h2 depth w fmt L hd hPL
    exact ⟨τ, phi, foot, fun vCap eCap => let ⟨rep, ⟨hloc, _⟩, hR⟩ := hτ vCap eCap
      ⟨rep, hloc, fun G k M N sp hf hc hdl hdlg hdch hs hI hGn hCFmt hkCap =>
        let ⟨h1', h2', _⟩ := hR G k M N sp hf hc hdl hdlg hdch hs hI hGn hkCap
        ⟨dsRep_implements_kfbl_of_kfrbl (h1' hCFmt), h2'⟩⟩⟩⟩

/-- Sparse-core contract parameters extracted from the bridge at `(capExp, limbMul)`. -/
def drySCParams (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : SparseCoreOrdParams :=
  Classical.choose ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul)

theorem drySCParams_wordExp (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) :
    (drySCParams Psc capExp limbMul).wordExp = drySCWordExp Psc capExp :=
  (Classical.choose_spec (Classical.choose_spec ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).1

/-- `sizeParam`-indexed sparse-core allocation extracted from the bridge at `(capExp, limbMul)`. -/
def drySCAllocAt (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : ℕ → ℕ → List ℕ → ℕ :=
  Classical.choose (Classical.choose_spec ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))

/-- Sparse-core allocation specialized to circulation `J` via `drySCSizeParam J`. -/
def drySCAlloc (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) (J : Circulation) : ℕ → List ℕ → ℕ :=
  drySCAllocAt Psc capExp limbMul (drySCSizeParam J)

private theorem dsRep_local_cast_sc {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    (R : DSRep (SparseCoreOrdAbs T₂)) (hloc : R.Local) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Local := by
  subst h; exact hloc

private theorem dsRep_implements_cast_sc {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₂ G k M N vCap eCap capExp P alloc)) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₁ G k M N vCap eCap capExp P alloc) := by
  subst h; exact himpl

private theorem readoutFoot_cast_sc {w L depth capExp : ℕ} {fmt : Num.Format w}
    {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {G : MGraph} {k M N vCap eCap : ℕ}
    {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreReadoutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReadoutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

/-- Capacity-indexed concrete `DSRep` extracted from the bridge for circulation `J` at `(vCap, eCap)`. -/
def drySCRepAt (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree capExp limbMul vCap eCap : ℕ)
    (source J : Circulation)
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
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.2.2
    depth w F.fmt F.limbs (Expander.one_le_chosenL _) (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  let τ := Classical.choose hEx
  let phi := Classical.choose (Classical.choose_spec hEx)
  let foot := Classical.choose (Classical.choose_spec (Classical.choose_spec hEx))
  let hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  let rep := Classical.choose hCap
  hT ▸ (⟨τ, rep, phi, foot⟩ : DSRep (SparseCoreOrdAbs
    (sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth sparsifyImplUsed)))

/-- Locality of `drySCRepAt`. -/
theorem drySCRepAt_local (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree capExp limbMul vCap eCap : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    (drySCRepAt Psc allocationCoefficient allocationDegree capExp limbMul vCap eCap source J hw).Local := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent threshold A I.m
  let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
  let F := ipmQualityMinRatioFormat I.m V k hw
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  have hT : (concreteCirculationCfgWithLast dryWitnessUsed J).T =
      sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 capExp limbMul))).2.2.2
    depth w F.fmt F.limbs (Expander.one_le_chosenL _) (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  exact dsRep_local_cast_sc hT _ (Classical.choose_spec hCap).1.1

/-- Per-level `Implements` in `dryLinkedProgram`, discharging all solver-input hypotheses
(`1 ≤ depth`, `depth ≤ levelM + N₀ + k + F.limbs`, `IsValidLSFInitFor`, `SparseCoreCapHyp`,
`fmt.limbBits = 4`, `SparsifyPolyStretch`, and `γ_t = 1`) for every level `i < cfg.P.d`, every
graph `G` with `G.n ≤ G.m + 1`, and every `vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J`. -/
theorem drySCRepAt_implements_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCapPos : ∀ e, 1 ≤ J.capacity e)
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
    (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw).Implements
      (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFBL F.fmt F.limbs
        (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) := by
  intro W I V k F cfg lay limbMul
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let depth := Expander.chosenL (M₀ ^ 2)
  have hM₀_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 := chosenL_sq_le_four_mul_add_one hM₀_pos; have hN₀ : cfg.N₀ = 4 * M₀ := rfl; have hk1 := cfg.P.hk; omega
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
    (Expander.one_le_chosenL _) (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  have himpl0 := dsRep_implements_kfbl_of_kfrbl (((Classical.choose_spec hCap).2 G cfg.P.k
    (levelM cfg.TP cfg.P i) cfg.N₀ (drySCSizeParam J) hfmt hcap hdepth_le
    (chosenL_sq_le_bundleLogFactor hM₀_pos le_rfl) (chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim) hInit hGn_le
    (drySC_k_le_capExp J i)).1 (drySC_compInitFormatHyp J hJn hJm hCapPos hGm_le))
  have himplShift := dsRep_implements_shift hHas himpl0
  exact dsRep_implements_cast_sc hT _ himplShift

/-- Per-level `SparseCoreReadoutFootAt` in `dryLinkedProgram`, accompanying
`drySCRepAt_implements_level` with the per-run `R.foot` and returned-heap-pointer readout
guarantees for ops `2`, `3`, and `5`. -/
theorem drySCRepAt_readoutFoot_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCapPos : ∀ e, 1 ≤ J.capacity e)
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
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    SparseCoreReadoutFootAt F.fmt F.limbs
      (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
      (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw)
      (dryLinkedProgram W Psc.sc inner) lay.scOp := by
  intro W I V k F cfg lay limbMul
  let threshold := concreteEdgeThresholdWithLast W
  let A := concreteQualityBudgetWithLast W
  let M₀ := max I.m threshold
  let depth := Expander.chosenL (M₀ ^ 2)
  have hM₀_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 := chosenL_sq_le_four_mul_add_one hM₀_pos; have hN₀ : cfg.N₀ = 4 * M₀ := rfl; have hk1 := cfg.P.hk; omega
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
    (Expander.one_le_chosenL _) (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCap := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx)) vCap eCap
  have hfoot0 := ((Classical.choose_spec hCap).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) hfmt hcap hdepth_le (chosenL_sq_le_bundleLogFactor hM₀_pos le_rfl)
    (chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i vCap eCap hlim)
    hInit hGn_le (drySC_k_le_capExp J i)).2.1
  have hfootShift := sparseCoreReadoutFootAt_shift hHas hfoot0
  exact readoutFoot_cast_sc hT _ hfootShift

/-- Discharges the per-level sparse-core word-size bound for `drySCParams` directly from
`drySCWordExp_le_39 Psc`. -/
theorem drySCWordBound_proved (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        allocationCoefficient) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      ∀ i < cfg.P.d,
        (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^
            (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp *
            (F.limbs + 1) <
          2 ^ dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source := by
  intro source J hJn hJm _hCost hCap hw
  dsimp only
  intro i hi
  rw [drySCParams_wordExp]
  have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm (fun e => (hCap e).1)
    i hi.le 0 0 (by omega)).2
  exact Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
    allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm (fun e => (hCap e).1) hw
    (drySCWordExp Psc dryCapExp) (drySCWordExp_le_39 Psc) i _ hL

/-! ## Second dry run through the sparse-core bridge -/

/-- Bridged sparse-core `DSRep` of the second dry run at caps `(G.n, initTargetCap cfg G)`,
fitting under `dryCapLimit` (`dry_initTargetCap_le_capLimit`). -/
def drySCRep (Psc : DrySparseCorePieces) (allocationCoefficient allocationDegree : ℕ)
    (source J : Circulation)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T) :=
  let G := namedInstance (solverConnectedAugmented J)
  drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) G.n
    (initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J) G) source J hw

/-- The space of the sparse-core init at each level `i < d`: for any pointers, the allocation of
op `6` on the init arguments of level `i` is at most `coreInitSpace i`. Of the old readout layout
`OrdCoreReadoutLayout`, only this bound stays. -/
def DrySCInitSpaceLe (allocation : ℕ → List ℕ → ℕ) (coreInitSpace : ℕ → ℕ)
    (d k N L P depth : ℕ) (lvlM : ℕ → ℕ) : Prop :=
  ∀ i < d, ∀ g l gr o h,
    allocation 6 [g, l, gr, o, k, lvlM i, N, L, P, depth, h] ≤ coreInitSpace i

/-- Remaining bridge hypotheses needed to instantiate `initConcreteBody_meets_spec` on
`dryLinkedProgram` with `openInner.toInnerCode`: parameter setup (`initParamSetupContract`), the
sparse-core contract `sparseCoreOrdMachineContractKFBL` with `SparseCoreReadoutFootAt` at every
level of the initial chain (`hCoreImplKFBL`, proved by `drySC_hCoreImplKFBL_proved`), the
last-level contract at the last graph of the initial chain (`hLastImpl`, `hLastSpaceLe`), the
space of the sparse-core init (`hInitSpaceLe`),
per-level fixed-point fits (`hCoreLenFits` for lengths on the `2 ^ (-P)` grid, and
`hLastStretchFits`), and the three size bounds into `sz`. All 22 concrete code,
placement, format, numeric, graph, and word-size hypotheses of `initConcreteBody_meets_spec` are
discharged automatically by `dryInitConcrete_meets_spec`. -/
structure DrySCInitBridgeHyps (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) where
  paramSpace : Circulation → Circulation → ℕ
  paramCost : Circulation → Circulation → ℕ
  lastMult : Circulation → Circulation → ℕ
  stretchP : Circulation → Circulation → ℕ
  lastSpace : Circulation → Circulation → ℕ
  coreInitSpace : Circulation → Circulation → ℕ → ℕ
  lastAlloc : Circulation → Circulation → ℕ → List ℕ → ℕ
  hParam : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
    let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
    MeetsContract w p (dryParamSetupProc Psc.sc openInner)
      (initParamSetupContract w I.m V F.limbs F.fmt.precision cfg.P.d cfg.P.k
        ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10) cfg.N₀
        (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2))
        (levelM cfg.TP cfg.P) (paramSpace source J) (paramCost source J))
  hCoreImplKFBL : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
    let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
    let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
    let lay := dryTailLay Psc.sc openInner.toInnerCode
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    let R := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ i < cfg.P.d,
        R.Implements w p lay.scInit lay.scOp
            (sparseCoreOrdMachineContractKFBL F.fmt F.limbs depth cfg.T (chain.G i) cfg.P.k
              (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G) dryCapExp
              (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
          SparseCoreReadoutFootAt F.fmt F.limbs depth cfg.T (chain.G i) cfg.P.k
            (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G) dryCapExp
            (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R p lay.scOp
  hLastImpl : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
    let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
    let lay := dryTailLay Psc.sc openInner.toInnerCode
    ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
        (lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision (chain.G cfg.P.d).E).Implements
          w p lay.lastInit lay.lastOp
          (lastLevelRuntimeMachineContract F.fmt F.limbs dryLastTool (chain.G cfg.P.d) vc ec
            (lastMult source J) (stretchP source J) (lastAlloc source J))
  hLastSpaceLe : ∀ source J args, lastAlloc source J 1 args ≤ lastSpace source J
  hInitSpaceLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    DrySCInitSpaceLe (drySCAlloc Psc dryCapExp limbMul J) (coreInitSpace source J) cfg.P.d
      cfg.P.k cfg.N₀ F.limbs F.fmt.precision depth (levelM cfg.TP cfg.P)
  hCoreLenFits : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun _source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
      IsDyadicGrid G F.fmt.precision ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
        ∃ q : ℤ, Num.Fits 4 F.limbs q ∧ (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
          chain.toTreeChain.chainLen ℓ₀ (i + 1) e
  hLastStretchFits : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
      ∀ e ∈ (chain.G cfg.P.d).E,
        2 * (2 : ℝ) ^ stretchP source J *
          lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
        Num.capacity 4 F.limbs
  hSpaceLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d (paramSpace source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (lastSpace source J)
      (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
      (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
      (coreInitSpace source J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initSpace'
  hFixedLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d (paramCost source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (lastMult source J) LinkCut.PathProg.pathC
      (drySCParams Psc dryCapExp limbMul)
      (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initFixed
  hMulLe : ∀ source J,
    max (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).mul (lastMult source J) ≤
      (sz source J).toolMul

/-- Discharges `OrdInitConcreteSpecW` in `dryLinkedProgram` via `initConcreteBody_meets_spec`
from `DrySCInitBridgeHyps` and `DryFixedPointCapBounds`. -/
theorem drySC_hInit_of_bridge (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInitBridge : DrySCInitBridgeHyps Psc openInner B hB sz)
    (hCapBounds : DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) sz) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
      let s := sz source J
      OrdInitConcreteSpecW (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
        F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        cfg Rcore (namedInstance I) (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
        (dryTailLay Psc.sc openInner.toInnerCode).initConcrete
        s.B_tree dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        (dryCapLimit dryWitnessUsed J)
        (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
        s.initSpace' s.initFixed s.toolMul := by
  intro source J hJn hJm hCost hCap hw
  obtain ⟨_, hthrTree, hCapTreeInit, _, _, _, _⟩ := hCapBounds source J hJn hJm hCost hCap hw
  exact dryInitConcrete_meets_spec Psc.sc openInner (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)
    source J hJn hJm (fun e => (hCap e).1) hw
    (drySCRepAt_local Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) _ _ source J hw)
    hthrTree hCapTreeInit
    (hInitBridge.hParam source J hJn hJm hCost hCap hw)
    (hInitBridge.hCoreImplKFBL source J hJn hJm hCost hCap hw)
    (hInitBridge.hLastImpl source J hJn hJm hCost hCap hw)
    (hInitBridge.hLastSpaceLe source J)
    (hInitBridge.hInitSpaceLe source J hJn hJm hCost hCap hw)
    (hInitBridge.hCoreLenFits source J hJn hJm hCost hCap hw)
    (hInitBridge.hLastStretchFits source J hJn hJm hCost hCap hw)
    (hInitBridge.hSpaceLe source J hJn hJm hCost hCap hw)
    (hInitBridge.hFixedLe source J hJn hJm hCost hCap hw)
    (hInitBridge.hMulLe source J)

/-- Named solver inner-spec hypotheses instantiated on `drySCRep Psc`, `drySCWordExp Psc`, and
`openInner.toInnerCode` (with the proved `initConcreteBody` installed; its `OrdInitConcreteSpecW`
is discharged by `drySC_hInit_of_bridge` via `initConcreteBody_meets_spec`). -/
structure DrySCSolverHyps (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop where
  hCore : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    OrdChainUpdateCoreSpecWKFBL (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
      (dryCapLimit dryWitnessUsed J) G.n (initTargetCap cfg G) cfg Rcore
      (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
      (dryTailLay Psc.sc openInner.toInnerCode).ordChainCore
      s.coreSpace s.coreFixed s.toolMul s.treeMul s.B_bound s.R_bound
  hSelect : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    OrdCycleRouteSelectSpecW (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
      (dryCapLimit dryWitnessUsed J) cfg Rcore
      (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
      (dryTailLay Psc.sc openInner.toInnerCode).selectRoute
      s.selectSpace s.selectBudget s.maxEdges s.maxPaths
  hEval : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    OrdCycleRouteEvalSpecW (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) cfg Rcore
      (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
      (dryTailLay Psc.sc openInner.toInnerCode).evalCycle
      s.evalSpace s.evalBudget s.maxEdges s.maxPaths
  hTerm : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    ShiftTermChainSyncSpecWExt (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
      (dryCapLimit dryWitnessUsed J) (2 * levelM cfg.TP cfg.P cfg.P.d) cfg Rcore
      (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
      (dryTailLay Psc.sc openInner.toInnerCode).shiftTermChain
      s.termSpace s.termFixed s.toolMul s.treeMul
  hDeep : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    ShiftDeepChainSyncSpecWExtKFBL (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
      F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
      (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
      (dryCapLimit dryWitnessUsed J) (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
      ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size)
      (2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m))
      (2 * (cfg.P.d + 1) * I.n) G.n (initTargetCap cfg G) cfg Rcore
      (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
      (dryTailLay Psc.sc openInner.toInnerCode).shiftDeepChain
      s.deepSpace s.deepFixed s.toolMul s.treeMul
  hCapBounds : DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) sz
  hEnv : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
    let s := sz source J
    OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (s.initSpace' + initWiredExtraSpace cfg (namedInstance I))
      (s.initFixed + initWiredExtraCost cfg (namedInstance I))
      (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
      (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
      s.maxEdges s.maxPaths s.toolMul s.treeMul
      (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
      (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
        62 * (cfg.P.d + 1) + 240)
      Rcore B.cycleRate (B.cycleAllocation I.n I.m)

/-- The `DyadicWithVConcretePrograms` package wired through the sparse-core top-layer bridge,
with the proved concrete initializer `initConcreteBody` installed (`openInner.toInnerCode`) and
`OrdInitConcreteSpecW` discharged via `initConcreteBody_meets_spec`. -/
def dryProgramsSC (Psc : DrySparseCorePieces)
    (openInner : SolverInnerOpen) (hinner : openInner.IsDeterministic)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInitBridge : DrySCInitBridgeHyps Psc openInner B hB sz)
    (hS : DrySCSolverHyps Psc openInner B hB sz) : DyadicWithVConcretePrograms where
  lastTool := dryLastTool
  lastConstant := dryLastConstant
  lastSpec := dryLastSpec
  witness := dryWitnessUsed
  cycleInit := solverCycleInit
  cycleOp := solverOpsDispatch mrdsCycleBase
  cycle := dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc openInner.toInnerCode
  cycleDeterministic := dryCycle_noRand _ _ Psc.hsc (SolverInnerOpen.toInnerCode_isDeterministic hinner)
  cycleRate := B.cycleRate
  cycleAllocation := B.cycleAllocation
  cycleSpace := B.cycleSpace
  allocationCoefficient := dryAllocCoeffFull B hB
  allocationDegree := dryAllocDeg B hB
  cycleSpace_poly := dryAllocFull_spec B hB
  cycleRateExponent := dryRateExponent B hB
  cycleRateExponent_nonneg := (dryRate_spec B hB).2.1
  cycleRateConstant := dryRateConstant B hB
  cycleRateConstant_pos := (dryRate_spec B hB).1
  cycleRate_subpoly := (dryRate_spec B hB).2.2
  supported := by
    intro source J hJn hJm hCost hCap
    dsimp only
    intro hw
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let inner := openInner.toInnerCode
    let cycle := dryCycle threshold A Psc.sc inner
    let I := solverConnectedAugmented J
    let dispatch := mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase) cycle.length
    let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
    obtain ⟨hthrB, hthrTree, hCapTreeInit, hmaxEP, hcapEvalB, hcapTreeB, hcapOffB⟩ :=
      hS.hCapBounds source J hJn hJm hCost hCap hw
    obtain ⟨hQuotaBoundW, h4M3W⟩ :=
      Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
        (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
        ((le_max_right _ _).trans (le_max_left _ _)) source J hJn hJm (fun e => (hCap e).1) hw
    have hTail := dryTail_hasAt threshold A dispatch Psc.sc inner forest
    let lay := dryTailLay Psc.sc inner
    let s := sz source J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let wordExp := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
    let stretchP := (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size
    have hWB := drySCWordBound_proved Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      (le_max_right _ _) source J hJn hJm hCost hCap hw
    exact ordSolver_supported_full_wired dryLastTool dryLastConstant dryLastSpec dryWitnessUsed
      solverCycleInit lay.initConcrete lay.overwrite lay.clog mrdsCycleBase
      solverCycleChainRefresh lay.ordEdits lay.ordChainCore lay.shiftQuotaWriter
      solverCycleFindCycle lay.selectRoute lay.evalCycle
      solverCycleShiftLevel lay.shiftTermChain lay.shiftDeepChain
      cycle B.cycleRate B.cycleAllocation B.cycleSpace
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hJn hJm hCost hCap hw
      (drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw)
      dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J) wordExp
      stretchP (2 * (Ordered.alg2NameBase cfg (namedInstance I) + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m))
      (2 * (cfg.P.d + 1) * I.n) s.initSpace' s.initFixed s.selectSpace s.selectBudget s.evalSpace
      s.evalBudget s.termSpace s.termFixed s.deepSpace s.deepFixed s.maxEdges s.maxPaths s.toolMul
      s.treeMul (DryChainLenGridInv J) s.coreSpace s.coreFixed s.B_tree s.B_bound s.R_bound
      (drySCRepAt_local Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
        (concreteReadout2LimbMul dryWitnessUsed) _ _ source J hw)
      h4M3W hQuotaBoundW hthrB hthrTree hCapTreeInit hmaxEP hcapEvalB hcapTreeB hcapOffB hWB
      (drySparseCoreCapLevels_proved dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
        source J hJn hJm hCost hCap hw)
      (dryInitTargetCap_le_intCapMax J hJn hJm (fun e => (hCap e).1))
      (dryTwoMulN_le_forestEdgeCap J)
      (dryChainLenGridInv_deepShiftChainInvHyps (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
        wordExp stretchP (le_max_right _ _) source J hJn hJm (fun e => (hCap e).1) hw hWB
        (dryLastStretchP_im_le_100_E J hJn hJm (fun e => (hCap e).1)))
      (solverOps_hasAt threshold A dispatch Psc.sc inner forest)
      (solverTail_initWired_at hTail) (solverTail_overwrite_at hTail)
      (solverTail_clog_meetsContract hTail) (solverTail_chainRefresh_at hTail)
      (solverTail_ordEdits_at hTail) (solverTail_shiftQuotaWriter_at hTail)
      (solverTail_findCycle_at hTail) (solverTail_shiftLevel_at hTail)
      (drySC_hInit_of_bridge Psc openInner B hB sz hInitBridge hS.hCapBounds source J hJn hJm hCost hCap hw)
      (hS.hCore source J hJn hJm hCost hCap hw) (hS.hSelect source J hJn hJm hCost hCap hw)
      (hS.hEval source J hJn hJm hCost hCap hw) (hS.hTerm source J hJn hJm hCost hCap hw)
      (hS.hDeep source J hJn hJm hCost hCap hw) (hS.hEnv source J hJn hJm hCost hCap hw)
      (fun j hj args => B.cycleAllocation_le_cycleSpace I.n I.m j hj args)

/-- **Theorem 1.1 (page 2), second dry run through the sparse-core bridge with proved Init.**
Derives `MinCostFlowStatement` from the sparse-core piece hypotheses
(`DrySparseCorePieces`), the inner procedures given as parameters (`SolverInnerOpen`, with
`initConcreteBody` and its local helpers already installed), the explicit Init bridge hypotheses
(`DrySCInitBridgeHyps`), and the other five inner specs (`DrySCSolverHyps`), discharging
`OrdInitConcreteSpecW` via `initConcreteBody_meets_spec`, `SparsifyPolyStretch`, `γ_t = 1`,
`wordExp ≤ 39`, `DrySparseCoreCapLevels`, and the per-level sparse-core word bound automatically. -/
theorem theorem_1_1_dry_run_sc (Psc : DrySparseCorePieces)
    (openInner : SolverInnerOpen) (hinner : openInner.IsDeterministic)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hInitBridge : DrySCInitBridgeHyps Psc openInner B hB sz)
    (hS : DrySCSolverHyps Psc openInner B hB sz) :
    MinCostFlowStatement :=
  theorem_1_1_of_dyadic_withV_mrds_programs
    (dryProgramsSC Psc openInner hinner B hB sz hInitBridge hS)

end MinCostFlow.Final.DryRun
