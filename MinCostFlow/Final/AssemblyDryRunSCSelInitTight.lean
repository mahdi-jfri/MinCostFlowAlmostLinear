module

public import MinCostFlow.Final.AssemblyDryRunSCSelBridge
public import MinCostFlow.Final.AssemblyDryRunSCInitDischarged
public import MinCostFlow.MinRatio.WireReembPotChain
import MinCostFlow.Final.AssemblyDryRunSC
import MinCostFlow.Final.AssemblyDryRunSCFormat
import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
import MinCostFlow.Final.AssemblyDryRunSCFits
import Mathlib.Tactic

/-!
# Concrete re-embedding potential and tight `OrdInitConcreteSpecW` in `dryLinkedProgramSel` (`AssemblyDryRunSCSelInitTight`)

Provides the concrete re-embedding potential `dryPot := progReembPot` and transfers the
initializer sub-contracts into `dryLinkedProgramSel`:
1. `dryPot` and `dryPot_facts`: fixes `pot := progReembPot` on
   `(concreteCirculationCfgWithLast dryWitnessUsed J).T.State` and discharges `ToolReembPotFacts`
   via `progReembPotFacts`.
2. `dryInnerCodeSel_hasInit_sel`, `dryInnerCodeSel_hasParam_sel`, `drySC_coreKFBL_sel`, and
   `drySC_hLastImpl_sel`: placement and contract transfers inside `dryLinkedProgramSel`.
3. `dryInitCode_hInitConcrete_tight_sel`: proves `OrdInitConcreteSpecW` at `lay.initConcrete`
   inside `dryLinkedProgramSel` with the exact tight `(initConcreteSpace, initConcreteFixed,
   max PscP.mul (dryLastMult J))` bounds required by `solverInitWiredSel_runs` and
   `solverInitWiredSel_cost_to_spec`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete re-embedding potential `dryPot := progReembPot` -/

/-- Concrete re-embedding potential on the dry-run core tool state (`progReembPot`). -/
def dryPot (J : Circulation) :
    (concreteCirculationCfgWithLast dryWitnessUsed J).T.State → ℕ :=
  progReembPot

/-- `dryPot J` meets `ToolReembPotFacts` for `(concreteCirculationCfgWithLast dryWitnessUsed J).T`. -/
theorem dryPot_facts (J : Circulation) :
    ToolReembPotFacts (concreteCirculationCfgWithLast dryWitnessUsed J).T (dryPot J) := by
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent threshold A I.m
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  exact progReembPotFacts (dryLSFInitUsed L P) dryCLsstUsed depth sparsifyImplUsed

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Placement and sub-contract transfers into `dryLinkedProgramSel` -/

private theorem hasAt_peel_st {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Placement of `dryInitConcreteProcs` at `lay.initConcrete` inside `dryLinkedProgramSel`. -/
theorem dryInnerCodeSel_hasInit_sel (Psc : DrySparseCorePieces)
    (paramCode coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.initConcrete
    let ops := mrdsCycleBase
    let paramProc := b + dryInitConcreteLen + paramCode.off
    p.procs[b]? = some (initConcreteBody (b + 17 + dgIdxInitFromLists) paramProc (b + 1)
        lay.scInit (lay.scOp 3) (lay.scOp 2) (b + 2) (lay.scOp 5)
        lay.lastInit (lay.lastOp 0) (ops + 81) (ops + 81 + 1)
        (b + 4) (ops + 20) (ops + 16) (ops + 4) ops) ∧
    p.procs[b + 1]? = some buildSortedEndsBody ∧
    p.procs[b + 2]? = some (wireCoreLenBody (b + 3)) ∧
    p.procs[b + 3]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    ∀ {w : ℕ},
      MeetsContract w p (b + 4) (pathSlotBindContract w) ∧
      ∀ vCap eCap G vL eEdges,
        MeetsContract w p (b + 17 + dgIdxInitFromLists)
          (dgInitFromListsContract w vCap eCap G vL eEdges) := by
  intro inner p lay b ops paramProc
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  set env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    Psc.sc solverTailBase
  have hInner' : p.HasAt env.innerBase (inner.procs env) := hInner
  unfold inner dryInnerCodeSel at hInner'
  dsimp only at hInner'
  obtain ⟨_, r1⟩ := hasAt_peel_st (b' := env.innerBase + 1) hInner' (by simp)
  have hInitSub := Num.hasAt_append_left r1
  unfold dryInitCode at hInitSub
  dsimp only at hInitSub
  have hInitBlock := Num.hasAt_append_left hInitSub
  have hBase := dryInitConcreteProcs_hasAt (w := 0) hInitBlock
  have hbEq : env.innerBase + 1 = b := by
    dsimp only [b, lay, inner, dryTailLay, solverTailLayout, dryInnerCodeSel, dryInitCode, env,
      solverTailInnerEnv]
  have hScInit : env.scInit = lay.scInit := rfl
  have hScOp : ∀ j, env.scOp j = lay.scOp j := fun _ => rfl
  have hLastInit : env.lastInit = lay.lastInit := rfl
  have hLastOp : ∀ j, env.lastOp j = lay.lastOp j := fun _ => rfl
  have hOpsEq : env.opsBase = ops := rfl
  have hParamEq : env.innerBase + 1 + dryInitConcreteLen + paramCode.off = paramProc := by
    dsimp only [paramProc]; rw [hbEq]
  refine ⟨?_, ?_, ?_, ?_, fun {w} => ?_⟩
  · simpa only [hbEq, hParamEq, hScInit, hScOp, hLastInit, hLastOp, hOpsEq] using hBase.1
  · simpa only [hbEq] using hBase.2.1
  · simpa only [hbEq] using hBase.2.2.1
  · simpa only [hbEq, hOpsEq] using hBase.2.2.2.1
  · have hW := dryInitConcreteProcs_hasAt (w := w) hInitBlock
    exact ⟨by simpa only [hbEq] using hW.2.2.2.2.1,
      fun vCap eCap G vL eEdges => by simpa only [hbEq] using hW.2.2.2.2.2 vCap eCap G vL eEdges⟩

/-- Placement of `dryParamProcs` at `dryInitParamProc` inside `dryLinkedProgramSel`. -/
theorem dryInnerCodeSel_hasParam_sel (Psc : DrySparseCorePieces)
    (coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let b := dryInitParamProc Psc.sc (dryParamCode Psc) coreCode selectCode termCode deepCode
    p.HasAt b (dryParamProcs b) := by
  intro inner p b
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  set env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    Psc.sc solverTailBase
  have hInner' : p.HasAt env.innerBase (inner.procs env) := hInner
  unfold inner dryInnerCodeSel at hInner'
  dsimp only at hInner'
  obtain ⟨_, r1⟩ := hasAt_peel_st (b' := env.innerBase + 1) hInner' (by simp)
  have hInitSub := Num.hasAt_append_left r1
  unfold dryInitCode at hInitSub
  dsimp only at hInitSub
  obtain ⟨_, hParamAt⟩ := hasAt_peel_st (b' := env.innerBase + 1 + dryInitConcreteLen) hInitSub
    (by simp [dryInitConcreteProcs_length])
  have hbEq : env.innerBase + 1 + dryInitConcreteLen = dryParamBase Psc := rfl
  have hbEq2 : b = dryParamBase Psc := by
    dsimp only [b, dryInitParamProc, dryTailLay, solverTailLayout, dryInnerCodeSel, dryInitCode,
      dryParamCode, dryParamBase, env, solverTailInnerEnv]
    omega
  rw [hbEq] at hParamAt
  have hEqProcs : (dryParamCode Psc).procs { env with innerBase := dryParamBase Psc } =
      dryParamProcs (dryParamBase Psc) := by simp [dryParamCode]
  rw [hEqProcs] at hParamAt
  rw [hbEq2]
  exact hParamAt

private theorem dsRep_implements_cast_sel {w : ℕ} {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {L depth capExp : ℕ} {fmt : Num.Format w}
    {G : MGraph} {k M N vCap eCap : ℕ} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₂ G k M N vCap eCap capExp P alloc)) :
    (h ▸ R : DSRep (SparseCoreOrdAbs T₁)).Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T₁ G k M N vCap eCap capExp P alloc) := by
  subst h; exact himpl

private theorem readoutFoot_cast_sel {w : ℕ} {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {L depth capExp : ℕ} {fmt : Num.Format w}
    {G : MGraph} {k M N vCap eCap : ℕ} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreReadoutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReadoutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

/-- Per-level `KFBL` `Implements` and `SparseCoreReadoutFootAt` inside `dryLinkedProgramSel`. -/
theorem drySC_coreKFBL_sel (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
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
    R.Implements (dryWordSize W allocationCoefficient allocationDegree source) p lay.scInit lay.scOp
        (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
          (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
          (initTargetCap cfg (namedInstance I)) dryCapExp
          (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
        (initTargetCap cfg (namedInstance I)) dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J) R p lay.scOp := by
  intro W I V k F cfg lay limbMul R p
  let M₀ := max I.m (concreteEdgeThresholdWithLast W)
  let depth := Expander.chosenL (M₀ ^ 2)
  have hlim := dry_initTargetCap_le_capLimit J hJn hJm hCapPos
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one cfg.P.hM₀
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap := concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le
    (namedInstance I).n (initTargetCap cfg (namedInstance I)) hlim
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
    (namedInstance I).n (initTargetCap cfg (namedInstance I))
  have hBoth := (Classical.choose_spec hCapSpec).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) rfl hcap hdepth_le (chosenL_sq_le_bundleLogFactor cfg.P.hM₀ le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i (namedInstance I).n (initTargetCap cfg (namedInstance I)) hlim)
    hInit hGn_le (drySC_k_le_capExp J i)
  exact ⟨dsRep_implements_cast_sel hT _ (dsRep_implements_shift hHas
      (dsRep_implements_kfbl_of_kfrbl (hBoth.1 (drySC_compInitFormatHyp J hJn hJm hCapPos hGm_le)))),
    readoutFoot_cast_sel hT _ (sparseCoreReadoutFootAt_shift hHas hBoth.2.1)⟩

/-- Last-level implementation at `chain.G d` inside `dryLinkedProgramSel`. -/
theorem drySC_hLastImpl_sel (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode)
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
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      let lay := dryTailLay Psc.sc inner
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          (lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision (chain.G cfg.P.d).E).Implements
            w p lay.lastInit lay.lastOp
            (lastLevelRuntimeMachineContract F.fmt F.limbs cfg.L (chain.G cfg.P.d) vc ec
              (dryLastMult J) (dryLastStretchP J) (fun _ _ => dryLastSpace J)) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg G w p lay ℓ₀ g₀ hLen chain vc ec hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he => lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  obtain ⟨hconn, hnm⟩ :=
    drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR cfg.P.d le_rfl
  obtain ⟨-, -, hEsub, -, -⟩ :=
    drySC_chainLen_bounds J hJn hJm hCap1 ℓ₀ g₀ hLen cfg.P.d le_rfl
  have hm : (chain.G cfg.P.d).m ≤ (solverConnectedAugmented J).m :=
    le_trans (Finset.card_le_card hEsub) (namedInstance_m I).le
  have hmD : (chain.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
    have hGV := namedInstance_valid I
      (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
    obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
      (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
    have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
    have hnG : G.n ≤ cfg.N₀ := by
      have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
      rw [hInEq]; exact hIn
    have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G ℓ₀ := by
      intro e he
      have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
      rw [abs_le] at hlog
      exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
        by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
    have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G ℓ₀ g₀ hGV hmG hnG hℓ
    have hLvl := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hγM₀ hV.hγk hInit.1 cfg.P.d le_rfl
    exact_mod_cast hLvl.2.2.1
  refine lastLevelRuntime_implements_mono
    (dryLastBodies_implements (dryLinkedProgramSel_lastLevel_hasAt dryWitnessUsed Psc.sc inner selInitCode)
      F.fmt (chain.G cfg.P.d) rfl hconn hnm) ?_ ?_ ?_
  · exact packedLastLevelMultiplier_le_dryLastMultBound (le_trans hnm (Nat.add_le_add_right hmD 1)) hmD
  · have hsz := Nat.size_le_size (Nat.add_le_add_right hm 1)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size
    omega
  · intro _
    exact drySC_lastAllocLe_proved allocationCoefficient allocationDegree
      source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen vc ec hcap

/-! ## 3. Tight `OrdInitConcreteSpecW` inside `dryLinkedProgramSel` -/

private theorem initSel_ipmQuality_arith (m V k : ℕ) :
    let L := ipmQualityLimbs m V k
    let P := ipmQualityPrecision m V k
    let epsExp := k + Num.IPM.alphaExponent m V + 10
    P ≤ 4 * L ∧ 4 ∣ P ∧ 0 < L ∧ epsExp ≤ P ∧ P - epsExp + 1 < 4 * L := by
  have hk : k ≤ qualitySlackExponent m V k := qualityExponent_le_qualitySlackExponent m V k
  have hα : Num.IPM.alphaExponent m V ≤ Num.IPM.alphaScale m V := by
    unfold Num.IPM.alphaExponent Num.IPM.alphaScale
    have hc : Nat.clog 2 (1000 * (m.size + V.size)) ≤ 1000 * (m.size + V.size) :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
    omega
  dsimp only [ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits, ipmQualityRangeExponent]
  exact ⟨by omega, Nat.dvd_mul_right 4 _, by omega, by omega, by omega⟩

private theorem initSel_cfg_eps_eq (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    (concreteCirculationCfgWithLast dryWitnessUsed J).ε =
      ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P := by
  intro I V k P epsExp
  have hle : epsExp ≤ P := (initSel_ipmQuality_arith I.m V k).2.2.2.1
  dsimp only [concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
    Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
  have h1024 : (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have h2e : (0 : ℝ) < (2 : ℝ) ^ epsExp := by positivity
  have hpow : (2 : ℝ) ^ (P - epsExp) * (2 : ℝ) ^ epsExp = (2 : ℝ) ^ P := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  push_cast
  rw [eq_div_iff h2pos.ne', h1024]
  calc (1 / (2 : ℝ) ^ k) * (1 / (2 : ℝ) ^ Num.IPM.alphaExponent I.m V) / (2 : ℝ) ^ 10 *
        (2 : ℝ) ^ P
      = (2 : ℝ) ^ P /
          ((2 : ℝ) ^ k * (2 : ℝ) ^ Num.IPM.alphaExponent I.m V * (2 : ℝ) ^ 10) := by ring
    _ = (2 : ℝ) ^ P / (2 : ℝ) ^ epsExp := by
        dsimp only [epsExp]; rw [pow_add, pow_add]
    _ = (2 : ℝ) ^ (P - epsExp) := by
        rw [div_eq_iff h2e.ne']; exact hpow.symm

private lemma initSel_capTree_lt (I : Instance) (V k : ℕ) {w : ℕ}
    (hw : ipmQualityParameterWordBits I.m V k ≤ w)
    (h2n1Le : 2 * (namedInstance I).n + 1 ≤ 4 * I.m + 5) :
    let F := ipmQualityMinRatioFormat I.m V k hw
    2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) < (Num.capacity 4 F.limbs : ℤ) := by
  intro F
  have hlog1 : 2 * (namedInstance I).n + 1 < 2 ^ (F.rangeExponent + 12) := by
    have hsz : (2 * (namedInstance I).n + 1).size ≤ F.rangeExponent + 12 := by
      have h1 : (2 * (namedInstance I).n + 1).size ≤ (4 * I.m + 5).size := Nat.size_le_size h2n1Le
      have h2 : (4 * I.m + 5).size ≤ I.m.size + 4 := by
        rw [Nat.size_le]; have := Nat.lt_size_self I.m; have := Nat.one_le_pow I.m.size 2 (by decide)
        rw [pow_add]; omega
      have h3 : I.m.size ≤ F.rangeExponent + 8 := by
        have := le_trans (Nat.le_add_right I.m.size V.size) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
        have hsr := slackRangeExponent_le_qualitySlackExponent I.m V k
        dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]
        unfold slackRangeExponent at hsr; omega
      omega
    exact lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by decide) hsz)
  have h2n : ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) ≤ (2 : ℤ) ^ (F.rangeExponent + 12) := by
    exact_mod_cast le_of_lt hlog1
  have hCapEq : (Num.capacity 4 F.limbs : ℤ) = (2 : ℤ) ^ (4 * F.limbs) := by
    have h16 : ((2 ^ 4 : ℕ) : ℤ) = (2 : ℤ) ^ 4 := by norm_num
    change ((2 ^ 4 : ℕ) : ℤ) ^ F.limbs = (2 : ℤ) ^ (4 * F.limbs)
    rw [h16, ← pow_mul]
  have h4L : F.fmt.precision + 3 * F.rangeExponent + 15 ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
      ipmQualityRangeExponent]
    omega
  rw [hCapEq]
  have hnn : (0 : ℤ) ≤ (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) := by positivity
  have hmul : 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤
      (2 : ℤ) ^ (F.fmt.precision + 3 * F.rangeExponent + 14) := by
    have hle1 : 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) ≤
        2 * (2 : ℤ) ^ (F.rangeExponent + 12) := by linarith
    calc 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
          (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1)
        ≤ (2 * (2 : ℤ) ^ (F.rangeExponent + 12)) *
          (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) :=
          mul_le_mul_of_nonneg_right hle1 hnn
      _ = (2 : ℤ) ^ (F.fmt.precision + 3 * F.rangeExponent + 14) := by
          have hexp : F.rangeExponent + 12 + (F.fmt.precision + 2 * F.rangeExponent + 1) + 1 =
              F.fmt.precision + 3 * F.rangeExponent + 14 := by ring
          rw [mul_assoc, ← pow_add, ← pow_succ', hexp]
  exact lt_of_le_of_lt hmul (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (Nat.lt_of_succ_le h4L))

set_option maxHeartbeats 800000 in
/-- **Tight `OrdInitConcreteSpecW` inside `dryLinkedProgramSel`** at `lay.initConcrete`,
preserving the exact `initConcreteSpace`, `initConcreteFixed`, and `max PscP.mul (dryLastMult J)`
bounds (leaving headroom for `dryInitSelectSpace`, `dryInitSelectFixed`, and `+ dryKeyCost`). -/
theorem dryInitCode_hInitConcrete_tight_sel (Psc : DrySparseCorePieces)
    (coreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdInitConcreteSpecW
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10)
        cfg Rcore (namedInstance I)
        (dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode)
        (dryTailLay Psc.sc inner).initConcrete
        s.B_tree dryCapExp limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp
        (initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d (dryParamSpace source J)
          dryCapExp (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
          (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
          (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
          (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1))
          cfg.N₀)
        (initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d (dryParamCost source J)
          dryCapExp (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC PscP
          (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀)
        (max PscP.mul (dryLastMult J)) := by
  intro inner source J hJn hJm hCost hCap hw I V k F cfg limbMul PscP Rcore s
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
  let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
  let lay := dryTailLay Psc.sc inner
  let B := dryInnerBounds Psc openSz hOpen selSz hSel
  let hB := dryInnerBounds_hyp Psc openSz hOpen selSz hSel
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hSCWordCoeff : Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    le_max_right _ _
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hArith := initSel_ipmQuality_arith I.m V k
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hGV : (namedInstance I).IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hGE : (namedInstance I).E = Finset.range I.m := rfl
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hVlt : ∀ v ∈ (namedInstance I).V, v < (namedInstance I).n := fun v hv => by
    rw [hInEq]; exact Finset.mem_range.mp hv
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap1
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
  have heCapEq : initRootECap cfg.N₀ cfg.P.k I.m = initTargetCap cfg (namedInstance I) :=
    initRootECap_eq_initTargetCap rfl hImPos rfl (le_max_left _ _)
  have hcap0 : (namedInstance I).n + initRootECap cfg.N₀ cfg.P.k I.m + 2 ≤ dryCapLimit dryWitnessUsed J :=
    heCapEq.symm ▸ dry_initTargetCap_le_capLimit J hJn hJm hCap1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk1 : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha1 : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod : (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) ≤ 1 :=
      (mul_le_mul hk1 ha1 (by positivity) (by norm_num)).trans (by norm_num)
    have hE1 : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hnn : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
  have hDW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w := by
    have hM1 : 1 ≤ cfg.P.M₀ := le_trans (by omega : 1 ≤ 2)
      ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
    exact lt_of_le_of_lt ((chosenL_sq_le_four_mul_add_one hM1).trans
      (by change 4 * cfg.P.M₀ + 1 ≤ 4 * cfg.P.M₀ + 3; omega)) h4M3W
  have hwk : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * (namedInstance I).m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have hsearchW : 20 * (4 * F.limbs + 8) + 100 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    exact lt_of_le_of_lt (by omega : 20 * (4 * F.limbs + 8) + 100 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k) hB14
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap1).1
  have hInLe : I.n ≤ 2 * I.m + 2 := by change J.n + 1 ≤ 2 * I.m + 2; omega
  have h2n1Le : 2 * (namedInstance I).n + 1 ≤ 4 * I.m + 5 := by rw [hInEq]; omega
  have hvw : 2 * (namedInstance I).n + 1 < 2 ^ w := by
    have hMle : I.m ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    exact lt_of_le_of_lt (by omega : 2 * (namedInstance I).n + 1 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k) hB14
  have hwidthN : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs := by
    have hlog1 : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ (4 * I.m + 5).size :=
      (Nat.log_mono_right h2n1Le).trans (le_of_lt (Nat.log_lt_of_lt_pow (by omega) (Nat.lt_size_self _)))
    have hsz : (4 * I.m + 5).size ≤ I.m.size + 4 := by
      rw [Nat.size_le]
      have h1 : I.m < 2 ^ I.m.size := Nat.lt_size_self I.m
      have h2 : 1 ≤ 2 ^ I.m.size := Nat.one_le_pow _ _ (by decide)
      rw [pow_add]; omega
    have hmsz : I.m.size ≤ F.rangeExponent + 8 := by
      have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
        le_trans (Nat.le_add_right _ _) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
      have h2 := slackRangeExponent_le_qualitySlackExponent I.m V k
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]
      unfold slackRangeExponent at h2; omega
    have h4L : F.rangeExponent + 12 ≤ 4 * F.limbs := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision]; omega
    omega
  have hMw : ∀ i < cfg.P.d, levelM cfg.TP cfg.P i < 2 ^ w := by
    intro i hi
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap1 i hi.le 0 0 (by omega)).2
    have h1 := Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hSCWordCoeff source J hJn hJm hCap1 hw
      1 (by decide) i _ hL
    have hle : levelM cfg.TP cfg.P i ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 1 * (F.limbs + 1) := by
      rw [pow_one]; exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    exact lt_of_le_of_lt hle h1
  have hOps := solverOpsProcs_initHelpers hw14
    (dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner selInitCode)
  obtain ⟨h0, h1, h2, h3, h45⟩ :=
    dryInnerCodeSel_hasInit_sel Psc (dryParamCode Psc) coreCode selectCode termCode deepCode selInitCode
  obtain ⟨hBind, hDgInit⟩ := h45 (w := w)
  have hLastReadout : p.procs[lay.lastOp 0]? = some LastLevelProgram.readoutBody :=
    packedLastLevelBodies_readout_at
      (dryLinkedProgramSel_lastLevel_hasAt dryWitnessUsed Psc.sc inner selInitCode)
  have hParam := dryParamProcs_discharges_hParam_at B hB p
    (dryInitParamProc Psc.sc (dryParamCode Psc) coreCode selectCode termCode deepCode)
    (dryInnerCodeSel_hasParam_sel Psc coreCode selectCode termCode deepCode selInitCode)
    source J hJn hJm hCost hCap hw
  have hCoreImpl :
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin (namedInstance I) F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).1
        ∀ i < cfg.P.d,
          Rcore.Implements w p lay.scInit lay.scOp
            (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
              cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
              (initRootECap cfg.N₀ cfg.P.k I.m) dryCapExp PscP
              (drySCAlloc Psc dryCapExp limbMul J)) ∧
          SparseCoreReadoutFootAt F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
            cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n
            (initRootECap cfg.N₀ cfg.P.k I.m) dryCapExp PscP
            (drySCAlloc Psc dryCapExp limbMul J) Rcore p lay.scOp := by
    intro ℓ₀ g₀ hLen chain i hi
    have hlPos : ∀ e ∈ (namedInstance I).E, 0 < ℓ₀ e := fun e he =>
      lt_of_lt_of_le (by positivity) (hLen e he).1
    have hlR : ∀ e ∈ (namedInstance I).E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
      (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
    have hnm : (chain.G i).n ≤ (chain.G i).m + 1 :=
      (drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le).2
    have hGm_le : (chain.G i).m ≤ I.m :=
      (Finset.card_le_card (drySC_chainLen_bounds J hJn hJm hCap1 ℓ₀ g₀ hLen i hi.le).2.2.1).trans
        (namedInstance_m I).le
    rw [heCapEq]
    exact drySC_coreKFBL_sel Psc inner selInitCode
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hJn hJm hCap1 hw
      i hi (chain.G i) hnm hGm_le
  have hLastImpl := drySC_hLastImpl_sel Psc inner selInitCode
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  have hCoreLenFits := drySC_hCoreLenFits_onGrid
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  have hLastStretchFits := drySC_hLastStretchFits_Im
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  exact initConcreteBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (E := F.rangeExponent) (m := I.m) (V := V)
    (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (capExp := dryCapExp) (limbMul := limbMul) (capLimit := dryCapLimit dryWitnessUsed J)
    (initConcreteProc := lay.initConcrete)
    (graphPack := lay.initConcrete + 17 + dgIdxInitFromLists)
    (paramSetup := dryInitParamProc Psc.sc (dryParamCode Psc) coreCode selectCode termCode deepCode)
    (sortedEnds := lay.initConcrete + 1) (coreInit := lay.scInit)
    (coreLenProc := lay.initConcrete + 2) (edgeProc := lay.initConcrete + 3)
    (signExt := mrdsCycleBase + 17) (mul := mrdsCycleBase + 11) (intDiv := mrdsCycleBase + 22)
    (lastInit := lay.lastInit) (treeBase := mrdsCycleBase + 81) (bind := lay.initConcrete + 4)
    (shift := mrdsCycleBase + 20) (divide := mrdsCycleBase + 16)
    (negate := mrdsCycleBase + 4) (copy := mrdsCycleBase)
    (lastMult := dryLastMult J) (stretchP := dryLastStretchP J) (lastSpace := dryLastSpace J)
    (paramSpace := dryParamSpace source J) (paramCost := dryParamCost source J)
    (fmt := F.fmt) (cfg := cfg) (P_sc := PscP)
    (coreAlloc := drySCAlloc Psc dryCapExp limbMul J) (lastAlloc := fun _ _ => dryLastSpace J)
    (coreInitSpace := dryCoreInitSpace Psc J) (Rcore := Rcore)
    (opCore := lay.scOp) (opLast := lay.lastOp) (G := namedInstance I) (p := p) (B_tree := s.B_tree)
    h0 rfl rfl hArith.1
    (sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _)
    (fixedPointLastLevelTool_buildEqOnE _ _)
    (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    hVcfg hGV hGE hVlt hmG hnG hcap0 hEΨ (initSel_cfg_eps_eq J) hεPos hεLe
    (le_refl _) (initSel_capTree_lt I V k hw h2n1Le) cfg.P.hd hw14 hwk h4M3W
    hfit.2.2.2.2.2.2.2 hfit.2.2.1 hDW hsearchW
    hArith.2.1 hArith.2.2.1 hArith.2.2.2.1 hArith.2.2.2.2 hvw hwidthN hMw
    (hDgInit _ _ _ _ _) hParam h1 h2 h3
    hOps.2.2.2.2.1 hOps.2.2.1 hOps.2.2.2.2.2.2.1 hOps.2.2.2.2.2.1 hOps.2.2.2.1 hOps.2.1 hOps.1
    hBind hOps.2.2.2.2.2.2.2
    hCoreImpl hLastImpl hLastReadout (fun _ => le_refl _)
    (fun i _ g l gr o h => le_of_eq (drySCAlloc_init_eq_dryCoreInitSpace Psc J i g l gr o _ _ h))
    hCoreLenFits hLastStretchFits

/-- The tight `initMul` of `dryInitCode_hInitConcrete_tight_sel` plus `selSz.keyCost` fits inside
`dryToolMul` for every select-rebuild size table built via `mkDrySelectRebuildSizes`. -/
theorem dryInitMul_add_keyCost_le_dryToolMul (Psc : DrySparseCorePieces)
    (initSel : DryInitSelectSizes) (shiftSel : DryShiftSelectSizes) (source J : Circulation) :
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    let PscP := drySCParams Psc dryCapExp limbMul
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    max PscP.mul (dryLastMult J) + selSz.keyCost source J ≤
      dryToolMul Psc selSz source J := by
  intro limbMul PscP selSz
  dsimp only [dryToolMul, deepShiftToolMulBound, selSz, mkDrySelectRebuildSizes, dryCReemb,
    PscP, limbMul]
  omega

end MinCostFlow.Final.DryRun

end
