module

public import MinCostFlow.Final.AssemblyDryRunSCSelBridge
public import MinCostFlow.MinRatio.WireShiftDeep
import MinCostFlow.Final.AssemblyDryRunSCInit
import MinCostFlow.Final.AssemblyDryRunSCRem
import MinCostFlow.MinRatio.WireCoreLenK
import MinCostFlow.MinRatio.WireShiftDeepSpecMonoKFBL
import Mathlib.Tactic

/-!
# Concrete `shiftDeepChain` block and proof of `hDeepKFBL` (`AssemblyDryRunSCDeepCode`)

Packages the deterministic deep-shift synchronization module (`WireShiftDeep.lean`,
`shiftDeepChainBodyKFBL`) together with its five local helpers (`wireSuffixPackEditsBody`,
`wireCoreLenBody`, `wireCoreLenEdgeBody`, `pathSlotBindBody`, `wireCanonCopyBody`) into a
relocatable `SolverInnerSubCode` block `dryDeepCode`, and proves `ShiftDeepChainSyncSpecWExtKFBL`
unconditionally for `dryDeepCode` inside `dryLinkedProgram` at `drySCRep` and
`dryInnerSizesWithSelect`:

* `dryDeepProcs`, `dryDeepCode`: the 6-procedure deterministic `SolverInnerSubCode` block.
* `dryInnerCodeSel_hasDeep`: extracts all 6 procedures of `dryDeepCode` at `lay.shiftDeepChain`.
* `dryDeepCode_hLastImpl`: discharges `shiftDeepChainBody_meets_spec`'s last-level hypothesis
  at `dryLastMult J`, `dryLastStretchP J`, and `fun _ _ => dryLastSpace J` for every connected
  graph `G` with `G.m ≤ I.m`, `G.m ≤ levelM cfg.TP cfg.P cfg.P.d`, and `G.n ≤ G.m + 1`.
* `dryDeepCode_hDeepKFBL`: discharges `ShiftDeepChainSyncSpecWExtKFBL` for `dryDeepCode` via
  `shiftDeepChainBody_meets_spec`, `drySC_coreKFBL`, and `drySC_forestCap_level`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete 6-procedure deterministic `SolverInnerSubCode` block for `shiftDeepChain` -/

/-- Fixed length (`6`) of `dryDeepProcs`. -/
def dryDeepCodeLen : ℕ := 6

/-- Concrete deterministic procedure block of length `6` placed at `env.innerBase` implementing
`shiftDeepChainBodyKFBL` and its five local helpers:
* `b + 0`: `shiftDeepChainBodyKFBL` (calling `env.scInit`, `env.scOp 1/3/2/5`, `env.lastInit`,
  `b + 2`, `b + 1`, `dryPathTreeOp ops 4/1/0`, `b + 4`, `b + 5`, `ops + 69`);
* `b + 1`: `wireSuffixPackEditsBody`;
* `b + 2`: `wireCoreLenBody (b + 3)`;
* `b + 3`: `wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops`;
* `b + 4`: `pathSlotBindBody`;
* `b + 5`: `wireCanonCopyBody ops (ops + 4)`. -/
def dryDeepProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [shiftDeepChainBodyKFBL env.scInit (env.scOp 1) (env.scOp 3) (env.scOp 2) (b + 2)
      (env.scOp 5) env.lastInit (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 4) (b + 5) (ops + 69),
   wireSuffixPackEditsBody,
   wireCoreLenBody (b + 3),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops,
   pathSlotBindBody,
   wireCanonCopyBody ops (ops + 4)]

theorem dryDeepProcs_length (env : SolverInnerEnv) :
    (dryDeepProcs env).length = dryDeepCodeLen := rfl

theorem dryDeepProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ dryDeepProcs env, s.NoRand := by
  intro s hs
  unfold dryDeepProcs at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact shiftDeepChainBodyKFBL_noRand _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact wireSuffixPackEditsBody_noRand
  · exact wireCoreLenBody_noRand _
  · exact wireCoreLenEdgeBody_noRand _ _ _ _
  · simp [pathSlotBindBody, Stmt.NoRand]
  · exact wireCanonCopyBody_noRand _ _

/-- Relocatable `SolverInnerSubCode` for `shiftDeepChain` (`shiftDeepChainBodyKFBL`). -/
def dryDeepCode : SolverInnerSubCode where
  procs := dryDeepProcs
  len := dryDeepCodeLen
  hlen := dryDeepProcs_length
  hnoRand := dryDeepProcs_noRand
  off := 0

/-! ## 2. Placement inside `dryLinkedProgram` with `dryInnerCodeSel` -/

private theorem hasAt_peel_deep {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

private theorem hasAt_dryInnerCodeSel_deep {p : Program} {env : SolverInnerEnv}
    (initCode coreCode selectCode termCode : SolverInnerSubCode)
    (hInner : p.HasAt env.innerBase
      ((dryInnerCodeSel initCode coreCode selectCode termCode dryDeepCode).procs env)) :
    let b := env.innerBase + (1 + initCode.len + coreCode.len + selectCode.len + termCode.len + 0)
    p.procs[b]? = some (shiftDeepChainBodyKFBL env.scInit (env.scOp 1) (env.scOp 3) (env.scOp 2)
        (b + 2) (env.scOp 5) env.lastInit (b + 1) (dryPathTreeOp env.opsBase 4)
        (dryPathTreeOp env.opsBase 1) (dryPathTreeOp env.opsBase 0) (b + 4) (b + 5)
        (env.opsBase + 69)) ∧
    p.procs[b + 1]? = some wireSuffixPackEditsBody ∧
    p.procs[b + 2]? = some (wireCoreLenBody (b + 3)) ∧
    p.procs[b + 3]? = some (wireCoreLenEdgeBody (env.opsBase + 17) (env.opsBase + 11)
        (env.opsBase + 22) env.opsBase) ∧
    p.procs[b + 4]? = some pathSlotBindBody ∧
    p.procs[b + 5]? = some (wireCanonCopyBody env.opsBase (env.opsBase + 4)) := by
  intro b
  unfold dryInnerCodeSel at hInner
  dsimp only at hInner
  obtain ⟨_, r1⟩ := hasAt_peel_deep (b' := env.innerBase + 1) hInner (by simp)
  obtain ⟨_, r2⟩ := hasAt_peel_deep (b' := env.innerBase + 1 + initCode.len) r1
    (by simp [initCode.hlen])
  obtain ⟨_, r3⟩ := hasAt_peel_deep (b' := env.innerBase + 1 + initCode.len + coreCode.len) r2
    (by simp [coreCode.hlen])
  obtain ⟨_, r4⟩ := hasAt_peel_deep
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len) r3
    (by simp [selectCode.hlen])
  obtain ⟨_, hDeepAt⟩ := hasAt_peel_deep
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len) r4
    (by simp [termCode.hlen])
  have hbEq : env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len = b := by
    dsimp only [b]; omega
  have hDeepAt' : p.HasAt b (dryDeepProcs { env with innerBase := b }) := by
    have h1 := hDeepAt
    change p.HasAt (env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len)
      (dryDeepProcs { env with
        innerBase := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len +
          termCode.len }) at h1
    rw [hbEq] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, dryDeepProcs, List.getElem_cons_zero] using
      hDeepAt' 0 (by rw [dryDeepProcs_length]; decide)
  · simpa only [dryDeepProcs, List.getElem_cons_succ, List.getElem_cons_zero] using
      hDeepAt' 1 (by rw [dryDeepProcs_length]; decide)
  · simpa only [dryDeepProcs, List.getElem_cons_succ, List.getElem_cons_zero] using
      hDeepAt' 2 (by rw [dryDeepProcs_length]; decide)
  · simpa only [dryDeepProcs, List.getElem_cons_succ, List.getElem_cons_zero] using
      hDeepAt' 3 (by rw [dryDeepProcs_length]; decide)
  · simpa only [dryDeepProcs, List.getElem_cons_succ, List.getElem_cons_zero] using
      hDeepAt' 4 (by rw [dryDeepProcs_length]; decide)
  · simpa only [dryDeepProcs, List.getElem_cons_succ, List.getElem_cons_zero] using
      hDeepAt' 5 (by rw [dryDeepProcs_length]; decide)

/-- Extracts all 6 procedure entries of `dryDeepCode` inside `dryLinkedProgram` with
`dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hasDeep (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode dryDeepCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
    let lay := dryTailLay Psc.sc inner
    let b := lay.shiftDeepChain
    let ops := mrdsCycleBase
    p.procs[b]? = some (shiftDeepChainBodyKFBL lay.scInit (lay.scOp 1) (lay.scOp 3) (lay.scOp 2)
        (b + 2) (lay.scOp 5) lay.lastInit (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
        (dryPathTreeOp ops 0) (b + 4) (b + 5) (ops + 69)) ∧
    p.procs[b + 1]? = some wireSuffixPackEditsBody ∧
    p.procs[b + 2]? = some (wireCoreLenBody (b + 3)) ∧
    p.procs[b + 3]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.procs[b + 4]? = some pathSlotBindBody ∧
    p.procs[b + 5]? = some (wireCanonCopyBody ops (ops + 4)) := by
  intro inner p lay b ops
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length))
  exact hasAt_dryInnerCodeSel_deep initCode coreCode selectCode termCode hInner

/-! ## 3. Helper lemmas for `SparseCoreForestCapAt` and `hLastImpl` -/

/-- Monotonicity of `SparseCoreForestCapAt` in `fcap`. -/
private theorem sparseCoreForestCapAt_mono {w L depth k M N vCap eCap capExp fcap₁ fcap₂ : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}
    (h : SparseCoreForestCapAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
      fcap₁ R p op)
    (hle : fcap₁ ≤ fcap₂) :
    SparseCoreForestCapAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
      fcap₂ R p op := by
  refine ⟨fun b a x args mem pos ω hargs hhead hrep hpre hfoot hz hroom => ?_⟩
  obtain ⟨body, hbody, o, st', c, x', hr, hrep', hF, hresp, hc⟩ :=
    h.op2_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hroom
  obtain ⟨fv, fe, hLw, hLSF, hfEnd, hfFoot, hstEnd, hE1, hE2, hfCap⟩ := hF
  exact ⟨body, hbody, o, st', c, x', hr, hrep',
    ⟨fv, fe, hLw, hLSF, hfEnd, hfFoot, hstEnd, hE1, hE2, hfCap.trans hle⟩, hresp, hc⟩

/-- Discharges `shiftDeepChainBody_meets_spec`'s last-level hypothesis for every connected graph `G`
with `G.m ≤ I.m`, `G.m ≤ levelM cfg.TP cfg.P cfg.P.d`, and `G.n ≤ G.m + 1`, at `dryLastMult J`,
`dryLastStretchP J`, and `fun _ _ => dryLastSpace J`. -/
theorem dryDeepCode_hLastImpl (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
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
    let G0 := namedInstance I
    let w := dryWordSize W allocationCoefficient allocationDegree source
    let p := dryLinkedProgram W Psc.sc inner
    let lay := dryTailLay Psc.sc inner
    ∀ G : MGraph, G.m ≤ I.m → G.m ≤ levelM cfg.TP cfg.P cfg.P.d → G.n ≤ G.m + 1 →
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation G0.n (initTargetCap cfg G0) 4 F.limbs
          F.fmt.precision G.E).Implements
        w p lay.lastInit lay.lastOp
        (lastLevelRuntimeMachineContract F.fmt F.limbs cfg.L G G0.n (initTargetCap cfg G0)
          (dryLastMult J) (dryLastStretchP J) (fun _ _ => dryLastSpace J)) := by
  intro W I V k F cfg G0 w p lay G hGmI hGmD hGnM hConn
  have hcapLim : G0.n + initTargetCap cfg G0 + 2 ≤ dryCapLimit W J :=
    dry_initTargetCap_le_capLimit J hJn hJm hCapPos
  refine lastLevelRuntime_implements_mono
    (dryLastLevel_implements (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) _ Psc.sc inner _ F.fmt G rfl hConn hGnM) ?_ ?_ ?_
  · exact packedLastLevelMultiplier_le_dryLastMultBound
      (le_trans hGnM (Nat.add_le_add_right hGmD 1)) hGmD
  · have hsz := Nat.size_le_size (Nat.add_le_add_right hGmI 1)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (G.m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size
    omega
  · intro args
    dsimp only [W] at hcapLim
    exact packedRuntimeAllocation_le_bound G lastGuest lastCanonConst
      (by omega) hGmI (by omega) (by omega) 1 args

/-! ## 4. Unconditional proof of `hDeepKFBL` for `dryDeepCode` -/

/-- **Unconditional proof of `hDeepKFBL` for `dryDeepCode` in `theorem_1_1_skeleton_kfbl_sel`:**
discharges `ShiftDeepChainSyncSpecWExtKFBL` at `drySCRep` and `dryInnerSizesWithSelect`
directly via `shiftDeepChainBody_meets_spec`, `drySC_coreKFBL`, `drySC_forestCap_level`,
and `dryDeepCode_hLastImpl`. -/
theorem dryDeepCode_hDeepKFBL (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode dryDeepCode
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
      DeepShiftOpsHypKFBL
        (w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        (L := F.limbs) (capExp := dryCapExp) (capLimit := dryCapLimit dryWitnessUsed J)
        (fcap := dryDeepFCap J) (lastMul := dryLastMult J)
        (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
        (deepSpace := s.deepSpace) (deepFixed := s.deepFixed) (toolMul := s.toolMul)
        (fmt := F.fmt) (cfg := cfg) (Psc := PscP)
        (allocation := drySCAlloc Psc dryCapExp limbMul J)
        (lastAlloc := fun _ _ => dryLastSpace J)
        (dryDeepRestartSpace Psc J)
        (dryDeepLevelSpace Psc J)
        (deepShiftLevelCost F.limbs dryCapExp cfg PscP) (dryLastSpace J) →
      ShiftDeepChainSyncSpecWExtKFBL
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) PscP.wordExp
        (dryLastStretchP J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
        G.n (initTargetCap cfg G) cfg Rcore
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryTailLay Psc.sc inner).shiftDeepChain
        s.deepSpace s.deepFixed s.toolMul s.treeMul := by
  intro inner source J hJn hJm hCost hCap hw
  dsimp only
  intro hOps
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
  let coeff := dryAllocCoeffConcrete Psc openSz hOpen selSz hSel
  let deg := dryAllocDegConcrete Psc openSz hOpen selSz hSel
  let w := dryWordSize W coeff deg source
  let p := dryLinkedProgram W Psc.sc inner
  let lay := dryTailLay Psc.sc inner
  let b := lay.shiftDeepChain
  let ops := mrdsCycleBase
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hWidth : F.fmt.precision ≤ 4 * F.limbs := by
    change ipmQualityPrecision I.m V k ≤ 4 * ipmQualityLimbs I.m V k
    unfold ipmQualityLimbs
    omega
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
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly W) ≤ coeff :=
    (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W)
      coeff deg hWordCoeff source J hJn hJm hCap1 hw
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
  have hOpsAt := solverOps_hasAt (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W)
        Psc.sc inner).length))
  have hInitH := solverOpsProcs_initHelpers hw14 hOpsAt
  have hEvalH := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl hOpsAt
  obtain ⟨hDeepAt, hPackAt, hCoreLenAt, hEdgeAt, hBindAt, hCanonAt⟩ :=
    dryInnerCodeSel_hasDeep Psc initCode coreCode selectCode termCode
  have hcapLim : G.n + initTargetCap cfg G + 2 ≤ dryCapLimit W J :=
    dry_initTargetCap_le_capLimit J hJn hJm hCap1
  have hCore : DeepShiftCoreKFBL F.fmt F.limbs I.m G.n (initTargetCap cfg G) dryCapExp cfg PscP
      (drySCAlloc Psc dryCapExp limbMul J)
      (drySCRep Psc coeff deg source J hw) p lay.scInit lay.scOp :=
    fun j hj H hH hHm => drySC_coreKFBL Psc inner coeff deg source J hJn hJm hCap1 hw j hj H hH hHm
  have hFCap : DeepShiftForestCapKFBL F.fmt F.limbs G.n (initTargetCap cfg G) dryCapExp cfg PscP
      (drySCAlloc Psc dryCapExp limbMul J) (dryDeepFCap J)
      (drySCRep Psc coeff deg source J hw) p lay.scOp := by
    intro j hj H hH
    have h1 := drySC_forestCap_level Psc inner coeff deg source J hJn hJm hCap1 hw j hj
      G.n (initTargetCap cfg G) hcapLim H hH
    refine sparseCoreForestCapAt_mono h1 ?_
    unfold dryDeepFCap dynGraphSize
    dsimp only
    have hsq : (G.n + initTargetCap cfg G + 2) ^ 2 ≤ (dryCapLimit W J) ^ 2 :=
      Nat.pow_le_pow_left hcapLim 2
    dsimp only [W] at hcapLim hsq
    omega
  have hBindHasAt : p.HasAt (b + 4) [pathSlotBindBody] := by
    intro idx hidx
    have h0 : idx = 0 := by simp at hidx; omega
    subst h0; simpa using hBindAt
  refine ShiftDeepChainSyncSpecWExtKFBL.mono_treeMul ?_ (Nat.le_add_right _ _)
  exact shiftDeepChainBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (drainUnit := detectOffTreeDrainUnit F.limbs) (capExp := dryCapExp) (limbMul := limbMul)
    (wordExp := PscP.wordExp) (stretchPrec := dryLastStretchP J) (lastMul := dryLastMult J)
    (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
    (deepSpace := (dryInnerSizesWithSelect Psc openSz selSz source J).deepSpace)
    (deepFixed := (dryInnerSizesWithSelect Psc openSz selSz source J).deepFixed)
    (toolMul := (dryInnerSizesWithSelect Psc openSz selSz source J).toolMul)
    (vCap := G.n) (eCap := initTargetCap cfg G) (capLimit := dryCapLimit W J)
    (fcap := dryDeepFCap J) (restartSpace := dryDeepRestartSpace Psc J)
    (lastSpace := dryLastSpace J)
    (shiftDeepChainProc := b) (initCore := lay.scInit) (coreLenProc := b + 2)
    (edgeProc := b + 3) (signExt := ops + 17) (mul := ops + 11) (intDiv := ops + 22)
    (copy := ops) (lastInit := lay.lastInit) (packEditsProc := b + 1)
    (initTree := ops + 81) (bind := b + 4) (canonCopy := b + 5) (isNeg := ops + 69)
    (fmt := F.fmt) (cfg := cfg) (Psc := PscP)
    (allocation := drySCAlloc Psc dryCapExp limbMul J)
    (lastAlloc := fun _ _ => dryLastSpace J)
    (Rcore := drySCRep Psc coeff deg source J hw) (p := p)
    (opCore := lay.scOp) (opLast := lay.lastOp) (opTree := dryPathTreeOp ops)
    (dryDeepLevelSpace Psc J) (deepShiftLevelCost F.limbs dryCapExp cfg PscP)
    hDeepAt hPackAt
    (drySCRep_local Psc coeff deg source J hw)
    rfl rfl hWidth hL4W hw17 cfg.P.hk hkW hdW hN0W hDepthW
    (sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _)
    rfl hCore hFCap hcapLim
    (dryDeepCode_hLastImpl Psc inner coeff deg source J hJn hJm hCap1 hw)
    hCoreLenAt hEdgeAt hInitH.2.2.2.2.1 hInitH.2.2.1 hInitH.2.2.2.2.2.2.1 hInitH.1
    hEvalH.2.2.2.2.2 (pathSlotBind_meetsContract hBindHasAt)
    (fun v => wireCanonCopy_meetsContract v hCanonAt hEvalH.1 hEvalH.2.2.1)
    hEvalH.2.2.2.2.1 hOps

end MinCostFlow.Final.DryRun

end
