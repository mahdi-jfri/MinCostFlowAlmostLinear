module

public import MinCostFlow.Final.AssemblyDryRunSCDeepCode
public import MinCostFlow.Final.AssemblyDryRunSCInit
import Mathlib.Tactic

/-!
# Relocatable `initConcrete` block for `dryInnerCodeSel` (`AssemblyDryRunSCInitCode`)

Packages `dryInitConcreteProcs` (`AssemblyDryRunSCInit.lean`, length 20: `initConcreteBody`,
`buildSortedEndsBody`, `wireCoreLenBody`, `wireCoreLenEdgeBody`, `pathSlotBindBody`, and the 15
dynamic-graph initialization procedures) together with a parameter-setup `SolverInnerSubCode`
block `paramCode` into a relocatable `SolverInnerSubCode` block `dryInitCode paramCode` for
`dryInnerCodeSel`.

Provides:
* `dryInitCode`: relocatable `SolverInnerSubCode` (`len = dryInitConcreteLen + paramCode.len`,
  `off = 0`, deterministic whenever `paramCode` is deterministic).
* `dryInnerCodeSel_hasInit`: extracts `dryInitConcreteProcs` at `lay.initConcrete` inside
  `dryLinkedProgram` with `dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode
  deepCode`.
* `dryInitCode_hInitConcrete`: discharges `OrdInitConcreteSpecW` at `lay.initConcrete` inside
  `dryLinkedProgram` with `dryInnerCodeSel` (the exact `hInitConcrete` hypothesis of
  `theorem_1_1_skeleton_kfbl_sel`, `theorem_1_1_skeleton_kfbl_sel_deep`, and
  `theorem_1_1_skeleton_kfbl_sel_deep_select`), reusing `dryInitConcrete_meets_spec`'s exact
  bridge hypotheses (`paramSetup`, `hCoreImpl`, `hLastImpl`, `hCoreLenFits`, `hLastStretchFits`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Relocatable `SolverInnerSubCode` block `dryInitCode` -/

/-- Relocatable `SolverInnerSubCode` placing `dryInitConcreteProcs` at `env.innerBase` (length `20`,
entry at offset `0`) followed by `paramCode` at `env.innerBase + 20`. -/
def dryInitCode (paramCode : SolverInnerSubCode) : SolverInnerSubCode where
  procs env :=
    dryInitConcreteProcs env (env.innerBase + dryInitConcreteLen + paramCode.off) ++
      paramCode.procs { env with innerBase := env.innerBase + dryInitConcreteLen }
  len := dryInitConcreteLen + paramCode.len
  hlen env := by
    rw [List.length_append, dryInitConcreteProcs_length, paramCode.hlen]
  hnoRand env s hs := by
    rcases List.mem_append.mp hs with h | h
    · exact dryInitConcreteProcs_noRand _ _ s h
    · exact paramCode.hnoRand _ s h
  off := 0

/-- Absolute procedure index of `paramCode` inside `dryLinkedProgram` with
`dryInnerCodeSel (dryInitCode paramCode) ...`. -/
def dryInitParamProc (sc : SparseCoreCode)
    (paramCode coreCode selectCode termCode deepCode : SolverInnerSubCode) : ℕ :=
  let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
  (dryTailLay sc inner).initConcrete + dryInitConcreteLen + paramCode.off

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Placement inside `dryLinkedProgram` with `dryInnerCodeSel` -/

private theorem hasAt_peel_initSel {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

private theorem hasAt_dryInnerCodeSel_init {p : Program} {env : SolverInnerEnv}
    (paramCode coreCode selectCode termCode deepCode : SolverInnerSubCode)
    (hInner : p.HasAt env.innerBase
      ((dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode).procs env)) :
    let b := env.innerBase + 1 + 0
    let ops := env.opsBase
    let paramProc := b + dryInitConcreteLen + paramCode.off
    p.procs[b]? = some (initConcreteBody (b + 17 + dgIdxInitFromLists) paramProc (b + 1)
        env.scInit (env.scOp 3) (env.scOp 2) (b + 2) (env.scOp 5)
        env.lastInit (env.lastOp 0) (ops + 81) (ops + 81 + 1)
        (b + 4) (ops + 20) (ops + 16) (ops + 4) ops) ∧
    p.procs[b + 1]? = some buildSortedEndsBody ∧
    p.procs[b + 2]? = some (wireCoreLenBody (b + 3)) ∧
    p.procs[b + 3]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    ∀ {w : ℕ},
      MeetsContract w p (b + 4) (pathSlotBindContract w) ∧
      ∀ vCap eCap G vL eEdges,
        MeetsContract w p (b + 17 + dgIdxInitFromLists)
          (dgInitFromListsContract w vCap eCap G vL eEdges) := by
  intro b ops paramProc
  unfold dryInnerCodeSel at hInner
  dsimp only at hInner
  obtain ⟨_, r1⟩ := hasAt_peel_initSel (b' := env.innerBase + 1) hInner (by simp)
  have hInitSub := Num.hasAt_append_left r1
  unfold dryInitCode at hInitSub
  dsimp only at hInitSub
  have hInitBlock := Num.hasAt_append_left hInitSub
  have hbEq : env.innerBase + 1 = b := rfl
  have hBase := dryInitConcreteProcs_hasAt (w := 0) hInitBlock
  refine ⟨?_, ?_, ?_, ?_, fun {w} => ?_⟩
  · simpa only [hbEq, paramProc, ops] using hBase.1
  · simpa only [hbEq] using hBase.2.1
  · simpa only [hbEq] using hBase.2.2.1
  · simpa only [hbEq, ops] using hBase.2.2.2.1
  · have hW := dryInitConcreteProcs_hasAt (w := w) hInitBlock
    exact ⟨by simpa only [hbEq] using hW.2.2.2.2.1,
      fun vCap eCap G vL eEdges => by simpa only [hbEq] using hW.2.2.2.2.2 vCap eCap G vL eEdges⟩

/-- Placement of `dryInitConcreteProcs` at `lay.initConcrete` inside `dryLinkedProgram` with
`dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode`. -/
theorem dryInnerCodeSel_hasInit (Psc : DrySparseCorePieces)
    (paramCode coreCode selectCode termCode deepCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
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
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length))
  have h := hasAt_dryInnerCodeSel_init paramCode coreCode selectCode termCode deepCode hInner
  refine ⟨?_, ?_, ?_, ?_, fun {w} => ⟨?_, fun vCap eCap G vL eEdges => ?_⟩⟩
  · simpa only [inner, p, lay, b, ops, paramProc, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using h.1
  · simpa only [inner, p, lay, b, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using h.2.1
  · simpa only [inner, p, lay, b, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using h.2.2.1
  · simpa only [inner, p, lay, b, ops, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using h.2.2.2.1
  · simpa only [inner, p, lay, b, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using
      (h.2.2.2.2 (w := w)).1
  · simpa only [inner, p, lay, b, dryLinkedProgram, dryTailLay, solverTailLayout,
      solverTailInnerEnv, dryInnerCodeSel, dryInitCode, Nat.add_zero, Nat.add_assoc] using
      (h.2.2.2.2 (w := w)).2 vCap eCap G vL eEdges

private theorem initCode_ipmQuality_arith (m V k : ℕ) :
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

private theorem initCode_cfg_eps_eq (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    (concreteCirculationCfgWithLast dryWitnessUsed J).ε =
      ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P := by
  intro I V k P epsExp
  have hle : epsExp ≤ P := (initCode_ipmQuality_arith I.m V k).2.2.2.1
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

/-! ## 3. Discharging `hInitConcrete` for `dryInnerCodeSel` -/

private lemma initCode_capTree_lt
    (I : Instance) (V k : ℕ) {w : ℕ} (hw : ipmQualityParameterWordBits I.m V k ≤ w)
    (h2n1Le : 2 * (namedInstance I).n + 1 ≤ 4 * I.m + 5) :
    let F := ipmQualityMinRatioFormat I.m V k hw
    2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) <
      (Num.capacity 4 F.limbs : ℤ) := by
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
/-- Discharges `OrdInitConcreteSpecW` at `lay.initConcrete` inside `dryLinkedProgram` with
`dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode`, for a single
dry-run input `(source, J)`. -/
theorem dryInitCode_meets_spec
    (Psc : DrySparseCorePieces)
    (paramCode coreCode selectCode termCode deepCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz)
    (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
    (hParam :
      let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      MeetsContract
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryInitParamProc Psc.sc paramCode coreCode selectCode termCode deepCode)
        (initParamSetupContract
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          I.m V F.limbs F.fmt.precision cfg.P.d cfg.P.k ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) cfg.N₀
          (Expander.chosenL (cfg.P.M₀ ^ 2)) (levelM cfg.TP cfg.P)
          (dryParamSpace source J) (dryParamCost source J)))
    (hCoreImpl :
      let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let lay := dryTailLay Psc.sc inner
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d,
          Rcore.Implements
            (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
              (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
            (dryLinkedProgram dryWitnessUsed Psc.sc inner) lay.scInit lay.scOp
            (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
              cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G)
              dryCapExp (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
          SparseCoreReadoutFootAt F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
            cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G)
            dryCapExp (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
            Rcore (dryLinkedProgram dryWitnessUsed Psc.sc inner) lay.scOp)
    (hLastImpl :
      let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let lay := dryTailLay Psc.sc inner
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          (LastLevelProgram.lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision
            (chain.G cfg.P.d).E).Implements
            (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
              (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
            (dryLinkedProgram dryWitnessUsed Psc.sc inner) lay.lastInit lay.lastOp
            (lastLevelRuntimeMachineContract F.fmt F.limbs cfg.L (chain.G cfg.P.d) vc ec
              (dryLastMult J) (dryLastStretchP J) (fun _ _ => dryLastSpace J)))
    (hCoreLenFits :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        (∀ e ∈ G.E, ∃ q₀ : ℤ, (q₀ : ℝ) / (2 : ℝ) ^ F.fmt.precision = ℓ₀ e) →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 F.limbs q ∧ (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e)
    (hLastStretchFits :
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
          2 * (2 : ℝ) ^ dryLastStretchP J *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs)
    (hInitSpaceLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
      ∀ i < cfg.P.d, ∀ g l gr o h,
        drySCAlloc Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J 6
          [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P i, cfg.N₀, F.limbs, F.fmt.precision, depth, h] ≤
        dryCoreInitSpace Psc J i) :
    let inner := dryInnerCodeSel (dryInitCode paramCode) coreCode selectCode termCode deepCode
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
    let s := dryInnerSizesWithSelect Psc openSz selSz source J
    OrdInitConcreteSpecW
      (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
      F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10)
      cfg Rcore (namedInstance I)
      (dryLinkedProgram dryWitnessUsed Psc.sc inner)
      (dryTailLay Psc.sc inner).initConcrete
      s.B_tree dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
      (dryCapLimit dryWitnessUsed J)
      (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
      s.initSpace' s.initFixed s.toolMul := by
  intro inner I V k F cfg Rcore s
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
  let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
  let lay := dryTailLay Psc.sc inner
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  let PscP := drySCParams Psc dryCapExp limbMul
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
  have hArith := initCode_ipmQuality_arith I.m V k
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : (namedInstance I).IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hGE : (namedInstance I).E = Finset.range I.m := rfl
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hVlt : ∀ v ∈ (namedInstance I).V, v < (namedInstance I).n := fun v hv => by
    rw [hInEq]; exact Finset.mem_range.mp hv
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have heCapEq : initRootECap cfg.N₀ cfg.P.k I.m = initTargetCap cfg (namedInstance I) :=
    initRootECap_eq_initTargetCap rfl hImPos rfl (le_max_left _ _)
  have hcap0 : (namedInstance I).n + initRootECap cfg.N₀ cfg.P.k I.m + 2 ≤ dryCapLimit dryWitnessUsed J :=
    heCapEq.symm ▸ dry_initTargetCap_le_capLimit J hJn hJm hCap
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
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap hw
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
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
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
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap i hi.le 0 0 (by omega)).2
    have h1 := Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hSCWordCoeff source J hJn hJm hCap hw
      1 (by decide) i _ hL
    have hle : levelM cfg.TP cfg.P i ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 1 * (F.limbs + 1) := by
      rw [pow_one]; exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    exact lt_of_le_of_lt hle h1
  have hOps := solverOpsProcs_initHelpers hw14
    (solverOps_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)
      (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
      Psc.sc inner
      (dynLctForestBodies 4 (mrdsCycleBase +
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)))
  obtain ⟨h0, h1, h2, h3, h45⟩ :=
    dryInnerCodeSel_hasInit Psc paramCode coreCode selectCode termCode deepCode
  obtain ⟨hBind, hDgInit⟩ := h45 (w := w)
  have hLastReadout : p.procs[lay.lastOp 0]? = some LastLevelProgram.readoutBody :=
    packedLastLevelBodies_readout_at
      (solverCycle_lastLevel_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed)
        (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
          (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
            (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
        _ _ _ Psc.sc inner _)
  have hCapTree : 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) * s.B_tree <
      (Num.capacity 4 F.limbs : ℤ) :=
    initCode_capTree_lt I V k hw h2n1Le
  have hCoreSpec := initConcreteBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (E := F.rangeExponent) (m := I.m) (V := V)
    (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (capExp := dryCapExp) (limbMul := limbMul) (capLimit := dryCapLimit dryWitnessUsed J)
    (initConcreteProc := lay.initConcrete)
    (graphPack := lay.initConcrete + 17 + dgIdxInitFromLists)
    (paramSetup := dryInitParamProc Psc.sc paramCode coreCode selectCode termCode deepCode)
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
    hVcfg hGV hGE hVlt hmG hnG hcap0 hEΨ (initCode_cfg_eps_eq J) hεPos hεLe
    (le_refl _) hCapTree cfg.P.hd hw14 hwk h4M3W hfit.2.2.2.2.2.2.2 hfit.2.2.1 hDW hsearchW
    hArith.2.1 hArith.2.2.1 hArith.2.2.2.1 hArith.2.2.2.2 hvw hwidthN hMw
    (hDgInit _ _ _ _ _) hParam h1 h2 h3
    hOps.2.2.2.2.1 hOps.2.2.1 hOps.2.2.2.2.2.2.1 hOps.2.2.2.2.2.1 hOps.2.2.2.1 hOps.2.1 hOps.1
    hBind hOps.2.2.2.2.2.2.2
    (fun ℓ₀ g₀ hL i hi => by rw [heCapEq]; exact hCoreImpl ℓ₀ g₀ hL i hi)
    hLastImpl hLastReadout (fun _ => le_refl _) hInitSpaceLe hCoreLenFits hLastStretchFits
  exact ordInitConcreteSpecW_mono hCoreSpec (Nat.le_add_right _ _) (Nat.le_add_right _ _) (by
    dsimp only [s, PscP, limbMul, dryInnerSizesWithSelect, dryToolMul, deepShiftToolMulBound]; omega)

end MinCostFlow.Final.DryRun

end
