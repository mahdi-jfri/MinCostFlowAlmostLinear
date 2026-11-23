module

public import MinCostFlow.Final.AssemblyDryRunSCInitSpace
public import MinCostFlow.MinRatio.WireEval
public import MinCostFlow.MinRatio.WireShiftTerm
import MinCostFlow.LinkCut.PathProg.Implements
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Concrete `evalCycle` and `shiftTermChain` packaging (`AssemblyDryRunSCRem`)

Packages the five other solver inner-level procedures into `SolverInnerOpenNoParam`:
* `evalCycle` (`MinRatio/WireEval.lean`, `evalCycleBody`) and `shiftTermChain`
  (`MinRatio/WireShiftTerm.lean`, `shiftTermChainBody`, together with its two local helpers
  `pathSlotBindBody` and `wireCanonCopyBody`) are installed concretely at offsets `0..3`;
* the three procedures `ordChainCore`, `selectRoute` and `shiftDeepChain`
  are parameterized as relocatable deterministic blocks (`SolverInnerSubCode`).

Provides:
* `SolverInnerSubCode`, `dryEvalTermProcs`, `dryInnerRem`, and `dryInnerRem_isDeterministic`;
* `dryInnerRem_hasEvalTerm` and `solverOpsProcs_evalTermHelpers` (extracting `copyWords`, `add`,
  `negate`, `subtract`, `isNegative`, and `pathTree_implements` from `solverOpsProcs`);
* `ordCycleRouteEvalSpecW_mono` and `drySC_hEval_proved`: proves `DrySCSolverHyps.hEval` inside
  `dryLinkedProgram` with `dryInnerRem`, reducing it to two plain inequalities on `sz`
  (`evalCycleSpace ≤ s.evalSpace` and `evalCycleBudget ≤ s.evalBudget`);
* `shiftTermChainSyncSpecWExt_mono` and `drySC_hTermExt_proved`: proves `ShiftTermChainSyncSpecWExt`
  for `shiftTermChainBody` inside `dryLinkedProgram` with `dryInnerRem`, reducing it to three plain
  inequalities on `sz` (`lastTreeCap * (2 + wireTreeSyncEditSpace L) ≤ s.termSpace`,
  `41 * lastTreeCap + 320 ≤ s.termFixed`, and `wireTreeSyncEditCost L drainUnit + 2 ≤ s.treeMul`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## Parameterized sub-module blocks and concrete `SolverInnerOpenNoParam` -/

/-- Relocatable deterministic procedure block of fixed length for one of the parameter
inner-level solver procedures (`ordChainCore`, `selectRoute`, or `shiftDeepChain`). -/
structure SolverInnerSubCode where
  procs : SolverInnerEnv → List Stmt
  len : ℕ
  hlen : ∀ env, (procs env).length = len
  hnoRand : ∀ env, ∀ s ∈ procs env, s.NoRand
  off : ℕ

/-- Fixed length (`4`) of `dryEvalTermProcs`. -/
def dryEvalTermLen : ℕ := 4

/-- Procedure-index dispatch for the Section 6 path tree inside `solverOpsProcs` at `ops`. -/
def dryPathTreeOp (ops : ℕ) (i : ℕ) : ℕ := ops + 81 + 1 + i

/-- Concrete deterministic procedure block of length `4` placed at `env.innerBase` inside
`SolverInnerOpenNoParam`, implementing:
* `b + 0`: `evalCycleBody` (`OrdCycleRouteEvalSpecW`, calling `opTree 3`, `Num.add`, `Num.subtract`);
* `b + 1`: `shiftTermChainBody` (`ShiftTermChainSyncSpecWExt`, calling `opTree 4, 1, 0`,
  `pathSlotBindBody`, `wireCanonCopyBody`, `Num.isNegative`);
* `b + 2`: `pathSlotBindBody`;
* `b + 3`: `wireCanonCopyBody` (calling `copyWords`, `Num.negate`). -/
def dryEvalTermProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [evalCycleBody (dryPathTreeOp ops 3) (ops + 2) (ops + 6),
   shiftTermChainBody (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
     (b + 2) (b + 3) (ops + 69),
   pathSlotBindBody,
   wireCanonCopyBody ops (ops + 4)]

theorem dryEvalTermProcs_length (env : SolverInnerEnv) :
    (dryEvalTermProcs env).length = dryEvalTermLen := rfl

theorem dryEvalTermProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ dryEvalTermProcs env, s.NoRand := by
  intro s hs
  unfold dryEvalTermProcs at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact evalCycleBody_noRand _ _ _
  · exact shiftTermChainBody_noRand _ _ _ _ _ _
  · simp [pathSlotBindBody, Stmt.NoRand]
  · exact wireCanonCopyBody_noRand _ _

/-- Builds `SolverInnerOpenNoParam` with concrete `evalCycle` (`0`) and `shiftTermChain` (`1`),
and parameterized blocks for `ordChainCore`, `selectRoute`, and `shiftDeepChain`. -/
def dryInnerRem (coreCode selectCode deepCode : SolverInnerSubCode) : SolverInnerOpenNoParam where
  procs env :=
    let b := env.innerBase
    dryEvalTermProcs env ++
      (coreCode.procs { env with innerBase := b + dryEvalTermLen } ++
      (selectCode.procs { env with innerBase := b + dryEvalTermLen + coreCode.len } ++
       deepCode.procs { env with innerBase := b + dryEvalTermLen + coreCode.len + selectCode.len }))
  len := dryEvalTermLen + coreCode.len + selectCode.len + deepCode.len
  hlen env := by
    simp only [List.length_append, dryEvalTermProcs_length, coreCode.hlen, selectCode.hlen,
      deepCode.hlen]
    omega
  evalCycleOff := 0
  shiftTermChainOff := 1
  ordChainCoreOff := dryEvalTermLen + coreCode.off
  selectRouteOff := dryEvalTermLen + coreCode.len + selectCode.off
  shiftDeepChainOff := dryEvalTermLen + coreCode.len + selectCode.len + deepCode.off

/-- Determinism of `dryInnerRem coreCode selectCode deepCode` from the parts. -/
theorem dryInnerRem_isDeterministic (coreCode selectCode deepCode : SolverInnerSubCode) :
    (dryInnerRem coreCode selectCode deepCode).IsDeterministic := by
  intro env s hs
  unfold dryInnerRem at hs
  simp only [List.mem_append] at hs
  rcases hs with h1 | h2 | h3 | h4
  · exact dryEvalTermProcs_noRand env s h1
  · exact coreCode.hnoRand _ s h2
  · exact selectCode.hnoRand _ s h3
  · exact deepCode.hnoRand _ s h4

/-! ## Placement and helper-contract extraction inside `dryLinkedProgram` -/

private theorem hasAt_peel_rem {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Extracts `copyWords`, `Num.add`, `Num.negate`, `Num.subtract`, `Num.isNegative`, and the
Section 6 path-tree `Implements` statement from `solverOpsProcs` at `base` (for `14 ≤ w`). -/
theorem solverOpsProcs_evalTermHelpers {w base chainRefreshProc findCycleProc shiftLevelProc L : ℕ}
    {fmt : Num.Format w} {p : Program} (hw : 14 ≤ w) (hfmt4 : fmt.limbBits = 4)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc)) :
    MeetsContract w p base (copyWordsContract w) ∧
    MeetsContract w p (base + 2) (Num.addContract w 4) ∧
    MeetsContract w p (base + 4) (Num.negateContract w 4) ∧
    MeetsContract w p (base + 6) (Num.subtractContract w 4) ∧
    MeetsContract w p (base + 69) (Num.isNegativeContract w 4) ∧
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p (base + 81)
      (dryPathTreeOp base)
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)) := by
  have hw1 : 1 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hbase4 : Num.base 4 < 2 ^ w := by
    change 2 ^ 4 < 2 ^ w; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hw10 : 2 * 4 + 2 ≤ w := by omega
  unfold solverOpsProcs at hp
  obtain ⟨hmCopyW, r1⟩ := hasAt_peel_rem (b' := base + 1) hp (by change base + 1 = base + 1; rfl)
  obtain ⟨_, r2⟩ := hasAt_peel_rem (b' := base + 2) r1 (by change base + 1 + 1 = base + 2; omega)
  obtain ⟨hmAdd, r3⟩ := hasAt_peel_rem (b' := base + 4) r2 (by change base + 2 + 2 = base + 4; omega)
  obtain ⟨hmNeg, r4⟩ := hasAt_peel_rem (b' := base + 6) r3 (by change base + 4 + 2 = base + 6; omega)
  obtain ⟨hmSub, r5⟩ := hasAt_peel_rem (b' := base + 11) r4 (by change base + 6 + 5 = base + 11; omega)
  obtain ⟨_, r6⟩ := hasAt_peel_rem (b' := base + 16) r5 (by change base + 11 + 5 = base + 16; omega)
  obtain ⟨_, r7⟩ := hasAt_peel_rem (b' := base + 48) r6 (by change base + 16 + 32 = base + 48; omega)
  obtain ⟨_, r8⟩ := hasAt_peel_rem (b' := base + 59) r7 (by change base + 48 + 11 = base + 59; omega)
  obtain ⟨_, r9⟩ := hasAt_peel_rem (b' := base + 64) r8 (by change base + 59 + 5 = base + 64; omega)
  obtain ⟨_, r10⟩ := hasAt_peel_rem (b' := base + 69) r9 (by change base + 64 + 5 = base + 69; omega)
  obtain ⟨hmIsNeg, r11⟩ := hasAt_peel_rem (b' := base + 70) r10 (by change base + 69 + 1 = base + 70; omega)
  obtain ⟨_, r12⟩ := hasAt_peel_rem (b' := base + 73) r11 (by change base + 70 + 3 = base + 73; omega)
  obtain ⟨_, r13⟩ := hasAt_peel_rem (b' := base + 77) r12 (by change base + 73 + 4 = base + 77; omega)
  obtain ⟨_, r14⟩ := hasAt_peel_rem (b' := base + 80) r13 (by change base + 77 + 3 = base + 80; omega)
  obtain ⟨_, r15⟩ := hasAt_peel_rem (b' := base + 81) r14 (by change base + 80 + 1 = base + 81; omega)
  obtain ⟨hmTree, _⟩ := hasAt_peel_rem (b' := base + 145) r15 (by change base + 81 + 64 = base + 145; omega)
  have hTreeImpl := LinkCut.PathProg.pathTree_implements fmt L (by omega) (by omega) (hfmt4.symm ▸ hmTree)
  rw [hfmt4] at hTreeImpl
  exact ⟨copyWords_meetsContract hmCopyW,
    Num.add_meetsContract (by decide) hw10 hmAdd,
    Num.negate_meetsContract hw1 hbase4 hmNeg,
    Num.subtract_meetsContract (by decide) hw10 hmSub,
    Num.isNegative_meetsContract (by decide) hw1 hbase4 hmIsNeg,
    hTreeImpl⟩

/-- Placement of `evalCycleBody`, `shiftTermChainBody`, `pathSlotBindBody`, and `wireCanonCopyBody`
inside `dryLinkedProgram` when `dryInnerRem coreCode selectCode deepCode` is installed. -/
theorem dryInnerRem_hasEvalTerm (Psc : DrySparseCorePieces)
    (coreCode selectCode deepCode : SolverInnerSubCode) :
    let rem := dryInnerRem coreCode selectCode deepCode
    let inner := rem.toSolverInnerOpen.toInnerCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
    let lay := dryTailLay Psc.sc inner
    let bRem := lay.innerBase + dryInitConcreteLen
    let ops := mrdsCycleBase
    p.procs[lay.evalCycle]? =
      some (evalCycleBody (dryPathTreeOp ops 3) (ops + 2) (ops + 6)) ∧
    p.procs[lay.shiftTermChain]? =
      some (shiftTermChainBody (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
        (bRem + 2) (bRem + 3) (ops + 69)) ∧
    p.HasAt (bRem + 2) [pathSlotBindBody] ∧
    p.procs[bRem + 3]? = some (wireCanonCopyBody ops (ops + 4)) := by
  intro rem inner p lay bRem ops
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length))
  have hTail1 := Num.hasAt_append_right hInner
  rw [dryInitConcreteProcs_length] at hTail1
  have hRem := Num.hasAt_append_left hTail1
  have hET : p.HasAt bRem (dryEvalTermProcs
      { (solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst Psc.sc
          solverTailBase) with innerBase := bRem }) :=
    Num.hasAt_append_left hRem
  have hEvalIdx : lay.evalCycle = bRem := by
    change lay.innerBase + (dryInitConcreteLen + 0) = lay.innerBase + dryInitConcreteLen
    omega
  have hTermIdx : lay.shiftTermChain = bRem + 1 := by
    change lay.innerBase + (dryInitConcreteLen + 1) = lay.innerBase + dryInitConcreteLen + 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEvalIdx]; exact hET.head
  · rw [hTermIdx]; exact hET.get (i := 1) (by simp [dryEvalTermProcs])
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [dryEvalTermProcs] using hET.get (i := 2) (by simp [dryEvalTermProcs])
  · exact hET.get (i := 3) (by simp [dryEvalTermProcs])

/-! ## Monotonicity and dry-run proof of `hEval` (`OrdCycleRouteEvalSpecW`) -/

/-- Monotonicity of `OrdCycleRouteEvalSpecW` in `evalSpace` and `evalBudget`. -/
theorem ordCycleRouteEvalSpecW_mono {w L P m V psi k epsExp drainUnit evalCycleProc
    sp₁ sp₂ bud₁ bud₂ maxEdges maxPaths : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (h : OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p evalCycleProc
      sp₁ bud₁ maxEdges maxPaths)
    (hsp : sp₁ ≤ sp₂) (hbud : bud₁ ≤ bud₂) :
    OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p evalCycleProc
      sp₂ bud₂ maxEdges maxPaths := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun root edgesBase pathsBase workHeap pos ω mem model tok B R edges paths
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hroom => ?_⟩
  obtain ⟨nh, c, out, tok', inner, norm, hr, hlo, hhi, hlv, hic, hnorm, hin, hno, hinnerEq,
      hlnormEq, htEd, htPt, ht18, hrep', hmeta', hnum', hoff', hbd', hz, hfr, hft, hc⟩ :=
    hrun root edgesBase pathsBase workHeap pos ω mem model tok B R edges paths
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
      (lt_of_le_of_lt (Nat.add_le_add_left hsp workHeap) hroom)
  exact ⟨nh, c, out, tok', inner, norm, hr, hlo, le_trans hhi (Nat.add_le_add_left hsp workHeap),
    hlv, hic, hnorm, hin, hno, hinnerEq, hlnormEq, htEd, htPt, ht18, hrep', hmeta', hnum', hoff', hbd',
    hz, hfr, hft, le_trans hc (Nat.add_le_add_right hbud _)⟩

/-- **Dry-run proof of `hEval` (`OrdCycleRouteEvalSpecW`)**: discharges `DrySCSolverHyps.hEval`
in `dryLinkedProgram` with `dryInnerRem coreCode selectCode deepCode` directly from
`evalCycleBody_meets_spec`, taking only the two plain size inequalities on `sz`. -/
theorem drySC_hEval_proved (Psc : DrySparseCorePieces)
    (coreCode selectCode deepCode : SolverInnerSubCode)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hEvalSpace : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleSpace F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalSpace)
    (hEvalBudget : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        evalCycleBudget F.limbs (sz source J).maxEdges (sz source J).maxPaths ≤
          (sz source J).evalBudget) :
    let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
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
        s.evalSpace s.evalBudget s.maxEdges s.maxPaths := by
  intro openInner source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let inner := openInner.toInnerCode
  have hw14 : 14 ≤ dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source :=
    (ipm_quality_parameter_words_fit I.m V k hw).1
  have hOps := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl
    (solverOps_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)
      (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
      Psc.sc inner
      (dynLctForestBodies 4 (mrdsCycleBase +
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)))
  obtain ⟨hEvalAt, _, _, _⟩ := dryInnerRem_hasEvalTerm Psc coreCode selectCode deepCode
  have hSpec := evalCycleBody_meets_spec
    (w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
    (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (initTree := mrdsCycleBase + 81) (opTree := dryPathTreeOp mrdsCycleBase)
    (numAdd := mrdsCycleBase + 2) (numSub := mrdsCycleBase + 6)
    (maxEdges := (sz source J).maxEdges) (maxPaths := (sz source J).maxPaths)
    (fmt := F.fmt) (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw)
    (drySCRepAt_local Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) _ _ source J hw)
    rfl (le_trans (by decide : 10 ≤ 14) hw14) hEvalAt hOps.2.2.2.2.2 hOps.2.1 hOps.2.2.2.1
  exact ordCycleRouteEvalSpecW_mono hSpec
    (hEvalSpace source J hJn hJm hCost hCap hw)
    (hEvalBudget source J hJn hJm hCost hCap hw)

/-! ## Monotonicity and dry-run proof of `hTermExt` (`ShiftTermChainSyncSpecWExt`) -/

/-- Monotonicity of `ShiftTermChainSyncSpecWExt` in `termSpace`, `termFixed`, `toolMul`, `treeMul`. -/
theorem shiftTermChainSyncSpecWExt_mono {w L P m V psi k epsExp drainUnit capExp limbMul capLimit
    lastTreeCap shiftTermChainProc sp₁ sp₂ fix₁ fix₂ tm₁ tm₂ tr₁ tr₂ : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (h : ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      lastTreeCap cfg Rcore p shiftTermChainProc sp₁ fix₁ tm₁ tr₁)
    (hsp : sp₁ ≤ sp₂) (hfix : fix₁ ≤ fix₂) (htm : tm₁ ≤ tm₂) (htr : tr₁ ≤ tr₂) :
    ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      lastTreeCap cfg Rcore p shiftTermChainProc sp₂ fix₂ tm₂ tr₂ := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun root heap pos ω mem0 mem model tok B R
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hroom => ?_⟩
  obtain ⟨nh, c, out, tok', hr, hlo, hhi, hlv, hic, hrep', hmeta', hnum', hoff', hbd', hz, hfr, hft, hc⟩ :=
    hrun root heap pos ω mem0 mem model tok B R
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
      (lt_of_le_of_lt (Nat.add_le_add_left hsp heap) hroom)
  have h1' := Nat.mul_le_mul_right
    ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalRuntime - model.chain.totalRuntime) htm
  have h2' := Nat.mul_le_mul_right
    ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalTreeUpdates - model.chain.totalTreeUpdates) htr
  exact ⟨nh, c, out, tok', hr, hlo, le_trans hhi (Nat.add_le_add_left hsp heap),
    hlv, hic, hrep', hmeta', hnum', hoff', hbd', hz, hfr, hft,
    le_trans hc (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hfix h1') h2') _)⟩

/-- **Dry-run proof of `ShiftTermChainSyncSpecWExt` for `shiftTermChainBody`**: discharges all
code, contract, path-tree, format, and word-size hypotheses of `shiftTermChainBody_meets_spec`
inside `dryLinkedProgram` with `dryInnerRem`, leaving only three plain size inequalities on `sz`. -/
theorem drySC_hTermExt_proved (Psc : DrySparseCorePieces)
    (coreCode selectCode deepCode : SolverInnerSubCode)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (lastTreeCap : Circulation → Circulation → ℕ)
    (hTermSpace : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        lastTreeCap source J * (2 + wireTreeSyncEditSpace F.limbs) ≤ (sz source J).termSpace)
    (hTermFixed : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J _ =>
        41 * lastTreeCap source J + 320 ≤ (sz source J).termFixed)
    (hTreeMul : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤ (sz source J).treeMul) :
    let openInner := (dryInnerRem coreCode selectCode deepCode).toSolverInnerOpen
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
      let s := sz source J
      ShiftTermChainSyncSpecWExt
        (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        (dryCapLimit dryWitnessUsed J) (lastTreeCap source J) cfg Rcore
        (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode)
        (dryTailLay Psc.sc openInner.toInnerCode).shiftTermChain
        s.termSpace s.termFixed s.toolMul s.treeMul := by
  intro openInner source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
  let inner := openInner.toInnerCode
  have hw14 : 14 ≤ w := (ipm_quality_parameter_words_fit I.m V k hw).1
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs]; omega
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
  have hOps := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl
    (solverOps_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)
      (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
      Psc.sc inner
      (dynLctForestBodies 4 (mrdsCycleBase +
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)))
  obtain ⟨_, hTermAt, hBindAt, hCanonAt⟩ := dryInnerRem_hasEvalTerm Psc coreCode selectCode deepCode
  have hBind := pathSlotBind_meetsContract (w := w) hBindAt
  have hCanon : ∀ v, MeetsContract w (dryLinkedProgram dryWitnessUsed Psc.sc inner)
      ((dryTailLay Psc.sc inner).innerBase + dryInitConcreteLen + 3)
      (wireCanonCopyContract w v) :=
    fun v => wireCanonCopy_meetsContract v hCanonAt hOps.1 hOps.2.2.1
  have hSpec := shiftTermChainBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (capExp := dryCapExp) (limbMul := concreteReadout2LimbMul dryWitnessUsed)
    (capLimit := dryCapLimit dryWitnessUsed J) (lastTreeCap := lastTreeCap source J)
    (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw)
    (fmt := F.fmt)
    (initTree := mrdsCycleBase + 81) (opTree := dryPathTreeOp mrdsCycleBase)
    (bind := (dryTailLay Psc.sc inner).innerBase + dryInitConcreteLen + 2)
    (canonCopy := (dryTailLay Psc.sc inner).innerBase + dryInitConcreteLen + 3)
    (isNeg := mrdsCycleBase + 69)
    hTermAt
    (drySCRepAt_local Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) _ _ source J hw)
    rfl hLpos hL4W hOps.2.2.2.2.2 hBind hCanon hOps.2.2.2.2.1
  exact shiftTermChainSyncSpecWExt_mono hSpec
    (hTermSpace source J hJn hJm hCost hCap hw)
    (hTermFixed source J hJn hJm hCost hCap hw)
    (Nat.zero_le _)
    (hTreeMul source J hJn hJm hCost hCap hw)

end MinCostFlow.Final.DryRun

end
