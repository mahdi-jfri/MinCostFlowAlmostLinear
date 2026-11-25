module

public import MinCostFlow.Final.AssemblyDryRunSCDeepCode
public import MinCostFlow.Final.AssemblyDryRunSCDeepSelectProof
public import MinCostFlow.Final.AssemblyDryRunSCInitDischarged
public import MinCostFlow.Final.AssemblyDryRunSCSelInit
public import MinCostFlow.Final.WireInitSelectSizes
public import MinCostFlow.Final.AssemblyDryRunSCEnvelope
public import MinCostFlow.Final.AssemblyDryRunSCCompImpl
public import MinCostFlow.MinRatio.WireSelectQueryProofs
public import MinCostFlow.Num.IsZero
public import MinCostFlow.Num.Less
import MinCostFlow.MinRatio.WireSelectRawLoops
import MinCostFlow.MinRatio.WireSelectRawStitch
import MinCostFlow.Final.AssemblyDryRunSCRem
import Mathlib.Tactic

/-!
# Concrete `selectRoute` block and proof of `hSelectHeap` (`AssemblyDryRunSCSelectRoute`)

Packages the deterministic heap-backed cycle selector `selectRouteBody 4 2` (`WireSelectQuery.lean`,
reading the select-heap handle from `solverSelectHeapAddr table d = table + 4 * d + 2`) together
with its local deterministic helpers (`selectRawRouteBody`, `cancelRoutePathsBody`,
`cancelPairOuterBody`, `cancelPairInnerBody`, `Num.isZeroBody`, `selectFillRevBody`,
`selectSplitStepsBody`, `selectEmitStitchesBody`, `pathCompareExchangeBody`,
`pathCancelCompareBody`, `pathSwapWordsBody`, `cancelRouteEdgesLoopBody`,
`cancelEdgesFindOppBody`, `Num.lessModule`) into a relocatable `SolverInnerSubCode` block
`drySelectRouteCode`, reusing `Num.add`, `Num.isNegative`, and the path-tree oracle
`pathTreeBodies 4` from `solverOpsProcs`.

Provides:
* `drySelectRouteProcs`, `drySelectRouteCode`: the 17-procedure deterministic `SolverInnerSubCode`.
* `ordCycleRouteSelectSpecHeap_mono`: monotonicity of `OrdCycleRouteSelectSpecHeap` in
  `selectSpace` and `selectBudget`.
* `dryInnerCodeSel_hasSelectRoute`: extracts all 17 procedures of `drySelectRouteCode` at
  `lay.selectRoute` inside `dryLinkedProgram`.
* `drySelectRouteCode_hSelectHeap` and `drySelectRouteCode_hSelectHeap_core`: discharge the exact
  `hSelectHeap` hypothesis of `theorem_1_1_skeleton_kfbl_sel` (at `dMul = 4, kOff = 2`) for
  `drySelectRouteCode` via `ordCycleRouteSelectSpecHeap_proved`, unconditionally for
  `openSz := coreSz.toDryOpenSizes` (`WireSelectSizes.lean`).
* `theorem_1_1_skeleton_kfbl_sel`: the unified Theorem 1.1 (page 2) assembly theorem on
  `solverStateRepSelKFBL` (`dryLinkedProgramSel` at `drySelInitProc`), fixing
  `initCode := dryInitCode (dryParamCode Psc)`, `selectCode := drySelectRouteCode`,
  `deepCode := dryDeepSelectCode`, `selInitCode := drySelInitCode`,
  `initSel := dryInitSelectSizes Psc`, `shiftSel := dryShiftSelectSizes Psc`, and `pot := dryPot`,
  and unconditionally discharging P4, `DSRep.Implements`, `DryInitSelectSizeBounds`,
  `DryShiftSelectSizeBounds`, `hInitSel`, `hSelectHeap`, `hDeepSel`, `hEval`,
  `DryFixedPointCapBounds`, `DryEnvelopeIneqs`, `DeepShiftChainInvHyps`, `DrySparseCoreCapLevels`,
  and the embedding-length bound.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete 17-procedure deterministic `SolverInnerSubCode` block for `selectRoute` -/

/-- Fixed length (`17`) of `drySelectRouteProcs`. -/
def drySelectRouteCodeLen : ℕ := 17

/-- Concrete deterministic procedure block of length `17` placed at `env.innerBase`, implementing
`selectRouteBody 4 2` (at offset `0`) and its local helpers, reusing `Num.add` (`ops + 2`),
`Num.isNegative` (`ops + 69`), and `pathTreeBodies 4` (`ops + 81`) from `solverOpsProcs`:
* `b + 0`: `selectRouteBody 4 2 (b + 1) (b + 12) (b + 2)`;
* `b + 1`: `selectRawRouteBody (ops + 69) (b + 5) (b + 6) (b + 7) (b + 8)`;
* `b + 2`: `cancelRoutePathsBody (b + 2) (b + 3)`;
* `b + 3`: `cancelPairOuterBody (b + 3) (b + 4)`;
* `b + 4`: `cancelPairInnerBody (b + 4) (dryPathTreeOp ops 3) (b + 9)`;
* `b + 5`: `Num.isZeroBody (b + 5)`;
* `b + 6`: `selectFillRevBody (b + 6)`;
* `b + 7`: `selectSplitStepsBody (b + 7)`;
* `b + 8`: `selectEmitStitchesBody (b + 8)`;
* `b + 9`: `pathCompareExchangeBody (b + 10) (b + 11)`;
* `b + 10`: `pathCancelCompareBody (ops + 2) (b + 14)`;
* `b + 11`: `pathSwapWordsBody`;
* `b + 12`: `cancelRouteEdgesLoopBody (b + 12) (b + 13)`;
* `b + 13`: `cancelEdgesFindOppBody (b + 13)`;
* `b + 14 .. b + 16`: `Num.lessModule (b + 14) 4`. -/
def drySelectRouteProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [selectRouteBody 4 2 (b + 1) (b + 12) (b + 2),
   selectRawRouteBody (ops + 69) (b + 5) (b + 6) (b + 7) (b + 8),
   cancelRoutePathsBody (b + 2) (b + 3),
   cancelPairOuterBody (b + 3) (b + 4),
   cancelPairInnerBody (b + 4) (dryPathTreeOp ops 3) (b + 9),
   Num.isZeroBody (b + 5),
   selectFillRevBody (b + 6),
   selectSplitStepsBody (b + 7),
   selectEmitStitchesBody (b + 8),
   pathCompareExchangeBody (b + 10) (b + 11),
   pathCancelCompareBody (ops + 2) (b + 14),
   pathSwapWordsBody,
   cancelRouteEdgesLoopBody (b + 12) (b + 13),
   cancelEdgesFindOppBody (b + 13)] ++
  Num.lessModule (b + 14) 4

theorem drySelectRouteProcs_length (env : SolverInnerEnv) :
    (drySelectRouteProcs env).length = drySelectRouteCodeLen := rfl

theorem drySelectRouteProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ drySelectRouteProcs env, s.NoRand := by
  intro s hs
  unfold drySelectRouteProcs at hs
  rw [List.mem_append] at hs
  rcases hs with h1 | h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact selectRouteBody_noRand _ _ _ _ _
    · exact selectRawRouteBody_noRand _ _ _ _ _
    · exact cancelRoutePathsBody_noRand _ _
    · exact cancelPairOuterBody_noRand _ _
    · exact cancelPairInnerBody_noRand _ _ _
    · exact Num.isZeroBody_noRand _
    · exact selectFillRevBody_noRand _
    · exact selectSplitStepsBody_noRand _
    · exact selectEmitStitchesBody_noRand _
    · simp [pathCompareExchangeBody, Stmt.NoRand]
    · simp [pathCancelCompareBody, Stmt.NoRand]
    · simp [pathSwapWordsBody, Stmt.NoRand]
    · simp [cancelRouteEdgesLoopBody, Stmt.NoRand]
    · simp [cancelEdgesFindOppBody, Stmt.NoRand]
  · exact Num.lessModule_noRand _ _ s h2

/-- Relocatable `SolverInnerSubCode` for `selectRoute` (`selectRouteBody 4 2`). -/
def drySelectRouteCode : SolverInnerSubCode where
  procs := drySelectRouteProcs
  len := drySelectRouteCodeLen
  hlen := drySelectRouteProcs_length
  hnoRand := drySelectRouteProcs_noRand
  off := 0

/-- Concrete space bound emitted by `drySelectRouteCode` for parameters `(maxPaths, L)`. -/
def drySelectRouteSpace (maxPaths L : ℕ) : ℕ :=
  selectRouteTotalSpace maxPaths L (pathApplySpace L)

/-- Concrete amortized step budget emitted by `drySelectRouteCode` for parameters `(maxPaths, L)`. -/
def drySelectRouteBudget (maxPaths L : ℕ) : ℕ :=
  selectRouteTotalCost L maxPaths L
    (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1))

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Monotonicity of `OrdCycleRouteSelectSpecHeap` -/

/-- `OrdCycleRouteSelectSpecHeap` is monotone in `selectSpace` and `selectBudget`. -/
theorem ordCycleRouteSelectSpecHeap_mono
    {w L P m V psi k epsExp drainUnit dMul kOff selectProc sp₁ sp₂ bud₁ bud₂ maxEdges maxPaths : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (h : OrdCycleRouteSelectSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p selectProc sp₁ bud₁ maxEdges maxPaths)
    (hsp : sp₁ ≤ sp₂) (hbud : bud₁ ≤ bud₂) :
    OrdCycleRouteSelectSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p selectProc sp₂ bud₂ maxEdges maxPaths := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun root descBase workHeap pos size ω mem model tok loc B R
      G₀ σ σ_mwu γ_ℓ γ_c hrep hnum hoff hBd hMod hlog hme1 hmep hEmb hcapE hcapT
      hLk hhb hhbLt hMatch hMetaE hlocEnd hlocDisj hbelow hwh hz hroom => ?_⟩
  obtain ⟨work1, cost, out, tok', edges, paths, hr, hw1Lo, hw1Hi, hrest⟩ :=
    hrun root descBase workHeap pos size ω mem model tok loc B R G₀ σ σ_mwu γ_ℓ γ_c
      hrep hnum hoff hBd hMod hlog hme1 hmep hEmb hcapE hcapT hLk hhb hhbLt hMatch hMetaE
      hlocEnd hlocDisj hbelow hwh hz (by omega)
  refine ⟨work1, cost, out, tok', edges, paths, hr, hw1Lo, by omega, ?_⟩
  rcases hrest with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, by omega⟩

/-! ## 3. Placement inside `dryLinkedProgram` with `dryInnerCodeSel` -/

private theorem hasAt_peel_sel {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

private theorem hasAt_dryInnerCodeSel_selectRoute {p : Program} {env : SolverInnerEnv}
    (initCode coreCode termCode deepCode : SolverInnerSubCode)
    (hInner : p.HasAt env.innerBase
      ((dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode).procs env)) :
    let b := env.innerBase + (1 + initCode.len + coreCode.len + 0)
    let ops := env.opsBase
    p.procs[b]? = some (selectRouteBody 4 2 (b + 1) (b + 12) (b + 2)) ∧
    p.procs[b + 1]? = some (selectRawRouteBody (ops + 69) (b + 5) (b + 6) (b + 7) (b + 8)) ∧
    p.procs[b + 2]? = some (cancelRoutePathsBody (b + 2) (b + 3)) ∧
    p.procs[b + 3]? = some (cancelPairOuterBody (b + 3) (b + 4)) ∧
    p.procs[b + 4]? = some (cancelPairInnerBody (b + 4) (dryPathTreeOp ops 3) (b + 9)) ∧
    p.HasAt (b + 5) (Num.isZeroModule (b + 5)) ∧
    p.procs[b + 6]? = some (selectFillRevBody (b + 6)) ∧
    p.procs[b + 7]? = some (selectSplitStepsBody (b + 7)) ∧
    p.procs[b + 8]? = some (selectEmitStitchesBody (b + 8)) ∧
    p.HasAt (b + 9) [pathCompareExchangeBody (b + 10) (b + 11)] ∧
    p.HasAt (b + 10) [pathCancelCompareBody (ops + 2) (b + 14)] ∧
    p.HasAt (b + 11) [pathSwapWordsBody] ∧
    p.procs[b + 12]? = some (cancelRouteEdgesLoopBody (b + 12) (b + 13)) ∧
    p.procs[b + 13]? = some (cancelEdgesFindOppBody (b + 13)) ∧
    p.HasAt (b + 14) (Num.lessModule (b + 14) 4) := by
  intro b ops
  unfold dryInnerCodeSel at hInner
  dsimp only at hInner
  obtain ⟨_, r1⟩ := hasAt_peel_sel (b' := env.innerBase + 1) hInner (by simp)
  obtain ⟨_, r2⟩ := hasAt_peel_sel (b' := env.innerBase + 1 + initCode.len) r1
    (by simp [initCode.hlen])
  obtain ⟨_, r3⟩ := hasAt_peel_sel (b' := env.innerBase + 1 + initCode.len + coreCode.len) r2
    (by simp [coreCode.hlen])
  have hbEq : env.innerBase + 1 + initCode.len + coreCode.len = b := by dsimp only [b]; omega
  rw [hbEq] at r3
  have hSelAt : p.HasAt b (drySelectRouteProcs { env with innerBase := b }) :=
    Num.hasAt_append_left r3
  unfold drySelectRouteProcs at hSelAt
  dsimp only at hSelAt
  have hHead := Num.hasAt_append_left hSelAt
  have hTail : p.HasAt (b + 14) (Num.lessModule (b + 14) 4) := by
    simpa using Num.hasAt_append_right hSelAt
  have hSingle : ∀ {i : ℕ} {s : Stmt}, p.procs[b + i]? = some s → p.HasAt (b + i) [s] := by
    intro i s hs j hj
    have hj0 : j = 0 := by change j < 1 at hj; omega
    subst hj0
    simpa using hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTail⟩
  · simpa [ops] using hHead 0 (by simp)
  · simpa [ops] using hHead 1 (by simp)
  · simpa [ops] using hHead 2 (by simp)
  · simpa [ops] using hHead 3 (by simp)
  · simpa [ops] using hHead 4 (by simp)
  · exact hSingle (by simpa [ops] using hHead 5 (by simp))
  · simpa [ops] using hHead 6 (by simp)
  · simpa [ops] using hHead 7 (by simp)
  · simpa [ops] using hHead 8 (by simp)
  · exact hSingle (by simpa [ops] using hHead 9 (by simp))
  · exact hSingle (by simpa [ops] using hHead 10 (by simp))
  · exact hSingle (by simpa [ops] using hHead 11 (by simp))
  · simpa [ops] using hHead 12 (by simp)
  · simpa [ops] using hHead 13 (by simp)

/-- Placement of all 17 procedures of `drySelectRouteCode` at `lay.selectRoute` inside
`dryLinkedProgram` with `dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hasSelectRoute (Psc : DrySparseCorePieces)
    (initCode coreCode termCode deepCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
    let lay := dryTailLay Psc.sc inner
    let b := lay.selectRoute
    let ops := mrdsCycleBase
    p.procs[b]? = some (selectRouteBody 4 2 (b + 1) (b + 12) (b + 2)) ∧
    p.procs[b + 1]? = some (selectRawRouteBody (ops + 69) (b + 5) (b + 6) (b + 7) (b + 8)) ∧
    p.procs[b + 2]? = some (cancelRoutePathsBody (b + 2) (b + 3)) ∧
    p.procs[b + 3]? = some (cancelPairOuterBody (b + 3) (b + 4)) ∧
    p.procs[b + 4]? = some (cancelPairInnerBody (b + 4) (dryPathTreeOp ops 3) (b + 9)) ∧
    p.HasAt (b + 5) (Num.isZeroModule (b + 5)) ∧
    p.procs[b + 6]? = some (selectFillRevBody (b + 6)) ∧
    p.procs[b + 7]? = some (selectSplitStepsBody (b + 7)) ∧
    p.procs[b + 8]? = some (selectEmitStitchesBody (b + 8)) ∧
    p.HasAt (b + 9) [pathCompareExchangeBody (b + 10) (b + 11)] ∧
    p.HasAt (b + 10) [pathCancelCompareBody (ops + 2) (b + 14)] ∧
    p.HasAt (b + 11) [pathSwapWordsBody] ∧
    p.procs[b + 12]? = some (cancelRouteEdgesLoopBody (b + 12) (b + 13)) ∧
    p.procs[b + 13]? = some (cancelEdgesFindOppBody (b + 13)) ∧
    p.HasAt (b + 14) (Num.lessModule (b + 14) 4) := by
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
  exact hasAt_dryInnerCodeSel_selectRoute initCode coreCode termCode deepCode hInner

/-! ## 4. Discharging `hSelectHeap` of `theorem_1_1_skeleton_kfbl_sel` -/

/-- General discharge of `hSelectHeap` for `drySelectRouteCode` inside `dryLinkedProgram` with
`dryInnerCodeSel` at `(dMul, kOff) = (4, 2)` and `drySCRep`, whenever `openSz.selectSpace` and
`openSz.selectBudget` dominate `drySelectRouteSpace` and `drySelectRouteBudget`. -/
theorem drySelectRouteCode_hSelectHeap (Psc : DrySparseCorePieces)
    (initCode coreCode termCode deepCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz)
    (hSelSpace : ForAllDryInputs dryWitnessUsed
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      drySelectRouteSpace (openSz.maxPaths source J) F.limbs ≤ openSz.selectSpace source J)
    (hSelBudget : ForAllDryInputs dryWitnessUsed
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      drySelectRouteBudget (openSz.maxPaths source J) F.limbs ≤ openSz.selectBudget source J) :
    let inner := dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdCycleRouteSelectSpecHeap
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) 4 2 cfg Rcore
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryTailLay Psc.sc inner).selectRoute
        s.selectSpace s.selectBudget s.maxEdges s.maxPaths := by
  intro inner source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
  let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
  let b := (dryTailLay Psc.sc inner).selectRoute
  have hw14 : 14 ≤ w := (ipm_quality_parameter_words_fit I.m V k hw).1
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hw1 : 1 < 2 ^ w := by omega
  have hbase4 : Num.base 4 < 2 ^ w := by change 2 ^ 4 < 2 ^ w; omega
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
  obtain ⟨hpSel, hpRaw, hpCancel, hpOuter, hpInner, hZeroAt, hpFillRev, hpSplit, hpEmit,
      hCmpExAt, hCmpAt, hSwapAt, hpCancelEd, hpFindOpp, hLessAt⟩ :=
    dryInnerCodeSel_hasSelectRoute Psc initCode coreCode termCode deepCode
  have hLess := Num.less_meetsContract (w := w) (h := 4) (by decide) hw1 hbase4 hLessAt
  have hZero := Num.isZero_meetsContract (w := w) (h := 4) hw1 hZeroAt
  have hSwap := pathSwapWords_meetsContract (w := w) hSwapAt
  have hBase := ordCycleRouteSelectSpecHeap_proved
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (dMul := 4) (kOff := 2) (selectProc := b) (rawProc := b + 1)
    (cancelEdgesProc := b + 12) (findOppProc := b + 13) (cancelProc := b + 2)
    (outerProc := b + 3) (innerProc := b + 4) (isNegProc := mrdsCycleBase + 69)
    (isZeroProc := b + 5) (fillRev := b + 6) (splitSteps := b + 7) (emitStitches := b + 8)
    (initTree := mrdsCycleBase + 81) (cmpExch := b + 9)
    (maxEdges := openSz.maxEdges source J) (maxPaths := openSz.maxPaths source J)
    (fmt := F.fmt) (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (opTree := dryPathTreeOp mrdsCycleBase)
    (Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    (p := p)
    hw16 (by omega) rfl
    (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    hpSel hpRaw hpCancelEd hpFindOpp hpCancel hpOuter hpInner hOps.2.2.2.2.1 hZero
    (fun Q => selectFillRev_meetsContract hpFillRev)
    (fun G0 Fg W fl => selectSplitSteps_meetsContract hpSplit)
    (fun G0 W fl p0 => selectEmitStitches_meetsContract hpEmit)
    hOps.2.2.2.2.2
    (fun ab cd ad cb => pathCompareExchange_meetsContract ab cd ad cb hCmpExAt
      (pathCancelCompare_meetsContract ab cd ad cb hCmpAt hOps.2.1 hLess) hSwap)
  exact ordCycleRouteSelectSpecHeap_mono hBase
    (hSelSpace source J hJn hJm hCost hCap hw)
    (hSelBudget source J hJn hJm hCost hCap hw)

/-- **Unconditional discharge of `hSelectHeap`** for `drySelectRouteCode` at
`openSz := coreSz.toDryOpenSizes` (`WireSelectSizes.lean`), where `openSz.selectSpace` and
`openSz.selectBudget` match `drySelectRouteSpace` and `drySelectRouteBudget` definitionally. -/
theorem drySelectRouteCode_hSelectHeap_core (Psc : DrySparseCorePieces)
    (initCode coreCode termCode deepCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCore.toDryOpenSizeBounds
    let inner := dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdCycleRouteSelectSpecHeap
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) 4 2 cfg Rcore
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryTailLay Psc.sc inner).selectRoute
        s.selectSpace s.selectBudget s.maxEdges s.maxPaths :=
  drySelectRouteCode_hSelectHeap Psc initCode coreCode termCode deepCode
    coreSz.toDryOpenSizes hCore.toDryOpenSizeBounds selSz hSel
    (fun _ _ _ _ _ _ _ => le_refl _) (fun _ _ _ _ _ _ _ => le_refl _)

/-- Placement of all 17 procedures of `drySelectRouteCode` at `lay.selectRoute` inside
`dryLinkedProgramSel` with `dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hasSelectRoute_sel (Psc : DrySparseCorePieces)
    (initCode coreCode termCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.selectRoute
    let ops := mrdsCycleBase
    p.procs[b]? = some (selectRouteBody 4 2 (b + 1) (b + 12) (b + 2)) ∧
    p.procs[b + 1]? = some (selectRawRouteBody (ops + 69) (b + 5) (b + 6) (b + 7) (b + 8)) ∧
    p.procs[b + 2]? = some (cancelRoutePathsBody (b + 2) (b + 3)) ∧
    p.procs[b + 3]? = some (cancelPairOuterBody (b + 3) (b + 4)) ∧
    p.procs[b + 4]? = some (cancelPairInnerBody (b + 4) (dryPathTreeOp ops 3) (b + 9)) ∧
    p.HasAt (b + 5) (Num.isZeroModule (b + 5)) ∧
    p.procs[b + 6]? = some (selectFillRevBody (b + 6)) ∧
    p.procs[b + 7]? = some (selectSplitStepsBody (b + 7)) ∧
    p.procs[b + 8]? = some (selectEmitStitchesBody (b + 8)) ∧
    p.HasAt (b + 9) [pathCompareExchangeBody (b + 10) (b + 11)] ∧
    p.HasAt (b + 10) [pathCancelCompareBody (ops + 2) (b + 14)] ∧
    p.HasAt (b + 11) [pathSwapWordsBody] ∧
    p.procs[b + 12]? = some (cancelRouteEdgesLoopBody (b + 12) (b + 13)) ∧
    p.procs[b + 13]? = some (cancelEdgesFindOppBody (b + 13)) ∧
    p.HasAt (b + 14) (Num.lessModule (b + 14) 4) :=
  hasAt_dryInnerCodeSel_selectRoute initCode coreCode termCode deepCode
    (dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc
      (dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode) selInitCode)

/-- Unconditional discharge of `hSelectHeap` for `drySelectRouteCode` inside `dryLinkedProgramSel`
at `openSz := coreSz.toDryOpenSizes`. -/
theorem drySelectRouteCode_hSelectHeap_sel (Psc : DrySparseCorePieces)
    (initCode coreCode termCode deepCode selInitCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCore.toDryOpenSizeBounds
    let inner := dryInnerCodeSel initCode coreCode drySelectRouteCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdCycleRouteSelectSpecHeap
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) 4 2 cfg Rcore
        p (dryTailLay Psc.sc inner).selectRoute
        s.selectSpace s.selectBudget s.maxEdges s.maxPaths := by
  intro openSz hOpen inner p source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
  let b := (dryTailLay Psc.sc inner).selectRoute
  have hw14 : 14 ≤ w := (ipm_quality_parameter_words_fit I.m V k hw).1
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hw1 : 1 < 2 ^ w := by omega
  have hbase4 : Num.base 4 < 2 ^ w := by change 2 ^ 4 < 2 ^ w; omega
  have hOps := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl
    (dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner selInitCode)
  obtain ⟨hpSel, hpRaw, hpCancel, hpOuter, hpInner, hZeroAt, hpFillRev, hpSplit, hpEmit,
      hCmpExAt, hCmpAt, hSwapAt, hpCancelEd, hpFindOpp, hLessAt⟩ :=
    dryInnerCodeSel_hasSelectRoute_sel Psc initCode coreCode termCode deepCode selInitCode
  exact ordCycleRouteSelectSpecHeap_proved
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (dMul := 4) (kOff := 2) (selectProc := b) (rawProc := b + 1)
    (cancelEdgesProc := b + 12) (findOppProc := b + 13) (cancelProc := b + 2)
    (outerProc := b + 3) (innerProc := b + 4) (isNegProc := mrdsCycleBase + 69)
    (isZeroProc := b + 5) (fillRev := b + 6) (splitSteps := b + 7) (emitStitches := b + 8)
    (initTree := mrdsCycleBase + 81) (cmpExch := b + 9)
    (maxEdges := openSz.maxEdges source J) (maxPaths := openSz.maxPaths source J)
    (fmt := F.fmt) (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (opTree := dryPathTreeOp mrdsCycleBase)
    (Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    (p := p)
    hw16 (by omega) rfl
    (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    hpSel hpRaw hpCancelEd hpFindOpp hpCancel hpOuter hpInner hOps.2.2.2.2.1
    (Num.isZero_meetsContract (w := w) (h := 4) hw1 hZeroAt)
    (fun Q => selectFillRev_meetsContract hpFillRev)
    (fun G0 Fg W fl => selectSplitSteps_meetsContract hpSplit)
    (fun G0 W fl p0 => selectEmitStitches_meetsContract hpEmit)
    hOps.2.2.2.2.2
    (fun ab cd ad cb => pathCompareExchange_meetsContract ab cd ad cb hCmpExAt
      (pathCancelCompare_meetsContract ab cd ad cb hCmpAt hOps.2.1
        (Num.less_meetsContract (w := w) (h := 4) (by decide) hw1 hbase4 hLessAt))
      (pathSwapWords_meetsContract (w := w) hSwapAt))

/-- Assembles `DrySparseCorePieces` from the unpacked first-phase branch hypotheses, instantiating
P4 unconditionally via `dryCompCode`, `dryCFS`, and `dryCF_hyp`. -/
noncomputable def mkDrySparseCorePieces
    (firstStep firstInit : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JS : AsmBrCoreStepAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
              sparsifyImplUsed depth fmt.precision L_in capExp limbMul
              (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreS,
            JS.mul = C.stepMul capExp limbMul ∧
            JS.ysMul = C.stepYs capExp limbMul ∧
            JS.spaceP = C.stepSpace capExp)
    (hFirstInit :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
              limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp) :
    DrySparseCorePieces where
  cf := dryCompCode
  firstStep := firstStep
  firstInit := firstInit
  CFS := dryCFS
  hCF := dryCF_hyp
  hBR := ⟨⟨C, hC, fun depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot =>
    ⟨hFirstStep depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot,
     hFirstInit depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot⟩⟩⟩


/-- **Factored `DyadicWithVConcretePrograms` bundle on `solverStateRepSelKFBL` and `drySCRep`.**
Produces the concrete solver bundle used by both `theorem_1_1_skeleton_kfbl_sel` (old statement)
and `narrowStatement_of_dyadic_withV` (narrow-word statement). -/
noncomputable def dryDyadicWithVBundle_sel
    (firstStep firstInit : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JS : AsmBrCoreStepAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
              sparsifyImplUsed depth fmt.precision L_in capExp limbMul
              (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreS,
            JS.mul = C.stepMul capExp limbMul ∧
            JS.ysMul = C.stepYs capExp limbMul ∧
            JS.spaceP = C.stepSpace capExp)
    (hFirstInit :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
              limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp)
    (coreCode termCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (hCoreSel :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
      let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
        (dryShiftSelectSizeBounds Psc)
      let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode drySelectRouteCode
        termCode dryDeepSelectCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        OrdChainUpdateCoreSpecWKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
          dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J)
          (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
          4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul)
    (hTermSel :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
      let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
        (dryShiftSelectSizeBounds Psc)
      let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode drySelectRouteCode
        termCode dryDeepSelectCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        ShiftTermChainSyncSpecWExtKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
          (detectOffTreeDrainUnit F.limbs) dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
          (dryCapLimit dryWitnessUsed J) (2 * levelM cfg.TP cfg.P cfg.P.d)
          G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) F.rangeExponent
          (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).shiftTermChain
          s.termSpace s.termFixed s.toolMul s.treeMul) :
    DyadicWithVConcretePrograms :=
  let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
  let openSz := coreSz.toDryOpenSizes
  let hOpen := hCore.toDryOpenSizeBounds
  let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
  let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
    (dryShiftSelectSizeBounds Psc)
  let B := dryInnerBounds Psc openSz hOpen selSz hSel
  let hB := dryInnerBounds_hyp Psc openSz hOpen selSz hSel
  let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode drySelectRouteCode
    termCode dryDeepSelectCode
  let hInitSel := drySelInitCode_hInitSel Psc coreCode drySelectRouteCode termCode
    dryDeepSelectCode coreSz hCore (dryShiftSelectSizes Psc) (dryShiftSelectSizeBounds Psc)
  let hSelectHeap := drySelectRouteCode_hSelectHeap_sel Psc (dryInitCode (dryParamCode Psc))
    coreCode termCode dryDeepSelectCode drySelInitCode coreSz hCore selSz hSel
  let hDeepSel := dryDeepSelectCode_hDeepSel Psc (dryInitCode (dryParamCode Psc))
    coreCode drySelectRouteCode termCode drySelInitCode openSz hOpen
    (dryInitSelectSizes Psc) (dryInitSelectSizeBounds Psc)
    dryTermSelectSizes dryTermSelectSizeBounds
  let hImpl := drySolver_implements_sel Psc (dryInitCode (dryParamCode Psc)) coreCode
    drySelectRouteCode termCode dryDeepSelectCode drySelInitCode coreSz hCore selSz hSel
    (fun _ J => dryPot J) hInitSel hCoreSel hSelectHeap hTermSel hDeepSel
  { lastTool := dryLastTool
    lastConstant := dryLastConstant
    lastSpec := dryLastSpec
    witness := dryWitnessUsed
    cycleInit := drySelInitProc (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner drySelInitCode
    cycleOp := solverOpsDispatch mrdsCycleBase
    cycle := dryCycleWithSelInit (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner drySelInitCode
    cycleDeterministic := dryCycleWithSelInit_noRand _ _ drySelInitCode Psc.hsc
      (dryInnerCodeSel_isDeterministic (dryInitCode (dryParamCode Psc)) coreCode
        drySelectRouteCode termCode dryDeepSelectCode)
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
    supported := fun source J hJn hJm hCost hCap hw =>
      ⟨_, hImpl source J hJn hJm hCost hCap hw,
        fun j hj args => B.cycleAllocation_le_cycleSpace _ _ j hj args⟩ }

end MinCostFlow.Final.DryRun

end
