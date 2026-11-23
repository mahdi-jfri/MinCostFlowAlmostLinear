module

public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectCode
public import MinCostFlow.MinRatio.WireChainCoreBranchAEnvKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBIntOutKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTermKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSync2aKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSync2bKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBPushRunKFBL
import MinCostFlow.Final.AssemblyDryRunSCInit
import MinCostFlow.MinRatio.UpdateOffTreePush
import Mathlib.Tactic

/-!
# Relocatable inner chain-core block `dryInnerCoreCode` (`AssemblyDryRunSCInnerCode`)

Packages the inner chain-update core `ordChainUpdateCoreBodyKFBL` (Branch A `wireBranchAKFBL` and
Branch B) together with its local Branch A helpers, Branch B helpers, and dynamic-graph library
(`dgOpsProcs`, `dgEdgeProcs`, `dgSplitProcs`, `dgBatchProcs`) into a relocatable deterministic
`SolverInnerSubCode` block `dryInnerCoreCodeOf` (and its concrete default `dryInnerCoreCode`)
with `off := 0`.

When wrapped by `dryCoreSelectCode` (`Final/AssemblyDryRunSCCoreSelectCode.lean`), `dryTailLay`
places `dryInnerCoreCodeOf` at `b := lay.ordChainCore + 1`, so its entry sits at
`lay.ordChainCore + 1 + innerCoreCode.off = lay.ordChainCore + 1`, matching
`dryCoreSel_hCoreSel_of_ext` (`Final/AssemblyDryRunSCCoreSelectEnd.lean`):

* `dryInnerCoreBranchA`: `wireBranchAKFBL` instantiated at the local indices of `env.innerBase`,
  the shared arithmetic/path-tree helpers of `env.opsBase`, `env.level0Rename`, and the core/last
  procedures `env.scInit`, `env.scOp`, `env.lastInit`.
* `dryInnerCoreBranchB`: concrete default Branch B statement composing `wireBranchBPrefixKFBL`,
  `wireBranchBFrontKFBL`, `wireBranchBLoopKFBL`, `wireBranchBIntKFBL`, `wireBranchBTermKFBL`,
  `collectTermForestStmt`, `wireBranchBSync2aStmt`, `wireBranchBSync2bStmt`, and
  `wirePushInsertedBody`.
* `dryInnerCoreCodeOf`, `dryInnerCoreCode`: the 37-procedure deterministic `SolverInnerSubCode`
  blocks with `off := 0`.
* `dryInnerCoreCodeOf_hasAll`: extracts every procedure entry (`b + 0 .. b + 21`) and all four
  dynamic-graph `HasAt` placements (`b + 22`, `b + 29`, `b + 31`, `b + 34`) inside
  `dryLinkedProgramSel`.
* `dryInnerCoreCodeOf_bindC`, `dryInnerCoreCodeOf_canonC`, `dryInnerCoreCodeOf_dgApplyC`,
  `dryInnerCoreCodeOf_dgInitC`, `dryInnerCoreCodeOf_renP`: immediate contract/placement lemmas
  for the helper procedures called by `BranchAEnvKFBL`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Inner chain-core statements and 37-procedure `SolverInnerSubCode` block -/

/-- Fixed length (`37`) of `dryInnerCoreProcsOf`. -/
def dryInnerCoreCodeLen : ℕ := 37

/-- Branch A statement (`wireBranchAKFBL`) instantiated at the local offsets of
`dryInnerCoreProcsOf` relative to `b := env.innerBase` and `ops := env.opsBase`. -/
def dryInnerCoreBranchA (env : SolverInnerEnv) : Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  wireBranchAKFBL
    (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
    (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch) (b + 6)
    (env.scOp 2) env.level0Rename (b + 7) (b + 8) env.scInit (env.scOp 3)
    (b + 9) (env.scOp 5) env.lastInit (b + 11)

theorem dryInnerCoreBranchA_noRand (env : SolverInnerEnv) :
    (dryInnerCoreBranchA env).NoRand :=
  wireBranchAKFBL_noRand ..

/-- Concrete Branch B statement composing prefix, front, plain-step loop, interior/terminal exits,
Sync 2a, Sync 2b, live-insertion push, and return at the local offsets of `dryInnerCoreProcsOf`. -/
def dryInnerCoreBranchB (env : SolverInnerEnv) : Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  wireBranchBPrefixKFBL (b + 12) (b + 13) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) (b + 14) (b + 4) (b + 6) ;;
  wireBranchBFrontKFBL (b + 15) ;;
  wireBranchBLoopKFBL (env.scOp 0) (env.scOp 2) (b + 34 + dgIdxApplyBatch)
      (b + 15) (b + 16) (b + 17) ;;
  .cond (.bin .lt (.reg 96) (.reg 75))
    (wireBranchBIntKFBL (b + 34 + dgIdxApplyBatch) env.scInit (env.scOp 3) (env.scOp 2)
      (b + 9) (env.scOp 5) env.lastInit)
    (wireBranchBTermKFBL (env.scOp 3) (env.scOp 2) (b + 9) (env.scOp 5) env.lastInit ;;
      collectTermForestStmt 81) ;;
  wireBranchBSync2aStmt (b + 13) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) ;;
  .assign 99 (.load (.reg 72)) ;;
  wireBranchBSync2bStmt (b + 1) (b + 19) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69) ;;
  .call 10 (b + 20) [.reg 70, .reg 87, .reg 94] ;;
  .ret (.reg 4)

theorem dryInnerCoreBranchB_noRand (env : SolverInnerEnv) :
    (dryInnerCoreBranchB env).NoRand := by
  simp only [dryInnerCoreBranchB, Stmt.NoRand]
  exact ⟨wireBranchBPrefixKFBL_noRand .., wireBranchBFrontKFBL_noRand _,
    wireBranchBLoopKFBL_noRand ..,
    ⟨wireBranchBIntKFBL_noRand ..,
      ⟨wireBranchBTermKFBL_noRand .., collectTermForestStmt_noRand _⟩⟩,
    wireBranchBSync2aStmt_noRand .., trivial, wireBranchBSync2bStmt_noRand .., trivial, trivial⟩

/-- Concrete 37-procedure deterministic block placed at `b := env.innerBase`:
* `b + 0`: `ordChainUpdateCoreBodyKFBL (dryInnerCoreBranchA env) (mkBranchB env)` (entry, `off = 0`);
* `b + 1 .. b + 11`: Branch A local helpers (`packEdits`, `bind`, `canonCopy`, `refreshAccounts`,
  `refreshOne`, `updateLen0`, `compactLevel0`, `buildSortedEnds`, `coreLen`, `coreLenEdge`,
  `rebuildOffReady`);
* `b + 12 .. b + 21`: Branch B local helpers (`collectDel`, `emitCuts`, `zeroIns`, `rawCopy`,
  `updateCoreLenFromBatch`, `selOutSlot`, `collectTouched`, `filterPresentEdits`, `pushInserted`,
  `offTreePush`);
* `b + 22 .. b + 36`: dynamic-graph library (`dgOpsProcs` at `b + 22`, `dgEdgeProcs` at `b + 29`,
  `dgSplitProcs` at `b + 31`, `dgBatchProcs` at `b + 34`). -/
def dryInnerCoreProcsOf (mkBranchB : SolverInnerEnv → Stmt) (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  let bDg := b + 22
  [ordChainUpdateCoreBodyKFBL (dryInnerCoreBranchA env) (mkBranchB env),
   wireSuffixPackEditsBody,
   pathSlotBindBody,
   wireCanonCopyBody ops (ops + 4),
   wireRefreshAccountsBody (ops + 20) (ops + 4) (b + 5),
   wireRefreshOneAccountBody (ops + 16) (ops + 2) (ops + 6) (ops + 4) ops (ops + 69),
   wireUpdateLen0FromBatchBody ops,
   wireCompactLevel0Body ops (b + 34 + dgIdxInitFromLists),
   buildSortedEndsBody,
   wireCoreLenBody (b + 10),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops,
   wireRebuildOffReadyBody (ops + 69),
   wireCollectDeletedEdgesBody,
   wireEmitTreeCutsBody,
   wireZeroInsertSlotsBody,
   wireRawCopyBody,
   wireUpdateCoreLenFromBatchBody (b + 10),
   wireSelOutSlotBody (b + 18),
   wireCollectTouchedEdgesBody,
   wireFilterPresentEditsBody,
   wirePushInsertedBody (b + 21),
   offTreePushBody (ops + 69)] ++
  dgOpsProcs ++
  dgEdgeProcs bDg ++
  dgSplitProcs bDg (bDg + 9) ++
  dgBatchProcs bDg (bDg + 7) (bDg + 9) (bDg + 12)

theorem dryInnerCoreProcsOf_length (mkBranchB : SolverInnerEnv → Stmt) (env : SolverInnerEnv) :
    (dryInnerCoreProcsOf mkBranchB env).length = dryInnerCoreCodeLen := by
  simp [dryInnerCoreProcsOf, dryInnerCoreCodeLen, dgOpsProcs, dgEdgeProcs, dgSplitProcs,
    dgBatchProcs]

theorem dryInnerCoreProcsOf_noRand (mkBranchB : SolverInnerEnv → Stmt)
    (hBNoRand : ∀ env, (mkBranchB env).NoRand) (env : SolverInnerEnv) :
    ∀ s ∈ dryInnerCoreProcsOf mkBranchB env, s.NoRand := by
  intro s hs
  unfold dryInnerCoreProcsOf at hs
  simp only [List.mem_append] at hs
  rcases hs with (((hHead | hOps) | hEdge) | hSplit) | hBatch
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hHead
    rcases hHead with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ordChainUpdateCoreBodyKFBL_noRand (dryInnerCoreBranchA_noRand env) (hBNoRand env)
    · exact wireSuffixPackEditsBody_noRand
    · simp [pathSlotBindBody, Stmt.NoRand]
    · exact wireCanonCopyBody_noRand ..
    · exact wireRefreshAccountsBody_noRand ..
    · exact wireRefreshOneAccountBody_noRand ..
    · exact wireUpdateLen0FromBatchBody_noRand ..
    · exact wireCompactLevel0Body_noRand ..
    · exact buildSortedEndsBody_noRand
    · exact wireCoreLenBody_noRand ..
    · exact wireCoreLenEdgeBody_noRand ..
    · exact wireRebuildOffReadyBody_noRand ..
    · exact wireCollectDeletedEdgesBody_noRand
    · exact wireEmitTreeCutsBody_noRand
    · exact wireZeroInsertSlotsBody_noRand
    · exact wireRawCopyBody_noRand
    · exact wireUpdateCoreLenFromBatchBody_noRand ..
    · exact wireSelOutSlotBody_noRand ..
    · exact wireCollectTouchedEdgesBody_noRand
    · exact wireFilterPresentEditsBody_noRand
    · exact wirePushInsertedBody_noRand ..
    · exact offTreePushBody_noRand ..
  · exact dgOpsProcs_noRand s hOps
  · exact dgEdgeProcs_noRand _ s hEdge
  · exact dgSplitProcs_noRand _ _ s hSplit
  · exact dgBatchProcs_noRand _ _ _ _ s hBatch

/-- Relocatable deterministic `SolverInnerSubCode` for the inner chain-update core
(`ordChainUpdateCoreBodyKFBL` at offset `0`), parameterized by the Branch B statement `mkBranchB`. -/
def dryInnerCoreCodeOf (mkBranchB : SolverInnerEnv → Stmt)
    (hBNoRand : ∀ env, (mkBranchB env).NoRand) : SolverInnerSubCode where
  procs := dryInnerCoreProcsOf mkBranchB
  len := dryInnerCoreCodeLen
  hlen := dryInnerCoreProcsOf_length mkBranchB
  hnoRand := dryInnerCoreProcsOf_noRand mkBranchB hBNoRand
  off := 0

/-- Concrete default `SolverInnerSubCode` for the inner chain-update core using
`dryInnerCoreBranchB`. -/
def dryInnerCoreCode : SolverInnerSubCode :=
  dryInnerCoreCodeOf dryInnerCoreBranchB dryInnerCoreBranchB_noRand

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Procedure placement and helper contracts inside `dryLinkedProgramSel` -/

private theorem hasAt_peel_ic {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Extracts every procedure entry (`b + 0 .. b + 21`) and all four dynamic-graph `HasAt`
placements (`b + 22`, `b + 29`, `b + 31`, `b + 34`) of `dryInnerCoreCodeOf mkBranchB hBNoRand`
at `b := lay.ordChainCore + 1 = lay.ordChainCore + 1 + innerCoreCode.off` inside
`dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_hasAll (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.ordChainCore + 1
    let ops := mrdsCycleBase
    let env0 := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc solverTailBase
    let envIn : SolverInnerEnv := { env0 with innerBase := b }
    let bDg := b + 22
    lay.ordChainCore + 1 + innerCoreCode.off = b ∧
    p.procs[b]? = some (ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL (b + 1) (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
        (b + 2) (b + 3) (ops + 69) (b + 4) (b + 34 + dgIdxApplyBatch) (b + 6)
        (lay.scOp 2) (solverTailBase + 11) (b + 7) (b + 8) lay.scInit (lay.scOp 3)
        (b + 9) (lay.scOp 5) lay.lastInit (b + 11))
      (mkBranchB envIn)) ∧
    p.procs[b + 1]? = some wireSuffixPackEditsBody ∧
    p.procs[b + 2]? = some pathSlotBindBody ∧
    p.procs[b + 3]? = some (wireCanonCopyBody ops (ops + 4)) ∧
    p.procs[b + 4]? = some (wireRefreshAccountsBody (ops + 20) (ops + 4) (b + 5)) ∧
    p.procs[b + 5]? =
      some (wireRefreshOneAccountBody (ops + 16) (ops + 2) (ops + 6) (ops + 4) ops (ops + 69)) ∧
    p.procs[b + 6]? = some (wireUpdateLen0FromBatchBody ops) ∧
    p.procs[b + 7]? = some (wireCompactLevel0Body ops (b + 34 + dgIdxInitFromLists)) ∧
    p.procs[b + 8]? = some buildSortedEndsBody ∧
    p.procs[b + 9]? = some (wireCoreLenBody (b + 10)) ∧
    p.procs[b + 10]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.procs[b + 11]? = some (wireRebuildOffReadyBody (ops + 69)) ∧
    p.procs[b + 12]? = some wireCollectDeletedEdgesBody ∧
    p.procs[b + 13]? = some wireEmitTreeCutsBody ∧
    p.procs[b + 14]? = some wireZeroInsertSlotsBody ∧
    p.procs[b + 15]? = some wireRawCopyBody ∧
    p.procs[b + 16]? = some (wireUpdateCoreLenFromBatchBody (b + 10)) ∧
    p.procs[b + 17]? = some (wireSelOutSlotBody (b + 18)) ∧
    p.procs[b + 18]? = some wireCollectTouchedEdgesBody ∧
    p.procs[b + 19]? = some wireFilterPresentEditsBody ∧
    p.procs[b + 20]? = some (wirePushInsertedBody (b + 21)) ∧
    p.procs[b + 21]? = some (offTreePushBody (ops + 69)) ∧
    p.HasAt bDg dgOpsProcs ∧
    p.HasAt (bDg + 7) (dgEdgeProcs bDg) ∧
    p.HasAt (bDg + 9) (dgSplitProcs bDg (bDg + 9)) ∧
    p.HasAt (bDg + 12) (dgBatchProcs bDg (bDg + 7) (bDg + 9) (bDg + 12)) := by
  intro innerCoreCode inner p lay b ops env0 envIn bDg
  have hSel := dryCoreSelectCode_hasAll Psc initCode innerCoreCode selectCode termCode deepCode
    selInitCode
  have hIn : p.HasAt b (dryInnerCoreProcsOf mkBranchB envIn) := hSel.2.1
  unfold dryInnerCoreProcsOf at hIn
  simp only [List.append_assoc] at hIn
  obtain ⟨hHead, hTail1⟩ := hasAt_peel_ic hIn (b' := bDg) rfl
  obtain ⟨hOps, hTail2⟩ := hasAt_peel_ic hTail1 (b' := bDg + 7) (by simp [dgOpsProcs])
  obtain ⟨hEdge, hTail3⟩ := hasAt_peel_ic hTail2 (b' := bDg + 9) (by simp [dgEdgeProcs])
  obtain ⟨hSplit, hBatch⟩ := hasAt_peel_ic hTail3 (b' := bDg + 12) (by simp [dgSplitProcs])
  have hHeadGet (i : ℕ) (hi : i < 22) := hHead.get (i := i) (by simpa using hi)
  have hScInit : envIn.scInit = lay.scInit := rfl
  have hScOp : ∀ j, envIn.scOp j = lay.scOp j := fun _ => rfl
  have hLastInit : envIn.lastInit = lay.lastInit := rfl
  have hOpsEq : envIn.opsBase = ops := rfl
  have hRenEq : envIn.level0Rename = solverTailBase + 11 := rfl
  have hInBase : envIn.innerBase = b := rfl
  refine ⟨by simp [innerCoreCode, dryInnerCoreCodeOf, b],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hOps, hEdge, hSplit, hBatch⟩
  · simpa [dryInnerCoreBranchA, hScInit, hScOp, hLastInit, hOpsEq, hRenEq, hInBase] using
      hHeadGet 0 (by decide)
  · simpa using hHeadGet 1 (by decide)
  · simpa using hHeadGet 2 (by decide)
  · simpa [hOpsEq] using hHeadGet 3 (by decide)
  · simpa [hOpsEq, hInBase] using hHeadGet 4 (by decide)
  · simpa [hOpsEq] using hHeadGet 5 (by decide)
  · simpa [hOpsEq] using hHeadGet 6 (by decide)
  · simpa [hOpsEq, hInBase] using hHeadGet 7 (by decide)
  · simpa using hHeadGet 8 (by decide)
  · simpa [hInBase] using hHeadGet 9 (by decide)
  · simpa [hOpsEq] using hHeadGet 10 (by decide)
  · simpa [hOpsEq] using hHeadGet 11 (by decide)
  · simpa using hHeadGet 12 (by decide)
  · simpa using hHeadGet 13 (by decide)
  · simpa using hHeadGet 14 (by decide)
  · simpa using hHeadGet 15 (by decide)
  · simpa [hInBase] using hHeadGet 16 (by decide)
  · simpa [hInBase] using hHeadGet 17 (by decide)
  · simpa using hHeadGet 18 (by decide)
  · simpa using hHeadGet 19 (by decide)
  · simpa [hInBase] using hHeadGet 20 (by decide)
  · simpa [hOpsEq] using hHeadGet 21 (by decide)

/-- `pathSlotBindContract` at `lay.ordChainCore + 1 + 2` inside `dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_bindC (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand) (w : ℕ) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    MeetsContract w p (lay.ordChainCore + 1 + 2) (pathSlotBindContract w) := by
  intro innerCoreCode inner p lay
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  have hHas : p.HasAt (lay.ordChainCore + 1 + 2) [pathSlotBindBody] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa using hAll.2.2.2.1
  exact pathSlotBind_meetsContract hHas

/-- `wireCanonCopyContract` at `lay.ordChainCore + 1 + 3` inside `dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_canonC (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    {w : ℕ} (hw14 : 14 ≤ w) (v : PathEdgeValue) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    MeetsContract w p (lay.ordChainCore + 1 + 3) (wireCanonCopyContract w v) := by
  intro innerCoreCode inner p lay
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  have hOps := solverOpsProcs_initHelpers hw14
    (dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner selInitCode)
  exact wireCanonCopy_meetsContract v hAll.2.2.2.2.1 hOps.1 hOps.2.1

/-- `dgApplyBatchContract` at `lay.ordChainCore + 1 + 34 + dgIdxApplyBatch` inside
`dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_dgApplyC (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (w vCap eCap : ℕ) (G' : MGraph) (U : List Update) (bW : ℕ) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    MeetsContract w p (lay.ordChainCore + 1 + 34 + dgIdxApplyBatch)
      (dgApplyBatchContract w vCap eCap G' G' U bW) := by
  intro innerCoreCode inner p lay
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  have hDg := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact dgApplyBatch_meetsContract hDg.2.2.2 hDg.2.1 hDg.2.2.1 hDg.1

/-- `dgInitFromListsContract` at `lay.ordChainCore + 1 + 34 + dgIdxInitFromLists` inside
`dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_dgInitC (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand)
    (w vCap eCap : ℕ) (G' : MGraph) (vL : List ℕ) (eTriples : List (ℕ × ℕ × ℕ)) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    MeetsContract w p (lay.ordChainCore + 1 + 34 + dgIdxInitFromLists)
      (dgInitFromListsContract w vCap eCap G' vL eTriples) := by
  intro innerCoreCode inner p lay
  have hAll := dryInnerCoreCodeOf_hasAll Psc initCode selectCode termCode deepCode selInitCode
    mkBranchB hBNoRand
  have hDg := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact dgInitFromLists_meetsContract hDg.2.2.2 hDg.2.1 hDg.1

/-- `level0RenameBody` at `solverTailBase + 11` inside `dryLinkedProgramSel`. -/
theorem dryInnerCoreCodeOf_renP (Psc : DrySparseCorePieces)
    (initCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (mkBranchB : SolverInnerEnv → Stmt) (hBNoRand : ∀ env, (mkBranchB env).NoRand) :
    let innerCoreCode := dryInnerCoreCodeOf mkBranchB hBNoRand
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode)
      selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    p.procs[solverTailBase + 11]? = some level0RenameBody := by
  intro innerCoreCode inner p
  exact solverTail_level0Rename_at
    (dryLinkedProgramSel_tail_hasAt dryWitnessUsed Psc.sc inner selInitCode)

end MinCostFlow.Final.DryRun

end
