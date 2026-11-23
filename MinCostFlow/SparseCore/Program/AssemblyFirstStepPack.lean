module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriver
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Prog
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSpan
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepBunPrepProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourFacts
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepProg
public import MinCostFlow.SparseCore.Program.AssemblyCode
public import MinCostFlow.SparseCore.Program.BundleModule
public import MinCostFlow.SparseCore.Program.SpanBucketInit

import Mathlib.Tactic

/-!
# The code of the first step (`AssemblyFirstStepPack`)

The first step of a branch is one block of procedures, placed at `env.bSelf` in `scProg`
(`asmFsStepCode : ScSubCode`). This file gives the block and the places of its procedures.

* `asmFsStepProcs env` lists the 51 procedures: the driver, the main procedure, the scan of
  Phase 1, the procedures of Phase 2, the procedures of Phase 3, the 37 procedures of Phase 4,
  and the three procedures of the tour block of Phase 3 at the end. The comment of
  `asmFsStepProcsHead` gives each offset. The calls go to these offsets and to the blocks that
  `env` names (the tour, the output graph, the bundle table, the spanners, the copy routine).
* `hasAt_getElem?` reads one procedure off a placement `p.HasAt b l`.
* `asmFsP4Code` is the record of the procedures of Phase 4 (`AsmFirstP4Code`), for a program
  that holds the block at `env.bSelf` and the outside blocks that Phase 4 calls.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- The first 48 procedures of the first step, at `b = env.bSelf`. Offsets:
* `0` the driver, `1` the main procedure, `2` the scan of Phase 1;
* Phase 2: `3` the new components, `4` one component, `5` the spanner of a component,
  `6` the export of its graph, `7` the root of a vertex in the tour;
* Phase 3: `8` the body, `9` the deletion triples, `10` the groups (the tour block is at `48`);
* Phase 4: `11` the body, `12` to `35` the selection and the spanner tasks, `36` to `40` the
  lists of the output graph, `41` to `45` the rotation, `46` and `47` the re-embedding. -/
def asmFsStepProcsHead (env : ScFirstEnv) : List Stmt :=
  [asmFirstStepDriverStmt (env.bSelf + 1) (env.bSelf + 1),
   asmFirstStepMainStmt (env.bSelf + 2) (env.bSelf + 3) (env.bSelf + 8) (env.bSelf + 11),
   asmFirstScanBatchStmt,
   asmFirstNewActStmt (env.bSelf + 4) (env.bSelf + 5),
   asmFirstInitOneCompStmt (env.bSelf + 7) (tourOp env.bTour 4) (env.bBun + bundleOffSort)
     (env.bBun + bundleIdxInitSlots),
   asmFirstInitSpanBody (env.bSelf + 6) (env.bSpan + bsIdxOp0 + 0),
   asmFirstInitExpBody (env.bBun + bundleIdxExportGraph),
   asmFirstTourVertRootStmt (tourOp env.bTour 10),
   asmFirstPhase3Stmt (env.bSelf + 9) (env.bSelf + 10) (env.bSelf + 48 + 2)
     (env.bBun + bundleIdxStep),
   asmFirstBuildDelTriplesStmt (env.bBun + bundleIdxReadParent),
   asmFirstBuildGroupsStmt (env.bBun + bundleOffSort),
   asmFirstPhase4Stmt (env.bSelf + 12) (env.bSelf + 36) (env.bSelf + 41) (env.bSelf + 46),
   asmFirstP4SelStmt (env.bSelf + 13) (env.bSelf + 14),
   asmFirstP4FrontStmt (env.bSelf + 16) (env.bSelf + 17) (env.bSelf + 18),
   asmFirstMarkOutSelStmt (env.bSelf + 15),
   asmFirstEvalTgtEStmt,
   asmFirstP4SpanStmt (env.bSelf + 22) (env.bSelf + 23),
   asmFirstP4SeedStmt (env.bSelf + 19) (env.bSelf + 20) (env.bSelf + 21),
   asmFirstPrepFlagsStmt,
   asmFirstSeedBatchStmt (env.bSelf + 33),
   asmFirstSeedLazyStmt (env.bSelf + 21),
   asmFirstAppendListStmt (env.bSelf + 33),
   asmFirstP4LoopStmt (env.bSelf + 25),
   asmFirstP4NewLoopStmt (env.bSelf + 24),
   asmFirstP4NewStmt (env.bSelf + 35) (env.bSelf + 31),
   asmFirstP4TaskStmt (env.bSpan + bsIdxOp0 + 1) (env.bSelf + 26),
   asmFirstP4AfterStmt (env.bSelf + 27) (env.bSelf + 28) (env.bSelf + 29) (env.bSelf + 30)
     (env.bSelf + 31),
   asmFirstScanSlotUHStmt (env.bSelf + 32),
   asmFirstScanSlotDStmt (env.bSelf + 33) (env.bSelf + 34),
   asmFirstScanSlotRStmt (env.bSelf + 33),
   asmFirstScanDleftStmt (env.bSelf + 32) (env.bSpan + bsOffRead + spanReadIdxPiWalkPtr),
   asmFirstCopySlotListStmt env.readLib.copy (env.bSpan + bsOffRead + spanReadIdxPiWalkPtr),
   asmFirstP4EdgeStmt (env.bSelf + 33) (env.bSelf + 34),
   asmFirstPushDedupStmt,
   asmFirstMarkSlotEdgeStmt,
   asmFirstScanNewSlotStmt (env.bSelf + 33),
   asmFirstP4ListsStmt (env.bSelf + 37) (env.bSelf + 38) (env.bSelf + 39) (env.bSelf + 40),
   asmFirstQueryInsEndsStmt (tourOp env.bTour 10),
   asmFirstBuildDelStmt (env.bBun + bundleOffSort),
   asmFirstBuildInsStmt (env.bBun + bundleOffSort),
   asmFirstCopyInsStmt,
   asmFirstP4RotStmt (env.bSelf + 42) (env.bSelf + 43) (env.bSelf + 44) (env.bSelf + 45),
   asmFirstCollectRotDirectStmt,
   asmFirstCollectRotBatchStmt (env.bSelf + 7),
   asmFirstCollectRotEditsStmt (env.bSelf + 7),
   asmFirstBuildRotStmt (env.bBun + bundleOffSort),
   asmFirstP4ReembStmt (env.bSelf + 47) (env.bSelf + 45),
   asmFirstStrideCopyStmt]

/-- **The procedures of the first step**: the 48 of `asmFsStepProcsHead`, then the tour block of
Phase 3 at offset `48`. -/
def asmFsStepProcs (env : ScFirstEnv) : List Stmt :=
  asmFsStepProcsHead env ++
    asmFirstTourBlockProcs (env.bSelf + 48) env.bTour env.bOut env.readLib.copy

end

public section

theorem asmFsStepProcsHead_length (env : ScFirstEnv) : (asmFsStepProcsHead env).length = 48 :=
  rfl

theorem asmFsStepProcs_noRand (env : ScFirstEnv) : ∀ s ∈ asmFsStepProcs env, s.NoRand := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · simp only [asmFsStepProcsHead, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact asmFirstStepDriverStmt_noRand _ _
    · exact asmFirstStepMainStmt_noRand _ _ _ _
    · exact asmFirstScanBatchStmt_noRand
    · exact asmFirstNewActStmt_noRand _ _
    · exact asmFirstInitOneCompStmt_noRand _ _ _ _
    · exact asmFirstInitSpanBody_noRand _ _
    · exact asmFirstInitExpBody_noRand _
    · exact asmFirstTourVertRootStmt_noRand _
    · exact asmFirstPhase3Stmt_noRand _ _ _ _
    · exact asmFirstBuildDelTriplesStmt_noRand _
    · exact asmFirstBuildGroupsStmt_noRand _
    · exact asmFirstPhase4Stmt_noRand _ _ _ _
    · exact asmFirstP4SelStmt_noRand _ _
    · exact asmFirstP4FrontStmt_noRand _ _ _
    · exact asmFirstMarkOutSelStmt_noRand _
    · exact asmFirstEvalTgtEStmt_noRand
    · exact asmFirstP4SpanStmt_noRand _ _
    · exact asmFirstP4SeedStmt_noRand _ _ _
    · exact asmFirstPrepFlagsStmt_noRand
    · exact asmFirstSeedBatchStmt_noRand _
    · exact asmFirstSeedLazyStmt_noRand _
    · exact asmFirstAppendListStmt_noRand _
    · exact asmFirstP4LoopStmt_noRand _
    · exact asmFirstP4NewLoopStmt_noRand _
    · exact asmFirstP4NewStmt_noRand _ _
    · exact asmFirstP4TaskStmt_noRand _ _
    · exact asmFirstP4AfterStmt_noRand _ _ _ _ _
    · exact asmFirstScanSlotUHStmt_noRand _
    · exact asmFirstScanSlotDStmt_noRand _ _
    · exact asmFirstScanSlotRStmt_noRand _
    · exact asmFirstScanDleftStmt_noRand _ _
    · exact asmFirstCopySlotListStmt_noRand _ _
    · exact asmFirstP4EdgeStmt_noRand _ _
    · exact asmFirstPushDedupStmt_noRand
    · exact asmFirstMarkSlotEdgeStmt_noRand
    · exact asmFirstScanNewSlotStmt_noRand _
    · exact asmFirstP4ListsStmt_noRand _ _ _ _
    · exact asmFirstQueryInsEndsStmt_noRand _
    · exact asmFirstBuildDelStmt_noRand _
    · exact asmFirstBuildInsStmt_noRand _
    · exact asmFirstCopyInsStmt_noRand
    · exact asmFirstP4RotStmt_noRand _ _ _ _
    · exact asmFirstCollectRotDirectStmt_noRand
    · exact asmFirstCollectRotBatchStmt_noRand _
    · exact asmFirstCollectRotEditsStmt_noRand _
    · exact asmFirstBuildRotStmt_noRand _
    · exact asmFirstP4ReembStmt_noRand _ _
    · exact asmFirstStrideCopyStmt_noRand
  · exact asmFirstTourBlockProcs_noRand _ _ _ _ s hs

end

@[expose] public section

/-- **The code of the first step**, with its main entry (the driver) at offset `0`. -/
def asmFsStepCode : ScSubCode where
  procs := asmFsStepProcs
  hnoRand := asmFsStepProcs_noRand
  offMain := 0

end

public section

/-- **One procedure of a placed list**: if `p` holds the list `l` at `b` and the entry `i` of `l`
is `s`, then the procedure `b + i` of `p` is `s`. -/
theorem hasAt_getElem? {p : Program} {b : ℕ} {l : List Stmt} (hp : p.HasAt b l) {i : ℕ}
    {s : Stmt} (h : l[i]? = some s) : p.procs[b + i]? = some s := by
  obtain ⟨hi, hs⟩ := List.getElem?_eq_some_iff.mp h
  have := hp i hi
  rw [this, hs]

/-- The tour block of Phase 3 sits at `env.bSelf + 48`. -/
theorem asmFsStep_hasTourBlock {p : Program} {env : ScFirstEnv}
    (hp : p.HasAt env.bSelf (asmFsStepProcs env)) :
    p.HasAt (env.bSelf + 48)
      (asmFirstTourBlockProcs (env.bSelf + 48) env.bTour env.bOut env.readLib.copy) := by
  unfold asmFsStepProcs at hp
  intro i hi
  have h1 := hp ((asmFsStepProcsHead env).length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ i)] at h1
  simpa [Nat.add_assoc, asmFsStepProcsHead_length] using h1

end

@[expose] public section

/-- **The procedures of Phase 4** (`AsmFirstP4Code`) in a program `p` that holds the first step
at `env.bSelf`, the spanners at `env.bSpan`, the copy routine at `env.readLib.copy`, the sort at
`env.bBun + bundleOffSort`, and the root of an end at `tourOp env.bTour 10` (`HE`). The root of a
vertex is the procedure `env.bSelf + 7`. -/
def asmFsP4Code {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ} {impl : SparsifyImpl} {p : Program}
    {env : ScFirstEnv} (hp : p.HasAt env.bSelf (asmFsStepProcs env))
    (hpSpan : p.HasAt env.bSpan (bucketSpannerProcs impl env.bSpan))
    (hcopy : p.HasAt env.readLib.copy [copyWords])
    (HE : AsmFirstTourEndRootAt TR w p (tourOp env.bTour 10))
    (hpSort : p.HasAt (env.bBun + bundleOffSort) (sortProcs (env.bBun + bundleOffSort))) :
    AsmFirstP4Code TR w impl p (env.bSelf + 7) where
  fSelP := env.bSelf + 12
  fFront := env.bSelf + 13
  fSel := env.bSelf + 14
  fEval := env.bSelf + 15
  fSpan := env.bSelf + 16
  fSeed := env.bSelf + 17
  fFlags := env.bSelf + 18
  fSeedB := env.bSelf + 19
  fSeedL := env.bSelf + 20
  fAppend := env.bSelf + 21
  fLoop := env.bSelf + 22
  fNewLoop := env.bSelf + 23
  fNew := env.bSelf + 24
  bSpan := env.bSpan
  fTask := env.bSelf + 25
  fAfter := env.bSelf + 26
  fScanUH := env.bSelf + 27
  fScanD := env.bSelf + 28
  fScanR := env.bSelf + 29
  fDleft := env.bSelf + 30
  fCopySl := env.bSelf + 31
  fEdge := env.bSelf + 32
  fPush := env.bSelf + 33
  fMark := env.bSelf + 34
  fScanNew := env.bSelf + 35
  bRead := env.bSpan + bsOffRead
  bCopy := env.readLib.copy
  fLists := env.bSelf + 36
  fEnds := env.bSelf + 37
  fDel := env.bSelf + 38
  fIns := env.bSelf + 39
  fCopyIns := env.bSelf + 40
  fEndRoot := tourOp env.bTour 10
  fRot := env.bSelf + 41
  fDirect := env.bSelf + 42
  fBatch := env.bSelf + 43
  fEdits := env.bSelf + 44
  fBuild := env.bSelf + 45
  fReemb := env.bSelf + 46
  fCopyStr := env.bSelf + 47
  bSort := env.bBun + bundleOffSort
  hfFront := hasAt_getElem? hp (i := 13) rfl
  hfSel := hasAt_getElem? hp (i := 14) rfl
  hfEval := hasAt_getElem? hp (i := 15) rfl
  hfSpan := hasAt_getElem? hp (i := 16) rfl
  hfSeed := hasAt_getElem? hp (i := 17) rfl
  hfFlags := hasAt_getElem? hp (i := 18) rfl
  hfSeedB := hasAt_getElem? hp (i := 19) rfl
  hfSeedL := hasAt_getElem? hp (i := 20) rfl
  hfAppend := hasAt_getElem? hp (i := 21) rfl
  hfLoop := hasAt_getElem? hp (i := 22) rfl
  hfNewLoop := hasAt_getElem? hp (i := 23) rfl
  hpSpan := hpSpan
  hfTask := hasAt_getElem? hp (i := 25) rfl
  hfAfter := hasAt_getElem? hp (i := 26) rfl
  hfUH := hasAt_getElem? hp (i := 27) rfl
  hfD := hasAt_getElem? hp (i := 28) rfl
  hfR := hasAt_getElem? hp (i := 29) rfl
  hfDl := hasAt_getElem? hp (i := 30) rfl
  hfC := hasAt_getElem? hp (i := 31) rfl
  hfEdge := hasAt_getElem? hp (i := 32) rfl
  hfPush := hasAt_getElem? hp (i := 33) rfl
  hfMark := hasAt_getElem? hp (i := 34) rfl
  hfNew := hasAt_getElem? hp (i := 24) rfl
  hfN := hasAt_getElem? hp (i := 35) rfl
  hcopy := hcopy
  hread := bucketSpannerProcs_hasReadout hpSpan
  HE := HE
  hfSelP := hasAt_getElem? hp (i := 12) rfl
  hfLists := hasAt_getElem? hp (i := 36) rfl
  hfEnds := hasAt_getElem? hp (i := 37) rfl
  hfDel := hasAt_getElem? hp (i := 38) rfl
  hfIns := hasAt_getElem? hp (i := 39) rfl
  hfCopyIns := hasAt_getElem? hp (i := 40) rfl
  hfRot := hasAt_getElem? hp (i := 41) rfl
  hfDirect := hasAt_getElem? hp (i := 42) rfl
  hfBatch := hasAt_getElem? hp (i := 43) rfl
  hfEdits := hasAt_getElem? hp (i := 44) rfl
  hfBuild := hasAt_getElem? hp (i := 45) rfl
  hfReemb := hasAt_getElem? hp (i := 46) rfl
  hfCopyStr := hasAt_getElem? hp (i := 47) rfl
  hpSort := hpSort

end

end MinCostFlow.SparseCore.Program
