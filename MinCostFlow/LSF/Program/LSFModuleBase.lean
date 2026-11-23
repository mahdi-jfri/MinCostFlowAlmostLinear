module

public import MinCostFlow.LSF.Program.InitFull
public import MinCostFlow.LSF.Program.BatchOps
public import MinCostFlow.LSF.Program.PrepStage
public import MinCostFlow.LSF.Program.WidthsProc
public import MinCostFlow.LSF.Program.TreePhase
public import MinCostFlow.LSF.Program.OrderPhasePre
public import MinCostFlow.LSF.Program.DecompPhase
public import MinCostFlow.LSF.Program.FPhase
public import MinCostFlow.LSF.Program.WstrWidth
public import MinCostFlow.LSF.Program.InitOneProc
public import MinCostFlow.LSF.Program.StoreArgs
public import MinCostFlow.LSF.Program.InitTreeLSSTOps
public import MinCostFlow.LSF.Program.InitTreeQNat
public import MinCostFlow.LSF.Program.InitTreeCopies
public import MinCostFlow.LSF.Program.InitEdgeCopy
public import MinCostFlow.LSF.Program.InitTreeWeights
public import MinCostFlow.LSF.Program.InitTreeCopy
public import MinCostFlow.LSF.Program.InitParams
public import MinCostFlow.LSF.Program.InitScan
public import MinCostFlow.LSF.Program.LSimProc
public import MinCostFlow.LSF.Program.T0Edges
public import MinCostFlow.LSF.Program.RootTree
public import MinCostFlow.LSF.Program.BinaryLift
public import MinCostFlow.LSF.Program.RootStage
public import MinCostFlow.LSF.Program.EndpointIdx
public import MinCostFlow.LSF.Program.Lca
public import MinCostFlow.LSF.Program.CongScatter
public import MinCostFlow.LSF.Program.SubtreeSum
public import MinCostFlow.LSF.Program.CongRank
public import MinCostFlow.LSF.Program.CongOrder
public import MinCostFlow.LSF.Program.UpMin
public import MinCostFlow.LSF.Program.OrderStage
public import MinCostFlow.LSF.Program.TBlockFill
public import MinCostFlow.LSF.Program.TTrack
public import MinCostFlow.LSF.Program.TStage
public import MinCostFlow.LSF.Program.THSize
public import MinCostFlow.LSF.Program.THHeavy
public import MinCostFlow.LSF.Program.THPlace
public import MinCostFlow.LSF.Program.THDepth
public import MinCostFlow.LSF.Program.THProc
public import MinCostFlow.LSF.Program.THStage
public import MinCostFlow.LSF.Program.UArith
public import MinCostFlow.LSF.Program.UArithMul
public import MinCostFlow.LSF.Program.UExt
public import MinCostFlow.LSF.Program.BlkFill
public import MinCostFlow.LSF.Program.WDepth
public import MinCostFlow.LSF.Program.TreeDist
public import MinCostFlow.LSF.Program.DuvPass
public import MinCostFlow.LSF.Program.AccEdge
public import MinCostFlow.LSF.Program.AccLevel
public import MinCostFlow.LSF.Program.FRLevel
public import MinCostFlow.LSF.Program.FRMp
public import MinCostFlow.LSF.Program.FROwn
public import MinCostFlow.LSF.Program.FRRt
public import MinCostFlow.LSF.Program.WstrThresh
public import MinCostFlow.LSF.Program.WstrPrep
public import MinCostFlow.LSF.Program.LevelStep
public import MinCostFlow.LSF.Program.LevelLoop
public import MinCostFlow.LSF.Program.WstrEdge
public import MinCostFlow.LSF.Program.WstrOut
public import MinCostFlow.LSF.Program.Wstr
public import MinCostFlow.LSF.Program.WstrStage
public import MinCostFlow.LSF.Program.DecompDeg
public import MinCostFlow.LSF.Program.DecompGreedy
public import MinCostFlow.LSF.Program.DecompLabel
public import MinCostFlow.LSF.Program.DecompMark
public import MinCostFlow.LSF.Program.DecompClosure
public import MinCostFlow.LSF.Program.DecompWTProc
public import MinCostFlow.LSF.Program.FlagMerge
public import MinCostFlow.LSF.Program.UpClosure
public import MinCostFlow.LSF.Program.RootsStage
public import MinCostFlow.LSF.Program.FGraph
public import MinCostFlow.LSF.Program.FAncFill
public import MinCostFlow.LSF.Program.WKeysProof
public import MinCostFlow.LSF.Program.WAddV
public import MinCostFlow.LSF.Program.WScanProof
public import MinCostFlow.LSF.Program.WBlockProof


/-!
# Relocatable Module Assembly and Determinism for Dynamic LSF (`LSFModuleBase`)

Defines the relocatable offsets, submodule procedure lists, `lsfModuleProcs`, `lsfModule`,
length lemmas, determinism (`lsfModuleProcs_noRand`, `lsfModule_isDeterministic`), and `HasAt`
chunk extraction (`LSFModuleHasAt`, `lsfModuleHasAt_of_hasAt`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-! ## Relocatable module offsets -/

def lsfBaseLsst (b : ℕ) : ℕ := lsfSharedEnd b
def lsfBaseA1 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseLsst b + (87 + Q_AN.procs.length)
def lsfBaseA2 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseA1 Q_AN b + 14
def lsfBaseB1 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseA2 Q_AN b + 4
def lsfBaseB2 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseB1 Q_AN b + 11
def lsfBaseC1 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseB2 Q_AN b + 12
def lsfBaseC2 (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseC1 Q_AN b + 15
def lsfBaseD (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseC2 Q_AN b + 14
def lsfBaseOne (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseD Q_AN b + 15
def lsfBaseBat (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseOne Q_AN b + 3
def lsfModuleEnd (Q_AN : Program) (b : ℕ) : ℕ := lsfBaseBat Q_AN b + 10

/-- `InitIdx` wired to the relocatable LSF module at base `b`. -/
def lsfInitIdx (Q_AN : Program) (b : ℕ) : InitIdx where
  log2 := lsfBaseUtils b + idxUtilLog2
  prep := lsfBaseA1 Q_AN b + 3
  widths := lsfBaseA1 Q_AN b + 4
  tree := lsfBaseA2 Q_AN b + 3
  order := lsfBaseB2 Q_AN b + 11
  lb := lsfBaseD Q_AN b + 0
  decomp := lsfBaseD Q_AN b + 5
  forest := lsfBaseD Q_AN b + 12
  store20 := lsfBaseD Q_AN b + 13
  store24 := lsfBaseD Q_AN b + 14

/-- Natural-number ceiling of `max K_AN 1`, matching `defaultC_ceil K_AN` in `lsfSharedProcs`. -/
noncomputable def lsfKNat (K_AN : ℝ) : ℕ := Nat.ceil (max K_AN 1)

lemma defaultC_ceil_lsfKNat (K_AN : ℝ) :
    defaultC_ceil ((lsfKNat K_AN : ℕ) : ℝ) = defaultC_ceil K_AN := by
  dsimp only [defaultC_ceil, lsfKNat]
  have h1 : (1 : ℝ) ≤ (Nat.ceil (max K_AN 1) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.le_ceil (max K_AN 1)
      rw [h0, Nat.cast_zero] at this
      linarith [le_max_right K_AN 1]))
  rw [max_eq_left h1, Nat.ceil_natCast]

/-! ## Submodule procedure lists -/

def lsfProcsA1 (Q_AN : Program) (c_AN b h : ℕ) : List Stmt :=
  let a1 := lsfBaseA1 Q_AN b
  let u := lsfBaseUtils b
  [ initParamsProc (u + idxUtilLog2)
  , initScanStmt
  , initCopyGStmt (lsfBaseDg b)
  , prepStageProc (a1 + 0) (a1 + 1) (a1 + 2)
  , widthsProc (u + idxUtilLog2)
  , limbsToWordProc
  , sumWeightsProc b
  , multQNatStepProc b (a1 + 5)
  , initTreeQNatProc b h (a1 + 6) (a1 + 7)
  , emitEdgeCopiesProc b
  , initTreeCopiesProc b (a1 + 9)
  , initMarkBridgesStmt u
  , treeCopiesProc (a1 + 8) (u + idxUtilMemFill) (a1 + 10) (a1 + 11)
  , lsimProc (u + idxUtilLog2) c_AN h ]

def lsfProcsA2 (Q_AN : Program) (b h : ℕ) : List Stmt :=
  let a1 := lsfBaseA1 Q_AN b
  let a2 := lsfBaseA2 Q_AN b
  [ lsstFrontierProc (lsfBaseLsst b) h
  , t0EdgesProc
  , treeLsstProc (a2 + 0) (a2 + 1)
  , treePhaseProc (a1 + 12) (a1 + 13) (a2 + 2) ]

def lsfProcsB1 (Q_AN : Program) (b : ℕ) : List Stmt :=
  let b1 := lsfBaseB1 Q_AN b
  let u := lsfBaseUtils b
  [ rootTreeProc
  , upVProc
  , rootStageProc (b1 + 0) (u + idxUtilMemCopy) (b1 + 1)
  , storeWordStmt
  , endpointIdxProc
  , lcaProc
  , congScatterProc (b1 + 5) (u + idxUtilMemFill) (u + idxUtilMemCopy)
      (u + idxUtilAddTo) (u + idxUtilSubFrom)
  , subtreeSumProc (u + idxUtilAddTo)
  , congRankProc (u + idxUtilKeyedMergeSort)
  , congOrderProc (u + idxUtilMemFill) (b1 + 6) (b1 + 7) (b1 + 8)
  , upMinProc ]

def lsfProcsB2 (Q_AN : Program) (b h : ℕ) : List Stmt :=
  let b1 := lsfBaseB1 Q_AN b
  let b2 := lsfBaseB2 Q_AN b
  let u := lsfBaseUtils b
  let emptyG : MGraph := { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  [ orderStageProc (b1 + 4) (b1 + 9) (b1 + 10)
  , tBlockFillProc
  , tTrackProc (lsfBaseDg b)
  , tStageProc (u + idxUtilMemCopy) (b2 + 1) (b2 + 2)
  , thSizeProc
  , thHeavyProc
  , thOffProc
  , thPlaceProc
  , thDepthProc
  , thProc (b2 + 4) (b2 + 5) (b2 + 6) (b2 + 7) (b2 + 8)
  , thStageProc (b2 + 9) (u + idxUtilMemCopy)
  , orderPhaseProc 0 h emptyG emptyG [] [] (b1 + 2) (b1 + 3) (b2 + 0) (b2 + 3) (b2 + 10) ]

def lsfProcsC1 (Q_AN : Program) (b h : ℕ) : List Stmt :=
  let b1 := lsfBaseB1 Q_AN b
  let c1 := lsfBaseC1 Q_AN b
  [ uAccProc h
  , uLoadWordProc h
  , uMulProc (c1 + 0)
  , uExtProc
  , idFillProc
  , blkExtLoopProc (c1 + 3)
  , wDepthProc (c1 + 0)
  , treeDistProc (c1 + 0) (b1 + 5)
  , duvProc (c1 + 7)
  , accEdgeProc (c1 + 0)
  , accLevelProc (c1 + 9)
  , levelFlagProc
  , frMpProc
  , frOwnProc
  , frRtProc ]

def lsfProcsC2 (Q_AN : Program) (b : ℕ) : List Stmt :=
  let c1 := lsfBaseC1 Q_AN b
  let c2 := lsfBaseC2 Q_AN b
  let u := lsfBaseUtils b
  [ threshProc (u + idxUtilLog2) (c1 + 1) (c1 + 2) (u + idxUtilEmitDefaultC)
  , wstrPrepProc (c1 + 4) (c1 + 5) (u + idxUtilMemFill) (c1 + 6) (c1 + 8)
  , levelStepProc (c1 + 11) (c1 + 12) (c1 + 13) (c1 + 14) (c1 + 8) (c1 + 10)
  , levelsProc (c2 + 2)
  , wstrEdgeProc (c1 + 1) (c1 + 0) (c1 + 2) (lsfBaseLess b + 2) (c1 + 3)
  , wstrOutProc (c2 + 4)
  , wstrProc (c2 + 0) (c2 + 1) (c2 + 3) (c1 + 5) (c2 + 5)
  , wstrStageProc (c2 + 6)
  , decompDegProc
  , decompGreedyProc
  , decompLabelProc
  , decompMarkProc
  , decompClosureProc
  , decompWTProc (c2 + 8) (c2 + 9) (c2 + 10) (c2 + 11) (c2 + 12) ]

def lsfProcsD (Q_AN : Program) (b h : ℕ) : List Stmt :=
  let c1 := lsfBaseC1 Q_AN b
  let c2 := lsfBaseC2 Q_AN b
  let d := lsfBaseD Q_AN b
  let u := lsfBaseUtils b
  [ wstrLBProc (u + idxUtilLog2)
  , flagMergeProc
  , upLevelProc
  , upClosureProc (d + 2)
  , rootsStageProc (d + 3) (c1 + 12) (c1 + 13) (c1 + 14)
  , decompPhaseProc 0 h 0 (c2 + 13) (d + 0) (c2 + 7) (u + idxUtilMemCopy) (d + 1) (d + 4)
  , fGraphProc (lsfBaseDg b)
  , fAncFillProc
  , wKeysProc (c1 + 1)
  , wAddVProc
  , wScanProc (d + 9)
  , wBlockProc (d + 8) (u + idxUtilKeyedMergeSort) (d + 10)
  , fPhaseProc 0 h (d + 6) (d + 7) (d + 11)
  , storeArgsStmt 0 20
  , storeArgsStmt 0 24 ]

def lsfProcsOne (h : ℕ) : List Stmt :=
  [ initOneBlocksProc
  , initOneWstrProc h
  , storeArgsStmt 0 8 ]

def lsfProcsBat (Q_AN : Program) (b : ℕ) : List Stmt :=
  let bat := lsfBaseBat Q_AN b
  let dg := lsfBaseDg b
  [ minEdgeUpProc
  , splitCompBFSProc
  , addOrigRootProc (bat + 0) (dg + 7 + dgIdxDeleteEdge) (bat + 1)
  , lsfSetWstrOneProc
  , lsfTBlockInsertProc (dg + 7 + dgIdxInsertEdge)
  , lsfTBlockDeleteProc (dg + 7 + dgIdxDeleteEdge)
  , lsfTBlockSplitProc (dg + dgIdxAddVertex) (dg + 9 + dgIdxMoveSlotLoop)
  , lsfInsertUpdateProc (bat + 2) (dg + 7 + dgIdxInsertEdge) (bat + 4) (bat + 3)
  , lsfDeleteUpdateProc (bat + 2) (dg + 7 + dgIdxDeleteEdge) (bat + 5)
  , lsfSplitUpdateProc (bat + 2) (dg + 12 + dgIdxApplyUpdate) (bat + 1) (bat + 6) ]

lemma lsfProcsA1_length (Q_AN : Program) (c_AN b h : ℕ) : (lsfProcsA1 Q_AN c_AN b h).length = 14 := rfl
lemma lsfProcsA2_length (Q_AN : Program) (b h : ℕ) : (lsfProcsA2 Q_AN b h).length = 4 := rfl
lemma lsfProcsB1_length (Q_AN : Program) (b : ℕ) : (lsfProcsB1 Q_AN b).length = 11 := rfl
lemma lsfProcsB2_length (Q_AN : Program) (b h : ℕ) : (lsfProcsB2 Q_AN b h).length = 12 := rfl
lemma lsfProcsC1_length (Q_AN : Program) (b h : ℕ) : (lsfProcsC1 Q_AN b h).length = 15 := rfl
lemma lsfProcsC2_length (Q_AN : Program) (b : ℕ) : (lsfProcsC2 Q_AN b).length = 14 := rfl
lemma lsfProcsD_length (Q_AN : Program) (b h : ℕ) : (lsfProcsD Q_AN b h).length = 15 := rfl
lemma lsfProcsOne_length (h : ℕ) : (lsfProcsOne h).length = 3 := rfl
lemma lsfProcsBat_length (Q_AN : Program) (b : ℕ) : (lsfProcsBat Q_AN b).length = 10 := rfl

/-- Complete relocatable list of procedures for the dynamic LSF data structure starting at index `b`.
Entry `b + lsfIdxInit` (`b + 0`) is `Initialize`; entry `b + lsfIdxBatch` (`b + 1`) is `ApplyBatch`. -/
noncomputable def lsfModuleProcs (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) : List Stmt :=
  [ lsfInitBody (lsfInitIdx Q_AN b) (lsfBaseOne Q_AN b + 0) (lsfBaseOne Q_AN b + 1)
      (lsfBaseOne Q_AN b + 2) h
  , lsfApplyBatchProc (lsfBaseBat Q_AN b + 7) (lsfBaseBat Q_AN b + 8) (lsfBaseBat Q_AN b + 9) ] ++
  lsfSharedProcs b (lsfKNat K_AN) h ++
  lsstModule Q_AN (lsfBaseLsst b) h ++
  lsfProcsA1 Q_AN c_AN b h ++
  lsfProcsA2 Q_AN b h ++
  lsfProcsB1 Q_AN b ++
  lsfProcsB2 Q_AN b h ++
  lsfProcsC1 Q_AN b h ++
  lsfProcsC2 Q_AN b ++
  lsfProcsD Q_AN b h ++
  lsfProcsOne h ++
  lsfProcsBat Q_AN b

/-- Standalone deterministic WordRAM program for the dynamic LSF data structure (Lemma 5.4). -/
noncomputable def lsfModule (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) : Program :=
  ⟨lsfModuleProcs Q_AN c_AN K_AN 0 h⟩

lemma lsfModuleProcs_length (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    (lsfModuleProcs Q_AN c_AN K_AN b h).length = 257 + Q_AN.procs.length := by
  simp only [lsfModuleProcs, List.length_append, lsfSharedProcs_length, lsstModule_length,
    lsfProcsA1_length, lsfProcsA2_length, lsfProcsB1_length, lsfProcsB2_length,
    lsfProcsC1_length, lsfProcsC2_length, lsfProcsD_length, lsfProcsOne_length,
    lsfProcsBat_length, List.length_cons, List.length_nil]
  omega

lemma lsfModuleEnd_eq (Q_AN : Program) (b : ℕ) :
    lsfModuleEnd Q_AN b = b + (257 + Q_AN.procs.length) := by
  dsimp only [lsfModuleEnd, lsfBaseBat, lsfBaseOne, lsfBaseD, lsfBaseC2, lsfBaseC1,
    lsfBaseB2, lsfBaseB1, lsfBaseA2, lsfBaseA1, lsfBaseLsst, lsfSharedEnd, lsfBaseUtils,
    lsfBaseIntDiv, lsfBaseMul, lsfBaseSub, lsfBaseAdd, lsfBaseShiftL, lsfBaseLess,
    lsfBaseCopy, lsfBaseSort, lsfBaseDg]
  omega

/-! ## Determinism (`NoRand` / `IsDeterministic`) -/

private lemma lsfProcsA1_noRand (Q_AN : Program) (c_AN b h : ℕ) :
    ∀ s ∈ lsfProcsA1 Q_AN c_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfProcsA1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initParamsProc_noRand _
  · exact initScanStmt_noRand
  · exact initCopyGStmt_noRand _
  · exact prepStageProc_noRand _ _ _
  · exact widthsProc_noRand _
  · exact limbsToWordProc_noRand
  · exact sumWeightsProc_noRand _
  · exact multQNatStepProc_noRand _ _
  · exact initTreeQNatProc_noRand _ _ _ _
  · exact emitEdgeCopiesProc_noRand _
  · exact initTreeCopiesProc_noRand _ _
  · exact initMarkBridgesStmt_noRand _
  · exact treeCopiesProc_noRand _ _ _ _
  · exact lsimProc_noRand _ _ _

private lemma lsfProcsA2_noRand (Q_AN : Program) (b h : ℕ) :
    ∀ s ∈ lsfProcsA2 Q_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfProcsA2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact lsstFrontierProc_noRand _ _
  · exact t0EdgesProc_noRand
  · exact treeLsstProc_noRand _ _
  · exact treePhaseProc_noRand _ _ _

private lemma lsfProcsB1_noRand (Q_AN : Program) (b : ℕ) :
    ∀ s ∈ lsfProcsB1 Q_AN b, s.NoRand := by
  intro s hs
  simp only [lsfProcsB1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rootTreeProc_noRand
  · exact upVProc_noRand
  · exact rootStageProc_noRand _ _ _
  · exact storeWordStmt_noRand
  · exact endpointIdxProc_noRand
  · exact lcaProc_noRand
  · exact congScatterProc_noRand _ _ _ _ _
  · exact subtreeSumProc_noRand _
  · exact congRankProc_noRand _
  · exact congOrderProc_noRand _ _ _ _
  · exact upMinProc_noRand

private lemma lsfProcsB2_noRand (Q_AN : Program) (b h : ℕ) :
    ∀ s ∈ lsfProcsB2 Q_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfProcsB2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact orderStageProc_noRand _ _ _
  · exact tBlockFillProc_noRand
  · exact tTrackProc_noRand _
  · exact tStageProc_noRand _ _ _
  · exact thSizeProc_noRand
  · exact thHeavyProc_noRand
  · exact thOffProc_noRand
  · exact thPlaceProc_noRand
  · exact thDepthProc_noRand
  · exact thProc_noRand _ _ _ _ _
  · exact thStageProc_noRand _ _
  · exact callSeqStmt_noRand _ _ _ _

private lemma lsfProcsC1_noRand (Q_AN : Program) (b h : ℕ) :
    ∀ s ∈ lsfProcsC1 Q_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfProcsC1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uAccProc_noRand _
  · exact uLoadWordProc_noRand _
  · exact uMulProc_noRand _
  · exact uExtProc_noRand
  · exact idFillProc_noRand
  · exact blkExtLoopProc_noRand _
  · exact wDepthProc_noRand _
  · exact treeDistProc_noRand _ _
  · exact duvProc_noRand _
  · exact accEdgeProc_noRand _
  · exact accLevelProc_noRand _
  · exact levelFlagProc_noRand
  · exact frMpProc_noRand
  · exact frOwnProc_noRand
  · exact frRtProc_noRand

private lemma lsfProcsC2_noRand (Q_AN : Program) (b : ℕ) :
    ∀ s ∈ lsfProcsC2 Q_AN b, s.NoRand := by
  intro s hs
  simp only [lsfProcsC2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threshProc_noRand _ _ _ _
  · exact wstrPrepProc_noRand _ _ _ _ _
  · exact levelStepProc_noRand _ _ _ _ _ _
  · exact levelsProc_noRand _
  · exact wstrEdgeProc_noRand _ _ _ _ _
  · exact wstrOutProc_noRand _
  · exact wstrProc_noRand _ _ _ _ _
  · exact wstrStageProc_noRand _
  · exact decompDegProc_noRand
  · exact decompGreedyProc_noRand
  · exact decompLabelProc_noRand
  · exact decompMarkProc_noRand
  · exact decompClosureProc_noRand
  · exact decompWTProc_noRand _ _ _ _ _

private lemma lsfProcsD_noRand (Q_AN : Program) (b h : ℕ) :
    ∀ s ∈ lsfProcsD Q_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfProcsD, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wstrLBProc_noRand _
  · exact flagMergeProc_noRand
  · exact upLevelProc_noRand
  · exact upClosureProc_noRand _
  · exact rootsStageProc_noRand _ _ _ _
  · exact decompPhaseProc_noRand _ _ _ _ _ _ _ _ _
  · exact fGraphProc_noRand _
  · exact fAncFillProc_noRand
  · exact wKeysProc_noRand _
  · exact wAddVProc_noRand
  · exact wScanProc_noRand _
  · exact wBlockProc_noRand _ _ _
  · exact callSeqStmt_noRand _ _ _ _
  · exact storeArgsStmt_noRand _ _
  · exact storeArgsStmt_noRand _ _

private lemma lsfProcsOne_noRand (h : ℕ) : ∀ s ∈ lsfProcsOne h, s.NoRand := by
  intro s hs
  simp only [lsfProcsOne, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact initOneBlocksProc_noRand
  · exact initOneWstrProc_noRand _
  · exact storeArgsStmt_noRand _ _

private lemma lsfProcsBat_noRand (Q_AN : Program) (b : ℕ) :
    ∀ s ∈ lsfProcsBat Q_AN b, s.NoRand := by
  intro s hs
  simp only [lsfProcsBat, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact minEdgeUpProc_noRand
  · exact splitCompBFSProc_noRand
  · exact addOrigRootProc_noRand _ _ _
  · exact lsfSetWstrOneProc_noRand
  · exact lsfTBlockInsertProc_noRand _
  · exact lsfTBlockDeleteProc_noRand _
  · exact lsfTBlockSplitProc_noRand _ _
  · exact lsfInsertUpdateProc_noRand _ _ _ _
  · exact lsfDeleteUpdateProc_noRand _ _ _
  · exact lsfSplitUpdateProc_noRand _ _ _ _

/-- Every procedure in `lsfModuleProcs` is deterministic (`NoRand`). -/
theorem lsfModuleProcs_noRand (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    ∀ s ∈ lsfModuleProcs Q_AN c_AN K_AN b h, s.NoRand := by
  intro s hs
  simp only [lsfModuleProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((((((((((rfl | rfl) | hSh) | hLsst) | hA1) | hA2) | hB1) | hB2) | hC1) | hC2) | hD) | hOne) | hBat
  · exact lsfInitBody_noRand _ _ _ _ _
  · exact lsfApplyBatchProc_noRand _ _ _
  · exact lsfSharedProcs_noRand _ _ _ s hSh
  · exact lsstModule_noRand _ _ _ s hLsst
  · exact lsfProcsA1_noRand _ _ _ _ s hA1
  · exact lsfProcsA2_noRand _ _ _ s hA2
  · exact lsfProcsB1_noRand _ _ s hB1
  · exact lsfProcsB2_noRand _ _ _ s hB2
  · exact lsfProcsC1_noRand _ _ _ s hC1
  · exact lsfProcsC2_noRand _ _ s hC2
  · exact lsfProcsD_noRand _ _ _ s hD
  · exact lsfProcsOne_noRand _ s hOne
  · exact lsfProcsBat_noRand _ _ s hBat

/-- The standalone dynamic LSF program `lsfModule` is deterministic. -/
theorem lsfModule_isDeterministic (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) :
    (lsfModule Q_AN c_AN K_AN h).IsDeterministic :=
  lsfModuleProcs_noRand Q_AN c_AN K_AN 0 h

/-! ## `HasAt` chunk extraction -/

structure LSFModuleHasAt (p Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) : Prop where
  hInit : p.procs[b + lsfIdxInit]? = some
    (lsfInitBody (lsfInitIdx Q_AN b) (lsfBaseOne Q_AN b + 0) (lsfBaseOne Q_AN b + 1)
      (lsfBaseOne Q_AN b + 2) h)
  hBatch : p.procs[b + lsfIdxBatch]? = some
    (lsfApplyBatchProc (lsfBaseBat Q_AN b + 7) (lsfBaseBat Q_AN b + 8) (lsfBaseBat Q_AN b + 9))
  hShared : p.HasAt (b + 2) (lsfSharedProcs b (lsfKNat K_AN) h)
  hLsst : p.HasAt (lsfBaseLsst b) (lsstModule Q_AN (lsfBaseLsst b) h)
  hA1 : p.HasAt (lsfBaseA1 Q_AN b) (lsfProcsA1 Q_AN c_AN b h)
  hA2 : p.HasAt (lsfBaseA2 Q_AN b) (lsfProcsA2 Q_AN b h)
  hB1 : p.HasAt (lsfBaseB1 Q_AN b) (lsfProcsB1 Q_AN b)
  hB2 : p.HasAt (lsfBaseB2 Q_AN b) (lsfProcsB2 Q_AN b h)
  hC1 : p.HasAt (lsfBaseC1 Q_AN b) (lsfProcsC1 Q_AN b h)
  hC2 : p.HasAt (lsfBaseC2 Q_AN b) (lsfProcsC2 Q_AN b)
  hD : p.HasAt (lsfBaseD Q_AN b) (lsfProcsD Q_AN b h)
  hOne : p.HasAt (lsfBaseOne Q_AN b) (lsfProcsOne h)
  hBat : p.HasAt (lsfBaseBat Q_AN b) (lsfProcsBat Q_AN b)

lemma hasAt_cast {p : Program} {a : ℕ} (b : ℕ) {xs : List Stmt} (h : p.HasAt a xs) (heq : a = b) :
    p.HasAt b xs := heq ▸ h

lemma lsfModuleHasAt_of_hasAt {p Q_AN : Program} {c_AN b h : ℕ} {K_AN : ℝ}
    (hp : p.HasAt b (lsfModuleProcs Q_AN c_AN K_AN b h)) :
    LSFModuleHasAt p Q_AN c_AN K_AN b h := by
  have hp0 : p.HasAt b
      ([lsfInitBody (lsfInitIdx Q_AN b) (lsfBaseOne Q_AN b + 0) (lsfBaseOne Q_AN b + 1)
          (lsfBaseOne Q_AN b + 2) h,
        lsfApplyBatchProc (lsfBaseBat Q_AN b + 7) (lsfBaseBat Q_AN b + 8) (lsfBaseBat Q_AN b + 9)] ++
       (lsfSharedProcs b (lsfKNat K_AN) h ++
        (lsstModule Q_AN (lsfBaseLsst b) h ++
         (lsfProcsA1 Q_AN c_AN b h ++
          (lsfProcsA2 Q_AN b h ++
           (lsfProcsB1 Q_AN b ++
            (lsfProcsB2 Q_AN b h ++
             (lsfProcsC1 Q_AN b h ++
              (lsfProcsC2 Q_AN b ++
               (lsfProcsD Q_AN b h ++
                (lsfProcsOne h ++ lsfProcsBat Q_AN b))))))))))) := by
    simpa only [lsfModuleProcs, List.append_assoc] using hp
  have hEnt := Num.hasAt_append_left hp0
  have r1 := hasAt_cast (b + 2) (Num.hasAt_append_right hp0) (by simp)
  have hSh := Num.hasAt_append_left r1
  have r2 := hasAt_cast (lsfBaseLsst b) (Num.hasAt_append_right r1) (by
    rw [lsfSharedProcs_length]
    dsimp only [lsfBaseLsst, lsfSharedEnd, lsfBaseUtils, lsfBaseIntDiv, lsfBaseMul, lsfBaseSub,
      lsfBaseAdd, lsfBaseShiftL, lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg])
  have hLsst := Num.hasAt_append_left r2
  have r3 := hasAt_cast (lsfBaseA1 Q_AN b) (Num.hasAt_append_right r2) (by rw [lsstModule_length]; rfl)
  have hA1 := Num.hasAt_append_left r3
  have r4 := hasAt_cast (lsfBaseA2 Q_AN b) (Num.hasAt_append_right r3) (by rw [lsfProcsA1_length]; rfl)
  have hA2 := Num.hasAt_append_left r4
  have r5 := hasAt_cast (lsfBaseB1 Q_AN b) (Num.hasAt_append_right r4) (by rw [lsfProcsA2_length]; rfl)
  have hB1 := Num.hasAt_append_left r5
  have r6 := hasAt_cast (lsfBaseB2 Q_AN b) (Num.hasAt_append_right r5) (by rw [lsfProcsB1_length]; rfl)
  have hB2 := Num.hasAt_append_left r6
  have r7 := hasAt_cast (lsfBaseC1 Q_AN b) (Num.hasAt_append_right r6) (by rw [lsfProcsB2_length]; rfl)
  have hC1 := Num.hasAt_append_left r7
  have r8 := hasAt_cast (lsfBaseC2 Q_AN b) (Num.hasAt_append_right r7) (by rw [lsfProcsC1_length]; rfl)
  have hC2 := Num.hasAt_append_left r8
  have r9 := hasAt_cast (lsfBaseD Q_AN b) (Num.hasAt_append_right r8) (by rw [lsfProcsC2_length]; rfl)
  have hD := Num.hasAt_append_left r9
  have r10 := hasAt_cast (lsfBaseOne Q_AN b) (Num.hasAt_append_right r9) (by rw [lsfProcsD_length]; rfl)
  have hOne := Num.hasAt_append_left r10
  have hBat := hasAt_cast (lsfBaseBat Q_AN b) (Num.hasAt_append_right r10) (by rw [lsfProcsOne_length]; rfl)
  exact
    { hInit := hEnt.get (i := 0) (by simp)
      hBatch := hEnt.get (i := 1) (by simp)
      hShared := hSh
      hLsst := hLsst
      hA1 := hA1
      hA2 := hA2
      hB1 := hB1
      hB2 := hB2
      hC1 := hC1
      hC2 := hC2
      hD := hD
      hOne := hOne
      hBat := hBat }

end

end MinCostFlow.LSF.Program
