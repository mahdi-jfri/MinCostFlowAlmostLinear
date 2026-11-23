module

public import MinCostFlow.DynSpanner.Program.DynSpannerDS

/-!
# Relocatable Deterministic Module for `dynSpannerDS`: Definitions (`SpanModuleDefs`)

Defines the offset table, chunked concatenation `dynSpannerDSProcs impl b`, and base records
(`dynSpannerDSInitBases`, `dynSpannerDSStepZeroBases`, `dynSpannerDSStepPosNEBases`,
`dynSpannerDSStepPosFullBases`, `dynSpannerDSUpdateLoopBases`) anchoring all 62 sub-procedure
blocks of `dynSpannerDS` at a single base index `b`.

Placing the variable-length relocated guest table `sparsifyGuestProcs impl (b + 108)` at the end
gives every fixed library block a constant offset from `b`, with initialization at
`b + dynSpannerInitOff` (`b + 52`) and batch update at `b + dynSpannerUpdateOff` (`b + 107`).
The length, determinism, and `DSRep.Implements` proofs are in `SpanModule.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

@[expose] public section

def dsOffAux : ℕ := 0
def dsOffSort : ℕ := 6
def dsOffOps : ℕ := 10
def dsOffEdge : ℕ := 17
def dsOffSplit : ℕ := 19
def dsOffBatch : ℕ := 22
def dsOffGT : ℕ := 25
def dsOffEmit : ℕ := 30
def dsOffFwd : ℕ := 33
def dsOffRevPrim : ℕ := 35
def dsOffRevCore : ℕ := 37
def dsOffRevDyn : ℕ := 38
def dsOffSpDyn : ℕ := 39
def dsOffRev : ℕ := 40
def dsOffLW : ℕ := 42
def dsOffPhase : ℕ := 45
def dsOffInit : ℕ := 50
def dsOffZAux : ℕ := 53
def dsOffF : ℕ := 56
def dsOffR : ℕ := 57
def dsOffD : ℕ := 58
def dsOffU : ℕ := 59
def dsOffPref : ℕ := 60
def dsOffCB : ℕ := 61
def dsOffZ : ℕ := 62
def dsOffClrA : ℕ := 63
def dsOffSZ : ℕ := 64
def dsOffSS : ℕ := 65
def dsOffEmb : ℕ := 66
def dsOffC : ℕ := 70
def dsOffCA : ℕ := 71
def dsOffRe : ℕ := 72
def dsOffRA : ℕ := 73
def dsOffRS : ℕ := 74
def dsOffDR : ℕ := 75
def dsOffDA : ℕ := 76
def dsOffIR : ℕ := 77
def dsOffUT : ℕ := 78
def dsOffAU : ℕ := 79
def dsOffUE : ℕ := 80
def dsOffFL : ℕ := 81
def dsOffRB : ℕ := 82
def dsOffSE : ℕ := 83
def dsOffST : ℕ := 84
def dsOffFin : ℕ := 85
def dsOffCD : ℕ := 86
def dsOffNE : ℕ := 87
def dsOffEm : ℕ := 88
def dsOffEp : ℕ := 89
def dsOffPos : ℕ := 90
def dsOffAffP : ℕ := 91
def dsOffHead : ℕ := 94
def dsOffWP : ℕ := 95
def dsOffProj : ℕ := 96
def dsOffBP : ℕ := 97
def dsOffPS : ℕ := 98
def dsOffAS : ℕ := 99
def dsOffSum : ℕ := 100
def dsOffFull : ℕ := 101
def dsOffUL : ℕ := 102
def dsOffOp : ℕ := 107
def dsOffGuest : ℕ := 108

/-- Offset of `dsInitStmt` within `dynSpannerDSProcs impl b`. -/
def dynSpannerInitOff : ℕ := dsOffInit + initIdx

/-- Offset of `dsUpdateOpStmt` within `dynSpannerDSProcs impl b`. -/
def dynSpannerUpdateOff : ℕ := dsOffOp

/-- Chunk 1 (offsets `0..34`, length `35`): utilities, dynamic graph, forward translation. -/
def dynSpannerChunk1 (b : ℕ) : List Stmt :=
  stepAuxProcs ++
  sortProcs (b + dsOffSort) ++
  dgOpsProcs ++
  dgEdgeProcs (b + dsOffOps) ++
  dgSplitProcs (b + dsOffOps) (b + dsOffSplit) ++
  dgBatchProcs (b + dsOffOps) (b + dsOffEdge) (b + dsOffSplit) (b + dsOffBatch) ++
  gtProcs (b + dsOffSort) (b + dsOffOps) ++
  gtEmitProcs (b + dsOffSort) (b + dsOffOps) (b + dsOffGT) ++
  gtForwardProcs (b + dsOffOps) (b + dsOffGT) (b + dsOffEmit) (b + dsOffFwd)

/-- Chunk 2 (offsets `35..52`, length `18`): reverse translation, sparsifier host, walks, init. -/
def dynSpannerChunk2 (impl : SparsifyImpl) (b : ℕ) : List Stmt :=
  gtRevPrimProcs ++
  gtRevCoreProcs (b + dsOffBatch) (b + dsOffRevPrim) ++
  gtRevDynProcs (b + dsOffOps) (b + dsOffGT) (b + dsOffRevCore) ++
  sparsifyDynProcs impl.program.regBound impl.cw (b + dsOffFwd) (b + dsOffRevDyn) (b + dsOffGuest) ++
  revProcs (b + dsOffOps) (b + dsOffRev) ++
  levelWalkProcs (b + dsOffOps) (b + dsOffRev) ++
  phaseProcs (b + dsOffOps) (b + dsOffEdge) ++
  initProcs (b + dsOffOps) (b + dsOffEdge) (b + dsOffBatch) (b + dsOffPhase)
    (b + dsOffLW) (b + dsOffSpDyn) (b + dsOffInit)

/-- Chunk 3 (offsets `53..64`, length `12`): prefix, clearers, and level-0 restart step. -/
def dynSpannerChunk3 (b : ℕ) : List Stmt :=
  stepZeroAuxProcs (b + dsOffOps) ++
  filterCopyProcs ++
  restrictRecProcs (b + dsOffF) ++
  levelsDeleteProcs (b + dsOffPhase) ++
  applyUProcs (b + dsOffBatch) (b + dsOffD) ++
  stepPrefixProcs (b + dsOffR) (b + dsOffU) ++
  clearBucketsProcs ++
  zeroRangeProcs ++
  clearAboveProcs (b + dsOffZ) ++
  stepZeroProcs (b + dsOffAux) (b + dsOffZAux) (b + dsOffPref) (b + dsOffPhase)
    (b + dsOffCB) (b + dsOffClrA) (b + dsOffInit)

/-- Chunk 4 (offsets `65..87`, length `23`): positive-level nonempty branch and tail. -/
def dynSpannerChunk4 (b : ℕ) : List Stmt :=
  sparsifyStageProcs (b + dsOffSpDyn) (b + dsOffLW) ++
  embOpsProcs (b + dsOffOps) ++
  compProcs (b + dsOffEmb) ++
  compAllProcs (b + dsOffC) ++
  reembedProcs (b + dsOffEmb) ++
  reembedAllProcs (b + dsOffOps) (b + dsOffRe) ++
  reembStageProcs (b + dsOffCA) (b + dsOffRA) ++
  delRecordsProcs ++
  delAllProcs (b + dsOffDR) ++
  insRecordsProcs (b + dsOffOps) ++
  uhTailProcs (b + dsOffDA) (b + dsOffIR) ++
  applyUHProcs (b + dsOffBatch) ++
  uhEndProcs (b + dsOffUT) (b + dsOffAU) ++
  fillLevelProcs (b + dsOffPhase) ++
  rebuildBucketsProcs (b + dsOffCB) (b + dsOffFL) ++
  stepEndProcs (b + dsOffUE) (b + dsOffRB) ++
  stepTailProcs (b + dsOffSE) (b + dsOffClrA) ++
  stepFinishProcs (b + dsOffST) (b + dsOffLW) ++
  collectDProcs ++
  stepPosNonEmptyProcs (b + dsOffAux) (b + dsOffSS) (b + dsOffRS) (b + dsOffFin) (b + dsOffCD)

/-- Chunk 5 (offsets `88..107`, length `20`): empty/epilogue/full positive step, batch loop, op 0. -/
def dynSpannerChunk5 (b : ℕ) : List Stmt :=
  stepPosEmptyProcs (b + dsOffFin) ++
  stepPosEpilogueProcs (b + dsOffAux) (b + dsOffPhase) ++
  stepPosProcs (b + dsOffNE) (b + dsOffEm) (b + dsOffEp) ++
  affectedProcs (b + dsOffOps) ++
  stepHeadProcs (b + dsOffAffP) (b + dsOffPref) ++
  walkPtrsProcs ++
  projProcs (b + dsOffEmb) ++
  buildProjProcs (b + dsOffOps) (b + dsOffEdge) (b + dsOffProj) ++
  projStageProcs (b + dsOffWP) (b + dsOffBP) ++
  affStageProcs (b + dsOffAffP) (b + dsOffPS) ++
  wordSumProcs ++
  stepPosFullProcs (b + dsOffHead) (b + dsOffSum) (b + dsOffAS) (b + dsOffPos) ++
  updateLoopProcs (b + dsOffAux) (b + dsOffPhase) (b + dsOffSZ) (b + dsOffFull) (b + dsOffUL) ++
  dsOpProcs (b + dsOffAux) (b + dsOffUL)

/-- Complete relocatable deterministic procedure list for `dynSpannerDS`, anchored at `b`. -/
def dynSpannerDSProcs (impl : SparsifyImpl) (b : ℕ) : List Stmt :=
  dynSpannerChunk1 b ++
  dynSpannerChunk2 impl b ++
  dynSpannerChunk3 b ++
  dynSpannerChunk4 b ++
  dynSpannerChunk5 b ++
  sparsifyGuestProcs impl (b + dsOffGuest)

/-- `DSInitBases` anchored at `b` inside `dynSpannerDSProcs impl b`. -/
def dynSpannerDSInitBases (b : ℕ) : DSInitBases where
  bOps := b + dsOffOps
  bEdge := b + dsOffEdge
  bBatch := b + dsOffBatch
  bPhase := b + dsOffPhase
  bLW := b + dsOffLW
  bSpDyn := b + dsOffSpDyn
  bInit := b + dsOffInit
  bSort := b + dsOffSort
  bSplit := b + dsOffSplit
  bFwd := b + dsOffFwd
  bRevPrim := b + dsOffRevPrim
  bRevCore := b + dsOffRevCore
  bRevDyn := b + dsOffRevDyn
  bEmit := b + dsOffEmit
  bGuest := b + dsOffGuest
  bGT := b + dsOffGT
  bRev := b + dsOffRev

/-- `StepZeroBases` anchored at `b` inside `dynSpannerDSProcs impl b`. -/
def dynSpannerDSStepZeroBases (b : ℕ) : StepZeroBases where
  bAux := b + dsOffAux
  bZAux := b + dsOffZAux
  bSort := b + dsOffSort
  bOps := b + dsOffOps
  bEdge := b + dsOffEdge
  bSplit := b + dsOffSplit
  bBatch := b + dsOffBatch
  bGT := b + dsOffGT
  bEmit := b + dsOffEmit
  bFwd := b + dsOffFwd
  bRevPrim := b + dsOffRevPrim
  bRevCore := b + dsOffRevCore
  bRevDyn := b + dsOffRevDyn
  bGuest := b + dsOffGuest
  bSpDyn := b + dsOffSpDyn
  bRev := b + dsOffRev
  bLW := b + dsOffLW
  bPhase := b + dsOffPhase
  bInit := b + dsOffInit
  bF := b + dsOffF
  bR := b + dsOffR
  bD := b + dsOffD
  bU := b + dsOffU
  bPref := b + dsOffPref
  bCB := b + dsOffCB
  bZ := b + dsOffZ
  bClrA := b + dsOffClrA
  bSZ := b + dsOffSZ

/-- `StepPosNEBases` anchored at `b` inside `dynSpannerDSProcs impl b`. -/
def dynSpannerDSStepPosNEBases (b : ℕ) : StepPosNEBases where
  bAux := b + dsOffAux
  bSort := b + dsOffSort
  bOps := b + dsOffOps
  bEdge := b + dsOffEdge
  bSplit := b + dsOffSplit
  bBatch := b + dsOffBatch
  bGT := b + dsOffGT
  bEmit := b + dsOffEmit
  bFwd := b + dsOffFwd
  bRevPrim := b + dsOffRevPrim
  bRevCore := b + dsOffRevCore
  bRevDyn := b + dsOffRevDyn
  bGuest := b + dsOffGuest
  bSpDyn := b + dsOffSpDyn
  bRev := b + dsOffRev
  bLW := b + dsOffLW
  bSS := b + dsOffSS
  bEmb := b + dsOffEmb
  bC := b + dsOffC
  bCA := b + dsOffCA
  bRe := b + dsOffRe
  bRA := b + dsOffRA
  bRS := b + dsOffRS
  bDR := b + dsOffDR
  bDA := b + dsOffDA
  bIR := b + dsOffIR
  bUT := b + dsOffUT
  bAU := b + dsOffAU
  bUE := b + dsOffUE
  bCB := b + dsOffCB
  bPhase := b + dsOffPhase
  bFL := b + dsOffFL
  bRB := b + dsOffRB
  bSE := b + dsOffSE
  bZ := b + dsOffZ
  bClrA := b + dsOffClrA
  bST := b + dsOffST
  bFin := b + dsOffFin
  bCD := b + dsOffCD
  bNE := b + dsOffNE

/-- `StepPosFullBases` anchored at `b` inside `dynSpannerDSProcs impl b`. -/
def dynSpannerDSStepPosFullBases (b : ℕ) : StepPosFullBases where
  ne := dynSpannerDSStepPosNEBases b
  bAffP := b + dsOffAffP
  bD := b + dsOffD
  bU := b + dsOffU
  bF := b + dsOffF
  bR := b + dsOffR
  bPref := b + dsOffPref
  bHead := b + dsOffHead
  bWP := b + dsOffWP
  bBP := b + dsOffBP
  bProj := b + dsOffProj
  bPS := b + dsOffPS
  bAS := b + dsOffAS
  bSum := b + dsOffSum
  bEm := b + dsOffEm
  bEp := b + dsOffEp
  bPos := b + dsOffPos
  bFull := b + dsOffFull

/-- `UpdateLoopBases` anchored at `b` inside `dynSpannerDSProcs impl b`. -/
def dynSpannerDSUpdateLoopBases (b : ℕ) : UpdateLoopBases where
  sz := dynSpannerDSStepZeroBases b
  pos := dynSpannerDSStepPosFullBases b
  bUL := b + dsOffUL

end

end MinCostFlow.SparseCore.Program
