module

public import MinCostFlow.SparseCore.Program.AssemblyTopProcs
public import MinCostFlow.SparseCore.Program.AssemblyBranchValue
public import MinCostFlow.SparseCore.Program.TourProcs
public import MinCostFlow.SparseCore.Program.BundleModule
public import MinCostFlow.SparseCore.Program.BunRestartProg

import MinCostFlow.SparseCore.Program.SpanBucketInit
import MinCostFlow.SparseCore.Program.RestartModelState
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import MinCostFlow.LSF.Program.BatchTBlockOpsBase

/-!
# The single combined sparse-core Word-RAM program (`AssemblyCode`)

Assembles all concrete sparse-core procedure modules together with the
three parameter procedure lists (P4 component-LSF family `ScCompCode`, first phase of the
branch step `ScSubCode`, and first phase of the branch init `ScSubCode`) into one deterministic
`WordRAM.Program` (`scProg`) at fixed offsets (`ScCodeLayout`):

| Block | Base | Procedures | Source |
| --- | --- | --- | --- |
| P4 component-LSF family | `0` | `cf.procs` | parameter `ScCompCode` |
| P10 readout library | `bReadLib` | `readLibProcs bReadLib` | `ReadLib`, `DynGraph*`, `copyWords`, `lsfSetWstrOneProc`, `ReadLoops` |
| P10 readout branch ops | `bRead` | `readBranchProcs readLib cf.fRoot bRead` | `ReadMain` |
| P6 bucket spanners | `bSpan` | `bucketSpannerProcs impl bSpan` | `SpanBucketDefs` |
| P2 core rotation tour | `bTour` | `tourProcs bTour` (`94` procs) | `TourProcs` |
| P7 output step / reset / helper | `bOut` | `outProcs bOut nm sm fm lm` (`20` procs) | `OutProcs` |
| P5 bundle manager | `bBun` | `bundleProcs bBun …` (`15` procs) | `BundleModule` |
| P5 bundle restart | `fBun` | `[bunRestartStmt …]` (`1` proc) | `BunRestartProg` |
| First phase of branch step | `bFirstS` | `firstStep.procs envStep` | parameter `ScSubCode` |
| First phase of branch init | `bFirstI` | `firstInit.procs envInit` | parameter `ScSubCode` |
| Branch glue (12 procs) | `bGlue` | `asmBrGlueProcs I` | `AssemblyBranch*`, `RestartIface`, `EmbRefreshDefs` |
| Top-layer dispatch (29 procs) | `bTop` | `asmTopProcs bTop …` | `AssemblyTopProcs` |

Proves determinism (`scProg_isDeterministic`), placement (`HasAt`) for every sub-module,
`HasAsmBrProcs` (depth-free), `HasAsmTopProcs`, `HasTourProcs`, `OutProcsAt`, `HasReadProcs`,
and `bunRestartStmt` placement.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Parameter code records for the sub-modules given as parameters -/

/-- Deterministic procedure list and entry indices for the component-LSF family (P4), placed at
offset `0` of the combined sparse-core program. -/
structure ScCompCode where
  procs : List Stmt
  hnoRand : ∀ s ∈ procs, s.NoRand
  fInit : ℕ
  fBatch : ℕ
  fExport : ℕ
  fRoot : ℕ

/-- Fixed offsets of all already-placed sparse-core sub-modules passed to the first-phase step and
init sub-modules (`ScSubCode`). -/
structure ScFirstEnv where
  bSelf : ℕ
  fCFRoot : ℕ
  readLib : ReadLib
  bRead : ℕ
  bSpan : ℕ
  bTour : ℕ
  bOut : ℕ
  bBun : ℕ
  fBunRestart : ℕ

/-- Relocatable deterministic procedure block parameterized by `ScFirstEnv`, with its main entry
at `env.bSelf + offMain`. Used for the first phase of a branch step (`fCoreS`) and the first phase
of a branch init (`fCoreI`). -/
structure ScSubCode where
  procs : ScFirstEnv → List Stmt
  hnoRand : ∀ env, ∀ s ∈ procs env, s.NoRand
  offMain : ℕ

/-! ## Concrete library and glue blocks -/

/-- `ReadLib` offsets placed contiguously starting at base `b`. -/
def readLibAt (b : ℕ) : ReadLib :=
  let bOps := b
  let bEdge := bOps + dgOpsProcs.length
  let bSplit := bEdge + (dgEdgeProcs bOps).length
  let bBatch := bSplit + (dgSplitProcs bOps bSplit).length
  let bCollect := bBatch + (dgBatchProcs bOps bEdge bSplit bBatch).length
  let bCopy := bCollect + 1
  let bSetOne := bCopy + 1
  let bLoops := bSetOne + 1
  ⟨bOps, bEdge, bSplit, bBatch, bCollect, bCopy, bSetOne, bLoops⟩

/-- Contiguous procedure list realizing `readLibAt b` at base `b`. -/
def readLibProcs (b : ℕ) : List Stmt :=
  let L := readLibAt b
  dgOpsProcs ++ dgEdgeProcs L.ops ++ dgSplitProcs L.ops L.split ++
    dgBatchProcs L.ops L.edge L.split L.batch ++
    [collectStmt, copyWords, LSF.Program.lsfSetWstrOneProc] ++
    readLoopProcs L.edge

/-- The 12 branch-glue procedures (`init`, `step`, `restart`, P8 `f8`, embedding refresh `fEmb`,
and the four readouts with their bodies) for index record `I`. -/
def asmBrGlueProcs (I : AsmBrProcIdx) : List Stmt :=
  [ asmBrInitStmt I.fCoreI (I.bRead + readBranchIdx13 4),
    asmBrStepStmt I.fCoreS (outIdxStep I.bOut) (I.bRead + readBranchIdx13 2),
    asmBrRestartStmt I.f8 (outIdxReset I.bOut) I.fEmb,
    restartBranchStmt I.fBun (I.bSpan + bsIdxOp0 + 0) (I.bRead + readBranchIdx13 3),
    embRefreshStmt I.bCopy (I.bSpan + bsOffRead + spanReadIdxPiWalkPtr),
    asmBrReadStmt I.fRL ASM_BR_READ,
    readLSFStmt,
    asmBrReadStmt I.fRS ASM_BR_READ,
    readSStmt,
    asmBrReadStmt I.fRE ASM_BR_EMB,
    embReadStmt,
    asmBrReadOrdStmt I.fList ]

theorem asmBrGlueProcs_length (I : AsmBrProcIdx) : (asmBrGlueProcs I).length = 12 := rfl

/-! ## Determinism (`Stmt.NoRand`) of concrete blocks -/

private theorem noRand_append {xs ys : List Stmt}
    (hx : ∀ s ∈ xs, s.NoRand) (hy : ∀ s ∈ ys, s.NoRand) :
    ∀ s ∈ xs ++ ys, s.NoRand := fun s hs =>
  (List.mem_append.mp hs).elim (hx s) (hy s)

private theorem copyWords_noRand : copyWords.NoRand := by
  simp [copyWords, forRange, forUp, Stmt.NoRand]

theorem embReadStmt_noRand : embReadStmt.NoRand := by
  simp [embReadStmt, Stmt.NoRand]

theorem readLibProcs_noRand (b : ℕ) : ∀ s ∈ readLibProcs b, s.NoRand := by
  unfold readLibProcs
  refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
    dgOpsProcs_noRand (dgEdgeProcs_noRand _)) (dgSplitProcs_noRand _ _))
    (dgBatchProcs_noRand _ _ _ _)) ?_) (readLoopProcs_noRand _)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact collectStmt_noRand
  · exact copyWords_noRand
  · exact LSF.Program.lsfSetWstrOneProc_noRand

private theorem outMainProcs_noRand (b nm sm fm lm : ℕ) :
    ∀ s ∈ outMainProcs b nm sm fm lm, s.NoRand := by
  intro s hs
  simp only [outMainProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · simp [outSmallSideBody, ssHead, ssInit, ssWalkBody, ssCopy, ssTail, ssQuery, forRange, forUp,
      Stmt.NoRand]
  · simp [outResetBody, rsSetup, rsDelBody, rsInsBody, rsMark, Stmt.NoRand]
  · simp [outStepBody, osSetup, osDelPhase, osDelIter, osSplitPhase, osSplitIter, osInsPhase,
      osInsIter, osInsEnd, osRotPhase, osRotIter, osFinal, osFilters, osBHdr, osChoose, osEHdr,
      osQuery, osBumpB, osBumpE, rsMark, Stmt.NoRand]
  · simp [outFilterBody, ofIter, Stmt.NoRand]
  · simp [outWalkBody, owIter, Stmt.NoRand]

theorem outProcs_noRand (b nm sm fm lm : ℕ) : ∀ s ∈ outProcs b nm sm fm lm, s.NoRand := by
  unfold outProcs
  exact noRand_append (noRand_append (noRand_append (noRand_append
    (outMainProcs_noRand b nm sm fm lm) (dgEdgeProcs_noRand _)) dgOpsProcs_noRand)
    (dgSplitProcs_noRand _ _)) (dgBatchProcs_noRand _ _ _ _)

theorem asmBrGlueProcs_noRand (I : AsmBrProcIdx) : ∀ s ∈ asmBrGlueProcs I, s.NoRand := by
  intro s hs
  simp only [asmBrGlueProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact asmBrInitStmt_noRand _ _
  · exact asmBrStepStmt_noRand _ _ _
  · exact asmBrRestartStmt_noRand _ _ _
  · exact restartBranchStmt_noRand _ _ _
  · exact embRefreshStmt_noRand _ _
  · exact asmBrReadStmt_noRand _ _
  · exact readLSFStmt_noRand
  · exact asmBrReadStmt_noRand _ _
  · exact readSStmt_noRand
  · exact asmBrReadStmt_noRand _ _
  · exact embReadStmt_noRand
  · exact asmBrReadOrdStmt_noRand _

/-! ## Fixed offset layout and combined sparse-core program -/

/-- Complete fixed offset layout of the combined sparse-core program `scProg`. -/
structure ScCodeLayout where
  bReadLib : ℕ
  readLib : ReadLib
  bRead : ℕ
  bSpan : ℕ
  bTour : ℕ
  bOut : ℕ
  bBun : ℕ
  fBun : ℕ
  bFirstS : ℕ
  envStep : ScFirstEnv
  bFirstI : ℕ
  envInit : ScFirstEnv
  bGlue : ℕ
  bp : AsmBranchProcs
  I : AsmBrProcIdx
  bTop : ℕ

/-- Computes the fixed offset layout of `scProg impl cf firstStep firstInit`. -/
def scLayout (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    ScCodeLayout :=
  let bReadLib := cf.procs.length
  let readLib := readLibAt bReadLib
  let bRead := bReadLib + (readLibProcs bReadLib).length
  let bSpan := bRead + (readBranchProcs readLib cf.fRoot bRead).length
  let bTour := bSpan + (bucketSpannerProcs impl bSpan).length
  let bOut := bTour + (tourProcs bTour).length
  let bBun := bOut + (outProcs bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11)
    (tourOp bTour 9)).length
  let fBun := bBun + (bundleProcs bBun (tourOp bTour 4) (tourOp bTour 12) (tourOp bTour 10)).length
  let bFirstS := fBun + 1
  let envStep : ScFirstEnv :=
    { bSelf := bFirstS, fCFRoot := cf.fRoot, readLib := readLib, bRead := bRead,
      bSpan := bSpan, bTour := bTour, bOut := bOut, bBun := bBun, fBunRestart := fBun }
  let bFirstI := bFirstS + (firstStep.procs envStep).length
  let envInit : ScFirstEnv :=
    { bSelf := bFirstI, fCFRoot := cf.fRoot, readLib := readLib, bRead := bRead,
      bSpan := bSpan, bTour := bTour, bOut := bOut, bBun := bBun, fBunRestart := fBun }
  let bGlue := bFirstI + (firstInit.procs envInit).length
  let bp : AsmBranchProcs :=
    { fInit := bGlue + 0, fStep := bGlue + 1, fRestart := bGlue + 2,
      fReadLSF := bGlue + 5, fReadS := bGlue + 7, fReadEmb := bGlue + 9, fReadOrd := bGlue + 11 }
  let I : AsmBrProcIdx :=
    { fCoreI := bFirstI + firstInit.offMain,
      fCoreS := bFirstS + firstStep.offMain,
      bOut := bOut,
      nm := tourOp bTour 8, sm := tourOp bTour 7, fm := tourOp bTour 11, lm := tourOp bTour 9,
      f8 := bGlue + 3, fEmb := bGlue + 4,
      bSpan := bSpan, bCopy := readLib.copy, bRead := bRead,
      fBun := fBun,
      fRL := bGlue + 6, fRS := bGlue + 8, fRE := bGlue + 10,
      fList := tourOp bTour 9 }
  let bTop := bGlue + 12
  ⟨bReadLib, readLib, bRead, bSpan, bTour, bOut, bBun, fBun, bFirstS, envStep, bFirstI, envInit,
    bGlue, bp, I, bTop⟩

/-- **The single combined sparse-core Word-RAM program** containing P4 (`cf`), P10 (`readLibProcs`
and `readBranchProcs`), P6 (`bucketSpannerProcs`), P2 (`tourProcs`), P7 (`outProcs`), P5
(`bundleProcs` and `bunRestartStmt`), the two first-phase blocks (`firstStep` and `firstInit`), the
12 branch glue procedures (`asmBrGlueProcs`), and the 29 top-layer dispatch procedures
(`asmTopProcs`). -/
def scProg (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) : Program :=
  let L := scLayout impl cf firstStep firstInit
  ⟨ cf.procs ++
    readLibProcs L.bReadLib ++
    readBranchProcs L.readLib cf.fRoot L.bRead ++
    bucketSpannerProcs impl L.bSpan ++
    tourProcs L.bTour ++
    outProcs L.bOut (tourOp L.bTour 8) (tourOp L.bTour 7) (tourOp L.bTour 11) (tourOp L.bTour 9) ++
    bundleProcs L.bBun (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10) ++
    [bunRestartStmt (L.bOut + 4) (tourOp L.bTour 10) (L.bBun + bundleOffSort)
      (L.bBun + bundleIdxInitSlots) (L.bBun + bundleIdxExportGraph)] ++
    firstStep.procs L.envStep ++
    firstInit.procs L.envInit ++
    asmBrGlueProcs L.I ++
    asmTopProcs L.bTop cf.fInit cf.fBatch cf.fExport L.bp ⟩

/-! ## Determinism and block placement (`HasAt`) proofs -/

/-- `scProg` is deterministic (`Program.IsDeterministic`). -/
theorem scProg_isDeterministic (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    (scProg impl cf firstStep firstInit).IsDeterministic := by
  unfold Program.IsDeterministic scProg
  refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
    (noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      cf.hnoRand
      (readLibProcs_noRand _))
      (readBranchProcs_noRand _ _ _))
      (bucketSpannerProcs_noRand _ _))
      (tourProcs_noRand _))
      (outProcs_noRand _ _ _ _ _))
      (bundleProcs_noRand _ _ _ _))
      (by intro s hs; simp at hs; subst hs; exact bunRestartStmt_noRand _ _ _ _ _))
      (firstStep.hnoRand _))
      (firstInit.hnoRand _))
      (asmBrGlueProcs_noRand _))
    (asmTopProcs_noRand _ _ _ _ _)

private theorem hasAt_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := fun i hi => by
  have h1 := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at h1

private theorem hasAt_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := fun i hi => by
  have h1 := h (xs.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right xs.length i)] at h1
  simpa [Nat.add_assoc] using h1

private theorem hasAt_self (p : Program) : p.HasAt 0 p.procs := fun i hi => by
  simp [List.getElem?_eq_getElem hi]

/-- Unpacks `HasAt` for all 12 contiguous blocks of `scProg impl cf firstStep firstInit`. -/
theorem scProg_blocks (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    let p := scProg impl cf firstStep firstInit
    p.HasAt 0 cf.procs ∧
    p.HasAt L.bReadLib (readLibProcs L.bReadLib) ∧
    p.HasAt L.bRead (readBranchProcs L.readLib cf.fRoot L.bRead) ∧
    p.HasAt L.bSpan (bucketSpannerProcs impl L.bSpan) ∧
    p.HasAt L.bTour (tourProcs L.bTour) ∧
    p.HasAt L.bOut (outProcs L.bOut (tourOp L.bTour 8) (tourOp L.bTour 7) (tourOp L.bTour 11)
      (tourOp L.bTour 9)) ∧
    p.HasAt L.bBun (bundleProcs L.bBun (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10)) ∧
    p.HasAt L.fBun [bunRestartStmt (L.bOut + 4) (tourOp L.bTour 10) (L.bBun + bundleOffSort)
      (L.bBun + bundleIdxInitSlots) (L.bBun + bundleIdxExportGraph)] ∧
    p.HasAt L.bFirstS (firstStep.procs L.envStep) ∧
    p.HasAt L.bFirstI (firstInit.procs L.envInit) ∧
    p.HasAt L.bGlue (asmBrGlueProcs L.I) ∧
    p.HasAt L.bTop (asmTopProcs L.bTop cf.fInit cf.fBatch cf.fExport L.bp) := by
  intro L p
  have h12 : p.HasAt 0 p.procs := hasAt_self p
  change p.HasAt 0 (_ ++ _) at h12
  have hTop := hasAt_right h12; have h11 := hasAt_left h12
  have hGlue := hasAt_right h11; have h10 := hasAt_left h11
  have hFirstI := hasAt_right h10; have h9 := hasAt_left h10
  have hFirstS := hasAt_right h9; have h8 := hasAt_left h9
  have hFBun := hasAt_right h8; have h7 := hasAt_left h8
  have hBun := hasAt_right h7; have h6 := hasAt_left h7
  have hOut := hasAt_right h6; have h5 := hasAt_left h6
  have hTour := hasAt_right h5; have h4 := hasAt_left h5
  have hSpan := hasAt_right h4; have h3 := hasAt_left h4
  have hRead := hasAt_right h3; have h2 := hasAt_left h3
  have hRLib := hasAt_right h2; have hCF := hasAt_left h2
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    asmBrGlueProcs_length] at hRLib hRead hSpan hTour hOut hBun hFBun hFirstS hFirstI hGlue hTop
  exact ⟨hCF, hRLib, hRead, hSpan, hTour, hOut, hBun, hFBun, hFirstS, hFirstI, hGlue, hTop⟩

/-- Unpacks `ReadLib.Has` from `p.HasAt b (readLibProcs b)`. -/
theorem readLib_has_of_hasAt {p : Program} {b : ℕ} (h : p.HasAt b (readLibProcs b)) :
    (readLibAt b).Has p := by
  unfold readLibProcs at h
  have hLoops := hasAt_right h; have h5 := hasAt_left h
  have hTri := hasAt_right h5; have h4 := hasAt_left h5
  have hBatch := hasAt_right h4; have h3 := hasAt_left h4
  have hSplit := hasAt_right h3; have h2 := hasAt_left h3
  have hEdge := hasAt_right h2; have hOps := hasAt_left h2
  simp only [List.length_append, List.length_cons, List.length_nil] at hEdge hSplit hBatch hTri hLoops
  have hCol : p.procs[(readLibAt b).collect]? = some collectStmt := by
    simpa [readLibAt, Nat.add_assoc] using hTri 0 (by decide)
  have hCopy : p.HasAt (readLibAt b).copy [copyWords] := fun i hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [readLibAt, Nat.add_assoc] using hTri 1 (by decide)
  have hSetOne : p.procs[(readLibAt b).setOne]? = some LSF.Program.lsfSetWstrOneProc := by
    simpa [readLibAt, Nat.add_assoc] using hTri 2 (by decide)
  exact ⟨hOps, hEdge, hSplit, hBatch, hCol, hCopy, hSetOne, by simpa [readLibAt, Nat.add_assoc] using hLoops⟩

theorem scProg_hasComp (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (scProg impl cf firstStep firstInit).HasAt 0 cf.procs :=
  (scProg_blocks impl cf firstStep firstInit).1

theorem scProg_hasReadLib (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (scLayout impl cf firstStep firstInit).readLib.Has (scProg impl cf firstStep firstInit) :=
  readLib_has_of_hasAt (scProg_blocks impl cf firstStep firstInit).2.1

theorem scProg_hasRead (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    HasReadProcs (scProg impl cf firstStep firstInit)
      (scLayout impl cf firstStep firstInit).bRead cf.fRoot :=
  ⟨_, scProg_hasReadLib impl cf firstStep firstInit,
    (scProg_blocks impl cf firstStep firstInit).2.2.1⟩

theorem scProg_hasCopy (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (scProg impl cf firstStep firstInit).HasAt
      (scLayout impl cf firstStep firstInit).readLib.copy [copyWords] :=
  (scProg_hasReadLib impl cf firstStep firstInit).2.2.2.2.2.1

theorem scProg_hasSpan (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (scProg impl cf firstStep firstInit).HasAt (scLayout impl cf firstStep firstInit).bSpan
      (bucketSpannerProcs impl (scLayout impl cf firstStep firstInit).bSpan) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.1

theorem scProg_hasTour (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    HasTourProcs (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).bTour := by
  have h := (scProg_blocks impl cf firstStep firstInit).2.2.2.2.1
  intro i hi
  rw [List.getElem?_eq_getElem hi]
  exact h i hi

theorem scProg_hasOut (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    OutProcsAt (scProg impl cf firstStep firstInit) L.bOut
      (tourOp L.bTour 8) (tourOp L.bTour 7) (tourOp L.bTour 11) (tourOp L.bTour 9) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.1

theorem scProg_hasBundle (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    (scProg impl cf firstStep firstInit).HasAt L.bBun
      (bundleProcs L.bBun (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10)) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.1

theorem scProg_bunRestartAt (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    (scProg impl cf firstStep firstInit).procs[L.fBun]? =
      some (bunRestartStmt (L.bOut + 4) (tourOp L.bTour 10) (L.bBun + bundleOffSort)
        (L.bBun + bundleIdxInitSlots) (L.bBun + bundleIdxExportGraph)) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.2.1.head

theorem scProg_hasFirstStep (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    (scProg impl cf firstStep firstInit).HasAt L.bFirstS (firstStep.procs L.envStep) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.2.2.1

theorem scProg_hasFirstInit (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    (scProg impl cf firstStep firstInit).HasAt L.bFirstI (firstInit.procs L.envInit) :=
  (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.2.2.2.1

/-- `scProg` satisfies depth-free `HasAsmBrProcs` at `L.bp`, `cf.fRoot`, and `L.I`. -/
theorem scProg_hasAsmBrProcs (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    HasAsmBrProcs (scProg impl cf firstStep firstInit) L.bp impl cf.fRoot L.I := by
  intro L
  have hGlue := (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.2.2.2.2.1
  have hAt : ∀ i (hi : i < 12),
      (scProg impl cf firstStep firstInit).procs[L.bGlue + i]? =
        some ((asmBrGlueProcs L.I)[i]'(by rw [asmBrGlueProcs_length]; exact hi)) :=
    fun i hi => hGlue i (by rw [asmBrGlueProcs_length]; exact hi)
  exact
    { init := hAt 0 (by decide)
      step := hAt 1 (by decide)
      restart := hAt 2 (by decide)
      span := scProg_hasSpan impl cf firstStep firstInit
      out := scProg_hasOut impl cf firstStep firstInit
      p8 := hAt 3 (by decide)
      emb := hAt 4 (by decide)
      copy := scProg_hasCopy impl cf firstStep firstInit
      read := scProg_hasRead impl cf firstStep firstInit
      readLSF := hAt 5 (by decide)
      readLSFBody := hAt 6 (by decide)
      readS := hAt 7 (by decide)
      readSBody := hAt 8 (by decide)
      readEmb := hAt 9 (by decide)
      readEmbBody := hAt 10 (by decide)
      readOrd := hAt 11 (by decide) }

/-- `scProg` satisfies `HasAsmTopProcs` at `L.bTop`, `cf.fInit`, `cf.fBatch`, `cf.fExport`, and
`L.bp`. -/
theorem scProg_hasAsmTopProcs (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    let L := scLayout impl cf firstStep firstInit
    HasAsmTopProcs (scProg impl cf firstStep firstInit) L.bTop cf.fInit cf.fBatch cf.fExport L.bp := by
  intro L i hi
  rw [List.getElem?_eq_getElem hi]
  exact (scProg_blocks impl cf firstStep firstInit).2.2.2.2.2.2.2.2.2.2.2 i hi

end MinCostFlow.SparseCore.Program
