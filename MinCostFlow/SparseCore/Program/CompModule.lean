module

public import MinCostFlow.SparseCore.Program.CompInitProcs
public import MinCostFlow.SparseCore.Program.CompReadoutEdge
public import MinCostFlow.SparseCore.Program.CompExport
public import MinCostFlow.SparseCore.Program.CompSplitListBatch
public import MinCostFlow.SparseCore.Program.CompWindowInst
public import MinCostFlow.SparseCore.Program.ReadSpec
import MinCostFlow.LSF.Program.LSFModuleBase

/-!
# Relocatable Module Assembly for Per-Component Dynamic LSF (`CompModule`)

Assembles all deterministic (`NoRand`) procedures of piece P4 into a single relocatable
procedure block `compLSFProcs W b` (and standalone deterministic program `compLSFProgram W`):

* `compIdxInit b = b` (`init`: `compInitProc`)
* `compIdxOp b 0 = b + 1` (`op 0`: `compBatchWithSplitsProc`, emitting both `Read.LSFChangeAt`
  and `CompSplitListAt`)
* `compIdxOp b 1..5 = b + 2..b + 6` (`op 1..5`: `O(1)` readout procedures `compVertCompProc`,
  `compWindowHandleProc`, `compRootProc`, `compEdgeInfoProc`, `compInfoProc`)
* `compIdxOp b 6 = b + 7` (`op 6`: linear-time single-branch export `compExportBranchProc`)

Proves:
* `compLSFProcs_length` and `compLSFProcs_noRand` / `compLSFProgram_isDeterministic`
* `compLSFProcs_implements`: `(compLSFRepFull W k).Implements w p (compIdxInit b) (compIdxOp b)
  (compLSFDSFullWithSplits W w k G₀)` whenever `p.HasAt b (compLSFProcs W b)`
* `compRootQueryAt`: `Read.RootQueryAt w p (compIdxOp b 3)` at constant cost `150`
* `canonicalCompLSF_implements`: end-to-end instantiation with P3's `canonicalLSFWindowImpl`
  (`h = 4`, `canonicalLSFInit`, `lsfWindowProcs`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Relocatable procedure indices and module layout -/

/-- Entry index of `init` inside `compLSFProcs W b`. -/
def compIdxInit (b : ℕ) : ℕ := b

/-- Entry index of operation `i` (`0..6`) inside `compLSFProcs W b`. -/
def compIdxOp (b i : ℕ) : ℕ := b + 1 + i

/-- Start index of the embedded `lsfModuleProcs` block inside `compLSFProcs W b`. -/
def compBaseLsf (b : ℕ) : ℕ := b + 34

/-- Start index of the embedded P3 window-initializer block `W.procs` inside `compLSFProcs W b`. -/
def compBaseWin (W : LSFWindowImpl) (b : ℕ) : ℕ :=
  compBaseLsf b + (257 + W.Q_AN.procs.length)

/-- Fixed-length (`34`-procedure) core block of P4: the `8` public entry points (`init`,
`op 0..6`) followed by the `26` internal helper procedures. -/
def compCoreProcs (W : LSFWindowImpl) (b : ℕ) : List Stmt :=
  let bLsf := compBaseLsf b
  let bWin := compBaseWin W b
  let bDgInit := lsfBaseDg bLsf + 12 + dgIdxInitFromLists
  let bSort := lsfBaseSort bLsf
  let bBfs := b + 8
  let bCons := b + 9
  let bErase := b + 10
  let bApp := b + 11
  let bZero := b + 12
  let bMark := b + 13
  let bLogAdd := b + 14
  let bPreLog := b + 15
  let bDisp := b + 16
  let bIns := b + 17
  let bDel := b + 18
  let bSplit := b + 19
  let bPackChg := b + 20
  let bRootVal := b + 21
  let bEnds := b + 22
  let bEndRoots := b + 23
  let bUFInitFind := b + 24
  let bUFPairUnion := b + 25
  let bUFClean := b + 26
  let bEmit := b + 27
  let bPackSp := b + 28
  let bCopy := b + 29
  let bTEdges := b + 30
  let bFEdges := b + 31
  let bRoots := b + 32
  let bPairs := b + 33
  [ compInitProc W.h bBfs bDgInit (bWin + W.initOff)
  , compBatchWithSplitsProc bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp
  , compVertCompProc
  , compWindowHandleProc
  , compRootProc
  , compEdgeInfoProc
  , compInfoProc
  , compExportBranchProc bCopy bTEdges bFEdges bRoots bPairs
  , compBfsCompProc
  , ghostConsProc
  , ghostEraseProc
  , ghostAppendProc
  , compZeroRangeProc
  , compMarkTouchProc
  , compLogAddOrigRootProc (lsfBaseBat W.Q_AN bLsf + 0)
      (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)
  , compPreLogProc bLogAdd
  , compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)
  , compStepInsertProc bCons bMark bDisp
  , compStepDeleteProc bErase bMark bDisp
  , compStepSplitProc bApp bMark bDisp
  , compPackChangesProc bZero
  , compRootValProc
  , compEdgeEndsProc
  , compEdgeEndRootsProc
  , compUFInitFindProc
  , compUFPairUnionProc
  , compUFCleanProc
  , compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort)
      bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean
  , compPackSplitsProc bZero
  , compCopyWordsProc
  , compExpTEdgesProc
  , compExpFEdgesProc
  , compExpRootsProc
  , compExpPairsProc ]

/-- Complete relocatable procedure block for P4 placed at base index `b`. -/
noncomputable def compLSFProcs (W : LSFWindowImpl) (b : ℕ) : List Stmt :=
  compCoreProcs W b ++
  lsfModuleProcs W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h ++
  W.procs (compBaseWin W b)

/-- Standalone deterministic Word-RAM program for P4. -/
noncomputable def compLSFProgram (W : LSFWindowImpl) : Program :=
  ⟨compLSFProcs W 0⟩

lemma compCoreProcs_length (W : LSFWindowImpl) (b : ℕ) : (compCoreProcs W b).length = 34 := rfl

/-- Total length of `compLSFProcs W b`. -/
theorem compLSFProcs_length (W : LSFWindowImpl) (b : ℕ) :
    (compLSFProcs W b).length = 291 + W.Q_AN.procs.length + W.procsLen := by
  simp only [compLSFProcs, List.length_append, compCoreProcs_length, lsfModuleProcs_length,
    W.procs_length]
  omega

private lemma compCoreProcs_noRand (W : LSFWindowImpl) (b : ℕ) :
    ∀ s ∈ compCoreProcs W b, s.NoRand := by
  intro s hs
  simp only [compCoreProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact compInitProc_noRand _ _ _ _
  · exact compBatchWithSplitsProc_noRand _ _ _ _ _ _ _ _
  · exact compReadoutProcs_noRand _ (by simp [compReadoutProcs])
  · exact compReadoutProcs_noRand _ (by simp [compReadoutProcs])
  · exact compReadoutProcs_noRand _ (by simp [compReadoutProcs])
  · exact compReadoutProcs_noRand _ (by simp [compReadoutProcs])
  · exact compReadoutProcs_noRand _ (by simp [compReadoutProcs])
  · exact compExportBranchProc_noRand _ _ _ _ _
  · exact compBfsCompProc_noRand
  · exact compHelperProcs_noRand _ (by simp [compHelperProcs])
  · exact compHelperProcs_noRand _ (by simp [compHelperProcs])
  · exact compHelperProcs_noRand _ (by simp [compHelperProcs])
  · exact compHelperProcs_noRand _ (by simp [compHelperProcs])
  · exact compHelperProcs_noRand _ (by simp [compHelperProcs])
  · exact compLogAddOrigRootProc_noRand _ _ _
  · exact compPreLogProc_noRand _
  · exact compDispatchOneProc_noRand _ _ _
  · exact compStepInsertProc_noRand _ _ _
  · exact compStepDeleteProc_noRand _ _ _
  · exact compStepSplitProc_noRand _ _ _
  · exact compPackChangesProc_noRand _
  · exact compRootValProc_noRand
  · exact compEdgeEndsProc_noRand
  · exact compEdgeEndRootsProc_noRand
  · exact compUFInitFindProc_noRand
  · exact compUFPairUnionProc_noRand
  · exact compUFCleanProc_noRand
  · exact compEmitBranchSplitProc_noRand _ _ _ _ _ _ _
  · exact compPackSplitsProc_noRand _
  · exact compCopyWordsProc_noRand
  · exact compExpTEdgesProc_noRand
  · exact compExpFEdgesProc_noRand
  · exact compExpRootsProc_noRand
  · exact compExpPairsProc_noRand

/-- Every procedure in `compLSFProcs W b` is deterministic (`NoRand`). -/
theorem compLSFProcs_noRand (W : LSFWindowImpl) (b : ℕ) :
    ∀ s ∈ compLSFProcs W b, s.NoRand := by
  intro s hs
  simp only [compLSFProcs, List.mem_append] at hs
  rcases hs with (hC | hL) | hW
  · exact compCoreProcs_noRand W b s hC
  · exact lsfModuleProcs_noRand W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h s hL
  · exact W.procs_noRand (compBaseWin W b) s hW

/-- The standalone program `compLSFProgram W` is deterministic. -/
theorem compLSFProgram_isDeterministic (W : LSFWindowImpl) :
    (compLSFProgram W).IsDeterministic :=
  compLSFProcs_noRand W 0

/-! ## 2. `HasAt` extraction helpers -/

private lemma compHasAt_core {W : LSFWindowImpl} {p : Program} {b : ℕ}
    (hp : p.HasAt b (compLSFProcs W b)) :
    p.HasAt b (compCoreProcs W b) := by
  have hp' : p.HasAt b (compCoreProcs W b ++
      (lsfModuleProcs W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h ++ W.procs (compBaseWin W b))) := by
    simpa only [compLSFProcs, List.append_assoc] using hp
  exact MinCostFlow.Num.hasAt_append_left hp'

private lemma compHasAt_lsf {W : LSFWindowImpl} {p : Program} {b : ℕ}
    (hp : p.HasAt b (compLSFProcs W b)) :
    p.HasAt (compBaseLsf b) (lsfModuleProcs W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h) := by
  have hp' : p.HasAt b (compCoreProcs W b ++
      (lsfModuleProcs W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h ++ W.procs (compBaseWin W b))) := by
    simpa only [compLSFProcs, List.append_assoc] using hp
  have h1 := MinCostFlow.Num.hasAt_append_right hp'
  rw [compCoreProcs_length] at h1
  exact MinCostFlow.Num.hasAt_append_left h1

private lemma compHasAt_win {W : LSFWindowImpl} {p : Program} {b : ℕ}
    (hp : p.HasAt b (compLSFProcs W b)) :
    p.HasAt (compBaseWin W b) (W.procs (compBaseWin W b)) := by
  have hp' : p.HasAt b (compCoreProcs W b ++
      (lsfModuleProcs W.Q_AN W.c_AN W.K_AN (compBaseLsf b) W.h ++ W.procs (compBaseWin W b))) := by
    simpa only [compLSFProcs, List.append_assoc] using hp
  have h1 := MinCostFlow.Num.hasAt_append_right hp'
  rw [compCoreProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [lsfModuleProcs_length] at h2
  exact h2

private lemma compCore_get {W : LSFWindowImpl} {p : Program} {b i : ℕ}
    (hC : p.HasAt b (compCoreProcs W b)) (hi : i < 34) :
    p.procs[b + i]? = some ((compCoreProcs W b)[i]'(by rw [compCoreProcs_length]; exact hi)) :=
  hC.get (i := i) (by rw [compCoreProcs_length]; exact hi)

/-! ## 3. Full `DSRep.Implements` theorem (init + `op 0..6`) -/

/-- **Main P4 implementation theorem**: any program `p` containing `compLSFProcs W b`
at base index `b` implements `compLSFDSFullWithSplits W w k G₀` under `compLSFRepFull W k` across
`init` (`compIdxInit b`) and all 7 operations `op 0..6` (`compIdxOp b i`). -/
theorem compLSFProcs_implements (W : LSFWindowImpl) (w k b : ℕ) (G₀ : MGraph)
    {p : Program} (hp : p.HasAt b (compLSFProcs W b)) :
    (compLSFRepFull W k).Implements w p (compIdxInit b) (compIdxOp b)
      (compLSFDSFullWithSplits W w k G₀) := by
  have hCore := compHasAt_core hp
  have hLsf := compHasAt_lsf hp
  have hWin := compHasAt_win hp
  have hSh := (lsfModuleHasAt_of_hasAt hLsf).hShared
  have hSort : p.HasAt (lsfBaseSort (compBaseLsf b)) (sortProcs (lsfBaseSort (compBaseLsf b))) :=
    lsfHasAt_sort hSh
  have hDg : ∀ {vCap eCap} (G : MGraph) (vLs : List ℕ) (eLs : List (ℕ × ℕ × ℕ)),
      MeetsContract w p (lsfBaseDg (compBaseLsf b) + 12 + dgIdxInitFromLists)
        (dgInitFromListsContract w vCap eCap G vLs eLs) := fun G vLs eLs =>
    dgInitFromLists_meetsContract (lsfHasAt_dgBatch hSh) (lsfHasAt_dgEdge hSh) (lsfHasAt_dgOps hSh)
  refine ⟨compLSFRepFull_local W k, ?_, ?_⟩
  · -- `init`
    intro args mem pos ω hwords hpre hz hsp
    have hbody : p.procs[compIdxInit b]? = some (compInitProc W.h (b + 8)
        (lsfBaseDg (compBaseLsf b) + 12 + dgIdxInitFromLists) (compBaseWin W b + W.initOff)) := by
      simpa [compIdxInit, compCoreProcs] using compCore_get hCore (i := 0) (by decide)
    obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', -, -, -⟩ :=
      compLSFDSFullWithSplits_init
        (by simpa [compCoreProcs] using compCore_get hCore (i := 8) (by decide))
        hDg hWin hpre hwords hz hsp
    exact ⟨_, hbody, o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩
  · -- `op i` (`0..6`; `i ≥ 7` vacuously false)
    intro i hndl S x args mem pos ω hwords hhead hrep hpre hfoot hz hsp
    match i with
    | 0 =>
      have hbody : p.procs[compIdxOp b 0]? = some (compBatchWithSplitsProc
          (b + 12) (b + 17) (b + 18) (b + 19) (b + 22) (b + 27) (b + 20) (b + 28)) := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 1) (by decide)
      rcases hpre with ⟨hk, b', batchPtr, heap, totalWords, U, rfl, hw16, hBAt, hBVal, hBCaps,
        hBWords, hBHeap, hBOut⟩
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', -, -, -, -⟩ :=
        compLSFDS_op0_withSplits_for
          (by simpa [compCoreProcs] using compCore_get hCore (i := 12) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 14) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 15) (by decide))
          hLsf
          (by simpa [compCoreProcs] using compCore_get hCore (i := 9) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 10) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 11) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 13) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 16) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 17) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 18) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 19) (by decide))
          hSort
          (by simpa [compCoreProcs] using compCore_get hCore (i := 21) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 22) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 23) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 24) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 25) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 26) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 27) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 20) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 28) (by decide))
          hrep hk hw16 hBAt hBVal hBCaps hBWords hBHeap hBOut hwords hfoot hz hsp
      exact ⟨_, hbody, o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩
    | 1 =>
      have hbody : p.procs[compIdxOp b 1]? = some compVertCompProc := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 2) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 1) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩ :=
        compLSFDS_op1 hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | 2 =>
      have hbody : p.procs[compIdxOp b 2]? = some compWindowHandleProc := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 3) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 2) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩ :=
        compLSFDS_op2 hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | 3 =>
      have hbody : p.procs[compIdxOp b 3]? = some compRootProc := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 4) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 3) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', -⟩ :=
        compLSFDS_op3 hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | 4 =>
      have hbody : p.procs[compIdxOp b 4]? = some compEdgeInfoProc := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 5) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 4) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩ :=
        compLSFDS_op4 hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | 5 =>
      have hbody : p.procs[compIdxOp b 5]? = some compInfoProc := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 6) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 5) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩ :=
        compLSFDS_op5 hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | 6 =>
      have hbody : p.procs[compIdxOp b 6]? = some (compExportBranchProc
          (b + 29) (b + 30) (b + 31) (b + 32) (b + 33)) := by
        simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 7) (by decide)
      refine ⟨_, hbody, compLSFDSFullWithSplits_lift_readonly (i := 6) (by decide) hrep ?_⟩
      obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', -, -⟩ :=
        compLSFDS_op6 (G₀ := G₀)
          (by simpa [compCoreProcs] using compCore_get hCore (i := 29) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 30) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 31) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 32) (by decide))
          (by simpa [compCoreProcs] using compCore_get hCore (i := 33) (by decide))
          hrep (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hpre)
          hwords hhead hfoot hz (by simpa [compLSFDSFullWithSplits, compLSFDSFull] using hsp)
      exact ⟨o, st', c, hrun, S', x', hrep',
        by simpa [compLSFDSFull] using hpost', hpost'.1,
        by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩
    | n + 7 =>
      exfalso
      simp [compLSFDSFullWithSplits, compLSFDSFull, compLSFDS] at hpre

/-- Standalone-program corollary of `compLSFProcs_implements`. -/
theorem compLSFProgram_implements (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) :
    (compLSFRepFull W k).Implements w (compLSFProgram W) (compIdxInit 0) (compIdxOp 0)
      (compLSFDSFullWithSplits W w k G₀) :=
  compLSFProcs_implements W w k 0 G₀ (fun i hi => by simp [compLSFProgram, hi])

/-! ## 4. P10 `Read.RootQueryAt` export (operation `3`) -/

/-- P4's `Read.RootQueryAt` instance (`ReadSpec.lean`) exported at `compIdxOp b 3` (`compRootProc`),
operating directly on `compLSFRepFull W k` at constant cost `150`. -/
noncomputable def compRootQueryAt (W : LSFWindowImpl) (w k b : ℕ) {p : Program}
    (hp : p.HasAt b (compLSFProcs W b)) :
    Read.RootQueryAt w p (compIdxOp b 3) where
  σ := CompLSFFamily k
  R := compLSFRepFull W k
  root S j u := if hj : j < k then (S ⟨j, hj⟩).RF.root u else 0
  ok S j u := ∃ hj : j < k, 16 ≤ 2 ^ w ∧ u ∈ (S ⟨j, hj⟩).G.V
  cost := 150
  R_local := compLSFRepFull_local W k
  runs := by
    intro hndl j u h S x mem pos ω hhndl hj_w hu_w hh_w ⟨hj, hw16, huV⟩ hrep hfoot hz hsp
    have hCore := compHasAt_core hp
    have hbody : p.procs[compIdxOp b 3]? = some compRootProc := by
      simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 4) (by decide)
    have hk : 1 ≤ k := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
    have huV0 : u ∈ (S ⟨0, hk⟩).G.V := by
      obtain ⟨ℓ₀, hBr⟩ := hrep.2.2.2.2.2.2.2.2.2.2.2.1
      rw [← (hBr ⟨j, hj⟩).2.2.1]; exact huV
    have hpre : (compLSFDS W w k (S ⟨0, hk⟩).G₀).pre 3 S [hndl, j, u, h] mem :=
      ⟨hk, hndl, j, u, h, rfl, hw16, hj, huV0⟩
    have hargs : ∀ a ∈ [hndl, j, u, h], a < 2 ^ w := by
      intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost'⟩ :=
      compLSFDSFullWithSplits_lift_readonly (i := 3) (by decide) hrep (by
        obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', -⟩ :=
          compLSFDS_op3 (G₀ := (S ⟨0, hk⟩).G₀) hrep hpre hargs rfl hfoot hz hsp
        exact ⟨o, st', c, hrun, S', x', hrep', by simpa [compLSFDSFull] using hpost', hpost'.1,
          by simpa [compLSFDSFull] using hresp', by simpa [compLSFDSFull] using hcost'⟩)
    simp only [compLSFDSFullWithSplits, show (3 : ℕ) ≠ 0 by decide, ↓reduceIte,
      compLSFDSFull, show (3 : ℕ) ≠ 6 by decide, compLSFDS] at hpost' hresp' hcost'
    obtain ⟨rfl, hj', hroot⟩ := hpost'
    rcases hresp' with ⟨hlo, hhi, hz', hfr', hft'⟩
    exact ⟨compRootProc, hbody, o, st', c, x', hrun,
      by simpa [hj, heapArg] using hroot, hrep', hlo, hhi, hz', hfr', hft', hcost'⟩

/-! ## 5. End-to-end canonical P3 instantiation (`canonicalLSFWindowImpl`) -/

/-- **End-to-end P3+P4 theorem**: instantiating `compLSFProcs` with P3's canonical window
initializer `canonicalLSFWindowImpl` (`h = 4`, `canonicalLSFInit`, `lsfWindowProcs`) yields a
deterministic Word-RAM implementation of `compLSFDSFullWithSplits` across `init` and `op 0..6`. -/
theorem canonicalCompLSF_implements (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp w k b : ℕ) (G₀ : MGraph)
    {p : Program}
    (hp : p.HasAt b (compLSFProcs (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) b)) :
    (compLSFRepFull (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) k).Implements
      w p (compIdxInit b) (compIdxOp b)
      (compLSFDSFullWithSplits (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) w k G₀) :=
  compLSFProcs_implements (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) w k b G₀ hp

/-! ## 6. Capacity-preserving direct entry lemmas for wrapper assembly -/

/-- Direct `init` entry theorem preserving `(vCap, eCap, L_w)` metadata of `x'`. -/
theorem compLSFProcs_init_runs {W : LSFWindowImpl} {w k b : ℕ} {G₀ : MGraph} {p : Program}
    (hp : p.HasAt b (compLSFProcs W b)) {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpre : (compLSFDSFullWithSplits W w k G₀).initPre args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w) (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDSFullWithSplits W w k G₀).initSpace args mem < 2 ^ w) :
    ∃ body, p.procs[compIdxInit b]? = some body ∧ ∃ o st' c S' x',
      Runs w p ω body (startState args mem pos) o st' c ∧
      CompLSFRepAt W k (heapArg args) S' x' st'.mem ∧
      (compLSFDSFullWithSplits W w k G₀).initPost args mem S' st'.mem ∧
      (compLSFRepFull W k).Respects (fun _ => False) (heapArg args)
        ((compLSFDSFullWithSplits W w k G₀).initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
      c + compPhiFull k (heapArg args) x' st'.mem ≤
        (compLSFDSFullWithSplits W w k G₀).initCost args mem ∧
      x'.vCap = args.getD 6 0 ∧ x'.eCap = args.getD 7 0 ∧ x'.L_w = args.getD 5 0 := by
  have hCore := compHasAt_core hp
  have hSh := (lsfModuleHasAt_of_hasAt (compHasAt_lsf hp)).hShared
  have hDg : ∀ {vCap eCap} (G : MGraph) (vLs : List ℕ) (eLs : List (ℕ × ℕ × ℕ)),
      MeetsContract w p (lsfBaseDg (compBaseLsf b) + 12 + dgIdxInitFromLists)
        (dgInitFromListsContract w vCap eCap G vLs eLs) := fun G vLs eLs =>
    dgInitFromLists_meetsContract (lsfHasAt_dgBatch hSh) (lsfHasAt_dgEdge hSh) (lsfHasAt_dgOps hSh)
  have hbody : p.procs[compIdxInit b]? = some (compInitProc W.h (b + 8)
      (lsfBaseDg (compBaseLsf b) + 12 + dgIdxInitFromLists) (compBaseWin W b + W.initOff)) := by
    simpa [compIdxInit, compCoreProcs] using compCore_get hCore (i := 0) (by decide)
  obtain ⟨o, st', c, hrun, S', x', h1, h2, h3, h4, h5, h6, h7⟩ :=
    compLSFDSFullWithSplits_init
      (by simpa [compCoreProcs] using compCore_get hCore (i := 8) (by decide))
      hDg (compHasAt_win hp) hpre hargs hz hsp
  exact ⟨_, hbody, o, st', c, S', x', hrun, h1, h2, h3, h4, h5, h6, h7⟩

/-- Direct `op 0` (batch with splits) entry theorem preserving `(vCap, eCap, L_w)` metadata and
pinning the postcondition explicitly to the caller's batch `U`. -/
theorem compLSFProcs_batch_runs {W : LSFWindowImpl} {w k b hndl batchPtr heap totalWords : ℕ}
    {G₀ : MGraph} {p : Program}
    (hp : p.HasAt b (compLSFProcs W b)) {S : CompLSFFamily k} {x : CompLSFMeta k}
    {U : List Update} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hrep : CompLSFRepAt W k hndl S x mem)
    (hk : 1 ≤ k) (hw16 : 16 ≤ 2 ^ w)
    (hBAt : BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords)
    (hBVal : (S ⟨0, hk⟩).G.BatchIsValid U)
    (hBCaps : BatchWithinCaps (mem (hndl + compOffVCap)) (mem (hndl + compOffECap)) U)
    (hBWords : ∀ i < totalWords, mem (batchPtr + i) < 2 ^ w)
    (hBHeap : batchPtr + totalWords ≤ heap)
    (hBOut : ∀ i < totalWords, batchPtr + i < hndl ∨ mem (hndl + compOffEndAddr) ≤ batchPtr + i)
    (hargs : ∀ a ∈ [hndl, batchPtr, heap], a < 2 ^ w)
    (hfoot : ∀ a, compFoot hndl x a → a < heap) (hz : ZeroFrom mem heap)
    (hsp : heap + (compLSFDSFullWithSplits W w k G₀).space 0 S [hndl, batchPtr, heap] mem < 2 ^ w) :
    ∃ body, p.procs[compIdxOp b 0]? = some body ∧ ∃ o st' c S' x',
      Runs w p ω body (startState [hndl, batchPtr, heap] mem pos) o st' c ∧
      CompLSFRepAt W k hndl S' x' st'.mem ∧
      (compLSFDSFullWithSplits W w k G₀).post 0 S [hndl, batchPtr, heap] mem S' st'.mem ∧
      (compLSFRepFull W k).Respects (compFoot hndl x) heap
        ((compLSFDSFullWithSplits W w k G₀).space 0 S [hndl, batchPtr, heap] mem) mem o.value hndl x' st'.mem ∧
      c + compPhiFull k hndl x' st'.mem ≤
        (compLSFDSFullWithSplits W w k G₀).cost 0 S [hndl, batchPtr, heap] mem + compPhiFull k hndl x mem ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
      CompBatchPostFullAt w k S [hndl, batchPtr, heap] mem o.value U S' st'.mem := by
  have hCore := compHasAt_core hp
  have hLsf := compHasAt_lsf hp
  have hSort := lsfHasAt_sort (lsfModuleHasAt_of_hasAt hLsf).hShared
  have hbody : p.procs[compIdxOp b 0]? = some (compBatchWithSplitsProc
      (b + 12) (b + 17) (b + 18) (b + 19) (b + 22) (b + 27) (b + 20) (b + 28)) := by
    simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 1) (by decide)
  obtain ⟨o, st', c, hrun, S', x', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    compLSFDS_op0_withSplits_for
      (by simpa [compCoreProcs] using compCore_get hCore (i := 12) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 14) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 15) (by decide))
      hLsf
      (by simpa [compCoreProcs] using compCore_get hCore (i := 9) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 10) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 11) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 13) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 16) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 17) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 18) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 19) (by decide))
      hSort
      (by simpa [compCoreProcs] using compCore_get hCore (i := 21) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 22) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 23) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 24) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 25) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 26) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 27) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 20) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 28) (by decide))
      hrep hk hw16 hBAt hBVal hBCaps hBWords hBHeap hBOut hargs hfoot hz hsp
  exact ⟨_, hbody, o, st', c, S', x', hrun, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Direct `op 3` (root query) entry theorem preserving `x` identically and `compPhiFull`. -/
theorem compLSFProcs_root_runs {W : LSFWindowImpl} {w k b hndl : ℕ} {G₀ : MGraph} {p : Program}
    (hp : p.HasAt b (compLSFProcs W b)) {S : CompLSFFamily k} {x : CompLSFMeta k}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hrep : CompLSFRepAt W k hndl S x mem)
    (hpre : (compLSFDS W w k G₀).pre 3 S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w) (hhead : args.head? = some hndl)
    (hfoot : ∀ a, compFoot hndl x a → a < heapArg args) (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 3 S args mem < 2 ^ w) :
    ∃ body, p.procs[compIdxOp b 3]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧
      CompLSFRepAt W k hndl S x st'.mem ∧
      (compLSFDS W w k G₀).post 3 S args mem S st'.mem ∧
      (compLSFRepFull W k).Respects (compFoot hndl x) (heapArg args)
        ((compLSFDS W w k G₀).space 3 S args mem) mem o.value hndl x st'.mem ∧
      c + compPhiFull k hndl x st'.mem ≤
        (compLSFDS W w k G₀).cost 3 S args mem + compPhiFull k hndl x mem := by
  have hbody : p.procs[compIdxOp b 3]? = some compRootProc := by
    simpa [compIdxOp, compCoreProcs] using compCore_get (compHasAt_core hp) (i := 4) (by decide)
  obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', rfl⟩ :=
    compLSFDS_op3 hrep hpre hargs hhead hfoot hz hsp
  have hS : S' = S := hpost'.1
  subst hS
  have hsp_eq := compSplitPhi_eq_of_same_state hrep hrep'
  exact ⟨_, hbody, o, st', c, hrun, hrep', hpost', hresp', by dsimp [compPhiFull]; omega⟩

/-- Direct `op 6` (single-branch export) entry theorem preserving `x` identically and `compPhiFull`. -/
theorem compLSFProcs_export_runs {W : LSFWindowImpl} {w k b hndl : ℕ} {G₀ : MGraph} {p : Program}
    (hp : p.HasAt b (compLSFProcs W b)) {S : CompLSFFamily k} {x : CompLSFMeta k}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hrep : CompLSFRepAt W k hndl S x mem)
    (hpre : CompExportPre w k S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w) (hhead : args.head? = some hndl)
    (hfoot : ∀ a, compFoot hndl x a → a < heapArg args) (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + compExportSpace args mem < 2 ^ w) :
    ∃ body, p.procs[compIdxOp b 6]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧
      CompLSFRepAt W k hndl S x st'.mem ∧
      CompExportPost W w k S args mem S st'.mem ∧
      (compLSFRepFull W k).Respects (compFoot hndl x) (heapArg args)
        (compExportSpace args mem) mem o.value hndl x st'.mem ∧
      c + compPhiFull k hndl x st'.mem ≤
        compExportCost k S args mem + compPhiFull k hndl x mem ∧
      o.value = st'.mem (heapArg args + 5) + mem (hndl + compOffECap) * mem (hndl + compOffLW) := by
  have hCore := compHasAt_core hp
  have hbody : p.procs[compIdxOp b 6]? = some (compExportBranchProc
      (b + 29) (b + 30) (b + 31) (b + 32) (b + 33)) := by
    simpa [compIdxOp, compCoreProcs] using compCore_get hCore (i := 7) (by decide)
  obtain ⟨o, st', c, hrun, S', x', hrep', hpost', hresp', hcost', rfl, hout_eq⟩ :=
    compLSFDS_op6 (G₀ := G₀)
      (by simpa [compCoreProcs] using compCore_get hCore (i := 29) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 30) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 31) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 32) (by decide))
      (by simpa [compCoreProcs] using compCore_get hCore (i := 33) (by decide))
      hrep (by simpa [compLSFDSFull] using hpre) hargs hhead hfoot hz
      (by simpa [compLSFDSFull] using hsp)
  simp only [compLSFDSFull, ↓reduceIte] at hpost' hresp' hcost'
  have hS : S' = S := hpost'.1
  subst hS
  have hsp_eq := compSplitPhi_eq_of_same_state hrep hrep'
  exact ⟨_, hbody, o, st', c, hrun, hrep', hpost', hresp', by dsimp [compPhiFull]; omega, hout_eq⟩

end

end MinCostFlow.SparseCore.Program
