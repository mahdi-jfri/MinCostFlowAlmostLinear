module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP3
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Post
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Sel
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue10

/-!
# Phase 4 in the top proof of the first step: the definitions (`AssemblyFirstStepHP4Defs`)

The top proof (`asmFirstStep_coreStepAt_of`) asks, as `hP4`, that Phase 4 runs on the arguments
that the driver passes, from the state that Phase 3 leaves (`AsmFsQ₃`), and that a predicate
`Q₄` holds after it. This file names what the proof of `hP4` (`AssemblyFirstStepHP4`) uses.

* `AsmFirstP4Code`: the procedures that Phase 4 calls, at their indices of the program (part of
  the packaging).
* `AsmFsQ₃At`: `AsmFsQ₃` with its witnesses as arguments, so that `Q₄` can name them.
* `AsmFsQ₄`: the predicate after Phase 4. It keeps `AsmFsQ₃At` and adds the post of Phase 4
  (`AsmFirstPhase4Post`) on the spanners of the side record after Phase 2, the tasks that Phase 3
  wrote, the tour after Phase 3 and the old embedding table.
* `AsmFsP4Open`: the premises of Phase 4 on the tasks that the descriptors of Phase 3 do not
  give (proved in `AssemblyFsOpen.lean`): the descriptors
  (`AsmFirstBunStepOut`), the caps of the outputs of the tasks (`P4TaskCaps`) and the edges of
  the new spanners after the tasks.
* `AsmFsP4Room`: the room of Phase 4 below `2 ^ w`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The procedures of Phase 4** in the program `p`, for the sparsifier `impl` and the tour
family `TR`, with the procedure `fVertRoot` that finds the root of a vertex in the tour: the
indices of the procedures and the facts that they hold the bodies that `asmFirstP4Sel_runs` and
`asmFirstPhase4_runs_of_sel` call. -/
structure AsmFirstP4Code (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (impl : SparsifyImpl)
    (p : Program) (fVertRoot : ℕ) where
  fSelP : ℕ
  fFront : ℕ
  fSel : ℕ
  fEval : ℕ
  fSpan : ℕ
  fSeed : ℕ
  fFlags : ℕ
  fSeedB : ℕ
  fSeedL : ℕ
  fAppend : ℕ
  fLoop : ℕ
  fNewLoop : ℕ
  fNew : ℕ
  bSpan : ℕ
  fTask : ℕ
  fAfter : ℕ
  fScanUH : ℕ
  fScanD : ℕ
  fScanR : ℕ
  fDleft : ℕ
  fCopySl : ℕ
  fEdge : ℕ
  fPush : ℕ
  fMark : ℕ
  fScanNew : ℕ
  bRead : ℕ
  bCopy : ℕ
  fLists : ℕ
  fEnds : ℕ
  fDel : ℕ
  fIns : ℕ
  fCopyIns : ℕ
  fEndRoot : ℕ
  fRot : ℕ
  fDirect : ℕ
  fBatch : ℕ
  fEdits : ℕ
  fBuild : ℕ
  fReemb : ℕ
  fCopyStr : ℕ
  bSort : ℕ
  hfFront : p.procs[fFront]? = some (asmFirstP4FrontStmt fSpan fSeed fFlags)
  hfSel : p.procs[fSel]? = some (asmFirstMarkOutSelStmt fEval)
  hfEval : p.procs[fEval]? = some asmFirstEvalTgtEStmt
  hfSpan : p.procs[fSpan]? = some (asmFirstP4SpanStmt fLoop fNewLoop)
  hfSeed : p.procs[fSeed]? = some (asmFirstP4SeedStmt fSeedB fSeedL fAppend)
  hfFlags : p.procs[fFlags]? = some asmFirstPrepFlagsStmt
  hfSeedB : p.procs[fSeedB]? = some (asmFirstSeedBatchStmt fPush)
  hfSeedL : p.procs[fSeedL]? = some (asmFirstSeedLazyStmt fAppend)
  hfAppend : p.procs[fAppend]? = some (asmFirstAppendListStmt fPush)
  hfLoop : p.procs[fLoop]? = some (asmFirstP4LoopStmt fTask)
  hfNewLoop : p.procs[fNewLoop]? = some (asmFirstP4NewLoopStmt fNew)
  hpSpan : p.HasAt bSpan (bucketSpannerProcs impl bSpan)
  hfTask : p.procs[fTask]? = some (asmFirstP4TaskStmt (bSpan + bsIdxOp0 + 1) fAfter)
  hfAfter : p.procs[fAfter]? = some (asmFirstP4AfterStmt fScanUH fScanD fScanR fDleft fCopySl)
  hfUH : p.procs[fScanUH]? = some (asmFirstScanSlotUHStmt fEdge)
  hfD : p.procs[fScanD]? = some (asmFirstScanSlotDStmt fPush fMark)
  hfR : p.procs[fScanR]? = some (asmFirstScanSlotRStmt fPush)
  hfDl : p.procs[fDleft]? = some (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr))
  hfC : p.procs[fCopySl]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr))
  hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark)
  hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt
  hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt
  hfNew : p.procs[fNew]? = some (asmFirstP4NewStmt fScanNew fCopySl)
  hfN : p.procs[fScanNew]? = some (asmFirstScanNewSlotStmt fPush)
  hcopy : p.HasAt bCopy [copyWords]
  hread : p.HasAt bRead spanReadoutProcs
  HE : AsmFirstTourEndRootAt TR w p fEndRoot
  hfSelP : p.procs[fSelP]? = some (asmFirstP4SelStmt fFront fSel)
  hfLists : p.procs[fLists]? = some (asmFirstP4ListsStmt fEnds fDel fIns fCopyIns)
  hfEnds : p.procs[fEnds]? = some (asmFirstQueryInsEndsStmt fEndRoot)
  hfDel : p.procs[fDel]? = some (asmFirstBuildDelStmt bSort)
  hfIns : p.procs[fIns]? = some (asmFirstBuildInsStmt bSort)
  hfCopyIns : p.procs[fCopyIns]? = some asmFirstCopyInsStmt
  hfRot : p.procs[fRot]? = some (asmFirstP4RotStmt fDirect fBatch fEdits fBuild)
  hfDirect : p.procs[fDirect]? = some asmFirstCollectRotDirectStmt
  hfBatch : p.procs[fBatch]? = some (asmFirstCollectRotBatchStmt fVertRoot)
  hfEdits : p.procs[fEdits]? = some (asmFirstCollectRotEditsStmt fVertRoot)
  hfBuild : p.procs[fBuild]? = some (asmFirstBuildRotStmt bSort)
  hfReemb : p.procs[fReemb]? = some (asmFirstP4ReembStmt fCopyStr fBuild)
  hfCopyStr : p.procs[fCopyStr]? = some asmFirstStrideCopyStmt
  hpSort : p.HasAt bSort (sortProcs bSort)

/-- The body of Phase 4 for the procedures `K`. -/
def AsmFirstP4Code.stmt {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ} {impl : SparsifyImpl}
    {p : Program} {fVertRoot : ℕ} (K : AsmFirstP4Code TR w impl p fVertRoot) : Stmt :=
  asmFirstPhase4Stmt K.fSelP K.fLists K.fRot K.fReemb

/-- The list of the new components of the scan on the arguments `A`. -/
def AsmFsArgs.newComps {depth : ℕ} {τ : Type} (A : AsmFsArgs τ depth)
    (cmpH : ℕ) (comps : List (Finset ℕ)) : List (ℕ × ℕ) :=
  (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem cmpH comps A.tr.activeComps) A.U).newComps

/-- **`AsmFsQ₃` with its witnesses as arguments**: the end `hEnd₂` of Phase 2, the side record
`y'`, the tour state `tx1` and the lazy lists `lazyE` of Phase 2, the end `hEnd₃` of Phase 3 and
the witnesses of the post of Phase 3. -/
def AsmFsQ₃At {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl) (P L capExp limbMul w : ℕ)
    (Ψ : BundleTreeState depth → ℕ) (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ) : Prop :=
  AsmFsScanFacts TRc scProgB5 impl P L capExp limbMul w Ψ A st₁ c₁ ∧
  ∃ tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ, HEq tx₀ A.x.xTour ∧
  AsmFirstNewActPostAt TS TRc w depth capExp fVertRoot fInitOne fInitSpan impl p A.ω hRoot
      A.x.restH A.x.tourH (A.h + 9 + 2 * A.x.eCap + A.x.vCap)
      (A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words) st₁.pos A.tr A.ord
      A.x.sTour.marked A.x.xRest tx₀ (A.newComps A.x.xRest.cmpH A.x.xRest.comps)
      st₁.mem hEnd₂ st₂ c₂ y' tx1 lazyE ∧
  AsmFirstPhase3PostAt w depth y'.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5 bBun bTourStep
      fDelTriples fBuildGroups y'.bunH A.x.tourH A.batch A.words A.edits A.editWords A.spPtr
      (A.h + 9 + 2 * A.x.eCap + A.x.vCap + 4 * A.words) hEnd₂ st₂.pos p A.ω
      (fun _ => canonicalSparsify impl) A.tr A.U A.ord A.ed
      (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U).delEdges
      y'.slotOf y'.bunS y'.xBun tx1 st₂.mem hEnd₃ st₃ c₃
      tx_pot' splitPtr outDescPtr mk' Mset Ys touched

/-- **The predicate `Q₄` after Phase 4**: the witnesses of `Q₃` with `AsmFsQ₃At`, and the post of
Phase 4 for the spanners of `y'`, the tasks that Phase 3 wrote at `outDescPtr + 1`, the new slots
`[|slots|, nSlots1)`, the tour state `tx_pot'` and the marks `mk'` of Phase 3, the old embedding
table, and the foot of the old output graph as the cells to avoid. All outcomes are returns. -/
def AsmFsQ₄ {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl) (P L capExp limbMul w : ℕ)
    (Ψ : BundleTreeState depth → ℕ) (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (o₂ : Outcome) (st₂ : State) (c₂ : ℕ) (o₃ : Outcome) (st₃ : State)
    (c₃ : ℕ) (o₄ : Outcome) (st₄ : State) (c₄ : ℕ) : Prop :=
  ∃ hEnd₂, o₂ = .returned hEnd₂ ∧
  ∃ (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ),
  ∃ hEnd₃, o₃ = .returned hEnd₃ ∧
  ∃ (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ),
  AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun bTourStep
      fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
      outDescPtr mk' Mset Ys touched ∧
  AsmFirstPhase4Post (asmBrSP impl w depth y') TRc K.HE.mul K.HE.querySpace hRoot.mul
      hRoot.querySpace y'.spanH hEnd₃ A.x.xRest.eCap5 A.x.xRest.vCap5 A.x.embH
      A.x.xRest.slots.length
      (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
        (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
      A.x.tourH A.h y'.spanS y'.xSpan (p4TasksOf st₃.mem (outDescPtr + 1) touched.length)
      A.x.yEmb.view A.x.yEmb A.U A.ed A.c lazyE mk' tx_pot'
      ((outGraphRep A.x.vCap A.x.eCap).foot A.x.outH A.x.gOut) st₃.mem A.tr A.ord o₄ st₄ c₄

/-- **The premises of Phase 4 on the tasks that the descriptors of Phase 3 do not give**, for the spanner parameters
`P`, the spanners `S6`, the descriptors at `descPtr`, the heap pointer `hp`, the new slots
`[lo, hi)`, the tasks `tasks` and the memory `mem₀` after Phase 3: the descriptors meet
`AsmFirstBunStepOut`, the outputs of the tasks stay below the edge cap (`P4TaskCaps`), and the
spanners of the new slots after the tasks have edges below the edge cap. -/
def AsmFsP4Open (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (eCap descPtr hp lo hi : ℕ) (tasks : List SpanUpdTask) (mem₀ : ℕ → ℕ) : Prop :=
  AsmFirstBunStepOut P cap S6 descPtr hp tasks mem₀ ∧
  (∀ t ∈ tasks, ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d →
    mem₀ t.batchPtr ≠ 0 → P4TaskCaps P eCap d (decodeBatch mem₀ t.batchPtr (d.state P).G).1) ∧
  (∀ s, lo ≤ s → s < hi → ∃ (hs : s < cap) (d : DSHist),
    p4SpanAfter P S6 mem₀ tasks ⟨s, hs⟩ = some d ∧ ∀ e ∈ (d.state P).G.E, e < eCap)

/-- **The room of Phase 4** in words of width `w`: from the heap pointer `hp`, the work space, the
space of the tasks read from the `nTasks` descriptors at `descPtr`, the space of the new slots
`[lo, hi)` and the room of the lists, the rotation and the re-embedding (`asmFirstPhase4Room`,
with `nSp` splits, `nU` updates, `nEd` order edits and the query spaces `qE`, `qR` of the tour). -/
def AsmFsP4Room (w : ℕ) (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem : ℕ → ℕ)
    (hp vCap eCap descPtr nTasks lo hi nSp nU nEd qE qR : ℕ) : Prop :=
  hp + p4WsSize eCap + ((p4TasksOf mem descPtr nTasks).map (p4TaskSpace P S6 mem)).sum +
    rangeCost (p4NewSpace P (p4SpanAfter P S6 mem (p4TasksOf mem descPtr nTasks))) lo hi +
    asmFirstPhase4Room vCap eCap nSp nU nEd qE qR < 2 ^ w

end

end MinCostFlow.SparseCore.Program
