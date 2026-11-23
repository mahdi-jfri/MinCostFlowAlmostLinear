module

public import MinCostFlow.SparseCore.Program.OrdStoreImplements
public import MinCostFlow.SparseCore.Program.TourInit
public import MinCostFlow.SparseCore.Program.TourOpsCut
public import MinCostFlow.SparseCore.Program.TourOpsFirstMarked
public import MinCostFlow.SparseCore.Program.TourOpsEdits
import Mathlib.Tactic

/-!
# Tour Procedure Table (`tourProcs`)

Assembles all 94 deterministic WordRAM procedures of the core rotation tour data structure
(`ordStoreProcs b` at `b + 0 .. b + 18`, followed by the 75 tour splay, edit, cut/link, init,
and query procedures at `b + 19 .. b + 93`), proves `tourProcs_noRand`, and provides constructors
unpacking `HasTourProcs p b` into `HasOrdStoreProcs`, `TourListExactProcs`, and `TourEditProcs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Num MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- The 75 tour procedures appended directly after `ordStoreProcs b` (at indices `b + 19 .. b + 93`). -/
def tourOwnProcs (b : ℕ) : List Stmt :=
  [ copyWords,                                                            -- 19
    tourRevBody,                                                          -- 20
    tourActBody,                                                          -- 21
    tourPullBody,                                                         -- 22
    tourIsIdBody,                                                         -- 23
    tourSetIdBody,                                                        -- 24
    tourOpenSumTestBody,                                                  -- 25
    tourOpenValTestBody,                                                  -- 26
    tourMarkSumTestBody,                                                  -- 27
    tourMarkValTestBody,                                                  -- 28
    revNodeBody (b + 20),                                                 -- 29
    applyTagBody (b + 21),                                                -- 30
    pushDownRevBody (b + 29),                                             -- 31
    pushDownTagBody (b + 23) (b + 24) (b + 19) (b + 30),                  -- 32
    pushDownBody (b + 31) (b + 32),                                       -- 33
    pullBody (b + 22),                                                    -- 34
    rotateBody (b + 34),                                                  -- 35
    splayStepBody (b + 35),                                               -- 36
    splayLoopBody (b + 37) (b + 36),                                      -- 37
    pushPathBody (b + 38) (b + 33),                                       -- 38
    splayBody (b + 38) (b + 37),                                          -- 39
    leftmostWalkBody (b + 40) (b + 33),                                   -- 40
    descendBody (b + 41) (b + 33) (b + 25) (b + 26),                      -- 41
    descendBody (b + 42) (b + 33) (b + 27) (b + 28),                      -- 42
    tourDetachLeftBody (b + 34),                                          -- 43
    tourDetachRightBody (b + 34),                                         -- 44
    tourAttachLeftBody (b + 34),                                          -- 45
    tourSetValBody (b + 34),                                              -- 46
    tourInitNodeBody,                                                     -- 47
    tourJoinBody (b + 40) (b + 39) (b + 45),                              -- 48
    tourRotateFrontBody (b + 39) (b + 43) (b + 48),                       -- 49
    tourDeleteNodeBody (b + 39) (b + 43) (b + 44) (b + 48),               -- 50
    tourInsertBeforeBody (b + 39) (b + 43) (b + 45),                      -- 51
    tourFindFirstBody (b + 41) (b + 25) (b + 39),                         -- 52
    tourFindFirstBody (b + 42) (b + 27) (b + 39),                         -- 53
    tourNextReadyBody (b + 39) (b + 43) (b + 44) (b + 48) (b + 52) (b + 25) (b + 26), -- 54
    tourNextReadyBody (b + 39) (b + 43) (b + 44) (b + 48) (b + 53) (b + 27) (b + 28), -- 55
    tourListReadyBody (b + 52) (b + 44) (b + 48),                         -- 56
    tourListReadyBody (b + 53) (b + 44) (b + 48),                         -- 57
    tourSetValNodeBody (b + 39) (b + 46),                                 -- 58
    tourRootTagOfBody (b + 39),                                           -- 59
    tourWalk0Body,                                                        -- 60
    tourDescMark0Body,                                                    -- 61
    tourJoinBody (b + 60) (b + 37) (b + 45),                              -- 62
    tourFindFirstBody (b + 61) (b + 27) (b + 37),                         -- 63
    tourListReadyBody (b + 63) (b + 44) (b + 62),                         -- 64
    tourDropOneBody (b + 50) (b + 58) (b + 49) (b + 18),                  -- 65
    tourEditDropBody (b + 65),                                            -- 66
    tourSplayRankBody (b + 39),                                           -- 67
    tourMoveCollectBody,                                                  -- 68
    tourMoveRankSortNextBody (b + 67) (b + 5) (b + 18),                   -- 69
    tourMoveSplitLoopBody (b + 39) (b + 43) (b + 48),                     -- 70
    tourWalkFrontBody (b + 40) (b + 39),                                  -- 71
    tourEditMoveBody (b + 39) (b + 58) (b + 49) (b + 68) (b + 69) (b + 70) (b + 71), -- 72
    tourEditInsertBody (b + 47) (b + 51) (b + 58) (b + 49),               -- 73
    tourEditRotateBody (b + 58) (b + 49),                                 -- 74
    tourDedupSelBody,                                                     -- 75
    tourCutSplitBody (b + 39) (b + 43) (b + 44) (b + 48) (b + 49),        -- 76
    tourLinkSpliceBody (b + 39) (b + 43) (b + 44) (b + 48),               -- 77
    tourInitStage1Body (b + 15) (b + 47) (b + 48),                        -- 78
    tourOpApplyEditsBody (b + 66) (b + 72) (b + 73) (b + 74) (b + 75) (b + 16), -- 79 (Op 0)
    tourOpCutBody (b + 76) (b + 59) (b + 58) (b + 49),                    -- 80 (Op 1)
    tourOpLinkBody (b + 77) (b + 59) (b + 58) (b + 49),                   -- 81 (Op 2)
    tourOpChangeRootBody (b + 58) (b + 49),                               -- 82 (Op 3)
    tourOpListBody (b + 39) (b + 56) 13,                                  -- 83 (Op 4)
    tourOpAdjacentBody (b + 54),                                          -- 84 (Op 5)
    tourOpNextOpenBody (b + 54),                                          -- 85 (Op 6)
    tourOpSetMarkBody (b + 58),                                           -- 86 (Op 7)
    tourOpNextMarkedBody (b + 55),                                        -- 87 (Op 8)
    tourOpListBody (b + 37) (b + 64) 14,                                  -- 88 (Op 9)
    tourOpRootOfExactBody (b + 37),                                       -- 89 (Op 10)
    tourOpFirstMarkedBody (b + 39) (b + 53),                              -- 90 (Op 11)
    tourOpLenBody (b + 37),                                               -- 91 (Op 12)
    tourOpVertOwnerBody,                                                  -- 92 (Op 13)
    tourInitBody (b + 78) (b + 89) (b + 81) (b + 82) ]                    -- 93 (Init)

/-- The complete list of 94 deterministic procedures of the core rotation tour data structure,
relocated to start at procedure index `b`. -/
def tourProcs (b : ℕ) : List Stmt :=
  ordStoreProcs b ++ tourOwnProcs b

theorem tourProcs_length (b : ℕ) : (tourProcs b).length = 94 := rfl

/-- Program `p` contains all 94 tour procedures starting at index `b`. -/
def HasTourProcs (p : Program) (b : ℕ) : Prop :=
  ∀ i < (tourProcs b).length, p.procs[b + i]? = (tourProcs b)[i]?

/-- Procedure index of initialization `[vCap, eCap, ordPtr, fePtr, rsPtr, heap]` in `tourProcs b`. -/
def tourInit (b : ℕ) : ℕ := b + 93

/-- Procedure index of operation `i` (`0 .. 13`) in `tourProcs b`. -/
def tourOp (b i : ℕ) : ℕ := b + 79 + i

/-- Determinism of `copyWords`. -/
private theorem tourCopyWords_noRand : copyWords.NoRand := by
  simp [copyWords, forRange, forUp, Stmt.NoRand]

/-- Every procedure in `tourProcs b` is deterministic (`Stmt.NoRand`). -/
theorem tourProcs_noRand (b : ℕ) : ∀ s ∈ tourProcs b, s.NoRand := by
  intro s hs
  rw [tourProcs, List.mem_append] at hs
  rcases hs with hord | hown
  · exact ordStoreProcs_noRand b s hord
  · simp only [tourOwnProcs, List.mem_cons, List.not_mem_nil, or_false] at hown
    have hpay := tourPayload_bodies_noRand
    have hsp := tourSplayProg_bodies_noRand (b + 34)
    have hso := tourSplayOps_bodies_noRand (b + 40) (b + 39) (b + 43) (b + 44) (b + 45) (b + 48)
    have hso0 := tourSplayOps_bodies_noRand (b + 60) (b + 37) (b + 43) (b + 44) (b + 45) (b + 62)
    have hsqO := tourSplayQuery_bodies_noRand (b + 41) (b + 25) (b + 26) (b + 39) (b + 43) (b + 44) (b + 48) (b + 52) (b + 46)
    have hsqM := tourSplayQuery_bodies_noRand (b + 42) (b + 27) (b + 28) (b + 39) (b + 43) (b + 44) (b + 48) (b + 53) (b + 46)
    have hsq0 := tourSplayQuery_bodies_noRand (b + 61) (b + 27) (b + 28) (b + 37) (b + 43) (b + 44) (b + 62) (b + 63) (b + 46)
    have hlo := tourOpsLenOwner_noRand (b + 37)
    have hpt := tourOpsPointQuery_bodies_noRand (b + 54) (b + 55) (b + 59)
    have hcl := tourSplayCutLink_bodies_noRand (b + 39) (b + 43) (b + 44) (b + 48) (b + 49)
    have hms := tourMoveSplay_bodies_noRand (b + 40) (b + 39) (b + 43) (b + 48)
    have hmp := tourMovePrep_bodies_noRand (b + 67) (b + 5) (b + 18)
    have hdr := tourEditDrop_bodies_noRand (b + 50) (b + 58) (b + 49) (b + 18) (b + 65)
    rcases hown with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact tourCopyWords_noRand
    · exact hpay.1
    · exact hpay.2.1
    · exact hpay.2.2.1
    · exact hpay.2.2.2.1
    · exact hpay.2.2.2.2.1
    · exact hpay.2.2.2.2.2.1
    · exact hpay.2.2.2.2.2.2.1
    · exact hpay.2.2.2.2.2.2.2.1
    · exact hpay.2.2.2.2.2.2.2.2
    · exact revNodeBody_noRand _
    · exact applyTagBody_noRand _
    · exact pushDownRevBody_noRand _
    · exact pushDownTagBody_noRand _ _ _ _
    · exact pushDownBody_noRand _ _
    · exact pullBody_noRand _
    · exact rotateBody_noRand _
    · exact splayStepBody_noRand _
    · exact splayLoopBody_noRand _ _
    · exact pushPathBody_noRand _ _
    · exact splayBody_noRand _ _
    · exact leftmostWalkBody_noRand _ _
    · exact descendBody_noRand _ _ _ _
    · exact descendBody_noRand _ _ _ _
    · exact hsp.1
    · exact hsp.2.1
    · exact hsp.2.2.1
    · exact hsp.2.2.2.1
    · exact hsp.2.2.2.2
    · exact hso.1
    · exact hso.2.1
    · exact hso.2.2.1
    · exact hso.2.2.2
    · exact hsqO.1
    · exact hsqM.1
    · exact hsqO.2.1
    · exact hsqM.2.1
    · exact hsqO.2.2.1
    · exact hsqM.2.2.1
    · exact hsqO.2.2.2.1
    · exact hsqO.2.2.2.2
    · exact tourListZero_bodies_noRand.1
    · exact tourListZero_bodies_noRand.2
    · exact hso0.1
    · exact hsq0.1
    · exact hsq0.2.2.1
    · exact hdr.1
    · exact hdr.2
    · exact hms.1
    · exact hmp.1
    · exact hmp.2
    · exact hms.2.2
    · exact hms.2.1
    · exact tourEditMoveBody_noRand _ _ _ _ _ _ _
    · exact tourEditInsertBody_noRand _ _ _ _
    · exact tourEditRotateBody_noRand _ _
    · exact tourEditsPrep_noRand.1
    · exact hcl.1
    · exact hcl.2
    · exact tourInitStage1Body_noRand _ _ _
    · exact tourOpApplyEditsBody_noRand _ _ _ _ _ _
    · exact tourOpCutBody_noRand _ _ _ _
    · exact tourOpLinkBody_noRand _ _ _ _
    · exact tourOpChangeRootBody_noRand _ _
    · exact tourOpListBody_noRand _ _ _
    · exact hpt.2.1
    · exact hpt.1
    · exact tourOpSetMarkBody_noRand _
    · exact hpt.2.2.1
    · exact tourOpListBody_noRand _ _ _
    · exact hlo.2.1
    · exact tourOpFirstMarkedBody_noRand _ _
    · exact hlo.1
    · exact hlo.2.2
    · exact tourInitBody_noRand _ _ _ _

/-! ## Unpacking `HasTourProcs` into procedure bundles -/

theorem HasTourProcs.toOrdStore {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    HasOrdStoreProcs p b := by
  intro i hi
  have hlt : i < (tourProcs b).length := by
    simp only [tourProcs, ordStoreProcs, List.length_append, List.length_cons, List.length_nil] at hi ⊢
    omega
  have h := hp i hlt
  rw [tourProcs, List.getElem?_append_left hi] at h
  exact h

theorem HasTourProcs.get {p : Program} {b : ℕ} (hp : HasTourProcs p b) (i : ℕ) (hi : i < 94) :
    p.procs[b + i]? = (tourProcs b)[i]? :=
  hp i hi

theorem tourCopy_ok {w : ℕ} {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    MeetsContract w p (b + 19) (copyWordsContract w) :=
  copyWords_meetsContract fun i hi => by
    obtain rfl : i = 0 := by simpa using hi
    simpa [Nat.add_zero, tourProcs, ordStoreProcs, tourOwnProcs] using hp.get 19 (by decide)

def HasTourProcs.toSplayCore {w : ℕ} {p : Program} {b : ℕ}
    (hp : HasTourProcs p b) (hw : 16 ≤ 2 ^ w) : TourSplayCoreProcs w p :=
  let steps := tourPayloadSteps hw
    (hp.get 20 (by decide)) (hp.get 21 (by decide)) (hp.get 22 (by decide))
    (hp.get 23 (by decide)) (hp.get 24 (by decide))
  let lazy : LazyProcs w p tourPayload tourLayout (tourOk w) steps :=
    { copy := b + 19
      revNode := b + 29
      applyTag := b + 30
      pushDownRev := b + 31
      pushDownTag := b + 32
      pushDown := b + 33
      copy_ok := tourCopy_ok hp
      revNode_body := hp.get 29 (by decide)
      applyTag_body := hp.get 30 (by decide)
      pushDownRev_body := hp.get 31 (by decide)
      pushDownTag_body := hp.get 32 (by decide)
      pushDown_body := hp.get 33 (by decide) }
  let splay : SplayProcs lazy :=
    { pull := b + 34
      rotate := b + 35
      step := b + 36
      loop := b + 37
      pushPath := b + 38
      splay := b + 39
      pull_body := hp.get 34 (by decide)
      rotate_body := hp.get 35 (by decide)
      step_body := hp.get 36 (by decide)
      loop_body := hp.get 37 (by decide)
      pushPath_body := hp.get 38 (by decide)
      splay_body := hp.get 39 (by decide) }
  { steps := steps
    steps_cost := rfl
    steps_space := rfl
    lazy := lazy
    splay := splay
    openTests := tourOpenReadyTests hw (hp.get 25 (by decide)) (hp.get 26 (by decide))
    openTests_cost := rfl
    markTests := tourMarkReadyTests hw (hp.get 27 (by decide)) (hp.get 28 (by decide))
    markTests_cost := rfl
    walkProc := b + 40
    walk_body := hp.get 40 (by decide)
    openDescProc := b + 41
    openDesc_body := hp.get 41 (by decide)
    markDescProc := b + 42
    markDesc_body := hp.get 42 (by decide) }

def HasTourProcs.toSplayOps {w : ℕ} {p : Program} {b : ℕ}
    (hp : HasTourProcs p b) (hw : 16 ≤ 2 ^ w) : TourSplayOpsProcs w p :=
  { toTourSplayCoreProcs := hp.toSplayCore hw
    detachLeft := b + 43
    detachLeft_body := hp.get 43 (by decide)
    detachRight := b + 44
    detachRight_body := hp.get 44 (by decide)
    attachLeft := b + 45
    attachLeft_body := hp.get 45 (by decide)
    setVal := b + 46
    setVal_body := hp.get 46 (by decide)
    initNode := b + 47
    initNode_body := hp.get 47 (by decide)
    join := b + 48
    join_body := hp.get 48 (by decide)
    rotateFront := b + 49
    rotateFront_body := hp.get 49 (by decide)
    deleteNode := b + 50
    deleteNode_body := hp.get 50 (by decide)
    insertBefore := b + 51
    insertBefore_body := hp.get 51 (by decide) }

def HasTourProcs.toSplayQuery {w : ℕ} {p : Program} {b : ℕ}
    (hp : HasTourProcs p b) (hw : 16 ≤ 2 ^ w) : TourSplayQueryProcs w p :=
  { toTourSplayOpsProcs := hp.toSplayOps hw
    findFirstOpen := b + 52
    findFirstOpen_body := hp.get 52 (by decide)
    findFirstMark := b + 53
    findFirstMark_body := hp.get 53 (by decide)
    nextOpen := b + 54
    nextOpen_body := hp.get 54 (by decide)
    nextMark := b + 55
    nextMark_body := hp.get 55 (by decide)
    listOpen := b + 56
    listOpen_body := hp.get 56 (by decide)
    listMark := b + 57
    listMark_body := hp.get 57 (by decide)
    setValNode := b + 58
    setValNode_body := hp.get 58 (by decide)
    rootTagOf := b + 59
    rootTagOf_body := hp.get 59 (by decide) }

def HasTourProcs.toListExact {w : ℕ} {p : Program} {b : ℕ}
    (hp : HasTourProcs p b) (hw : 16 ≤ 2 ^ w) : TourListExactProcs w p :=
  { toTourSplayQueryProcs := hp.toSplayQuery hw
    walk0 := b + 60
    walk0_body := hp.get 60 (by decide)
    descMark0 := b + 61
    descMark0_body := hp.get 61 (by decide)
    join0 := b + 62
    join0_body := hp.get 62 (by decide)
    findFirstMark0 := b + 63
    findFirstMark0_body := hp.get 63 (by decide)
    listMark0 := b + 64
    listMark0_body := hp.get 64 (by decide) }

def HasTourProcs.toEditProcs {w : ℕ} {p : Program} {b : ℕ}
    (hp : HasTourProcs p b) (hw : 16 ≤ 2 ^ w) :
    TourEditProcs w p (ordStoreOp b 0) (ordStoreOp b 2) :=
  { toTourSplayQueryProcs := hp.toSplayQuery hw
    dropOneProc := b + 65
    dropOne_body := hp.get 65 (by decide)
    dropProc := b + 66
    drop_body := hp.get 66 (by decide)
    rankProc := b + 67
    rank_body := hp.get 67 (by decide)
    siftProc := b + 4
    sift_body := hp.get 4 (by decide)
    sortProc := b + 5
    sort_body := hp.get 5 (by decide)
    collectProc := b + 68
    collect_body := hp.get 68 (by decide)
    rankSortProc := b + 69
    rankSort_body := hp.get 69 (by decide)
    splitLoopProc := b + 70
    splitLoop_body := hp.get 70 (by decide)
    walkFrontProc := b + 71
    walkFront_body := hp.get 71 (by decide)
    moveProc := b + 72
    move_body := hp.get 72 (by decide)
    insProc := b + 73
    ins_body := hp.get 73 (by decide)
    rotProc := b + 74
    rot_body := hp.get 74 (by decide)
    dedupProc := b + 75
    dedup_body := hp.get 75 (by decide) }

/-! ## Direct body accessors for `tourInit` and `tourOp` -/

theorem HasTourProcs.cutSplit_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[b + 76]? = some (tourCutSplitBody (b + 39) (b + 43) (b + 44) (b + 48) (b + 49)) :=
  hp.get 76 (by decide)

theorem HasTourProcs.linkSplice_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[b + 77]? = some (tourLinkSpliceBody (b + 39) (b + 43) (b + 44) (b + 48)) :=
  hp.get 77 (by decide)

theorem HasTourProcs.stage1_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[b + 78]? = some (tourInitStage1Body (b + 15) (b + 47) (b + 48)) :=
  hp.get 78 (by decide)

theorem HasTourProcs.op0_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 0]? = some (tourOpApplyEditsBody (b + 66) (b + 72) (b + 73) (b + 74) (b + 75) (b + 16)) :=
  hp.get 79 (by decide)

theorem HasTourProcs.op1_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 1]? = some (tourOpCutBody (b + 76) (b + 59) (b + 58) (b + 49)) :=
  hp.get 80 (by decide)

theorem HasTourProcs.op2_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 2]? = some (tourOpLinkBody (b + 77) (b + 59) (b + 58) (b + 49)) :=
  hp.get 81 (by decide)

theorem HasTourProcs.op3_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 3]? = some (tourOpChangeRootBody (b + 58) (b + 49)) :=
  hp.get 82 (by decide)

theorem HasTourProcs.op4_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 4]? = some (tourOpListBody (b + 39) (b + 56) 13) :=
  hp.get 83 (by decide)

theorem HasTourProcs.op5_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 5]? = some (tourOpAdjacentBody (b + 54)) :=
  hp.get 84 (by decide)

theorem HasTourProcs.op6_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 6]? = some (tourOpNextOpenBody (b + 54)) :=
  hp.get 85 (by decide)

theorem HasTourProcs.op7_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 7]? = some (tourOpSetMarkBody (b + 58)) :=
  hp.get 86 (by decide)

theorem HasTourProcs.op8_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 8]? = some (tourOpNextMarkedBody (b + 55)) :=
  hp.get 87 (by decide)

theorem HasTourProcs.op9_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 9]? = some (tourOpListBody (b + 37) (b + 64) 14) :=
  hp.get 88 (by decide)

theorem HasTourProcs.op10_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 10]? = some (tourOpRootOfExactBody (b + 37)) :=
  hp.get 89 (by decide)

theorem HasTourProcs.op11_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 11]? = some (tourOpFirstMarkedBody (b + 39) (b + 53)) :=
  hp.get 90 (by decide)

theorem HasTourProcs.op12_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 12]? = some (tourOpLenBody (b + 37)) :=
  hp.get 91 (by decide)

theorem HasTourProcs.op13_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourOp b 13]? = some tourOpVertOwnerBody :=
  hp.get 92 (by decide)

theorem HasTourProcs.init_body {p : Program} {b : ℕ} (hp : HasTourProcs p b) :
    p.procs[tourInit b]? = some (tourInitBody (b + 78) (b + 89) (b + 81) (b + 82)) :=
  hp.get 93 (by decide)

end MinCostFlow.SparseCore.Program
