module

public import MinCostFlow.SparseCore.Program.BundleStepScanProcs
public import MinCostFlow.SparseCore.Program.BundleDllProcs
public import MinCostFlow.DynSpanner.Program.SortOps

/-!
# Phase 3 slot-emission procedures and pure packed-key / batch lemmas (`BundleStepEmitProcs`)

Defines the deterministic Word-RAM procedures for Phase 3 of `bundleStep`:
* `bundleStepEmitPopDelsStmt bMergeSort`: pops and clears `slotDelHead[s]`/`slotDelNext`, sorts
  the deleted edges into `delArr`.
* `bundleStepEmitPopCandsStmt bMergeSort`: pops and clears `slotCandHead[s]`/`candNext`/`inCand`,
  sorts the candidate splitting bundles into `candArr`.
* `bundleStepEmitDelRecsStmt`: computes the batch upper bound `1 + 2 * delCnt + 6 * candEndsSum`,
  reserves `batchPtr`, and emits `[1, e]` records for all sorted deletions.
* `bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner`: splits one candidate
  bundle `b` by final core vertex (packing `v * (2 * eCap) + key`, sorting via `bMergeSort`,
  keeping group 0 in `b`, and moving groups `1..d-1` into fresh bundles `nB, nB+1, ...` while
  emitting tag-`2` split records).
* `bundleStepEmitSlotStmt bDllPush bDllErase bMergeSort bTourOwner`: combines all steps for a
  single touched slot `s`, clearing `slotTouched[s]` and writing `[s, batchPtr, totalWords]` to
  `outDescPtr`.

Also proves the pure packed-key sorting correspondence with `byRootVRuns` and the automatic
`SmallBatchAt` bound for tag-`1` / tag-`2` batches.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Sub-statements and `bundleStepEmitSlotStmt` -/

/-- Step 3A: pops and clears `slotDelHead[s]`/`slotDelNext` into `r16 = delArr` (`r17 = delCnt`),
advances `r4`, and sorts `delArr` via `bMergeSort`. -/
def bundleStepEmitPopDelsStmt (bMergeSort : ℕ) : Stmt :=
  .assign 16 (.reg 4) ;;
  .assign 17 (.const 0) ;;
  .assign 18 (.load (.bin .add (.reg 13) (.reg 2))) ;;
  .store (.bin .add (.reg 13) (.reg 2)) (.const 0) ;;
  .loop (.reg 18)
    (.assign 19 (.bin .sub (.reg 18) (.const 1)) ;;
     .assign 18 (.load (.bin .add (.reg 14) (.reg 19))) ;;
     .store (.bin .add (.reg 14) (.reg 19)) (.const 0) ;;
     .store (.bin .add (.reg 16) (.reg 17)) (.reg 19) ;;
     .assign 17 (.bin .add (.reg 17) (.const 1))) ;;
  .assign 18 (.bin .add (.reg 16) (.reg 17)) ;;
  .assign 4 (.bin .add (.reg 18) (.reg 17)) ;;
  .call 19 bMergeSort [.reg 16, .reg 17, .reg 18]

/-- Step 3B: pops and clears `slotCandHead[s]`/`candNext`/`inCand` into `r18 = candArr`
(`r19 = candCnt`), advances `r4`, and sorts `candArr` via `bMergeSort`. -/
def bundleStepEmitPopCandsStmt (bMergeSort : ℕ) : Stmt :=
  .assign 18 (.reg 4) ;;
  .assign 19 (.const 0) ;;
  .assign 20 (.load (.bin .add (.reg 15) (.reg 2))) ;;
  .store (.bin .add (.reg 15) (.reg 2)) (.const 0) ;;
  .loop (.reg 20)
    (.assign 21 (.bin .sub (.reg 20) (.const 1)) ;;
     .assign 22 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
       (.bin .mul (.const 5) (.reg 8))) (.reg 21)) ;;
     .assign 20 (.load (.reg 22)) ;;
     .store (.reg 22) (.const 0) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3))
       (.bin .mul (.const 4) (.reg 8))) (.reg 21)) (.const 0) ;;
     .store (.bin .add (.reg 18) (.reg 19)) (.reg 21) ;;
     .assign 19 (.bin .add (.reg 19) (.const 1))) ;;
  .assign 20 (.bin .add (.reg 18) (.reg 19)) ;;
  .assign 4 (.bin .add (.reg 20) (.reg 19)) ;;
  .call 21 bMergeSort [.reg 18, .reg 19, .reg 20]

/-- Step 3B': consumes `btCurBunBase[s]` / `btCurTagBase[s]` (clearing both to `0`), scatters
the `M_s` scanned `(b, packedVK)` pairs onto `bsSeenBase[b]` using 2-word heap nodes, then
flattens `bsSeenBase[candArr[i]]` into CSR arrays `r13 = candScanOff[0..candCnt]` and
`r14 = candScanBuf[0..M_s)`, restoring `bsSeenBase[b] = 0` for all `b < bunCap` and setting
`r23 = M_s`. Advances `r4` by `3 * M_s + candCnt + 1`. -/
def bundleStepEmitBuildCSRStmt : Stmt :=
  .assign 25 (.load (.reg 0)) ;;
  .assign 26 (.bin .add (.bin .add (.reg 15) (.reg 25)) (.reg 2)) ;;
  .assign 27 (.bin .add (.reg 26) (.reg 25)) ;;
  .assign 25 (.load (.reg 26)) ;;
  .assign 23 (.load (.reg 27)) ;;
  .store (.reg 26) (.const 0) ;;
  .store (.reg 27) (.const 0) ;;
  .assign 26 (.bin .add (.bin .add (.reg 7) (.const 3)) (.bin .mul (.const 3) (.reg 8))) ;;
  .loop (.reg 25)
    (.assign 27 (.load (.reg 25)) ;;
     .assign 28 (.load (.bin .add (.reg 25) (.const 1))) ;;
     .assign 25 (.load (.bin .add (.reg 25) (.const 2))) ;;
     .assign 29 (.load (.bin .add (.reg 26) (.reg 27))) ;;
     .store (.reg 4) (.reg 28) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.reg 29) ;;
     .store (.bin .add (.reg 26) (.reg 27)) (.reg 4) ;;
     .assign 4 (.bin .add (.reg 4) (.const 2))) ;;
  .assign 13 (.reg 4) ;;
  .assign 14 (.bin .add (.bin .add (.reg 13) (.reg 19)) (.const 1)) ;;
  .assign 4 (.bin .add (.reg 14) (.reg 23)) ;;
  .assign 27 (.const 0) ;;
  forRange 28 (.const 0) (.reg 19)
    (.assign 29 (.load (.bin .add (.reg 18) (.reg 28))) ;;
     .store (.bin .add (.reg 13) (.reg 28)) (.reg 27) ;;
     .assign 30 (.load (.bin .add (.reg 26) (.reg 29))) ;;
     .store (.bin .add (.reg 26) (.reg 29)) (.const 0) ;;
     .loop (.reg 30)
       (.assign 31 (.load (.reg 30)) ;;
        .store (.bin .add (.reg 14) (.reg 27)) (.reg 31) ;;
        .assign 27 (.bin .add (.reg 27) (.const 1)) ;;
        .assign 30 (.load (.bin .add (.reg 30) (.const 1))))) ;;
  .store (.bin .add (.reg 13) (.reg 19)) (.reg 27)

/-- Step 3C: reserves `[batchPtr, batchPtr + 1 + 2 * delCnt + 6 * scannedEnds)` in `r20`
(using `r23 = scannedEnds`), initializes `r21 = writeOff := 1`, `r22 = updCnt := 0`, and emits
`[1, e]` for all `e ∈ delArr`. -/
def bundleStepEmitDelRecsStmt : Stmt :=
  .assign 20 (.reg 4) ;;
  .assign 4 (.bin .add (.bin .add (.bin .add (.reg 20) (.const 1))
    (.bin .mul (.const 2) (.reg 17))) (.bin .mul (.const 6) (.reg 23))) ;;
  .assign 21 (.const 1) ;;
  .assign 22 (.const 0) ;;
  forRange 24 (.const 0) (.reg 17)
    (.assign 25 (.load (.bin .add (.reg 16) (.reg 24))) ;;
     .store (.bin .add (.reg 20) (.reg 21)) (.const 1) ;;
     .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25) ;;
     .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
     .assign 22 (.bin .add (.reg 22) (.const 1)))

/-- Scans a sorted packed-key array `mem[r27 .. r27 + r30)` (`r6 = 2 * eCap`) in one linear pass
to find the first maximum-length same-root run (matching `maxRunIdx`), setting
`r31 = winStart`, `r32 = winEnd`, `r33 = winLen = winEnd - winStart`. Preserves `r ≤ 30` and
all memory. -/
def bundleStepEmitMaxRunStmt : Stmt :=
  .assign 31 (.const 0) ;;
  .assign 32 (.const 0) ;;
  .assign 33 (.const 0) ;;
  .assign 34 (.const 0) ;;
  .loop (.bin .lt (.reg 34) (.reg 30))
    (.assign 35 (.reg 34) ;;
     .assign 36 (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) ;;
     .assign 37 (.const 1) ;;
     .loop (.reg 37)
       (.cond (.bin .lt (.reg 34) (.reg 30))
         (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 34))) (.reg 6)) (.reg 36))
           (.assign 34 (.bin .add (.reg 34) (.const 1)))
           (.assign 37 (.const 0)))
         (.assign 37 (.const 0))) ;;
     .assign 38 (.bin .sub (.reg 34) (.reg 35)) ;;
     .cond (.bin .lt (.reg 33) (.reg 38))
       (.assign 31 (.reg 35) ;;
        .assign 32 (.reg 34) ;;
        .assign 33 (.reg 38))
       .nop)

/-- Tail of `bundleStepEmitOneRunStmt` after moving `xs` from `b` to `nB`: advances `r4` past the
moved-head buffer, updates `size[b]` and `size[nB]`, then branches on `kept < moved` to either walk
`b`'s DLL and emit tag `3` (kept ends) or keep the moved buffers and emit tag `2` (moved ends), so
every split record lists the smaller side (`5 + min kept moved` words). -/
def bundleStepEmitOneRunTailStmt : Stmt :=
  .assign 4 (.bin .add (.reg 32) (.reg 34)) ;;
  .assign 36 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 25)) ;;
  .assign 37 (.bin .sub (.load (.reg 36)) (.bin .add (.reg 33) (.reg 34))) ;;
  .store (.reg 36) (.reg 37) ;;
  .store (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 31))
    (.bin .add (.reg 33) (.reg 34)) ;;
  .cond (.bin .lt (.reg 37) (.bin .add (.reg 33) (.reg 34)))
    (.assign 32 (.reg 4) ;;
     .assign 33 (.const 0) ;;
     .assign 34 (.const 0) ;;
     .assign 35 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))) ;;
     .loop (.reg 35)
       (.assign 36 (.bin .sub (.reg 35) (.const 1)) ;;
        .cond (.bin .eq (.bin .mod (.reg 36) (.const 2)) (.const 0))
          (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
            (.bin .div (.reg 36) (.const 2)) ;;
           .assign 33 (.bin .add (.reg 33) (.const 1)))
          (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 36) (.const 2)) ;;
           .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
        .assign 35 (.load (.bin .add (.reg 11) (.reg 36)))) ;;
     .assign 4 (.bin .add (.reg 32) (.reg 34)) ;;
     .assign 38 (.const 3))
    (.assign 38 (.const 2)) ;;
  forRange 36 (.const 0) (.reg 34)
    (.store (.bin .add (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33)) (.reg 36))
      (.load (.bin .add (.reg 32) (.reg 36)))) ;;
  .store (.bin .add (.reg 20) (.reg 21)) (.reg 38) ;;
  .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25) ;;
  .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 2)) (.reg 31) ;;
  .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 3)) (.reg 33) ;;
  .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 4)) (.reg 34) ;;
  .assign 21 (.bin .add (.bin .add (.bin .add (.reg 21) (.const 5)) (.reg 33)) (.reg 34)) ;;
  .assign 22 (.bin .add (.reg 22) (.const 1))

/-- Step 3D-inner: moves one maximal same-vertex run starting at `r29 = idx` (vertex `r30 = vCur`)
from bundle `r25 = b` to fresh bundle `r31 = b'`, emits a compact tag-`2` or tag-`3` split record
at `r20 + r21` listing the smaller side, and updates `size[b]`, `size[b']`, `r21`, `r22`, `r29`,
and `r4`. -/
def bundleStepEmitOneRunStmt (bDllPush bDllErase : ℕ) : Stmt :=
  .assign 30 (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) ;;
  .assign 31 (.load (.bin .add (.reg 7) (.const 1))) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.bin .add (.reg 31) (.const 1)) ;;
  .assign 32 (.reg 4) ;;
  .assign 33 (.const 0) ;;
  .assign 34 (.const 0) ;;
  .assign 35 (.const 1) ;;
  .loop (.reg 35)
    (.cond (.bin .lt (.reg 29) (.reg 26))
      (.assign 36 (.load (.bin .add (.reg 27) (.reg 29))) ;;
       .cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30))
         (.assign 37 (.bin .mod (.reg 36) (.reg 6)) ;;
          .call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] ;;
          .call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] ;;
          .store (.bin .add (.reg 9) (.reg 37)) (.reg 31) ;;
          .cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
            (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
              (.bin .div (.reg 37) (.const 2)) ;;
             .assign 33 (.bin .add (.reg 33) (.const 1)))
            (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
             .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
          .assign 29 (.bin .add (.reg 29) (.const 1)))
         (.assign 35 (.const 0)))
      (.assign 35 (.const 0))) ;;
  bundleStepEmitOneRunTailStmt

/-- Step 3D: splits candidate bundle `b = candArr[r24]` by final core vertex in time proportional
to its scanned ends `m_b = candScanOff[r24+1] - candScanOff[r24]`:
* Branch 1 (`winLen < degB - m_b`): the unscanned kept run is strictly largest, so it keeps name
  `b` untouched while all runs of `packArr[0..m_b)` move into fresh bundles.
* Branch 2 (`degB - m_b ≤ winLen`, hence `degB ≤ 2 * m_b`): packs all `degB` ends via `bTourOwner`,
  sorts, finds the first maximum-length run `[winStart, winEnd)`, keeps it in `b`, and emits runs
  in `[0, winStart)` and `[winEnd, degB)`. -/
def bundleStepEmitOneCandStmt (bDllPush bDllErase bMergeSort bTourOwner : ℕ) : Stmt :=
  .assign 25 (.load (.bin .add (.reg 18) (.reg 24))) ;;
  .assign 26 (.load (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 25))) ;;
  .cond (.reg 26)
    (.assign 28 (.load (.bin .add (.reg 13) (.reg 24))) ;;
     .assign 29 (.load (.bin .add (.reg 13) (.bin .add (.reg 24) (.const 1)))) ;;
     .assign 30 (.bin .sub (.reg 29) (.reg 28)) ;;
     .cond (.reg 30)
       (.assign 27 (.reg 4) ;;
        .assign 4 (.bin .add (.reg 27) (.reg 30)) ;;
        forRange 31 (.const 0) (.reg 30)
          (.store (.bin .add (.reg 27) (.reg 31))
            (.load (.bin .add (.reg 14) (.bin .add (.reg 28) (.reg 31))))) ;;
        .assign 28 (.reg 4) ;;
        .assign 4 (.bin .add (.reg 28) (.reg 30)) ;;
        .call 29 bMergeSort [.reg 27, .reg 30, .reg 28] ;;
        bundleStepEmitMaxRunStmt ;;
        .cond (.bin .lt (.reg 33) (.bin .sub (.reg 26) (.reg 30)))
          (.assign 26 (.reg 30) ;;
           .assign 29 (.const 0) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase))
          (.assign 27 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 27) (.reg 26)) ;;
           .assign 28 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))) ;;
           .assign 29 (.const 0) ;;
           .loop (.reg 28)
             (.assign 30 (.bin .sub (.reg 28) (.const 1)) ;;
              .assign 31 (.reg 4) ;;
              .call 4 bTourOwner [.reg 1, .reg 30, .reg 4] ;;
              .assign 32 (.load (.reg 31)) ;;
              .store (.bin .add (.reg 27) (.reg 29))
                (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)) ;;
              .assign 29 (.bin .add (.reg 29) (.const 1)) ;;
              .assign 28 (.load (.bin .add (.reg 11) (.reg 30)))) ;;
           .assign 28 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 28) (.reg 26)) ;;
           .call 29 bMergeSort [.reg 27, .reg 26, .reg 28] ;;
           .assign 30 (.reg 26) ;;
           bundleStepEmitMaxRunStmt ;;
           .assign 23 (.reg 26) ;;
           .assign 28 (.reg 32) ;;
           .assign 26 (.reg 31) ;;
           .assign 29 (.const 0) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase) ;;
           .assign 26 (.reg 23) ;;
           .assign 29 (.reg 28) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase)))
       .nop)
    .nop

/-- `args = [tbl, tourH, s, outDescPtr, h]`: Phase 3 emission for one touched slot `s`.
Pops & sorts deletions and candidate splitting bundles, builds per-candidate scanned-end CSR from
`btCurBunBase[s]`/`btCurTagBase[s]` (clearing both to `0`), splits each candidate in time
proportional to its scanned ends, restores all per-slot scratch arrays to `0`, writes `BatchAt`
at a freshly allocated `batchPtr`, stores `[s, batchPtr, totalWords]` at `outDescPtr`, and returns
the new heap pointer `h'`. -/
def bundleStepEmitSlotStmt (bDllPush bDllErase bMergeSort bTourOwner : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 6 (.bin .mul (.const 2) (.reg 5)) ;;
  .assign 7 (.load (.bin .add (.load (.bin .add (.reg 0) (.const 3))) (.reg 2))) ;;
  .assign 8 (.load (.reg 7)) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 7))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const 8))) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const 11))) ;;
  bundleStepEmitPopDelsStmt bMergeSort ;;
  bundleStepEmitPopCandsStmt bMergeSort ;;
  bundleStepEmitBuildCSRStmt ;;
  bundleStepEmitDelRecsStmt ;;
  forRange 24 (.const 0) (.reg 19)
    (bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner) ;;
  .store (.bin .add (.reg 12) (.reg 2)) (.const 0) ;;
  .store (.reg 20) (.reg 22) ;;
  .store (.reg 3) (.reg 2) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 20) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 21) ;;
  .ret (.reg 4)

lemma bundleStepEmitPopDelsStmt_noRand (bMergeSort : ℕ) :
    (bundleStepEmitPopDelsStmt bMergeSort).NoRand := by
  simp only [bundleStepEmitPopDelsStmt, Stmt.NoRand]; trivial

lemma bundleStepEmitPopCandsStmt_noRand (bMergeSort : ℕ) :
    (bundleStepEmitPopCandsStmt bMergeSort).NoRand := by
  simp only [bundleStepEmitPopCandsStmt, Stmt.NoRand]; trivial

lemma bundleStepEmitBuildCSRStmt_noRand : bundleStepEmitBuildCSRStmt.NoRand := by
  simp only [bundleStepEmitBuildCSRStmt, forRange, Stmt.NoRand]; trivial

lemma bundleStepEmitDelRecsStmt_noRand : bundleStepEmitDelRecsStmt.NoRand := by
  simp only [bundleStepEmitDelRecsStmt, forRange, Stmt.NoRand]; trivial

lemma bundleStepEmitMaxRunStmt_noRand : bundleStepEmitMaxRunStmt.NoRand := by
  simp only [bundleStepEmitMaxRunStmt, Stmt.NoRand]; trivial

lemma bundleStepEmitOneRunStmt_noRand (bDllPush bDllErase : ℕ) :
    (bundleStepEmitOneRunStmt bDllPush bDllErase).NoRand := by
  simp only [bundleStepEmitOneRunStmt, bundleStepEmitOneRunTailStmt, forRange, Stmt.NoRand]; trivial

lemma bundleStepEmitOneCandStmt_noRand (bDllPush bDllErase bMergeSort bTourOwner : ℕ) :
    (bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner).NoRand := by
  unfold bundleStepEmitOneCandStmt forRange
  repeat first
    | exact bundleStepEmitMaxRunStmt_noRand
    | exact bundleStepEmitOneRunStmt_noRand _ _
    | exact trivial
    | constructor

lemma bundleStepEmitSlotStmt_noRand (bDllPush bDllErase bMergeSort bTourOwner : ℕ) :
    (bundleStepEmitSlotStmt bDllPush bDllErase bMergeSort bTourOwner).NoRand := by
  unfold bundleStepEmitSlotStmt forRange
  repeat first
    | exact bundleStepEmitPopDelsStmt_noRand _
    | exact bundleStepEmitPopCandsStmt_noRand _
    | exact bundleStepEmitBuildCSRStmt_noRand
    | exact bundleStepEmitDelRecsStmt_noRand
    | exact bundleStepEmitOneCandStmt_noRand _ _ _ _
    | exact trivial
    | constructor

/-! ## 2. Space and cost bounds for Phase 3 -/

/-- Heap space budget for `bundleStepEmitSlotStmt` given `delCnt` deletions, `candCnt` candidates,
and `scannedEnds` total scanned candidate-bundle ends of the slot. -/
def bundleStepEmitSlotSpace (TS : BundleTourSpec) (delCnt candCnt scannedEnds : ℕ) : ℕ :=
  2 + 4 * delCnt + 3 * candCnt + (17 + 2 * TS.querySpace) * scannedEnds

/-- Cost bound for `bundleStepEmitSlotStmt` (excluding tour potential drop), proportional to
`scannedEnds` rather than `candEndsSum`. -/
def bundleStepEmitSlotCost (TS : BundleTourSpec) (eCap delCnt candCnt scannedEnds : ℕ) : ℕ :=
  300 * delCnt * (Nat.log 2 (delCnt + 1) + 1) +
  300 * candCnt * (Nat.log 2 (candCnt + 1) + 1) +
  (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scannedEnds + 1) + 1) + 1050) * scannedEnds +
  500 * candCnt + 550

/-! ## 3. Packed-key encoding and `SmallBatchAt` helpers -/

end

public section

lemma packEndKey_div {eCap v key : ℕ} (hk : key < 2 * eCap) :
    packEndKey eCap v key / (2 * eCap) = v := by
  unfold packEndKey
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, zero_add]

lemma packEndKey_mod {eCap v key : ℕ} (hk : key < 2 * eCap) :
    packEndKey eCap v key % (2 * eCap) = key := by
  unfold packEndKey
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

lemma packEndKey_lt_iff {eCap v₁ k₁ v₂ k₂ : ℕ} (hk₁ : k₁ < 2 * eCap) (hk₂ : k₂ < 2 * eCap) :
    packEndKey eCap v₁ k₁ < packEndKey eCap v₂ k₂ ↔ v₁ < v₂ ∨ (v₁ = v₂ ∧ k₁ < k₂) := by
  unfold packEndKey
  constructor
  · intro h
    by_cases hv : v₁ < v₂
    · exact Or.inl hv
    · by_cases heq : v₁ = v₂
      · exact Or.inr ⟨heq, by subst heq; omega⟩
      · have hgt : v₂ + 1 ≤ v₁ := by omega
        have hmul : (v₂ + 1) * (2 * eCap) ≤ v₁ * (2 * eCap) := Nat.mul_le_mul_right _ hgt
        rw [Nat.add_mul, Nat.one_mul] at hmul; omega
  · rintro (hlt | ⟨rfl, hk⟩)
    · have hle : v₁ + 1 ≤ v₂ := hlt
      have hmul : (v₁ + 1) * (2 * eCap) ≤ v₂ * (2 * eCap) := Nat.mul_le_mul_right _ hle
      rw [Nat.add_mul, Nat.one_mul] at hmul; omega
    · omega

lemma packEndKey_le_iff {eCap v₁ k₁ v₂ k₂ : ℕ} (hk₁ : k₁ < 2 * eCap) (hk₂ : k₂ < 2 * eCap) :
    packEndKey eCap v₁ k₁ ≤ packEndKey eCap v₂ k₂ ↔ v₁ < v₂ ∨ (v₁ = v₂ ∧ k₁ ≤ k₂) := by
  rw [← not_lt, packEndKey_lt_iff hk₂ hk₁]
  push Not
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : v₁ = v₂
    · exact Or.inr ⟨h, h2 h.symm⟩
    · exact Or.inl (by omega)
  · rintro (h | ⟨rfl, h⟩)
    · exact ⟨by omega, fun h' => by omega⟩
    · exact ⟨le_refl _, fun _ => h⟩

lemma packEndKey_inj {eCap v₁ k₁ v₂ k₂ : ℕ} (hk₁ : k₁ < 2 * eCap) (hk₂ : k₂ < 2 * eCap)
    (heq : packEndKey eCap v₁ k₁ = packEndKey eCap v₂ k₂) : v₁ = v₂ ∧ k₁ = k₂ :=
  ⟨(packEndKey_div hk₁).symm.trans ((congrArg (· / (2 * eCap)) heq).trans (packEndKey_div hk₂)),
   (packEndKey_mod hk₁).symm.trans ((congrArg (· % (2 * eCap)) heq).trans (packEndKey_mod hk₂))⟩

/-- Any permutation of a `Nodup` list `L` that is sorted (`Pairwise (· ≤ ·)`) equals
`L.toFinset.sort (· ≤ ·)`. -/
lemma sorted_perm_eq_toFinset_sort {L L' : List ℕ} (hnd : L.Nodup) (hperm : L'.Perm L)
    (hsort : L'.Pairwise (· ≤ ·)) :
    L' = L.toFinset.sort (· ≤ ·) := by
  have hnd' : L'.Nodup := hperm.nodup_iff.mpr hnd
  have hperm2 : L'.Perm (L.toFinset.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hnd' (Finset.sort_nodup _ _)]
    intro x; simp [Finset.mem_sort, List.mem_toFinset, hperm.mem_iff]
  exact hperm2.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hsort (Finset.pairwise_sort _ _)

/-- Canonical sorted packed-key list of `B.ends b` equals the flatMap of `rawByRootVRuns`. -/
lemma rawByRootVRuns_pack_eq_sort {eCap : ℕ} {B : BundleState} {E : Finset ℕ}
    {src' : End → ℕ} {b : ℕ} (hE : ∀ e ∈ E, e < eCap) :
    ((rawByRootVRuns B E src' b).flatMap fun vr => vr.2.map fun x => packEndKey eCap vr.1 (endKey x)) =
      ((survivingEnds B E b).image fun x => packEndKey eCap (src' x) (endKey x)).sort (· ≤ ·) := by
  set L := (rawByRootVRuns B E src' b).flatMap fun vr => vr.2.map fun x => packEndKey eCap vr.1 (endKey x)
  set S := (survivingEnds B E b).image fun x => packEndKey eCap (src' x) (endKey x)
  have hk_lt : ∀ x ∈ survivingEnds B E b, endKey x < 2 * eCap := fun x hx => by
    have he := hE x.1 (Finset.mem_filter.mp hx).2
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  have hL_pw : L.Pairwise (· < ·) := by
    simp only [L, rawByRootVRuns, List.flatMap_map, List.map_map]
    rw [List.pairwise_flatMap]
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [List.pairwise_map]
      have hsort_nd := Finset.sort_nodup (((survivingEnds B E b).filter fun x => src' x = v).image endKey) (· ≤ ·)
      have hsort_le := Finset.pairwise_sort (((survivingEnds B E b).filter fun x => src' x = v).image endKey) (· ≤ ·)
      have hlt : (((survivingEnds B E b).filter fun x => src' x = v).image endKey).sort (· ≤ ·)
          |>.Pairwise (· < ·) :=
        (hsort_le.and hsort_nd).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2
      refine hlt.imp_of_mem fun {k₁ k₂} hk₁ hk₂ h12 => ?_
      have hmem₁ := (Finset.mem_sort (r := (· ≤ ·))).mp hk₁
      have hmem₂ := (Finset.mem_sort (r := (· ≤ ·))).mp hk₂
      obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hmem₁
      obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hmem₂
      simp only [Function.comp_apply, bundle_endKey_endOfKey]
      rw [packEndKey_lt_iff (hk_lt _ (Finset.mem_filter.mp hx₁).1) (hk_lt _ (Finset.mem_filter.mp hx₂).1)]
      exact Or.inr ⟨rfl, h12⟩
    · have hV_lt : ((finalRootsOf B E src' b).sort (· ≤ ·)).Pairwise (· < ·) :=
        ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2
      refine hV_lt.imp fun {v₁ v₂} hv12 p₁ hp₁ p₂ hp₂ => ?_
      simp only [List.mem_map, Function.comp_apply, Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
      rcases hp₁ with ⟨k₁, ⟨x₁, ⟨hx₁, _⟩, rfl⟩, rfl⟩
      rcases hp₂ with ⟨k₂, ⟨x₂, ⟨hx₂, _⟩, rfl⟩, rfl⟩
      simp only [bundle_endKey_endOfKey]
      rw [packEndKey_lt_iff (hk_lt _ hx₁) (hk_lt _ hx₂)]
      exact Or.inl hv12
  have hL_nd : L.Nodup := hL_pw.imp ne_of_lt
  have hL_le : L.Pairwise (· ≤ ·) := hL_pw.imp le_of_lt
  have hperm : L.Perm (S.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hL_nd (Finset.sort_nodup _ _)]
    intro pk
    simp only [L, S, rawByRootVRuns, List.mem_flatMap, List.mem_map, Finset.mem_sort,
      Finset.mem_image, finalRootsOf]
    constructor
    · rintro ⟨⟨v, xs⟩, ⟨v', ⟨x₀, _, rfl⟩, hpair⟩, x, hx, rfl⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hx
      rcases hx with ⟨k, ⟨y, ⟨hy, hyv⟩, rfl⟩, rfl⟩
      exact ⟨y, hy, by rw [bundle_endOfKey_endKey, hyv]⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(src' y, _), ⟨src' y, ⟨y, hy, rfl⟩, rfl⟩, y, ?_, rfl⟩
      refine List.mem_map.mpr ⟨endKey y, ?_, bundle_endOfKey_endKey y⟩
      rw [Finset.mem_sort]; exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩, rfl⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hL_le (Finset.pairwise_sort _ _)

/-- Appending two `BatchBodyAt` segments concatenates their update lists and sums their word
lengths. -/
lemma batchBodyAt_append {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U₁ U₂ : List Update} {w₁ w₂ : ℕ}
    (h1 : BatchBodyAt mem a G U₁ w₁)
    (h2 : BatchBodyAt mem (a + w₁) (G.applyBatch U₁) U₂ w₂) :
    BatchBodyAt mem a G (U₁ ++ U₂) (w₁ + w₂) := by
  induction U₁ generalizing a G w₁ with
  | nil =>
    simp only [BatchBodyAt] at h1; subst h1
    simpa [MGraph.applyBatch] using h2
  | cons u us ih =>
    rcases h1 with ⟨len, hlen, hu, hrest⟩
    refine ⟨len, by omega, hu, ?_⟩
    have hsub : w₁ + w₂ - len = (w₁ - len) + w₂ := by omega
    rw [hsub]
    refine ih hrest ?_
    have haddr : a + len + (w₁ - len) = a + w₁ := by omega
    rw [haddr]; exact h2

/-- Appending a single encoded update at the end of a `BatchBodyAt` segment. -/
lemma bundle_batchBodyAt_snoc {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {u : Update}
    {w₁ len : ℕ} (h1 : BatchBodyAt mem a G U w₁)
    (hu : UpdateAt mem (a + w₁) (G.applyBatch U) u len) :
    BatchBodyAt mem a G (U ++ [u]) (w₁ + len) :=
  batchBodyAt_append h1 ⟨len, le_refl _, hu, by simp [BatchBodyAt]⟩

/-- Locality of `BatchBodyAt`: preserving memory on `[a, a + tot)` preserves `BatchBodyAt`. -/
lemma batchBodyAt_agree {m1 m2 : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {tot : ℕ}
    (h : BatchBodyAt m1 a G U tot) (hEq : ∀ x, a ≤ x → x < a + tot → m2 x = m1 x) :
    BatchBodyAt m2 a G U tot := by
  induction U generalizing a G tot with
  | nil => exact h
  | cons u us ih =>
    rcases h with ⟨len, hlen, hu, hrest⟩
    refine ⟨len, hlen, ?_, ih hrest fun x hx1 hx2 => hEq x (by omega) (by omega)⟩
    cases u with
    | insert e x y =>
      rcases hu with ⟨rfl, hL⟩
      exact ⟨rfl, fun i hi => (hEq (a + i) (by omega) (by simp at hi; omega)).trans (hL i hi)⟩
    | delete e =>
      rcases hu with ⟨rfl, hL⟩
      exact ⟨rfl, fun i hi => (hEq (a + i) (by omega) (by simp at hi; omega)).trans (hL i hi)⟩
    | split v v' St Sh =>
      rcases hu with ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, hL⟩ | ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, hL⟩
      · refine Or.inl ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        exact (hEq (a + i) (by omega) (by omega)).trans (hL i (by simp; omega))
      · refine Or.inr ⟨Lt, Lh, hnd1, hnd2, h1, h2, hlen_eq, fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        exact (hEq (a + i) (by omega) (by omega)).trans (hL i (by simp; omega))

end

end MinCostFlow.SparseCore.Program
