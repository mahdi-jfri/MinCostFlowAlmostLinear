module

public import MinCostFlow.MinRatio.WireSelectUpdate
public import MinCostFlow.MinRatio.WireFindCycleSpec
public import MinCostFlow.MinRatio.PathCompareExchange
public import MinCostFlow.MinRatio.PathSwapHistory
public import MinCostFlow.MinRatio.PathCancellationAccounting
public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.IsZero
import WordRAM.Tactic

/-!
# Word-RAM cycle-query (`Select`) and path-cancellation post-processing

Implements the cycle query (`FindCycle` / `Select`) of Algorithm 1 (page 21) and Algorithm 2
(page 29) on the maintained select-heap `SelectHeapLoc`:
1. `selectRawRouteBody` (`[root, hb, descBase, workHeap]`):
   - Reads `size := mem[hb]` in O(1); if `size = 0`, writes empty `[workHeap, 0, workHeap, 0]`
     at `descBase + 2 .. descBase + 5` and returns `workHeap`.
   - Otherwise reads `eBest := arr[0]` (`O(1)`), `lvl := lvl[eBest]` (`O(1)`), tests the sign
     `N_{eBest} ≤ 0` via `Num.isNegative` + `Num.isZero` (`O(Lk)`), calls `opCore 4` when
     `lvl < d` (`O(P.readout)`), and emits `edges_raw` (`ExplicitEdgesAt`, matching
     `rawEdgesOfWalk`) and `paths_raw` (`PathEndpointsAt`, matching `rawPathsOfWalk`) in
     `O(|W|)` steps.
   - Total raw-query cost: **`O(Lk + P.readout + |W|)`** (`O(log)` plus cycle length).
2. `cancelRoutePathsBody` (`[root, pathsBase, pathsLen, workHeap]`):
   - Runs the repeated `(i < j)` scan calling `opTree 3` (`PathSummary`) on `(a, b), (c, d),
     (a, d), (c, b)` and `pathCompareExchangeBody` on `[s_ab + L, s_cd + L, s_ad + L, s_cb + L,
     L, pathsBase + 2*i + 1, pathsBase + 2*j + 1, work]`.
   - By `pathSwap_index_history` and `pathCancel_account_of_index_scan`, terminates in at most
     `4 * K^4` swaps and `(4 * K^4 + 1) * K^2` comparisons, producing cancellation-free `paths`
     meeting `CycleRouteAt model edges paths`.
3. `selectRouteBody` (`[root, descBase, workHeap]` with `hb` read from a fixed root/wrapper arg
   `selectRouteWithHeapBody [root, hb, descBase, workHeap]`): composes `selectRawRouteBody`
   and `cancelRoutePathsBody`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program LinkCut

/-! ## 1. Tail-recursive route-extraction helpers and `selectRawRouteBody` -/

/-- Fill `stepsBase[2*(t+1) .. 2*embLen+1]` with `walkRev (emb[eBest])` starting at index `t`.
Arguments: `[wPtr, embLen, stepsBase, t]`. -/
def selectFillRevBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 3) (.reg 1))
    (.assign 4 (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 3)) ;; -- embLen - 1 - t
     .assign 5 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 2) (.reg 4)))) ;;
     .assign 6 (.bin .sub (.const 1)
       (.load (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 4))))) ;;
     .assign 7 (.bin .add (.reg 3) (.const 1)) ;;
     .store (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.reg 5) ;;
     .store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.const 1)) (.reg 6) ;;
     .call 8 self [.reg 0, .reg 1, .reg 2, .reg 7] ;;
     .ret (.const 0))
    (.ret (.const 0))

/-- Scan `stepsBase[0 .. K - 1]` from index `t`, orienting each step by `flip` and partitioning
into off-tree edges (`mem[slots + f] = 0`, written to `edgesBase`, incrementing `mem[descBase + 3]`)
vs single-edge tree paths (`mem[slots + f] ≠ 0`, written to `pathsBase`, incrementing
`mem[descBase + 5]`).
Arguments: `[slots, intToExt, tailSlot, headSlot, stepsBase, K, flip, edgesBase, pathsBase, descBase, t]`. -/
def selectSplitStepsBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 10) (.reg 5))
    (.assign 11 (.load (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 10)))) ;; -- f
     .assign 12 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 10))) (.const 1))) ;; -- d
     .cond (.reg 6) (.assign 12 (.bin .sub (.const 1) (.reg 12))) .nop ;; -- d_or
     .assign 13 (.load (.bin .add (.reg 0) (.reg 11))) ;; -- slots[f]
     .cond (.bin .eq (.reg 13) (.const 0))
       (.assign 14 (.load (.bin .add (.reg 9) (.const 3))) ;; -- eCnt
        .store (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 14))) (.reg 11) ;;
        .store (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 12) ;;
        .store (.bin .add (.reg 9) (.const 3)) (.bin .add (.reg 14) (.const 1)))
       (.assign 14 (.load (.bin .add (.reg 9) (.const 5))) ;; -- pCnt
        .assign 15 (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 2) (.reg 11))))) ;; -- tail0(f)
        .assign 16 (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 3) (.reg 11))))) ;; -- head0(f)
        .cond (.reg 12)
          (.store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.reg 15) ;;
           .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 16))
          (.store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.reg 16) ;;
           .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 14))) (.const 1)) (.reg 15)) ;;
        .store (.bin .add (.reg 9) (.const 5)) (.bin .add (.reg 14) (.const 1))) ;;
     .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
       .bin .add (.reg 10) (.const 1)] ;;
     .ret (.const 0))
    (.ret (.const 0))

/-- Append the `K` stitching endpoint pairs of `(cycleSegments (C.G 0) W).2` (swapped when `flip = 1`)
into `pathsBase` starting from step index `t`, incrementing `mem[descBase + 5]`.
Arguments: `[intToExt, tailSlot, headSlot, stepsBase, K, flip, pathsBase, descBase, t]`. -/
def selectEmitStitchesBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 8) (.reg 4))
    (.assign 9 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8)))) ;; -- f_t
     .assign 10 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 8))) (.const 1))) ;; -- d_t
     .assign 11 (.bin .mod (.bin .add (.reg 8) (.const 1)) (.reg 4)) ;; -- (t + 1) % K
     .assign 12 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 11)))) ;; -- f_{next}
     .assign 13 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 11))) (.const 1))) ;; -- d_{next}
     .cond (.reg 10)
       (.assign 14 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 2) (.reg 9))))))
       (.assign 14 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 9)))))) ;; -- dst(W[t])
     .cond (.reg 13)
       (.assign 15 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 12))))))
       (.assign 15 (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 2) (.reg 12)))))) ;; -- src(W[next])
     .assign 16 (.load (.bin .add (.reg 7) (.const 5))) ;; -- pCnt
     .cond (.reg 5)
       (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 15) ;;
        .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 14))
       (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.reg 14) ;;
        .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg 15)) ;;
     .store (.bin .add (.reg 7) (.const 5)) (.bin .add (.reg 16) (.const 1)) ;;
     .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
       .bin .add (.reg 8) (.const 1)] ;;
     .ret (.const 0))
    (.ret (.const 0))

/-- Raw cycle-route extractor (`args = [root, hb, descBase, workHeap]`):
reads the top candidate `eBest = arr[0]` from `hb` in `O(1)`, determines its orientation
`flip = !(decide (N_{eBest} ≤ 0))` in `O(Lk)`, reads `emb[eBest]` directly from the owned
embedding table `embPtr[i]` in `metaPtr` when `i < d` (`O(1)` lookup), and emits exact
`rawEdgesOfWalk C.chainTree W flip` (internal off-tree edge IDs) and
`rawPathsOfWalk (C.G 0) C.chainTree W flip` (tree steps + stitches) in `O(Lk + K)`. -/
def selectRawRouteBody (isNegProc isZeroProc fillRev splitSteps emitStitches : ℕ) : Stmt :=
  -- args: 0 = root, 1 = hb, 2 = descBase, 3 = workHeap
  .assign 4 (.load (.reg 1)) ;; -- size
  .cond (.bin .eq (.reg 4) (.const 0))
    (.store (.bin .add (.reg 2) (.const 2)) (.reg 3) ;;
     .store (.bin .add (.reg 2) (.const 3)) (.const 0) ;;
     .store (.bin .add (.reg 2) (.const 4)) (.reg 3) ;;
     .store (.bin .add (.reg 2) (.const 5)) (.const 0) ;;
     .ret (.reg 3))
    (.assign 5 (.load (.bin .add (.reg 1) (.const shLkOff))) ;; -- Lk
     .assign 6 (.load (.bin .add (.reg 1) (.const shArrOff))) ;; -- arrPtr
     .assign 7 (.load (.bin .add (.reg 1) (.const shLvlOff))) ;; -- lvlPtr
     .assign 8 (.load (.bin .add (.reg 1) (.const shNumOff))) ;; -- numBase
     .assign 9 (.load (.reg 6)) ;; -- eBest = arr[0]
     .assign 10 (.load (.bin .add (.reg 7) (.reg 9))) ;; -- i = lvl[eBest]
     .assign 11 (.bin .add (.reg 8) (.bin .mul (.reg 9) (.reg 5))) ;; -- numPtr
     .call 12 isNegProc [.reg 11, .reg 5] ;;
     .call 13 isZeroProc [.reg 11, .reg 5] ;;
     -- `flip = 1` iff `N_{eBest} > 0` iff `isNeg = 0 ∧ isZero = 0`
     .assign 14 (.bin .eq (.bin .add (.reg 12) (.reg 13)) (.const 0)) ;; -- flip ∈ {0, 1}
     -- Load solver directory pointers: handle, d, slots, rootGraph (`dgIntToExtBase`, `dgETailSlotBase`, `dgEHeadSlotBase`)
     .assign 15 (.load (.reg 0)) ;; -- tok.handle
     .assign 16 (.load (.bin .add (.reg 15) (.const 11))) ;; -- d
     .assign 17 (.load (.bin .add (.reg 0) (.const 6))) ;; -- tok.slots
     .assign 18 (.load (.bin .add (.reg 0) (.const 14))) ;; -- tok.rootGraph
     .assign 19 (.load (.reg 18)) ;; -- vCap0
     .assign 20 (.load (.bin .add (.reg 18) (.const 1))) ;; -- eCap0
     .assign 21 (.bin .add (.bin .add (.reg 18) (.const 4)) (.bin .mul (.const 4) (.reg 19))) ;; -- intToExt0
     .assign 22 (.bin .add (.bin .add (.bin .add (.reg 18) (.const 4))
       (.bin .mul (.const 7) (.reg 19))) (.bin .mul (.const 3) (.reg 20))) ;; -- tailSlot0
     .assign 23 (.bin .add (.reg 22) (.reg 20)) ;; -- headSlot0
     -- Branch on `i = d` (cycle length 1) vs `i < d` (direct lookup in owned `embPtr[i]`)
     .cond (.bin .eq (.reg 10) (.reg 16))
       (.assign 24 (.reg 3) ;; -- edgesBase = workHeap
        .assign 25 (.bin .add (.reg 3) (.const 2)) ;; -- pathsBase = workHeap + 2
        .assign 26 (.bin .sub (.const 1) (.reg 14)) ;; -- dirBit = 1 - flip
        .assign 27 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 22) (.reg 9))))) ;; -- tail0(eBest)
        .assign 28 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 23) (.reg 9))))) ;; -- head0(eBest)
        .store (.reg 24) (.reg 9) ;;
        .store (.bin .add (.reg 24) (.const 1)) (.reg 26) ;;
        .cond (.reg 26)
          (.store (.reg 25) (.reg 28) ;; .store (.bin .add (.reg 25) (.const 1)) (.reg 27))
          (.store (.reg 25) (.reg 27) ;; .store (.bin .add (.reg 25) (.const 1)) (.reg 28)) ;;
        .store (.bin .add (.reg 2) (.const 2)) (.reg 24) ;;
        .store (.bin .add (.reg 2) (.const 3)) (.const 1) ;;
        .store (.bin .add (.reg 2) (.const 4)) (.reg 25) ;;
        .store (.bin .add (.reg 2) (.const 5)) (.const 1) ;;
        .ret (.bin .add (.reg 3) (.const 4)))
       (.assign 27 (.load (.bin .add (.reg 1) (.const shMetaOff))) ;; -- metaPtr
        .assign 28 (.bin .add (.bin .add (.reg 27) (.const smTableOff))
          (.bin .add (.bin .mul (.const 5) (.bin .add (.reg 16) (.const 1))) (.reg 10))) ;; -- smEntryAddr metaPtr d 5 i
        .assign 30 (.load (.reg 28)) ;; -- embPtr = mloc.embPtr i
        .assign 31 (.load (.bin .add (.reg 30) (.reg 9))) ;; -- wPtr = emb[eBest]
        .assign 32 (.load (.reg 31)) ;; -- embLen = |emb_i(eBest)|
        .assign 33 (.bin .add (.reg 32) (.const 1)) ;; -- K = 1 + embLen
        .assign 34 (.reg 3) ;; -- stepsBase = workHeap
        .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;; -- edgesBase = workHeap + 2*K
        .assign 36 (.bin .add (.reg 35) (.bin .mul (.const 2) (.reg 33))) ;; -- pathsBase = workHeap + 4*K
        .assign 37 (.bin .add (.reg 36) (.bin .mul (.const 4) (.reg 33))) ;; -- work1 = workHeap + 8*K
        .store (.reg 34) (.reg 9) ;;
        .store (.bin .add (.reg 34) (.const 1)) (.const 1) ;;
        .call 38 fillRev [.reg 31, .reg 32, .reg 34, .const 0] ;;
        .store (.bin .add (.reg 2) (.const 2)) (.reg 35) ;;
        .store (.bin .add (.reg 2) (.const 3)) (.const 0) ;;
        .store (.bin .add (.reg 2) (.const 4)) (.reg 36) ;;
        .store (.bin .add (.reg 2) (.const 5)) (.const 0) ;;
        .call 38 splitSteps [.reg 17, .reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
          .reg 35, .reg 36, .reg 2, .const 0] ;;
        .call 38 emitStitches [.reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
          .reg 36, .reg 2, .const 0] ;;
        .ret (.reg 37)))

theorem selectFillRevBody_noRand (self : ℕ) : (selectFillRevBody self).NoRand := by
  simp [selectFillRevBody, Stmt.NoRand]

theorem selectSplitStepsBody_noRand (self : ℕ) : (selectSplitStepsBody self).NoRand := by
  simp [selectSplitStepsBody, Stmt.NoRand]

theorem selectEmitStitchesBody_noRand (self : ℕ) : (selectEmitStitchesBody self).NoRand := by
  simp [selectEmitStitchesBody, Stmt.NoRand]

theorem selectRawRouteBody_noRand (isNegProc isZeroProc fillRev splitSteps emitStitches : ℕ) :
    (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches).NoRand := by
  simp [selectRawRouteBody, Stmt.NoRand]

/-- Raw cycle-query space bound: `8 * K` words (`2*K` steps + `2*K` edges + `4*K` paths). -/
def selectRawRouteSpace (K : ℕ) : ℕ := 8 * K

/-- Raw cycle-query time cost bound: **`O(Lk + K)`** (`O(log)` + cycle length). -/
def selectRawRouteCost (Lk K : ℕ) : ℕ :=
  19 * Lk + 350 * K + 360

/-! ## 2. Tail-recursive `cancelRoutePathsBody`: `O(K^6 · pathTreeBudget)` path cancellation -/

/-- Inner increasing-index scan (`j .. K - 1` for fixed `i`), calling `opTree 3` (`PathSummary`)
four times per pair `(i, j)` and `cmpExch` (`pathCompareExchangeBody`), setting `mem[flagPtr] := 1`
whenever a swap occurs, and returning the final scratch pointer.
Arguments: `[treeHeap, L, pathsBase, K, i, j, flagPtr, work]`. -/
def cancelPairInnerBody (self opTree3 cmpExch : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 5) (.reg 3))
    (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))) ;; -- a
     .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;; -- b
     .assign 10 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5)))) ;; -- c
     .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1))) ;; -- d
     .assign 12 (.reg 7) ;; -- s_ab
     .call 7 opTree3 [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
     .assign 18 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1))) ;;
     .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
     .assign 13 (.reg 7) ;; -- s_cd
     .call 7 opTree3 [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
     .assign 18 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 1))) ;;
     .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
     .assign 14 (.reg 7) ;; -- s_ad
     .call 7 opTree3 [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
     .assign 18 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 1))) ;;
     .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
     .assign 15 (.reg 7) ;; -- s_cb
     .call 7 opTree3 [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
     .assign 18 (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 1))) ;;
     .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
     .call 16 cmpExch
       [.bin .add (.reg 12) (.reg 1),
        .bin .add (.reg 13) (.reg 1),
        .bin .add (.reg 14) (.reg 1),
        .bin .add (.reg 15) (.reg 1),
        .reg 1,
        .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1),
        .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1),
        .reg 7] ;;
     .assign 7 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 1))) ;;
     .cond (.reg 16) (.store (.reg 6) (.const 1)) .nop ;;
     .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1),
       .reg 6, .reg 7] ;;
     .ret (.reg 17))
    (.ret (.reg 7))

/-- Outer increasing-index scan (`i .. K - 1`), calling `inner` on `(i, i + 1 .. K - 1)`.
Arguments: `[treeHeap, L, pathsBase, K, i, flagPtr, work]`. -/
def cancelPairOuterBody (self inner : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 4) (.reg 3))
    (.call 7 inner [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 4) (.const 1),
       .reg 5, .reg 6] ;;
     .call 8 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1), .reg 5, .reg 7] ;;
     .ret (.reg 8))
    (.ret (.reg 6))

/-- Full cancellation loop (`[root, pathsBase, K, workHeap]`): runs `outer` with flag cell
`workHeap` and scratch starting at `workHeap + 1`; if any swap occurred (`mem[workHeap] ≠ 0`),
repeats from the returned `work1`, otherwise returns `work1`. -/
def cancelRoutePathsBody (self outer : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;; -- tok.handle
  .assign 5 (.load (.reg 4)) ;; -- tok.treeHeap
  .assign 6 (.load (.bin .add (.reg 4) (.const 5))) ;; -- L
  .store (.reg 3) (.const 0) ;; -- swapped flag := 0
  .call 7 outer [.reg 5, .reg 6, .reg 1, .reg 2, .const 0, .reg 3, .bin .add (.reg 3) (.const 1)] ;;
  .assign 8 (.load (.reg 3)) ;;
  .cond (.reg 8)
    (.call 9 self [.reg 0, .reg 1, .reg 2, .reg 7] ;; .ret (.reg 9))
    (.ret (.reg 7))

theorem cancelPairInnerBody_noRand (self opTree3 cmpExch : ℕ) :
    (cancelPairInnerBody self opTree3 cmpExch).NoRand := by
  simp [cancelPairInnerBody, Stmt.NoRand]

theorem cancelPairOuterBody_noRand (self inner : ℕ) :
    (cancelPairOuterBody self inner).NoRand := by
  simp [cancelPairOuterBody, Stmt.NoRand]

theorem cancelRoutePathsBody_noRand (self outer : ℕ) :
    (cancelRoutePathsBody self outer).NoRand := by
  simp [cancelRoutePathsBody, Stmt.NoRand]

/-! ## 2b. In-place `O(K^2)` opposite-pair edge cancellation (`cancelRouteEdgesLoopBody`) -/

/-- Scan `edgesBase[j .. len - 1]` for the first entry `(e, 1 - d)` opposite to `(e, d)`.
Returns its index `< len` if found, or `len` otherwise. Read-only (`0` memory writes).
Arguments: `[edgesBase, len, e, d, j]`. -/
def cancelEdgesFindOppBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 4) (.reg 1))
    (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
     .cond (.bin .eq (.reg 5) (.reg 2))
       (.cond (.bin .eq (.bin .add (.reg 6) (.reg 3)) (.const 1))
         (.ret (.reg 4))
         .nop)
       .nop ;;
     .call 7 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1)] ;;
     .ret (.reg 7))
    (.ret (.reg 1))

/-- In-place opposite-pair cancellation on `edgesBase[0 .. len - 1]` (`len = mem[descBase + 3]`):
at cursor `i`, searches `[i + 1 .. len - 1]` for an opposite-orientation duplicate of `edges[i]`;
if found at `j`, removes both slots `j` and `i` by swapping with the tail (`len := len - 2`,
storing `mem[descBase + 3] := len`) and re-checks `i`; otherwise advances `i := i + 1`.
Uses `0` scratch words and runs in `O(len^2)` steps.
Arguments: `[edgesBase, descBase, i]`. -/
def cancelRouteEdgesLoopBody (self findOpp : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .cond (.bin .lt (.reg 2) (.reg 3))
    (.assign 4 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2)))) ;;
     .assign 5 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))) (.const 1))) ;;
     .call 6 findOpp [.reg 0, .reg 3, .reg 4, .reg 5, .bin .add (.reg 2) (.const 1)] ;;
     .cond (.bin .lt (.reg 6) (.reg 3))
       (.assign 7 (.bin .sub (.reg 3) (.const 1)) ;;
        .cond (.bin .lt (.reg 6) (.reg 7))
          (.assign 8 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 7)))) ;;
           .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 7))) (.const 1))) ;;
           .store (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 6))) (.reg 8) ;;
           .store (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 6))) (.const 1)) (.reg 9))
          .nop ;;
        .assign 10 (.bin .sub (.reg 7) (.const 1)) ;;
        .cond (.bin .lt (.reg 2) (.reg 10))
          (.assign 8 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 10)))) ;;
           .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 10))) (.const 1))) ;;
           .store (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))) (.reg 8) ;;
           .store (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))) (.const 1)) (.reg 9))
          .nop ;;
        .store (.bin .add (.reg 1) (.const 3)) (.reg 10) ;;
        .call 11 self [.reg 0, .reg 1, .reg 2] ;;
        .ret (.const 0))
       (.call 11 self [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1)] ;;
        .ret (.const 0)))
    (.ret (.const 0))

theorem cancelEdgesFindOppBody_noRand (self : ℕ) : (cancelEdgesFindOppBody self).NoRand := by
  simp [cancelEdgesFindOppBody, Stmt.NoRand]

theorem cancelRouteEdgesLoopBody_noRand (self findOpp : ℕ) :
    (cancelRouteEdgesLoopBody self findOpp).NoRand := by
  simp [cancelRouteEdgesLoopBody, Stmt.NoRand]

/-- Combined cycle-route selector (`[root, descBase, workHeap]` with fixed heap handle `hb`
read from a constant). The solver uses `selectRouteBody` instead. -/
def selectRouteWithHeapBody (hb : ℕ) (rawProc cancelProc : ℕ) : Stmt :=
  .call 3 rawProc [.reg 0, .const hb, .reg 1, .reg 2] ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 4))) ;; -- pathsBase
  .assign 5 (.load (.bin .add (.reg 1) (.const 5))) ;; -- pathsLen
  .call 6 cancelProc [.reg 0, .reg 4, .reg 5, .reg 3] ;;
  .ret (.reg 6)

theorem selectRouteWithHeapBody_noRand (hb rawProc cancelProc : ℕ) :
    (selectRouteWithHeapBody hb rawProc cancelProc).NoRand := by
  simp [selectRouteWithHeapBody, Stmt.NoRand]

/-- Fixed-program cycle-route selector (`[root, descBase, workHeap]`): loads the select-heap
handle `hb` at runtime from `mem[tok.table + dMul * d + kOff]` (where `dMul` and `kOff` are
compile-time constants of the solver's metadata region), then calls `selectRawRoute`,
`cancelRouteEdges` (cancelling opposite-orientation off-tree edge pairs in place), and
`cancelRoutePaths`. One fixed program serves every runtime-allocated `SelectHeapLoc`. -/
def selectRouteBody (dMul kOff rawProc cancelEdgesProc cancelProc : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;; -- tok.handle
  .assign 8 (.load (.bin .add (.reg 7) (.const 11))) ;; -- d
  .assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;; -- tok.table
  .assign 10 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const dMul) (.reg 8))) (.const kOff))) ;; -- hb
  .call 3 rawProc [.reg 0, .reg 10, .reg 1, .reg 2] ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 2))) ;; -- edgesBase
  .call 12 cancelEdgesProc [.reg 11, .reg 1, .const 0] ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 4))) ;; -- pathsBase
  .assign 5 (.load (.bin .add (.reg 1) (.const 5))) ;; -- pathsLen
  .call 6 cancelProc [.reg 0, .reg 4, .reg 5, .reg 3] ;;
  .ret (.reg 6)

theorem selectRouteBody_noRand (dMul kOff rawProc cancelEdgesProc cancelProc : ℕ) :
    (selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc).NoRand := by
  simp [selectRouteBody, Stmt.NoRand]

/-! ## 3. Pure connectivity and cost-bound lemmas for cycle selection & cancellation -/

private noncomputable def projFrom (C : TreeChain) : ℕ → ℕ → ℕ
  | k, v =>
    if _ : k ≤ C.d then
      projFrom C (k + 1) ((C.activeLSF k).F.root v)
    else v
termination_by k => C.d + 1 - k

/-- Every edge of `C.G 0` has its endpoints connected in `C.chainTree` whenever `C.Holds` and
`C.LastLevelSpans`. -/
theorem chainTree_connected_of_mem_G0 {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    {e : ℕ} (he : e ∈ (C.G 0).E) :
    C.chainTree.Connected ((C.G 0).tail e) ((C.G 0).head e) := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hprojFrom_eq : ∀ j ≤ C.d + 1, ∀ v, projFrom C j (C.proj j v) = C.proj (C.d + 1) v := by
    intro j hj
    induction hrem : C.d + 1 - j generalizing j with
    | zero =>
      have hje : j = C.d + 1 := by omega
      subst hje; intro v; unfold projFrom; simp
    | succ m ih =>
      have hjle : j ≤ C.d := by omega
      intro v
      unfold projFrom; rw [dite_eq_left hjle]
      exact ih (j + 1) (by omega) (by omega) v
  have hconstEdge : ∀ rem, ∀ j ≤ C.d, C.d - j = rem →
      ∀ f ∈ (C.G j).E, projFrom C j ((C.G j).tail f) = projFrom C j ((C.G j).head f) := by
    intro rem
    induction rem with
    | zero =>
      intro j hj hrem f hf
      have hjd : j = C.d := by omega
      subst hjd
      have hEnds := C.G_isValid hH C.d le_rfl f hf
      have hconnG : (C.G C.d).Connected ((C.G C.d).tail f) ((C.G C.d).head f) :=
        ⟨[(f, true)], .cons hf rfl (.nil _)⟩
      have hconnF := hSpan _ hEnds.1 _ hEnds.2 hconnG
      have hRF := (C.activeLSF_holds hH le_rfl).2.1
      have hrootEq : (C.activeLSF C.d).F.root ((C.G C.d).tail f) =
          (C.activeLSF C.d).F.root ((C.G C.d).head f) :=
        root_eq_of_connected hRF hEnds.1 hEnds.2 hconnF
      unfold projFrom
      rw [dite_eq_left le_rfl, dite_eq_left le_rfl, hrootEq]
    | succ m ih =>
      intro j hj hrem f hf
      have hjlt : j < C.d := by omega
      have hEnds := C.G_isValid hH j hj f hf
      have hRF := (C.activeLSF_holds hH hj).2.1
      by_cases hfF : f ∈ (C.activeLSF j).F.F.E
      · have hFsub := (C.activeLSF_holds hH hj).2.1.2.2.2.2
        have hconnF : (C.activeLSF j).F.F.Connected ((C.G j).tail f) ((C.G j).head f) :=
          ⟨[(f, true)], .cons hfF (by simp [MGraph.src, (hFsub.2.2 f hfF).1])
            (by simpa [MGraph.dst, (hFsub.2.2 f hfF).2] using MGraph.IsWalk.nil ((C.G j).head f))⟩
        have hrootEq := root_eq_of_connected hRF hEnds.1 hEnds.2 hconnF
        unfold projFrom; rw [dite_eq_left hj, dite_eq_left hj, hrootEq]
      · have hfCore : f ∈ (C.activeCore j).E := Finset.mem_sdiff.mpr ⟨hf, hfF⟩
        have hEmbW : (C.G (j + 1)).IsWalk ((C.activeCore j).tail f) ((C.activeCore j).head f)
            (C.activeEmb j f) := by
          have h := (C.activeS_isSparsified hH hjlt).2.1.2 f hfCore
          rwa [C.activeS_eq_G_succ hH hjlt] at h
        have hwalkConst : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
            (C.G (j + 1)).IsWalk a b P → projFrom C (j + 1) a = projFrom C (j + 1) b := by
          intro a b P hW
          induction hW with
          | nil _ => rfl
          | @cons a c x rest he' hsrc _ ihW =>
            obtain ⟨e', dir⟩ := x
            have hstep := ih (j + 1) (by omega) (by omega) e' he'
            cases dir
            · simp only [MGraph.src, MGraph.dst] at hsrc ihW
              rw [← hsrc]; exact hstep.symm.trans ihW
            · simp only [MGraph.src, MGraph.dst] at hsrc ihW
              rw [← hsrc]; exact hstep.trans ihW
        have hEq1 := hwalkConst hEmbW
        simp only [TreeChain.activeCore, coreGraph] at hEq1
        unfold projFrom; rw [dite_eq_left hj, dite_eq_left hj]
        exact hEq1
  have hEnds0 := C.G_isValid hH 0 (Nat.zero_le _) e he
  have hProjEq : C.proj (C.d + 1) ((C.G 0).tail e) = C.proj (C.d + 1) ((C.G 0).head e) := by
    have h0 := hconstEdge C.d 0 (Nat.zero_le _) (by omega) e he
    simpa [TreeChain.proj] using (hprojFrom_eq 0 (Nat.zero_le _) _).symm.trans
      (h0.trans (hprojFrom_eq 0 (Nat.zero_le _) _))
  exact C.connected_chainTree_of_proj_eq hH hSub (C.d + 1) le_rfl _ hEnds0.1 _ hEnds0.2 hProjEq

/-- Every pair in `rawPathsOfWalk (C.G 0) C.chainTree W flip` has all endpoints in the same
connected component of `C.chainTree` whenever all steps of `W` lie in `(C.G 0).E` and all
`cycleSegments` stitches are connected in `C.chainTree`. -/
theorem rawPathsOfWalk_same_comp {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    {W : List (ℕ × Bool)} {flip : Bool}
    (hWE : ∀ x ∈ W, x.1 ∈ (C.G 0).E)
    (hStConn : ∀ q ∈ (cycleSegments (C.G 0) W).2, C.chainTree.Connected q.1 q.2) :
    ∀ p ∈ rawPathsOfWalk (C.G 0) C.chainTree W flip,
      ∀ q ∈ rawPathsOfWalk (C.G 0) C.chainTree W flip,
        C.chainTree.Connected p.1 q.1 := by
  cases W with
  | nil =>
    intro p hp
    unfold rawPathsOfWalk orientWalkSteps cycleSegments at hp
    cases flip <;> simp at hp
  | cons x0 rest =>
    set W' := x0 :: rest
    have hEdgeConn : ∀ x ∈ W', C.chainTree.Connected ((C.G 0).src x) ((C.G 0).dst x) := fun x hx => by
      have hc := chainTree_connected_of_mem_G0 hH hSpan (hWE x hx)
      cases hx2 : x.2
      · simpa [MGraph.src, MGraph.dst, hx2] using MGraph.connected_symm hc
      · simpa [MGraph.src, MGraph.dst, hx2] using hc
    have hAuxChain : ∀ (xs : List (ℕ × Bool)) (s0 : ℕ) (x : ℕ × Bool),
        (∀ y ∈ x :: xs, C.chainTree.Connected ((C.G 0).src y) ((C.G 0).dst y)) →
        (∀ q ∈ (cycleSegmentsAux (C.G 0) s0 x xs).2, C.chainTree.Connected q.1 q.2) →
        (∀ y ∈ x :: xs, C.chainTree.Connected ((C.G 0).src x) ((C.G 0).src y) ∧
            C.chainTree.Connected ((C.G 0).src x) ((C.G 0).dst y)) ∧
        (∀ q ∈ (cycleSegmentsAux (C.G 0) s0 x xs).2,
            C.chainTree.Connected ((C.G 0).src x) q.1 ∧
            C.chainTree.Connected ((C.G 0).src x) q.2) := by
      intro xs
      induction xs with
      | nil =>
        intro s0 x he hq
        have hx := he x List.mem_cons_self
        have hq0 : C.chainTree.Connected ((C.G 0).dst x) s0 :=
          hq ((C.G 0).dst x, s0) (by simp [cycleSegmentsAux])
        refine ⟨(fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hnil
          · exact ⟨MGraph.connected_refl _ _, hx⟩
          · cases hnil),
          (fun q hqm => by
            simp only [cycleSegmentsAux, List.mem_singleton] at hqm
            subst hqm
            exact ⟨hx, MGraph.connected_trans hx hq0⟩)⟩
      | cons y ys ih =>
        intro s0 x he hq
        have hx := he x List.mem_cons_self
        have hst : C.chainTree.Connected ((C.G 0).dst x) ((C.G 0).src y) :=
          hq ((C.G 0).dst x, (C.G 0).src y) (by simp [cycleSegmentsAux])
        have hxy : C.chainTree.Connected ((C.G 0).src x) ((C.G 0).src y) :=
          MGraph.connected_trans hx hst
        obtain ⟨ihV, ihQ⟩ := ih s0 y (fun z hz => he z (List.mem_cons_of_mem _ hz))
          (fun q hqm => hq q (by simp [cycleSegmentsAux, hqm]))
        refine ⟨fun z hz => ?_, fun q hqm => ?_⟩
        · rcases List.mem_cons.mp hz with rfl | hrest
          · exact ⟨MGraph.connected_refl _ _, hx⟩
          · exact ⟨MGraph.connected_trans hxy (ihV z hrest).1,
              MGraph.connected_trans hxy (ihV z hrest).2⟩
        · simp only [cycleSegmentsAux, List.mem_cons] at hqm
          rcases hqm with rfl | hrest
          · exact ⟨hx, hxy⟩
          · exact ⟨MGraph.connected_trans hxy (ihQ q hrest).1,
              MGraph.connected_trans hxy (ihQ q hrest).2⟩
    have hChain := hAuxChain rest ((C.G 0).src x0) x0 hEdgeConn (by simpa [cycleSegments, W'] using hStConn)
    have hAllComp : ∀ p ∈ rawPathsOfWalk (C.G 0) C.chainTree W' flip,
        C.chainTree.Connected ((C.G 0).src x0) p.1 := by
      intro p hp
      unfold rawPathsOfWalk at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
        have hyOr := (List.mem_filter.mp hy).1
        unfold orientWalkSteps at hyOr
        cases flip
        · simp only [Bool.false_eq_true, ↓reduceIte] at hyOr
          exact (hChain.1 y hyOr).1
        · simp only [↓reduceIte, List.mem_map] at hyOr
          obtain ⟨⟨ze, zd⟩, hz, rfl⟩ := hyOr
          have hsrcFlip : (C.G 0).src (ze, !zd) = (C.G 0).dst (ze, zd) := by cases zd <;> rfl
          rw [hsrcFlip]; exact (hChain.1 (ze, zd) hz).2
      · cases flip
        · simp only [Bool.false_eq_true, ↓reduceIte] at hp
          exact (hChain.2 p (by simpa [cycleSegments, W'] using hp)).1
        · simp only [↓reduceIte, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact (hChain.2 q (by simpa [cycleSegments, W'] using hq)).2
    intro p hp q hq
    exact MGraph.connected_trans (MGraph.connected_symm (hAllComp p hp)) (hAllComp q hq)

/-- Cancellation loop budget: at most `(4 * K^4 + 1) * K^2` pair comparisons, each doing 4
`opTree 3` (`PathSummary`) calls and 1 `pathCompareExchangeBody` call. -/
def cancelRoutePathsCost (K L treeBudget : ℕ) : ℕ :=
  (4 * K ^ 4 + 1) * (K * K * (4 * treeBudget + 117 * L + 440) + 120) + 40

/-- Cancellation loop space bound: at most `(4 * K^4 + 1) * K^2 * (4 * treeSpace + 2 * L)`. -/
def cancelRoutePathsSpace (K L treeSpace : ℕ) : ℕ :=
  (4 * K ^ 4 + 1) * (K * K * (4 * treeSpace + 2 * L) + 1)

/-- In-place opposite-pair edge-cancellation budget: `O(K^2)`. -/
def cancelRouteEdgesCost (K : ℕ) : ℕ :=
  50 * K * K + 150 * K + 20

/-- Combined `selectRouteBody` cost bound: raw query (`O(Lk + K)`), opposite-pair edge
cancellation (`O(K^2)`), and path cancellation (`O(K^6 · (treeBudget + L))`). -/
def selectRouteTotalCost (Lk K L treeBudget : ℕ) : ℕ :=
  selectRawRouteCost Lk K + cancelRouteEdgesCost K + cancelRoutePathsCost K L treeBudget + 150

/-- Combined `selectRouteBody` space bound. -/
def selectRouteTotalSpace (K L treeSpace : ℕ) : ℕ :=
  selectRawRouteSpace K + cancelRoutePathsSpace K L treeSpace

end MinCostFlow.MinRatio
