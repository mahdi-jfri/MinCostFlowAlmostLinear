module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.RouteBatch
public import MinCostFlow.ExpanderDecomp.RouteProgLayout
public import MinCostFlow.ExpanderDecomp.RouteProgCongr
public import MinCostFlow.ExpanderDecomp.RouteProgPairsBase
public import MinCostFlow.ExpanderDecomp.RouteProgShortPath
public import MinCostFlow.ExpanderDecomp.RouteProgBall
public import MinCostFlow.ExpanderDecomp.RouteProgResCsr

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Layout, Chunk Chains, Workspace Disjointness, and Sub-Statements (`RouteProgBatchBase`)

Provides all building blocks for the deterministic Word-RAM `runBatchProc` procedure:

1. **Chunk chains (`ChunkChainAt`)**: O(1) tail-appended linked list of non-empty `PathListAt`
   chunks stored in a dedicated `chunkHeap` disjoint from `pathHeap`, enabling FIFO accumulation
   `acc[i] ++ batchPaths[i]` across batches without mutating nodes inside `pathHeap`.
2. **Pure combinatorial lemmas**: `(V \ sp.remVerts).card ≤ sp.cost`, `batchRoutePairs_inv`
   (including `∑_i (A_i \ V_i).card ≤ br.cost` and `totalDemand remPairs + routedCount = totalDemand pairs`),
   `batchBallLoop_cost_add`, and `sort_sdiff_map_locOf`.
3. **Contiguous batch scratch layout (`ws`)**: places all 36 scratch sub-configs and arrays
   contiguously starting at `ws` (size `batchScratchSize nX m2 k`), giving one-line `omega` proofs
   of `SpDisj`, `BallDisj`, `ResCsrDisj`, and `CurBDisj`.
4. **Configuration block (`BatchCfg`, 26 words)**, write set (`BatchWriteSet`), output predicate
   (`BatchOutAt`), cost bound (`batchProgCost`), and verified sub-statements:
   - `batchMarkMatchedStmt` (walk `PathListAt`, stamp `matchAStamp`, clear `pairB`),
   - `batchCompactAStmt` (in-place compaction of `aData` slice),
   - `batchAppendChunkStmt` (O(1) chunk allocation & tail-link),
   - `batchFilterLiveStmt` (filter sorted slice against `liveStamp`),
   - `batchCopyBallStmt` (stamp `liveStamp` and append ball vertices to `cutList`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Chunk-Chain Representation for FIFO Multi-Batch Path Accumulation -/

/-- A singly-linked chain of non-empty path chunks `(head, tail)` in `[cLo, cHi)`, where each
chunk node at `ch` occupies 2 words `[pathHead, nextChunk]` with `PathListAt mem X pLo pHi pathHead ps`
and `ps ≠ []`. The accumulated path list is `chunks.flatten`. -/
def ChunkChainAt (mem : ℕ → ℕ) (X : Finset ℕ) (pLo pHi cLo cHi : ℕ) :
    ℕ → ℕ → List (List ((ℕ × ℕ) × List ℕ)) → Prop
  | head, tail, [] => head = 0 ∧ tail = 0
  | head, tail, [ps] =>
    head = tail ∧
    cLo ≤ head ∧ head + 2 ≤ cHi ∧ head ≠ 0 ∧
    ps ≠ [] ∧
    PathListAt mem X pLo pHi (mem head) ps ∧
    mem (head + 1) = 0
  | head, tail, ps :: qs :: rest =>
    cLo ≤ head ∧ head + 2 ≤ cHi ∧ head ≠ 0 ∧
    ps ≠ [] ∧
    PathListAt mem X pLo pHi (mem head) ps ∧
    head ≠ tail ∧
    head + 1 < tail + 1 ∧
    ChunkChainAt mem X pLo pHi cLo cHi (mem (head + 1)) tail (qs :: rest)

/-- List of 2-word chunk-node addresses along a `ChunkChainAt` of length `n`. -/
def chunkAddrs (mem : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | head, n + 1 => head :: chunkAddrs mem (mem (head + 1)) n

/-- Pairwise 2-word node disjointness across the `k` chunk chains stored at `accHeadAddr`,
parameterized by the chunk count `lens i` of each pair `i < k`. -/
def ChunksDisj (mem : ℕ → ℕ) (accHeadAddr k : ℕ) (lens : ℕ → ℕ) : Prop :=
  ∀ i < k, ∀ j < k, i ≠ j →
    ∀ a ∈ chunkAddrs mem (mem (accHeadAddr + i)) (lens i),
    ∀ b ∈ chunkAddrs mem (mem (accHeadAddr + j)) (lens j),
      a + 2 ≤ b ∨ b + 2 ≤ a

/-! ## 2. Contiguous Batch Scratch Workspace Layout -/

/-- Fixed offsets of all 36 scratch sub-configs and arrays inside `[ws, ws + batchScratchSize nX m2 k)`. -/
def wsSpCfg (ws : ℕ) : ℕ := ws
def wsBfsCfg (ws : ℕ) : ℕ := ws + 20
def wsDfsCfg (ws : ℕ) : ℕ := ws + 44
def wsBallCfg (ws : ℕ) : ℕ := ws + 76
def wsBfsBallCfg (ws : ℕ) : ℕ := ws + 100
def wsIsoStamp (ws : ℕ) : ℕ := ws + 124
def wsMatchAStamp (ws nX : ℕ) : ℕ := ws + 124 + nX
def wsVisStamp (ws nX : ℕ) : ℕ := ws + 124 + 2 * nX
def wsDist (ws nX : ℕ) : ℕ := ws + 124 + 3 * nX
def wsLayerOff (ws nX : ℕ) : ℕ := ws + 124 + 4 * nX
def wsLayerData (ws nX : ℕ) : ℕ := ws + 125 + 5 * nX
def wsTmpNxt (ws nX : ℕ) : ℕ := ws + 125 + 6 * nX
def wsCurStamp (ws nX : ℕ) : ℕ := ws + 125 + 7 * nX
def wsCurPtr (ws nX : ℕ) : ℕ := ws + 125 + 8 * nX
def wsUsedStamp (ws nX : ℕ) : ℕ := ws + 125 + 9 * nX
def wsDeadStamp (ws nX : ℕ) : ℕ := ws + 125 + 10 * nX
def wsStkVert (ws nX : ℕ) : ℕ := ws + 125 + 11 * nX
def wsStkEdge (ws nX : ℕ) : ℕ := ws + 125 + 12 * nX
def wsUsedList (ws nX : ℕ) : ℕ := ws + 125 + 13 * nX
def wsSBuf (ws nX : ℕ) : ℕ := ws + 125 + 14 * nX
def wsResOff (ws nX : ℕ) : ℕ := ws + 125 + 15 * nX
def wsResNb (ws nX : ℕ) : ℕ := ws + 126 + 16 * nX
def wsBOff (ws nX m2 : ℕ) : ℕ := ws + 126 + 16 * nX + m2
def wsBLen (ws nX m2 k : ℕ) : ℕ := ws + 127 + 16 * nX + m2 + k
def wsBData (ws nX m2 k : ℕ) : ℕ := ws + 127 + 16 * nX + m2 + 2 * k
def wsBCur (ws nX m2 k : ℕ) : ℕ := ws + 127 + 17 * nX + m2 + 2 * k
def wsLayerOffS (ws nX m2 k : ℕ) : ℕ := ws + 127 + 17 * nX + m2 + 3 * k
def wsLayerDataS (ws nX m2 k : ℕ) : ℕ := ws + 128 + 18 * nX + m2 + 3 * k
def wsLayerOffT (ws nX m2 k : ℕ) : ℕ := ws + 128 + 19 * nX + m2 + 3 * k
def wsLayerDataT (ws nX m2 k : ℕ) : ℕ := ws + 129 + 20 * nX + m2 + 3 * k
def wsBallStamp (ws nX m2 k : ℕ) : ℕ := ws + 129 + 21 * nX + m2 + 3 * k
def wsBallList (ws nX m2 k : ℕ) : ℕ := ws + 129 + 22 * nX + m2 + 3 * k
def wsLiveStamp (ws nX m2 k : ℕ) : ℕ := ws + 129 + 23 * nX + m2 + 3 * k
def wsSBallBuf (ws nX m2 k : ℕ) : ℕ := ws + 129 + 24 * nX + m2 + 3 * k
def wsTBallBuf (ws nX m2 k : ℕ) : ℕ := ws + 129 + 25 * nX + m2 + 3 * k
def wsCutList (ws nX m2 k : ℕ) : ℕ := ws + 129 + 26 * nX + m2 + 3 * k

/-- Total size of the contiguous batch scratch block `[ws, ws + batchScratchSize nX m2 k)`. -/
def batchScratchSize (nX m2 k : ℕ) : ℕ :=
  129 + 27 * nX + m2 + 3 * k

/-! ## 3. Batch Configuration Block, Sub-Configs, Write Set, and Disjointness -/

/-- 24-word input configuration block for `runBatchProc` at `cfgAddr + 0 .. cfgAddr + 23`.
In-out/output words reside at `cfgAddr + 16 .. cfgAddr + 25`. -/
structure BatchCfg where
  nX : ℕ
  k : ℕ
  d : ℕ
  b : ℕ
  Hbatch : ℕ
  offAddr : ℕ
  nbAddr : ℕ
  edgeAddr : ℕ
  pairBAddr : ℕ
  aOffAddr : ℕ
  aLenAddr : ℕ
  aDataAddr : ℕ
  accHeadAddr : ℕ
  accTailAddr : ℕ
  ws : ℕ
  m2 : ℕ
  curDemandIn : ℕ
  batchGenIn : ℕ
  bfsGenIn : ℕ
  dfsGenIn : ℕ
  ballGenIn : ℕ
  liveGenIn : ℕ
  pathHeapIn : ℕ
  chunkHeapIn : ℕ

/-- The 24 input words of `cfg` reside at `cfgAddr + 0 .. cfgAddr + 23`. -/
def BatchCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (cfg : BatchCfg) : Prop :=
  mem (cfgAddr + 0) = cfg.nX ∧
  mem (cfgAddr + 1) = cfg.k ∧
  mem (cfgAddr + 2) = cfg.d ∧
  mem (cfgAddr + 3) = cfg.b ∧
  mem (cfgAddr + 4) = cfg.Hbatch ∧
  mem (cfgAddr + 5) = cfg.offAddr ∧
  mem (cfgAddr + 6) = cfg.nbAddr ∧
  mem (cfgAddr + 7) = cfg.edgeAddr ∧
  mem (cfgAddr + 8) = cfg.pairBAddr ∧
  mem (cfgAddr + 9) = cfg.aOffAddr ∧
  mem (cfgAddr + 10) = cfg.aLenAddr ∧
  mem (cfgAddr + 11) = cfg.aDataAddr ∧
  mem (cfgAddr + 12) = cfg.accHeadAddr ∧
  mem (cfgAddr + 13) = cfg.accTailAddr ∧
  mem (cfgAddr + 14) = cfg.ws ∧
  mem (cfgAddr + 15) = cfg.m2 ∧
  mem (cfgAddr + 16) = cfg.curDemandIn ∧
  mem (cfgAddr + 17) = cfg.batchGenIn ∧
  mem (cfgAddr + 18) = cfg.bfsGenIn ∧
  mem (cfgAddr + 19) = cfg.dfsGenIn ∧
  mem (cfgAddr + 20) = cfg.ballGenIn ∧
  mem (cfgAddr + 21) = cfg.liveGenIn ∧
  mem (cfgAddr + 22) = cfg.pathHeapIn ∧
  mem (cfgAddr + 23) = cfg.chunkHeapIn

/-- Canonical `BfsCfg` for `shortPathBlock` inside `ws` for pair `stopVal` and generation `batchGen`. -/
def mkBatchSpBfsCfg (cfg : BatchCfg) (batchGen stopVal : ℕ) : BfsCfg where
  offAddr := cfg.offAddr
  nbAddr := cfg.nbAddr
  maskArrAddr := wsIsoStamp cfg.ws
  maskBadVal := batchGen
  hasStop := 1
  stopArrAddr := cfg.pairBAddr
  stopVal := stopVal
  visStampAddr := wsVisStamp cfg.ws cfg.nX
  distAddr := wsDist cfg.ws cfg.nX
  layerOffAddr := wsLayerOff cfg.ws cfg.nX
  layerDataAddr := wsLayerData cfg.ws cfg.nX
  tmpNxtAddr := wsTmpNxt cfg.ws cfg.nX
  bfsGen := 0
  maxDist := cfg.d
  initPtr := wsSBuf cfg.ws cfg.nX
  initLen := 0

/-- Canonical `DfsCfg` for `shortPathBlock` inside `ws`. -/
def mkBatchSpDfsCfg (cfg : BatchCfg) (batchGen stopVal : ℕ) : DfsCfg where
  offAddr := cfg.offAddr
  nbAddr := cfg.nbAddr
  edgeAddr := cfg.edgeAddr
  maskArrAddr := wsIsoStamp cfg.ws
  maskBadVal := batchGen
  stopArrAddr := cfg.pairBAddr
  stopVal := stopVal
  visStampAddr := wsVisStamp cfg.ws cfg.nX
  bfsGen := 0
  distAddr := wsDist cfg.ws cfg.nX
  curStampAddr := wsCurStamp cfg.ws cfg.nX
  curAddr := wsCurPtr cfg.ws cfg.nX
  usedStampAddr := wsUsedStamp cfg.ws cfg.nX
  deadStampAddr := wsDeadStamp cfg.ws cfg.nX
  stkVertAddr := wsStkVert cfg.ws cfg.nX
  stkEdgeAddr := wsStkEdge cfg.ws cfg.nX
  usedListAddr := wsUsedList cfg.ws cfg.nX
  dfsGen := 0
  targetDepth := 0
  srcPtr := wsSBuf cfg.ws cfg.nX
  srcLen := 0
  heapIn := 0
  inHead := 0
  inTail := 0

/-- Canonical `SpCfg` inside `ws`. -/
def mkBatchSpCfg (cfg : BatchCfg) (batchGen srcInPtr srcInLen bfsGen dfsGen heapIn : ℕ) : SpCfg where
  bfsCfgAddr := wsBfsCfg cfg.ws
  dfsCfgAddr := wsDfsCfg cfg.ws
  maskArrAddr := wsIsoStamp cfg.ws
  maskBadVal := batchGen
  usedListAddr := wsUsedList cfg.ws cfg.nX
  sBufAddr := wsSBuf cfg.ws cfg.nX
  srcInPtr := srcInPtr
  srcInLen := srcInLen
  d := cfg.d
  bfsGenIn := bfsGen
  dfsGenIn := dfsGen
  heapIn := heapIn

/-- Canonical `BfsCfg` for `growBall` inside `ws` (residual graph `resOff/resNb`, mask `liveStamp`). -/
def mkBatchBallBfsCfg (cfg : BatchCfg) (liveGen hL : ℕ) : BfsCfg where
  offAddr := wsResOff cfg.ws cfg.nX
  nbAddr := wsResNb cfg.ws cfg.nX
  maskArrAddr := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k
  maskBadVal := liveGen
  hasStop := 0
  stopArrAddr := 0
  stopVal := 0
  visStampAddr := wsVisStamp cfg.ws cfg.nX
  distAddr := wsDist cfg.ws cfg.nX
  layerOffAddr := 0
  layerDataAddr := 0
  tmpNxtAddr := wsTmpNxt cfg.ws cfg.nX
  bfsGen := 0
  maxDist := hL
  initPtr := 0
  initLen := 0

/-- Canonical `BallCfg` inside `ws`. -/
def mkBatchBallCfg (cfg : BatchCfg) (liveGen sLen tLen bfsGen ballGen : ℕ) : BallCfg where
  bfsCfgAddr := wsBfsBallCfg cfg.ws
  offAddr := wsResOff cfg.ws cfg.nX
  nbAddr := wsResNb cfg.ws cfg.nX
  maskArrAddr := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k
  maskBadVal := liveGen
  layerOffS := wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k
  layerDataS := wsLayerDataS cfg.ws cfg.nX cfg.m2 cfg.k
  layerOffT := wsLayerOffT cfg.ws cfg.nX cfg.m2 cfg.k
  layerDataT := wsLayerDataT cfg.ws cfg.nX cfg.m2 cfg.k
  sPtr := wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k
  sLen := sLen
  tPtr := wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k
  tLen := tLen
  ballStampAddr := wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k
  ballListAddr := wsBallList cfg.ws cfg.nX cfg.m2 cfg.k
  bfsGenIn := bfsGen
  ballGenIn := ballGen
  b := cfg.b

/-- Static sub-config words inside `ws` initialized once before `runBatchProc` runs. -/
def BatchSubCfgsInit (mem : ℕ → ℕ) (cfg : BatchCfg) (hL : ℕ) : Prop :=
  -- SpCfg static fields (0, 1, 2, 4, 5, 8)
  mem (wsSpCfg cfg.ws + 0) = wsBfsCfg cfg.ws ∧
  mem (wsSpCfg cfg.ws + 1) = wsDfsCfg cfg.ws ∧
  mem (wsSpCfg cfg.ws + 2) = wsIsoStamp cfg.ws ∧
  mem (wsSpCfg cfg.ws + 4) = wsUsedList cfg.ws cfg.nX ∧
  mem (wsSpCfg cfg.ws + 5) = wsSBuf cfg.ws cfg.nX ∧
  mem (wsSpCfg cfg.ws + 8) = cfg.d ∧
  -- BfsCfg (SP) static fields (0, 1, 2, 4, 5, 7, 8, 9, 10, 11, 13, 14)
  mem (wsBfsCfg cfg.ws + 0) = cfg.offAddr ∧
  mem (wsBfsCfg cfg.ws + 1) = cfg.nbAddr ∧
  mem (wsBfsCfg cfg.ws + 2) = wsIsoStamp cfg.ws ∧
  mem (wsBfsCfg cfg.ws + 4) = 1 ∧
  mem (wsBfsCfg cfg.ws + 5) = cfg.pairBAddr ∧
  mem (wsBfsCfg cfg.ws + 7) = wsVisStamp cfg.ws cfg.nX ∧
  mem (wsBfsCfg cfg.ws + 8) = wsDist cfg.ws cfg.nX ∧
  mem (wsBfsCfg cfg.ws + 9) = wsLayerOff cfg.ws cfg.nX ∧
  mem (wsBfsCfg cfg.ws + 10) = wsLayerData cfg.ws cfg.nX ∧
  mem (wsBfsCfg cfg.ws + 11) = wsTmpNxt cfg.ws cfg.nX ∧
  mem (wsBfsCfg cfg.ws + 13) = cfg.d ∧
  mem (wsBfsCfg cfg.ws + 14) = wsSBuf cfg.ws cfg.nX ∧
  -- DfsCfg (SP) static fields (0..3, 5, 7, 9..16, 19)
  mem (wsDfsCfg cfg.ws + 0) = cfg.offAddr ∧
  mem (wsDfsCfg cfg.ws + 1) = cfg.nbAddr ∧
  mem (wsDfsCfg cfg.ws + 2) = cfg.edgeAddr ∧
  mem (wsDfsCfg cfg.ws + 3) = wsIsoStamp cfg.ws ∧
  mem (wsDfsCfg cfg.ws + 5) = cfg.pairBAddr ∧
  mem (wsDfsCfg cfg.ws + 7) = wsVisStamp cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 9) = wsDist cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 10) = wsCurStamp cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 11) = wsCurPtr cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 12) = wsUsedStamp cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 13) = wsDeadStamp cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 14) = wsStkVert cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 15) = wsStkEdge cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 16) = wsUsedList cfg.ws cfg.nX ∧
  mem (wsDfsCfg cfg.ws + 19) = wsSBuf cfg.ws cfg.nX ∧
  -- BallCfg static fields (0..3, 5..9, 11, 13, 14, 17)
  mem (wsBallCfg cfg.ws + 0) = wsBfsBallCfg cfg.ws ∧
  mem (wsBallCfg cfg.ws + 1) = wsResOff cfg.ws cfg.nX ∧
  mem (wsBallCfg cfg.ws + 2) = wsResNb cfg.ws cfg.nX ∧
  mem (wsBallCfg cfg.ws + 3) = wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 5) = wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 6) = wsLayerDataS cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 7) = wsLayerOffT cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 8) = wsLayerDataT cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 9) = wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 11) = wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 13) = wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 14) = wsBallList cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBallCfg cfg.ws + 17) = cfg.b ∧
  -- BfsCfg (Ball) static fields (0..2, 4..8, 11, 13)
  mem (wsBfsBallCfg cfg.ws + 0) = wsResOff cfg.ws cfg.nX ∧
  mem (wsBfsBallCfg cfg.ws + 1) = wsResNb cfg.ws cfg.nX ∧
  mem (wsBfsBallCfg cfg.ws + 2) = wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ∧
  mem (wsBfsBallCfg cfg.ws + 4) = 0 ∧
  mem (wsBfsBallCfg cfg.ws + 5) = 0 ∧
  mem (wsBfsBallCfg cfg.ws + 6) = 0 ∧
  mem (wsBfsBallCfg cfg.ws + 7) = wsVisStamp cfg.ws cfg.nX ∧
  mem (wsBfsBallCfg cfg.ws + 8) = wsDist cfg.ws cfg.nX ∧
  mem (wsBfsBallCfg cfg.ws + 11) = wsTmpNxt cfg.ws cfg.nX ∧
  mem (wsBfsBallCfg cfg.ws + 13) = hL

/-- Addresses that `runBatchProc` may overwrite. -/
def BatchWriteSet (cfg : BatchCfg) (cfgAddr pathHeapLimit chunkHeapBase chunkHeapLimit : ℕ)
    (a : ℕ) : Prop :=
  (cfg.pairBAddr ≤ a ∧ a < cfg.pairBAddr + cfg.nX) ∨
  (cfg.aLenAddr ≤ a ∧ a < cfg.aLenAddr + cfg.k) ∨
  (cfg.aDataAddr ≤ a ∧ a < cfg.aDataAddr + cfg.nX) ∨
  (cfg.accHeadAddr ≤ a ∧ a < cfg.accHeadAddr + cfg.k) ∨
  (cfg.accTailAddr ≤ a ∧ a < cfg.accTailAddr + cfg.k) ∨
  (cfgAddr + 16 ≤ a ∧ a < cfgAddr + 26) ∨
  (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨
  (cfg.pathHeapIn ≤ a ∧ a < pathHeapLimit) ∨
  (chunkHeapBase ≤ a ∧ a < chunkHeapLimit)

/-- Region-level disjointness and word-size invariants for `runBatchProc`.
All 12 top-level memory regions are mutually disjoint, `pathHeap` has at least `15 * nX` words
of headroom (`5 * nX` allocated in the batch + `10 * nX` `shortPathBlock` safety margin), and
`chunkHeap` has at least `2 * nX` words of headroom. -/
structure BatchDisj (w cfgAddr pathHeapBase pathHeapLimit chunkHeapBase chunkHeapLimit hL : ℕ)
    (cfg : BatchCfg) : Prop where
  -- Path & chunk heap bounds (non-zero base so head ≠ 0)
  hp_pos : 0 < pathHeapBase
  hp_lo : pathHeapBase ≤ cfg.pathHeapIn
  hp_hi : cfg.pathHeapIn + 15 * cfg.nX ≤ pathHeapLimit
  ch_pos : 0 < chunkHeapBase
  ch_lo : chunkHeapBase ≤ cfg.chunkHeapIn
  ch_hi : cfg.chunkHeapIn + 2 * cfg.curDemandIn ≤ chunkHeapLimit
  -- Mutual disjointness of top-level regions:
  -- Read-only: off (nX+1), nb (m2), edge (m2), aOff (k+1)
  -- Mutable: pairB (nX), aLen (k), aData (nX), accHead (k), accTail (k), cfg (26), ws (S),
  --          pathHeap [pathHeapBase, pathHeapLimit), chunkHeap [chunkHeapBase, chunkHeapLimit)
  -- Simple ordering: every read-only region disjoint from all writable regions, and writable
  -- regions pairwise disjoint!
  ro_off_pb : DisjRange cfg.offAddr (cfg.nX + 1) cfg.pairBAddr cfg.nX
  ro_off_al : DisjRange cfg.offAddr (cfg.nX + 1) cfg.aLenAddr cfg.k
  ro_off_ad : DisjRange cfg.offAddr (cfg.nX + 1) cfg.aDataAddr cfg.nX
  ro_off_ah : DisjRange cfg.offAddr (cfg.nX + 1) cfg.accHeadAddr cfg.k
  ro_off_at : DisjRange cfg.offAddr (cfg.nX + 1) cfg.accTailAddr cfg.k
  ro_off_cfg : DisjRange cfg.offAddr (cfg.nX + 1) cfgAddr 26
  ro_off_ws : DisjRange cfg.offAddr (cfg.nX + 1) cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ro_off_hp : DisjRange cfg.offAddr (cfg.nX + 1) pathHeapBase (pathHeapLimit - pathHeapBase)
  ro_off_ch : DisjRange cfg.offAddr (cfg.nX + 1) chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ro_nb_pb : DisjRange cfg.nbAddr cfg.m2 cfg.pairBAddr cfg.nX
  ro_nb_al : DisjRange cfg.nbAddr cfg.m2 cfg.aLenAddr cfg.k
  ro_nb_ad : DisjRange cfg.nbAddr cfg.m2 cfg.aDataAddr cfg.nX
  ro_nb_ah : DisjRange cfg.nbAddr cfg.m2 cfg.accHeadAddr cfg.k
  ro_nb_at : DisjRange cfg.nbAddr cfg.m2 cfg.accTailAddr cfg.k
  ro_nb_cfg : DisjRange cfg.nbAddr cfg.m2 cfgAddr 26
  ro_nb_ws : DisjRange cfg.nbAddr cfg.m2 cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ro_nb_hp : DisjRange cfg.nbAddr cfg.m2 pathHeapBase (pathHeapLimit - pathHeapBase)
  ro_nb_ch : DisjRange cfg.nbAddr cfg.m2 chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ro_edge_pb : DisjRange cfg.edgeAddr cfg.m2 cfg.pairBAddr cfg.nX
  ro_edge_al : DisjRange cfg.edgeAddr cfg.m2 cfg.aLenAddr cfg.k
  ro_edge_ad : DisjRange cfg.edgeAddr cfg.m2 cfg.aDataAddr cfg.nX
  ro_edge_ah : DisjRange cfg.edgeAddr cfg.m2 cfg.accHeadAddr cfg.k
  ro_edge_at : DisjRange cfg.edgeAddr cfg.m2 cfg.accTailAddr cfg.k
  ro_edge_cfg : DisjRange cfg.edgeAddr cfg.m2 cfgAddr 26
  ro_edge_ws : DisjRange cfg.edgeAddr cfg.m2 cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ro_edge_hp : DisjRange cfg.edgeAddr cfg.m2 pathHeapBase (pathHeapLimit - pathHeapBase)
  ro_edge_ch : DisjRange cfg.edgeAddr cfg.m2 chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ro_ao_pb : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.pairBAddr cfg.nX
  ro_ao_al : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.aLenAddr cfg.k
  ro_ao_ad : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.aDataAddr cfg.nX
  ro_ao_ah : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.accHeadAddr cfg.k
  ro_ao_at : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.accTailAddr cfg.k
  ro_ao_cfg : DisjRange cfg.aOffAddr (cfg.k + 1) cfgAddr 26
  ro_ao_ws : DisjRange cfg.aOffAddr (cfg.k + 1) cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ro_ao_hp : DisjRange cfg.aOffAddr (cfg.k + 1) pathHeapBase (pathHeapLimit - pathHeapBase)
  ro_ao_ch : DisjRange cfg.aOffAddr (cfg.k + 1) chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  -- Writable regions pairwise disjoint
  pb_al : DisjRange cfg.pairBAddr cfg.nX cfg.aLenAddr cfg.k
  pb_ad : DisjRange cfg.pairBAddr cfg.nX cfg.aDataAddr cfg.nX
  pb_ah : DisjRange cfg.pairBAddr cfg.nX cfg.accHeadAddr cfg.k
  pb_at : DisjRange cfg.pairBAddr cfg.nX cfg.accTailAddr cfg.k
  pb_cfg : DisjRange cfg.pairBAddr cfg.nX cfgAddr 26
  pb_ws : DisjRange cfg.pairBAddr cfg.nX cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  pb_hp : DisjRange cfg.pairBAddr cfg.nX pathHeapBase (pathHeapLimit - pathHeapBase)
  pb_ch : DisjRange cfg.pairBAddr cfg.nX chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  al_ad : DisjRange cfg.aLenAddr cfg.k cfg.aDataAddr cfg.nX
  al_ah : DisjRange cfg.aLenAddr cfg.k cfg.accHeadAddr cfg.k
  al_at : DisjRange cfg.aLenAddr cfg.k cfg.accTailAddr cfg.k
  al_cfg : DisjRange cfg.aLenAddr cfg.k cfgAddr 26
  al_ws : DisjRange cfg.aLenAddr cfg.k cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  al_hp : DisjRange cfg.aLenAddr cfg.k pathHeapBase (pathHeapLimit - pathHeapBase)
  al_ch : DisjRange cfg.aLenAddr cfg.k chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ad_ah : DisjRange cfg.aDataAddr cfg.nX cfg.accHeadAddr cfg.k
  ad_at : DisjRange cfg.aDataAddr cfg.nX cfg.accTailAddr cfg.k
  ad_cfg : DisjRange cfg.aDataAddr cfg.nX cfgAddr 26
  ad_ws : DisjRange cfg.aDataAddr cfg.nX cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ad_hp : DisjRange cfg.aDataAddr cfg.nX pathHeapBase (pathHeapLimit - pathHeapBase)
  ad_ch : DisjRange cfg.aDataAddr cfg.nX chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ah_at : DisjRange cfg.accHeadAddr cfg.k cfg.accTailAddr cfg.k
  ah_cfg : DisjRange cfg.accHeadAddr cfg.k cfgAddr 26
  ah_ws : DisjRange cfg.accHeadAddr cfg.k cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  ah_hp : DisjRange cfg.accHeadAddr cfg.k pathHeapBase (pathHeapLimit - pathHeapBase)
  ah_ch : DisjRange cfg.accHeadAddr cfg.k chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  at_cfg : DisjRange cfg.accTailAddr cfg.k cfgAddr 26
  at_ws : DisjRange cfg.accTailAddr cfg.k cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  at_hp : DisjRange cfg.accTailAddr cfg.k pathHeapBase (pathHeapLimit - pathHeapBase)
  at_ch : DisjRange cfg.accTailAddr cfg.k chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  cfg_ws : DisjRange cfgAddr 26 cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k)
  cfg_hp : DisjRange cfgAddr 26 pathHeapBase (pathHeapLimit - pathHeapBase)
  cfg_ch : DisjRange cfgAddr 26 chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  ws_hp : DisjRange cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k) pathHeapBase (pathHeapLimit - pathHeapBase)
  ws_ch : DisjRange cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k) chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  hp_ch : DisjRange pathHeapBase (pathHeapLimit - pathHeapBase) chunkHeapBase (chunkHeapLimit - chunkHeapBase)
  -- Word-size bounds
  w_off : cfg.offAddr + cfg.nX + 5 < 2 ^ w
  w_nb : cfg.nbAddr + cfg.m2 + 5 < 2 ^ w
  w_edge : cfg.edgeAddr + cfg.m2 + 5 < 2 ^ w
  w_ao : cfg.aOffAddr + cfg.k + 5 < 2 ^ w
  w_pb : cfg.pairBAddr + cfg.nX + 5 < 2 ^ w
  w_al : cfg.aLenAddr + cfg.k + 5 < 2 ^ w
  w_ad : cfg.aDataAddr + cfg.nX + 5 < 2 ^ w
  w_ah : cfg.accHeadAddr + cfg.k + 5 < 2 ^ w
  w_at : cfg.accTailAddr + cfg.k + 5 < 2 ^ w
  w_cfg : cfgAddr + 30 < 2 ^ w
  w_ws : cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k + 10 < 2 ^ w
  w_hp : pathHeapLimit + 10 < 2 ^ w
  w_ch : chunkHeapLimit + 10 < 2 ^ w
  w_nX4 : 4 * cfg.nX + 5 < 2 ^ w
  w_m2 : cfg.m2 + 5 < 2 ^ w
  w_k : cfg.k + 5 < 2 ^ w
  w_d : cfg.d + 5 < 2 ^ w
  w_hL : hL + 5 < 2 ^ w
  w_Hbatch : cfg.nX * cfg.Hbatch + 5 < 2 ^ w
  w_Hbatch_s : cfg.Hbatch + 5 < 2 ^ w
  w_bgen : cfg.batchGenIn + 5 < 2 ^ w
  w_bfsgen : cfg.bfsGenIn + cfg.k * (cfg.d + 3) + cfg.d + 10 < 2 ^ w
  w_dfsgen : cfg.dfsGenIn + cfg.k * (cfg.d + 1) + cfg.d + 10 < 2 ^ w
  w_ballgen : cfg.ballGenIn + cfg.k + 10 < 2 ^ w
  w_livegen : cfg.liveGenIn + 5 < 2 ^ w
  w_mul : 16 * cfg.b * cfg.m2 + 5 < 2 ^ w
  w_b16 : 16 * cfg.b + 5 < 2 ^ w
  w_4 : 4 ≤ 2 ^ w

/-- Output predicate for `runBatchProc` matching `res = runBatch G X Δ b L pairs`. -/
def BatchOutAt (mem : ℕ → ℕ) (X : Finset ℕ) (cfg : BatchCfg)
    (cfgAddr pathHeapBase _pathHeapLimit chunkHeapBase chunkHeapLimit hL : ℕ)
    (accChunks : List (List (List ((ℕ × ℕ) × List ℕ))))
    (res : BatchResult) : Prop :=
  let outDemand := mem (cfgAddr + 16)
  let outBatchGen := mem (cfgAddr + 17)
  let outBfsGen := mem (cfgAddr + 18)
  let outDfsGen := mem (cfgAddr + 19)
  let outBallGen := mem (cfgAddr + 20)
  let outLiveGen := mem (cfgAddr + 21)
  let outPathHeap := mem (cfgAddr + 22)
  let outChunkHeap := mem (cfgAddr + 23)
  let outcome := mem (cfgAddr + 24)
  let cutSize := mem (cfgAddr + 25)
  outBatchGen = cfg.batchGenIn + 1 ∧
  cfg.bfsGenIn ≤ outBfsGen ∧ outBfsGen ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3) ∧
  cfg.dfsGenIn ≤ outDfsGen ∧ outDfsGen ≤ cfg.dfsGenIn + cfg.k * (cfg.d + 1) ∧
  cfg.ballGenIn ≤ outBallGen ∧ outBallGen ≤ cfg.ballGenIn + cfg.k ∧
  cfg.liveGenIn ≤ outLiveGen ∧ outLiveGen ≤ cfg.liveGenIn + 1 ∧
  cfg.pathHeapIn ≤ outPathHeap ∧ outPathHeap ≤ cfg.pathHeapIn + 5 * cfg.nX ∧
  outPathHeap ≤ cfg.pathHeapIn + 5 * res.cost ∧
  cfg.chunkHeapIn ≤ outChunkHeap ∧ outChunkHeap ≤ chunkHeapLimit ∧
  -- All stamp arrays stay bounded by their output generation counters
  (∀ v < X.card, mem (wsIsoStamp cfg.ws + v) ≤ outBatchGen) ∧
  (∀ v < X.card, mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ outBatchGen) ∧
  (∀ v < X.card, mem (wsVisStamp cfg.ws cfg.nX + v) ≤ outBfsGen) ∧
  (∀ v < X.card, mem (wsCurStamp cfg.ws cfg.nX + v) ≤ outDfsGen) ∧
  (∀ v < X.card, mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ outDfsGen) ∧
  (∀ v < X.card, mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ outDfsGen) ∧
  (∀ v < X.card, mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ outBallGen) ∧
  (∀ v < X.card, mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ outLiveGen) ∧
  -- Static sub-configs inside `ws` remain intact
  BatchSubCfgsInit mem cfg hL ∧
  -- Outcome-specific postcondition
  match res.outcome with
  | .matched batchPaths remPairs =>
    outcome = 0 ∧
    outDemand = totalDemand remPairs ∧
    outChunkHeap ≤ cfg.chunkHeapIn + 2 * batchPaths.flatten.length ∧
    LocalPairsAt mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X remPairs X.card ∧
    (∀ i (_hi : i < remPairs.length),
      let ch := accChunks.getD i []
      let bp := batchPaths.getD i []
      let newCh := if bp = [] then ch else ch ++ [bp]
      ChunkChainAt mem X pathHeapBase outPathHeap chunkHeapBase outChunkHeap
        (mem (cfg.accHeadAddr + i)) (mem (cfg.accTailAddr + i)) newCh) ∧
    ChunksDisj mem cfg.accHeadAddr remPairs.length
      (fun i => (if batchPaths.getD i [] = [] then accChunks.getD i []
                 else accChunks.getD i [] ++ [batchPaths.getD i []]).length)
  | .cut U =>
    outcome = 1 ∧
    cutSize = U.card ∧
    ∃ ul : List ℕ, ul.length = U.card ∧ ul.Nodup ∧
      (∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U) ∧
      (∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul) ∧
      ListAt mem (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k) ul

/-- Step bound for `runBatchProc`: `1500 * br.cost + 500`. -/
def batchProgCost (modelCost : ℕ) : ℕ :=
  1500 * modelCost + 500


end MinCostFlow.ExpanderDecomp
