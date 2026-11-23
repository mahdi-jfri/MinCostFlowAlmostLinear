module

public import MinCostFlow.ExpanderDecomp.RouteProgBatch
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.RouteOrCut

import Mathlib.Tactic.Ring

/-!
# Outer Batch-Loop Procedure Layout and Statements (`RouteProgLoopBase`)

Fixes the configuration record, disjointness bundle, write set, and deterministic Word-RAM
statements for Procedure 5 (`routeOrCutCsrProc`), implementing `routeOrCut`
on a prebuilt local CSR `AdjCsrAt` and local terminal pairs `LocalPairsAt`:
- `RouteLoopCfg`, `RouteLoopCfgAt`: 32-word configuration block extending `BatchCfg`
  (`cfgAddr + 0 .. 25`) with 6 read-only fields (`R`, `z`, `hL`, `origVertAddr`, `outAddr`,
  `walksAddr`) at `cfgAddr + 26 .. 31`.
- `RouteLoopWriteSet`, `RouteLoopDisj`: region disjointness and word-size bounds across all
  `R` batches, plus `RouteLoopDisj.toBatchDisj`.
- `initBatchSubCfgsStmt`: initializes all 56 static sub-configuration words (`BatchSubCfgsInit`)
  inside `ws[0 .. 123]` in `O(1)` time.
- `routeBatchesLoopStmt`: runs up to `R` batches of `runBatchProc`, stopping early once
  `curDemand ≤ z` or a batch returns a cut (`tag = 1`).
- `emitCutStmt` and `emitMatchedStmt`: serialize the resulting `RouteOutAt` at `outAddr`
  (translating local vertex IDs via `origVertAddr`) and, when matched, `WalksAt` at `walksAddr`.
- `routeOrCutCsrProc`, `routeOrCutCsrProc_noRand`: full deterministic procedure with `O(1)`
  early exit when `curDemand ≤ z ∨ R = 0`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Configuration Block, Write Set, and Disjointness -/

/-- Full 32-word configuration for `routeOrCutCsrProc`: `BatchCfg` at `cfgAddr + 0 .. 25` plus
6 read-only outer-loop fields at `cfgAddr + 26 .. 31`. -/
structure RouteLoopCfg where
  batch : BatchCfg
  R : ℕ
  z : ℕ
  hL : ℕ
  origVertAddr : ℕ
  outAddr : ℕ
  walksAddr : ℕ

/-- The 32 configuration words of `rcfg` reside at `cfgAddr + 0 .. cfgAddr + 31`
(with `cfgAddr + 24, 25` reserved for batch outputs `outcomeTag, cutSize`). -/
def RouteLoopCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (rcfg : RouteLoopCfg) : Prop :=
  BatchCfgAt mem cfgAddr rcfg.batch ∧
  mem (cfgAddr + 26) = rcfg.R ∧
  mem (cfgAddr + 27) = rcfg.z ∧
  mem (cfgAddr + 28) = rcfg.hL ∧
  mem (cfgAddr + 29) = rcfg.origVertAddr ∧
  mem (cfgAddr + 30) = rcfg.outAddr ∧
  mem (cfgAddr + 31) = rcfg.walksAddr

/-- Combined write set of `routeOrCutCsrProc`: `BatchWriteSet` plus `[outAddr, outAddr + 2 + 2*nX)`
and `[walksAddr, walksAddr + 1 + nX)`. -/
def RouteLoopWriteSet (rcfg : RouteLoopCfg) (cfgAddr pHi cLo cHi : ℕ) (a : ℕ) : Prop :=
  BatchWriteSet rcfg.batch cfgAddr pHi cLo cHi a ∨
  (rcfg.outAddr ≤ a ∧ a < rcfg.outAddr + 2 + 2 * rcfg.batch.nX) ∨
  (rcfg.walksAddr ≤ a ∧ a < rcfg.walksAddr + 1 + rcfg.batch.nX)

/-- Region disjointness and word-size bounds for `routeOrCutCsrProc` across up to `R` batches. -/
structure RouteLoopDisj (w cfgAddr pLo pHi cLo cHi : ℕ) (rcfg : RouteLoopCfg) : Prop where
  hp_pos : 0 < pLo
  hp_lo : pLo ≤ rcfg.batch.pathHeapIn
  ch_pos : 0 < cLo
  ch_lo : cLo ≤ rcfg.batch.chunkHeapIn
  ch_hi : rcfg.batch.chunkHeapIn + 2 * rcfg.batch.curDemandIn ≤ cHi
  -- Read-only CSR/aOff vs mutable regions
  ro_off_pb : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.pairBAddr rcfg.batch.nX
  ro_off_al : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.aLenAddr rcfg.batch.k
  ro_off_ad : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.aDataAddr rcfg.batch.nX
  ro_off_ah : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.accHeadAddr rcfg.batch.k
  ro_off_at : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.accTailAddr rcfg.batch.k
  ro_off_cfg : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) cfgAddr 32
  ro_off_ws : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ro_off_hp : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) pLo (pHi - pLo)
  ro_off_ch : DisjRange rcfg.batch.offAddr (rcfg.batch.nX + 1) cLo (cHi - cLo)
  ro_nb_pb : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.pairBAddr rcfg.batch.nX
  ro_nb_al : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.aLenAddr rcfg.batch.k
  ro_nb_ad : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.aDataAddr rcfg.batch.nX
  ro_nb_ah : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.accHeadAddr rcfg.batch.k
  ro_nb_at : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.accTailAddr rcfg.batch.k
  ro_nb_cfg : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 cfgAddr 32
  ro_nb_ws : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ro_nb_hp : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 pLo (pHi - pLo)
  ro_nb_ch : DisjRange rcfg.batch.nbAddr rcfg.batch.m2 cLo (cHi - cLo)
  ro_edge_pb : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.pairBAddr rcfg.batch.nX
  ro_edge_al : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.aLenAddr rcfg.batch.k
  ro_edge_ad : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.aDataAddr rcfg.batch.nX
  ro_edge_ah : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.accHeadAddr rcfg.batch.k
  ro_edge_at : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.accTailAddr rcfg.batch.k
  ro_edge_cfg : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 cfgAddr 32
  ro_edge_ws : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ro_edge_hp : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 pLo (pHi - pLo)
  ro_edge_ch : DisjRange rcfg.batch.edgeAddr rcfg.batch.m2 cLo (cHi - cLo)
  ro_ao_pb : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.pairBAddr rcfg.batch.nX
  ro_ao_al : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.aLenAddr rcfg.batch.k
  ro_ao_ad : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.aDataAddr rcfg.batch.nX
  ro_ao_ah : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.accHeadAddr rcfg.batch.k
  ro_ao_at : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.accTailAddr rcfg.batch.k
  ro_ao_cfg : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) cfgAddr 32
  ro_ao_ws : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ro_ao_hp : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) pLo (pHi - pLo)
  ro_ao_ch : DisjRange rcfg.batch.aOffAddr (rcfg.batch.k + 1) cLo (cHi - cLo)
  -- Mutual disjointness among mutable batch regions
  pb_al : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX rcfg.batch.aLenAddr rcfg.batch.k
  pb_ad : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX rcfg.batch.aDataAddr rcfg.batch.nX
  pb_ah : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX rcfg.batch.accHeadAddr rcfg.batch.k
  pb_at : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX rcfg.batch.accTailAddr rcfg.batch.k
  pb_cfg : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX cfgAddr 32
  pb_ws : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  pb_hp : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX pLo (pHi - pLo)
  pb_ch : DisjRange rcfg.batch.pairBAddr rcfg.batch.nX cLo (cHi - cLo)
  al_ad : DisjRange rcfg.batch.aLenAddr rcfg.batch.k rcfg.batch.aDataAddr rcfg.batch.nX
  al_ah : DisjRange rcfg.batch.aLenAddr rcfg.batch.k rcfg.batch.accHeadAddr rcfg.batch.k
  al_at : DisjRange rcfg.batch.aLenAddr rcfg.batch.k rcfg.batch.accTailAddr rcfg.batch.k
  al_cfg : DisjRange rcfg.batch.aLenAddr rcfg.batch.k cfgAddr 32
  al_ws : DisjRange rcfg.batch.aLenAddr rcfg.batch.k rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  al_hp : DisjRange rcfg.batch.aLenAddr rcfg.batch.k pLo (pHi - pLo)
  al_ch : DisjRange rcfg.batch.aLenAddr rcfg.batch.k cLo (cHi - cLo)
  ad_ah : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX rcfg.batch.accHeadAddr rcfg.batch.k
  ad_at : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX rcfg.batch.accTailAddr rcfg.batch.k
  ad_cfg : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX cfgAddr 32
  ad_ws : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ad_hp : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX pLo (pHi - pLo)
  ad_ch : DisjRange rcfg.batch.aDataAddr rcfg.batch.nX cLo (cHi - cLo)
  ah_at : DisjRange rcfg.batch.accHeadAddr rcfg.batch.k rcfg.batch.accTailAddr rcfg.batch.k
  ah_cfg : DisjRange rcfg.batch.accHeadAddr rcfg.batch.k cfgAddr 32
  ah_ws : DisjRange rcfg.batch.accHeadAddr rcfg.batch.k rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  ah_hp : DisjRange rcfg.batch.accHeadAddr rcfg.batch.k pLo (pHi - pLo)
  ah_ch : DisjRange rcfg.batch.accHeadAddr rcfg.batch.k cLo (cHi - cLo)
  at_cfg : DisjRange rcfg.batch.accTailAddr rcfg.batch.k cfgAddr 32
  at_ws : DisjRange rcfg.batch.accTailAddr rcfg.batch.k rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  at_hp : DisjRange rcfg.batch.accTailAddr rcfg.batch.k pLo (pHi - pLo)
  at_ch : DisjRange rcfg.batch.accTailAddr rcfg.batch.k cLo (cHi - cLo)
  cfg_ws : DisjRange cfgAddr 32 rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  cfg_hp : DisjRange cfgAddr 32 pLo (pHi - pLo)
  cfg_ch : DisjRange cfgAddr 32 cLo (cHi - cLo)
  ws_hp : DisjRange rcfg.batch.ws (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
    pLo (pHi - pLo)
  ws_ch : DisjRange rcfg.batch.ws (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
    cLo (cHi - cLo)
  hp_ch : DisjRange pLo (pHi - pLo) cLo (cHi - cLo)
  -- Extra outer-loop regions: origVert, outAddr, walksAddr
  orig_pb : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.pairBAddr rcfg.batch.nX
  orig_al : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.aLenAddr rcfg.batch.k
  orig_ad : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.aDataAddr rcfg.batch.nX
  orig_ah : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.accHeadAddr rcfg.batch.k
  orig_at : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.accTailAddr rcfg.batch.k
  orig_cfg : DisjRange rcfg.origVertAddr rcfg.batch.nX cfgAddr 32
  orig_ws : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  orig_hp : DisjRange rcfg.origVertAddr rcfg.batch.nX pLo (pHi - pLo)
  orig_ch : DisjRange rcfg.origVertAddr rcfg.batch.nX cLo (cHi - cLo)
  orig_out : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.outAddr (2 + 2 * rcfg.batch.nX)
  orig_walks : DisjRange rcfg.origVertAddr rcfg.batch.nX rcfg.walksAddr (1 + rcfg.batch.nX)
  out_ah : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) rcfg.batch.accHeadAddr rcfg.batch.k
  out_cfg : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) cfgAddr 32
  out_ws : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  out_hp : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) pLo (pHi - pLo)
  out_ch : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) cLo (cHi - cLo)
  out_walks : DisjRange rcfg.outAddr (2 + 2 * rcfg.batch.nX) rcfg.walksAddr (1 + rcfg.batch.nX)
  walks_ah : DisjRange rcfg.walksAddr (1 + rcfg.batch.nX) rcfg.batch.accHeadAddr rcfg.batch.k
  walks_cfg : DisjRange rcfg.walksAddr (1 + rcfg.batch.nX) cfgAddr 32
  walks_ws : DisjRange rcfg.walksAddr (1 + rcfg.batch.nX) rcfg.batch.ws
    (batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k)
  walks_hp : DisjRange rcfg.walksAddr (1 + rcfg.batch.nX) pLo (pHi - pLo)
  walks_ch : DisjRange rcfg.walksAddr (1 + rcfg.batch.nX) cLo (cHi - cLo)
  -- Word-size bounds across all R batches
  w_off : rcfg.batch.offAddr + rcfg.batch.nX + 5 < 2 ^ w
  w_nb : rcfg.batch.nbAddr + rcfg.batch.m2 + 5 < 2 ^ w
  w_edge : rcfg.batch.edgeAddr + rcfg.batch.m2 + 5 < 2 ^ w
  w_pb : rcfg.batch.pairBAddr + rcfg.batch.nX + 5 < 2 ^ w
  w_ao : rcfg.batch.aOffAddr + rcfg.batch.k + 5 < 2 ^ w
  w_al : rcfg.batch.aLenAddr + rcfg.batch.k + 5 < 2 ^ w
  w_ad : rcfg.batch.aDataAddr + rcfg.batch.nX + 5 < 2 ^ w
  w_ah : rcfg.batch.accHeadAddr + rcfg.batch.k + 5 < 2 ^ w
  w_at : rcfg.batch.accTailAddr + rcfg.batch.k + 5 < 2 ^ w
  w_cfg : cfgAddr + 36 < 2 ^ w
  w_ws : rcfg.batch.ws + batchScratchSize rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + 10 < 2 ^ w
  w_hp : pHi + 10 < 2 ^ w
  w_ch : cHi + 10 < 2 ^ w
  w_orig : rcfg.origVertAddr + rcfg.batch.nX + 5 < 2 ^ w
  w_out : rcfg.outAddr + 2 + 2 * rcfg.batch.nX + 5 < 2 ^ w
  w_walks : rcfg.walksAddr + 1 + rcfg.batch.nX + 5 < 2 ^ w
  w_bgen : rcfg.batch.batchGenIn + rcfg.R + 5 < 2 ^ w
  w_bfsgen : rcfg.batch.bfsGenIn + rcfg.R * (rcfg.batch.k * (rcfg.batch.d + 3)) + rcfg.batch.d + 10 < 2 ^ w
  w_dfsgen : rcfg.batch.dfsGenIn + rcfg.R * (rcfg.batch.k * (rcfg.batch.d + 1)) + rcfg.batch.d + 10 < 2 ^ w
  w_ballgen : rcfg.batch.ballGenIn + rcfg.R * rcfg.batch.k + 10 < 2 ^ w
  w_livegen : rcfg.batch.liveGenIn + rcfg.R + 5 < 2 ^ w
  w_hL : rcfg.hL + 5 < 2 ^ w
  w_d : rcfg.batch.d + 5 < 2 ^ w
  w_m2 : rcfg.batch.m2 + 5 < 2 ^ w
  w_k : rcfg.batch.k + 5 < 2 ^ w
  w_Hbatch : rcfg.batch.nX * rcfg.batch.Hbatch + 5 < 2 ^ w
  w_Hbatch_s : rcfg.batch.Hbatch + 5 < 2 ^ w
  w_mul : 16 * rcfg.batch.b * rcfg.batch.m2 + 5 < 2 ^ w
  w_b16 : 16 * rcfg.batch.b + 5 < 2 ^ w
  w_nX4 : 4 * rcfg.batch.nX + 5 < 2 ^ w
  w_R : rcfg.R + 5 < 2 ^ w
  w_z : rcfg.z + 5 < 2 ^ w
  w_4 : 4 ≤ 2 ^ w

private lemma disj_shrink_r {a1 l1 a2 l2 l2' : ℕ} (h : DisjRange a1 l1 a2 l2) (hle : l2' ≤ l2) :
    DisjRange a1 l1 a2 l2' := by
  unfold DisjRange at h ⊢; omega

private lemma disj_shrink_l {a1 l1 l1' a2 l2 : ℕ} (h : DisjRange a1 l1 a2 l2) (hle : l1' ≤ l1) :
    DisjRange a1 l1' a2 l2 := by
  unfold DisjRange at h ⊢; omega

/-- Build a `BatchDisj` for an updated mutable state at batch step `t < R`. -/
lemma RouteLoopDisj.toBatchDisj {w cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (h : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {t curDem batchGen bfsGen dfsGen ballGen liveGen pathHeap chunkHeap : ℕ}
    (ht : t < rcfg.R)
    (hp_lo : pLo ≤ pathHeap) (hp_hi : pathHeap + 15 * rcfg.batch.nX ≤ pHi)
    (hc_lo : cLo ≤ chunkHeap) (hc_hi : chunkHeap + 2 * curDem ≤ cHi)
    (hbg : batchGen ≤ rcfg.batch.batchGenIn + t)
    (hbfs : bfsGen ≤ rcfg.batch.bfsGenIn + t * (rcfg.batch.k * (rcfg.batch.d + 3)))
    (hdfs : dfsGen ≤ rcfg.batch.dfsGenIn + t * (rcfg.batch.k * (rcfg.batch.d + 1)))
    (hball : ballGen ≤ rcfg.batch.ballGenIn + t * rcfg.batch.k)
    (hlive : liveGen ≤ rcfg.batch.liveGenIn + t) :
    BatchDisj w cfgAddr pLo pHi cLo cHi rcfg.hL
      { rcfg.batch with
        curDemandIn := curDem
        batchGenIn := batchGen
        bfsGenIn := bfsGen
        dfsGenIn := dfsGen
        ballGenIn := ballGen
        liveGenIn := liveGen
        pathHeapIn := pathHeap
        chunkHeapIn := chunkHeap } := by
  have ht1 : t + 1 ≤ rcfg.R := ht
  have h1 : (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 3)) ≤
      rcfg.R * (rcfg.batch.k * (rcfg.batch.d + 3)) := Nat.mul_le_mul_right _ ht1
  have h2 : (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 1)) ≤
      rcfg.R * (rcfg.batch.k * (rcfg.batch.d + 1)) := Nat.mul_le_mul_right _ ht1
  have h3 : (t + 1) * rcfg.batch.k ≤ rcfg.R * rcfg.batch.k := Nat.mul_le_mul_right _ ht1
  have h1' : t * (rcfg.batch.k * (rcfg.batch.d + 3)) + rcfg.batch.k * (rcfg.batch.d + 3) =
      (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 3)) := by ring
  have h2' : t * (rcfg.batch.k * (rcfg.batch.d + 1)) + rcfg.batch.k * (rcfg.batch.d + 1) =
      (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 1)) := by ring
  have h3' : t * rcfg.batch.k + rcfg.batch.k = (t + 1) * rcfg.batch.k := by ring
  exact
    { hp_pos := h.hp_pos, hp_lo := hp_lo, hp_hi := hp_hi,
      ch_pos := h.ch_pos, ch_lo := hc_lo, ch_hi := hc_hi,
      ro_off_pb := h.ro_off_pb, ro_off_al := h.ro_off_al, ro_off_ad := h.ro_off_ad,
      ro_off_ah := h.ro_off_ah, ro_off_at := h.ro_off_at,
      ro_off_cfg := disj_shrink_r h.ro_off_cfg (by decide),
      ro_off_ws := h.ro_off_ws, ro_off_hp := h.ro_off_hp, ro_off_ch := h.ro_off_ch,
      ro_nb_pb := h.ro_nb_pb, ro_nb_al := h.ro_nb_al, ro_nb_ad := h.ro_nb_ad,
      ro_nb_ah := h.ro_nb_ah, ro_nb_at := h.ro_nb_at,
      ro_nb_cfg := disj_shrink_r h.ro_nb_cfg (by decide),
      ro_nb_ws := h.ro_nb_ws, ro_nb_hp := h.ro_nb_hp, ro_nb_ch := h.ro_nb_ch,
      ro_edge_pb := h.ro_edge_pb, ro_edge_al := h.ro_edge_al, ro_edge_ad := h.ro_edge_ad,
      ro_edge_ah := h.ro_edge_ah, ro_edge_at := h.ro_edge_at,
      ro_edge_cfg := disj_shrink_r h.ro_edge_cfg (by decide),
      ro_edge_ws := h.ro_edge_ws, ro_edge_hp := h.ro_edge_hp, ro_edge_ch := h.ro_edge_ch,
      ro_ao_pb := h.ro_ao_pb, ro_ao_al := h.ro_ao_al, ro_ao_ad := h.ro_ao_ad,
      ro_ao_ah := h.ro_ao_ah, ro_ao_at := h.ro_ao_at,
      ro_ao_cfg := disj_shrink_r h.ro_ao_cfg (by decide),
      ro_ao_ws := h.ro_ao_ws, ro_ao_hp := h.ro_ao_hp, ro_ao_ch := h.ro_ao_ch,
      pb_al := h.pb_al, pb_ad := h.pb_ad, pb_ah := h.pb_ah, pb_at := h.pb_at,
      pb_cfg := disj_shrink_r h.pb_cfg (by decide),
      pb_ws := h.pb_ws, pb_hp := h.pb_hp, pb_ch := h.pb_ch,
      al_ad := h.al_ad, al_ah := h.al_ah, al_at := h.al_at,
      al_cfg := disj_shrink_r h.al_cfg (by decide),
      al_ws := h.al_ws, al_hp := h.al_hp, al_ch := h.al_ch,
      ad_ah := h.ad_ah, ad_at := h.ad_at,
      ad_cfg := disj_shrink_r h.ad_cfg (by decide),
      ad_ws := h.ad_ws, ad_hp := h.ad_hp, ad_ch := h.ad_ch,
      ah_at := h.ah_at, ah_cfg := disj_shrink_r h.ah_cfg (by decide),
      ah_ws := h.ah_ws, ah_hp := h.ah_hp, ah_ch := h.ah_ch,
      at_cfg := disj_shrink_r h.at_cfg (by decide),
      at_ws := h.at_ws, at_hp := h.at_hp, at_ch := h.at_ch,
      cfg_ws := disj_shrink_l h.cfg_ws (by decide),
      cfg_hp := disj_shrink_l h.cfg_hp (by decide),
      cfg_ch := disj_shrink_l h.cfg_ch (by decide),
      ws_hp := h.ws_hp, ws_ch := h.ws_ch, hp_ch := h.hp_ch,
      w_off := h.w_off, w_nb := h.w_nb, w_edge := h.w_edge, w_pb := h.w_pb,
      w_ao := h.w_ao, w_al := h.w_al, w_ad := h.w_ad, w_ah := h.w_ah, w_at := h.w_at,
      w_cfg := by have := h.w_cfg; omega,
      w_ws := h.w_ws, w_hp := h.w_hp, w_ch := h.w_ch,
      w_nX4 := h.w_nX4, w_m2 := h.w_m2, w_k := h.w_k, w_d := h.w_d, w_hL := h.w_hL,
      w_Hbatch := h.w_Hbatch, w_Hbatch_s := h.w_Hbatch_s,
      w_bgen := by dsimp only; have := h.w_bgen; omega,
      w_bfsgen := by dsimp only; have := h.w_bfsgen; omega,
      w_dfsgen := by dsimp only; have := h.w_dfsgen; omega,
      w_ballgen := by dsimp only; have := h.w_ballgen; omega,
      w_livegen := by dsimp only; have := h.w_livegen; omega,
      w_mul := h.w_mul, w_b16 := h.w_b16, w_4 := h.w_4 }

/-! ## 2. Deterministic Word-RAM Statements for Procedure 5 -/

/-- Load static fields and compute scratch sub-array addresses into registers `1 .. 30`.
Expects `reg 0 = cfgAddr`. -/
def initSubCfgsLoadStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))   -- nX
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))   -- k
    , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))   -- d
    , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))   -- b
    , .assign 5 (.load (.bin .add (.reg 0) (.const 5)))   -- offAddr
    , .assign 6 (.load (.bin .add (.reg 0) (.const 6)))   -- nbAddr
    , .assign 7 (.load (.bin .add (.reg 0) (.const 7)))   -- edgeAddr
    , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))   -- pairBAddr
    , .assign 9 (.load (.bin .add (.reg 0) (.const 14)))  -- ws
    , .assign 10 (.load (.bin .add (.reg 0) (.const 15))) -- m2
    , .assign 11 (.load (.bin .add (.reg 0) (.const 28))) -- hL
    , .assign 12 (.bin .add (.reg 9) (.const 124))                                       -- wsIsoStamp
    , .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1)))                   -- wsVisStamp
    , .assign 14 (.bin .add (.reg 13) (.reg 1))                                          -- wsDist
    , .assign 15 (.bin .add (.reg 14) (.reg 1))                                          -- wsLayerOff
    , .assign 16 (.bin .add (.bin .add (.reg 15) (.reg 1)) (.const 1))                   -- wsLayerData
    , .assign 17 (.bin .add (.reg 16) (.reg 1))                                          -- wsTmpNxt
    , .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 7) (.reg 1)))                   -- wsUsedList
    , .assign 19 (.bin .add (.reg 18) (.reg 1))                                          -- wsSBuf
    , .assign 20 (.bin .add (.reg 19) (.reg 1))                                          -- wsResOff
    , .assign 21 (.bin .add (.bin .add (.reg 20) (.reg 1)) (.const 1))                   -- wsResNb
    , .assign 22 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 21) (.reg 10))
        (.reg 1)) (.const 1)) (.bin .mul (.const 3) (.reg 2)))                           -- wsLayerOffS
    , .assign 23 (.bin .add (.bin .add (.reg 22) (.reg 1)) (.const 1))                   -- wsLayerDataS
    , .assign 24 (.bin .add (.reg 23) (.reg 1))                                          -- wsLayerOffT
    , .assign 25 (.bin .add (.bin .add (.reg 24) (.reg 1)) (.const 1))                   -- wsLayerDataT
    , .assign 26 (.bin .add (.reg 25) (.reg 1))                                          -- wsBallStamp
    , .assign 27 (.bin .add (.reg 26) (.reg 1))                                          -- wsBallList
    , .assign 28 (.bin .add (.reg 27) (.reg 1))                                          -- wsLiveStamp
    , .assign 29 (.bin .add (.reg 28) (.reg 1))                                          -- wsSBallBuf
    , .assign 30 (.bin .add (.reg 29) (.reg 1)) ]                                        -- wsTBallBuf

/-- Write the 6 static fields of `SpCfg` (`ws + 0..8`) and 12 static fields of `BfsCfg` (`ws + 20..34`). -/
def initSubCfgsSpBfsStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 9) (.const 0)) (.bin .add (.reg 9) (.const 20))
    , .store (.bin .add (.reg 9) (.const 1)) (.bin .add (.reg 9) (.const 44))
    , .store (.bin .add (.reg 9) (.const 2)) (.reg 12)
    , .store (.bin .add (.reg 9) (.const 4)) (.reg 18)
    , .store (.bin .add (.reg 9) (.const 5)) (.reg 19)
    , .store (.bin .add (.reg 9) (.const 8)) (.reg 3)
    , .store (.bin .add (.reg 9) (.const 20)) (.reg 5)
    , .store (.bin .add (.reg 9) (.const 21)) (.reg 6)
    , .store (.bin .add (.reg 9) (.const 22)) (.reg 12)
    , .store (.bin .add (.reg 9) (.const 24)) (.const 1)
    , .store (.bin .add (.reg 9) (.const 25)) (.reg 8)
    , .store (.bin .add (.reg 9) (.const 27)) (.reg 13)
    , .store (.bin .add (.reg 9) (.const 28)) (.reg 14)
    , .store (.bin .add (.reg 9) (.const 29)) (.reg 15)
    , .store (.bin .add (.reg 9) (.const 30)) (.reg 16)
    , .store (.bin .add (.reg 9) (.const 31)) (.reg 17)
    , .store (.bin .add (.reg 9) (.const 33)) (.reg 3)
    , .store (.bin .add (.reg 9) (.const 34)) (.reg 19) ]

/-- Write the 15 static fields of `DfsCfg` (`ws + 44..63`). -/
def initSubCfgsDfsStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 9) (.const 44)) (.reg 5)
    , .store (.bin .add (.reg 9) (.const 45)) (.reg 6)
    , .store (.bin .add (.reg 9) (.const 46)) (.reg 7)
    , .store (.bin .add (.reg 9) (.const 47)) (.reg 12)
    , .store (.bin .add (.reg 9) (.const 49)) (.reg 8)
    , .store (.bin .add (.reg 9) (.const 51)) (.reg 13)
    , .store (.bin .add (.reg 9) (.const 53)) (.reg 14)
    , .store (.bin .add (.reg 9) (.const 54)) (.bin .add (.reg 17) (.reg 1))
    , .store (.bin .add (.reg 9) (.const 55)) (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 1)))
    , .store (.bin .add (.reg 9) (.const 56)) (.bin .add (.reg 17) (.bin .mul (.const 3) (.reg 1)))
    , .store (.bin .add (.reg 9) (.const 57)) (.bin .add (.reg 17) (.bin .mul (.const 4) (.reg 1)))
    , .store (.bin .add (.reg 9) (.const 58)) (.bin .add (.reg 17) (.bin .mul (.const 5) (.reg 1)))
    , .store (.bin .add (.reg 9) (.const 59)) (.bin .add (.reg 17) (.bin .mul (.const 6) (.reg 1)))
    , .store (.bin .add (.reg 9) (.const 60)) (.reg 18)
    , .store (.bin .add (.reg 9) (.const 63)) (.reg 19) ]

/-- Write the 13 static fields of `BallCfg` (`ws + 76..93`) and 10 static fields of
`BfsBallCfg` (`ws + 100..113`). -/
def initSubCfgsBallStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 9) (.const 76)) (.bin .add (.reg 9) (.const 100))
    , .store (.bin .add (.reg 9) (.const 77)) (.reg 20)
    , .store (.bin .add (.reg 9) (.const 78)) (.reg 21)
    , .store (.bin .add (.reg 9) (.const 79)) (.reg 28)
    , .store (.bin .add (.reg 9) (.const 81)) (.reg 22)
    , .store (.bin .add (.reg 9) (.const 82)) (.reg 23)
    , .store (.bin .add (.reg 9) (.const 83)) (.reg 24)
    , .store (.bin .add (.reg 9) (.const 84)) (.reg 25)
    , .store (.bin .add (.reg 9) (.const 85)) (.reg 29)
    , .store (.bin .add (.reg 9) (.const 87)) (.reg 30)
    , .store (.bin .add (.reg 9) (.const 89)) (.reg 26)
    , .store (.bin .add (.reg 9) (.const 90)) (.reg 27)
    , .store (.bin .add (.reg 9) (.const 93)) (.reg 4)
    , .store (.bin .add (.reg 9) (.const 100)) (.reg 20)
    , .store (.bin .add (.reg 9) (.const 101)) (.reg 21)
    , .store (.bin .add (.reg 9) (.const 102)) (.reg 28)
    , .store (.bin .add (.reg 9) (.const 104)) (.const 0)
    , .store (.bin .add (.reg 9) (.const 105)) (.const 0)
    , .store (.bin .add (.reg 9) (.const 106)) (.const 0)
    , .store (.bin .add (.reg 9) (.const 107)) (.reg 13)
    , .store (.bin .add (.reg 9) (.const 108)) (.reg 14)
    , .store (.bin .add (.reg 9) (.const 111)) (.reg 17)
    , .store (.bin .add (.reg 9) (.const 113)) (.reg 11) ]

/-- Initialize all 56 static sub-configuration words (`BatchSubCfgsInit`) in `ws[0..123]`. -/
def initBatchSubCfgsStmt : Stmt :=
  seqStmts
    [ initSubCfgsLoadStmt
    , initSubCfgsSpBfsStmt
    , initSubCfgsDfsStmt
    , initSubCfgsBallStmt ]

/-- Guard expression for the outer batch loop: `1` iff `iter < R ∧ z < curDemand ∧ tag = 0`. -/
def routeLoopGuardExpr : Expr :=
  .bin .mul
    (.bin .mul (.bin .lt (.reg 4) (.reg 2))
               (.bin .lt (.reg 3) (.load (.bin .add (.reg 0) (.const 16)))))
    (.bin .eq (.reg 5) (.const 0))

/-- Outer batch loop calling `runBatchProc` at index `bBatch` up to `R` times.
Expects `reg 0 = cfgAddr`. Ends with `reg 5 = finalTag` (`0` = matched, `1` = cut). -/
def routeBatchesLoopStmt (bBatch : ℕ) : Stmt :=
  seqStmts
    [ .assign 2 (.load (.bin .add (.reg 0) (.const 26))) -- R
    , .assign 3 (.load (.bin .add (.reg 0) (.const 27))) -- z
    , .assign 4 (.const 0)                               -- iter
    , .assign 5 (.const 0)                               -- tag
    , .loop routeLoopGuardExpr
        (seqStmts
          [ .call 5 bBatch [.reg 0]
          , .assign 4 (.bin .add (.reg 4) (.const 1)) ]) ]

/-- Emit `RouteOutAt` for a cut `U` from `wsCutList[0 .. cutSize - 1]`.
Expects `reg 0 = cfgAddr`. -/
def emitCutStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))  -- nX
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))  -- k
    , .assign 3 (.load (.bin .add (.reg 0) (.const 14))) -- ws
    , .assign 4 (.load (.bin .add (.reg 0) (.const 15))) -- m2
    , .assign 6 (.load (.bin .add (.reg 0) (.const 25))) -- cutSize
    , .assign 7 (.load (.bin .add (.reg 0) (.const 29))) -- origVertAddr
    , .assign 8 (.load (.bin .add (.reg 0) (.const 30))) -- outAddr
    , .assign 9 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 3) (.const 129))
        (.bin .mul (.const 26) (.reg 1))) (.reg 4)) (.bin .mul (.const 3) (.reg 2))) -- wsCutList
    , .store (.reg 8) (.const 1)
    , .store (.bin .add (.reg 8) (.const 1)) (.reg 6)
    , .assign 10 (.const 0)
    , .loop (.bin .lt (.reg 10) (.reg 6))
        (seqStmts
          [ .assign 11 (.load (.bin .add (.reg 9) (.reg 10)))
          , .assign 12 (.load (.bin .add (.reg 7) (.reg 11)))
          , .store (.bin .add (.bin .add (.reg 8) (.const 2)) (.reg 10)) (.reg 12)
          , .assign 10 (.bin .add (.reg 10) (.const 1)) ]) ]

/-- Inner loop emitting a single `PathListAt` starting at `reg 13` into `outAddr` (`reg 8`) and
`walksAddr` (`reg 9`), updating edge counter `reg 10`. -/
def emitPathListLoopStmt : Stmt :=
  .loop (.bin .lt (.const 0) (.reg 13))
    (seqStmts
      [ .assign 14 (.load (.reg 13))                                           -- sLoc
      , .assign 15 (.load (.bin .add (.reg 13) (.const 1)))                    -- tLoc
      , .assign 16 (.load (.bin .add (.reg 13) (.const 2)))                    -- wPtr
      , .assign 17 (.load (.bin .add (.reg 7) (.reg 14)))                      -- orig(sLoc)
      , .assign 18 (.load (.bin .add (.reg 7) (.reg 15)))                      -- orig(tLoc)
      , .store (.bin .add (.bin .add (.reg 8) (.const 2))
          (.bin .mul (.const 2) (.reg 10))) (.reg 17)
      , .store (.bin .add (.bin .add (.reg 8) (.const 3))
          (.bin .mul (.const 2) (.reg 10))) (.reg 18)
      , .store (.bin .add (.bin .add (.reg 9) (.const 1)) (.reg 10)) (.reg 16)
      , .assign 10 (.bin .add (.reg 10) (.const 1))
      , .assign 13 (.load (.bin .add (.reg 13) (.const 3))) ])

/-- Middle loop emitting a `ChunkChainAt` starting at `reg 12`. -/
def emitChunkChainLoopStmt : Stmt :=
  .loop (.bin .lt (.const 0) (.reg 12))
    (seqStmts
      [ .assign 13 (.load (.reg 12))
      , emitPathListLoopStmt
      , .assign 12 (.load (.bin .add (.reg 12) (.const 1))) ])

/-- Emit `RouteOutAt` at `outAddr` and `WalksAt` at `walksAddr` for a matched outcome by
scanning the `k` accumulated chunk chains at `accHeadAddr`. Expects `reg 0 = cfgAddr`. -/
def emitMatchedStmt : Stmt :=
  seqStmts
    [ .assign 2 (.load (.bin .add (.reg 0) (.const 1)))  -- k
    , .assign 6 (.load (.bin .add (.reg 0) (.const 12))) -- accHeadAddr
    , .assign 7 (.load (.bin .add (.reg 0) (.const 29))) -- origVertAddr
    , .assign 8 (.load (.bin .add (.reg 0) (.const 30))) -- outAddr
    , .assign 9 (.load (.bin .add (.reg 0) (.const 31))) -- walksAddr
    , .assign 10 (.const 0)                              -- cnt
    , .assign 11 (.const 0)                              -- j
    , .loop (.bin .lt (.reg 11) (.reg 2))
        (seqStmts
          [ .assign 12 (.load (.bin .add (.reg 6) (.reg 11)))
          , emitChunkChainLoopStmt
          , .assign 11 (.bin .add (.reg 11) (.const 1)) ])
    , .store (.reg 8) (.const 0)
    , .store (.bin .add (.reg 8) (.const 1)) (.reg 10)
    , .store (.reg 9) (.reg 10) ]

/-- Early-exit statement writing an empty matched result at `outAddr` and `walksAddr` and
returning `0` in `O(1)` steps. Expects `reg 0 = cfgAddr`. -/
def emitEmptyMatchedRetStmt : Stmt :=
  seqStmts
    [ .assign 8 (.load (.bin .add (.reg 0) (.const 30)))
    , .assign 9 (.load (.bin .add (.reg 0) (.const 31)))
    , .store (.reg 8) (.const 0)
    , .store (.bin .add (.reg 8) (.const 1)) (.const 0)
    , .store (.reg 9) (.const 0)
    , .ret (.const 0) ]

/-- Procedure 5 (`routeOrCutCsrProc bBatch`): executes `routeOrCut` on a prebuilt local CSR and
local terminal pairs, taking argument `[cfgAddr]` and calling `runBatchProc` at index `bBatch`.
Returns `0` for `.matched` and `1` for `.cut`. -/
def routeOrCutCsrProc (bBatch : ℕ) : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 16))) -- curDemand
    , .assign 2 (.load (.bin .add (.reg 0) (.const 26))) -- R
    , .assign 3 (.load (.bin .add (.reg 0) (.const 27))) -- z
    , .cond (.bin .mul (.bin .lt (.reg 3) (.reg 1)) (.bin .lt (.const 0) (.reg 2)))
        (seqStmts
          [ initBatchSubCfgsStmt
          , routeBatchesLoopStmt bBatch
          , .cond (.reg 5) emitCutStmt emitMatchedStmt
          , .ret (.reg 5) ])
        emitEmptyMatchedRetStmt ]

theorem routeOrCutCsrProc_noRand (bBatch : ℕ) :
    Stmt.NoRand (routeOrCutCsrProc bBatch) := by
  unfold routeOrCutCsrProc initBatchSubCfgsStmt initSubCfgsLoadStmt initSubCfgsSpBfsStmt
    initSubCfgsDfsStmt initSubCfgsBallStmt routeBatchesLoopStmt emitCutStmt emitMatchedStmt
    emitChunkChainLoopStmt emitPathListLoopStmt emitEmptyMatchedRetStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-- Step bound for `routeOrCutCsrProc`: `2500 * routeOrCutCost + 2500`. -/
def routeCsrProgCost (modelCost : ℕ) : ℕ :=
  2500 * modelCost + 2500

end MinCostFlow.ExpanderDecomp
