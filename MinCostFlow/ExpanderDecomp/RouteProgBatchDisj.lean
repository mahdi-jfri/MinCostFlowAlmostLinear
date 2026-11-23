module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchLemmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Statements and Disjointness Builders (`RouteProgBatchDisj`)

Deterministic Word-RAM sub-statements (`batchMarkMatchedStmt`..`runBatchProc`),
`runBatchProc_noRand`, and disjointness builders (`BatchDisj.to_spDisj`, `to_resCsrDisj`,
`to_curBDisj`, `to_ballDisj`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. Sub-Statements and Full `runBatchProc` Procedure -/

/-- Walk `PathListAt` starting at `r22` (`nd`), stamping `matchAStamp[aLoc] := batchGen` (`r17`)
and clearing `pairB[bLoc] := 0`. Uses `r8 = pairBAddr`, `r16 = matchAStampAddr`, `r17 = batchGen`,
`r22 = nd`, scratch `r23, r24`. -/
def batchMarkMatchedStmt : Stmt :=
  .loop (.reg 22)
    (seqStmts
      [ .assign 23 (.load (.reg 22))
      , .assign 24 (.load (.bin .add (.reg 22) (.const 1)))
      , .store (.bin .add (.reg 16) (.reg 23)) (.reg 17)
      , .store (.bin .add (.reg 8) (.reg 24)) (.const 0)
      , .assign 22 (.load (.bin .add (.reg 22) (.const 3))) ])

/-- Compact `aData[r23 .. r23 + r24 - 1]` in-place, keeping entries `v` with
`matchAStamp[v] ≠ batchGen` (`r17`), leaving new length in `r25`.
Uses `r16 = matchAStampAddr`, `r17 = batchGen`, `r23 = base = aData + aOff[i]`, `r24 = len`,
scratch `r25 = wpos`, `r26 = rpos`, `r27, r28`. -/
def batchCompactAStmt : Stmt :=
  seqStmts
    [ .assign 25 (.const 0)
    , .assign 26 (.const 0)
    , .loop (.bin .lt (.reg 26) (.reg 24))
        (seqStmts
          [ .assign 27 (.load (.bin .add (.reg 23) (.reg 26)))
          , .assign 28 (.load (.bin .add (.reg 16) (.reg 27)))
          , .cond (.bin .eq (.reg 28) (.reg 17))
              .nop
              (seqStmts
                [ .store (.bin .add (.reg 23) (.reg 25)) (.reg 27)
                , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
          , .assign 26 (.bin .add (.reg 26) (.const 1)) ]) ]

/-- If `r25 > 0` (`spLen > 0`), allocate a 2-word chunk `[spHead, 0]` at `chunkHeapPtr` (`r21`)
and tail-link it onto `(accHead[i], accTail[i])`.
Uses `r12 = accHeadAddr`, `r13 = accTailAddr`, `r21 = chunkHeapPtr`, `r22 = spHead`,
`r25 = spLen`, `r29 = i`, scratch `r26, r27`. -/
def batchAppendChunkStmt : Stmt :=
  .cond (.reg 25)
    (seqStmts
      [ .store (.reg 21) (.reg 22)
      , .store (.bin .add (.reg 21) (.const 1)) (.const 0)
      , .assign 26 (.load (.bin .add (.reg 12) (.reg 29)))
      , .cond (.reg 26)
          (seqStmts
            [ .assign 27 (.load (.bin .add (.reg 13) (.reg 29)))
            , .store (.bin .add (.reg 27) (.const 1)) (.reg 21) ])
          (.store (.bin .add (.reg 12) (.reg 29)) (.reg 21))
      , .store (.bin .add (.reg 13) (.reg 29)) (.reg 21)
      , .assign 21 (.bin .add (.reg 21) (.const 2)) ])
    .nop

/-- Filter `inBase[0 .. inLen - 1]` into `outBuf`, keeping entries `v` with
`liveStamp[v] ≠ liveGen`, leaving output length in `r25`.
Uses `r22 = liveStampAddr`, `r23 = liveGen`, `r24 = inBase`, `r26 = inLen`, `r27 = outBuf`,
scratch `r25 = wpos`, `r28 = rpos`, `r29 = v`, `r30 = stv`. -/
def batchFilterLiveStmt : Stmt :=
  seqStmts
    [ .assign 25 (.const 0)
    , .assign 28 (.const 0)
    , .loop (.bin .lt (.reg 28) (.reg 26))
        (seqStmts
          [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
          , .assign 30 (.load (.bin .add (.reg 22) (.reg 29)))
          , .cond (.bin .eq (.reg 30) (.reg 23))
              .nop
              (seqStmts
                [ .store (.bin .add (.reg 27) (.reg 25)) (.reg 29)
                , .assign 25 (.bin .add (.reg 25) (.const 1)) ])
          , .assign 28 (.bin .add (.reg 28) (.const 1)) ]) ]

/-- Copy `ballList[0 .. ballCnt - 1]` into `cutList[cutSize ..]` while stamping
`liveStamp[u] := liveGen`.
Uses `r22 = liveStampAddr`, `r23 = liveGen`, `r24 = ballListAddr`, `r25 = cutListAddr`,
`r26 = ballCnt`, `r27 = cutSize` (updated in place), scratch `r28 = j`, `r29 = u`. -/
def batchCopyBallStmt : Stmt :=
  seqStmts
    [ .assign 28 (.const 0)
    , .loop (.bin .lt (.reg 28) (.reg 26))
        (seqStmts
          [ .assign 29 (.load (.bin .add (.reg 24) (.reg 28)))
          , .store (.bin .add (.reg 22) (.reg 29)) (.reg 23)
          , .store (.bin .add (.reg 25) (.reg 27)) (.reg 29)
          , .assign 27 (.bin .add (.reg 27) (.const 1))
          , .assign 28 (.bin .add (.reg 28) (.const 1)) ]) ]

/-- Pair-routing loop of `runBatchProc` (`batchRoutePairs`).
Expects:
- `r0 = cfgAddr`, `r1 = nX`, `r2 = k`, `r8 = pairBAddr`, `r9 = aOffAddr`, `r10 = aLenAddr`,
  `r11 = aDataAddr`, `r12 = accHeadAddr`, `r13 = accTailAddr`, `r14 = ws`,
  `r15 = spCfgAddr (= ws)`, `r16 = matchAStampAddr`,
  `r17 = batchGen`, `r18 = bfsGen`, `r19 = dfsGen`, `r20 = pathHeap`, `r21 = chunkHeap`,
  `r29 = i (0)`, `r30 = routedTotal (0)`, `r31 = bfsCfgAddr`, `r32 = dfsCfgAddr`.
- Modifies `r18, r19, r20, r21, r22..r30`. -/
def batchRouteLoopStmt (bSp : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 29) (.reg 2))
    (seqStmts
      [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
      , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
      , .store (.bin .add (.reg 15) (.const 3)) (.reg 17)
      , .store (.bin .add (.reg 15) (.const 6)) (.reg 23)
      , .store (.bin .add (.reg 15) (.const 7)) (.reg 24)
      , .store (.bin .add (.reg 15) (.const 9)) (.reg 18)
      , .store (.bin .add (.reg 15) (.const 10)) (.reg 19)
      , .store (.bin .add (.reg 15) (.const 11)) (.reg 20)
      , .store (.bin .add (.reg 31) (.const 3)) (.reg 17)
      , .store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 29) (.const 1))
      , .store (.bin .add (.reg 32) (.const 4)) (.reg 17)
      , .store (.bin .add (.reg 32) (.const 6)) (.bin .add (.reg 29) (.const 1))
      , .call 25 bSp [.reg 15]
      , .assign 22 (.load (.bin .add (.reg 15) (.const 12)))
      , .assign 20 (.load (.bin .add (.reg 15) (.const 14)))
      , .assign 18 (.load (.bin .add (.reg 15) (.const 16)))
      , .assign 19 (.load (.bin .add (.reg 15) (.const 17)))
      , .assign 30 (.bin .add (.reg 30) (.reg 25))
      , batchAppendChunkStmt
      , batchMarkMatchedStmt
      , .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
      , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
      , batchCompactAStmt
      , .store (.bin .add (.reg 10) (.reg 29)) (.reg 25)
      , .assign 29 (.bin .add (.reg 29) (.const 1)) ])

/-- Ball-growing loop of `runBatchProc` (`batchBallLoop`, called only on cut branch).
Expects:
- `r0 = cfgAddr`, `r1 = nX`, `r2 = k`, `r9 = aOffAddr`, `r10 = aLenAddr`, `r11 = aDataAddr`,
  `r14 = ws`, `r15 = ballCfgAddr`, `r16 = bfsBallCfgAddr`,
  `r17 = bOffAddr`, `r18 = bfsGen`, `r19 = ballGen`, `r20 = bLenAddr`, `r21 = bDataAddr`,
  `r22 = liveStampAddr`, `r23 = liveGen`,
  `r31 = i (0)`, `r32 = cutSize (0)`, `r33 = sBallBufAddr`, `r34 = tBallBufAddr`,
  `r35 = ballListAddr`, `r36 = cutListAddr`. -/
def batchBallLoopStmt (bBall : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 31) (.reg 2))
    (seqStmts
      [ .cond (.bin .lt (.bin .mul (.const 4) (.reg 32)) (.reg 1))
          (seqStmts
            [ .assign 24 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 31))))
            , .assign 26 (.load (.bin .add (.reg 10) (.reg 31)))
            , .assign 27 (.reg 33)
            , batchFilterLiveStmt
            , .assign 37 (.reg 25)
            , .assign 24 (.bin .add (.reg 21) (.load (.bin .add (.reg 17) (.reg 31))))
            , .assign 26 (.load (.bin .add (.reg 20) (.reg 31)))
            , .assign 27 (.reg 34)
            , batchFilterLiveStmt
            , .assign 38 (.reg 25)
            , .cond (.bin .lt (.const 0) (.reg 37))
                (.cond (.bin .lt (.const 0) (.reg 38))
                  (seqStmts
                    [ .store (.bin .add (.reg 15) (.const 4)) (.reg 23)
                    , .store (.bin .add (.reg 15) (.const 10)) (.reg 37)
                    , .store (.bin .add (.reg 15) (.const 12)) (.reg 38)
                    , .store (.bin .add (.reg 15) (.const 15)) (.reg 18)
                    , .store (.bin .add (.reg 15) (.const 16)) (.reg 19)
                    , .store (.bin .add (.reg 16) (.const 3)) (.reg 23)
                    , .call 26 bBall [.reg 15]
                    , .assign 18 (.load (.bin .add (.reg 15) (.const 19)))
                    , .assign 19 (.load (.bin .add (.reg 15) (.const 20)))
                    , .assign 24 (.reg 35)
                    , .assign 25 (.reg 36)
                    , .assign 27 (.reg 32)
                    , batchCopyBallStmt
                    , .assign 32 (.reg 27) ])
                  .nop)
                .nop
            , .assign 31 (.bin .add (.reg 31) (.const 1)) ])
          (.assign 31 (.reg 2)) ])

/-- Load routing-phase fields from `cfgAddr` (`r0`) and initialize loop registers. -/
def batchLoadRouteStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))
    , .assign 9 (.load (.bin .add (.reg 0) (.const 9)))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 10)))
    , .assign 11 (.load (.bin .add (.reg 0) (.const 11)))
    , .assign 12 (.load (.bin .add (.reg 0) (.const 12)))
    , .assign 13 (.load (.bin .add (.reg 0) (.const 13)))
    , .assign 14 (.load (.bin .add (.reg 0) (.const 14)))
    , .assign 15 (.reg 14)
    , .assign 16 (.bin .add (.bin .add (.reg 14) (.const 124)) (.reg 1))
    , .assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const 17))) (.const 1))
    , .assign 18 (.load (.bin .add (.reg 0) (.const 18)))
    , .assign 19 (.load (.bin .add (.reg 0) (.const 19)))
    , .assign 20 (.load (.bin .add (.reg 0) (.const 22)))
    , .assign 21 (.load (.bin .add (.reg 0) (.const 23)))
    , .assign 29 (.const 0)
    , .assign 30 (.const 0)
    , .assign 31 (.bin .add (.reg 14) (.const 20))
    , .assign 32 (.bin .add (.reg 14) (.const 44)) ]

/-- Cut-branch body of `runBatchProc`: builds residual CSR + sorted `curB`, runs
`batchBallLoopStmt`, writes outputs (`outcome = 1, cutSize`), and returns `1`. -/
def batchCutBranchStmt (bRes bCurB bBall : ℕ) : Stmt :=
  seqStmts
    [ .assign 3 (.load (.bin .add (.reg 0) (.const 5)))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 6)))
    , .assign 5 (.load (.bin .add (.reg 0) (.const 15)))
    , .assign 6 (.bin .add (.reg 14) (.const 124))
    , .assign 7 (.bin .add (.bin .add (.reg 14) (.const 125)) (.bin .mul (.const 15) (.reg 1)))
    , .assign 22 (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 1))
    , .call 23 bRes [.reg 3, .reg 4, .reg 6, .reg 17, .reg 1, .reg 7, .reg 22]
    , .assign 17 (.bin .add (.reg 22) (.reg 5))
    , .assign 20 (.bin .add (.bin .add (.reg 17) (.const 1)) (.reg 2))
    , .assign 21 (.bin .add (.reg 20) (.reg 2))
    , .assign 24 (.bin .add (.reg 21) (.reg 1))
    , .call 25 bCurB [.reg 8, .reg 1, .reg 2, .reg 17, .reg 20, .reg 21, .reg 24]
    , .assign 15 (.bin .add (.reg 14) (.const 76))
    , .assign 16 (.bin .add (.reg 14) (.const 100))
    , .assign 19 (.load (.bin .add (.reg 0) (.const 20)))
    , .assign 22 (.load (.bin .add (.reg 15) (.const 3)))
    , .assign 23 (.bin .add (.load (.bin .add (.reg 0) (.const 21))) (.const 1))
    , .assign 33 (.load (.bin .add (.reg 15) (.const 9)))
    , .assign 34 (.load (.bin .add (.reg 15) (.const 11)))
    , .assign 35 (.load (.bin .add (.reg 15) (.const 14)))
    , .assign 36 (.bin .add (.reg 34) (.reg 1))
    , .assign 31 (.const 0)
    , .assign 32 (.const 0)
    , batchBallLoopStmt bBall
    , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
    , .store (.bin .add (.reg 0) (.const 20)) (.reg 19)
    , .store (.bin .add (.reg 0) (.const 21)) (.reg 23)
    , .store (.bin .add (.reg 0) (.const 24)) (.const 1)
    , .store (.bin .add (.reg 0) (.const 25)) (.reg 32)
    , .ret (.const 1) ]

/-- Full deterministic Word-RAM procedure `runBatchProc` for `runBatch`.
Argument: `[cfgAddr]`. Returns `0` for `matched` or `1` for `cut`. -/
def runBatchProc (bSp bRes bCurB bBall : ℕ) : Stmt :=
  seqStmts
    [ batchLoadRouteStmt
    , batchRouteLoopStmt bSp
    , .store (.bin .add (.reg 0) (.const 17)) (.reg 17)
    , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
    , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
    , .store (.bin .add (.reg 0) (.const 22)) (.reg 20)
    , .store (.bin .add (.reg 0) (.const 23)) (.reg 21)
    , .assign 26 (.load (.bin .add (.reg 0) (.const 4)))
    , .assign 27 (.load (.bin .add (.reg 0) (.const 16)))
    , .cond (.bin .lt (.bin .mul (.reg 30) (.reg 26)) (.reg 27))
        (batchCutBranchStmt bRes bCurB bBall)
        (seqStmts
          [ .store (.bin .add (.reg 0) (.const 16)) (.bin .sub (.reg 27) (.reg 30))
          , .store (.bin .add (.reg 0) (.const 24)) (.const 0)
          , .store (.bin .add (.reg 0) (.const 25)) (.const 0)
          , .ret (.const 0) ]) ]

theorem runBatchProc_noRand (bSp bRes bCurB bBall : ℕ) :
    Stmt.NoRand (runBatchProc bSp bRes bCurB bBall) := by
  unfold runBatchProc batchLoadRouteStmt batchRouteLoopStmt batchAppendChunkStmt
    batchMarkMatchedStmt batchCompactAStmt batchCutBranchStmt batchBallLoopStmt
    batchFilterLiveStmt batchCopyBallStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander


/-! ## 7. Disjointness Builders from `BatchDisj` -/

lemma BatchDisj.to_spDisj {w cfgAddr pLo pHi cLo cHi hL : ℕ} {cfg : BatchCfg}
    (h : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    {batchGen stopVal srcInPtr srcInLen bfsGen dfsGen heapIn : ℕ}
    (hbg : batchGen ≤ cfg.batchGenIn + 1)
    (hsv : stopVal ≤ cfg.k)
    (hsrc_sub : cfg.aDataAddr ≤ srcInPtr ∧ srcInPtr + srcInLen ≤ cfg.aDataAddr + cfg.nX)
    (hbfsg : bfsGen ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 1))
    (hdfsg : dfsGen ≤ cfg.dfsGenIn + cfg.k * (cfg.d + 1))
    (hhp_lo : pLo ≤ heapIn) (hhp_hi : heapIn + 10 * cfg.nX ≤ pHi) :
    SpDisj w cfg.nX cfg.m2
      (mkBatchSpCfg cfg batchGen srcInPtr srcInLen bfsGen dfsGen heapIn)
      (mkBatchSpBfsCfg cfg batchGen stopVal)
      (mkBatchSpDfsCfg cfg batchGen stopVal)
      (wsSpCfg cfg.ws) := by
  have hS := rfl (a := batchScratchSize cfg.nX cfg.m2 cfg.k)
  have hw_off := h.w_off; have hw_nb := h.w_nb; have hw_edge := h.w_edge
  have hw_pb := h.w_pb; have hw_ad := h.w_ad; have hw_ws := h.w_ws
  have hw_hp := h.w_hp; have hw_nX4 := h.w_nX4; have hw_m2 := h.w_m2
  have hw_k := h.w_k; have hw_d := h.w_d; have hw_bgen := h.w_bgen
  have hw_bfsgen := h.w_bfsgen; have hw_dfsgen := h.w_dfsgen; have hw4 := h.w_4
  have hhp_lo_le : pLo ≤ pHi := by omega
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' hhp_lo_le
  -- Unpack needed top-level DisjRange hypotheses
  have h_off_ws := h.ro_off_ws; have h_nb_ws := h.ro_nb_ws; have h_edge_ws := h.ro_edge_ws
  have h_pb_ws := h.pb_ws; have h_ad_ws := h.ad_ws; have h_ws_hp := h.ws_hp
  have h_off_hp := h.ro_off_hp; have h_nb_hp := h.ro_nb_hp; have h_edge_hp := h.ro_edge_hp
  have h_pb_hp := h.pb_hp; have h_ad_hp := h.ad_hp
  have hhp_pos : 1 ≤ heapIn := by have := h.hp_pos; omega
  have hk_le : cfg.k * (cfg.d + 1) ≤ cfg.k * (cfg.d + 3) := Nat.mul_le_mul_left _ (by omega)
  unfold DisjRange at h_off_ws h_nb_ws h_edge_ws h_pb_ws h_ad_ws h_ws_hp h_off_hp h_nb_hp h_edge_hp h_pb_hp h_ad_hp
  unfold batchScratchSize at h_off_ws h_nb_ws h_edge_ws h_pb_ws h_ad_ws h_ws_hp hw_ws
  refine
    { bfs_mask := rfl, bfs_bad := rfl, bfs_hasStop := rfl, bfs_maxDist := rfl, bfs_initPtr := rfl
      dfs_off := rfl, dfs_nb := rfl, dfs_mask := rfl, dfs_bad := rfl, dfs_stop := rfl
      dfs_stopVal := rfl, dfs_vis := rfl, dfs_dist := rfl, dfs_usedList := rfl, dfs_srcPtr := rfl
      bfs_disj := ?_, dfs_disj := ?_,
      cs_hp10 := ?_, cur_hp10 := ?_, us_hp10 := ?_, ds_hp10 := ?_, sv_hp10 := ?_, se_hp10 := ?_,
      ul_hp10 := ?_, dco_hp10 := ?_, dcfg_hp10 := ?_, off_hp10 := ?_, nb_hp10 := ?_,
      edge_hp10 := ?_, mask_hp10 := ?_, stop_hp10 := ?_, vis_hp10 := ?_, dist_hp10 := ?_,
      sbuf_hp10 := ?_,
      bcfg_dcfg := by simp [mkBatchSpCfg, wsBfsCfg, wsDfsCfg, DisjRange]
      bcfg_sp := by simp [mkBatchSpCfg, wsBfsCfg, wsSpCfg, DisjRange]
      dcfg_sp := by simp [mkBatchSpCfg, wsDfsCfg, wsSpCfg, DisjRange]
      bcfg_off := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, DisjRange]; rcases h_off_ws with x | x <;> omega
      bcfg_nb := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, DisjRange]; rcases h_nb_ws with x | x <;> omega
      bcfg_edge := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsBfsCfg, DisjRange]; rcases h_edge_ws with x | x <;> omega
      bcfg_stop := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, DisjRange]; rcases h_pb_ws with x | x <;> omega
      bcfg_vis := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, wsVisStamp, DisjRange]; omega
      bcfg_dist := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, wsDist, DisjRange]; omega
      bcfg_cs := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsBfsCfg, wsCurStamp, DisjRange]; omega
      bcfg_us := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsBfsCfg, wsUsedStamp, DisjRange]; omega
      bcfg_ds := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsBfsCfg, wsDeadStamp, DisjRange]; omega
      dcfg_off := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsDfsCfg, DisjRange]; rcases h_off_ws with x | x <;> omega
      dcfg_nb := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsDfsCfg, DisjRange]; rcases h_nb_ws with x | x <;> omega
      dcfg_edge := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsDfsCfg, DisjRange]; rcases h_edge_ws with x | x <;> omega
      dcfg_stop := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsDfsCfg, DisjRange]; rcases h_pb_ws with x | x <;> omega
      dcfg_vis := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsDfsCfg, wsVisStamp, DisjRange]; omega
      dcfg_dist := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsDfsCfg, wsDist, DisjRange]; omega
      dcfg_cs := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsDfsCfg, wsCurStamp, DisjRange]; omega
      dcfg_us := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsDfsCfg, wsUsedStamp, DisjRange]; omega
      dcfg_ds := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsDfsCfg, wsDeadStamp, DisjRange]; omega
      dcfg_ul := by simp [mkBatchSpCfg, wsDfsCfg, wsUsedList, DisjRange]; omega
      sp_off := by simp [mkBatchSpBfsCfg, wsSpCfg, DisjRange]; rcases h_off_ws with x | x <;> omega
      sp_nb := by simp [mkBatchSpBfsCfg, wsSpCfg, DisjRange]; rcases h_nb_ws with x | x <;> omega
      sp_edge := by simp [mkBatchSpDfsCfg, wsSpCfg, DisjRange]; rcases h_edge_ws with x | x <;> omega
      sp_stop := by simp [mkBatchSpBfsCfg, wsSpCfg, DisjRange]; rcases h_pb_ws with x | x <;> omega
      sp_vis := by simp [mkBatchSpBfsCfg, wsSpCfg, wsVisStamp, DisjRange]; omega
      sp_cs := by simp [mkBatchSpDfsCfg, wsSpCfg, wsCurStamp, DisjRange]; omega
      sp_us := by simp [mkBatchSpDfsCfg, wsSpCfg, wsUsedStamp, DisjRange]; omega
      sp_ds := by simp [mkBatchSpDfsCfg, wsSpCfg, wsDeadStamp, DisjRange]; omega
      bcfg_dfsW := fun a ha hw => by
        simp only [DfsWriteSet, mkBatchSpCfg, mkBatchSpDfsCfg, wsBfsCfg, wsDfsCfg, wsCurStamp,
          wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
      bcfg_hp10 := by simp [mkBatchSpCfg, wsBfsCfg, DisjRange]; rcases h_ws_hp with x | x <;> omega
      dcfg_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg, wsDfsCfg, wsVisStamp,
          wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      edge_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg, wsBfsCfg,
          wsVisStamp, wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases h_edge_ws with x | x <;> rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      cs_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg, wsBfsCfg,
          wsCurStamp, wsVisStamp, wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      us_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg, wsBfsCfg,
          wsUsedStamp, wsVisStamp, wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      ds_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg, wsBfsCfg,
          wsDeadStamp, wsVisStamp, wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      hp10_bfsW := fun a ha hw => by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, wsBfsCfg,
          wsVisStamp, wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha hw
        rcases h_ws_hp with x | x <;> rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      mask_sbuf := by simp [mkBatchSpCfg, wsIsoStamp, wsSBuf, DisjRange]; omega
      mask_bcfg := by simp [mkBatchSpCfg, wsIsoStamp, wsBfsCfg, DisjRange]
      mask_dcfg := by simp [mkBatchSpCfg, wsIsoStamp, wsDfsCfg, DisjRange]
      mask_sp := by simp [mkBatchSpCfg, wsIsoStamp, wsSpCfg, DisjRange]
      mask_off := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsIsoStamp, DisjRange]; rcases h_off_ws with x | x <;> omega
      mask_nb := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsIsoStamp, DisjRange]; rcases h_nb_ws with x | x <;> omega
      mask_edge := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsIsoStamp, DisjRange]; rcases h_edge_ws with x | x <;> omega
      mask_stop := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsIsoStamp, DisjRange]; rcases h_pb_ws with x | x <;> omega
      mask_vis := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsIsoStamp, wsVisStamp, DisjRange]; omega
      mask_dist := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsIsoStamp, wsDist, DisjRange]; omega
      mask_cs := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsIsoStamp, wsCurStamp, DisjRange]; omega
      mask_us := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsIsoStamp, wsUsedStamp, DisjRange]; omega
      mask_ds := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsIsoStamp, wsDeadStamp, DisjRange]; omega
      mask_ul := by simp [mkBatchSpCfg, wsIsoStamp, wsUsedList, DisjRange]; omega
      sbuf_bcfg := by simp [mkBatchSpCfg, wsSBuf, wsBfsCfg, DisjRange]; omega
      sbuf_dcfg := by simp [mkBatchSpCfg, wsSBuf, wsDfsCfg, DisjRange]; omega
      sbuf_sp := by simp [mkBatchSpCfg, wsSBuf, wsSpCfg, DisjRange]; omega
      sbuf_off := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsSBuf, DisjRange]; rcases h_off_ws with x | x <;> omega
      sbuf_nb := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsSBuf, DisjRange]; rcases h_nb_ws with x | x <;> omega
      sbuf_edge := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsSBuf, DisjRange]; rcases h_edge_ws with x | x <;> omega
      sbuf_stop := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsSBuf, DisjRange]; rcases h_pb_ws with x | x <;> omega
      sbuf_vis := by simp [mkBatchSpCfg, mkBatchSpBfsCfg, wsSBuf, wsVisStamp, DisjRange]; omega
      sbuf_cs := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsSBuf, wsCurStamp, DisjRange]; omega
      sbuf_us := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsSBuf, wsUsedStamp, DisjRange]; omega
      sbuf_ds := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsSBuf, wsDeadStamp, DisjRange]; omega
      sbuf_src := by simp [mkBatchSpCfg, wsSBuf, DisjRange]; rcases h_ad_ws with x | x <;> omega
      sp_out_disj := fun a ha => ⟨by
        simp only [BfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, wsSpCfg, wsBfsCfg, wsVisStamp,
          wsDist, wsLayerOff, wsLayerData, wsTmpNxt] at ha ⊢
        intro hw; rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
        by
        simp only [DfsWriteSet, mkBatchSpCfg, mkBatchSpDfsCfg, wsSpCfg, wsDfsCfg, wsCurStamp,
          wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha ⊢
        intro hw; rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;>
          (try rcases h_ws_hp with x | x) <;> omega⟩
      sp_out_hp10 := by simp [mkBatchSpCfg, wsSpCfg, DisjRange]; rcases h_ws_hp with x | x <;> omega
      sp_in_disj := fun a ha hw => by
        simp only [SpWriteSet, BfsWriteSet, DfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg,
          mkBatchSpDfsCfg, wsSpCfg, wsBfsCfg, wsDfsCfg, wsIsoStamp, wsSBuf, wsVisStamp, wsDist,
          wsLayerOff, wsLayerData, wsTmpNxt, wsCurStamp, wsCurPtr, wsUsedStamp, wsDeadStamp,
          wsStkVert, wsStkEdge, wsUsedList] at ha hw
        rcases hw with (hw | hw | hw | hw | hw | hw) |
          (hw | hw | hw | hw | hw | hw | hw | hw | hw) | hw | (hw | hw) |
          (hw | hw | hw | hw) | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
      w_sp := by simp [wsSpCfg]; omega
      w_srcIn := by simp [mkBatchSpCfg]; omega
      w_hp10 := by simp [mkBatchSpCfg]; omega
      w_bgen := by simp [mkBatchSpCfg]; omega
      w_dgen := by simp [mkBatchSpCfg]; omega
      w_d := by simp [mkBatchSpCfg]; omega }
  · -- bfs_disj
    dsimp only [BfsDisj, mkBatchSpBfsCfg, mkBatchSpCfg, wsBfsCfg, wsVisStamp, wsDist,
      wsLayerOff, wsLayerData, wsTmpNxt, wsIsoStamp, wsSBuf, BfsWriteSet, DisjRange]
    refine ⟨by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega, by omega,
            fun a ha h => by rcases h with h | h | h | h | h | h <;> omega,
            fun a ha h => by rcases h_off_ws with x | x <;> rcases h with h | h | h | h | h | h <;> omega,
            fun a ha h => by rcases h_nb_ws with x | x <;> rcases h with h | h | h | h | h | h <;> omega,
            fun a ha h => by rcases h with h | h | h | h | h | h <;> omega,
            fun _ a ha h => by rcases h_pb_ws with x | x <;> rcases h with h | h | h | h | h | h <;> omega,
            fun a ha h => by rcases h with h | h | h | h | h | h <;> omega,
            by omega, by omega, by omega, by omega, fun _ => by omega,
            by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega, by omega, by omega, by omega, hw4⟩
  · -- dfs_disj
    refine
      { cs_cur := by simp [mkBatchSpDfsCfg, wsCurStamp, wsCurPtr, DisjRange]; omega
        cs_us := by simp [mkBatchSpDfsCfg, wsCurStamp, wsUsedStamp, DisjRange]; omega
        cs_ds := by simp [mkBatchSpDfsCfg, wsCurStamp, wsDeadStamp, DisjRange]; omega
        cs_sv := by simp [mkBatchSpDfsCfg, wsCurStamp, wsStkVert, DisjRange]; omega
        cs_se := by simp [mkBatchSpDfsCfg, wsCurStamp, wsStkEdge, DisjRange]; omega
        cs_ul := by simp [mkBatchSpDfsCfg, wsCurStamp, wsUsedList, DisjRange]; omega
        cs_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsCurStamp, wsDfsCfg, DisjRange]; omega
        cs_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsCurStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
        cur_us := by simp [mkBatchSpDfsCfg, wsCurPtr, wsUsedStamp, DisjRange]; omega
        cur_ds := by simp [mkBatchSpDfsCfg, wsCurPtr, wsDeadStamp, DisjRange]; omega
        cur_sv := by simp [mkBatchSpDfsCfg, wsCurPtr, wsStkVert, DisjRange]; omega
        cur_se := by simp [mkBatchSpDfsCfg, wsCurPtr, wsStkEdge, DisjRange]; omega
        cur_ul := by simp [mkBatchSpDfsCfg, wsCurPtr, wsUsedList, DisjRange]; omega
        cur_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsCurPtr, wsDfsCfg, DisjRange]; omega
        cur_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsCurPtr, DisjRange]; rcases h_ws_hp with x | x <;> omega
        us_ds := by simp [mkBatchSpDfsCfg, wsUsedStamp, wsDeadStamp, DisjRange]; omega
        us_sv := by simp [mkBatchSpDfsCfg, wsUsedStamp, wsStkVert, DisjRange]; omega
        us_se := by simp [mkBatchSpDfsCfg, wsUsedStamp, wsStkEdge, DisjRange]; omega
        us_ul := by simp [mkBatchSpDfsCfg, wsUsedStamp, wsUsedList, DisjRange]; omega
        us_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsUsedStamp, wsDfsCfg, DisjRange]; omega
        us_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsUsedStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
        ds_sv := by simp [mkBatchSpDfsCfg, wsDeadStamp, wsStkVert, DisjRange]; omega
        ds_se := by simp [mkBatchSpDfsCfg, wsDeadStamp, wsStkEdge, DisjRange]; omega
        ds_ul := by simp [mkBatchSpDfsCfg, wsDeadStamp, wsUsedList, DisjRange]; omega
        ds_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsDeadStamp, wsDfsCfg, DisjRange]; omega
        ds_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsDeadStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
        sv_se := by simp [mkBatchSpDfsCfg, wsStkVert, wsStkEdge, DisjRange]; omega
        sv_ul := by simp [mkBatchSpDfsCfg, wsStkVert, wsUsedList, DisjRange]; omega
        sv_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsStkVert, wsDfsCfg, DisjRange]; omega
        sv_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsStkVert, DisjRange]; rcases h_ws_hp with x | x <;> omega
        se_ul := by simp [mkBatchSpDfsCfg, wsStkEdge, wsUsedList, DisjRange]; omega
        se_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsStkEdge, wsDfsCfg, DisjRange]; omega
        se_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsStkEdge, DisjRange]; rcases h_ws_hp with x | x <;> omega
        ul_co := by simp [mkBatchSpCfg, mkBatchSpDfsCfg, wsUsedList, wsDfsCfg, DisjRange]; omega
        ul_hp := by simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsUsedList, DisjRange]; rcases h_ws_hp with x | x <;> omega
        co_hp := by simp [mkBatchSpCfg, wsDfsCfg, DisjRange]; rcases h_ws_hp with x | x <;> omega
        ro_cfg := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsCurStamp, wsCurPtr,
            wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
        ro_off := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsCurStamp, wsCurPtr,
            wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases h_off_ws with x | x <;> rcases h_off_hp with y | y <;>
            rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega
        ro_nb := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsCurStamp, wsCurPtr,
            wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases h_nb_ws with x | x <;> rcases h_nb_hp with y | y <;>
            rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega
        ro_edge := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsCurStamp, wsCurPtr,
            wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases h_edge_ws with x | x <;> rcases h_edge_hp with y | y <;>
            rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega
        ro_mask := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsIsoStamp, wsCurStamp,
            wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
        ro_stop := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsCurStamp, wsCurPtr,
            wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases h_pb_ws with x | x <;> rcases h_pb_hp with y | y <;>
            rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega
        ro_vis := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsVisStamp, wsCurStamp,
            wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
        ro_dist := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsDist, wsCurStamp,
            wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
        ro_src := fun a ha hw => by
          simp only [DfsWriteSet, mkBatchSpDfsCfg, mkBatchSpCfg, wsDfsCfg, wsSBuf, wsCurStamp,
            wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at ha hw
          rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw <;> (try rcases h_ws_hp with x | x) <;> omega
        hheap_pos := by simp [mkBatchSpCfg]; omega
        w_cfg := by simp [mkBatchSpCfg, wsDfsCfg]; omega
        w_off := by simp [mkBatchSpDfsCfg]; omega
        w_nb := by simp [mkBatchSpDfsCfg]; omega
        w_edge := by simp [mkBatchSpDfsCfg]; omega
        w_mask := by simp [mkBatchSpDfsCfg, wsIsoStamp]; omega
        w_stop := by simp [mkBatchSpDfsCfg]; omega
        w_vis := by simp [mkBatchSpDfsCfg, wsVisStamp]; omega
        w_dist := by simp [mkBatchSpDfsCfg, wsDist]; omega
        w_cs := by simp [mkBatchSpDfsCfg, wsCurStamp]; omega
        w_cur := by simp [mkBatchSpDfsCfg, wsCurPtr]; omega
        w_us := by simp [mkBatchSpDfsCfg, wsUsedStamp]; omega
        w_ds := by simp [mkBatchSpDfsCfg, wsDeadStamp]; omega
        w_sv := by simp [mkBatchSpDfsCfg, wsStkVert]; omega
        w_se := by simp [mkBatchSpDfsCfg, wsStkEdge]; omega
        w_ul := by simp [mkBatchSpDfsCfg, wsUsedList]; omega
        w_src := by simp [mkBatchSpDfsCfg, wsSBuf]; omega
        w_heap := by simp [mkBatchSpCfg]; omega
        w_mb := by simp [mkBatchSpDfsCfg]; omega
        w_sv_val := by simp [mkBatchSpDfsCfg]; omega
        w_bgen := by simp [mkBatchSpCfg]; omega
        w_dgen := by simp [mkBatchSpCfg]; omega
        w_td := by simp [mkBatchSpCfg]; omega
        w_m2 := by omega
        w_nX := by omega
        w4 := hw4 }
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsCurStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsCurPtr, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsUsedStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsDeadStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsStkVert, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsStkEdge, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, wsUsedList, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpCfg, wsDfsCfg, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpCfg, wsDfsCfg, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpBfsCfg, mkBatchSpCfg, DisjRange]; rcases h_off_hp with x | x <;> omega
  · simp [mkBatchSpBfsCfg, mkBatchSpCfg, DisjRange]; rcases h_nb_hp with x | x <;> omega
  · simp [mkBatchSpDfsCfg, mkBatchSpCfg, DisjRange]; rcases h_edge_hp with x | x <;> omega
  · simp [mkBatchSpCfg, wsIsoStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpBfsCfg, mkBatchSpCfg, DisjRange]; rcases h_pb_hp with x | x <;> omega
  · simp [mkBatchSpBfsCfg, mkBatchSpCfg, wsVisStamp, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpBfsCfg, mkBatchSpCfg, wsDist, DisjRange]; rcases h_ws_hp with x | x <;> omega
  · simp [mkBatchSpCfg, wsSBuf, DisjRange]; rcases h_ws_hp with x | x <;> omega

lemma BatchDisj.to_resCsrDisj {w cfgAddr pLo pHi cLo cHi hL : ℕ} {cfg : BatchCfg}
    (h : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg) {batchGen : ℕ} (hbg : batchGen ≤ cfg.batchGenIn + 1) :
    ResCsrDisj w cfg.nX cfg.m2 cfg.offAddr cfg.nbAddr (wsIsoStamp cfg.ws) batchGen
      (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) := by
  have h_off_ws := h.ro_off_ws; have h_nb_ws := h.ro_nb_ws; have hw_ws := h.w_ws
  have hw_off := h.w_off; have hw_nb := h.w_nb; have hw_nX4 := h.w_nX4; have hw_m2 := h.w_m2
  have hw_bgen := h.w_bgen; have hw4 := h.w_4
  unfold DisjRange batchScratchSize at h_off_ws h_nb_ws hw_ws
  refine
    { ro_rn := by simp [wsResOff, wsResNb, DisjRange]; omega
      ro_off := by simp [wsResOff, DisjRange]; rcases h_off_ws with x | x <;> omega
      ro_nb := by simp [wsResOff, DisjRange]; rcases h_nb_ws with x | x <;> omega
      ro_mask := by simp [wsResOff, wsIsoStamp, DisjRange]; omega
      rn_off := by simp [wsResNb, DisjRange]; rcases h_off_ws with x | x <;> omega
      rn_nb := by simp [wsResNb, DisjRange]; rcases h_nb_ws with x | x <;> omega
      rn_mask := by simp [wsResNb, wsIsoStamp, DisjRange]; omega
      w_off := hw_off, w_nb := hw_nb, w_mask := by simp [wsIsoStamp]; omega,
      w_ro := by simp [wsResOff]; omega, w_rn := by simp [wsResNb]; omega,
      w_nX := by omega, w_m2 := hw_m2, w_mb := by omega, w_4 := hw4 }

lemma BatchDisj.to_curBDisj {w cfgAddr pLo pHi cLo cHi hL : ℕ} {cfg : BatchCfg}
    (h : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg) :
    CurBDisj w cfg.nX cfg.k cfg.pairBAddr
      (wsBOff cfg.ws cfg.nX cfg.m2) (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k)
      (wsBData cfg.ws cfg.nX cfg.m2 cfg.k) (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) := by
  have h_pb_ws := h.pb_ws; have hw_ws := h.w_ws; have hw_pb := h.w_pb
  have hw_nX4 := h.w_nX4; have hw_k := h.w_k; have hw4 := h.w_4
  unfold DisjRange batchScratchSize at h_pb_ws hw_ws
  refine
    { bo_bl := by simp [wsBOff, wsBLen, DisjRange]; omega
      bo_bd := by simp [wsBOff, wsBData, DisjRange]; omega
      bo_bc := by simp [wsBOff, wsBCur, DisjRange]; omega
      bo_pb := by simp [wsBOff, DisjRange]; rcases h_pb_ws with x | x <;> omega
      bl_bd := by simp [wsBLen, wsBData, DisjRange]; omega
      bl_bc := by simp [wsBLen, wsBCur, DisjRange]; omega
      bl_pb := by simp [wsBLen, DisjRange]; rcases h_pb_ws with x | x <;> omega
      bd_bc := by simp [wsBData, wsBCur, DisjRange]; omega
      bd_pb := by simp [wsBData, DisjRange]; rcases h_pb_ws with x | x <;> omega
      bc_pb := by simp [wsBCur, DisjRange]; rcases h_pb_ws with x | x <;> omega
      w_pb := hw_pb, w_bo := by simp [wsBOff]; omega, w_bl := by simp [wsBLen]; omega,
      w_bd := by simp [wsBData]; omega, w_bc := by simp [wsBCur]; omega,
      w_nX := by omega, w_k := hw_k, w_4 := hw4 }

lemma BatchDisj.to_ballDisj {w cfgAddr pLo pHi cLo cHi hL : ℕ} {cfg : BatchCfg}
    (h : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    {liveGen sLen tLen bfsGen ballGen : ℕ}
    (hlg : liveGen ≤ cfg.liveGenIn + 1)
    (hsL : sLen ≤ cfg.nX) (htL : tLen ≤ cfg.nX)
    (hbfsg : bfsGen + 2 ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3))
    (hballg : ballGen + 1 ≤ cfg.ballGenIn + cfg.k) :
    BallDisj w cfg.nX cfg.m2
      (mkBatchBallCfg cfg liveGen sLen tLen bfsGen ballGen)
      (mkBatchBallBfsCfg cfg liveGen hL)
      (wsBallCfg cfg.ws) := by
  have hw_ws := h.w_ws; have hw_nX4 := h.w_nX4; have hw_m2 := h.w_m2
  have hw_hL := h.w_hL; have hw_livegen := h.w_livegen; have hw_bfsgen := h.w_bfsgen
  have hw_ballgen := h.w_ballgen; have hw_mul := h.w_mul; have hw_b16 := h.w_b16; have hw4 := h.w_4
  unfold batchScratchSize at hw_ws
  refine
    { bfs_off := rfl, bfs_nb := rfl, bfs_mask := rfl, bfs_bad := rfl, bfs_hasStop := rfl
      bfs_disj_S := by
        dsimp only [BfsDisj, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp, wsDist,
          wsLayerOffS, wsLayerDataS, wsTmpNxt, wsResOff, wsResNb, wsLiveStamp, wsSBallBuf,
          BfsWriteSet, DisjRange]
        refine ⟨by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun h0 => by omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                by omega, by omega, by omega, by omega, fun h0 => by omega,
                by omega, by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega, by omega, by omega, hw4⟩
      bfs_disj_T := by
        dsimp only [BfsDisj, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp, wsDist,
          wsLayerOffT, wsLayerDataT, wsTmpNxt, wsResOff, wsResNb, wsLiveStamp, wsTBallBuf,
          BfsWriteSet, DisjRange]
        refine ⟨by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                fun h0 => by omega,
                fun a ha hw => by rcases hw with hw | hw | hw | hw | hw | hw <;> omega,
                by omega, by omega, by omega, by omega, fun h0 => by omega,
                by omega, by omega, by omega, by omega, by omega, by omega,
                by omega, by omega, by omega, by omega, by omega, by omega, by omega, hw4⟩
      lOffS_bfsT := fun a ha hw => by
        dsimp only [BfsWriteSet, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp,
          wsDist, wsLayerOffS, wsLayerOffT, wsLayerDataT, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      lDataS_bfsT := fun a ha hw => by
        dsimp only [BfsWriteSet, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp,
          wsDist, wsLayerDataS, wsLayerOffT, wsLayerDataT, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      t_bfsS := fun a ha hw => by
        dsimp only [BfsWriteSet, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp,
          wsDist, wsTBallBuf, wsLayerOffS, wsLayerDataS, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      bs_bfsS := fun a ha hw => by
        dsimp only [BfsWriteSet, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp,
          wsDist, wsBallStamp, wsLayerOffS, wsLayerDataS, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      bs_bfsT := fun a ha hw => by
        dsimp only [BfsWriteSet, mkBatchBallBfsCfg, mkBatchBallCfg, wsBfsBallCfg, wsVisStamp,
          wsDist, wsBallStamp, wsLayerOffT, wsLayerDataT, wsTmpNxt] at ha hw
        rcases hw with hw | hw | hw | hw | hw | hw <;> omega
      bs_bl := by simp [mkBatchBallCfg, wsBallStamp, wsBallList, DisjRange]; omega
      bs_off := by simp [mkBatchBallCfg, wsBallStamp, wsResOff, DisjRange]; omega
      bs_nb := by simp [mkBatchBallCfg, wsBallStamp, wsResNb, DisjRange]; omega
      bs_mask := by simp [mkBatchBallCfg, wsBallStamp, wsLiveStamp, DisjRange]; omega
      bs_lOffS := by simp [mkBatchBallCfg, wsBallStamp, wsLayerOffS, DisjRange]; omega
      bs_lDataS := by simp [mkBatchBallCfg, wsBallStamp, wsLayerDataS, DisjRange]; omega
      bs_lOffT := by simp [mkBatchBallCfg, wsBallStamp, wsLayerOffT, DisjRange]; omega
      bs_lDataT := by simp [mkBatchBallCfg, wsBallStamp, wsLayerDataT, DisjRange]; omega
      bs_vis := by simp [mkBatchBallCfg, mkBatchBallBfsCfg, wsBallStamp, wsVisStamp, DisjRange]; omega
      bs_bcfg := by simp [mkBatchBallCfg, wsBallStamp, wsBfsBallCfg, DisjRange]; omega
      bs_cfg := by simp [mkBatchBallCfg, wsBallStamp, wsBallCfg, DisjRange]; omega
      bl_off := by simp [mkBatchBallCfg, wsBallList, wsResOff, DisjRange]; omega
      bl_nb := by simp [mkBatchBallCfg, wsBallList, wsResNb, DisjRange]; omega
      bl_mask := by simp [mkBatchBallCfg, wsBallList, wsLiveStamp, DisjRange]; omega
      bl_lOffS := by simp [mkBatchBallCfg, wsBallList, wsLayerOffS, DisjRange]; omega
      bl_lDataS := by simp [mkBatchBallCfg, wsBallList, wsLayerDataS, DisjRange]; omega
      bl_lOffT := by simp [mkBatchBallCfg, wsBallList, wsLayerOffT, DisjRange]; omega
      bl_lDataT := by simp [mkBatchBallCfg, wsBallList, wsLayerDataT, DisjRange]; omega
      bl_vis := by simp [mkBatchBallCfg, mkBatchBallBfsCfg, wsBallList, wsVisStamp, DisjRange]; omega
      bl_cfg := by simp [mkBatchBallCfg, wsBallList, wsBallCfg, DisjRange]; omega
      bcfg_cfg := by simp [mkBatchBallCfg, wsBallCfg, wsBfsBallCfg, DisjRange]
      cfg_vis := by simp [mkBatchBallBfsCfg, wsBallCfg, wsVisStamp, DisjRange]; omega
      lOffS_bcfg := by simp [mkBatchBallCfg, wsLayerOffS, wsBfsBallCfg, DisjRange]; omega
      lDataS_bcfg := by simp [mkBatchBallCfg, wsLayerDataS, wsBfsBallCfg, DisjRange]; omega
      bcfg_off := by simp [mkBatchBallCfg, wsBfsBallCfg, wsResOff, DisjRange]; omega
      bcfg_nb := by simp [mkBatchBallCfg, wsBfsBallCfg, wsResNb, DisjRange]; omega
      bcfg_mask := by simp [mkBatchBallCfg, wsBfsBallCfg, wsLiveStamp, DisjRange]; omega
      bcfg_s := by simp [mkBatchBallCfg, wsBfsBallCfg, wsSBallBuf, DisjRange]; omega
      bcfg_t := by simp [mkBatchBallCfg, wsBfsBallCfg, wsTBallBuf, DisjRange]; omega
      bcfg_vis := by simp [mkBatchBallCfg, mkBatchBallBfsCfg, wsBfsBallCfg, wsVisStamp, DisjRange]; omega
      w_cfg := by simp [wsBallCfg]; omega
      w_bs := by simp [mkBatchBallCfg, wsBallStamp]; omega
      w_bl := by simp [mkBatchBallCfg, wsBallList]; omega
      w_bgen := by simp [mkBatchBallCfg]; omega
      w_ballgen := by simp [mkBatchBallCfg]; omega
      w_mul := by simp [mkBatchBallCfg]; omega
      w_b16 := by simp [mkBatchBallCfg]; omega }


end MinCostFlow.ExpanderDecomp
