module

public import MinCostFlow.ExpanderDecomp.RouteProgLoopBase

/-!
# Static Sub-Configuration Initialization and Empty Early Exit (`RouteProgLoopInit`)

Verifies the straight-line initialization helper `initBatchSubCfgsStmt` (writing all 56 static
fields of `BatchSubCfgsInit` into `ws[0 .. 123]` in `O(1)` time) and the `O(1)` early-exit
helper `emitEmptyMatchedRetStmt` for Procedure 5 (`routeOrCutCsrProc`).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `initBatchSubCfgs_triple` -/

private def InitRegs (regs : ℕ → ℕ) (cfgAddr : ℕ) (rcfg : RouteLoopCfg) : Prop :=
  let c := rcfg.batch
  regs 0 = cfgAddr ∧ regs 1 = c.nX ∧ regs 2 = c.k ∧ regs 3 = c.d ∧ regs 4 = c.b ∧
  regs 5 = c.offAddr ∧ regs 6 = c.nbAddr ∧ regs 7 = c.edgeAddr ∧ regs 8 = c.pairBAddr ∧
  regs 9 = c.ws ∧ regs 10 = c.m2 ∧ regs 11 = rcfg.hL ∧
  regs 12 = wsIsoStamp c.ws ∧ regs 13 = wsVisStamp c.ws c.nX ∧
  regs 14 = wsDist c.ws c.nX ∧ regs 15 = wsLayerOff c.ws c.nX ∧
  regs 16 = wsLayerData c.ws c.nX ∧ regs 17 = wsTmpNxt c.ws c.nX ∧
  regs 18 = wsUsedList c.ws c.nX ∧ regs 19 = wsSBuf c.ws c.nX ∧
  regs 20 = wsResOff c.ws c.nX ∧ regs 21 = wsResNb c.ws c.nX ∧
  regs 22 = wsLayerOffS c.ws c.nX c.m2 c.k ∧ regs 23 = wsLayerDataS c.ws c.nX c.m2 c.k ∧
  regs 24 = wsLayerOffT c.ws c.nX c.m2 c.k ∧ regs 25 = wsLayerDataT c.ws c.nX c.m2 c.k ∧
  regs 26 = wsBallStamp c.ws c.nX c.m2 c.k ∧ regs 27 = wsBallList c.ws c.nX c.m2 c.k ∧
  regs 28 = wsLiveStamp c.ws c.nX c.m2 c.k ∧ regs 29 = wsSBallBuf c.ws c.nX c.m2 c.k ∧
  regs 30 = wsTBallBuf c.ws c.nX c.m2 c.k

private lemma initSubCfgsLoad_triple {w : ℕ} {p : Program}
    {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {st0 : State} (hcfg : RouteLoopCfgAt st0.mem cfgAddr rcfg) (hr0 : st0.regs 0 = cfgAddr) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω initSubCfgsLoadStmt st0 .normal st1 c1 ∧
      st1.mem = st0.mem ∧ InitRegs st1.regs cfgAddr rcfg ∧ c1 ≤ 290 := by
  intro ω
  set c := rcfg.batch
  have hw_cfg := hdisj.w_cfg
  have hw_ws : c.ws + (129 + 27 * c.nX + c.m2 + 3 * c.k) + 10 < 2 ^ w := hdisj.w_ws
  have hw_off : c.offAddr + c.nX + 5 < 2 ^ w := hdisj.w_off
  have hw_nb : c.nbAddr + c.m2 + 5 < 2 ^ w := hdisj.w_nb
  have hw_edge : c.edgeAddr + c.m2 + 5 < 2 ^ w := hdisj.w_edge
  have hw_pb : c.pairBAddr + c.nX + 5 < 2 ^ w := hdisj.w_pb
  have hw_d : c.d + 5 < 2 ^ w := hdisj.w_d
  have hw_b16 : 16 * c.b + 5 < 2 ^ w := hdisj.w_b16
  have hw_hL := hdisj.w_hL; have hw_k : c.k + 5 < 2 ^ w := hdisj.w_k
  have hw_m2 : c.m2 + 5 < 2 ^ w := hdisj.w_m2; have hw4 := hdisj.w_4
  rcases hcfg with ⟨⟨m0, m1, m2, m3, _, m5, m6, m7, m8, _, _, _, _, _, m14, m15, _, _, _, _, _, _, _, _⟩,
    _, _, m28, _, _, _⟩
  set regsA :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update st0.regs 1 c.nX) 2 c.k) 3 c.d) 4 c.b) 5 c.offAddr) 6 c.nbAddr)
    7 c.edgeAddr) 8 c.pairBAddr) 9 c.ws) 10 c.m2) 11 rcfg.hL
  set stA : State := { st0 with regs := regsA }
  have hA : ∃ cA,
      Runs w p ω
        (seqStmts
          [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
          , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
          , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))
          , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))
          , .assign 5 (.load (.bin .add (.reg 0) (.const 5)))
          , .assign 6 (.load (.bin .add (.reg 0) (.const 6)))
          , .assign 7 (.load (.bin .add (.reg 0) (.const 7)))
          , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))
          , .assign 9 (.load (.bin .add (.reg 0) (.const 14)))
          , .assign 10 (.load (.bin .add (.reg 0) (.const 15)))
          , .assign 11 (.load (.bin .add (.reg 0) (.const 28))) ])
        st0 .normal stA cA ∧ cA ≤ 90 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
            , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
            , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))
            , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))
            , .assign 5 (.load (.bin .add (.reg 0) (.const 5)))
            , .assign 6 (.load (.bin .add (.reg 0) (.const 6)))
            , .assign 7 (.load (.bin .add (.reg 0) (.const 7)))
            , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))
            , .assign 9 (.load (.bin .add (.reg 0) (.const 14)))
            , .assign 10 (.load (.bin .add (.reg 0) (.const 15)))
            , .assign 11 (.load (.bin .add (.reg 0) (.const 28))) ])
          st0 o s c0 ∧ (o = .normal ∧ s = stA) ∧ 0 + c0 ≤ 90 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := c.nX) (by rw [← m0]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.k) (by rw [← m1]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.d) (by rw [← m2]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.b) (by rw [← m3]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.offAddr) (by rw [← m5]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.nbAddr) (by rw [← m6]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.edgeAddr) (by rw [← m7]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.pairBAddr) (by rw [← m8]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.ws) (by rw [← m14]; eval_expr) ?_
      refine runs_seq_assign_le (v := c.m2) (by rw [← m15]; eval_expr) ?_
      refine runs_assign_le (v := rcfg.hL) (by rw [← m28]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
  have hA1 : stA.regs 1 = c.nX := by simp [stA, regsA]
  have hA2 : stA.regs 2 = c.k := by simp [stA, regsA]
  have hA9 : stA.regs 9 = c.ws := by simp [stA, regsA]
  have hA10 : stA.regs 10 = c.m2 := by simp [stA, regsA]
  set regsB :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    stA.regs 12 (wsIsoStamp c.ws)) 13 (wsVisStamp c.ws c.nX)) 14 (wsDist c.ws c.nX))
    15 (wsLayerOff c.ws c.nX)) 16 (wsLayerData c.ws c.nX)) 17 (wsTmpNxt c.ws c.nX))
    18 (wsUsedList c.ws c.nX)) 19 (wsSBuf c.ws c.nX)) 20 (wsResOff c.ws c.nX))
    21 (wsResNb c.ws c.nX)
  set stB : State := { stA with regs := regsB }
  have hB : ∃ cB,
      Runs w p ω
        (seqStmts
          [ .assign 12 (.bin .add (.reg 9) (.const 124))
          , .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1)))
          , .assign 14 (.bin .add (.reg 13) (.reg 1))
          , .assign 15 (.bin .add (.reg 14) (.reg 1))
          , .assign 16 (.bin .add (.bin .add (.reg 15) (.reg 1)) (.const 1))
          , .assign 17 (.bin .add (.reg 16) (.reg 1))
          , .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 7) (.reg 1)))
          , .assign 19 (.bin .add (.reg 18) (.reg 1))
          , .assign 20 (.bin .add (.reg 19) (.reg 1))
          , .assign 21 (.bin .add (.bin .add (.reg 20) (.reg 1)) (.const 1)) ])
        stA .normal stB cB ∧ cB ≤ 80 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 12 (.bin .add (.reg 9) (.const 124))
            , .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1)))
            , .assign 14 (.bin .add (.reg 13) (.reg 1))
            , .assign 15 (.bin .add (.reg 14) (.reg 1))
            , .assign 16 (.bin .add (.bin .add (.reg 15) (.reg 1)) (.const 1))
            , .assign 17 (.bin .add (.reg 16) (.reg 1))
            , .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 7) (.reg 1)))
            , .assign 19 (.bin .add (.reg 18) (.reg 1))
            , .assign 20 (.bin .add (.reg 19) (.reg 1))
            , .assign 21 (.bin .add (.bin .add (.reg 20) (.reg 1)) (.const 1)) ])
          stA o s c0 ∧ (o = .normal ∧ s = stB) ∧ 0 + c0 ≤ 80 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wsIsoStamp c.ws) (by unfold wsIsoStamp; eval_expr) ?_
      refine runs_seq_assign_le (v := wsVisStamp c.ws c.nX) (by unfold wsIsoStamp wsVisStamp; eval_expr) ?_
      refine runs_seq_assign_le (v := wsDist c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsVisStamp, wsDist, show c.ws + 124 + 2 * c.nX + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLayerOff c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsDist, wsLayerOff, show c.ws + 124 + 3 * c.nX + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLayerData c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsLayerOff, wsLayerData, show 1 < 2 ^ w by omega,
             show c.ws + 124 + 4 * c.nX + c.nX < 2 ^ w by omega,
             show c.ws + 124 + 4 * c.nX + c.nX + 1 < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsTmpNxt c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsLayerData, wsTmpNxt, show c.ws + 125 + 5 * c.nX + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsUsedList c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsTmpNxt, wsUsedList, show 7 < 2 ^ w by omega,
             show 7 * c.nX < 2 ^ w by omega, show c.ws + 125 + 6 * c.nX + 7 * c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsSBuf c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsUsedList, wsSBuf, show c.ws + 125 + 13 * c.nX + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsResOff c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsSBuf, wsResOff, show c.ws + 125 + 14 * c.nX + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_assign_le (v := wsResNb c.ws c.nX)
        (by simp [Expr.eval, BinOp.eval, hA1, wsResOff, wsResNb, show 1 < 2 ^ w by omega,
             show c.ws + 125 + 15 * c.nX + c.nX < 2 ^ w by omega,
             show c.ws + 125 + 15 * c.nX + c.nX + 1 < 2 ^ w by omega]; omega) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cB, h, ⟨rfl, rfl⟩, hcB⟩; exact ⟨cB, h, by omega⟩
  have hB1 : stB.regs 1 = c.nX := by simp [stB, regsB, hA1]
  have hB2 : stB.regs 2 = c.k := by simp [stB, regsB, hA2]
  have hB10 : stB.regs 10 = c.m2 := by simp [stB, regsB, hA10]
  have hB21 : stB.regs 21 = wsResNb c.ws c.nX := by simp [stB, regsB]
  set regsC :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    stB.regs 22 (wsLayerOffS c.ws c.nX c.m2 c.k)) 23 (wsLayerDataS c.ws c.nX c.m2 c.k))
    24 (wsLayerOffT c.ws c.nX c.m2 c.k)) 25 (wsLayerDataT c.ws c.nX c.m2 c.k))
    26 (wsBallStamp c.ws c.nX c.m2 c.k)) 27 (wsBallList c.ws c.nX c.m2 c.k))
    28 (wsLiveStamp c.ws c.nX c.m2 c.k)) 29 (wsSBallBuf c.ws c.nX c.m2 c.k))
    30 (wsTBallBuf c.ws c.nX c.m2 c.k)
  set stC : State := { stB with regs := regsC }
  have hC : ∃ cC,
      Runs w p ω
        (seqStmts
          [ .assign 22 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 21) (.reg 10))
              (.reg 1)) (.const 1)) (.bin .mul (.const 3) (.reg 2)))
          , .assign 23 (.bin .add (.bin .add (.reg 22) (.reg 1)) (.const 1))
          , .assign 24 (.bin .add (.reg 23) (.reg 1))
          , .assign 25 (.bin .add (.bin .add (.reg 24) (.reg 1)) (.const 1))
          , .assign 26 (.bin .add (.reg 25) (.reg 1))
          , .assign 27 (.bin .add (.reg 26) (.reg 1))
          , .assign 28 (.bin .add (.reg 27) (.reg 1))
          , .assign 29 (.bin .add (.reg 28) (.reg 1))
          , .assign 30 (.bin .add (.reg 29) (.reg 1)) ])
        stB .normal stC cC ∧ cC ≤ 80 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 22 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 21) (.reg 10))
                (.reg 1)) (.const 1)) (.bin .mul (.const 3) (.reg 2)))
            , .assign 23 (.bin .add (.bin .add (.reg 22) (.reg 1)) (.const 1))
            , .assign 24 (.bin .add (.reg 23) (.reg 1))
            , .assign 25 (.bin .add (.bin .add (.reg 24) (.reg 1)) (.const 1))
            , .assign 26 (.bin .add (.reg 25) (.reg 1))
            , .assign 27 (.bin .add (.reg 26) (.reg 1))
            , .assign 28 (.bin .add (.reg 27) (.reg 1))
            , .assign 29 (.bin .add (.reg 28) (.reg 1))
            , .assign 30 (.bin .add (.reg 29) (.reg 1)) ])
          stB o s c0 ∧ (o = .normal ∧ s = stC) ∧ 0 + c0 ≤ 80 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wsLayerOffS c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, hB2, hB10, hB21, wsResNb, wsLayerOffS,
             show 1 < 2 ^ w by omega, show 3 < 2 ^ w by omega, show 3 * c.k < 2 ^ w by omega,
             show c.ws + 126 + 16 * c.nX + c.m2 < 2 ^ w by omega,
             show c.ws + 126 + 16 * c.nX + c.m2 + c.nX < 2 ^ w by omega,
             show c.ws + 126 + 16 * c.nX + c.m2 + c.nX + 1 < 2 ^ w by omega,
             show c.ws + 126 + 16 * c.nX + c.m2 + c.nX + 1 + 3 * c.k < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLayerDataS c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsLayerOffS, wsLayerDataS, show 1 < 2 ^ w by omega,
             show c.ws + 127 + 17 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega,
             show c.ws + 127 + 17 * c.nX + c.m2 + 3 * c.k + c.nX + 1 < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLayerOffT c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsLayerDataS, wsLayerOffT,
             show c.ws + 128 + 18 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLayerDataT c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsLayerOffT, wsLayerDataT, show 1 < 2 ^ w by omega,
             show c.ws + 128 + 19 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega,
             show c.ws + 128 + 19 * c.nX + c.m2 + 3 * c.k + c.nX + 1 < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsBallStamp c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsLayerDataT, wsBallStamp,
             show c.ws + 129 + 20 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsBallList c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsBallStamp, wsBallList,
             show c.ws + 129 + 21 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsLiveStamp c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsBallList, wsLiveStamp,
             show c.ws + 129 + 22 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_seq_assign_le (v := wsSBallBuf c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsLiveStamp, wsSBallBuf,
             show c.ws + 129 + 23 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega) ?_
      refine runs_assign_le (v := wsTBallBuf c.ws c.nX c.m2 c.k)
        (by simp [Expr.eval, BinOp.eval, hB1, wsSBallBuf, wsTBallBuf,
             show c.ws + 129 + 24 * c.nX + c.m2 + 3 * c.k + c.nX < 2 ^ w by omega]; omega)
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cC, h, ⟨rfl, rfl⟩, hcC⟩; exact ⟨cC, h, by omega⟩
  rcases hA with ⟨cA, hrunA, hcA⟩
  rcases hB with ⟨cB, hrunB, hcB⟩
  rcases hC with ⟨cC, hrunC, hcC⟩
  obtain ⟨cBC, hrunBC, hcBC⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunB hrunC
  obtain ⟨cABC, hrunABC, hcABC⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA hrunBC
  refine ⟨stC, cABC, hrunABC, rfl, ?_, by simp at hcBC hcABC; omega⟩
  dsimp only [InitRegs]
  refine ⟨by simp [stC, regsC, stB, regsB, stA, regsA, hr0, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, stA, regsA, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, stA, regsA, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, stA, regsA, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, stA, regsA, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, stA, regsA, c], by simp [stC, regsC, stB, regsB, stA, regsA, c],
    by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c],
    by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c],
    by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, stB, regsB, c],
    by simp [stC, regsC, stB, regsB, c], by simp [stC, regsC, c], by simp [stC, regsC, c], by simp [stC, regsC, c],
    by simp [stC, regsC, c], by simp [stC, regsC, c], by simp [stC, regsC, c], by simp [stC, regsC, c],
    by simp [stC, regsC, c], by simp [stC, regsC, c]⟩

private lemma initSubCfgsSpBfs_triple {w : ℕ} {p : Program}
    {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {st0 : State} (hr : InitRegs st0.regs cfgAddr rcfg) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω initSubCfgsSpBfsStmt st0 .normal st1 c1 ∧
      st1.regs = st0.regs ∧
      (let c := rcfg.batch
       st1.mem (wsSpCfg c.ws + 0) = wsBfsCfg c.ws ∧
       st1.mem (wsSpCfg c.ws + 1) = wsDfsCfg c.ws ∧
       st1.mem (wsSpCfg c.ws + 2) = wsIsoStamp c.ws ∧
       st1.mem (wsSpCfg c.ws + 4) = wsUsedList c.ws c.nX ∧
       st1.mem (wsSpCfg c.ws + 5) = wsSBuf c.ws c.nX ∧
       st1.mem (wsSpCfg c.ws + 8) = c.d ∧
       st1.mem (wsBfsCfg c.ws + 0) = c.offAddr ∧
       st1.mem (wsBfsCfg c.ws + 1) = c.nbAddr ∧
       st1.mem (wsBfsCfg c.ws + 2) = wsIsoStamp c.ws ∧
       st1.mem (wsBfsCfg c.ws + 4) = 1 ∧
       st1.mem (wsBfsCfg c.ws + 5) = c.pairBAddr ∧
       st1.mem (wsBfsCfg c.ws + 7) = wsVisStamp c.ws c.nX ∧
       st1.mem (wsBfsCfg c.ws + 8) = wsDist c.ws c.nX ∧
       st1.mem (wsBfsCfg c.ws + 9) = wsLayerOff c.ws c.nX ∧
       st1.mem (wsBfsCfg c.ws + 10) = wsLayerData c.ws c.nX ∧
       st1.mem (wsBfsCfg c.ws + 11) = wsTmpNxt c.ws c.nX ∧
       st1.mem (wsBfsCfg c.ws + 13) = c.d ∧
       st1.mem (wsBfsCfg c.ws + 14) = wsSBuf c.ws c.nX) ∧
      (∀ a, ¬ (rcfg.batch.ws ≤ a ∧ a < rcfg.batch.ws + 35) → st1.mem a = st0.mem a) ∧
      c1 ≤ 180 := by
  intro ω
  set c := rcfg.batch
  have hw_ws : c.ws + (129 + 27 * c.nX + c.m2 + 3 * c.k) + 10 < 2 ^ w := hdisj.w_ws
  have hw4 := hdisj.w_4
  have hw_off : c.offAddr + c.nX + 5 < 2 ^ w := hdisj.w_off
  have hw_nb : c.nbAddr + c.m2 + 5 < 2 ^ w := hdisj.w_nb
  have hw_pb : c.pairBAddr + c.nX + 5 < 2 ^ w := hdisj.w_pb
  have hw_d : c.d + 5 < 2 ^ w := hdisj.w_d
  rcases hr with ⟨_, _, _, hr3, _, hr5, hr6, _, hr8, hr9, _, _, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, _⟩
  set mem1 :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update st0.mem
    (c.ws + 0) (c.ws + 20)) (c.ws + 1) (c.ws + 44)) (c.ws + 2) (wsIsoStamp c.ws))
    (c.ws + 4) (wsUsedList c.ws c.nX)) (c.ws + 5) (wsSBuf c.ws c.nX)) (c.ws + 8) c.d)
    (c.ws + 20) c.offAddr) (c.ws + 21) c.nbAddr) (c.ws + 22) (wsIsoStamp c.ws))
    (c.ws + 24) 1) (c.ws + 25) c.pairBAddr) (c.ws + 27) (wsVisStamp c.ws c.nX))
    (c.ws + 28) (wsDist c.ws c.nX)) (c.ws + 29) (wsLayerOff c.ws c.nX))
    (c.ws + 30) (wsLayerData c.ws c.nX)) (c.ws + 31) (wsTmpNxt c.ws c.nX))
    (c.ws + 33) c.d) (c.ws + 34) (wsSBuf c.ws c.nX)
  have h0 : ∃ o s c0, Runs w p ω initSubCfgsSpBfsStmt st0 o s c0 ∧
      (o = .normal ∧ s = { st0 with mem := mem1 }) ∧ 0 + c0 ≤ 180 := by
    dsimp only [initSubCfgsSpBfsStmt, seqStmts]
    refine runs_seq_store_le (x := c.ws + 0) (v := c.ws + 20) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 1) (v := c.ws + 44) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 2) (v := wsIsoStamp c.ws) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 4) (v := wsUsedList c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 5) (v := wsSBuf c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 8) (v := c.d) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 20) (v := c.offAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 21) (v := c.nbAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 22) (v := wsIsoStamp c.ws) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 24) (v := 1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 25) (v := c.pairBAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 27) (v := wsVisStamp c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 28) (v := wsDist c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 29) (v := wsLayerOff c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 30) (v := wsLayerData c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 31) (v := wsTmpNxt c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 33) (v := c.d) (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (x := c.ws + 34) (v := wsSBuf c.ws c.nX) (by eval_expr) (by eval_expr)
      ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  refine ⟨{ st0 with mem := mem1 }, c1, hrun1, rfl, ?_, ?_, by omega⟩
  · dsimp only [wsSpCfg, wsBfsCfg, wsDfsCfg, mem1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      dsimp only [c]
      try simp only [Nat.add_assoc, Nat.reduceAdd]
      repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)])
  · intro a ha
    dsimp only [mem1, c] at ha ⊢
    repeat rw [Function.update_of_ne (by omega)]

private lemma initSubCfgsDfs_triple {w : ℕ} {p : Program}
    {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {st0 : State} (hr : InitRegs st0.regs cfgAddr rcfg) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω initSubCfgsDfsStmt st0 .normal st1 c1 ∧
      st1.regs = st0.regs ∧
      (let c := rcfg.batch
       st1.mem (wsDfsCfg c.ws + 0) = c.offAddr ∧
       st1.mem (wsDfsCfg c.ws + 1) = c.nbAddr ∧
       st1.mem (wsDfsCfg c.ws + 2) = c.edgeAddr ∧
       st1.mem (wsDfsCfg c.ws + 3) = wsIsoStamp c.ws ∧
       st1.mem (wsDfsCfg c.ws + 5) = c.pairBAddr ∧
       st1.mem (wsDfsCfg c.ws + 7) = wsVisStamp c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 9) = wsDist c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 10) = wsCurStamp c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 11) = wsCurPtr c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 12) = wsUsedStamp c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 13) = wsDeadStamp c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 14) = wsStkVert c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 15) = wsStkEdge c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 16) = wsUsedList c.ws c.nX ∧
       st1.mem (wsDfsCfg c.ws + 19) = wsSBuf c.ws c.nX) ∧
      (∀ a, ¬ (rcfg.batch.ws + 44 ≤ a ∧ a < rcfg.batch.ws + 64) → st1.mem a = st0.mem a) ∧
      c1 ≤ 180 := by
  intro ω
  set c := rcfg.batch
  have hw_ws : c.ws + (129 + 27 * c.nX + c.m2 + 3 * c.k) + 10 < 2 ^ w := hdisj.w_ws
  have hw4 := hdisj.w_4
  have hw_off : c.offAddr + c.nX + 5 < 2 ^ w := hdisj.w_off
  have hw_nb : c.nbAddr + c.m2 + 5 < 2 ^ w := hdisj.w_nb
  have hw_edge : c.edgeAddr + c.m2 + 5 < 2 ^ w := hdisj.w_edge
  have hw_pb : c.pairBAddr + c.nX + 5 < 2 ^ w := hdisj.w_pb
  rcases hr with ⟨_, hr1, _, _, _, hr5, hr6, hr7, hr8, hr9, _, _, hr12, hr13, hr14, _, _, hr17, hr18, hr19, _⟩
  have hr17' : st0.regs 17 = c.ws + 125 + 6 * c.nX := hr17
  set mem1 :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update st0.mem
    (c.ws + 44) c.offAddr) (c.ws + 45) c.nbAddr) (c.ws + 46) c.edgeAddr)
    (c.ws + 47) (wsIsoStamp c.ws)) (c.ws + 49) c.pairBAddr) (c.ws + 51) (wsVisStamp c.ws c.nX))
    (c.ws + 53) (wsDist c.ws c.nX)) (c.ws + 54) (wsCurStamp c.ws c.nX))
    (c.ws + 55) (wsCurPtr c.ws c.nX)) (c.ws + 56) (wsUsedStamp c.ws c.nX))
    (c.ws + 57) (wsDeadStamp c.ws c.nX)) (c.ws + 58) (wsStkVert c.ws c.nX))
    (c.ws + 59) (wsStkEdge c.ws c.nX)) (c.ws + 60) (wsUsedList c.ws c.nX))
    (c.ws + 63) (wsSBuf c.ws c.nX)
  have h0 : ∃ o s c0, Runs w p ω initSubCfgsDfsStmt st0 o s c0 ∧
      (o = .normal ∧ s = { st0 with mem := mem1 }) ∧ 0 + c0 ≤ 180 := by
    dsimp only [initSubCfgsDfsStmt, seqStmts]
    refine runs_seq_store_le (x := c.ws + 44) (v := c.offAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 45) (v := c.nbAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 46) (v := c.edgeAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 47) (v := wsIsoStamp c.ws) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 49) (v := c.pairBAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 51) (v := wsVisStamp c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 53) (v := wsDist c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 54) (v := wsCurStamp c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsCurStamp, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 55) (v := wsCurPtr c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsCurPtr, show 2 < 2 ^ w by omega, show 2 * rcfg.batch.nX < 2 ^ w by omega, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + 2 * rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 56) (v := wsUsedStamp c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsUsedStamp, show 3 < 2 ^ w by omega, show 3 * rcfg.batch.nX < 2 ^ w by omega, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + 3 * rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 57) (v := wsDeadStamp c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsDeadStamp, show 4 < 2 ^ w by omega, show 4 * rcfg.batch.nX < 2 ^ w by omega, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + 4 * rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 58) (v := wsStkVert c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsStkVert, show 5 < 2 ^ w by omega, show 5 * rcfg.batch.nX < 2 ^ w by omega, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + 5 * rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 59) (v := wsStkEdge c.ws c.nX) (by eval_expr)
      (by dsimp only [c] at hw_ws hr17' ⊢; simp [Expr.eval, BinOp.eval, hr17', hr1, wsStkEdge, show 6 < 2 ^ w by omega, show 6 * rcfg.batch.nX < 2 ^ w by omega, show rcfg.batch.ws + 125 + 6 * rcfg.batch.nX + 6 * rcfg.batch.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_store_le (x := c.ws + 60) (v := wsUsedList c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (x := c.ws + 63) (v := wsSBuf c.ws c.nX) (by eval_expr) (by eval_expr)
      ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  refine ⟨{ st0 with mem := mem1 }, c1, hrun1, rfl, ?_, ?_, by omega⟩
  · dsimp only [wsDfsCfg, mem1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      dsimp only [c]
      try simp only [Nat.add_assoc, Nat.reduceAdd]
      repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)])
  · intro a ha
    dsimp only [mem1, c] at ha ⊢
    repeat rw [Function.update_of_ne (by omega)]

private lemma initSubCfgsBall_triple {w : ℕ} {p : Program}
    {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {st0 : State} (hr : InitRegs st0.regs cfgAddr rcfg) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω initSubCfgsBallStmt st0 .normal st1 c1 ∧
      st1.regs = st0.regs ∧
      (let c := rcfg.batch
       st1.mem (wsBallCfg c.ws + 0) = wsBfsBallCfg c.ws ∧
       st1.mem (wsBallCfg c.ws + 1) = wsResOff c.ws c.nX ∧
       st1.mem (wsBallCfg c.ws + 2) = wsResNb c.ws c.nX ∧
       st1.mem (wsBallCfg c.ws + 3) = wsLiveStamp c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 5) = wsLayerOffS c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 6) = wsLayerDataS c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 7) = wsLayerOffT c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 8) = wsLayerDataT c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 9) = wsSBallBuf c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 11) = wsTBallBuf c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 13) = wsBallStamp c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 14) = wsBallList c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBallCfg c.ws + 17) = c.b ∧
       st1.mem (wsBfsBallCfg c.ws + 0) = wsResOff c.ws c.nX ∧
       st1.mem (wsBfsBallCfg c.ws + 1) = wsResNb c.ws c.nX ∧
       st1.mem (wsBfsBallCfg c.ws + 2) = wsLiveStamp c.ws c.nX c.m2 c.k ∧
       st1.mem (wsBfsBallCfg c.ws + 4) = 0 ∧
       st1.mem (wsBfsBallCfg c.ws + 5) = 0 ∧
       st1.mem (wsBfsBallCfg c.ws + 6) = 0 ∧
       st1.mem (wsBfsBallCfg c.ws + 7) = wsVisStamp c.ws c.nX ∧
       st1.mem (wsBfsBallCfg c.ws + 8) = wsDist c.ws c.nX ∧
       st1.mem (wsBfsBallCfg c.ws + 11) = wsTmpNxt c.ws c.nX ∧
       st1.mem (wsBfsBallCfg c.ws + 13) = rcfg.hL) ∧
      (∀ a, ¬ (rcfg.batch.ws + 76 ≤ a ∧ a < rcfg.batch.ws + 114) → st1.mem a = st0.mem a) ∧
      c1 ≤ 220 := by
  intro ω
  set c := rcfg.batch
  have hw_ws : c.ws + (129 + 27 * c.nX + c.m2 + 3 * c.k) + 10 < 2 ^ w := hdisj.w_ws
  have hw4 := hdisj.w_4
  have hw_b16 : 16 * c.b + 5 < 2 ^ w := hdisj.w_b16; have hw_hL := hdisj.w_hL
  rcases hr with ⟨_, _, _, _, hr4, _, _, _, _, hr9, _, hr11, _, hr13, hr14, _, _, hr17, _, _, hr20, hr21,
    hr22, hr23, hr24, hr25, hr26, hr27, hr28, hr29, hr30⟩
  set mem1 :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update st0.mem
    (c.ws + 76) (c.ws + 100)) (c.ws + 77) (wsResOff c.ws c.nX)) (c.ws + 78) (wsResNb c.ws c.nX))
    (c.ws + 79) (wsLiveStamp c.ws c.nX c.m2 c.k)) (c.ws + 81) (wsLayerOffS c.ws c.nX c.m2 c.k))
    (c.ws + 82) (wsLayerDataS c.ws c.nX c.m2 c.k)) (c.ws + 83) (wsLayerOffT c.ws c.nX c.m2 c.k))
    (c.ws + 84) (wsLayerDataT c.ws c.nX c.m2 c.k)) (c.ws + 85) (wsSBallBuf c.ws c.nX c.m2 c.k))
    (c.ws + 87) (wsTBallBuf c.ws c.nX c.m2 c.k)) (c.ws + 89) (wsBallStamp c.ws c.nX c.m2 c.k))
    (c.ws + 90) (wsBallList c.ws c.nX c.m2 c.k)) (c.ws + 93) c.b)
    (c.ws + 100) (wsResOff c.ws c.nX)) (c.ws + 101) (wsResNb c.ws c.nX))
    (c.ws + 102) (wsLiveStamp c.ws c.nX c.m2 c.k)) (c.ws + 104) 0) (c.ws + 105) 0)
    (c.ws + 106) 0) (c.ws + 107) (wsVisStamp c.ws c.nX)) (c.ws + 108) (wsDist c.ws c.nX))
    (c.ws + 111) (wsTmpNxt c.ws c.nX)) (c.ws + 113) rcfg.hL
  have h0 : ∃ o s c0, Runs w p ω initSubCfgsBallStmt st0 o s c0 ∧
      (o = .normal ∧ s = { st0 with mem := mem1 }) ∧ 0 + c0 ≤ 220 := by
    dsimp only [initSubCfgsBallStmt, seqStmts]
    refine runs_seq_store_le (x := c.ws + 76) (v := c.ws + 100) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 77) (v := wsResOff c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 78) (v := wsResNb c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 79) (v := wsLiveStamp c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 81) (v := wsLayerOffS c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 82) (v := wsLayerDataS c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 83) (v := wsLayerOffT c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 84) (v := wsLayerDataT c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 85) (v := wsSBallBuf c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 87) (v := wsTBallBuf c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 89) (v := wsBallStamp c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 90) (v := wsBallList c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 93) (v := c.b) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 100) (v := wsResOff c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 101) (v := wsResNb c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 102) (v := wsLiveStamp c.ws c.nX c.m2 c.k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 104) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 105) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 106) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 107) (v := wsVisStamp c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 108) (v := wsDist c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := c.ws + 111) (v := wsTmpNxt c.ws c.nX) (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (x := c.ws + 113) (v := rcfg.hL) (by eval_expr) (by eval_expr)
      ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  refine ⟨{ st0 with mem := mem1 }, c1, hrun1, rfl, ?_, ?_, by omega⟩
  · dsimp only [wsBallCfg, wsBfsBallCfg, mem1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      dsimp only [c]
      try simp only [Nat.add_assoc, Nat.reduceAdd]
      repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)])
  · intro a ha
    dsimp only [mem1, c] at ha ⊢
    repeat rw [Function.update_of_ne (by omega)]

/-- Verification of `initBatchSubCfgsStmt`: establishes `BatchSubCfgsInit` in `≤ 860` steps,
modifying only `[ws, ws + 124)` and preserving `reg 0 = cfgAddr`. -/
theorem initBatchSubCfgs_triple {w : ℕ} {p : Program}
    {cfgAddr pLo pHi cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    {st0 : State} (hcfg : RouteLoopCfgAt st0.mem cfgAddr rcfg) (hr0 : st0.regs 0 = cfgAddr) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω initBatchSubCfgsStmt st0 .normal st1 c1 ∧
      st1.regs 0 = cfgAddr ∧
      BatchSubCfgsInit st1.mem rcfg.batch rcfg.hL ∧
      (∀ a, ¬ (rcfg.batch.ws ≤ a ∧ a < rcfg.batch.ws + 124) → st1.mem a = st0.mem a) ∧
      c1 ≤ 900 := by
  intro ω
  obtain ⟨st1, c1, hrun1, hmem1, hr1, hc1⟩ := initSubCfgsLoad_triple hdisj hcfg hr0 ω
  obtain ⟨st2, c2, hrun2, hreg2, hsb2, hfr2, hc2⟩ := initSubCfgsSpBfs_triple hdisj hr1 ω
  have hr2 : InitRegs st2.regs cfgAddr rcfg := hreg2 ▸ hr1
  obtain ⟨st3, c3, hrun3, hreg3, hsb3, hfr3, hc3⟩ := initSubCfgsDfs_triple hdisj hr2 ω
  have hr3 : InitRegs st3.regs cfgAddr rcfg := hreg3 ▸ hr2
  obtain ⟨st4, c4, hrun4, hreg4, hsb4, hfr4, hc4⟩ := initSubCfgsBall_triple hdisj hr3 ω
  have hrun34 : Runs w p ω (Stmt.seq initSubCfgsDfsStmt initSubCfgsBallStmt) st2 .normal st4 (c3 + c4 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st3, c3, c4, hrun3, hrun4, rfl⟩)
  have hrun24 : Runs w p ω (Stmt.seq initSubCfgsSpBfsStmt (Stmt.seq initSubCfgsDfsStmt initSubCfgsBallStmt))
      st1 .normal st4 (c2 + (c3 + c4 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hrun34, rfl⟩)
  have hrunAll : Runs w p ω initBatchSubCfgsStmt st0 .normal st4 (c1 + (c2 + (c3 + c4 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, hrun24, rfl⟩)
  have h4_eq_2 : ∀ a, a < rcfg.batch.ws + 35 → st4.mem a = st2.mem a := fun a ha =>
    (hfr4 a (by omega)).trans (hfr3 a (by omega))
  have h4_eq_3 : ∀ a, a < rcfg.batch.ws + 64 → st4.mem a = st3.mem a := fun a ha =>
    hfr4 a (by omega)
  refine ⟨st4, _, hrunAll, by rw [hreg4, hreg3, hreg2]; exact hr1.1, ?_, ?_, by omega⟩
  · rcases hsb2 with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
    rcases hsb3 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩
    rcases hsb4 with ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22⟩
    all_goals first
      | rwa [h4_eq_2 _ (by simp only [wsSpCfg, wsBfsCfg]; omega)]
      | rwa [h4_eq_3 _ (by simp only [wsDfsCfg]; omega)]
  · intro a ha
    rw [hfr4 a (by omega), hfr3 a (by omega), hfr2 a (by omega), hmem1]

/-! ## 2. `emitEmptyMatchedRet_triple` -/

/-- Verification of `emitEmptyMatchedRetStmt`: writes empty `RouteOutAt` at `outAddr` and empty
`WalksAt` at `walksAddr` and returns `0` in `≤ 60` steps. -/
theorem emitEmptyMatchedRet_triple {w : ℕ} {p : Program}
    {cfgAddr outAddr walksAddr k : ℕ}
    (hw_cfg : cfgAddr + 36 < 2 ^ w) (hw_out : outAddr + 2 < 2 ^ w)
    (_hw_walks : walksAddr + 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hout_walks : DisjRange outAddr 2 walksAddr 1)
    {st0 : State} (hm30 : st0.mem (cfgAddr + 30) = outAddr)
    (hm31 : st0.mem (cfgAddr + 31) = walksAddr) (hr0 : st0.regs 0 = cfgAddr) :
    ∀ ω, ∃ st1 c1,
      Runs w p ω emitEmptyMatchedRetStmt st0 (.returned 0) st1 c1 ∧
      RouteOutAt st1.mem outAddr (.matched (List.replicate k []) (fun _ => [])) ∧
      WalksAt st1.mem walksAddr 0 (fun _ => []) ∧
      (∀ a, a ≠ outAddr → a ≠ outAddr + 1 → a ≠ walksAddr → st1.mem a = st0.mem a) ∧
      c1 ≤ 60 := by
  intro ω
  set regs1 := Function.update (Function.update st0.regs 8 outAddr) 9 walksAddr
  set mem1 := Function.update (Function.update (Function.update st0.mem outAddr 0) (outAddr + 1) 0) walksAddr 0
  set st1 : State := { mem := mem1, regs := regs1, pos := st0.pos }
  have h0 : ∃ o s c0, Runs w p ω emitEmptyMatchedRetStmt st0 o s c0 ∧
      (o = .returned 0 ∧ s = st1) ∧ 0 + c0 ≤ 60 := by
    dsimp only [emitEmptyMatchedRetStmt, seqStmts]
    refine runs_seq_assign_le (v := outAddr) (by rw [← hm30]; eval_expr) ?_
    refine runs_seq_assign_le (v := walksAddr) (by rw [← hm31]; eval_expr) ?_
    refine runs_seq_store_le (x := outAddr) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := outAddr + 1) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := walksAddr) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
  unfold DisjRange at hout_walks
  have hflat : (List.replicate k ([] : List (ℕ × ℕ))).flatten = [] := by
    induction k with | zero => rfl | succ k _ => simp
  refine ⟨st1, c1, hrun1, ?_, ?_, ?_, by omega⟩
  · dsimp only [RouteOutAt]
    rw [hflat]
    refine ⟨?_, ?_, ?_⟩
    · simp only [st1, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · simp only [st1, mem1]; rw [Function.update_of_ne (by omega), Function.update_self]; rfl
    · intro i hi; exact absurd hi (Nat.not_lt_zero _)
  · refine ⟨by simp only [st1, mem1]; rw [Function.update_self], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · intro a h1 h2 h3
    simp only [st1, mem1]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]

end MinCostFlow.ExpanderDecomp
