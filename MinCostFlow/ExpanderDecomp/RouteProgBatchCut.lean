module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchBall

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Failed-Branch (Cut-Finding) Verification (`RouteProgBatchCut`)

Verifies `batchCutBranchStmt`: invokes `buildResCsrProc` and `buildCurBProc`, initializes the
ball-growing loop registers, runs `batchBallLoopStmt`, stores the cut outputs into `cfgAddr`, and
returns `1`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma batchCutPreRes_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg} {cfgAddr : ℕ}
    (hw_cfg : cfgAddr + 30 < 2 ^ w)
    (hw_ws : cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k + 10 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (h5 : st0.mem (cfgAddr + 5) = cfg.offAddr)
    (h6 : st0.mem (cfgAddr + 6) = cfg.nbAddr)
    (h15 : st0.mem (cfgAddr + 15) = cfg.m2)
    (hr0 : st0.regs 0 = cfgAddr) (hr1 : st0.regs 1 = cfg.nX) (hr14 : st0.regs 14 = cfg.ws) :
    ∀ ω,
      let st1 : State :=
        { st0 with
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update st0.regs 3 cfg.offAddr) 4 cfg.nbAddr)
            5 cfg.m2) 6 (wsIsoStamp cfg.ws)) 7 (wsResOff cfg.ws cfg.nX))
            22 (wsResNb cfg.ws cfg.nX) }
      ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 3 (.load (.bin .add (.reg 0) (.const 5)))
            , .assign 4 (.load (.bin .add (.reg 0) (.const 6)))
            , .assign 5 (.load (.bin .add (.reg 0) (.const 15)))
            , .assign 6 (.bin .add (.reg 14) (.const 124))
            , .assign 7 (.bin .add (.bin .add (.reg 14) (.const 125)) (.bin .mul (.const 15) (.reg 1)))
            , .assign 22 (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 1)) ])
          st0 .normal st1 c1 ∧ c1 ≤ 55 := by
  intro ω
  have hS : batchScratchSize cfg.nX cfg.m2 cfg.k = 129 + 27 * cfg.nX + cfg.m2 + 3 * cfg.k := rfl
  set st1 : State :=
    { st0 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st0.regs 3 cfg.offAddr) 4 cfg.nbAddr)
        5 cfg.m2) 6 (wsIsoStamp cfg.ws)) 7 (wsResOff cfg.ws cfg.nX))
        22 (wsResNb cfg.ws cfg.nX) }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .assign 3 (.load (.bin .add (.reg 0) (.const 5)))
          , .assign 4 (.load (.bin .add (.reg 0) (.const 6)))
          , .assign 5 (.load (.bin .add (.reg 0) (.const 15)))
          , .assign 6 (.bin .add (.reg 14) (.const 124))
          , .assign 7 (.bin .add (.bin .add (.reg 14) (.const 125)) (.bin .mul (.const 15) (.reg 1)))
          , .assign 22 (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 1)) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 55 := by
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := cfg.offAddr) (by rw [← h5]; eval_expr) ?_
    refine runs_seq_assign_le (v := cfg.nbAddr) (by rw [← h6]; eval_expr) ?_
    refine runs_seq_assign_le (v := cfg.m2) (by rw [← h15]; eval_expr) ?_
    refine runs_seq_assign_le (v := wsIsoStamp cfg.ws)
      (by unfold wsIsoStamp; eval_expr) ?_
    refine runs_seq_assign_le (v := wsResOff cfg.ws cfg.nX)
      (by unfold wsResOff; eval_expr) ?_
    refine runs_assign_le (v := wsResNb cfg.ws cfg.nX)
      (by simp only [Expr.eval, BinOp.eval, Function.update_self,
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 7),
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 6),
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 5),
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 4),
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 3), hr1, wsResOff, wsResNb]
          have h1 : 1 < 2 ^ w := by omega
          have h2 : cfg.ws + 125 + 15 * cfg.nX + 1 < 2 ^ w := by omega
          have h3 : cfg.ws + 125 + 15 * cfg.nX + 1 + cfg.nX < 2 ^ w := by omega
          simp [h1, h2, h3]; omega) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩

private lemma batchCutPreCurB_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg}
    (hw_ws : cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k + 10 < 2 ^ w)
    {st0 : State}
    (hr1 : st0.regs 1 = cfg.nX) (hr2 : st0.regs 2 = cfg.k)
    (hr5 : st0.regs 5 = cfg.m2) (hr22 : st0.regs 22 = wsResNb cfg.ws cfg.nX) :
    ∀ ω,
      let st1 : State :=
        { st0 with
          regs := Function.update (Function.update (Function.update (Function.update st0.regs
            17 (wsBOff cfg.ws cfg.nX cfg.m2))
            20 (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k))
            21 (wsBData cfg.ws cfg.nX cfg.m2 cfg.k))
            24 (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) }
      ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 17 (.bin .add (.reg 22) (.reg 5))
            , .assign 20 (.bin .add (.bin .add (.reg 17) (.const 1)) (.reg 2))
            , .assign 21 (.bin .add (.reg 20) (.reg 2))
            , .assign 24 (.bin .add (.reg 21) (.reg 1)) ])
          st0 .normal st1 c1 ∧ c1 ≤ 30 := by
  intro ω
  have hS : batchScratchSize cfg.nX cfg.m2 cfg.k = 129 + 27 * cfg.nX + cfg.m2 + 3 * cfg.k := rfl
  set st1 : State :=
    { st0 with
      regs := Function.update (Function.update (Function.update (Function.update st0.regs
        17 (wsBOff cfg.ws cfg.nX cfg.m2))
        20 (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k))
        21 (wsBData cfg.ws cfg.nX cfg.m2 cfg.k))
        24 (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .assign 17 (.bin .add (.reg 22) (.reg 5))
          , .assign 20 (.bin .add (.bin .add (.reg 17) (.const 1)) (.reg 2))
          , .assign 21 (.bin .add (.reg 20) (.reg 2))
          , .assign 24 (.bin .add (.reg 21) (.reg 1)) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 30 := by
    dsimp only [seqStmts]
    unfold wsResNb at hr22
    refine runs_seq_assign_le (v := wsBOff cfg.ws cfg.nX cfg.m2)
      (by simp [Expr.eval, BinOp.eval, hr22, hr5, wsBOff, show cfg.ws + 126 + 16 * cfg.nX + cfg.m2 < 2 ^ w by omega]) ?_
    refine runs_seq_assign_le (v := wsBLen cfg.ws cfg.nX cfg.m2 cfg.k)
      (by simp [Expr.eval, BinOp.eval, hr2, wsBOff, wsBLen, show 1 < 2 ^ w by omega,
            show cfg.ws + 126 + 16 * cfg.nX + cfg.m2 + 1 < 2 ^ w by omega,
            show cfg.ws + 126 + 16 * cfg.nX + cfg.m2 + 1 + cfg.k < 2 ^ w by omega]; omega) ?_
    refine runs_seq_assign_le (v := wsBData cfg.ws cfg.nX cfg.m2 cfg.k)
      (by simp [Expr.eval, BinOp.eval, hr2, wsBLen, wsBData,
            show cfg.ws + 127 + 16 * cfg.nX + cfg.m2 + cfg.k + cfg.k < 2 ^ w by omega]; omega) ?_
    refine runs_assign_le (v := wsBCur cfg.ws cfg.nX cfg.m2 cfg.k)
      (by simp [Expr.eval, BinOp.eval, hr1, wsBData, wsBCur,
            show cfg.ws + 127 + 16 * cfg.nX + cfg.m2 + 2 * cfg.k + cfg.nX < 2 ^ w by omega]; omega) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩

private lemma batchCutPreBall_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg} {cfgAddr : ℕ}
    (hw_cfg : cfgAddr + 30 < 2 ^ w)
    (hw_ws : cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k + 10 < 2 ^ w)
    (hw_lg : cfg.liveGenIn + 5 < 2 ^ w)
    {st0 : State}
    (h20 : st0.mem (cfgAddr + 20) = cfg.ballGenIn)
    (h21 : st0.mem (cfgAddr + 21) = cfg.liveGenIn)
    (hb3 : st0.mem (wsBallCfg cfg.ws + 3) = wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k)
    (hb9 : st0.mem (wsBallCfg cfg.ws + 9) = wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k)
    (hb11 : st0.mem (wsBallCfg cfg.ws + 11) = wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k)
    (hb14 : st0.mem (wsBallCfg cfg.ws + 14) = wsBallList cfg.ws cfg.nX cfg.m2 cfg.k)
    (hr0 : st0.regs 0 = cfgAddr) (hr1 : st0.regs 1 = cfg.nX) (hr14 : st0.regs 14 = cfg.ws) :
    ∀ ω,
      let st1 : State :=
        { st0 with
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update st0.regs
              15 (wsBallCfg cfg.ws)) 16 (wsBfsBallCfg cfg.ws))
              19 cfg.ballGenIn) 22 (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k))
              23 (cfg.liveGenIn + 1)) 33 (wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
              34 (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
              35 (wsBallList cfg.ws cfg.nX cfg.m2 cfg.k))
              36 (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)) 31 0) 32 0 }
      ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 15 (.bin .add (.reg 14) (.const 76))
            , .assign 16 (.bin .add (.reg 14) (.const 100))
            , .assign 19 (.load (.bin .add (.reg 0) (.const 20)))
            , .assign 22 (.load (.bin .add (.reg 15) (.const 3)))
            , .assign 23 (.bin .add (.load (.bin .add (.reg 0) (.const 21))) (.const 1))
            , .assign 33 (.load (.bin .add (.reg 15) (.const 9)))
            , .assign 34 (.load (.bin .add (.reg 15) (.const 11)))
            , .assign 35 (.load (.bin .add (.reg 15) (.const 14)))
            , .assign 36 (.bin .add (.reg 34) (.reg 1))
            , .assign 31 (.const 0)
            , .assign 32 (.const 0) ])
          st0 .normal st1 c1 ∧ c1 ≤ 80 := by
  intro ω
  have hS : batchScratchSize cfg.nX cfg.m2 cfg.k = 129 + 27 * cfg.nX + cfg.m2 + 3 * cfg.k := rfl
  set st1 : State :=
    { st0 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update st0.regs
          15 (wsBallCfg cfg.ws)) 16 (wsBfsBallCfg cfg.ws))
          19 cfg.ballGenIn) 22 (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k))
          23 (cfg.liveGenIn + 1)) 33 (wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
          34 (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
          35 (wsBallList cfg.ws cfg.nX cfg.m2 cfg.k))
          36 (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)) 31 0) 32 0 }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .assign 15 (.bin .add (.reg 14) (.const 76))
          , .assign 16 (.bin .add (.reg 14) (.const 100))
          , .assign 19 (.load (.bin .add (.reg 0) (.const 20)))
          , .assign 22 (.load (.bin .add (.reg 15) (.const 3)))
          , .assign 23 (.bin .add (.load (.bin .add (.reg 0) (.const 21))) (.const 1))
          , .assign 33 (.load (.bin .add (.reg 15) (.const 9)))
          , .assign 34 (.load (.bin .add (.reg 15) (.const 11)))
          , .assign 35 (.load (.bin .add (.reg 15) (.const 14)))
          , .assign 36 (.bin .add (.reg 34) (.reg 1))
          , .assign 31 (.const 0)
          , .assign 32 (.const 0) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 80 := by
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := wsBallCfg cfg.ws) (by unfold wsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := wsBfsBallCfg cfg.ws) (by unfold wsBfsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := cfg.ballGenIn) (by rw [← h20]; eval_expr) ?_
    refine runs_seq_assign_le (v := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k)
      (by rw [← hb3]; unfold wsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := cfg.liveGenIn + 1)
      (by simp [Expr.eval, BinOp.eval, hr0, show 21 < 2 ^ w by omega,
           show cfgAddr + 21 < 2 ^ w by omega, h21, show 1 < 2 ^ w by omega,
           show cfg.liveGenIn + 1 < 2 ^ w by omega]) ?_
    refine runs_seq_assign_le (v := wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k)
      (by rw [← hb9]; unfold wsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k)
      (by rw [← hb11]; unfold wsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := wsBallList cfg.ws cfg.nX cfg.m2 cfg.k)
      (by rw [← hb14]; unfold wsBallCfg; eval_expr) ?_
    refine runs_seq_assign_le (v := wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)
      (by simp [Expr.eval, BinOp.eval, hr1, wsTBallBuf, wsCutList,
            show cfg.ws + 129 + 25 * cfg.nX + cfg.m2 + 3 * cfg.k + cfg.nX < 2 ^ w by omega]; omega) ?_
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩

private lemma batchCutRet_triple {w : ℕ} {p : Program}
    {cfgAddr bfsGenF ballGenF liveGen1 cutSize : ℕ}
    (hw_cfg : cfgAddr + 30 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr) (hr18 : st0.regs 18 = bfsGenF)
    (hr19 : st0.regs 19 = ballGenF) (hr23 : st0.regs 23 = liveGen1)
    (hr32 : st0.regs 32 = cutSize) :
    ∀ ω,
      let memF := Function.update (Function.update (Function.update (Function.update
        (Function.update st0.mem (cfgAddr + 18) bfsGenF) (cfgAddr + 20) ballGenF)
        (cfgAddr + 21) liveGen1) (cfgAddr + 24) 1) (cfgAddr + 25) cutSize
      ∃ cF,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
            , .store (.bin .add (.reg 0) (.const 20)) (.reg 19)
            , .store (.bin .add (.reg 0) (.const 21)) (.reg 23)
            , .store (.bin .add (.reg 0) (.const 24)) (.const 1)
            , .store (.bin .add (.reg 0) (.const 25)) (.reg 32)
            , .ret (.const 1) ])
          st0 (.returned 1) { st0 with mem := memF } cF ∧ cF ≤ 45 := by
  intro ω
  set memF := Function.update (Function.update (Function.update (Function.update
    (Function.update st0.mem (cfgAddr + 18) bfsGenF) (cfgAddr + 20) ballGenF)
    (cfgAddr + 21) liveGen1) (cfgAddr + 24) 1) (cfgAddr + 25) cutSize
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
          , .store (.bin .add (.reg 0) (.const 20)) (.reg 19)
          , .store (.bin .add (.reg 0) (.const 21)) (.reg 23)
          , .store (.bin .add (.reg 0) (.const 24)) (.const 1)
          , .store (.bin .add (.reg 0) (.const 25)) (.reg 32)
          , .ret (.const 1) ])
        st0 o s c ∧ (o = .returned 1 ∧ s = { st0 with mem := memF }) ∧ 0 + c ≤ 45 := by
    dsimp only [seqStmts]
    refine runs_seq_store_le (x := cfgAddr + 18) (v := bfsGenF) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 20) (v := ballGenF) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 21) (v := liveGen1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 24) (v := 1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 25) (v := cutSize) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, cF, h, ⟨rfl, rfl⟩, hcF⟩; exact ⟨cF, h, by omega⟩

/-- Full verification of `batchCutBranchStmt`: builds residual CSR and sorted `curB`, runs
`batchBallLoopStmt`, stores outputs to `cfgAddr`, and returns `1`. -/
theorem batchCutBranch_triple {w : ℕ} {p : Program} {bRes bCurB bBall bBfs : ℕ}
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    {G : Graph} {X V_res : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL h L : ℕ}
    {remPairs : List (Finset ℕ × Finset ℕ)}
    {bfsGen0 dfsGen0 pathHeap0 chunkHeap0 : ℕ} {mem0 : ℕ → ℕ} {st0 : State}
    (hhL : h * L = hL)
    (hnX : cfg.nX = X.card) (hk : cfg.k = remPairs.length)
    (hVX_res : V_res ⊆ X)
    (hvalid : ValidTerminalPairs X remPairs)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hbfs_lo : cfg.bfsGenIn ≤ bfsGen0) (hbfs_hi : bfsGen0 ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 1))
    (_hdfs_lo : cfg.dfsGenIn ≤ dfsGen0) (_hdfs_hi : dfsGen0 ≤ cfg.dfsGenIn + cfg.k * (cfg.d + 1))
    (_hp_lo : cfg.pathHeapIn ≤ pathHeap0) (_hp_hi : pathHeap0 ≤ cfg.pathHeapIn + 5 * cfg.nX)
    (_hc_lo : cfg.chunkHeapIn ≤ chunkHeap0) (_hc_hi : chunkHeap0 ≤ cHi)
    (hcfg_static : ∀ o < 16, st0.mem (cfgAddr + o) = mem0 (cfgAddr + o))
    (hcfg5 : mem0 (cfgAddr + 5) = cfg.offAddr)
    (hcfg6 : mem0 (cfgAddr + 6) = cfg.nbAddr)
    (hcfg15 : mem0 (cfgAddr + 15) = cfg.m2)
    (hcfg17 : st0.mem (cfgAddr + 17) = cfg.batchGenIn + 1)
    (hcfg19 : st0.mem (cfgAddr + 19) = dfsGen0)
    (hcfg20 : st0.mem (cfgAddr + 20) = cfg.ballGenIn)
    (hcfg21 : st0.mem (cfgAddr + 21) = cfg.liveGenIn)
    (hcfg22 : st0.mem (cfgAddr + 22) = pathHeap0)
    (hcfg23 : st0.mem (cfgAddr + 23) = chunkHeap0)
    (hcsr : AdjCsrAt st0.mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X))
    (hlp : LocalPairsAt st0.mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X remPairs X.card)
    (hiso : ∀ v < X.card, st0.mem (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔ origOf X v ∈ V_res)
    (hiso_le : ∀ v < X.card, st0.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1)
    (hma_le : ∀ v < X.card, st0.mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1)
    (hvis_le : ∀ v < X.card, st0.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen0)
    (hcur_le : ∀ v < X.card, st0.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen0)
    (hused_le : ∀ v < X.card, st0.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen0)
    (hdead_le : ∀ v < X.card, st0.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen0)
    (hball_le : ∀ v < X.card, st0.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.ballGenIn)
    (hlive_le : ∀ v < X.card, st0.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn)
    (hsub : BatchSubCfgsInit st0.mem cfg hL)
    (hfr0 : ∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → st0.mem a = mem0 a)
    (hr0 : st0.regs 0 = cfgAddr) (hr1 : st0.regs 1 = cfg.nX) (hr2 : st0.regs 2 = cfg.k)
    (hr8 : st0.regs 8 = cfg.pairBAddr) (hr9 : st0.regs 9 = cfg.aOffAddr)
    (hr10 : st0.regs 10 = cfg.aLenAddr) (hr11 : st0.regs 11 = cfg.aDataAddr)
    (hr14 : st0.regs 14 = cfg.ws) (hr17 : st0.regs 17 = cfg.batchGenIn + 1)
    (hr18 : st0.regs 18 = bfsGen0) :
    ∀ ω,
      let Hres : Graph := ⟨G.n, G.inside V_res⟩
      let cutRes := batchBallLoop (adjOf Hres X) X cfg.b h L remPairs ∅ X 0
      ∃ stF c,
        Runs w p ω (batchCutBranchStmt bRes bCurB bBall) st0 (.returned 1) stF c ∧
        stF.mem (cfgAddr + 17) = cfg.batchGenIn + 1 ∧
        cfg.bfsGenIn ≤ stF.mem (cfgAddr + 18) ∧
        stF.mem (cfgAddr + 18) ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3) ∧
        stF.mem (cfgAddr + 19) = dfsGen0 ∧
        cfg.ballGenIn ≤ stF.mem (cfgAddr + 20) ∧
        stF.mem (cfgAddr + 20) ≤ cfg.ballGenIn + cfg.k ∧
        stF.mem (cfgAddr + 21) = cfg.liveGenIn + 1 ∧
        stF.mem (cfgAddr + 22) = pathHeap0 ∧
        stF.mem (cfgAddr + 23) = chunkHeap0 ∧
        stF.mem (cfgAddr + 24) = 1 ∧
        stF.mem (cfgAddr + 25) = cutRes.1.card ∧
        (∀ v < X.card, stF.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1) ∧
        (∀ v < X.card, stF.mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1) ∧
        (∀ v < X.card, stF.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ stF.mem (cfgAddr + 18)) ∧
        (∀ v < X.card, stF.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen0) ∧
        (∀ v < X.card, stF.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen0) ∧
        (∀ v < X.card, stF.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen0) ∧
        (∀ v < X.card, stF.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ stF.mem (cfgAddr + 20)) ∧
        (∀ v < X.card, stF.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn + 1) ∧
        BatchSubCfgsInit stF.mem cfg hL ∧
        (∃ ul : List ℕ, ul.length = cutRes.1.card ∧ ul.Nodup ∧
          (∀ x ∈ ul, x < X.card ∧ origOf X x ∈ cutRes.1) ∧
          (∀ v ∈ cutRes.1, v ∈ X ∧ locOf X v ∈ ul) ∧
          ListAt stF.mem (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k) ul) ∧
        (∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → stF.mem a = mem0 a) ∧
        c ≤ buildResCsrCost X.card cfg.m2 + buildCurBCost X.card cfg.k +
            1050 * cutRes.2 + 85 * X.card + 280 := by
  intro ω Hres cutRes
  have hw_cfg := hdisj.w_cfg; have hw_ws := hdisj.w_ws; have hw4 := hdisj.w_4
  -- Stage 1: pre-resCsr assigns
  obtain ⟨c1, hrun1, hc1⟩ := batchCutPreRes_triple (w := w) (p := p) hw_cfg hw_ws hw4
    ((hcfg_static 5 (by decide)).trans hcfg5)
    ((hcfg_static 6 (by decide)).trans hcfg6)
    ((hcfg_static 15 (by decide)).trans hcfg15) hr0 hr1 hr14 ω
  set st1 : State :=
    { st0 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st0.regs 3 cfg.offAddr) 4 cfg.nbAddr)
        5 cfg.m2) 6 (wsIsoStamp cfg.ws)) 7 (wsResOff cfg.ws cfg.nX))
        22 (wsResNb cfg.ws cfg.nX) }
  -- Stage 2: call bRes
  have hresDisj : ResCsrDisj w X.card cfg.m2 cfg.offAddr cfg.nbAddr (wsIsoStamp cfg.ws)
      (cfg.batchGenIn + 1) (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) := by
    rw [← hnX]; exact hdisj.to_resCsrDisj le_rfl
  have hresPre : (buildResCsrContract w G X V_res cfg.m2).pre
      [cfg.offAddr, cfg.nbAddr, wsIsoStamp cfg.ws, cfg.batchGenIn + 1, cfg.nX,
       wsResOff cfg.ws cfg.nX, wsResNb cfg.ws cfg.nX] st1.mem :=
    ⟨rfl, hnX, hVX_res, hcsr.1, hm2, hiso, hresDisj⟩
  have hresMC := buildResCsr_meetsContract (w := w) hres_proc G X V_res cfg.m2
  have hresArgs : evalArgs w st1 [.reg 3, .reg 4, .reg 6, .reg 17, .reg 1, .reg 7, .reg 22] =
      some [cfg.offAddr, cfg.nbAddr, wsIsoStamp cfg.ws, cfg.batchGenIn + 1, cfg.nX,
            wsResOff cfg.ws cfg.nX, wsResNb cfg.ws cfg.nX] := by
    simp [evalArgs, Expr.eval, st1, hr17, hr1]
  have hresW : ∀ v ∈ [cfg.offAddr, cfg.nbAddr, wsIsoStamp cfg.ws, cfg.batchGenIn + 1, cfg.nX,
      wsResOff cfg.ws cfg.nX, wsResNb cfg.ws cfg.nX], v < 2 ^ w := by
    intro v hv
    have := hdisj.w_off; have := hdisj.w_nb; have := hdisj.w_bgen; have := hdisj.w_nX4
    unfold batchScratchSize at hw_ws; unfold wsIsoStamp wsResOff wsResNb at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨st2, c2, _, hrun2, hpost2, _, hr2_oth, hc2⟩ :=
    runs_call_of_meetsContract (r := 23) hresMC hresArgs hresW hresPre ω
  simp only [buildResCsrContract, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hpost2 hc2
  rcases hpost2 with ⟨_, _, hresCsr2, hresFr2⟩
  -- Stage 3: pre-curB assigns
  obtain ⟨c3, hrun3, hc3⟩ := batchCutPreCurB_triple (w := w) (p := p) hw_ws
    (by rw [hr2_oth 1 (by decide)]; simp [st1, hr1])
    (by rw [hr2_oth 2 (by decide)]; simp [st1, hr2])
    (by rw [hr2_oth 5 (by decide)]; simp [st1])
    (by rw [hr2_oth 22 (by decide)]; simp [st1]) ω
  set st3 : State :=
    { st2 with
      regs := Function.update (Function.update (Function.update (Function.update st2.regs
        17 (wsBOff cfg.ws cfg.nX cfg.m2))
        20 (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k))
        21 (wsBData cfg.ws cfg.nX cfg.m2 cfg.k))
        24 (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) }
  -- Stage 4: call bCurB
  have hcurBDisj : CurBDisj w X.card remPairs.length cfg.pairBAddr
      (wsBOff cfg.ws cfg.nX cfg.m2) (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k)
      (wsBData cfg.ws cfg.nX cfg.m2 cfg.k) (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) := by
    rw [← hnX, ← hk]; exact hdisj.to_curBDisj
  have hst2_eq_st0_outside_res : ∀ a, a < wsResOff cfg.ws cfg.nX ∨ wsBOff cfg.ws cfg.nX cfg.m2 ≤ a →
      st2.mem a = st0.mem a := fun a ha =>
    hresFr2 a (by intro h; simp only [ResCsrWriteSet, wsResOff, wsResNb, wsBOff] at h ha; rcases h with h | h <;> omega)
  have hpb3 : LocalBPairsAt st3.mem cfg.pairBAddr X remPairs := fun v hv => by
    have hpb_ws := hdisj.pb_ws; unfold DisjRange batchScratchSize at hpb_ws
    have hneq : ¬ ResCsrWriteSet X.card cfg.m2 (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) (cfg.pairBAddr + v) := by
      intro h; simp only [ResCsrWriteSet, wsResOff, wsResNb] at h; rcases hpb_ws with x | x <;> rcases h with h | h <;> omega
    rw [show st3.mem _ = st2.mem _ from rfl, hresFr2 _ hneq]; exact hlp.1 v hv
  have hcurBPre : (buildCurBContract w X remPairs).pre
      [cfg.pairBAddr, cfg.nX, cfg.k, wsBOff cfg.ws cfg.nX cfg.m2, wsBLen cfg.ws cfg.nX cfg.m2 cfg.k,
       wsBData cfg.ws cfg.nX cfg.m2 cfg.k, wsBCur cfg.ws cfg.nX cfg.m2 cfg.k] st3.mem :=
    ⟨rfl, hnX, hk, routeTerminalPairs_of_validTerminalPairs hvalid, hpb3, hcurBDisj⟩
  have hcurBMC := buildCurB_meetsContract (w := w) hcurb_proc X remPairs
  have hcurBArgs : evalArgs w st3 [.reg 8, .reg 1, .reg 2, .reg 17, .reg 20, .reg 21, .reg 24] =
      some [cfg.pairBAddr, cfg.nX, cfg.k, wsBOff cfg.ws cfg.nX cfg.m2, wsBLen cfg.ws cfg.nX cfg.m2 cfg.k,
            wsBData cfg.ws cfg.nX cfg.m2 cfg.k, wsBCur cfg.ws cfg.nX cfg.m2 cfg.k] := by
    simp [evalArgs, Expr.eval, st3, hr2_oth 8 (by decide), hr2_oth 1 (by decide), hr2_oth 2 (by decide), st1, hr8, hr1, hr2]
  have hcurBW : ∀ v ∈ [cfg.pairBAddr, cfg.nX, cfg.k, wsBOff cfg.ws cfg.nX cfg.m2, wsBLen cfg.ws cfg.nX cfg.m2 cfg.k,
      wsBData cfg.ws cfg.nX cfg.m2 cfg.k, wsBCur cfg.ws cfg.nX cfg.m2 cfg.k], v < 2 ^ w := by
    intro v hv
    have := hdisj.w_pb; have := hdisj.w_nX4; have := hdisj.w_k
    unfold batchScratchSize at hw_ws; unfold wsBOff wsBLen wsBData wsBCur at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨st4, c4, _, hrun4, hpost4, _, hr4_oth, hc4⟩ :=
    runs_call_of_meetsContract (r := 25) hcurBMC hcurBArgs hcurBW hcurBPre ω
  simp only [buildCurBContract, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hpost4 hc4
  rcases hpost4 with ⟨_, _, hbs4, hcurBFr4⟩
  have hst4_eq_st2_outside_curB : ∀ a, a < wsBOff cfg.ws cfg.nX cfg.m2 ∨ wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k ≤ a →
      st4.mem a = st2.mem a := fun a ha =>
    hcurBFr4 a (by intro h; simp only [CurBWriteSet, wsBOff, wsBLen, wsBData, wsBCur, wsLayerOffS] at h ha
                   rcases h with h | h | h | h <;> omega)
  have hst4_outside_ws : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
      st4.mem a = st0.mem a := fun a ha => by
    have h1 : ¬ CurBWriteSet X.card remPairs.length (wsBOff cfg.ws cfg.nX cfg.m2)
        (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k) (wsBData cfg.ws cfg.nX cfg.m2 cfg.k)
        (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) a := by
      intro hw; rw [← hnX, ← hk] at hw; exact ha (batch_curBWriteSet_in_ws hw)
    have h2 : ¬ ResCsrWriteSet X.card cfg.m2 (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) a := by
      intro hw; rw [← hnX] at hw; exact ha (batch_resCsrWriteSet_in_ws hw)
    exact (hcurBFr4 a h1).trans (hresFr2 a h2)
  have hsub4 : BatchSubCfgsInit st4.mem cfg hL :=
    hsub.of_outside_124 fun a ha1 ha2 =>
      (hst4_eq_st2_outside_curB a (Or.inl (by unfold wsBOff; omega))).trans
        (hst2_eq_st0_outside_res a (Or.inl (by unfold wsResOff; omega)))
  -- Stage 5: pre-ballLoop assigns
  have hcfg_ws := hdisj.cfg_ws; unfold DisjRange at hcfg_ws
  have hm4_cfg : ∀ o < 26, st4.mem (cfgAddr + o) = st0.mem (cfgAddr + o) := fun o ho =>
    hst4_outside_ws _ (by rcases hcfg_ws with x | x <;> omega)
  have hball_sub_4 := hsub4
  rcases hball_sub_4 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hb3_4, _, _, _, _, hb9_4, hb11_4, _, hb14_4, _, _⟩
  obtain ⟨c5, hrun5, hc5⟩ := batchCutPreBall_triple (w := w) (p := p) hw_cfg hw_ws hdisj.w_livegen
    ((hm4_cfg 20 (by decide)).trans hcfg20) ((hm4_cfg 21 (by decide)).trans hcfg21)
    hb3_4 hb9_4 hb11_4 hb14_4
    (by rw [hr4_oth 0 (by decide)]; simp [st3, hr2_oth 0 (by decide), st1, hr0])
    (by rw [hr4_oth 1 (by decide)]; simp [st3, hr2_oth 1 (by decide), st1, hr1])
    (by rw [hr4_oth 14 (by decide)]; simp [st3, hr2_oth 14 (by decide), st1, hr14]) ω
  set st5 : State :=
    { st4 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update st4.regs
          15 (wsBallCfg cfg.ws)) 16 (wsBfsBallCfg cfg.ws))
          19 cfg.ballGenIn) 22 (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k))
          23 (cfg.liveGenIn + 1)) 33 (wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
          34 (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k))
          35 (wsBallList cfg.ws cfg.nX cfg.m2 cfg.k))
          36 (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)) 31 0) 32 0 }
  -- Stage 6: batchBallLoop_triple
  have hst4_eq_st0_lo : ∀ a, a < wsResOff cfg.ws cfg.nX → st4.mem a = st0.mem a := fun a ha =>
    (hst4_eq_st2_outside_curB a (Or.inl (by simp only [wsResOff, wsBOff] at ha ⊢; omega))).trans
      (hst2_eq_st0_outside_res a (Or.inl ha))
  have hst4_eq_st0_hi : ∀ a, wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k ≤ a → st4.mem a = st0.mem a := fun a ha =>
    (hst4_eq_st2_outside_curB a (Or.inr ha)).trans
      (hst2_eq_st0_outside_res a (Or.inr (by simp only [wsLayerOffS, wsBOff] at ha ⊢; omega)))
  have hinv5 : BatchBallInv st5.mem st4.mem G X V_res cfg hL remPairs 0 ∅ [] bfsGen0 cfg.ballGenIn := by
    refine ⟨Finset.empty_subset _, hbfs_lo,
      by rw [Nat.sub_zero, ← hk]; have : cfg.k * (cfg.d + 1) + 2 * cfg.k = cfg.k * (cfg.d + 3) := by ring
         omega,
      le_rfl, by rw [Nat.sub_zero, ← hk],
      hresCsr2.congr
        (fun k hk' => hst4_eq_st2_outside_curB _ (Or.inl (by unfold wsResOff wsBOff; omega)))
        (fun k hk' =>
          have hk2 : k < cfg.m2 := lt_of_lt_of_le hk' (le_trans (adjCsrOff_inside_le G hVX_res X.card) hm2)
          hst4_eq_st2_outside_curB _ (Or.inl (by unfold wsResNb wsBOff; omega))),
      ?_, hbs4,
      fun v hv => by
        rw [show st5.mem _ = st4.mem _ from rfl, hst4_eq_st0_hi _ (by unfold wsLiveStamp wsLayerOffS; omega)]
        exact ⟨fun _ => by simp [origOf_mem hv], fun _ => by have := hlive_le v hv; omega⟩,
      fun v hv => by
        rw [show st5.mem _ = st4.mem _ from rfl, hst4_eq_st0_hi _ (by unfold wsLiveStamp wsLayerOffS; omega)]
        have := hlive_le v hv; omega,
      fun v hv => by
        rw [show st5.mem _ = st4.mem _ from rfl, hst4_eq_st0_lo _ (by unfold wsVisStamp wsResOff; omega)]
        exact hvis_le v hv,
      fun v hv => by
        rw [show st5.mem _ = st4.mem _ from rfl, hst4_eq_st0_hi _ (by unfold wsBallStamp wsLayerOffS; omega)]
        exact hball_le v hv,
      rfl, List.nodup_nil, fun _ h => (nomatch h), fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (Nat.not_lt_zero _),
      hsub4, fun _ _ => rfl, fun _ _ => rfl⟩
    · have h1 := hdisj.ro_ao_ws; have h2 := hdisj.al_ws; have h3 := hdisj.ad_ws
      unfold DisjRange at h1 h2 h3
      refine ⟨by rw [show st5.mem _ = st4.mem _ from rfl, hst4_outside_ws _ (by rcases h1 with x | x <;> omega)]; exact hlp.2.1,
        fun j hj => ?_⟩
      have h_j := hlp.2.2 j hj
      have ho1 := hst4_outside_ws (cfg.aOffAddr + j) (by rcases h1 with x | x <;> omega)
      have ho2 := hst4_outside_ws (cfg.aOffAddr + j + 1) (by rcases h1 with x | x <;> omega)
      have hl := hst4_outside_ws (cfg.aLenAddr + j) (by rcases h2 with x | x <;> omega)
      refine ⟨by rw [show st5.mem _ = st4.mem _ from rfl, ho1, ho2, hl]; exact h_j.1,
        by rw [show st5.mem _ = st4.mem _ from rfl, hl]; exact h_j.2.1, fun t ht => ?_⟩
      have ht_le : st0.mem (cfg.aOffAddr + j) + t < X.card := by
        have hmo := localAPairsAt_slot_bound hlp.2 (j + 1) remPairs.length (by omega) le_rfl
        have := hlp.2.1; have := h_j.1; have := h_j.2.1
        rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmo
        simp only [List.length_map, Finset.length_sort] at ht; omega
      rw [show st5.mem _ = st4.mem _ from rfl, ho1, Nat.add_assoc,
          hst4_outside_ws _ (by rcases h3 with x | x <;> omega), ← Nat.add_assoc]
      exact h_j.2.2 t ht
  have hregs5 : BatchBallRegs st5.regs cfg cfgAddr bfsGen0 cfg.ballGenIn 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [st5], by simp [st5], ?_, ?_,
      by simp [st5], ?_, ?_, by simp [st5], by simp [st5], by simp [st5], by simp [st5],
      by simp [st5], by simp [st5], by simp [st5], by simp [st5]⟩
    all_goals
      simp only [st5]
      repeat rw [Function.update_of_ne (by decide)]
      rw [hr4_oth _ (by decide)]
      simp only [st3]
      repeat rw [Function.update_of_ne (by decide)]
      try rw [Function.update_self]
      try (rw [hr2_oth _ (by decide)]; simp only [st1]; repeat rw [Function.update_of_ne (by decide)]
           first | exact hr0 | exact hr1 | exact hr2 | exact hr9 | exact hr10 | exact hr11 | exact hr14 | exact hr18)
  obtain ⟨st6, c6, ulF, hrun6, hregs6, h6_32, hbLo6, hbHi6, hbgLo6, hbgHi6, hinv6, hc6⟩ :=
    batchBallLoop_triple hball_proc hbfs_proc hhL hnX hk hVX_res hvalid hm2 hdisj
      remPairs.length 0 ∅ [] bfsGen0 cfg.ballGenIn st5 (Nat.zero_add _) hinv5 hregs5 ω
  simp only [List.drop_zero, Finset.sdiff_empty, Finset.card_empty, Nat.sub_zero] at h6_32 hinv6 hc6
  -- Stage 7: post-ballLoop stores and .ret 1
  obtain ⟨c7, hrun7, hc7⟩ := batchCutRet_triple (w := w) (p := p)
    (cfgAddr := cfgAddr) (bfsGenF := st6.regs 18) (ballGenF := st6.regs 19)
    (liveGen1 := cfg.liveGenIn + 1) (cutSize := cutRes.1.card) hw_cfg hw4
    ((hregs6 0 (Or.inl (by decide))).trans hregs5.1) rfl rfl
    ((hregs6 23 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hregs5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    h6_32 ω
  set memF := Function.update (Function.update (Function.update (Function.update
    (Function.update st6.mem (cfgAddr + 18) (st6.regs 18)) (cfgAddr + 20) (st6.regs 19))
    (cfgAddr + 21) (cfg.liveGenIn + 1)) (cfgAddr + 24) 1) (cfgAddr + 25) cutRes.1.card
  set stF : State := { st6 with mem := memF }
  -- Stitch stages 1..7 into batchCutBranchStmt
  have hrun67 : Runs w p ω
      (seqStmts (batchBallLoopStmt bBall ::
        [ .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
        , .store (.bin .add (.reg 0) (.const 20)) (.reg 19)
        , .store (.bin .add (.reg 0) (.const 21)) (.reg 23)
        , .store (.bin .add (.reg 0) (.const 24)) (.const 1)
        , .store (.bin .add (.reg 0) (.const 25)) (.reg 32)
        , .ret (.const 1) ]))
      st5 (.returned 1) stF (c6 + c7 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st6, c6, c7, hrun6, hrun7, rfl⟩)
  obtain ⟨c57, hrun57, hc57⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun5 hrun67
  obtain ⟨c47, hrun47, hc47⟩ := batch_runs_seqStmts_append (by simp) (by simp)
    (show Runs w p ω (seqStmts [.call 25 bCurB [.reg 8, .reg 1, .reg 2, .reg 17, .reg 20, .reg 21, .reg 24]]) st3 .normal st4 c4 from hrun4) hrun57
  obtain ⟨c37, hrun37, hc37⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3 hrun47
  obtain ⟨c27, hrun27, hc27⟩ := batch_runs_seqStmts_append (by simp) (by simp)
    (show Runs w p ω (seqStmts [.call 23 bRes [.reg 3, .reg 4, .reg 6, .reg 17, .reg 1, .reg 7, .reg 22]]) st1 .normal st2 c2 from hrun2) hrun37
  obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1 hrun27
  -- Prove postconditions
  have hst6_outside_ws : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
      st6.mem a = st0.mem a := fun a ha => (hinv6.frame_ws a ha).trans (hst4_outside_ws a ha)
  have hmemF_eq_st6 : ∀ a, a < cfgAddr + 18 ∨ cfgAddr + 26 ≤ a → stF.mem a = st6.mem a := fun a ha => by
    simp only [stF, memF,
      Function.update_of_ne (by omega : a ≠ cfgAddr + 25),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 24),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 21),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 20),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 18)]
  have hmemF_ws : ∀ a, cfg.ws ≤ a → a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k → stF.mem a = st6.mem a :=
    fun a ha1 ha2 => hmemF_eq_st6 a (by rcases hcfg_ws with x | x <;> omega)
  have hmF18 : stF.mem (cfgAddr + 18) = st6.regs 18 := by
    simp only [stF, memF]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hmF20 : stF.mem (cfgAddr + 20) = st6.regs 19 := by
    simp only [stF, memF]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  have hmF21 : stF.mem (cfgAddr + 21) = cfg.liveGenIn + 1 := by
    simp only [stF, memF]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hmF24 : stF.mem (cfgAddr + 24) = 1 := by
    simp only [stF, memF]; rw [Function.update_of_ne (by omega), Function.update_self]
  have hmF25 : stF.mem (cfgAddr + 25) = cutRes.1.card := by
    simp only [stF, memF]; rw [Function.update_self]
  have hstF_ro_stamp : ∀ a,
      (wsIsoStamp cfg.ws ≤ a ∧ a < wsIsoStamp cfg.ws + 2 * cfg.nX) ∨
      (wsCurStamp cfg.ws cfg.nX ≤ a ∧ a < wsCurStamp cfg.ws cfg.nX + 4 * cfg.nX) →
      stF.mem a = st0.mem a := fun a ha => by
    have hin : cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k := by
      rcases ha with ha | ha <;> (simp only [wsIsoStamp, wsCurStamp, batchScratchSize] at ha ⊢; omega)
    have hlt : a < wsResOff cfg.ws cfg.nX := by
      rcases ha with ha | ha <;> (simp only [wsIsoStamp, wsCurStamp, wsResOff] at ha ⊢; omega)
    exact (hmemF_ws a hin.1 hin.2).trans ((hinv6.ro_stamps a ha).trans (hst4_eq_st0_lo a hlt))
  refine ⟨stF, cAll, hrunAll,
    (hmemF_eq_st6 _ (Or.inl (by omega))).trans ((hst6_outside_ws _ (by rcases hcfg_ws with x | x <;> omega)).trans hcfg17),
    by rw [hmF18]; exact hbLo6, by rw [hmF18]; exact hbHi6,
    by simp only [stF, memF, Function.update_of_ne (by omega : cfgAddr + 19 ≠ cfgAddr + 25),
         Function.update_of_ne (by omega : cfgAddr + 19 ≠ cfgAddr + 24),
         Function.update_of_ne (by omega : cfgAddr + 19 ≠ cfgAddr + 21),
         Function.update_of_ne (by omega : cfgAddr + 19 ≠ cfgAddr + 20),
         Function.update_of_ne (by omega : cfgAddr + 19 ≠ cfgAddr + 18)]
       exact (hst6_outside_ws _ (by rcases hcfg_ws with x | x <;> omega)).trans hcfg19,
    by rw [hmF20]; exact hbgLo6, by rw [hmF20]; exact hbgHi6,
    hmF21,
    by simp only [stF, memF, Function.update_of_ne (by omega : cfgAddr + 22 ≠ cfgAddr + 25),
         Function.update_of_ne (by omega : cfgAddr + 22 ≠ cfgAddr + 24),
         Function.update_of_ne (by omega : cfgAddr + 22 ≠ cfgAddr + 21),
         Function.update_of_ne (by omega : cfgAddr + 22 ≠ cfgAddr + 20),
         Function.update_of_ne (by omega : cfgAddr + 22 ≠ cfgAddr + 18)]
       exact (hst6_outside_ws _ (by rcases hcfg_ws with x | x <;> omega)).trans hcfg22,
    by simp only [stF, memF, Function.update_of_ne (by omega : cfgAddr + 23 ≠ cfgAddr + 25),
         Function.update_of_ne (by omega : cfgAddr + 23 ≠ cfgAddr + 24),
         Function.update_of_ne (by omega : cfgAddr + 23 ≠ cfgAddr + 21),
         Function.update_of_ne (by omega : cfgAddr + 23 ≠ cfgAddr + 20),
         Function.update_of_ne (by omega : cfgAddr + 23 ≠ cfgAddr + 18)]
       exact (hst6_outside_ws _ (by rcases hcfg_ws with x | x <;> omega)).trans hcfg23,
    hmF24, hmF25,
    fun v hv => by rw [hstF_ro_stamp _ (Or.inl ⟨by omega, by omega⟩)]; exact hiso_le v hv,
    fun v hv => by rw [hstF_ro_stamp _ (Or.inl ⟨by unfold wsMatchAStamp wsIsoStamp; omega, by unfold wsMatchAStamp wsIsoStamp; omega⟩)]; exact hma_le v hv,
    fun v hv => by rw [hmF18, hmemF_ws _ (by unfold wsVisStamp; omega) (by unfold wsVisStamp batchScratchSize; omega)]; exact hinv6.vis_le v hv,
    fun v hv => by rw [hstF_ro_stamp _ (Or.inr ⟨by omega, by omega⟩)]; exact hcur_le v hv,
    fun v hv => by rw [hstF_ro_stamp _ (Or.inr ⟨by unfold wsUsedStamp wsCurStamp; omega, by unfold wsUsedStamp wsCurStamp; omega⟩)]; exact hused_le v hv,
    fun v hv => by rw [hstF_ro_stamp _ (Or.inr ⟨by unfold wsDeadStamp wsCurStamp; omega, by unfold wsDeadStamp wsCurStamp; omega⟩)]; exact hdead_le v hv,
    fun v hv => by rw [hmF20, hmemF_ws _ (by unfold wsBallStamp; omega) (by unfold wsBallStamp batchScratchSize; omega)]; exact hinv6.ball_le v hv,
    fun v hv => by rw [hmemF_ws _ (by unfold wsLiveStamp; omega) (by unfold wsLiveStamp batchScratchSize; omega)]; exact hinv6.live_le v hv,
    hinv6.sub_init.of_outside_124 fun a ha1 ha2 => hmemF_ws a ha1 (by unfold batchScratchSize; omega),
    ⟨ulF, hinv6.ul_len, hinv6.ul_nd, hinv6.ul_sub, hinv6.ul_cov, fun j hj => by
      have hj_lt : j < X.card := by have := hinv6.ul_len; have := Finset.card_le_card hinv6.U_sub; omega
      rw [hmemF_ws _ (by unfold wsCutList; omega) (by unfold wsCutList batchScratchSize; omega)]
      exact hinv6.ul_at j hj⟩,
    fun a ha => by
      have ha' := ha; simp only [BatchWriteSet, not_or] at ha'
      rcases ha' with ⟨_, _, _, _, _, hcfg, hws, _, _⟩
      exact (hmemF_eq_st6 a (by omega)).trans ((hst6_outside_ws a hws).trans (hfr0 a ha)),
    ?_⟩
  have hsum_le : (remPairs.map fun ab => ab.1.card + ab.2.card).sum ≤ X.card :=
    validTerminalPairs_sum_card_le hvalid
  have hcut_le : cutRes.1.card ≤ X.card := Finset.card_le_card hinv6.U_sub
  change c6 ≤ 1050 * cutRes.2 + 45 * (remPairs.map fun ab => ab.1.card + ab.2.card).sum + 40 * cutRes.1.card + 25 at hc6
  simp only [argsSize, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc57 hc47 hc37 hc27 hcAll
  rw [← hk] at hc4
  omega

end MinCostFlow.ExpanderDecomp
