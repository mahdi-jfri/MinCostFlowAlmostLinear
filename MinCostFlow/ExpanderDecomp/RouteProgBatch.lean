module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchCut

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Procedure Verification (`RouteProgBatch`)

Completes the full deterministic Word-RAM verification of Procedure 4 (`runBatchProc`) against
`runBatch G X Δ b L pairs`:
- `batchRoutePairs_diff_card_le_cost`: `(V \ br.remVerts).card ≤ br.cost` and `br.routedCount = br.perPairPaths.flatten.length`.
- `batchLoadRoute_triple`, `batchStoreRouteOut_triple`, `batchMatchedRet_triple`: straight-line
  configuration load/store helpers.
- `runBatch_triple`: full Hoare triple for `runBatchProc`.
- `runBatchContract`, `runBatch_meetsContract`: contract and deterministic satisfaction proof
  with step bound `batchProgCost (runBatch G X Δ b L pairs).cost`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helpers -/

lemma validTerminalPairs_of_routeTerminalPairs {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} (h : RouteTerminalPairs X pairs) :
    ValidTerminalPairs X pairs := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have h1 := h.1 p hp
    exact ⟨h1.1, h1.2.1, h1.2.2.1⟩
  · have hmem := h.1
    have hpw := h.2
    clear h
    induction pairs with
    | nil => simp
    | cons p rest ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons]
      have hp := hmem p List.mem_cons_self
      have hpw' := List.pairwise_cons.mp hpw
      refine ⟨?_, ?_, ih (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) hpw'.2⟩
      · intro S hS
        rcases List.mem_cons.mp hS with rfl | hS
        · exact hp.2.2.2
        · rcases List.mem_flatMap.mp hS with ⟨q, hq, hSq⟩
          have hd := Finset.disjoint_union_left.mp (hpw'.1 q hq)
          have hd1 := Finset.disjoint_union_right.mp hd.1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hSq
          rcases hSq with rfl | rfl <;> [exact hd1.1; exact hd1.2]
      · intro S hS
        rcases List.mem_flatMap.mp hS with ⟨q, hq, hSq⟩
        have hd := Finset.disjoint_union_left.mp (hpw'.1 q hq)
        have hd2 := Finset.disjoint_union_right.mp hd.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hSq
        rcases hSq with rfl | rfl <;> [exact hd2.1; exact hd2.2]

/-! ## 2. Straight-Line Helpers (`batchLoadRouteStmt`, Store-Out, Matched Return) -/

private lemma batchLoadRoute_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg} {cfgAddr pLo pHi cLo cHi hL : ℕ}
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    {st0 : State} (hcfg : BatchCfgAt st0.mem cfgAddr cfg) (hr0 : st0.regs 0 = cfgAddr) :
    ∀ ω,
      ∃ st1 c1,
        Runs w p ω batchLoadRouteStmt st0 .normal st1 c1 ∧
        st1.mem = st0.mem ∧
        BatchRouteRegs st1.regs cfg cfgAddr cfg.bfsGenIn cfg.dfsGenIn cfg.pathHeapIn cfg.chunkHeapIn 0 0 ∧
        c1 ≤ 150 := by
  intro ω
  have hw_cfg := hdisj.w_cfg; have hw_ws := hdisj.w_ws; have hw_bgen := hdisj.w_bgen
  have hw_nX4 := hdisj.w_nX4; have hw4 := hdisj.w_4
  have hS : batchScratchSize cfg.nX cfg.m2 cfg.k = 129 + 27 * cfg.nX + cfg.m2 + 3 * cfg.k := rfl
  rcases hcfg with ⟨m0, m1, _, _, _, _, _, _, m8, m9, m10, m11, m12, m13, m14, _, _,
    m17, m18, m19, _, _, m22, m23⟩
  set regsA := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update st0.regs 1 cfg.nX) 2 cfg.k) 8 cfg.pairBAddr)
    9 cfg.aOffAddr) 10 cfg.aLenAddr) 11 cfg.aDataAddr) 12 cfg.accHeadAddr)
    13 cfg.accTailAddr) 14 cfg.ws) 15 (wsSpCfg cfg.ws)
  set stA : State := { st0 with regs := regsA }
  set regsB := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update regsA 16 (wsMatchAStamp cfg.ws cfg.nX))
    17 (cfg.batchGenIn + 1)) 18 cfg.bfsGenIn) 19 cfg.dfsGenIn) 20 cfg.pathHeapIn)
    21 cfg.chunkHeapIn) 29 0) 30 0) 31 (wsBfsCfg cfg.ws)) 32 (wsDfsCfg cfg.ws)
  set stB : State := { st0 with regs := regsB }
  have hA : ∃ cA,
      Runs w p ω
        (seqStmts
          [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
          , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
          , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))
          , .assign 9 (.load (.bin .add (.reg 0) (.const 9)))
          , .assign 10 (.load (.bin .add (.reg 0) (.const 10)))
          , .assign 11 (.load (.bin .add (.reg 0) (.const 11)))
          , .assign 12 (.load (.bin .add (.reg 0) (.const 12)))
          , .assign 13 (.load (.bin .add (.reg 0) (.const 13)))
          , .assign 14 (.load (.bin .add (.reg 0) (.const 14)))
          , .assign 15 (.reg 14) ])
        st0 .normal stA cA ∧ cA ≤ 70 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
            , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
            , .assign 8 (.load (.bin .add (.reg 0) (.const 8)))
            , .assign 9 (.load (.bin .add (.reg 0) (.const 9)))
            , .assign 10 (.load (.bin .add (.reg 0) (.const 10)))
            , .assign 11 (.load (.bin .add (.reg 0) (.const 11)))
            , .assign 12 (.load (.bin .add (.reg 0) (.const 12)))
            , .assign 13 (.load (.bin .add (.reg 0) (.const 13)))
            , .assign 14 (.load (.bin .add (.reg 0) (.const 14)))
            , .assign 15 (.reg 14) ])
          st0 o s c ∧ (o = .normal ∧ s = stA) ∧ 0 + c ≤ 70 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := cfg.nX) (by rw [← m0]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.k) (by rw [← m1]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.pairBAddr) (by rw [← m8]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.aOffAddr) (by rw [← m9]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.aLenAddr) (by rw [← m10]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.aDataAddr) (by rw [← m11]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.accHeadAddr) (by rw [← m12]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.accTailAddr) (by rw [← m13]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.ws) (by rw [← m14]; eval_expr) ?_
      refine runs_assign_le (v := wsSpCfg cfg.ws) (by unfold wsSpCfg; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cA, h, ⟨rfl, rfl⟩, hcA⟩; exact ⟨cA, h, by omega⟩
  have hB : ∃ cB,
      Runs w p ω
        (seqStmts
          [ .assign 16 (.bin .add (.bin .add (.reg 14) (.const 124)) (.reg 1))
          , .assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const 17))) (.const 1))
          , .assign 18 (.load (.bin .add (.reg 0) (.const 18)))
          , .assign 19 (.load (.bin .add (.reg 0) (.const 19)))
          , .assign 20 (.load (.bin .add (.reg 0) (.const 22)))
          , .assign 21 (.load (.bin .add (.reg 0) (.const 23)))
          , .assign 29 (.const 0)
          , .assign 30 (.const 0)
          , .assign 31 (.bin .add (.reg 14) (.const 20))
          , .assign 32 (.bin .add (.reg 14) (.const 44)) ])
        stA .normal stB cB ∧ cB ≤ 70 := by
    have hA0 : stA.regs 0 = cfgAddr := by simp [stA, regsA, hr0]
    have hA1 : stA.regs 1 = cfg.nX := by simp [stA, regsA]
    have hA14 : stA.regs 14 = cfg.ws := by simp [stA, regsA]
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 16 (.bin .add (.bin .add (.reg 14) (.const 124)) (.reg 1))
            , .assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const 17))) (.const 1))
            , .assign 18 (.load (.bin .add (.reg 0) (.const 18)))
            , .assign 19 (.load (.bin .add (.reg 0) (.const 19)))
            , .assign 20 (.load (.bin .add (.reg 0) (.const 22)))
            , .assign 21 (.load (.bin .add (.reg 0) (.const 23)))
            , .assign 29 (.const 0)
            , .assign 30 (.const 0)
            , .assign 31 (.bin .add (.reg 14) (.const 20))
            , .assign 32 (.bin .add (.reg 14) (.const 44)) ])
          stA o s c ∧ (o = .normal ∧ s = stB) ∧ 0 + c ≤ 70 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wsMatchAStamp cfg.ws cfg.nX)
        (by unfold wsMatchAStamp; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.batchGenIn + 1) (by rw [← m17]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.bfsGenIn) (by rw [← m18]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.dfsGenIn) (by rw [← m19]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.pathHeapIn) (by rw [← m22]; eval_expr) ?_
      refine runs_seq_assign_le (v := cfg.chunkHeapIn) (by rw [← m23]; eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := wsBfsCfg cfg.ws) (by unfold wsBfsCfg; eval_expr) ?_
      refine runs_assign_le (v := wsDfsCfg cfg.ws) (by unfold wsDfsCfg; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cB, h, ⟨rfl, rfl⟩, hcB⟩; exact ⟨cB, h, by omega⟩
  rcases hA with ⟨cA, hrunA, hcA⟩
  rcases hB with ⟨cB, hrunB, hcB⟩
  obtain ⟨c1, hrun1, hc1⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA hrunB
  refine ⟨stB, c1, hrun1, rfl, ?_, by simp at hc1; omega⟩
  refine ⟨by simp [stB, regsB, regsA, hr0], by simp [stB, regsB, regsA], by simp [stB, regsB, regsA],
    by simp [stB, regsB, regsA], by simp [stB, regsB, regsA], by simp [stB, regsB, regsA],
    by simp [stB, regsB, regsA], by simp [stB, regsB, regsA], by simp [stB, regsB, regsA],
    by simp [stB, regsB, regsA], by simp [stB, regsB, regsA], by simp [stB, regsB],
    by simp [stB, regsB], by simp [stB, regsB], by simp [stB, regsB], by simp [stB, regsB],
    by simp [stB, regsB], by simp [stB, regsB], by simp [stB, regsB], by simp [stB, regsB],
    by simp [stB, regsB]⟩

private lemma batchStoreRouteOut_triple {w : ℕ} {p : Program}
    {cfgAddr batchGen1 bfsGen1 dfsGen1 pathHeap1 chunkHeap1 Hbatch curDemand : ℕ}
    (hw_cfg : cfgAddr + 30 < 2 ^ w)
    {st0 : State}
    (hm4 : st0.mem (cfgAddr + 4) = Hbatch) (hm16 : st0.mem (cfgAddr + 16) = curDemand)
    (hr0 : st0.regs 0 = cfgAddr) (hr17 : st0.regs 17 = batchGen1)
    (hr18 : st0.regs 18 = bfsGen1) (hr19 : st0.regs 19 = dfsGen1)
    (hr20 : st0.regs 20 = pathHeap1) (hr21 : st0.regs 21 = chunkHeap1) :
    ∀ ω,
      let mem1 := Function.update (Function.update (Function.update (Function.update
        (Function.update st0.mem (cfgAddr + 17) batchGen1) (cfgAddr + 18) bfsGen1)
        (cfgAddr + 19) dfsGen1) (cfgAddr + 22) pathHeap1) (cfgAddr + 23) chunkHeap1
      let st1 : State :=
        { mem := mem1, regs := Function.update (Function.update st0.regs 26 Hbatch) 27 curDemand, pos := st0.pos }
      ∃ c1,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 0) (.const 17)) (.reg 17)
            , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
            , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
            , .store (.bin .add (.reg 0) (.const 22)) (.reg 20)
            , .store (.bin .add (.reg 0) (.const 23)) (.reg 21)
            , .assign 26 (.load (.bin .add (.reg 0) (.const 4)))
            , .assign 27 (.load (.bin .add (.reg 0) (.const 16))) ])
          st0 .normal st1 c1 ∧ c1 ≤ 55 := by
  intro ω
  set mem1 := Function.update (Function.update (Function.update (Function.update
    (Function.update st0.mem (cfgAddr + 17) batchGen1) (cfgAddr + 18) bfsGen1)
    (cfgAddr + 19) dfsGen1) (cfgAddr + 22) pathHeap1) (cfgAddr + 23) chunkHeap1
  set st1 : State :=
    { mem := mem1, regs := Function.update (Function.update st0.regs 26 Hbatch) 27 curDemand, pos := st0.pos }
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 0) (.const 17)) (.reg 17)
          , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
          , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
          , .store (.bin .add (.reg 0) (.const 22)) (.reg 20)
          , .store (.bin .add (.reg 0) (.const 23)) (.reg 21)
          , .assign 26 (.load (.bin .add (.reg 0) (.const 4)))
          , .assign 27 (.load (.bin .add (.reg 0) (.const 16))) ])
        st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 55 := by
    dsimp only [seqStmts]
    refine runs_seq_store_le (x := cfgAddr + 17) (v := batchGen1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 18) (v := bfsGen1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 19) (v := dfsGen1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 22) (v := pathHeap1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 23) (v := chunkHeap1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := Hbatch)
      (by simp [Expr.eval, BinOp.eval, hr0, show 4 < 2 ^ w by omega, show cfgAddr + 4 < 2 ^ w by omega, hm4]) ?_
    refine runs_assign_le (v := curDemand)
      (by simp [Expr.eval, BinOp.eval, hr0, show 16 < 2 ^ w by omega, show cfgAddr + 16 < 2 ^ w by omega, hm16])
      ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩

private lemma batchMatchedRet_triple {w : ℕ} {p : Program}
    {cfgAddr curDemand routed : ℕ}
    (hw_cfg : cfgAddr + 30 < 2 ^ w) (hle : routed ≤ curDemand) (hw_dem : curDemand < 2 ^ w)
    {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr) (hr27 : st0.regs 27 = curDemand) (hr30 : st0.regs 30 = routed) :
    ∀ ω,
      let memF := Function.update (Function.update (Function.update st0.mem
        (cfgAddr + 16) (curDemand - routed)) (cfgAddr + 24) 0) (cfgAddr + 25) 0
      ∃ cF,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 0) (.const 16)) (.bin .sub (.reg 27) (.reg 30))
            , .store (.bin .add (.reg 0) (.const 24)) (.const 0)
            , .store (.bin .add (.reg 0) (.const 25)) (.const 0)
            , .ret (.const 0) ])
          st0 (.returned 0) { st0 with mem := memF } cF ∧ cF ≤ 35 := by
  intro ω
  set memF := Function.update (Function.update (Function.update st0.mem
    (cfgAddr + 16) (curDemand - routed)) (cfgAddr + 24) 0) (cfgAddr + 25) 0
  have h0 : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 0) (.const 16)) (.bin .sub (.reg 27) (.reg 30))
          , .store (.bin .add (.reg 0) (.const 24)) (.const 0)
          , .store (.bin .add (.reg 0) (.const 25)) (.const 0)
          , .ret (.const 0) ])
        st0 o s c ∧ (o = .returned 0 ∧ s = { st0 with mem := memF }) ∧ 0 + c ≤ 35 := by
    dsimp only [seqStmts]
    refine runs_seq_store_le (x := cfgAddr + 16) (v := curDemand - routed) (by eval_expr)
      (by simp [Expr.eval, BinOp.eval, hr27, hr30, show curDemand - routed < 2 ^ w by omega]) ?_
    refine runs_seq_store_le (x := cfgAddr + 24) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 25) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0 with ⟨_, _, cF, h, ⟨rfl, rfl⟩, hcF⟩; exact ⟨cF, h, by omega⟩

/-! ## 3. Full Procedure Triple and Contract (`runBatch_triple`, `runBatch_meetsContract`) -/

theorem runBatch_triple {w : ℕ} {p : Program} {bSp bBfs bDfs bRes bCurB bBall : ℕ}
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    {G : Graph} {X : Finset ℕ} {Δ b L : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    {cfg : BatchCfg} {cfgAddr pLo pHi cLo cHi hL : ℕ}
    {accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))}
    {st0 : State}
    (hnX : cfg.nX = X.card) (hk : cfg.k = pairs.length)
    (hm2 : cfg.m2 = 2 * (G.inside X).length)
    (hd : cfg.d = routeD Δ b L) (hb : cfg.b = b) (hHb : cfg.Hbatch = routeHBatch Δ b L)
    (hhL : routeH Δ b * L = hL)
    (hdem : cfg.curDemandIn = totalDemand pairs)
    (hvalid : ValidTerminalPairs X pairs)
    (hcfg : BatchCfgAt st0.mem cfgAddr cfg)
    (hsub : BatchSubCfgsInit st0.mem cfg hL)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hcsr : AdjCsrAt st0.mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X))
    (hlp : LocalPairsAt st0.mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X pairs X.card)
    (hiso0 : ∀ v < X.card, st0.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn)
    (hma0 : ∀ v < X.card, st0.mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn)
    (hvis0 : ∀ v < X.card, st0.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ cfg.bfsGenIn)
    (hcur0 : ∀ v < X.card, st0.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn)
    (hused0 : ∀ v < X.card, st0.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn)
    (hdead0 : ∀ v < X.card, st0.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn)
    (hball0 : ∀ v < X.card, st0.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.ballGenIn)
    (hlive0 : ∀ v < X.card, st0.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn)
    (hchunks0 : ∀ j < pairs.length,
      ChunkChainAt st0.mem X pLo cfg.pathHeapIn cLo cfg.chunkHeapIn
        (st0.mem (cfg.accHeadAddr + j)) (st0.mem (cfg.accTailAddr + j)) (accChunks.getD j []))
    (hchDisj0 : ChunksDisj st0.mem cfg.accHeadAddr pairs.length (fun j => (accChunks.getD j []).length))
    (hr0 : st0.regs 0 = cfgAddr) :
    let res := runBatch G X Δ b L pairs
    Triple w p (fun st => st = st0) (runBatchProc bSp bRes bCurB bBall)
      (retPost fun v st' =>
        (match res.outcome with | .matched _ _ => v = 0 | .cut _ => v = 1) ∧
        BatchOutAt st'.mem X cfg cfgAddr pLo pHi cLo cHi hL accChunks res ∧
        (∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → st'.mem a = st0.mem a))
      (fun _ => batchProgCost (runBatch G X Δ b L pairs).cost) := by
  dsimp only
  intro st ω hst; rcases hst.symm with rfl
  have hw_cfg := hdisj.w_cfg; have hw_nX4 := hdisj.w_nX4; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  have hm2_le : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2 := by rw [adjCsrOff_adjOf_card, hm2]
  have hdem_le : cfg.curDemandIn ≤ X.card := by rw [hdem]; exact totalDemand_le_card_X hvalid
  -- Stage 1: batchLoadRouteStmt
  obtain ⟨st1, c1, hrun1, hmem1, hregs1, hc1⟩ := batchLoadRoute_triple hdisj hcfg hr0 ω
  -- Stage 2: batchRouteLoopStmt
  have hinv1 : BatchRouteInv st1.mem st0.mem G X cfg cfgAddr pLo pHi cLo cHi hL
      pairs pairs 0 X ∅ (fun j => accChunks.getD j []) cfg.bfsGenIn cfg.dfsGenIn
      cfg.pathHeapIn cfg.chunkHeapIn 0 := by
    rw [hmem1]
    exact ⟨rfl, rfl, hvalid, le_rfl, Finset.empty_subset _, fun _ _ _ => Finset.disjoint_empty_left _,
      by rw [Nat.zero_add, List.drop_zero, hdem], le_rfl, by simp, le_rfl, by simp, le_rfl, by simp,
      le_rfl, by simp, hcsr, hlp,
      fun v hv => ⟨fun _ => origOf_mem hv, fun _ => by have := hiso0 v hv; omega⟩,
      fun v hv => by have := hiso0 v hv; omega,
      fun v hv => ⟨fun h => by have := hma0 v hv; omega, fun h => absurd h (Finset.notMem_empty _)⟩,
      fun v hv => by have := hma0 v hv; omega,
      hvis0, hcur0, hused0, hdead0, hball0, hlive0, hsub, hchunks0, hchDisj0,
      fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨st2, c2, hrun2, hregs2_le28, _, hr30_2, hbLo2, hbHi2, hdLo2, hdHi2,
    hpLo2, hpHi2, hcLo2, hcHi2, hlp2, hiso2, hisoLe2, hmaLe2, hvis2, hcur2, hused2, hdead2,
    hball2, hlive2, hsub2, hcsr2, hch2, hchDisj2, hfr2, hcfgRo2, hc2⟩ :=
    batchRouteLoop_triple hsp_proc hbfs_proc hdfs_proc hnX hk hdem_le hm2_le hdisj
      pairs.length 0 pairs X ∅ (fun j => accChunks.getD j []) cfg.bfsGenIn cfg.dfsGenIn
      cfg.pathHeapIn cfg.chunkHeapIn 0 st1 (Nat.zero_add _) hinv1 hregs1 ω
  simp only [List.drop_zero, List.take_zero, List.nil_append, Nat.zero_add,
    Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hr30_2 hpHi2 hcHi2 hlp2 hiso2 hch2 hchDisj2 hc2
  set br := batchRoutePairs (adjOf G X) cfg.d pairs X
  have hbr_sub := batchRoutePairs_remVerts_sub (adjOf G X) cfg.d pairs X
  have hbr_dc : (X \ br.remVerts).card ≤ br.cost ∧ br.routedCount = br.perPairPaths.flatten.length :=
    ⟨hbr_sub.2.1, hbr_sub.2.2.2.2.2⟩
  have hbr_vd := batchRoutePairs_valid_and_demand G cfg.d pairs (routeTerminalPairs_of_validTerminalPairs hvalid) X le_rfl
  have hbr_rem_len : br.remPairs.length = pairs.length := hbr_sub.2.2.2.2.1
  have hbr_valid : ValidTerminalPairs X br.remPairs := validTerminalPairs_of_routeTerminalPairs hbr_vd.1
  have hbr_dem : totalDemand br.remPairs + br.routedCount = totalDemand pairs := hbr_vd.2
  have hbr_routed_le : br.routedCount ≤ X.card := by omega
  -- Stage 3: store route outputs + load Hbatch, curDemandIn
  have hr2_0 : st2.regs 0 = cfgAddr := (hregs2_le28 0 (Or.inl (by decide))).trans hregs1.1
  have hr2_17 : st2.regs 17 = cfg.batchGenIn + 1 :=
    (hregs2_le28 17 (Or.inl (by decide))).trans hregs1.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c3, hrun3, hc3⟩ := batchStoreRouteOut_triple (w := w) (p := p)
    (cfgAddr := cfgAddr) (batchGen1 := cfg.batchGenIn + 1)
    (bfsGen1 := st2.regs 18) (dfsGen1 := st2.regs 19)
    (pathHeap1 := st2.regs 20) (chunkHeap1 := st2.regs 21)
    (Hbatch := cfg.Hbatch) (curDemand := cfg.curDemandIn) hw_cfg
    ((hcfgRo2 4 (by decide)).trans hcfg.2.2.2.2.1)
    ((hcfgRo2 16 (by decide)).trans hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    hr2_0 hr2_17 rfl rfl rfl rfl ω
  set mem3 := Function.update (Function.update (Function.update (Function.update
    (Function.update st2.mem (cfgAddr + 17) (cfg.batchGenIn + 1)) (cfgAddr + 18) (st2.regs 18))
    (cfgAddr + 19) (st2.regs 19)) (cfgAddr + 22) (st2.regs 20)) (cfgAddr + 23) (st2.regs 21)
  set st3 : State :=
    { mem := mem3, regs := Function.update (Function.update st2.regs 26 cfg.Hbatch) 27 cfg.curDemandIn, pos := st2.pos }
  have hmem3_eq_st2 : ∀ a, a < cfgAddr + 17 ∨ cfgAddr + 24 ≤ a → st3.mem a = st2.mem a := fun a ha => by
    simp only [st3, mem3,
      Function.update_of_ne (by omega : a ≠ cfgAddr + 23),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 22),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 19),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 18),
      Function.update_of_ne (by omega : a ≠ cfgAddr + 17)]
  have hfr3 : ∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → st3.mem a = st0.mem a := fun a ha => by
    have hnot_cfg : a < cfgAddr + 16 ∨ cfgAddr + 26 ≤ a := by
      by_contra hc; push Not at hc
      exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
    exact (hmem3_eq_st2 a (by omega)).trans (hfr2 a ha)
  have hcfg_ws := hdisj.cfg_ws; unfold DisjRange at hcfg_ws
  have hmem3_ws : ∀ a, cfg.ws ≤ a → a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k → st3.mem a = st2.mem a :=
    fun a ha1 ha2 => hmem3_eq_st2 a (by rcases hcfg_ws with x | x <;> omega)
  have hp_hi_nX : st2.regs 20 ≤ cfg.pathHeapIn + 5 * cfg.nX := by
    have : (X \ br.remVerts).card ≤ X.card := Finset.card_le_card Finset.sdiff_subset
    omega
  have hc_hi_lim : st2.regs 21 ≤ cHi := by have := hdisj.ch_hi; omega
  have hmul_lt : br.routedCount * cfg.Hbatch < 2 ^ w := by
    have h1 : br.routedCount * cfg.Hbatch ≤ cfg.nX * cfg.Hbatch :=
      Nat.mul_le_mul_right _ (by omega)
    have := hdisj.w_Hbatch; omega
  have hsum_sdiff : (pairs.map fun ab => (ab.1 \ br.remVerts).card).sum ≤ (X \ br.remVerts).card :=
    sum_sdiff_le_sdiff_card (routeTerminalPairs_of_validTerminalPairs hvalid) br.remVerts
  set condStmt : Stmt :=
    .cond (.bin .lt (.bin .mul (.reg 30) (.reg 26)) (.reg 27))
      (batchCutBranchStmt bRes bCurB bBall)
      (seqStmts
        [ .store (.bin .add (.reg 0) (.const 16)) (.bin .sub (.reg 27) (.reg 30))
        , .store (.bin .add (.reg 0) (.const 24)) (.const 0)
        , .store (.bin .add (.reg 0) (.const 25)) (.const 0)
        , .ret (.const 0) ])
  -- Branch on br.routedCount * Hbatch < curDemandIn
  by_cases hsucc : br.routedCount * cfg.Hbatch ≥ cfg.curDemandIn
  · -- Matched branch (returns 0)
    have hcond0 : (Expr.bin .lt (.bin .mul (.reg 30) (.reg 26)) (.reg 27)).eval w st3 = some 0 := by
      simp [Expr.eval, BinOp.eval, st3, hr30_2, hmul_lt, show ¬ br.routedCount * cfg.Hbatch < cfg.curDemandIn by omega]
    obtain ⟨c4, hrun4, hc4⟩ := batchMatchedRet_triple (w := w) (p := p) (st0 := st3)
      (cfgAddr := cfgAddr) (curDemand := cfg.curDemandIn) (routed := br.routedCount)
      hw_cfg (by omega) (by omega)
      (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2_0)
      (by simp only [st3]; rw [Function.update_self])
      (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr30_2) ω
    set memF := Function.update (Function.update (Function.update st3.mem
      (cfgAddr + 16) (cfg.curDemandIn - br.routedCount)) (cfgAddr + 24) 0) (cfgAddr + 25) 0
    set stF : State := { st3 with mem := memF }
    have hrunCond : Runs w p ω condStmt st3 (.returned 0) stF _ :=
      batch_runs_cond_zero hcond0 hrun4
    obtain ⟨c34, hrun34, hc34⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3
      (show Runs w p ω (seqStmts [condStmt]) st3 (.returned 0) stF _ from hrunCond)
    have hrun24 : Runs w p ω (Stmt.seq (batchRouteLoopStmt bSp) (seqStmts
        [ .store (.bin .add (.reg 0) (.const 17)) (.reg 17)
        , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
        , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
        , .store (.bin .add (.reg 0) (.const 22)) (.reg 20)
        , .store (.bin .add (.reg 0) (.const 23)) (.reg 21)
        , .assign 26 (.load (.bin .add (.reg 0) (.const 4)))
        , .assign 27 (.load (.bin .add (.reg 0) (.const 16)))
        , condStmt ])) st1 (.returned 0) stF (c2 + c34 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c34, hrun2, hrun34, rfl⟩)
    have hrunAll : Runs w p ω (runBatchProc bSp bRes bCurB bBall) st0 (.returned 0) stF (c1 + (c2 + c34 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, hrun24, rfl⟩)
    have hres_eq : runBatch G X Δ b L pairs =
        { outcome := .matched br.perPairPaths br.remPairs, cost := br.cost + pairs.length + 1 } := by
      unfold runBatch; dsimp only
      rw [← hd, ← hHb, ← hdem]
      split_ifs with h
      · rfl
      · exact absurd hsucc h
    have hmemF_eq_st2 : ∀ a, a < cfgAddr + 16 ∨ cfgAddr + 26 ≤ a → stF.mem a = st2.mem a := fun a ha => by
      simp only [stF, memF,
        Function.update_of_ne (by omega : a ≠ cfgAddr + 25),
        Function.update_of_ne (by omega : a ≠ cfgAddr + 24),
        Function.update_of_ne (by omega : a ≠ cfgAddr + 16)]
      exact hmem3_eq_st2 a (by omega)
    have hmemF_ws : ∀ a, cfg.ws ≤ a → a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k → stF.mem a = st2.mem a :=
      fun a ha1 ha2 => hmemF_eq_st2 a (by rcases hcfg_ws with x | x <;> omega)
    have hmF16 : stF.mem (cfgAddr + 16) = totalDemand br.remPairs := by
      simp only [stF, memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]; omega
    have hmF17 : stF.mem (cfgAddr + 17) = cfg.batchGenIn + 1 := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
    have hmF18 : stF.mem (cfgAddr + 18) = st2.regs 18 := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
    have hmF19 : stF.mem (cfgAddr + 19) = st2.regs 19 := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have hmF20 : stF.mem (cfgAddr + 20) = cfg.ballGenIn := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hcfgRo2 20 (by decide)).trans hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmF21 : stF.mem (cfgAddr + 21) = cfg.liveGenIn := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hcfgRo2 21 (by decide)).trans hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmF22 : stF.mem (cfgAddr + 22) = st2.regs 20 := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
    have hmF23 : stF.mem (cfgAddr + 23) = st2.regs 21 := by
      simp only [stF, memF, st3, mem3]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
    have hmF24 : stF.mem (cfgAddr + 24) = 0 := by
      simp only [stF, memF]; rw [Function.update_of_ne (by omega), Function.update_self]
    have hkd1_le3 : cfg.k * (cfg.d + 1) ≤ cfg.k * (cfg.d + 3) := Nat.mul_le_mul_left _ (by omega)
    refine ⟨.returned 0, stF, _, hrunAll, ?_, ?_⟩
    · rw [hres_eq]
      dsimp only [retPost, BatchOutAt]
      refine ⟨rfl, ⟨hmF17, by rw [hmF18]; exact hbLo2, by rw [hmF18]; rw [← hk] at hbHi2; omega,
        by rw [hmF19]; exact hdLo2, by rw [hmF19, hk]; exact hdHi2,
        by rw [hmF20], by rw [hmF20]; omega,
        by rw [hmF21], by rw [hmF21]; omega,
        by rw [hmF22]; exact hpLo2, by rw [hmF22]; exact hp_hi_nX,
        by rw [hmF22]; omega,
        by rw [hmF23]; exact hcLo2, by rw [hmF23]; exact hc_hi_lim,
        fun v hv => by rw [hmF17, hmemF_ws _ (by unfold wsIsoStamp; omega) (by unfold wsIsoStamp batchScratchSize; omega)]; exact hisoLe2 v hv,
        fun v hv => by rw [hmF17, hmemF_ws _ (by unfold wsMatchAStamp; omega) (by unfold wsMatchAStamp batchScratchSize; omega)]; exact hmaLe2 v hv,
        fun v hv => by rw [hmF18, hmemF_ws _ (by unfold wsVisStamp; omega) (by unfold wsVisStamp batchScratchSize; omega)]; exact hvis2 v hv,
        fun v hv => by rw [hmF19, hmemF_ws _ (by unfold wsCurStamp; omega) (by unfold wsCurStamp batchScratchSize; omega)]; exact hcur2 v hv,
        fun v hv => by rw [hmF19, hmemF_ws _ (by unfold wsUsedStamp; omega) (by unfold wsUsedStamp batchScratchSize; omega)]; exact hused2 v hv,
        fun v hv => by rw [hmF19, hmemF_ws _ (by unfold wsDeadStamp; omega) (by unfold wsDeadStamp batchScratchSize; omega)]; exact hdead2 v hv,
        fun v hv => by rw [hmF20, hmemF_ws _ (by unfold wsBallStamp; omega) (by unfold wsBallStamp batchScratchSize; omega)]; exact hball2 v hv,
        fun v hv => by rw [hmF21, hmemF_ws _ (by unfold wsLiveStamp; omega) (by unfold wsLiveStamp batchScratchSize; omega)]; exact hlive2 v hv,
        hsub2.of_outside_124 fun a ha1 ha2 => hmemF_ws a ha1 (by unfold batchScratchSize; omega),
        hmF24, hmF16, by rw [hmF23, ← hbr_dc.2]; exact hcHi2, ?_, ?_, ?_⟩, ?_⟩
      · have h1 := hdisj.pb_cfg; have h2 := hdisj.ro_ao_cfg; have h3 := hdisj.al_cfg; have h4 := hdisj.ad_cfg
        unfold DisjRange at h1 h2 h3 h4
        refine ⟨fun v hv => by rw [hmemF_eq_st2 _ (by rcases h1 with x | x <;> omega)]; exact hlp2.1 v hv,
          ⟨by rw [hmemF_eq_st2 _ (by rcases h2 with x | x <;> omega)]; exact hlp2.2.1, fun j hj => ?_⟩⟩
        have h_j := hlp2.2.2 j hj
        have ho1 := hmemF_eq_st2 (cfg.aOffAddr + j) (by rcases h2 with x | x <;> omega)
        have ho2 := hmemF_eq_st2 (cfg.aOffAddr + j + 1) (by rcases h2 with x | x <;> omega)
        have hl := hmemF_eq_st2 (cfg.aLenAddr + j) (by rcases h3 with x | x <;> omega)
        refine ⟨by rw [ho1, ho2, hl]; exact h_j.1, by rw [hl]; exact h_j.2.1, fun t ht => ?_⟩
        have ht_le : st2.mem (cfg.aOffAddr + j) + t < X.card := by
          have hmo := localAPairsAt_slot_bound hlp2.2 (j + 1) br.remPairs.length (by omega) le_rfl
          have := hlp2.2.1; have := h_j.1; have := h_j.2.1
          rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmo
          simp only [List.length_map, Finset.length_sort] at ht; omega
        rw [ho1, Nat.add_assoc, hmemF_eq_st2 _ (by rcases h4 with x | x <;> omega), ← Nat.add_assoc]
        exact h_j.2.2 t ht
      · have h1 := hdisj.ah_cfg; have h2 := hdisj.at_cfg; have h3 := hdisj.cfg_hp; have h4 := hdisj.cfg_ch
        unfold DisjRange at h1 h2 h3 h4
        have hphp_le : st2.regs 20 ≤ pHi := by have := hdisj.hp_hi; omega
        have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by have := hdisj.hp_lo; have := hdisj.hp_hi; omega)
        have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' (by have := hdisj.ch_lo; have := hdisj.ch_hi; omega)
        intro j hj
        have hj' : j < pairs.length := by omega
        rw [hmF22, hmF23, hmemF_eq_st2 _ (by rcases h1 with x | x <;> omega),
            hmemF_eq_st2 _ (by rcases h2 with x | x <;> omega)]
        exact (hch2 j hj').congr
          (fun a ha1 ha2 => hmemF_eq_st2 a (by rcases h3 with x | x <;> omega))
          (fun a ha1 ha2 => hmemF_eq_st2 a (by rcases h4 with x | x <;> omega))
      · have h1 := hdisj.ah_cfg; have h3 := hdisj.cfg_hp; have h4 := hdisj.cfg_ch
        unfold DisjRange at h1 h3 h4
        have hphp_le : st2.regs 20 ≤ pHi := by have := hdisj.hp_hi; omega
        have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by have := hdisj.hp_lo; have := hdisj.hp_hi; omega)
        have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' (by have := hdisj.ch_lo; have := hdisj.ch_hi; omega)
        rw [hbr_rem_len]
        intro j1 hj1 j2 hj2 hne a ha b hb
        have hca : ∀ j (hj : j < pairs.length),
            chunkAddrs stF.mem (stF.mem (cfg.accHeadAddr + j))
              (if br.perPairPaths.getD j [] = [] then accChunks.getD j []
               else accChunks.getD j [] ++ [br.perPairPaths.getD j []]).length =
            chunkAddrs st2.mem (st2.mem (cfg.accHeadAddr + j))
              (if br.perPairPaths.getD j [] = [] then accChunks.getD j []
               else accChunks.getD j [] ++ [br.perPairPaths.getD j []]).length := fun j hj => by
          rw [hmemF_eq_st2 _ (by rcases h1 with x | x <;> omega)]
          exact ((hch2 j hj).congr_addrs
            (fun x hx1 hx2 => hmemF_eq_st2 x (by rcases h3 with y | y <;> omega))
            (fun x hx => by
              have hxb := (hch2 j hj).chunkAddrs_bounds x hx
              exact ⟨hmemF_eq_st2 x (by rcases h4 with y | y <;> omega),
                     hmemF_eq_st2 (x + 1) (by rcases h4 with y | y <;> omega)⟩)).2
        rw [hca j1 hj1] at ha; rw [hca j2 hj2] at hb
        exact hchDisj2 j1 hj1 j2 hj2 hne a ha b hb
      · intro a ha
        have hnot_cfg : a < cfgAddr + 16 ∨ cfgAddr + 26 ≤ a := by
          by_contra hc; push Not at hc
          exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
        exact (hmemF_eq_st2 a hnot_cfg).trans (hfr2 a ha)
    · rw [hres_eq]; dsimp only [batchProgCost]
      simp only [Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc3 hc4 hc34
      omega
  · -- Cut branch (returns 1)
    have hlt : br.routedCount * cfg.Hbatch < cfg.curDemandIn := by omega
    have hcond1 : (Expr.bin .lt (.bin .mul (.reg 30) (.reg 26)) (.reg 27)).eval w st3 = some 1 := by
      simp [Expr.eval, BinOp.eval, st3, hr30_2, hmul_lt, hlt, hw_ne]
    have hcsr3 : AdjCsrAt st3.mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X) := by
      have h1 := hdisj.ro_off_cfg; have h2 := hdisj.ro_nb_cfg; have h3 := hdisj.ro_edge_cfg
      unfold DisjRange at h1 h2 h3
      exact hcsr2.congr
        (fun k hk => hmem3_eq_st2 (cfg.offAddr + k) (by rcases h1 with x | x <;> omega))
        (fun k hk => hmem3_eq_st2 (cfg.nbAddr + k) (by rcases h2 with x | x <;> omega))
        (fun k hk => hmem3_eq_st2 (cfg.edgeAddr + k) (by rcases h3 with x | x <;> omega))
    have hlp3 : LocalPairsAt st3.mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X br.remPairs X.card := by
      have h1 := hdisj.pb_cfg; have h2 := hdisj.ro_ao_cfg; have h3 := hdisj.al_cfg; have h4 := hdisj.ad_cfg
      unfold DisjRange at h1 h2 h3 h4
      refine ⟨fun v hv => by rw [hmem3_eq_st2 _ (by rcases h1 with x | x <;> omega)]; exact hlp2.1 v hv,
        ⟨by rw [hmem3_eq_st2 _ (by rcases h2 with x | x <;> omega)]; exact hlp2.2.1, fun j hj => ?_⟩⟩
      have h_j := hlp2.2.2 j hj
      have ho1 := hmem3_eq_st2 (cfg.aOffAddr + j) (by rcases h2 with x | x <;> omega)
      have ho2 := hmem3_eq_st2 (cfg.aOffAddr + j + 1) (by rcases h2 with x | x <;> omega)
      have hl := hmem3_eq_st2 (cfg.aLenAddr + j) (by rcases h3 with x | x <;> omega)
      refine ⟨by rw [ho1, ho2, hl]; exact h_j.1, by rw [hl]; exact h_j.2.1, fun t ht => ?_⟩
      have ht_le : st2.mem (cfg.aOffAddr + j) + t < X.card := by
        have hmo := localAPairsAt_slot_bound hlp2.2 (j + 1) br.remPairs.length (by omega) le_rfl
        have := hlp2.2.1; have := h_j.1; have := h_j.2.1
        rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmo
        simp only [List.length_map, Finset.length_sort] at ht; omega
      rw [ho1, Nat.add_assoc, hmem3_eq_st2 _ (by rcases h4 with x | x <;> omega), ← Nat.add_assoc]
      exact h_j.2.2 t ht
    obtain ⟨stF, c4, hrun4, hmF17, hbLoF, hbHiF, hmF19, hbgLoF, hbgHiF, hmF21, hmF22, hmF23,
      hmF24, hmF25, hisoLeF, hmaLeF, hvisF, hcurF, husedF, hdeadF, hballF, hliveF,
      hsubF, hulF, hfrF, hc4⟩ :=
      batchCutBranch_triple hres_proc hcurb_proc hball_proc hbfs_proc
        (h := routeH Δ b) (L := L) hhL hnX (hk.trans hbr_rem_len.symm)
        (batchRoutePairs_remVerts_sub _ _ _ _).1 hbr_valid hm2_le hdisj
        hbLo2 (by rw [hk]; exact hbHi2) hdLo2 (by rw [hk]; exact hdHi2) hpLo2 hp_hi_nX hcLo2 hc_hi_lim
        (fun o ho => (hmem3_eq_st2 _ (Or.inl (by omega))).trans (hcfgRo2 o (by omega)))
        hcfg.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by simp only [st3, mem3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
             Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self])
        (by simp only [st3, mem3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self])
        (by simp only [st3, mem3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
             Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hcfgRo2 20 (by decide)).trans hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (by simp only [st3, mem3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
             Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hcfgRo2 21 (by decide)).trans hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (by simp only [st3, mem3]; rw [Function.update_of_ne (by omega), Function.update_self])
        (by simp only [st3, mem3]; rw [Function.update_self])
        hcsr3 hlp3
        (fun v hv => by rw [hmem3_ws _ (by unfold wsIsoStamp; omega) (by unfold wsIsoStamp batchScratchSize; omega)]; exact hiso2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsIsoStamp; omega) (by unfold wsIsoStamp batchScratchSize; omega)]; exact hisoLe2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsMatchAStamp; omega) (by unfold wsMatchAStamp batchScratchSize; omega)]; exact hmaLe2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsVisStamp; omega) (by unfold wsVisStamp batchScratchSize; omega)]; exact hvis2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsCurStamp; omega) (by unfold wsCurStamp batchScratchSize; omega)]; exact hcur2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsUsedStamp; omega) (by unfold wsUsedStamp batchScratchSize; omega)]; exact hused2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsDeadStamp; omega) (by unfold wsDeadStamp batchScratchSize; omega)]; exact hdead2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsBallStamp; omega) (by unfold wsBallStamp batchScratchSize; omega)]; exact hball2 v hv)
        (fun v hv => by rw [hmem3_ws _ (by unfold wsLiveStamp; omega) (by unfold wsLiveStamp batchScratchSize; omega)]; exact hlive2 v hv)
        (hsub2.of_outside_124 fun a ha1 ha2 => hmem3_ws a ha1 (by unfold batchScratchSize; omega))
        hfr3
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2_0)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 1 (Or.inl (by decide))).trans hregs1.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 2 (Or.inl (by decide))).trans hregs1.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 8 (Or.inl (by decide))).trans hregs1.2.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 9 (Or.inl (by decide))).trans hregs1.2.2.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 10 (Or.inl (by decide))).trans hregs1.2.2.2.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 11 (Or.inl (by decide))).trans hregs1.2.2.2.2.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact (hregs2_le28 14 (Or.inl (by decide))).trans hregs1.2.2.2.2.2.2.2.2.2.1)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2_17)
        (by simp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]) ω
    have hrunCond : Runs w p ω condStmt st3 (.returned 1) stF _ :=
      batch_runs_cond_pos hcond1 (by decide) hrun4
    obtain ⟨c34, hrun34, hc34⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3
      (show Runs w p ω (seqStmts [condStmt]) st3 (.returned 1) stF _ from hrunCond)
    have hrun24 : Runs w p ω (Stmt.seq (batchRouteLoopStmt bSp) (seqStmts
        [ .store (.bin .add (.reg 0) (.const 17)) (.reg 17)
        , .store (.bin .add (.reg 0) (.const 18)) (.reg 18)
        , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
        , .store (.bin .add (.reg 0) (.const 22)) (.reg 20)
        , .store (.bin .add (.reg 0) (.const 23)) (.reg 21)
        , .assign 26 (.load (.bin .add (.reg 0) (.const 4)))
        , .assign 27 (.load (.bin .add (.reg 0) (.const 16)))
        , condStmt ])) st1 (.returned 1) stF (c2 + c34 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, c34, hrun2, hrun34, rfl⟩)
    have hrunAll : Runs w p ω (runBatchProc bSp bRes bCurB bBall) st0 (.returned 1) stF (c1 + (c2 + c34 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, hrun24, rfl⟩)
    set Hres : Graph := ⟨G.n, G.inside br.remVerts⟩
    set baseC := br.cost + pairs.length + 1 + (X.card + 2 * (G.inside X).length + 1)
    set cutRes0 := batchBallLoop (adjOf Hres X) X cfg.b (routeH Δ b) L br.remPairs ∅ X 0
    have hadd_b := batchBallLoop_cost_add (adjOf Hres X) X cfg.b (routeH Δ b) L br.remPairs ∅ X 0 baseC
    simp only [Nat.zero_add] at hadd_b
    have hres_eq : runBatch G X Δ b L pairs =
        { outcome := .cut cutRes0.1, cost := cutRes0.2 + baseC } := by
      unfold runBatch; dsimp only
      rw [← hd, ← hHb, ← hdem]
      split_ifs with h
      · exact absurd h hsucc
      · rw [hb] at hadd_b
        simp only [BatchResult.mk.injEq, BatchOutcome.cut.injEq, cutRes0, hb]
        exact ⟨hadd_b.1, hadd_b.2⟩
    refine ⟨.returned 1, stF, _, hrunAll, ?_, ?_⟩
    · rw [hres_eq]
      dsimp only [retPost, BatchOutAt]
      refine ⟨rfl, ⟨hmF17, hbLoF, hbHiF,
        by rw [hmF19]; exact hdLo2, by rw [hmF19, hk]; exact hdHi2,
        hbgLoF, hbgHiF,
        by rw [hmF21]; omega, by rw [hmF21],
        by rw [hmF22]; exact hpLo2, by rw [hmF22]; exact hp_hi_nX,
        by rw [hmF22]; omega,
        by rw [hmF23]; exact hcLo2, by rw [hmF23]; exact hc_hi_lim,
        fun v hv => by rw [hmF17]; exact hisoLeF v hv,
        fun v hv => by rw [hmF17]; exact hmaLeF v hv,
        hvisF,
        fun v hv => by rw [hmF19]; exact hcurF v hv,
        fun v hv => by rw [hmF19]; exact husedF v hv,
        fun v hv => by rw [hmF19]; exact hdeadF v hv,
        hballF,
        fun v hv => by rw [hmF21]; exact hliveF v hv,
        hsubF, hmF24, hmF25, hulF⟩, hfrF⟩
    · rw [hres_eq]
      dsimp only [batchProgCost, buildResCsrCost, buildCurBCost, baseC] at hc4 ⊢
      simp only [Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc3 hc4 hc34
      omega

/-- Contract for `runBatchProc` (Procedure 4) on argument `[cfgAddr]`. -/
@[expose] def runBatchContract (w : ℕ) (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ))
    (cfg : BatchCfg) (pLo pHi cLo cHi hL : ℕ)
    (accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let cfgAddr := args.getD 0 0
    cfg.nX = X.card ∧
    cfg.k = pairs.length ∧
    cfg.m2 = 2 * (G.inside X).length ∧
    cfg.d = routeD Δ b L ∧
    cfg.b = b ∧
    cfg.Hbatch = routeHBatch Δ b L ∧
    routeH Δ b * L = hL ∧
    cfg.curDemandIn = totalDemand pairs ∧
    ValidTerminalPairs X pairs ∧
    BatchCfgAt mem cfgAddr cfg ∧
    BatchSubCfgsInit mem cfg hL ∧
    BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg ∧
    AdjCsrAt mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X) ∧
    LocalPairsAt mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X pairs X.card ∧
    (∀ v < X.card, mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn) ∧
    (∀ v < X.card, mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn) ∧
    (∀ v < X.card, mem (wsVisStamp cfg.ws cfg.nX + v) ≤ cfg.bfsGenIn) ∧
    (∀ v < X.card, mem (wsCurStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn) ∧
    (∀ v < X.card, mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn) ∧
    (∀ v < X.card, mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ cfg.dfsGenIn) ∧
    (∀ v < X.card, mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.ballGenIn) ∧
    (∀ v < X.card, mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn) ∧
    (∀ j < pairs.length,
      ChunkChainAt mem X pLo cfg.pathHeapIn cLo cfg.chunkHeapIn
        (mem (cfg.accHeadAddr + j)) (mem (cfg.accTailAddr + j)) (accChunks.getD j [])) ∧
    ChunksDisj mem cfg.accHeadAddr pairs.length (fun j => (accChunks.getD j []).length)
  post args mem v mem' :=
    let cfgAddr := args.getD 0 0
    let res := runBatch G X Δ b L pairs
    (match res.outcome with | .matched _ _ => v = 0 | .cut _ => v = 1) ∧
    BatchOutAt mem' X cfg cfgAddr pLo pHi cLo cHi hL accChunks res ∧
    (∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → mem' a = mem a)
  cost _ _ := batchProgCost (runBatch G X Δ b L pairs).cost

/-- `runBatchProc` deterministically meets `runBatchContract`. -/
theorem runBatch_meetsContract {w : ℕ} {p : Program}
    {idx bSp bBfs bDfs bRes bCurB bBall : ℕ}
    (hproc : p.procs[idx]? = some (runBatchProc bSp bRes bCurB bBall))
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ))
    (cfg : BatchCfg) (pLo pHi cLo cHi hL : ℕ)
    (accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))) :
    MeetsContract w p idx
      (runBatchContract w G X Δ b L pairs cfg pLo pHi cLo cHi hL accChunks) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hnX, hk, hm2, hd, hb, hHb, hhL, hdem, hvalid, hcfg, hsub, hdisj,
    hcsr, hlp, hiso0, hma0, hvis0, hcur0, hused0, hdead0, hball0, hlive0, hch0, hchDisj0⟩
  have htr := runBatch_triple (w := w) (p := p) (st0 := startState args mem pos)
    hsp_proc hbfs_proc hdfs_proc hres_proc hcurb_proc hball_proc
    hnX hk hm2 hd hb hHb hhL hdem hvalid hcfg hsub hdisj hcsr hlp
    hiso0 hma0 hvis0 hcur0 hused0 hdead0 hball0 hlive0 hch0 hchDisj0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨runBatchProc bSp bRes bCurB bBall, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
