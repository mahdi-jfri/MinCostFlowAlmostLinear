module

public import MinCostFlow.ExpanderDecomp.RouteProgBallBfs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Ball Growing Program Verification (`RouteProgBall`)

Completes the full correctness and cost verification of `growBallProc` (Procedure 3) from
`RouteProgBallSpec.lean` / `RouteProgBallBase.lean` / `RouteProgBallScan.lean` /
`RouteProgBallBfs.lean`, matching the exact model `growBall adj V S T b h L` in `RouteBall.lean`
with deterministic Word-RAM cost `≤ ballProgCost (growBall adj V S T b h L).cost`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

theorem growBall_triple {w : ℕ} {p : Program} {bBfs : ℕ}
    {X V S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {h L : ℕ}
    {cfg : BallCfg} {bfsCfg : BfsCfg} {cfgAddr m2 : ℕ} {st0 : State}
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hVX : V ⊆ X)
    (hSV : S ⊆ V)
    (hTV : T ⊆ V)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcfg : BallCfgAt st0.mem cfgAddr cfg)
    (hbfs_cfg : BfsCfgAt st0.mem cfg.bfsCfgAddr bfsCfg)
    (hmaxDist : bfsCfg.maxDist = h * L)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BallDisj w X.card m2 cfg bfsCfg cfgAddr)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hs_list : ListAt st0.mem cfg.sPtr ((S.sort (· ≤ ·)).map (locOf X)))
    (hs_len : cfg.sLen = S.card)
    (ht_list : ListAt st0.mem cfg.tPtr ((T.sort (· ≤ ·)).map (locOf X)))
    (ht_len : cfg.tLen = T.card)
    (hvis0 : ∀ v < X.card, st0.mem (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn)
    (hbs0 : ∀ v < X.card, st0.mem (cfg.ballStampAddr + v) ≤ cfg.ballGenIn)
    (hr0 : st0.regs 0 = cfgAddr) :
    let res := growBall adj V S T cfg.b h L
    Triple w p (fun st => st = st0) (growBallProc bBfs)
      (retPost fun v st' =>
        v = res.ball.card ∧
        BallOutAt st'.mem X cfg bfsCfg cfgAddr res ∧
        (∀ a, ¬ BallWriteSet X.card cfg bfsCfg cfgAddr a → st'.mem a = st0.mem a))
      (fun _ => ballProgCost (growBall adj V S T cfg.b h L).cost) := by
  have hbS := hdisj.bfs_disj_S
  have hbT := hdisj.bfs_disj_T
  have hw_cfg := hdisj.w_cfg
  have hw_off : cfg.offAddr + X.card + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_off] at this; exact this
  have hw_nb : cfg.nbAddr + m2 + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_nb] at this; exact this
  have hw_mask : cfg.maskArrAddr + X.card + 5 < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_mask] at this; exact this
  have hw_lOffS : cfg.layerOffS + X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lDataS : cfg.layerDataS + X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lOffT : cfg.layerOffT + X.card + 5 < 2 ^ w := hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_lDataT : cfg.layerDataT + X.card + 5 < 2 ^ w := hbT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_mb : cfg.maskBadVal < 2 ^ w := by
    have := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; dsimp only at this; rw [hdisj.bfs_bad] at this; exact this
  have hw_m2 : m2 + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_nX : X.card + 5 < 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw4 : 4 ≤ 2 ^ w := hbS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw_bs := hdisj.w_bs
  have hw_bl := hdisj.w_bl
  have hw_ballgen := hdisj.w_ballgen
  have hw_mul := hdisj.w_mul
  have hw_b16 := hdisj.w_b16
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  dsimp only
  intro st ω hst; subst hst
  set bfsS := bfsLayers adj V S (h * L) ∅
  set bfsT := bfsLayers adj V T (h * L) ∅
  set selBfs := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
  set selOff := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerOffS else cfg.layerOffT
  set selData := if bfsS.visited.card ≤ bfsT.visited.card then cfg.layerDataS else cfg.layerDataT
  -- Steps 1-3: Load BallCfg + BFS from S + BFS from T
  obtain ⟨stT, cST, hrunST, hregsT, hT19, hT20, hT21, hT22, hT23,
      hcsrT, hmaskT, hsel_loff, hsel_ldata, hbsT_le, hvisT_le, hT_fr_all, hcST⟩ :=
    growBallBfsST_triple hbfs_proc hVX hSV hTV hadj_X hcfg hbfs_cfg hmaxDist hcsr hm2 hdisj
      hmask hs_list hs_len ht_list ht_len hvis0 hbs0 hr0 ω
  change stT.regs 20 = bfsS.visited.card at hT20
  change stT.regs 21 = bfsS.layers.length at hT21
  change stT.regs 22 = bfsT.visited.card at hT22
  change stT.regs 23 = bfsT.layers.length at hT23
  change cST ≤ bfsProgCost bfsS.cost + bfsProgCost bfsT.cost + 350 at hcST
  -- Step 4: Select smaller ball via .cond (r22 < r20)
  set stSel : State :=
    { mem := stT.mem
      regs := Function.update (Function.update (Function.update stT.regs 24 selOff)
        25 selData) 26 selBfs.layers.length
      pos := stT.pos }
  have hcond_sel : ∃ cSel,
      Runs w p ω
        (.cond (.bin .lt (.reg 22) (.reg 20))
          (seqStmts [ .assign 24 (.reg 8), .assign 25 (.reg 9), .assign 26 (.reg 23) ])
          (seqStmts [ .assign 24 (.reg 6), .assign 25 (.reg 7), .assign 26 (.reg 21) ]))
        stT .normal stSel cSel ∧ cSel ≤ 20 := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card
    · have hnotlt : ¬ bfsT.visited.card < bfsS.visited.card := by omega
      have hev : (Expr.bin .lt (.reg 22) (.reg 20)).eval w stT = some 0 := by
        simp [Expr.eval, BinOp.eval, hT22, hT20, hnotlt]
      have h0 : ∃ o s c,
          Runs w p ω
            (.cond (.bin .lt (.reg 22) (.reg 20))
              (seqStmts [ .assign 24 (.reg 8), .assign 25 (.reg 9), .assign 26 (.reg 23) ])
              (seqStmts [ .assign 24 (.reg 6), .assign 25 (.reg 7), .assign 26 (.reg 21) ]))
            stT o s c ∧ (o = .normal ∧ s = stSel) ∧ 0 + c ≤ 20 := by
        refine runs_cond_zero_le hev ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := cfg.layerOffS)
          (by simp [Expr.eval, hregsT 6 (by decide)]) ?_
        refine runs_seq_assign_le (v := cfg.layerDataS)
          (by simp [Expr.eval, hregsT 7 (by decide)]) ?_
        refine runs_assign_le (v := bfsS.layers.length)
          (by simp [Expr.eval, hT21]) ?_ (by wram_cost)
        exact ⟨rfl, by simp [stSel, selBfs, selOff, selData, hle]⟩
      rcases h0 with ⟨_, _, cSel, hrun, ⟨rfl, rfl⟩, hcSel⟩
      exact ⟨cSel, hrun, by omega⟩
    · have hlt : bfsT.visited.card < bfsS.visited.card := by omega
      have hev : (Expr.bin .lt (.reg 22) (.reg 20)).eval w stT = some 1 := by
        simp [Expr.eval, BinOp.eval, hT22, hT20, hlt, hw_ne]
      have h0 : ∃ o s c,
          Runs w p ω
            (.cond (.bin .lt (.reg 22) (.reg 20))
              (seqStmts [ .assign 24 (.reg 8), .assign 25 (.reg 9), .assign 26 (.reg 23) ])
              (seqStmts [ .assign 24 (.reg 6), .assign 25 (.reg 7), .assign 26 (.reg 21) ]))
            stT o s c ∧ (o = .normal ∧ s = stSel) ∧ 0 + c ≤ 20 := by
        refine runs_cond_pos_le hev (by decide) ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := cfg.layerOffT)
          (by simp [Expr.eval, hregsT 8 (by decide)]) ?_
        refine runs_seq_assign_le (v := cfg.layerDataT)
          (by simp [Expr.eval, hregsT 9 (by decide)]) ?_
        refine runs_assign_le (v := bfsT.layers.length)
          (by simp [Expr.eval, hT23]) ?_ (by wram_cost)
        exact ⟨rfl, by simp [stSel, selBfs, selOff, selData, hle]⟩
      rcases h0 with ⟨_, _, cSel, hrun, ⟨rfl, rfl⟩, hcSel⟩
      exact ⟨cSel, hrun, by omega⟩
  rcases hcond_sel with ⟨cSel, hrunSel, hcSel⟩
  -- Step 5: Initialize r27, r28, r29, r30 and run ballScanLayersStmt + ballWriteRetStmt
  set stInit : State :=
    { mem := stT.mem
      regs := Function.update (Function.update (Function.update (Function.update
        stSel.regs 27 (cfg.ballGenIn + 1)) 28 0) 29 0) 30 0
      pos := stT.pos }
  have hinit_step : ∃ cInit,
      Runs w p ω
        (seqStmts
          [ .assign 27 (.bin .add (.reg 17) (.const 1))
          , .assign 28 (.const 0)
          , .assign 29 (.const 0)
          , .assign 30 (.const 0) ])
        stSel .normal stInit cInit ∧ cInit ≤ 20 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 27 (.bin .add (.reg 17) (.const 1))
            , .assign 28 (.const 0)
            , .assign 29 (.const 0)
            , .assign 30 (.const 0) ])
          stSel o s c ∧ (o = .normal ∧ s = stInit) ∧ 0 + c ≤ 20 := by
      dsimp only [seqStmts]
      have hsel17 : stSel.regs 17 = cfg.ballGenIn := by simp [stSel, hregsT 17 (by decide)]
      refine runs_seq_assign_le (v := cfg.ballGenIn + 1) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, cInit, hrun, ⟨rfl, rfl⟩, hcInit⟩
    exact ⟨cInit, hrun, by omega⟩
  rcases hinit_step with ⟨cInit, hrunInit, hcInit⟩
  -- Selected BFS properties
  have hsel_linv : selBfs.visited ⊆ V ∧ selBfs.layers.flatten.Nodup ∧
      (∀ x, x ∈ selBfs.layers.flatten ↔ x ∈ selBfs.visited) ∧
      selBfs.layers.flatten.length = selBfs.visited.card ∧ selBfs.layers.length ≤ V.card := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card
    · simp only [selBfs, hle, ↓reduceIte]; exact bfsLayers_layers_inv adj V S (h * L) ∅
    · simp only [selBfs, hle, ↓reduceIte]; exact bfsLayers_layers_inv adj V T (h * L) ∅
  have hsel_disj_bs_loff : DisjRange cfg.ballStampAddr X.card selOff (X.card + 1) := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selOff, hle, hdisj.bs_lOffS, hdisj.bs_lOffT]
  have hsel_disj_bs_data : DisjRange cfg.ballStampAddr X.card selData X.card := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selData, hle, hdisj.bs_lDataS, hdisj.bs_lDataT]
  have hsel_disj_bl_loff : DisjRange cfg.ballListAddr X.card selOff (X.card + 1) := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selOff, hle, hdisj.bl_lOffS, hdisj.bl_lOffT]
  have hsel_disj_bl_data : DisjRange cfg.ballListAddr X.card selData X.card := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selData, hle, hdisj.bl_lDataS, hdisj.bl_lDataT]
  have hw_selOff : selOff + X.card + 5 < 2 ^ w := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selOff, hle, hw_lOffS, hw_lOffT]
  have hw_selData : selData + X.card + 5 < 2 ^ w := by
    by_cases hle : bfsS.visited.card ≤ bfsT.visited.card <;> simp [selData, hle, hw_lDataS, hw_lDataT]
  have hbsInit_iff : ∀ v < X.card,
      stInit.mem (cfg.ballStampAddr + v) = cfg.ballGenIn + 1 ↔
      origOf X v ∈ (selBfs.layers.take 0).flatten.toFinset := by
    intro v hv
    simp only [stInit, List.take_zero, List.flatten_nil, List.toFinset_nil, Finset.notMem_empty,
      iff_false]
    have := hbsT_le v hv; omega
  obtain ⟨stScan, cScan, hrunScan, hpostScan, hcScan⟩ :=
    ballScanLayers_triple (p := p) (layers := selBfs.layers) hVX hadj_X hm2
      hsel_linv.2.1 (fun x hx => hsel_linv.1 ((hsel_linv.2.2.1 x).mp hx))
      (le_trans hsel_linv.2.2.2.2 (Finset.card_le_card hVX))
      (by rw [hsel_linv.2.2.2.1]; exact Finset.card_le_card (Finset.Subset.trans hsel_linv.1 hVX))
      hdisj.bs_bl hdisj.bs_off hdisj.bs_nb hdisj.bs_mask hsel_disj_bs_loff hsel_disj_bs_data
      hdisj.bl_off hdisj.bl_nb hdisj.bl_mask hsel_disj_bl_loff hsel_disj_bl_data
      hw_off hw_nb hw_mask hw_bs hw_bl hw_selOff hw_selData hw_m2 hw_nX hw_mb
      (by omega) hw_mul hw_b16 (by omega) hw4
      selBfs.layers.length 0 0 [] stInit (Nat.zero_add _)
      (by simp only [List.take_zero, List.flatten_nil, List.toFinset_nil, Finset.sdiff_empty, Nat.zero_add]
          exact sum_adj_sub_le_m2 hVX hm2)
      hcsrT hmaskT hsel_loff hsel_ldata
      hbsInit_iff
      (fun v hv => by simp only [stInit]; have := hbsT_le v hv; omega)
      (by simp) List.nodup_nil (fun _ h => by cases h) (fun _ h => by simp at h)
      (fun _ h => by simp at h)
      (by simp [stInit, stSel, hregsT 2 (by decide)])
      (by simp [stInit, stSel, hregsT 3 (by decide)])
      (by simp [stInit, stSel, hregsT 4 (by decide)])
      (by simp [stInit, stSel, hregsT 5 (by decide)])
      (by simp [stInit, stSel, hregsT 14 (by decide)])
      (by simp [stInit, stSel, hregsT 15 (by decide)])
      (by simp [stInit, stSel, hregsT 18 (by decide)])
      (by simp [stInit, stSel]) (by simp [stInit, stSel]) (by simp [stInit, stSel])
      (by simp [stInit]) (by simp [stInit]) (by simp [stInit]) (by simp [stInit]) ω
  simp only [List.take_zero, List.flatten_nil, List.toFinset_nil, List.drop_zero] at hpostScan hcScan
  rcases hpostScan with ⟨hrScan, hScan28, hbsScan, hbsScan_le, hblScan, hfrScan⟩
  -- Step 6: ballWriteRet_triple
  have hrScan0 : stScan.regs 0 = cfgAddr := by
    rw [hrScan 0 (by decide) (by decide)]; simp [stInit, stSel, hregsT 0 (by decide)]
  obtain ⟨oRet, stRet, cRet, hrunRet, hpostRet, hcRet⟩ :=
    ballWriteRet_triple (p := p) (st0 := stScan) hrScan0 hw_cfg stScan ω rfl
  cases oRet with
  | normal => exact hpostRet.elim
  | returned v =>
  rcases hpostRet with ⟨hvRet, h18, h19, h20, hfrRet⟩
  -- Chain st0 → stT → stSel → stInit → stScan → stRet into `growBallProc bBfs`
  have hrun_tail_scan : Runs w p ω (seqStmts [ ballScanLayersStmt, ballWriteRetStmt ])
      stInit (.returned v) stRet (cScan + cRet + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stScan, cScan, cRet, hrunScan, hrunRet, rfl⟩)
  obtain ⟨cA, hA, hcA⟩ := ball_runs_seqStmts_append (by simp) (by simp) hrunInit hrun_tail_scan
  simp only [List.length_cons, List.length_nil] at hcA
  have hrunSR : Runs w p ω
      (seqStmts
        [ .cond (.bin .lt (.reg 22) (.reg 20))
            (seqStmts [ .assign 24 (.reg 8), .assign 25 (.reg 9), .assign 26 (.reg 23) ])
            (seqStmts [ .assign 24 (.reg 6), .assign 25 (.reg 7), .assign 26 (.reg 21) ])
        , .assign 27 (.bin .add (.reg 17) (.const 1))
        , .assign 28 (.const 0)
        , .assign 29 (.const 0)
        , .assign 30 (.const 0)
        , ballScanLayersStmt
        , ballWriteRetStmt ])
      stT (.returned v) stRet (cSel + cA + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stSel, cSel, cA, hrunSel, hA, rfl⟩)
  obtain ⟨cAll, hrunAll, hcAll⟩ := ball_runs_seqStmts_append (by simp [ballBfsSTStmts]) (by simp) hrunST hrunSR
  simp only [ballBfsSTStmts, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hrunAll hcAll
  refine ⟨.returned v, stRet, cAll, hrunAll, ?_, ?_⟩
  · -- Postcondition
    have hadd_gb := scanBallLayers_cost_add adj V cfg.b selBfs.layers ∅ 0 0 (bfsS.cost + bfsT.cost + 1)
    simp only [Nat.zero_add] at hadd_gb
    have hball_eq : (growBall adj V S T cfg.b h L).ball =
        (scanBallLayers adj V cfg.b selBfs.layers ∅ 0 0).1 := by
      dsimp only [growBall]; exact hadd_gb.1
    have hrScan19 : stScan.regs 19 = cfg.bfsGenIn + 2 := by
      rw [hrScan 19 (by decide) (by decide)]; simp [stInit, stSel, hT19]
    have hrScan27 : stScan.regs 27 = cfg.ballGenIn + 1 := by
      rw [hrScan 27 (by decide) (by decide)]; simp [stInit]
    dsimp only [retPost, BallOutAt]
    rw [hball_eq]
    refine ⟨hvRet.trans hScan28, ⟨h18.trans hScan28, h19.trans hrScan19, h20.trans hrScan27,
      ?_, ?_, ?_, ?_⟩, ?_⟩
    · rcases hblScan with ⟨bl', hlen', hnd', hsub', hcov', hat'⟩
      refine ⟨bl', hlen', hnd', hsub', hcov', fun j hj => ?_⟩
      have hj_lt : j < X.card := by
        have hlen_le : bl'.length ≤ X.card := by
          have : bl'.toFinset ⊆ Finset.range X.card := fun x hx =>
            Finset.mem_range.mpr (hsub' x (List.mem_toFinset.mp hx)).1
          have := Finset.card_le_card this
          rwa [List.toFinset_card_of_nodup hnd', Finset.card_range] at this
        omega
      rw [hfrRet _ (by rcases hdisj.bl_cfg with x | x <;> omega)]
      exact hat' j hj
    · intro u hu
      rw [hfrRet _ (by rcases hdisj.bs_cfg with x | x <;> omega)]
      exact hbsScan u hu
    · intro u hu
      rw [hfrRet _ (by rcases hdisj.bs_cfg with x | x <;> omega)]
      exact hbsScan_le u hu
    · intro u hu
      rw [hfrRet _ (by rcases hdisj.cfg_vis with x | x <;> omega),
          hfrScan _ (by rcases hdisj.bs_vis with x | x <;> omega) (by rcases hdisj.bl_vis with x | x <;> omega)]
      exact hvisT_le u hu
    · intro a ha
      rw [hfrRet a (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))))))),
          hfrScan a
            (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))))))
            (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))))))]
      exact hT_fr_all a ha
  · -- Cost bound
    have hadd_gb := scanBallLayers_cost_add adj V cfg.b selBfs.layers ∅ 0 0 (bfsS.cost + bfsT.cost + 1)
    simp only [Nat.zero_add] at hadd_gb
    have hcost_eq : (growBall adj V S T cfg.b h L).cost =
        (scanBallLayers adj V cfg.b selBfs.layers ∅ 0 0).2 + (bfsS.cost + bfsT.cost + 1) := by
      dsimp only [growBall]; exact hadd_gb.2
    rw [hcost_eq]
    dsimp only at hcRet
    simp only [bfsProgCost, ballProgCost] at hcST ⊢
    omega

/-- Contract for `growBallProc` on argument `[cfgAddr]`. -/
@[expose] def growBallContract (w : ℕ) (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ))
    (h L : ℕ) (cfg : BallCfg) (bfsCfg : BfsCfg) (m2 : ℕ) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let cfgAddr := args.getD 0 0
    V ⊆ X ∧
    S ⊆ V ∧
    T ⊆ V ∧
    (∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X) ∧
    BallCfgAt mem cfgAddr cfg ∧
    BfsCfgAt mem cfg.bfsCfgAddr bfsCfg ∧
    bfsCfg.maxDist = h * L ∧
    NbCsrAt mem cfg.offAddr cfg.nbAddr X adj ∧
    adjCsrOff X adj X.card ≤ m2 ∧
    BallDisj w X.card m2 cfg bfsCfg cfgAddr ∧
    (∀ v < X.card, mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) ∧
    ListAt mem cfg.sPtr ((S.sort (· ≤ ·)).map (locOf X)) ∧
    cfg.sLen = S.card ∧
    ListAt mem cfg.tPtr ((T.sort (· ≤ ·)).map (locOf X)) ∧
    cfg.tLen = T.card ∧
    (∀ v < X.card, mem (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn) ∧
    (∀ v < X.card, mem (cfg.ballStampAddr + v) ≤ cfg.ballGenIn)
  post args mem v mem' :=
    let cfgAddr := args.getD 0 0
    let res := growBall adj V S T cfg.b h L
    v = res.ball.card ∧
    BallOutAt mem' X cfg bfsCfg cfgAddr res ∧
    (∀ a, ¬ BallWriteSet X.card cfg bfsCfg cfgAddr a → mem' a = mem a)
  cost _ _ := ballProgCost (growBall adj V S T cfg.b h L).cost

/-- `growBallProc` meets `growBallContract` deterministically. -/
theorem growBall_meetsContract {w : ℕ} {p : Program} {idx bBfs : ℕ}
    (hproc : p.procs[idx]? = some (growBallProc bBfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ)) (h L : ℕ)
    (cfg : BallCfg) (bfsCfg : BfsCfg) (m2 : ℕ) :
    MeetsContract w p idx (growBallContract w X V S T adj h L cfg bfsCfg m2) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hVX, hSV, hTV, hadj_X, hcfg, hbfs_cfg, hmaxDist, hcsr, hm2, hdisj,
    hmask, hs_list, hs_len, ht_list, ht_len, hvis0, hbs0⟩
  have htr := growBall_triple (w := w) (p := p) (st0 := startState args mem pos)
    hbfs_proc hVX hSV hTV hadj_X hcfg hbfs_cfg hmaxDist hcsr hm2 hdisj hmask
    hs_list hs_len ht_list ht_len hvis0 hbs0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨growBallProc bBfs, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
