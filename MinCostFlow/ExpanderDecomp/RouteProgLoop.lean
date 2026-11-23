module

public import MinCostFlow.ExpanderDecomp.RouteProgLoopInd

/-!
# Outer Batch-Loop Procedure Verification (`RouteProgLoop`)

Completes the deterministic Word-RAM verification of Procedure 5 (`routeOrCutCsrProc`),
implementing `routeOrCut` on prebuilt local CSR and local terminal pairs:
- `routeOrCutCsr_triple`: full Hoare triple for `routeOrCutCsrProc`.
- `routeOrCutCsrContract`, `routeOrCutCsr_meetsContract`: deterministic contract satisfaction
  writing `RouteOutAt` at `outAddr` and `WalksAt` at `walksAddr` (when matched), with literal
  cost bound `routeCsrProgCost (routeOrCutCost G X pairs Δ L b z)` and tight framing outside
  `mem' (cfgAddr + 22) + 15 * nX`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

theorem routeOrCutCsr_triple {w : ℕ} {p : Program}
    {bBatch bSp bBfs bDfs bRes bCurB bBall : ℕ}
    (hbatch_proc : p.procs[bBatch]? = some (runBatchProc bSp bRes bCurB bBall))
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    {G : Graph} {X : Finset ℕ} {Δ b L : ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    {rcfg : RouteLoopCfg} {cfgAddr pLo pHi cLo cHi : ℕ} {st0 : State}
    (hnX : rcfg.batch.nX = X.card) (hk : rcfg.batch.k = pairs.length)
    (hm2 : rcfg.batch.m2 = 2 * (G.inside X).length)
    (hd : rcfg.batch.d = routeD Δ b L) (hb : rcfg.batch.b = b)
    (hHb : rcfg.batch.Hbatch = routeHBatch Δ b L)
    (hR : rcfg.R = routeR Δ b L) (hhL : routeH Δ b * L = rcfg.hL)
    (hdem : rcfg.batch.curDemandIn = totalDemand pairs)
    (hvalid : ValidTerminalPairs X pairs)
    (hX_w : ∀ v ∈ X, v < 2 ^ w)
    (hcfg : RouteLoopCfgAt st0.mem cfgAddr rcfg)
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    (hpHi_res : rcfg.batch.pathHeapIn + 5 * routeOrCutCost G X pairs Δ L b rcfg.z + 15 * rcfg.batch.nX ≤ pHi)
    (hcsr : AdjCsrAt st0.mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X))
    (hlp : LocalPairsAt st0.mem rcfg.batch.pairBAddr rcfg.batch.aOffAddr rcfg.batch.aLenAddr
      rcfg.batch.aDataAddr X pairs X.card)
    (horig : ListAt st0.mem rcfg.origVertAddr (sortedX X))
    (hacc0 : ∀ j < pairs.length,
      st0.mem (rcfg.batch.accHeadAddr + j) = 0 ∧ st0.mem (rcfg.batch.accTailAddr + j) = 0)
    (hiso0 : ∀ v < X.card, st0.mem (wsIsoStamp rcfg.batch.ws + v) ≤ rcfg.batch.batchGenIn)
    (hma0 : ∀ v < X.card, st0.mem (wsMatchAStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.batchGenIn)
    (hvis0 : ∀ v < X.card, st0.mem (wsVisStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.bfsGenIn)
    (hcur0 : ∀ v < X.card, st0.mem (wsCurStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn)
    (hused0 : ∀ v < X.card, st0.mem (wsUsedStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn)
    (hdead0 : ∀ v < X.card, st0.mem (wsDeadStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn)
    (hball0 : ∀ v < X.card, st0.mem (wsBallStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ rcfg.batch.ballGenIn)
    (hlive0 : ∀ v < X.card, st0.mem (wsLiveStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ rcfg.batch.liveGenIn)
    (hr0 : st0.regs 0 = cfgAddr) :
    let res := routeOrCut G X pairs Δ L b rcfg.z
    let rcost := routeOrCutCost G X pairs Δ L b rcfg.z
    Triple w p (fun st => st = st0) (routeOrCutCsrProc bBatch)
      (retPost fun v st' =>
        (match res with | .matched _ _ => v = 0 | .cut _ => v = 1) ∧
        RouteOutAt st'.mem rcfg.outAddr res ∧
        (match res with
         | .matched matchings emb =>
             WalksAt st'.mem rcfg.walksAddr matchings.flatten.length emb ∧
             (∀ idx < matchings.flatten.length,
               pLo ≤ st'.mem (rcfg.walksAddr + 1 + idx) ∧
               st'.mem (rcfg.walksAddr + 1 + idx) + 1 + (emb idx).length ≤ st'.mem (cfgAddr + 22))
         | .cut _ => True) ∧
        rcfg.batch.pathHeapIn ≤ st'.mem (cfgAddr + 22) ∧
        st'.mem (cfgAddr + 22) ≤ rcfg.batch.pathHeapIn + 5 * rcost ∧
        (∀ a, ¬ RouteLoopWriteSet rcfg cfgAddr (st'.mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
          st'.mem a = st0.mem a))
      (fun _ => routeCsrProgCost (routeOrCutCost G X pairs Δ L b rcfg.z)) := by
  dsimp only
  intro st ω hst; rcases hst.symm with rfl
  rcases hcfg with ⟨⟨m0, m1, _m2, _m3, _m4, _m5, _m6, _m7, _m8, _m9, _m10, _m11, m12, _m13,
    m14, m15, m16, m17, m18, m19, m20, m21, m22, m23⟩, m26, m27, m28, m29, m30, m31⟩
  have hcfg' : RouteLoopCfgAt st0.mem cfgAddr rcfg :=
    ⟨⟨m0, m1, _m2, _m3, _m4, _m5, _m6, _m7, _m8, _m9, _m10, _m11, m12, _m13,
      m14, m15, m16, m17, m18, m19, m20, m21, m22, m23⟩, m26, m27, m28, m29, m30, m31⟩
  have hw_cfg := hdisj.w_cfg; have hw_R := hdisj.w_R; have hw_z := hdisj.w_z
  have hw_out := hdisj.w_out; have hw_walks := hdisj.w_walks; have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro h0; subst h0; simp at hw4
  have hdem_le_X : totalDemand pairs ≤ X.card := totalDemand_le_card_X hvalid
  have hw_dem : rcfg.batch.curDemandIn < 2 ^ w := by have := hdisj.w_nX4; omega
  set regs1 := Function.update (Function.update (Function.update st0.regs 1 rcfg.batch.curDemandIn)
    2 rcfg.R) 3 rcfg.z
  set st1 : State := { st0 with regs := regs1 }
  have hload : ∃ c1,
      Runs w p ω
        (seqStmts
          [ .assign 1 (.load (.bin .add (.reg 0) (.const 16)))
          , .assign 2 (.load (.bin .add (.reg 0) (.const 26)))
          , .assign 3 (.load (.bin .add (.reg 0) (.const 27))) ])
        st0 .normal st1 c1 ∧ c1 ≤ 30 := by
    have h0 : ∃ o s c0,
        Runs w p ω
          (seqStmts
            [ .assign 1 (.load (.bin .add (.reg 0) (.const 16)))
            , .assign 2 (.load (.bin .add (.reg 0) (.const 26)))
            , .assign 3 (.load (.bin .add (.reg 0) (.const 27))) ])
          st0 o s c0 ∧ (o = .normal ∧ s = st1) ∧ 0 + c0 ≤ 30 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := rcfg.batch.curDemandIn) (by rw [← m16]; eval_expr) ?_
      refine runs_seq_assign_le (v := rcfg.R) (by rw [← m26]; eval_expr) ?_
      refine runs_assign_le (v := rcfg.z) (by rw [← m27]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩
  rcases hload with ⟨c1, hrun1, hc1⟩
  set condExpr : Expr := .bin .mul (.bin .lt (.reg 3) (.reg 1)) (.bin .lt (.const 0) (.reg 2))
  set mainBranch : Stmt := seqStmts
    [ initBatchSubCfgsStmt, routeBatchesLoopStmt bBatch, .cond (.reg 5) emitCutStmt emitMatchedStmt, .ret (.reg 5) ]
  by_cases hgo : rcfg.z < rcfg.batch.curDemandIn ∧ 0 < rcfg.R
  · -- Non-trivial branch: z < totalDemand pairs ∧ 0 < R
    have hcond1 : condExpr.eval w st1 = some 1 := by
      simp [condExpr, Expr.eval, BinOp.eval, st1, regs1, hgo.1, hgo.2,
        show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega]
    -- Stage 1: initBatchSubCfgsStmt
    obtain ⟨st2, c2, hrun2, hr2_0, hsub2, hfr2, hc2⟩ :=
      initBatchSubCfgs_triple (p := p) (st0 := st1) hdisj hcfg' (by dsimp only [st1, regs1]; simp [hr0]) ω
    have hfr2_out124 : ∀ a, ¬ (rcfg.batch.ws ≤ a ∧ a < rcfg.batch.ws + 124) → st2.mem a = st0.mem a := hfr2
    have hfr2_bws : ∀ a, ¬ BatchWriteSet rcfg.batch cfgAddr (st2.mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
        st2.mem a = st0.mem a := fun a ha =>
      hfr2_out124 a (by intro h; apply ha; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by unfold batchScratchSize; omega⟩)))))))
    have hcfg_ws := hdisj.cfg_ws; unfold DisjRange at hcfg_ws
    have hst2_cfg : ∀ o < 32, st2.mem (cfgAddr + o) = st0.mem (cfgAddr + o) := fun o ho =>
      hfr2_out124 _ (by unfold batchScratchSize at hcfg_ws; rcases hcfg_ws with x | x <;> omega)
    -- Stage 2: routeBatchesLoopStmt
    set regs3 := Function.update (Function.update (Function.update (Function.update st2.regs
      2 rcfg.R) 3 rcfg.z) 4 0) 5 0
    set st3 : State := { st2 with regs := regs3 }
    have hloopPre : ∃ c3,
        Runs w p ω
          (seqStmts
            [ .assign 2 (.load (.bin .add (.reg 0) (.const 26)))
            , .assign 3 (.load (.bin .add (.reg 0) (.const 27)))
            , .assign 4 (.const 0)
            , .assign 5 (.const 0) ])
          st2 .normal st3 c3 ∧ c3 ≤ 35 := by
      have hm26' : st2.mem (cfgAddr + 26) = rcfg.R := (hst2_cfg 26 (by decide)).trans m26
      have hm27' : st2.mem (cfgAddr + 27) = rcfg.z := (hst2_cfg 27 (by decide)).trans m27
      have h0 : ∃ o s c0,
          Runs w p ω
            (seqStmts
              [ .assign 2 (.load (.bin .add (.reg 0) (.const 26)))
              , .assign 3 (.load (.bin .add (.reg 0) (.const 27)))
              , .assign 4 (.const 0)
              , .assign 5 (.const 0) ])
            st2 o s c0 ∧ (o = .normal ∧ s = st3) ∧ 0 + c0 ≤ 35 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := rcfg.R) (by rw [← hm26']; eval_expr) ?_
        refine runs_seq_assign_le (v := rcfg.z) (by rw [← hm27']; eval_expr) ?_
        refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
        refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c3, h, ⟨rfl, rfl⟩, hc3⟩; exact ⟨c3, h, by omega⟩
    rcases hloopPre with ⟨c3, hrun3, hc3⟩
    set initChunks : List (List (List ((ℕ × ℕ) × List ℕ))) := List.replicate pairs.length []
    have hinit_flat : initChunks.map List.flatten = List.replicate pairs.length [] := by
      dsimp only [initChunks]; rw [List.map_replicate]; rfl
    have hinit_flat_len : (initChunks.map List.flatten).flatten.length = 0 := by
      rw [hinit_flat]; induction pairs.length with | zero => rfl | succ _ _ => simp
    have hraw_eq : routeOrCutRaw G X pairs Δ L b rcfg.z =
        routeBatches G X Δ b L rcfg.z rcfg.R pairs (initChunks.map List.flatten) 0 := by
      unfold routeOrCutRaw
      rw [ite_eq_right (fun h => by omega), hR, hinit_flat]
    have hinv3 : RouteLoopInv st3.mem st0.mem G X rcfg cfgAddr pLo pHi cLo cHi
        (totalDemand pairs) 0 pairs initChunks 0 := by
      have hro1 := hdisj.ro_off_ws; have hro2 := hdisj.ro_nb_ws; have hro3 := hdisj.ro_edge_ws
      have hro4 := hdisj.pb_ws; have hro5 := hdisj.ro_ao_ws; have hro6 := hdisj.al_ws
      have hro7 := hdisj.ad_ws; have hro8 := hdisj.ah_ws; have hro9 := hdisj.at_ws
      unfold DisjRange at hro1 hro2 hro3 hro4 hro5 hro6 hro7 hro8 hro9
      have hcsr3 : AdjCsrAt st3.mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X) :=
        hcsr.congr
          (fun j hj => hfr2_out124 _ (by unfold batchScratchSize at hro1; rcases hro1 with x | x <;> omega))
          (fun j hj => hfr2_out124 _ (by have : adjCsrOff X (adjOf G X) X.card ≤ rcfg.batch.m2 := by rw [adjCsrOff_adjOf_card, hm2]
                                         unfold batchScratchSize at hro2; rcases hro2 with x | x <;> omega))
          (fun j hj => hfr2_out124 _ (by have : adjCsrOff X (adjOf G X) X.card ≤ rcfg.batch.m2 := by rw [adjCsrOff_adjOf_card, hm2]
                                         unfold batchScratchSize at hro3; rcases hro3 with x | x <;> omega))
      have hlp3 : LocalPairsAt st3.mem rcfg.batch.pairBAddr rcfg.batch.aOffAddr rcfg.batch.aLenAddr
          rcfg.batch.aDataAddr X pairs X.card := by
        refine ⟨fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hfr2_out124 _ (by unfold batchScratchSize at hro4; rcases hro4 with x | x <;> omega)]; exact hlp.1 v hv,
          ⟨by rw [show st3.mem _ = st2.mem _ from rfl, hfr2_out124 _ (by unfold batchScratchSize at hro5; rcases hro5 with x | x <;> omega)]; exact hlp.2.1,
           fun j hj => ?_⟩⟩
        have h_j := hlp.2.2 j hj
        have ho1 := hfr2_out124 (rcfg.batch.aOffAddr + j) (by unfold batchScratchSize at hro5; rcases hro5 with x | x <;> omega)
        have ho2 := hfr2_out124 (rcfg.batch.aOffAddr + j + 1) (by unfold batchScratchSize at hro5; rcases hro5 with x | x <;> omega)
        have hl := hfr2_out124 (rcfg.batch.aLenAddr + j) (by unfold batchScratchSize at hro6; rcases hro6 with x | x <;> omega)
        refine ⟨by rw [show st3.mem _ = st2.mem _ from rfl, show st3.mem _ = st2.mem _ from rfl,
                       show st3.mem _ = st2.mem _ from rfl, ho1, ho2, hl]; exact h_j.1,
          by rw [show st3.mem _ = st2.mem _ from rfl, hl]; exact h_j.2.1, fun t ht => ?_⟩
        have ht_le : st0.mem (rcfg.batch.aOffAddr + j) + t < X.card := by
          have hmo := localAPairsAt_slot_bound hlp.2 (j + 1) pairs.length (by omega) le_rfl
          have := hlp.2.1; have := h_j.1; have := h_j.2.1
          rw [show rcfg.batch.aOffAddr + (j + 1) = rcfg.batch.aOffAddr + j + 1 by omega] at hmo
          simp only [List.length_map, Finset.length_sort] at ht; omega
        rw [show st3.mem _ = st2.mem _ from rfl, ho1, Nat.add_assoc,
            show st3.mem _ = st2.mem _ from rfl,
            hfr2_out124 _ (by unfold batchScratchSize at hro7; rcases hro7 with x | x <;> omega), ← Nat.add_assoc]
        exact h_j.2.2 t ht
      have hst3_16 := (hst2_cfg 16 (by decide)).trans (m16.trans hdem)
      have hst3_17 := (hst2_cfg 17 (by decide)).trans m17
      have hst3_18 := (hst2_cfg 18 (by decide)).trans m18
      have hst3_19 := (hst2_cfg 19 (by decide)).trans m19
      have hst3_20 := (hst2_cfg 20 (by decide)).trans m20
      have hst3_21 := (hst2_cfg 21 (by decide)).trans m21
      have hst3_22 := (hst2_cfg 22 (by decide)).trans m22
      have hst3_23 := (hst2_cfg 23 (by decide)).trans m23
      exact
        { k_pairs := hk.symm, k_chunks := by simp [initChunks, hk], valid := hvalid,
          dem_inv := by omega, flat_le_cost := by omega,
          cfg_ro := fun o ho _ => hst2_cfg o ho,
          dem_mem := hst3_16,
          bgen_le := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_17]; simp,
          bfs_le := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_18]; simp,
          dfs_le := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_19]; simp,
          ball_le := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_20]; simp,
          live_le := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_21]; simp,
          php_lo := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_22],
          php_hi := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_22]; simp,
          chp_lo := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_23]; exact hdisj.ch_lo,
          chp_hi := by rw [show st3.mem _ = st2.mem _ from rfl, hst3_23]; have := hdisj.ch_hi; omega,
          iso_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_17, hfr2_out124 _ (by unfold wsIsoStamp; omega)]; exact hiso0 v hv,
          ma_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_17, hfr2_out124 _ (by unfold wsMatchAStamp; omega)]; exact hma0 v hv,
          vis_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_18, hfr2_out124 _ (by unfold wsVisStamp; omega)]; exact hvis0 v hv,
          cur_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_19, hfr2_out124 _ (by unfold wsCurStamp; omega)]; exact hcur0 v hv,
          used_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_19, hfr2_out124 _ (by unfold wsUsedStamp; omega)]; exact hused0 v hv,
          dead_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_19, hfr2_out124 _ (by unfold wsDeadStamp; omega)]; exact hdead0 v hv,
          ball_s_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_20, hfr2_out124 _ (by unfold wsBallStamp; omega)]; exact hball0 v hv,
          live_s_le := fun v hv => by rw [show st3.mem _ = st2.mem _ from rfl, hst3_21, hfr2_out124 _ (by unfold wsLiveStamp; omega)]; exact hlive0 v hv,
          sub_init := hsub2, csr := hcsr3, lp := hlp3,
          chunks := fun j hj => by
            have h0j := hacc0 j (by omega)
            have hj_eq : initChunks.getD j [] = [] := by
              simp [initChunks, List.getD_eq_getElem?_getD, show j < pairs.length by omega]
            rw [hj_eq]
            exact ⟨(hfr2_out124 _ (by unfold batchScratchSize at hro8; rcases hro8 with x | x <;> omega)).trans h0j.1,
              (hfr2_out124 _ (by unfold batchScratchSize at hro9; rcases hro9 with x | x <;> omega)).trans h0j.2⟩,
          ch_disj := fun j1 hj1 _ _ _ a ha => by
            dsimp only at ha
            have hj_eq : initChunks.getD j1 [] = [] := by
              simp [initChunks, List.getD_eq_getElem?_getD, show j1 < pairs.length by omega]
            rw [hj_eq] at ha; simp [chunkAddrs] at ha,
          frame := hfr2_bws }
    obtain ⟨st4, c4, hrun4, hr4_0, hpost4, hc4⟩ :=
      routeBatchesLoop_ind hbatch_proc hsp_proc hbfs_proc hdfs_proc hres_proc hcurb_proc hball_proc
        hnX hm2 hd hb hHb hhL hcfg' hdisj rcfg.R 0 pairs initChunks 0 st3 (Nat.zero_add _)
        (by rw [← hraw_eq]; exact hpHi_res) hinv3
        (by simp [st3, regs3, hr2_0]) (by simp [st3, regs3]) (by simp [st3, regs3])
        (by simp [st3, regs3]) (by simp [st3, regs3]) ω
    obtain ⟨c34, hrun34, hc34⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3
      (show Runs w p ω (seqStmts [.loop routeLoopGuardExpr _]) st3 .normal st4 c4 from hrun4)
    rw [← hraw_eq] at hpost4 hc4
    unfold RouteLoopPost at hpost4
    rcases hpost4 with ⟨hcfg_ro4, hp_lo4, hp_hi4, hfr4, hout4⟩
    have hcost_def : routeOrCutCost G X pairs Δ L b rcfg.z = (routeOrCutRaw G X pairs Δ L b rcfg.z).2 := rfl
    have horig4 : ListAt st4.mem rcfg.origVertAddr (sortedX X) := fun j hj => by
      simp only [sortedX, Finset.length_sort] at hj
      exact (hfr4 (rcfg.origVertAddr + j)
        (not_batchWriteSet_orig hdisj (by omega) (by omega))).trans (horig j (by simp [sortedX, hj]))
    have hrcost_ge_k1 : rcfg.batch.k + 1 ≤ routeOrCutCost G X pairs Δ L b rcfg.z := by
      obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rcfg.R ≠ 0)
      have h1 : routeOrCutCost G X pairs Δ L b rcfg.z =
          (routeBatches G X Δ b L rcfg.z (r' + 1) pairs (initChunks.map List.flatten) 0).2 := by
        unfold routeOrCutCost; rw [hraw_eq, hr']
      rw [h1]; unfold routeBatches
      rw [ite_eq_right (fun h => by omega)]
      dsimp only
      have hbp := (runBatch_props G Δ b L hvalid).1
      cases h : (runBatch G X Δ b L pairs).outcome with
      | cut _ => dsimp only; omega
      | matched bp rp =>
        dsimp only
        have hadd := routeBatches_cost_add G X Δ b L rcfg.z r' rp
          (List.zipWith (· ++ ·) (initChunks.map List.flatten) bp) 0 (runBatch G X Δ b L pairs).cost
        simp only [Nat.zero_add] at hadd ⊢; omega
    -- Stage 3: branch on tag = st4.regs 5, emit output, return tag
    cases hres : routeOrCut G X pairs Δ L b rcfg.z with
    | cut U =>
      have hres_raw : (routeOrCutRaw G X pairs Δ L b rcfg.z).1 = .cut U := hres
      rw [hres_raw] at hout4
      rcases hout4 with ⟨htag4, hm25_4, hX_le_cost, ul, hul_len, hul_nd, hul_sub, hul_cov, hul_at⟩
      have hcondCut : (Expr.reg 5).eval w st4 = some 1 := by simp [Expr.eval, htag4]
      obtain ⟨st5, c5, hrun5, hr5_5, hout5, hfr5, hc5⟩ :=
        emitCut_triple hnX hX_w hdisj hul_len hul_nd hul_sub hul_cov
          ((hcfg_ro4 0 (by decide) (Or.inl (by decide))).trans m0)
          ((hcfg_ro4 1 (by decide) (Or.inl (by decide))).trans m1)
          ((hcfg_ro4 14 (by decide) (Or.inl (by decide))).trans m14)
          ((hcfg_ro4 15 (by decide) (Or.inl (by decide))).trans m15)
          hm25_4
          ((hcfg_ro4 29 (by decide) (Or.inr (by decide))).trans m29)
          ((hcfg_ro4 30 (by decide) (Or.inr (by decide))).trans m30)
          hul_at horig4 hr4_0 ω
      have hrunCond5 : Runs w p ω (.cond (.reg 5) emitCutStmt emitMatchedStmt) st4 .normal st5 _ :=
        batch_runs_cond_pos hcondCut (by decide) hrun5
      obtain ⟨cRet, hret5, hcRet⟩ : ∃ cRet, Runs w p ω (.ret (.reg 5)) st5 (.returned 1) st5 cRet ∧ cRet ≤ 5 := by
        have h0 : ∃ o s c0, Runs w p ω (.ret (.reg 5)) st5 o s c0 ∧ (o = .returned 1 ∧ s = st5) ∧ 0 + c0 ≤ 5 :=
          runs_ret_le (v := 1) (by simp [Expr.eval, hr5_5, htag4]) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, c0, h, ⟨rfl, rfl⟩, hc0⟩; exact ⟨c0, h, by omega⟩
      have hrun56 : Runs w p ω (Stmt.seq (.cond (.reg 5) emitCutStmt emitMatchedStmt) (.ret (.reg 5)))
          st4 (.returned 1) st5 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hrunCond5, hret5, rfl⟩)
      have hrun26 : Runs w p ω mainBranch st1 (.returned 1) st5 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st4, c34, _, hrun34, hrun56, rfl⟩), rfl⟩)
      have hrunCond1 : Runs w p ω (.cond condExpr mainBranch emitEmptyMatchedRetStmt) st1 (.returned 1) st5 _ :=
        batch_runs_cond_pos hcond1 (by decide) hrun26
      obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1
        (show Runs w p ω (seqStmts [.cond condExpr mainBranch emitEmptyMatchedRetStmt]) st1 (.returned 1) st5 _ from hrunCond1)
      have hU_le_X : U.card ≤ X.card := Finset.card_le_card fun v hv => (hul_cov v hv).1
      have h22_eq : st5.mem (cfgAddr + 22) = st4.mem (cfgAddr + 22) :=
        hfr5 _ (by have hd := hdisj.out_cfg; unfold DisjRange at hd; omega)
      refine ⟨.returned 1, st5, cAll, hrunAll, ?_, ?_⟩
      · dsimp only [retPost]
        refine ⟨rfl, hout5, trivial, by rw [h22_eq]; exact hp_lo4, by rw [h22_eq, hcost_def]; exact hp_hi4, ?_⟩
        intro a ha
        rw [h22_eq] at ha
        exact (hfr5 a (by intro h; apply ha; exact Or.inr (Or.inl ⟨h.1, by omega⟩))).trans
          (hfr4 a (fun h => ha (Or.inl h)))
      · dsimp only [routeCsrProgCost, condExpr, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc3 hc4 hc34 hc5 hcRet hcAll ⊢
        omega
    | matched matchings emb =>
      have hres_raw : (routeOrCutRaw G X pairs Δ L b rcfg.z).1 = .matched matchings emb := hres
      rw [hres_raw] at hout4
      rcases hout4 with ⟨htag4, finChunks, hfc_len, hfc_le_dem, hfc_le_cost, hfc_eq, hfc_ch⟩
      have hcondM : (Expr.reg 5).eval w st4 = some 0 := by simp [Expr.eval, htag4]
      have hp_lo_le4 : pLo ≤ st4.mem (cfgAddr + 22) := le_trans hdisj.hp_lo hp_lo4
      have hdisj4 := hdisj.shrink_pHi (pHi' := st4.mem (cfgAddr + 22)) (by omega)
      obtain ⟨st5, c5, hrun5, hr5_5, hout5, hwalks5, hwb5, hfr5, hc5⟩ :=
        emitMatched_triple hnX hfc_len.symm hX_w hdisj4 hp_lo_le4
          (by have := hdisj.ch_lo; have := hdisj.ch_hi; omega) (by omega)
          ((hcfg_ro4 1 (by decide) (Or.inl (by decide))).trans m1)
          ((hcfg_ro4 12 (by decide) (Or.inl (by decide))).trans m12)
          ((hcfg_ro4 29 (by decide) (Or.inr (by decide))).trans m29)
          ((hcfg_ro4 30 (by decide) (Or.inr (by decide))).trans m30)
          ((hcfg_ro4 31 (by decide) (Or.inr (by decide))).trans m31)
          hfc_ch horig4 hr4_0 ω
      have hrunCond5 : Runs w p ω (.cond (.reg 5) emitCutStmt emitMatchedStmt) st4 .normal st5 _ :=
        batch_runs_cond_zero hcondM hrun5
      obtain ⟨cRet, hret5, hcRet⟩ : ∃ cRet, Runs w p ω (.ret (.reg 5)) st5 (.returned 0) st5 cRet ∧ cRet ≤ 5 := by
        have h0 : ∃ o s c0, Runs w p ω (.ret (.reg 5)) st5 o s c0 ∧ (o = .returned 0 ∧ s = st5) ∧ 0 + c0 ≤ 5 :=
          runs_ret_le (v := 0) (by simp [Expr.eval, hr5_5, htag4]) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, c0, h, ⟨rfl, rfl⟩, hc0⟩; exact ⟨c0, h, by omega⟩
      have hrun56 : Runs w p ω (Stmt.seq (.cond (.reg 5) emitCutStmt emitMatchedStmt) (.ret (.reg 5)))
          st4 (.returned 0) st5 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hrunCond5, hret5, rfl⟩)
      have hrun26 : Runs w p ω mainBranch st1 (.returned 0) st5 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st4, c34, _, hrun34, hrun56, rfl⟩), rfl⟩)
      have hrunCond1 : Runs w p ω (.cond condExpr mainBranch emitEmptyMatchedRetStmt) st1 (.returned 0) st5 _ :=
        batch_runs_cond_pos hcond1 (by decide) hrun26
      obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1
        (show Runs w p ω (seqStmts [.cond condExpr mainBranch emitEmptyMatchedRetStmt]) st1 (.returned 0) st5 _ from hrunCond1)
      have h22_eq : st5.mem (cfgAddr + 22) = st4.mem (cfgAddr + 22) :=
        hfr5 _ (by have h1 := hdisj.out_cfg; have h2 := hdisj.walks_cfg; unfold DisjRange at h1 h2; omega)
      have hmatch_eq : matchings = (finChunks.map List.flatten).map fun ps => ps.map Prod.fst :=
        (RouteResult.matched.inj hfc_eq).1.symm
      have hemb_eq : emb = fun idx => ((finChunks.map List.flatten).flatten.getD idx ((0, 0), [])).2 :=
        (RouteResult.matched.inj hfc_eq).2.symm
      have hlen_eq : matchings.flatten.length = (finChunks.map List.flatten).flatten.length := by
        rw [hmatch_eq, flatten_map_prod_fst, List.length_map]
      refine ⟨.returned 0, st5, cAll, hrunAll, ?_, ?_⟩
      · dsimp only [retPost]
        refine ⟨rfl, by rw [← hfc_eq]; exact hout5, ?_, by rw [h22_eq]; exact hp_lo4,
          by rw [h22_eq, hcost_def]; exact hp_hi4, ?_⟩
        · rw [hlen_eq, hemb_eq]
          refine ⟨hwalks5, fun idx hidx => ?_⟩
          have h := hwb5 idx hidx
          rw [h22_eq]
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some] using h
        · intro a ha
          rw [h22_eq] at ha
          refine (hfr5 a ?_).trans (hfr4 a (fun h => ha (Or.inl h)))
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · apply ha; exact Or.inr (Or.inl ⟨h1, by omega⟩)
          · apply ha; exact Or.inr (Or.inr ⟨h1, by omega⟩)
      · dsimp only [routeCsrProgCost, condExpr, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc3 hc4 hc34 hc5 hcRet hcAll ⊢
        omega
  · -- Early exit: totalDemand pairs ≤ z ∨ R = 0
    have hcond0 : condExpr.eval w st1 = some 0 := by
      have h0w : (0 : ℕ) < 2 ^ w := by omega
      have h1w : (1 : ℕ) < 2 ^ w := by omega
      unfold condExpr
      simp only [Expr.eval, BinOp.eval, st1, regs1, h0w, ↓reduceIte, Function.update_self,
        Function.update_of_ne (by decide : (1 : ℕ) ≠ 3), Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
        Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)]
      by_cases hA : rcfg.z < rcfg.batch.curDemandIn <;> by_cases hB : 0 < rcfg.R
      · exact absurd ⟨hA, hB⟩ hgo
      all_goals simp [hA, hB, h0w, h1w]
    have hres_eq : routeOrCut G X pairs Δ L b rcfg.z = .matched (List.replicate pairs.length []) (fun _ => []) ∧
        routeOrCutCost G X pairs Δ L b rcfg.z = 0 := by
      unfold routeOrCut routeOrCutCost routeOrCutRaw
      by_cases hdz : totalDemand pairs ≤ rcfg.z
      · simp [hdz]
      · have hR0 : rcfg.R = 0 := by omega
        have hrep : (List.replicate pairs.length ([] : List ((ℕ × ℕ) × List ℕ))).map (fun ps => ps.map Prod.fst) =
            List.replicate pairs.length [] := by rw [List.map_replicate]; rfl
        have hfl0 : (List.replicate pairs.length ([] : List ((ℕ × ℕ) × List ℕ))).flatten = [] := by
          induction pairs.length with | zero => rfl | succ _ _ => simp
        simp [hdz, ← hR, hR0, routeBatches, mkMatchedResult, hrep, hfl0]
    have hd_ow : DisjRange rcfg.outAddr 2 rcfg.walksAddr 1 := by
      have h := hdisj.out_walks; unfold DisjRange at h ⊢; omega
    obtain ⟨st2, c2, hrun2, hout2, hwalks2, hfr2, hc2⟩ :=
      emitEmptyMatchedRet_triple (p := p) (st0 := st1) (k := pairs.length) hw_cfg (by omega) (by omega) hw4 hd_ow
        m30 m31 (by dsimp only [st1, regs1]; simp [hr0]) ω
    have hrunCond0 : Runs w p ω (.cond condExpr mainBranch emitEmptyMatchedRetStmt) st1 (.returned 0) st2 _ :=
      batch_runs_cond_zero hcond0 hrun2
    obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1
      (show Runs w p ω (seqStmts [.cond condExpr mainBranch emitEmptyMatchedRetStmt]) st1 (.returned 0) st2 _ from hrunCond0)
    have h22_eq : st2.mem (cfgAddr + 22) = rcfg.batch.pathHeapIn := by
      have h1 := hdisj.out_cfg; have h2 := hdisj.walks_cfg; unfold DisjRange at h1 h2
      exact (hfr2 (cfgAddr + 22) (by omega) (by omega) (by omega)).trans m22
    have hflat0 : (List.replicate pairs.length ([] : List (ℕ × ℕ))).flatten = [] := by
      induction pairs.length with | zero => rfl | succ _ _ => simp
    refine ⟨.returned 0, st2, cAll, hrunAll, ?_, ?_⟩
    · dsimp only [retPost]; rw [hres_eq.1, hres_eq.2]
      refine ⟨rfl, hout2, ?_, by rw [h22_eq], by rw [h22_eq]; omega, ?_⟩
      · dsimp only
        rw [hflat0, List.length_nil]
        exact ⟨hwalks2, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · intro a ha
        exact hfr2 a (fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          (fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          (fun h => ha (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    · dsimp only [routeCsrProgCost, condExpr, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hcAll ⊢
      omega

/-- Contract for Procedure 5 (`routeOrCutCsrProc`) on argument `[cfgAddr]`. -/
def routeOrCutCsrContract (w : ℕ) (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ))
    (rcfg : RouteLoopCfg) (pLo pHi cLo cHi : ℕ) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let cfgAddr := args.getD 0 0
    rcfg.batch.nX = X.card ∧
    rcfg.batch.k = pairs.length ∧
    rcfg.batch.m2 = 2 * (G.inside X).length ∧
    rcfg.batch.d = routeD Δ b L ∧
    rcfg.batch.b = b ∧
    rcfg.batch.Hbatch = routeHBatch Δ b L ∧
    rcfg.R = routeR Δ b L ∧
    routeH Δ b * L = rcfg.hL ∧
    rcfg.batch.curDemandIn = totalDemand pairs ∧
    ValidTerminalPairs X pairs ∧
    (∀ v ∈ X, v < 2 ^ w) ∧
    RouteLoopCfgAt mem cfgAddr rcfg ∧
    RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg ∧
    rcfg.batch.pathHeapIn + 5 * routeOrCutCost G X pairs Δ L b rcfg.z + 15 * rcfg.batch.nX ≤ pHi ∧
    AdjCsrAt mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X) ∧
    LocalPairsAt mem rcfg.batch.pairBAddr rcfg.batch.aOffAddr rcfg.batch.aLenAddr
      rcfg.batch.aDataAddr X pairs X.card ∧
    ListAt mem rcfg.origVertAddr (sortedX X) ∧
    (∀ j < pairs.length,
      mem (rcfg.batch.accHeadAddr + j) = 0 ∧ mem (rcfg.batch.accTailAddr + j) = 0) ∧
    (∀ v < X.card, mem (wsIsoStamp rcfg.batch.ws + v) ≤ rcfg.batch.batchGenIn) ∧
    (∀ v < X.card, mem (wsMatchAStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.batchGenIn) ∧
    (∀ v < X.card, mem (wsVisStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.bfsGenIn) ∧
    (∀ v < X.card, mem (wsCurStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn) ∧
    (∀ v < X.card, mem (wsUsedStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn) ∧
    (∀ v < X.card, mem (wsDeadStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ rcfg.batch.dfsGenIn) ∧
    (∀ v < X.card, mem (wsBallStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ rcfg.batch.ballGenIn) ∧
    (∀ v < X.card, mem (wsLiveStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ rcfg.batch.liveGenIn)
  post args mem v mem' :=
    let cfgAddr := args.getD 0 0
    let res := routeOrCut G X pairs Δ L b rcfg.z
    let rcost := routeOrCutCost G X pairs Δ L b rcfg.z
    (match res with | .matched _ _ => v = 0 | .cut _ => v = 1) ∧
    RouteOutAt mem' rcfg.outAddr res ∧
    (match res with
     | .matched matchings emb =>
         WalksAt mem' rcfg.walksAddr matchings.flatten.length emb ∧
         (∀ idx < matchings.flatten.length,
           pLo ≤ mem' (rcfg.walksAddr + 1 + idx) ∧
           mem' (rcfg.walksAddr + 1 + idx) + 1 + (emb idx).length ≤ mem' (cfgAddr + 22))
     | .cut _ => True) ∧
    rcfg.batch.pathHeapIn ≤ mem' (cfgAddr + 22) ∧
    mem' (cfgAddr + 22) ≤ rcfg.batch.pathHeapIn + 5 * rcost ∧
    (∀ a, ¬ RouteLoopWriteSet rcfg cfgAddr (mem' (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
      mem' a = mem a)
  cost _ _ := routeCsrProgCost (routeOrCutCost G X pairs Δ L b rcfg.z)

/-- `routeOrCutCsrProc` deterministically meets `routeOrCutCsrContract`. -/
theorem routeOrCutCsr_meetsContract {w : ℕ} {p : Program}
    {idx bBatch bSp bBfs bDfs bRes bCurB bBall : ℕ}
    (hproc : p.procs[idx]? = some (routeOrCutCsrProc bBatch))
    (hbatch_proc : p.procs[bBatch]? = some (runBatchProc bSp bRes bCurB bBall))
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ))
    (rcfg : RouteLoopCfg) (pLo pHi cLo cHi : ℕ) :
    MeetsContract w p idx
      (routeOrCutCsrContract w G X Δ b L pairs rcfg pLo pHi cLo cHi) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨_, hnX, hk, hm2, hd, hb, hHb, hR, hhL, hdem, hvalid, hX_w, hcfg, hdisj,
    hpHi_res, hcsr, hlp, horig, hacc0, hiso0, hma0, hvis0, hcur0, hused0, hdead0, hball0, hlive0⟩
  have htr := routeOrCutCsr_triple (w := w) (p := p) (st0 := startState args mem pos)
    hbatch_proc hsp_proc hbfs_proc hdfs_proc hres_proc hcurb_proc hball_proc
    hnX hk hm2 hd hb hHb hR hhL hdem hvalid hX_w hcfg hdisj hpHi_res hcsr hlp horig hacc0
    hiso0 hma0 hvis0 hcur0 hused0 hdead0 hball0 hlive0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨routeOrCutCsrProc bBatch, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
