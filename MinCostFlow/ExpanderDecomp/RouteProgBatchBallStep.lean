module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchBallBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Cut-Finding Ball-Growing Step (`RouteProgBatchBallStep`)

Verifies `batchBallStep_grow`: the `S ≠ ∅ ∧ T ≠ ∅` branch of `batchBallLoopStmt` calling
`growBallProc` and `batchCopyBallStmt`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma batch_sub_of_ballSetup {mem mem' : ℕ → ℕ} {cfg : BatchCfg} {hL : ℕ}
    (h : BatchSubCfgsInit mem cfg hL)
    (hmem_out : ∀ a, a ≠ wsBallCfg cfg.ws + 4 → a ≠ wsBallCfg cfg.ws + 10 →
      a ≠ wsBallCfg cfg.ws + 12 → a ≠ wsBallCfg cfg.ws + 15 →
      a ≠ wsBallCfg cfg.ws + 16 → a ≠ wsBfsBallCfg cfg.ws + 3 → mem' a = mem a) :
    BatchSubCfgsInit mem' cfg hL :=
  h.of_agree fun off _ hnot =>
    hmem_out (cfg.ws + off)
      (by intro heq; simp only [wsBallCfg] at heq; have h80 : off = 80 := by { omega }; subst h80; exact hnot (by decide))
      (by intro heq; simp only [wsBallCfg] at heq; have h86 : off = 86 := by { omega }; subst h86; exact hnot (by decide))
      (by intro heq; simp only [wsBallCfg] at heq; have h88 : off = 88 := by { omega }; subst h88; exact hnot (by decide))
      (by intro heq; simp only [wsBallCfg] at heq; have h91 : off = 91 := by { omega }; subst h91; exact hnot (by decide))
      (by intro heq; simp only [wsBallCfg] at heq; have h92 : off = 92 := by { omega }; subst h92; exact hnot (by decide))
      (by intro heq; simp only [wsBfsBallCfg] at heq; have h103 : off = 103 := by { omega }; subst h103; exact hnot (by decide))

lemma batchBallStep_grow {w : ℕ} {p : Program} {bBall bBfs : ℕ}
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    {G : Graph} {X V_res : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL : ℕ}
    {remPairs : List (Finset ℕ × Finset ℕ)} {i : ℕ}
    {U S T : Finset ℕ} {ul : List ℕ} {bfsGen ballGen : ℕ}
    {mem0 : ℕ → ℕ} {st0 stF : State}
    (hnX : cfg.nX = X.card) (hk : cfg.k = remPairs.length)
    (hVX_res : V_res ⊆ X)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hi_lt : i < remPairs.length)
    (hSX : S ⊆ X \ U) (hTX : T ⊆ X \ U)
    (hinv : BatchBallInv st0.mem mem0 G X V_res cfg hL remPairs i U ul bfsGen ballGen)
    (hregs : BatchBallRegs st0.regs cfg cfgAddr bfsGen ballGen i U.card)
    (hregsF : ∀ r, r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      r ≠ 37 → r ≠ 38 → stF.regs r = st0.regs r)
    (hF37 : stF.regs 37 = S.card) (hF38 : stF.regs 38 = T.card)
    (hS_at : ListAt stF.mem (wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k) ((S.sort (· ≤ ·)).map (locOf X)))
    (hT_at : ListAt stF.mem (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k) ((T.sort (· ≤ ·)).map (locOf X)))
    (hfrF : ∀ a,
      ¬ ((wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card) ∨
         (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card)) →
      stF.mem a = st0.mem a) :
    ∀ ω,
      let Hres : Graph := ⟨G.n, G.inside V_res⟩
      ∀ (h L : ℕ), h * L = hL →
      let br' := growBall (adjOf Hres X) (X \ U) S T cfg.b h L
      ∃ stG cG ul1 bfsGen1 ballGen1,
        Runs w p ω
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
          stF .normal stG cG ∧
        (∀ r, r ≠ 18 → r ≠ 19 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
          r ≠ 32 → r ≠ 37 → r ≠ 38 → stG.regs r = st0.regs r) ∧
        stG.regs 18 = bfsGen1 ∧ stG.regs 19 = ballGen1 ∧ stG.regs 32 = (U ∪ br'.ball).card ∧
        BatchBallInv stG.mem mem0 G X V_res cfg hL remPairs (i + 1) (U ∪ br'.ball) ul1 bfsGen1 ballGen1 ∧
        cG ≤ ballProgCost br'.cost + 40 * br'.ball.card + 130 := by
  intro ω Hres h L hhL br'
  rcases hregs with ⟨hr0, hr1, hr2, hr9, hr10, hr11, hr14, hr15, hr16, hr17, hr18, hr19,
    hr20, hr21, hr22, hr23, hr31, hr32, hr33, hr34, hr35, hr36⟩
  have hw_ws := hdisj.w_ws; have hw4 := hdisj.w_4
  have hS_le_X : S.card ≤ cfg.nX := by rw [hnX]; exact Finset.card_le_card (Finset.Subset.trans hSX Finset.sdiff_subset)
  have hT_le_X : T.card ≤ cfg.nX := by rw [hnX]; exact Finset.card_le_card (Finset.Subset.trans hTX Finset.sdiff_subset)
  have hbfsg_le : bfsGen + 2 ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3) := by have := hinv.bfs_hi; omega
  have hballg_le : ballGen + 1 ≤ cfg.ballGenIn + cfg.k := by have := hinv.ball_hi; omega
  have hres_m2 : adjCsrOff X (adjOf Hres X) X.card ≤ cfg.m2 :=
    le_trans (adjCsrOff_inside_le G hVX_res X.card) hm2
  -- Phase 1: 6 config stores
  obtain ⟨st1, c1, hrun1, hregs1_eq, hm1_b4, hm1_b10, hm1_b12, hm1_b15, hm1_b16, hm1_bb3, hmem1_out, hc1⟩ :=
    batchBallCallSetup_triple (w := w) (p := p) (cfg := cfg) (sLen := S.card) (tLen := T.card)
      (bfsGen := bfsGen) (ballGen := ballGen)
      (by unfold batchScratchSize at hw_ws; omega) hw4
      (by rw [hregsF 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
      (by rw [hregsF 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
      (by rw [hregsF 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr18])
      (by rw [hregsF 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr19])
      (by rw [hregsF 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr23])
      hF37 hF38 ω
  have hmem1_outside_124 : ∀ a, a < cfg.ws ∨ cfg.ws + 124 ≤ a → st1.mem a = stF.mem a := fun a ha =>
    hmem1_out a (by simp [wsBallCfg]; omega) (by simp [wsBallCfg]; omega)
      (by simp [wsBallCfg]; omega) (by simp [wsBallCfg]; omega)
      (by simp [wsBallCfg]; omega) (by simp [wsBfsBallCfg]; omega)
  have hmem1_from_st0 : ∀ a, (a < cfg.ws ∨ cfg.ws + 124 ≤ a) →
      ¬ ((wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card) ∨
         (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card)) →
      st1.mem a = st0.mem a := fun a ha1 ha2 =>
    (hmem1_outside_124 a ha1).trans (hfrF a ha2)
  have hsub1 : BatchSubCfgsInit st1.mem cfg hL :=
    batch_sub_of_ballSetup
      (hinv.sub_init.of_outside_124 fun a ha1 ha2 => hfrF a (by unfold wsSBallBuf wsTBallBuf; omega))
      hmem1_out
  -- Phase 2: call growBallProc
  set ballCfg := mkBatchBallCfg cfg (cfg.liveGenIn + 1) S.card T.card bfsGen ballGen
  set bfsBallCfg : BfsCfg :=
    { mkBatchBallBfsCfg cfg (cfg.liveGenIn + 1) hL with
      layerOffAddr := st1.mem (wsBfsBallCfg cfg.ws + 9)
      layerDataAddr := st1.mem (wsBfsBallCfg cfg.ws + 10)
      bfsGen := st1.mem (wsBfsBallCfg cfg.ws + 12)
      initPtr := st1.mem (wsBfsBallCfg cfg.ws + 14)
      initLen := st1.mem (wsBfsBallCfg cfg.ws + 15) }
  have hballDisj : BallDisj w X.card cfg.m2 ballCfg bfsBallCfg (wsBallCfg cfg.ws) := by
    rw [← hnX]
    exact ballDisj_of_dyn (hdisj.to_ballDisj (liveGen := cfg.liveGenIn + 1) (sLen := S.card)
      (tLen := T.card) (bfsGen := bfsGen) (ballGen := ballGen) le_rfl hS_le_X hT_le_X (by omega) (by omega))
  have hballPre : (growBallContract w X (X \ U) S T (adjOf Hres X) h L ballCfg bfsBallCfg cfg.m2).pre
      [wsBallCfg cfg.ws] st1.mem := by
    refine ⟨rfl, Finset.sdiff_subset, hSX, hTX, fun u _ e he => adjOf_fst_mem_X Hres X u e he,
      ?_, ?_, hhL.symm, ?_, hres_m2, hballDisj, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
    · rcases hsub1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        b0, b1, b2, b3, b5, b6, b7, b8, b9, b11, b13, b14, b17, _⟩
      exact ⟨b0, b1, b2, b3, hm1_b4, b5, b6, b7, b8, b9, hm1_b10, b11, hm1_b12, b13, b14,
        hm1_b15, hm1_b16, b17⟩
    · rcases hsub1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _,
        c0, c1', c2', c4, c5, c6, c7, c8, c11, c13⟩
      exact ⟨c0, c1', c2', hm1_bb3, c4, c5, c6, c7, c8, rfl, rfl, c11, rfl, c13, rfl, rfl⟩
    · exact hinv.res_csr.congr
        (fun k hk => hmem1_from_st0 _ (by unfold wsResOff; omega) (by unfold wsResOff wsSBallBuf wsTBallBuf; omega))
        (fun k hk =>
          have hk' : k < cfg.m2 := lt_of_lt_of_le hk hres_m2
          hmem1_from_st0 _ (by unfold wsResNb; omega) (by unfold wsResNb wsSBallBuf wsTBallBuf; omega))
    · intro v hv
      rw [hmem1_from_st0 _ (by simp only [ballCfg, mkBatchBallCfg, wsLiveStamp]; omega)
        (by simp only [ballCfg, mkBatchBallCfg, wsLiveStamp, wsSBallBuf, wsTBallBuf]; omega)]
      exact hinv.live_ok v hv
    · intro j hj
      have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
      rw [hmem1_outside_124 _ (by simp only [ballCfg, mkBatchBallCfg, wsSBallBuf]; omega)]
      exact hS_at j hj
    · intro j hj
      have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
      rw [hmem1_outside_124 _ (by simp only [ballCfg, mkBatchBallCfg, wsTBallBuf]; omega)]
      exact hT_at j hj
    · intro v hv
      rw [hmem1_from_st0 _ (by simp only [bfsBallCfg, mkBatchBallBfsCfg, wsVisStamp]; omega)
        (by simp only [bfsBallCfg, mkBatchBallBfsCfg, wsVisStamp, wsSBallBuf, wsTBallBuf]; omega)]
      exact hinv.vis_le v hv
    · intro v hv
      rw [hmem1_from_st0 _ (by simp only [ballCfg, mkBatchBallCfg, wsBallStamp]; omega)
        (by simp only [ballCfg, mkBatchBallCfg, wsBallStamp, wsSBallBuf, wsTBallBuf]; omega)]
      exact hinv.ball_le v hv
  have hballMC := growBall_meetsContract (w := w) hball_proc hbfs_proc
    X (X \ U) S T (adjOf Hres X) h L ballCfg bfsBallCfg cfg.m2
  have hball_args : evalArgs w st1 [.reg 15] = some [wsBallCfg cfg.ws] := by
    simp [evalArgs, Expr.eval, hregs1_eq,
      hregsF 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15]
  obtain ⟨st2, c2, v2, hrun2, hpost2, hr2_26, hr2_oth, hc2⟩ :=
    runs_call_of_meetsContract (r := 26) hballMC hball_args
      (by intro v hv; simp at hv; subst hv; unfold batchScratchSize at hw_ws; unfold wsBallCfg; omega)
      hballPre ω
  simp only [growBallContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpost2 hc2
  rcases hpost2 with ⟨hv2, hballOut, hballFr⟩
  rcases hballOut with ⟨_, hm2_19, hm2_20, ⟨bl, hbl_len, hbl_nd, hbl_sub, hbl_cov, hbl_at⟩,
    _, hbs2_le, hvis2_le⟩
  have hbr_eq : growBall (adjOf Hres X) (X \ U) S T ballCfg.b h L = br' := rfl
  rw [hbr_eq] at hv2 hbl_len hbl_sub hbl_cov hc2
  have hbr_sub : br'.ball ⊆ X \ U := growBall_ball_sub (adjOf Hres X) (X \ U) S T cfg.b h L
  have hU_disj_br : Disjoint U br'.ball :=
    Finset.disjoint_left.mpr fun x hxU hxB => (Finset.mem_sdiff.mp (hbr_sub hxB)).2 hxU
  have hU1_sub : U ∪ br'.ball ⊆ X :=
    Finset.union_subset hinv.U_sub (Finset.Subset.trans hbr_sub Finset.sdiff_subset)
  have hU1_card : (U ∪ br'.ball).card = U.card + br'.ball.card :=
    Finset.card_union_of_disjoint hU_disj_br
  have hU1_le_X : U.card + br'.ball.card ≤ X.card := by
    rw [← hU1_card]; exact Finset.card_le_card hU1_sub
  -- Phase 3: load r18, r19, r24, r25, r27
  obtain ⟨c3, hrun3, hc3⟩ :=
    batchBallPostLoad_triple (w := w) (p := p) (ballCfgAddr := wsBallCfg cfg.ws)
      (bfsGen1 := bfsGen + 2) (ballGen1 := ballGen + 1)
      (ballListAddr := wsBallList cfg.ws cfg.nX cfg.m2 cfg.k)
      (cutListAddr := wsCutList cfg.ws cfg.nX cfg.m2 cfg.k) (cutSize := U.card)
      (by unfold batchScratchSize at hw_ws; unfold wsBallCfg; omega)
      (by unfold batchScratchSize at hw_ws; omega)
      (by rw [hr2_oth 15 (by decide), hregs1_eq,
              hregsF 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
      (by rw [hr2_oth 32 (by decide), hregs1_eq,
              hregsF 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr32])
      (by rw [hr2_oth 35 (by decide), hregs1_eq,
              hregsF 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr35])
      (by rw [hr2_oth 36 (by decide), hregs1_eq,
              hregsF 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr36])
      hm2_19 hm2_20 ω
  set st3 : State :=
    { st2 with
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update st2.regs 18 (bfsGen + 2)) 19 (ballGen + 1))
        24 (wsBallList cfg.ws cfg.nX cfg.m2 cfg.k))
        25 (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)) 27 U.card }
  -- Frame of st2 relative to st0 for untouched regions
  have hballFr' : ∀ a,
      ¬ BallWriteSet cfg.nX (mkBatchBallCfg cfg (cfg.liveGenIn + 1) S.card T.card bfsGen ballGen)
        (mkBatchBallBfsCfg cfg (cfg.liveGenIn + 1) hL) (wsBallCfg cfg.ws) a →
      st2.mem a = st1.mem a := fun a ha => hballFr a (by rw [← hnX]; exact ha)
  have hst2_outside_ws : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
      st2.mem a = mem0 a := by
    intro a ha
    rw [hballFr' a (fun hw => ha (batch_ballWriteSet_in_ws hw)),
        hmem1_from_st0 a (by unfold batchScratchSize at ha; omega)
          (by unfold batchScratchSize at ha; unfold wsSBallBuf wsTBallBuf; omega)]
    exact hinv.frame_ws a ha
  have hnotB_of_ws_range : ∀ a,
      (wsResOff cfg.ws cfg.nX ≤ a ∧ a < wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k) ∨
      (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + X.card) ∨
      (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsCutList cfg.ws cfg.nX cfg.m2 cfg.k + X.card) ∨
      (wsIsoStamp cfg.ws ≤ a ∧ a < wsIsoStamp cfg.ws + 2 * cfg.nX) ∨
      (wsCurStamp cfg.ws cfg.nX ≤ a ∧ a < wsCurStamp cfg.ws cfg.nX + 4 * cfg.nX) →
      st2.mem a = st0.mem a := by
    intro a ha
    rw [← hnX] at ha
    rw [hballFr' a (batch_not_ballWriteSet_ws_ro ha)]
    have h12 := batch_ws_ro_outside_124_and_bufs ha
    exact hmem1_from_st0 a h12.1 (by rw [← hnX]; exact h12.2)
  -- Phase 4: batchCopyBallStmt + r32 := r27
  have hul_at3 : ListAt st3.mem (wsCutList cfg.ws cfg.nX cfg.m2 cfg.k) ul := fun j hj => by
    have hj_lt : j < X.card := by have := hinv.ul_len; have := Finset.card_le_card hinv.U_sub; omega
    rw [show st3.mem _ = st2.mem _ from rfl,
        hnotB_of_ws_range _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hinv.ul_at j hj
  obtain ⟨st4, c4, hrun4, hregs4, hr27_4, hul4, hls4, hfr4, hc4⟩ :=
    batchCopyBall_triple (w := w) (p := p) (X := X) (st0 := st3)
      (liveStampAddr := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k)
      (liveGen := cfg.liveGenIn + 1)
      (ballListAddr := wsBallList cfg.ws cfg.nX cfg.m2 cfg.k)
      (cutListAddr := wsCutList cfg.ws cfg.nX cfg.m2 cfg.k)
      (bl := bl) (ul0 := ul)
      (fun x hx => (hbl_sub x hx).1) (by rw [hinv.ul_len, hbl_len]; exact hU1_le_X)
      (by unfold DisjRange wsLiveStamp wsCutList; left; omega)
      (by unfold DisjRange wsLiveStamp wsBallList; right; omega)
      (by unfold DisjRange wsCutList wsBallList; right; omega)
      (by unfold batchScratchSize at hw_ws; unfold wsLiveStamp; omega)
      (by unfold batchScratchSize at hw_ws; unfold wsBallList; omega)
      (by unfold batchScratchSize at hw_ws; unfold wsCutList; omega)
      (by have := hdisj.w_livegen; omega) hw4
      hbl_at hul_at3
      (by simp [st3, hr2_oth 22 (by decide), hregs1_eq,
              hregsF 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
      (by simp [st3, hr2_oth 23 (by decide), hregs1_eq,
              hregsF 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr23])
      (by simp [st3]) (by simp [st3])
      (by simp [st3, hr2_26, hv2, hbl_len]) (by simp [st3, hinv.ul_len]) ω
  set stG : State := { st4 with regs := Function.update st4.regs 32 (U ∪ br'.ball).card }
  have hrun5 : Runs w p ω (.assign 32 (.reg 27)) st4 .normal stG ((Expr.reg 27).size + 1) :=
    runs_assign_iff.mpr ⟨(U ∪ br'.ball).card,
      by simp [Expr.eval, hr27_4, hinv.ul_len, hbl_len, hU1_card], rfl, rfl, rfl⟩
  -- Stitch all phases
  have hrun45 : Runs w p ω (seqStmts [batchCopyBallStmt, .assign 32 (.reg 27)])
      st3 .normal stG (c4 + ((Expr.reg 27).size + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st4, c4, _, hrun4, hrun5, rfl⟩)
  obtain ⟨c35, hrun35, hc35⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun3 hrun45
  have hrun25 : Runs w p ω
      (seqStmts
        [ .call 26 bBall [.reg 15]
        , .assign 18 (.load (.bin .add (.reg 15) (.const 19)))
        , .assign 19 (.load (.bin .add (.reg 15) (.const 20)))
        , .assign 24 (.reg 35)
        , .assign 25 (.reg 36)
        , .assign 27 (.reg 32)
        , batchCopyBallStmt
        , .assign 32 (.reg 27) ])
      st1 .normal stG (c2 + c35 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, c35, hrun2, hrun35, rfl⟩)
  obtain ⟨cG, hrunG, hcG⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1 hrun25
  -- Prove ul1 := ul ++ bl invariants and BatchBallInv for stG
  have hfr4_not_ls_cl : ∀ a,
      (a < wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k ∨ wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + X.card ≤ a) →
      (a < wsCutList cfg.ws cfg.nX cfg.m2 cfg.k ∨ wsCutList cfg.ws cfg.nX cfg.m2 cfg.k + X.card ≤ a) →
      stG.mem a = st2.mem a := fun a h1 h2 =>
    hfr4 a (by intro h; rcases h with h | h <;> omega)
  have hinvG : BatchBallInv stG.mem mem0 G X V_res cfg hL remPairs (i + 1) (U ∪ br'.ball) (ul ++ bl)
      (bfsGen + 2) (ballGen + 1) := by
    refine ⟨hU1_sub, by have := hinv.bfs_lo; omega, by have := hinv.bfs_hi; omega,
      by have := hinv.ball_lo; omega, by have := hinv.ball_hi; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by rw [List.length_append, hinv.ul_len, hbl_len, hU1_card], ?_, ?_, ?_, hul4, ?_, ?_, ?_⟩
    · exact hinv.res_csr.congr
        (fun k hk => (hfr4_not_ls_cl _ (by unfold wsResOff wsLiveStamp; omega) (by unfold wsResOff wsCutList; omega)).trans
          (hnotB_of_ws_range _ (Or.inl ⟨by unfold wsResOff; omega, by unfold wsResOff wsLayerOffS; omega⟩)))
        (fun k hk =>
          have hk' : k < cfg.m2 := lt_of_lt_of_le hk hres_m2
          (hfr4_not_ls_cl _ (by unfold wsResNb wsLiveStamp; omega) (by unfold wsResNb wsCutList; omega)).trans
          (hnotB_of_ws_range _ (Or.inl ⟨by unfold wsResNb wsResOff; omega,
            by unfold wsResNb wsLayerOffS; omega⟩)))
    · have h1 := hdisj.ro_ao_ws; have h2 := hdisj.al_ws; have h3 := hdisj.ad_ws
      unfold DisjRange at h1 h2 h3
      have hws_eq : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
          stG.mem a = st0.mem a := fun a ha =>
        (hfr4_not_ls_cl a (by unfold batchScratchSize at ha; unfold wsLiveStamp; omega)
          (by unfold batchScratchSize at ha; unfold wsCutList; omega)).trans
          ((hst2_outside_ws a ha).trans (hinv.frame_ws a ha).symm)
      refine ⟨by rw [hws_eq _ (by rcases h1 with x | x <;> omega)]; exact hinv.la.1,
        fun j hj => ?_⟩
      have h_i := hinv.la.2 j hj
      have hm_o1 : stG.mem (cfg.aOffAddr + j) = st0.mem (cfg.aOffAddr + j) :=
        hws_eq _ (by rcases h1 with x | x <;> omega)
      have hm_o2 : stG.mem (cfg.aOffAddr + j + 1) = st0.mem (cfg.aOffAddr + j + 1) :=
        hws_eq _ (by rcases h1 with x | x <;> omega)
      have hm_l : stG.mem (cfg.aLenAddr + j) = st0.mem (cfg.aLenAddr + j) :=
        hws_eq _ (by rcases h2 with x | x <;> omega)
      refine ⟨by rw [hm_o1, hm_o2, hm_l]; exact h_i.1, by rw [hm_l]; exact h_i.2.1, fun t ht => ?_⟩
      have ht_le : st0.mem (cfg.aOffAddr + j) + t < X.card := by
        have hmo := localAPairsAt_slot_bound hinv.la (j + 1) remPairs.length (by omega) le_rfl
        have := hinv.la.1; have := h_i.1; have := h_i.2.1
        rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmo
        simp only [List.length_map, Finset.length_sort] at ht; omega
      rw [hm_o1, Nat.add_assoc, hws_eq _ (by rcases h3 with x | x <;> omega), ← Nat.add_assoc]
      exact h_i.2.2 t ht
    · have hbs_eq : ∀ a, wsResOff cfg.ws cfg.nX ≤ a → a < wsLayerOffS cfg.ws cfg.nX cfg.m2 cfg.k →
          stG.mem a = st0.mem a := fun a ha1 ha2 =>
        (hfr4_not_ls_cl a (by unfold wsLayerOffS at ha2; unfold wsLiveStamp; omega)
          (by unfold wsLayerOffS at ha2; unfold wsCutList; omega)).trans
          (hnotB_of_ws_range a (Or.inl ⟨ha1, ha2⟩))
      refine ⟨by rw [hbs_eq _ (by unfold wsResOff wsBOff; omega) (by unfold wsBOff wsLayerOffS; omega)]; exact hinv.bs.1,
        fun j hj => ?_⟩
      have h_i := hinv.bs.2 j hj
      have hm_o1 : stG.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j) = st0.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j) :=
        hbs_eq _ (by unfold wsResOff wsBOff; omega) (by unfold wsBOff wsLayerOffS; omega)
      have hm_o2 : stG.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j + 1) = st0.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j + 1) :=
        hbs_eq _ (by unfold wsResOff wsBOff; omega) (by unfold wsBOff wsLayerOffS; omega)
      have hm_l : stG.mem (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k + j) = st0.mem (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k + j) :=
        hbs_eq _ (by unfold wsResOff wsBLen; omega) (by unfold wsBLen wsLayerOffS; omega)
      refine ⟨by rw [hm_o1, hm_o2, hm_l]; exact h_i.1, by rw [hm_l]; exact h_i.2.1, fun t ht => ?_⟩
      have ht_le : st0.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j) + t < X.card := by
        have hmo := localBSlicesAt_slot_bound hinv.bs (j + 1) remPairs.length (by omega) le_rfl
        have := hinv.bs.1; have := h_i.1; have := h_i.2.1
        rw [show wsBOff cfg.ws cfg.nX cfg.m2 + (j + 1) = wsBOff cfg.ws cfg.nX cfg.m2 + j + 1 by omega] at hmo
        simp only [List.length_map, Finset.length_sort] at ht; omega
      rw [hm_o1, Nat.add_assoc,
          hbs_eq _ (by unfold wsResOff wsBData; omega) (by unfold wsBData wsLayerOffS; omega),
          ← Nat.add_assoc]
      exact h_i.2.2 t ht
    · intro v hv
      rw [show stG.mem _ = st4.mem _ from rfl, hls4 v hv]
      by_cases hbl_v : v ∈ bl
      · simp only [hbl_v, ↓reduceIte, ne_eq, not_true_eq_false, false_iff, Finset.mem_sdiff,
          Finset.mem_union, not_and, not_not]
        intro _; exact Or.inr (hbl_sub v hbl_v).2
      · simp only [hbl_v, ↓reduceIte]
        rw [show st3.mem _ = st2.mem _ from rfl,
            hnotB_of_ws_range _ (Or.inr (Or.inl ⟨by omega, by omega⟩)), hinv.live_ok v hv]
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
        constructor
        · intro ⟨hx, hnU⟩
          refine ⟨hx, hnU, fun hB => hbl_v ?_⟩
          have hcov := hbl_cov (origOf X v) hB
          rw [locOf_origOf hv] at hcov; exact hcov.2
        · intro ⟨hx, hnU, _⟩; exact ⟨hx, hnU⟩
    · intro v hv
      rw [show stG.mem _ = st4.mem _ from rfl, hls4 v hv]
      split_ifs
      · exact le_rfl
      · rw [show st3.mem _ = st2.mem _ from rfl,
            hnotB_of_ws_range _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        exact hinv.live_le v hv
    · intro v hv
      rw [hfr4_not_ls_cl _ (by unfold wsVisStamp wsLiveStamp; omega) (by unfold wsVisStamp wsCutList; omega)]
      exact hvis2_le v hv
    · intro v hv
      rw [hfr4_not_ls_cl _ (by unfold wsBallStamp wsLiveStamp; omega) (by unfold wsBallStamp wsCutList; omega)]
      exact hbs2_le v hv
    · rw [List.nodup_append]
      refine ⟨hinv.ul_nd, hbl_nd, fun x hx1 y hy2 heq => ?_⟩
      subst heq
      exact Finset.disjoint_left.mp hU_disj_br (hinv.ul_sub x hx1).2 (hbl_sub x hy2).2
    · intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact ⟨(hinv.ul_sub x h1).1, Finset.mem_union_left _ (hinv.ul_sub x h1).2⟩
      · exact ⟨(hbl_sub x h2).1, Finset.mem_union_right _ (hbl_sub x h2).2⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with h1 | h2
      · exact ⟨(hinv.ul_cov v h1).1, List.mem_append_left _ (hinv.ul_cov v h1).2⟩
      · exact ⟨(hbl_cov v h2).1, List.mem_append_right _ (hbl_cov v h2).2⟩
    · exact (hsub1.of_ballWriteSet hballFr').of_outside_124
        fun a ha1 ha2 => hfr4_not_ls_cl a (by unfold wsLiveStamp; omega) (by unfold wsCutList; omega)
    · intro a ha
      exact (hfr4_not_ls_cl a (by unfold batchScratchSize at ha; unfold wsLiveStamp; omega)
        (by unfold batchScratchSize at ha; unfold wsCutList; omega)).trans (hst2_outside_ws a ha)
    · intro a ha
      refine (hfr4_not_ls_cl a ?_ ?_).trans ((hnotB_of_ws_range a ?_).trans (hinv.ro_stamps a ha))
      · rcases ha with ha | ha <;> (simp only [wsIsoStamp, wsCurStamp, wsLiveStamp] at ha ⊢; omega)
      · rcases ha with ha | ha <;> (simp only [wsIsoStamp, wsCurStamp, wsCutList] at ha ⊢; omega)
      · rcases ha with ha | ha
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
  refine ⟨stG, cG, ul ++ bl, bfsGen + 2, ballGen + 1, hrunG, ?_,
    by simp [stG, hregs4 18 (by decide) (by decide) (by decide), st3],
    by simp [stG, hregs4 19 (by decide) (by decide) (by decide), st3],
    by simp [stG], hinvG, ?_⟩
  · intro r h18 h19 h24 h25 h26 h27 h28 h29 h30 h32 h37 h38
    simp only [stG, Function.update_of_ne h32, hregs4 r h27 h28 h29, st3,
      Function.update_of_ne h27, Function.update_of_ne h25, Function.update_of_ne h24,
      Function.update_of_ne h19, Function.update_of_ne h18,
      hr2_oth r h26, hregs1_eq, hregsF r h24 h25 h26 h27 h28 h29 h30 h37 h38]
  · simp only [Expr.size, argsSize, List.length_cons, List.length_nil, hbl_len] at hc1 hc2 hc3 hc4 hc35 hcG
    omega


end MinCostFlow.ExpanderDecomp
