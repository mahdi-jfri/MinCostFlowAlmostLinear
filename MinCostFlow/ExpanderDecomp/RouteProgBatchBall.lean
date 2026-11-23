module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchBallStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Cut-Finding Ball-Growing Loop Verification (`RouteProgBatchBall`)

Inductive verification of `batchBallLoopStmt` against `batchBallLoop` (failed-batch
branch).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. Full Ball-Growing Loop Verification (`batchBallLoop_triple`) -/

theorem batchBallLoop_triple {w : ℕ} {p : Program} {bBall bBfs : ℕ}
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    {G : Graph} {X V_res : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL h L : ℕ}
    {remPairs : List (Finset ℕ × Finset ℕ)}
    (hhL : h * L = hL)
    (hnX : cfg.nX = X.card) (hk : cfg.k = remPairs.length)
    (hVX_res : V_res ⊆ X)
    (hvalid : ValidTerminalPairs X remPairs)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    {mem0 : ℕ → ℕ} (rem : ℕ) :
    ∀ (i : ℕ) (U : Finset ℕ) (ul : List ℕ) (bfsGen ballGen : ℕ) (st0 : State),
      i + rem = remPairs.length →
      BatchBallInv st0.mem mem0 G X V_res cfg hL remPairs i U ul bfsGen ballGen →
      BatchBallRegs st0.regs cfg cfgAddr bfsGen ballGen i U.card →
      ∀ ω,
        let Hres : Graph := ⟨G.n, G.inside V_res⟩
        let res := batchBallLoop (adjOf Hres X) X cfg.b h L (remPairs.drop i) U (X \ U) 0
        ∃ stF c ulF,
          Runs w p ω (batchBallLoopStmt bBall) st0 .normal stF c ∧
          (∀ r, r ≤ 17 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 → stF.regs r = st0.regs r) ∧
          stF.regs 32 = res.1.card ∧
          cfg.bfsGenIn ≤ stF.regs 18 ∧ stF.regs 18 ≤ cfg.bfsGenIn + cfg.k * (cfg.d + 3) ∧
          cfg.ballGenIn ≤ stF.regs 19 ∧ stF.regs 19 ≤ cfg.ballGenIn + cfg.k ∧
          BatchBallInv stF.mem mem0 G X V_res cfg hL remPairs remPairs.length res.1 ulF
            (stF.regs 18) (stF.regs 19) ∧
          c ≤ 1050 * res.2 +
              45 * ((remPairs.drop i).map fun ab => ab.1.card + ab.2.card).sum +
              40 * (res.1.card - U.card) + 25 := by
  have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  induction rem with
  | zero =>
    intro i U ul bfsGen ballGen st0 hi hinv hregs ω
    have hi_eq : i = remPairs.length := by omega
    have hdrop : remPairs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rcases hregs with ⟨_, _, hr2, _, _, _, _, _, _, _, hr18, hr19, _, _, _, _, hr31, hr32, _, _, _, _⟩
    dsimp only; rw [hdrop]; simp only [batchBallLoop, List.map_nil, List.sum_nil, Nat.sub_self]
    refine ⟨st0, _, ul,
      batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, hr31, hr2, hk, hi_eq]),
      fun _ _ => rfl, hr32,
      by rw [hr18]; exact hinv.bfs_lo, by rw [hr18]; have := hinv.bfs_hi; omega,
      by rw [hr19]; exact hinv.ball_lo, by rw [hr19]; have := hinv.ball_hi; omega,
      by rw [hr18, hr19, ← hi_eq]; exact hinv, by simp [Expr.size]⟩
  | succ rem ih =>
    intro i U ul bfsGen ballGen st0 hi hinv hregs ω
    have hi_lt : i < remPairs.length := by omega
    rcases hab_eq : remPairs[i]'hi_lt with ⟨A', B'⟩
    have hdrop_eq : remPairs.drop i = (A', B') :: remPairs.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi_lt, hab_eq]
    have hvalid_i := hvalid.1 (remPairs[i]'hi_lt) (List.getElem_mem hi_lt)
    rw [hab_eq] at hvalid_i
    have hAX : A' ⊆ X := hvalid_i.1
    have hBX : B' ⊆ X := hvalid_i.2.1
    have hregs_c := hregs
    rcases hregs_c with ⟨hr0, hr1, hr2, hr9, hr10, hr11, hr14, hr15, hr16, hr17, hr18, hr19,
      hr20, hr21, hr22, hr23, hr31, hr32, hr33, hr34, hr35, hr36⟩
    have hcond_loop : (Expr.bin .lt (.reg 31) (.reg 2)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hr31, hr2, hk, hi_lt, hw_ne]
    have hU_le_X : U.card ≤ X.card := Finset.card_le_card hinv.U_sub
    have hw_nX4 := hdisj.w_nX4
    by_cases hcut_done : 4 * U.card ≥ X.card
    · -- Early stop: 4 * |U| ≥ |X|
      have hcond4 : (Expr.bin .lt (.bin .mul (.const 4) (.reg 32)) (.reg 1)).eval w st0 = some 0 := by
        simp [Expr.eval, BinOp.eval, hr32, hr1, hnX, show 4 < 2 ^ w by omega,
          show 4 * U.card < 2 ^ w by omega, show ¬ 4 * U.card < X.card by omega]
      set st1 : State := { st0 with regs := Function.update st0.regs 31 cfg.k }
      have hrun_set : Runs w p ω (.assign 31 (.reg 2)) st0 .normal st1 ((Expr.reg 2).size + 1) :=
        runs_assign_iff.mpr ⟨cfg.k, by simp [Expr.eval, hr2], rfl, rfl, rfl⟩
      have hrun_exit : Runs w p ω (batchBallLoopStmt bBall) st1 .normal st1 _ :=
        batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, st1, hr2])
      dsimp only; rw [hdrop_eq]; simp only [batchBallLoop, hcut_done, ↓reduceIte, Nat.sub_self]
      refine ⟨st1, _, ul,
        batch_runs_loop_step hcond_loop (by decide) (batch_runs_cond_zero hcond4 hrun_set) hrun_exit,
        fun r hr => by simp [st1, (batch_ball_r_ne hr).1],
        by simp [st1, hr32],
        by simp [st1, hr18]; exact hinv.bfs_lo,
        by simp [st1, hr18]; have := hinv.bfs_hi; omega,
        by simp [st1, hr19]; exact hinv.ball_lo,
        by simp [st1, hr19]; have := hinv.ball_hi; omega,
        ⟨hinv.U_sub, by simp [st1, hr18]; exact hinv.bfs_lo,
         by simp [st1, hr18]; have := hinv.bfs_hi; omega,
         by simp [st1, hr19]; exact hinv.ball_lo,
         by simp [st1, hr19]; have := hinv.ball_hi; omega,
         hinv.res_csr, hinv.la, hinv.bs, hinv.live_ok, hinv.live_le,
         by simp [st1, hr18]; exact hinv.vis_le,
         by simp [st1, hr19]; exact hinv.ball_le,
         hinv.ul_len, hinv.ul_nd, hinv.ul_sub, hinv.ul_cov, hinv.ul_at,
         hinv.sub_init, hinv.frame_ws, hinv.ro_stamps⟩,
        by simp only [Expr.size]; omega⟩
    · -- Continue: 4 * |U| < |X|
      have hlt4 : 4 * U.card < X.card := by omega
      have hcond4 : (Expr.bin .lt (.bin .mul (.const 4) (.reg 32)) (.reg 1)).eval w st0 = some 1 := by
        simp [Expr.eval, BinOp.eval, hr32, hr1, hnX, show 4 < 2 ^ w by omega,
          show 4 * U.card < 2 ^ w by omega, hlt4, hw_ne]
      -- Filter A' into wsSBallBuf -> r37
      have ha_i := hinv.la.2 i hi_lt; dsimp only at ha_i; rw [hab_eq] at ha_i; dsimp only at ha_i
      set aOff_i := st0.mem (cfg.aOffAddr + i)
      have haOff_hi : aOff_i + A'.card ≤ X.card := by
        have hmo := localAPairsAt_slot_bound hinv.la (i + 1) remPairs.length (by omega) le_rfl
        have := hinv.la.1; have := ha_i.1; have := ha_i.2.1
        rw [show cfg.aOffAddr + (i + 1) = cfg.aOffAddr + i + 1 by omega] at hmo; omega
      obtain ⟨stA, cA, hrunA, hregsA, hA37, hS_at, hfrA, hcA⟩ :=
        batchBallFilterOne_triple (w := w) (p := p) (X := X) (Vlive := X \ U) (A := A')
          (offAddr := cfg.aOffAddr) (lenAddr := cfg.aLenAddr) (dataAddr := cfg.aDataAddr)
          (liveStampAddr := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k)
          (liveGen := cfg.liveGenIn + 1)
          (outBuf := wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k) (i := i) (off_i := aOff_i) (dstReg := 37)
          (rOff := 9) (rLen := 10) (rData := 11) (rOut := 33)
          hAX Finset.sdiff_subset
          (by have h := hdisj.ad_ws; unfold DisjRange at h ⊢; unfold batchScratchSize at h; unfold wsSBallBuf
              exact h.elim (fun x => Or.inr (by omega)) (fun x => Or.inl (by omega)))
          (by unfold DisjRange wsSBallBuf wsLiveStamp; right; omega)
          (by have := hdisj.w_ao; omega) (by have := hdisj.w_al; omega)
          (by have := hdisj.w_ad; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsSBallBuf; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsLiveStamp; omega)
          (by have := hdisj.w_livegen; omega) hw4
          (by decide) (by decide) (by decide) (by decide) (by decide)
          rfl ha_i.2.1 ha_i.2.2 hinv.live_ok hr9 hr10 hr11 hr33 hr22 hr23 hr31 ω
      -- Filter B' into wsTBallBuf -> r38
      have hb_i := hinv.bs.2 i hi_lt; dsimp only at hb_i; rw [hab_eq] at hb_i; dsimp only at hb_i
      set bOff_i := st0.mem (wsBOff cfg.ws cfg.nX cfg.m2 + i)
      have hbOff_hi : bOff_i + B'.card ≤ X.card := by
        have hmo := localBSlicesAt_slot_bound hinv.bs (i + 1) remPairs.length (by omega) le_rfl
        have := hinv.bs.1; have := hb_i.1; have := hb_i.2.1
        rw [show wsBOff cfg.ws cfg.nX cfg.m2 + (i + 1) = wsBOff cfg.ws cfg.nX cfg.m2 + i + 1 by omega] at hmo; omega
      have hfrA_out : ∀ a, a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k → stA.mem a = st0.mem a :=
        fun a ha => hfrA a (by omega)
      obtain ⟨stB, cB, hrunB, hregsB, hB38, hT_at, hfrB, hcB⟩ :=
        batchBallFilterOne_triple (w := w) (p := p) (X := X) (Vlive := X \ U) (A := B')
          (offAddr := wsBOff cfg.ws cfg.nX cfg.m2)
          (lenAddr := wsBLen cfg.ws cfg.nX cfg.m2 cfg.k)
          (dataAddr := wsBData cfg.ws cfg.nX cfg.m2 cfg.k)
          (liveStampAddr := wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k)
          (liveGen := cfg.liveGenIn + 1)
          (outBuf := wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k) (i := i) (off_i := bOff_i) (dstReg := 38)
          (rOff := 17) (rLen := 20) (rData := 21) (rOut := 34)
          hBX Finset.sdiff_subset
          (by unfold DisjRange wsTBallBuf wsBData; right; omega)
          (by unfold DisjRange wsTBallBuf wsLiveStamp; right; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsBOff; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsBLen; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsBData; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsTBallBuf; omega)
          (by have := hdisj.w_ws; unfold batchScratchSize at this; unfold wsLiveStamp; omega)
          (by have := hdisj.w_livegen; omega) hw4
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (hfrA_out _ (by unfold wsBOff wsSBallBuf; omega))
          ((hfrA_out _ (by unfold wsBLen wsSBallBuf; omega)).trans hb_i.2.1)
          (fun j hj => by
            have hj_lt : j < B'.card := by simpa [Finset.length_sort] using hj
            rw [Nat.add_assoc, hfrA_out _ (by unfold wsBData wsSBallBuf; omega), ← Nat.add_assoc]
            exact hb_i.2.2 j hj)
          (fun v hv => by rw [hfrA_out _ (by unfold wsLiveStamp wsSBallBuf; omega)]; exact hinv.live_ok v hv)
          (by rw [hregsA 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
          (by rw [hregsA 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20])
          (by rw [hregsA 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr21])
          (by rw [hregsA 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr34])
          (by rw [hregsA 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
          (by rw [hregsA 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr23])
          (by rw [hregsA 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr31]) ω
      obtain ⟨cAB, hrunAB, hcAB⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA hrunB
      have hB37 : stB.regs 37 = (A' ∩ (X \ U)).card :=
        (hregsB 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hA37
      have hregsB_eq : ∀ r, r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
          r ≠ 37 → r ≠ 38 → stB.regs r = st0.regs r := fun r h24 h25 h26 h27 h28 h29 h30 h37 h38 =>
        (hregsB r h24 h25 h26 h27 h28 h29 h30 h38).trans (hregsA r h24 h25 h26 h27 h28 h29 h30 h37)
      have hfrB_all : ∀ a,
          ¬ ((wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card) ∨
             (wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ≤ a ∧ a < wsTBallBuf cfg.ws cfg.nX cfg.m2 cfg.k + X.card)) →
          stB.mem a = st0.mem a := fun a ha =>
        (hfrB a (fun h => ha (Or.inr h))).trans (hfrA a (fun h => ha (Or.inl h)))
      have hS_atB : ListAt stB.mem (wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k)
          (((A' ∩ (X \ U)).sort (· ≤ ·)).map (locOf X)) := fun j hj => by
        have hj_lt : j < X.card := by
          have : (A' ∩ (X \ U)).card ≤ X.card := Finset.card_le_card (Finset.Subset.trans Finset.inter_subset_left hAX)
          simp only [List.length_map, Finset.length_sort] at hj; omega
        rw [hfrB _ (by unfold wsSBallBuf wsTBallBuf; omega)]
        exact hS_at j hj
      set S := A' ∩ (X \ U)
      set T := B' ∩ (X \ U)
      let growStmt : Stmt := seqStmts
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
        , .assign 32 (.reg 27) ]
      -- Branch on S = ∅ ∨ T = ∅
      by_cases hST : S = ∅ ∨ T = ∅
      · -- Skip growBall: nested .cond evaluates to .nop
        have hcond_nop : ∃ cN, Runs w p ω
            (.cond (.bin .lt (.const 0) (.reg 37))
              (.cond (.bin .lt (.const 0) (.reg 38)) growStmt .nop) .nop)
            stB .normal stB cN ∧ cN ≤ 15 := by
          rcases hST with hS0 | hT0
          · have h0 : (Expr.bin .lt (.const 0) (.reg 37)).eval w stB = some 0 := by
              simp [Expr.eval, BinOp.eval, hB37, hS0, show 0 < 2 ^ w by omega]
            exact ⟨_, batch_runs_cond_zero h0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), by simp [Expr.size]⟩
          · by_cases hS0 : S = ∅
            · have h0 : (Expr.bin .lt (.const 0) (.reg 37)).eval w stB = some 0 := by
                simp [Expr.eval, BinOp.eval, hB37, hS0, show 0 < 2 ^ w by omega]
              exact ⟨_, batch_runs_cond_zero h0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), by simp [Expr.size]⟩
            · have hSpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
              have h1 : (Expr.bin .lt (.const 0) (.reg 37)).eval w stB = some 1 := by
                simp [Expr.eval, BinOp.eval, hB37, hSpos, show 0 < 2 ^ w by omega, hw_ne]
              have h2 : (Expr.bin .lt (.const 0) (.reg 38)).eval w stB = some 0 := by
                simp [Expr.eval, BinOp.eval, hB38, hT0, show 0 < 2 ^ w by omega]
              exact ⟨_, batch_runs_cond_pos h1 (by decide)
                (batch_runs_cond_zero h2 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)), by simp [Expr.size]⟩
        rcases hcond_nop with ⟨cN, hrunN, hcN⟩
        set st1 : State := { stB with regs := Function.update stB.regs 31 (i + 1) }
        have hrun_inc : Runs w p ω (.assign 31 (.bin .add (.reg 31) (.const 1))) stB .normal st1 _ :=
          runs_assign_iff.mpr ⟨i + 1,
            by simp [Expr.eval, BinOp.eval,
                 hregsB_eq 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
                 hr31, show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by have := hdisj.w_k; omega],
            rfl, rfl, rfl⟩
        have hrun_tail := runs_seq_iff.mpr (Or.inr ⟨stB, cN, _, hrunN, hrun_inc, rfl⟩)
        obtain ⟨cInner, hrunInner, hcInner⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunAB
          (show Runs w p ω (seqStmts [.cond (.bin .lt (.const 0) (.reg 37))
              (.cond (.bin .lt (.const 0) (.reg 38)) growStmt .nop) .nop,
            .assign 31 (.bin .add (.reg 31) (.const 1))]) stB .normal st1 _ from hrun_tail)
        have hrunBody := batch_runs_cond_pos (s2 := .assign 31 (.reg 2)) hcond4 (by decide) hrunInner
        have hinv1 : BatchBallInv st1.mem mem0 G X V_res cfg hL remPairs (i + 1) U ul bfsGen ballGen := by
          have hfr_not_st : ∀ a, a < wsSBallBuf cfg.ws cfg.nX cfg.m2 cfg.k ∨
              wsCutList cfg.ws cfg.nX cfg.m2 cfg.k ≤ a → st1.mem a = st0.mem a := fun a ha =>
            hfrB_all a (by simp only [wsSBallBuf, wsTBallBuf, wsCutList] at ha ⊢; omega)
          refine ⟨hinv.U_sub, hinv.bfs_lo, by have := hinv.bfs_hi; omega,
            hinv.ball_lo, by have := hinv.ball_hi; omega,
            hinv.res_csr.congr
              (fun k hk => hfr_not_st _ (Or.inl (by unfold wsResOff wsSBallBuf; omega)))
              (fun k hk =>
                have hk' : k < cfg.m2 := lt_of_lt_of_le hk (le_trans (adjCsrOff_inside_le G hVX_res X.card) hm2)
                hfr_not_st _ (Or.inl (by unfold wsResNb wsSBallBuf; omega))),
            ?_, ?_,
            fun v hv => by rw [hfr_not_st _ (Or.inl (by unfold wsLiveStamp wsSBallBuf; omega))]; exact hinv.live_ok v hv,
            fun v hv => by rw [hfr_not_st _ (Or.inl (by unfold wsLiveStamp wsSBallBuf; omega))]; exact hinv.live_le v hv,
            fun v hv => by rw [hfr_not_st _ (Or.inl (by unfold wsVisStamp wsSBallBuf; omega))]; exact hinv.vis_le v hv,
            fun v hv => by rw [hfr_not_st _ (Or.inl (by unfold wsBallStamp wsSBallBuf; omega))]; exact hinv.ball_le v hv,
            hinv.ul_len, hinv.ul_nd, hinv.ul_sub, hinv.ul_cov,
            fun j hj => by rw [hfr_not_st _ (Or.inr (by omega))]; exact hinv.ul_at j hj,
            hinv.sub_init.of_outside_124 fun a _ ha2 => hfr_not_st a (Or.inl (by unfold wsSBallBuf; omega)),
            fun a ha => (hfrB_all a (by simp only [wsSBallBuf, wsTBallBuf, batchScratchSize] at ha ⊢; omega)).trans (hinv.frame_ws a ha),
            fun a ha => (hfr_not_st a (Or.inl (by rcases ha with ha | ha <;> (simp only [wsIsoStamp, wsCurStamp, wsSBallBuf] at ha ⊢; omega)))).trans (hinv.ro_stamps a ha)⟩
          · have h1 := hdisj.ro_ao_ws; have h2 := hdisj.al_ws; have h3 := hdisj.ad_ws
            unfold DisjRange at h1 h2 h3
            have hws_eq : ∀ a, ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
                st1.mem a = st0.mem a := fun a ha =>
              hfrB_all a (by simp only [wsSBallBuf, wsTBallBuf, batchScratchSize] at ha ⊢; omega)
            refine ⟨by rw [hws_eq _ (by rcases h1 with x | x <;> omega)]; exact hinv.la.1,
              fun j hj => ?_⟩
            have h_j := hinv.la.2 j hj
            have h_o1 := hws_eq (cfg.aOffAddr + j) (by rcases h1 with x | x <;> omega)
            have h_o2 := hws_eq (cfg.aOffAddr + j + 1) (by rcases h1 with x | x <;> omega)
            have h_l := hws_eq (cfg.aLenAddr + j) (by rcases h2 with x | x <;> omega)
            refine ⟨by rw [h_o1, h_o2, h_l]; exact h_j.1, by rw [h_l]; exact h_j.2.1, fun t ht => ?_⟩
            have ht_le : st0.mem (cfg.aOffAddr + j) + t < X.card := by
              have hmo := localAPairsAt_slot_bound hinv.la (j + 1) remPairs.length (by omega) le_rfl
              have := hinv.la.1; have := h_j.1; have := h_j.2.1
              rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmo
              simp only [List.length_map, Finset.length_sort] at ht; omega
            rw [h_o1, Nat.add_assoc, hws_eq _ (by rcases h3 with x | x <;> omega), ← Nat.add_assoc]
            exact h_j.2.2 t ht
          · refine ⟨by rw [hfr_not_st _ (Or.inl (by unfold wsBOff wsSBallBuf; omega))]; exact hinv.bs.1,
              fun j hj => ?_⟩
            have h_j := hinv.bs.2 j hj
            have h_o1 := hfr_not_st (wsBOff cfg.ws cfg.nX cfg.m2 + j) (Or.inl (by unfold wsBOff wsSBallBuf; omega))
            have h_o2 := hfr_not_st (wsBOff cfg.ws cfg.nX cfg.m2 + j + 1) (Or.inl (by unfold wsBOff wsSBallBuf; omega))
            have h_l := hfr_not_st (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k + j) (Or.inl (by unfold wsBLen wsSBallBuf; omega))
            refine ⟨by rw [h_o1, h_o2, h_l]; exact h_j.1, by rw [h_l]; exact h_j.2.1, fun t ht => ?_⟩
            have ht_le : st0.mem (wsBOff cfg.ws cfg.nX cfg.m2 + j) + t < X.card := by
              have hmo := localBSlicesAt_slot_bound hinv.bs (j + 1) remPairs.length (by omega) le_rfl
              have := hinv.bs.1; have := h_j.1; have := h_j.2.1
              rw [show wsBOff cfg.ws cfg.nX cfg.m2 + (j + 1) = wsBOff cfg.ws cfg.nX cfg.m2 + j + 1 by omega] at hmo
              simp only [List.length_map, Finset.length_sort] at ht; omega
            rw [h_o1, Nat.add_assoc, hfr_not_st _ (Or.inl (by unfold wsBData wsSBallBuf; omega)), ← Nat.add_assoc]
            exact h_j.2.2 t ht
        have hregs1 : BatchBallRegs st1.regs cfg cfgAddr bfsGen ballGen (i + 1) U.card := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [st1], ?_, ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [st1]
            rwa [Function.update_of_ne (by decide),
              hregsB_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        obtain ⟨stF, cIH, ulF, hrunIH, hregsIH, hF32, hbLoF, hbHiF, hbgLoF, hbgHiF, hinvF, hcIH⟩ :=
          ih (i + 1) U ul bfsGen ballGen st1 (by omega) hinv1 hregs1 ω
        have hadd := batchBallLoop_cost_add (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop (i + 1)) U (X \ U) 0 1
        simp only [Nat.zero_add] at hadd
        have hstep_eq1 : (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop i) U (X \ U) 0).1 =
            (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop (i + 1)) U (X \ U) 0).1 := by
          rw [hdrop_eq]; dsimp only [batchBallLoop]
          simp only [hcut_done, show A' ∩ (X \ U) = S from rfl, show B' ∩ (X \ U) = T from rfl, hST, ↓reduceIte, Nat.zero_add]
          exact hadd.1
        have hstep_eq2 : (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop i) U (X \ U) 0).2 =
            (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop (i + 1)) U (X \ U) 0).2 + 1 := by
          rw [hdrop_eq]; dsimp only [batchBallLoop]
          simp only [hcut_done, show A' ∩ (X \ U) = S from rfl, show B' ∩ (X \ U) = T from rfl, hST, ↓reduceIte, Nat.zero_add]
          exact hadd.2
        refine ⟨stF, _, ulF, batch_runs_loop_step hcond_loop (by decide) hrunBody hrunIH,
          fun r hr => (hregsIH r hr).trans (by
            have hne := batch_ball_r_ne hr
            simp [st1, hne.1, hregsB_eq r hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1
              hne.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
              hne.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2]),
          by rw [hstep_eq1]; exact hF32, hbLoF, hbHiF, hbgLoF, hbgHiF,
          by rw [hstep_eq1]; exact hinvF, ?_⟩
        rw [hstep_eq1, hstep_eq2, hdrop_eq]
        simp only [List.map_cons, List.sum_cons, Expr.size, List.length_cons, List.length_nil, List.length_append] at hcA hcB hcAB hcInner hcIH ⊢
        omega
      · -- Both S ≠ ∅ and T ≠ ∅: call batchBallStep_grow
        push Not at hST
        have hSpos : 0 < S.card := Finset.card_pos.mpr hST.1
        have hTpos : 0 < T.card := Finset.card_pos.mpr hST.2
        have hcondS : (Expr.bin .lt (.const 0) (.reg 37)).eval w stB = some 1 := by
          simp [Expr.eval, BinOp.eval, hB37, hSpos, show 0 < 2 ^ w by omega, hw_ne]
        have hcondT : (Expr.bin .lt (.const 0) (.reg 38)).eval w stB = some 1 := by
          simp [Expr.eval, BinOp.eval, hB38, hTpos, show 0 < 2 ^ w by omega, hw_ne]
        obtain ⟨stG, cG, ul1, bfsGen1, ballGen1, hrunG, hregsG_eq, hG18, hG19, hG32, hinvG, hcG⟩ :=
          batchBallStep_grow hball_proc hbfs_proc hnX hk hVX_res hm2 hdisj hi_lt
            Finset.inter_subset_right Finset.inter_subset_right hinv hregs hregsB_eq hB37 hB38
            hS_atB hT_at hfrB_all ω h L hhL
        set br := growBall (adjOf ⟨G.n, G.inside V_res⟩ X) (X \ U) S T cfg.b h L
        set st1 : State := { stG with regs := Function.update stG.regs 31 (i + 1) }
        have hrun_inc : Runs w p ω (.assign 31 (.bin .add (.reg 31) (.const 1))) stG .normal st1 _ :=
          runs_assign_iff.mpr ⟨i + 1,
            by simp [Expr.eval, BinOp.eval,
                 hregsG_eq 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
                 hr31, show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by have := hdisj.w_k; omega],
            rfl, rfl, rfl⟩
        have hcondG := batch_runs_cond_pos (s2 := .nop) hcondS (by decide)
          (batch_runs_cond_pos (s2 := .nop) hcondT (by decide) hrunG)
        have hrun_tail := runs_seq_iff.mpr (Or.inr ⟨stG, _, _, hcondG, hrun_inc, rfl⟩)
        obtain ⟨cInner, hrunInner, hcInner⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunAB
          (show Runs w p ω (seqStmts [.cond (.bin .lt (.const 0) (.reg 37))
              (.cond (.bin .lt (.const 0) (.reg 38)) growStmt .nop) .nop,
            .assign 31 (.bin .add (.reg 31) (.const 1))]) stB .normal st1 _ from hrun_tail)
        have hrunBody := batch_runs_cond_pos (s2 := .assign 31 (.reg 2)) hcond4 (by decide) hrunInner
        have hregs1 : BatchBallRegs st1.regs cfg cfgAddr bfsGen1 ballGen1 (i + 1) (U ∪ br.ball).card := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            by simp [st1, hG18], by simp [st1, hG19],
            ?_, ?_, ?_, ?_, by simp [st1], by simp [st1, hG32], ?_, ?_, ?_, ?_⟩
          all_goals
            simp only [st1]
            rwa [Function.update_of_ne (by decide),
              hregsG_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        have hdiff_eq : (X \ U) \ br.ball = X \ (U ∪ br.ball) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
        obtain ⟨stF, cIH, ulF, hrunIH, hregsIH, hF32, hbLoF, hbHiF, hbgLoF, hbgHiF, hinvF, hcIH⟩ :=
          ih (i + 1) (U ∪ br.ball) ul1 bfsGen1 ballGen1 st1 (by omega) hinvG hregs1 ω
        have hadd := batchBallLoop_cost_add (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L
          (remPairs.drop (i + 1)) (U ∪ br.ball) (X \ (U ∪ br.ball)) 0 (br.cost + 1)
        simp only [Nat.zero_add] at hadd
        have hnotST : ¬ (S = ∅ ∨ T = ∅) := by
          rintro (h | h)
          · exact hST.1.ne_empty h
          · exact hST.2.ne_empty h
        have hstep_eq1 : (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop i) U (X \ U) 0).1 =
            (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop (i + 1)) (U ∪ br.ball) (X \ (U ∪ br.ball)) 0).1 := by
          rw [hdrop_eq]; dsimp only [batchBallLoop]
          simp only [hcut_done, show A' ∩ (X \ U) = S from rfl, show B' ∩ (X \ U) = T from rfl, hnotST, ↓reduceIte, Nat.zero_add]
          rw [show growBall (adjOf ⟨G.n, G.inside V_res⟩ X) (X \ U) S T cfg.b h L = br from rfl, hdiff_eq]
          exact hadd.1
        have hstep_eq2 : (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop i) U (X \ U) 0).2 =
            (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L (remPairs.drop (i + 1)) (U ∪ br.ball) (X \ (U ∪ br.ball)) 0).2 + (br.cost + 1) := by
          rw [hdrop_eq]; dsimp only [batchBallLoop]
          simp only [hcut_done, show A' ∩ (X \ U) = S from rfl, show B' ∩ (X \ U) = T from rfl, hnotST, ↓reduceIte, Nat.zero_add]
          rw [show growBall (adjOf ⟨G.n, G.inside V_res⟩ X) (X \ U) S T cfg.b h L = br from rfl, hdiff_eq]
          exact hadd.2
        have hball_mono : U ∪ br.ball ⊆ (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L
            (remPairs.drop (i + 1)) (U ∪ br.ball) (X \ (U ∪ br.ball)) 0).1 := by
          have hgen : ∀ (l : List (Finset ℕ × Finset ℕ)) (U0 V0 : Finset ℕ) (c0 : ℕ),
              U0 ⊆ (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L l U0 V0 c0).1 := by
            intro l; induction l with
            | nil => intro U0 _ _; exact le_rfl
            | cons p rest ihr =>
              intro U0 V0 c0; dsimp only [batchBallLoop]
              split_ifs
              · exact le_rfl
              · exact ihr U0 V0 _
              · exact Finset.Subset.trans Finset.subset_union_left (ihr _ _ _)
          exact hgen _ _ _ _
        have hU_disj : Disjoint U br.ball :=
          Finset.disjoint_left.mpr fun x hxU hxB =>
            (Finset.mem_sdiff.mp (growBall_ball_sub (adjOf ⟨G.n, G.inside V_res⟩ X) (X \ U) S T cfg.b h L hxB)).2 hxU
        have hU1_card : (U ∪ br.ball).card = U.card + br.ball.card := Finset.card_union_of_disjoint hU_disj
        have hcard_mono : (U ∪ br.ball).card ≤ (batchBallLoop (adjOf ⟨G.n, G.inside V_res⟩ X) X cfg.b h L
            (remPairs.drop (i + 1)) (U ∪ br.ball) (X \ (U ∪ br.ball)) 0).1.card := Finset.card_le_card hball_mono
        have hbr_pos : 1 ≤ br.cost := growBall_cost_pos (adjOf ⟨G.n, G.inside V_res⟩ X) (X \ U) S T cfg.b h L
        refine ⟨stF, _, ulF, batch_runs_loop_step hcond_loop (by decide) hrunBody hrunIH,
          fun r hr => (hregsIH r hr).trans (by
            have hne := batch_ball_r_ne hr
            simp [st1, hne.1, hregsG_eq r hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1
              hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
              hne.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.1
              hne.2.2.2.2.2.2.2.2.2.2.2.2]),
          by rw [hstep_eq1]; exact hF32, hbLoF, hbHiF, hbgLoF, hbgHiF,
          by rw [hstep_eq1]; exact hinvF, ?_⟩
        rw [hstep_eq1, hstep_eq2, hdrop_eq]
        simp only [ballProgCost, List.map_cons, List.sum_cons, Expr.size, List.length_cons, List.length_nil, List.length_append] at hcA hcB hcAB hcG hcInner hcIH ⊢
        omega

end MinCostFlow.ExpanderDecomp
