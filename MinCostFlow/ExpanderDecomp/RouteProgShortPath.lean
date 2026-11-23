module

public import MinCostFlow.ExpanderDecomp.RouteProgShortPathStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short-Path Blocking Word-RAM Procedure (`shortPathBlock_triple`, `shortPathBlock_meetsContract`)

Verifies `shortPathBlockProc` against `shortPathBlock`: filters `S` into `S ∩ V`,
runs up to `d + 1` BFS + DFS blocking phases calling `bfsLayersProc` and `dfsBlockProc`,
isolates accepted path vertices in `maskArr`, maintains `PathChainAt` and monotonic stamp bounds,
and runs in `≤ 900 * sp.cost + 50 * (S \ V).card + 250` deterministic Word-RAM steps.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Phase Loop Verification (`spPhaseLoop_triple`) -/

private lemma spPhaseLoop_triple {w : ℕ} {p : Program} {bBfs bDfs : ℕ}
    {X V0 S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg} {spCfgAddr m2 : ℕ}
    {mem0 : ℕ → ℕ}
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hV0X : V0 ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcsr0 : AdjCsrAt mem0 bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hbfs_cfg0 : BfsCfgAt mem0 spCfg.bfsCfgAddr bfsCfg)
    (hdfs_cfg0 : DfsCfgAt mem0 spCfg.dfsCfgAddr dfsCfg)
    (hstop0 : ∀ v < X.card, mem0 (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T)
    (rem : ℕ) :
    ∀ (V : Finset ℕ) (acc : List ((ℕ × ℕ) × List ℕ))
      (heapPtr head tail bfsGen dfsGen : ℕ) (st0 : State),
      SpLoopInv st0.mem mem0 X V0 S spCfg bfsCfg dfsCfg spCfgAddr
        rem V acc heapPtr head tail bfsGen dfsGen →
      SpLoopRegs st0.regs spCfg spCfgAddr
        rem (S ∩ V).card bfsGen dfsGen heapPtr head tail acc.length →
      ∀ ω, ∃ st' c,
        Runs w p ω (spPhaseLoopStmt bBfs bDfs) st0 .normal st' c ∧
        (let res := shortPathBlockLoop adj S T spCfg.d rem V acc 0
         ∃ heapPtr' head' tail' bfsGen' dfsGen',
           SpLoopInv st'.mem mem0 X V0 S spCfg bfsCfg dfsCfg spCfgAddr
             0 res.remVerts res.paths heapPtr' head' tail' bfsGen' dfsGen' ∧
           SpLoopRegs st'.regs spCfg spCfgAddr
             0 (st'.regs 14) bfsGen' dfsGen' heapPtr' head' tail' res.paths.length ∧
           bfsGen ≤ bfsGen' ∧ dfsGen ≤ dfsGen') ∧
        c ≤ 850 * (shortPathBlockLoop adj S T spCfg.d rem V acc 0).cost + 5 := by
  induction rem with
  | zero =>
    intro V acc heapPtr head tail bfsGen dfsGen st0 hinv hregs ω
    have hr13 : st0.regs 13 = 0 := hregs 13 (by decide)
    have hrun : Runs w p ω (spPhaseLoopStmt bBfs bDfs) st0 .normal st0 ((Expr.reg 13).size + 1) :=
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr13], rfl, rfl, rfl⟩)
    refine ⟨st0, _, hrun, ⟨heapPtr, head, tail, bfsGen, dfsGen, hinv, ?_, le_rfl, le_rfl⟩,
      by simp [shortPathBlockLoop, Expr.size]⟩
    intro r hr
    by_cases h14 : r = 14
    · subst h14; rfl
    · have := hregs r hr
      interval_cases r <;> first | exact this | omega
  | succ rem ih =>
    intro V acc heapPtr head tail bfsGen dfsGen st0 hinv hregs ω
    have hVX : V ⊆ X := Finset.Subset.trans hinv.V_sub hV0X
    have hSV_le_X : (S ∩ V).card ≤ X.card :=
      Finset.card_le_card (Finset.Subset.trans Finset.inter_subset_right hVX)
    have hV0V_le_X : (V0 \ V).card ≤ X.card :=
      Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset hV0X)
    have hw_sp := hdisj.w_sp
    have hw_bgen := hdisj.w_bgen
    have hw_dgen := hdisj.w_dgen
    have hw_d := hdisj.w_d
    have hw_hp10 := hdisj.w_hp10
    have hw_nX := hdisj.dfs_disj.w_nX
    have hw_bcfg : spCfg.bfsCfgAddr + 25 < 2 ^ w := hdisj.bfs_disj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hw_dcfg := hdisj.dfs_disj.w_cfg
    have hw_mask : spCfg.maskArrAddr + X.card + 5 < 2 ^ w := by
      have := hdisj.dfs_disj.w_mask; dsimp only at this; rw [hdisj.dfs_mask] at this; exact this
    have hw_mb : spCfg.maskBadVal < 2 ^ w := by
      have := hdisj.dfs_disj.w_mb; dsimp only at this; rw [hdisj.dfs_bad] at this; exact this
    have hw_ul : spCfg.usedListAddr + X.card + 5 < 2 ^ w := by
      have := hdisj.dfs_disj.w_ul; dsimp only at this; rw [hdisj.dfs_usedList] at this; exact this
    have hw_sbuf : spCfg.sBufAddr + X.card + 5 < 2 ^ w := by
      have := hdisj.dfs_disj.w_src; dsimp only at this; rw [hdisj.dfs_srcPtr] at this; exact this
    have hw4 := hdisj.dfs_disj.w4
    have hbfs_gen_le : bfsGen + 1 ≤ spCfg.bfsGenIn + spCfg.d + 1 := by have := hinv.bgen_hi; omega
    have hdfs_gen_le : dfsGen + 1 ≤ spCfg.dfsGenIn + spCfg.d + 1 := by have := hinv.dgen_hi; omega
    -- Unroll one iteration of spPhaseLoopStmt: guard r13 = rem + 1 ≠ 0
    have hr13 : st0.regs 13 = rem + 1 := hregs 13 (by decide)
    have hev_guard : (Expr.reg 13).eval w st0 = some (rem + 1) := by
      simp [Expr.eval, hr13]
    -- Step 1: r15 := bfsGen + 1; mem[bcfg+12] := bfsGen + 1; mem[bcfg+15] := (S ∩ V).card
    set bfsGen1 := bfsGen + 1
    set bfsCfg1 : BfsCfg := { bfsCfg with bfsGen := bfsGen1, initLen := (S ∩ V).card }
    set st1 : State :=
      { mem := Function.update (Function.update st0.mem (spCfg.bfsCfgAddr + 12) bfsGen1)
          (spCfg.bfsCfgAddr + 15) (S ∩ V).card
        regs := Function.update st0.regs 15 bfsGen1
        pos := st0.pos }
    have hpre_step : ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 15 (.bin .add (.reg 15) (.const 1))
            , .store (.bin .add (.reg 1) (.const 12)) (.reg 15)
            , .store (.bin .add (.reg 1) (.const 15)) (.reg 14) ])
          st0 .normal st1 c1 ∧ c1 ≤ 25 := by
      have h0 : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .assign 15 (.bin .add (.reg 15) (.const 1))
              , .store (.bin .add (.reg 1) (.const 12)) (.reg 15)
              , .store (.bin .add (.reg 1) (.const 15)) (.reg 14) ])
            st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 25 := by
        dsimp only [seqStmts]
        have hr1 : st0.regs 1 = spCfg.bfsCfgAddr := hregs 1 (by decide)
        have hr14 : st0.regs 14 = (S ∩ V).card := hregs 14 (by decide)
        have hr15 : st0.regs 15 = bfsGen := hregs 15 (by decide)
        refine runs_seq_assign_le (v := bfsGen1) (by eval_expr) ?_
        refine runs_seq_store_le (x := spCfg.bfsCfgAddr + 12) (v := bfsGen1) (by eval_expr) (by eval_expr) ?_
        refine runs_store_le (x := spCfg.bfsCfgAddr + 15) (v := (S ∩ V).card) (by eval_expr) (by eval_expr)
          ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c1, hrun, ⟨rfl, rfl⟩, hc1⟩
      exact ⟨c1, hrun, by omega⟩
    rcases hpre_step with ⟨c1, hrun1, hc1⟩
    have hfr1 : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st1.mem a = mem0 a := by
      intro a ha
      have hne15 : a ≠ spCfg.bfsCfgAddr + 15 := fun heq =>
        ha (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr heq.symm)))))
      have hne12 : a ≠ spCfg.bfsCfgAddr + 12 := fun heq =>
        ha (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl heq.symm)))))
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
      exact hinv.frame a ha
    -- Step 2: call bBfs [r1]
    have hbfs_cfg1 : BfsCfgAt st1.mem spCfg.bfsCfgAddr bfsCfg1 := by
      rcases hbfs_cfg0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, _, b13, b14, _⟩
      have hst : ∀ i < 16, i ≠ 12 → i ≠ 15 → st1.mem (spCfg.bfsCfgAddr + i) = mem0 (spCfg.bfsCfgAddr + i) :=
        fun i hi h12 h15 => bfsCfg_static_of_spFrame hdisj hfr1 hi h12 h15
      refine ⟨(hst 0 (by decide) (by decide) (by decide)).trans b0,
        (hst 1 (by decide) (by decide) (by decide)).trans b1,
        (hst 2 (by decide) (by decide) (by decide)).trans b2,
        (hst 3 (by decide) (by decide) (by decide)).trans b3,
        (hst 4 (by decide) (by decide) (by decide)).trans b4,
        (hst 5 (by decide) (by decide) (by decide)).trans b5,
        (hst 6 (by decide) (by decide) (by decide)).trans b6,
        (hst 7 (by decide) (by decide) (by decide)).trans b7,
        (hst 8 (by decide) (by decide) (by decide)).trans b8,
        (hst 9 (by decide) (by decide) (by decide)).trans b9,
        (hst 10 (by decide) (by decide) (by decide)).trans b10,
        (hst 11 (by decide) (by decide) (by decide)).trans b11,
        by simp [st1, bfsCfg1],
        (hst 13 (by decide) (by decide) (by decide)).trans b13,
        (hst 14 (by decide) (by decide) (by decide)).trans b14,
        by simp [st1, bfsCfg1]⟩
    have hcsr1 : AdjCsrAt st1.mem bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj :=
      adjCsrAt_of_spFrame hdisj hm2 hcsr0 hfr1
    have hstop1 : ∀ v < X.card, st1.mem (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T :=
      stop_of_spFrame hdisj hstop0 hfr1
    have hmask1 : ∀ v < X.card, st1.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V := by
      intro v hv
      have hne15 : spCfg.maskArrAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.mask_bcfg with x | x <;> omega
      have hne12 : spCfg.maskArrAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.mask_bcfg with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
      exact hinv.mask_ok v hv
    have hsbuf1 : ListAt st1.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) := by
      intro j hj
      have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
      have hne15 : spCfg.sBufAddr + j ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.sbuf_bcfg with x | x <;> omega
      have hne12 : spCfg.sBufAddr + j ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.sbuf_bcfg with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
      exact hinv.sbuf_at j hj
    have hvis1_fresh : ∀ v < X.card, st1.mem (bfsCfg.visStampAddr + v) ≠ bfsGen1 := by
      intro v hv
      have hne15 : bfsCfg.visStampAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_vis with x | x <;> omega
      have hne12 : bfsCfg.visStampAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_vis with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
      have := hinv.vis_le v hv; omega
    have hbfs_disj1 : BfsDisj w X.card m2 bfsCfg1 spCfg.bfsCfgAddr :=
      BfsDisj.of_sp hdisj hbfs_gen_le hSV_le_X
    have hbfs_pre : (bfsLayersContract w X V (S ∩ V) T adj bfsCfg1 m2).pre [spCfg.bfsCfgAddr] st1.mem := by
      dsimp only [bfsLayersContract, List.getD]
      exact ⟨rfl, hVX, Finset.inter_subset_right, hadj_X, hbfs_cfg1, hcsr1.1, hm2, hbfs_disj1,
        by simpa [bfsCfg1, hdisj.bfs_mask, hdisj.bfs_bad] using hmask1,
        fun h0 => by dsimp only [bfsCfg1] at h0; rw [hdisj.bfs_hasStop] at h0; omega,
        fun _ => hstop1, by simpa [bfsCfg1, hdisj.bfs_initPtr] using hsbuf1, rfl, hvis1_fresh⟩
    have hbfs_mc := bfsLayers_meetsContract (w := w) hbfs_proc X V (S ∩ V) T adj bfsCfg1 m2
    have hbfs_args : evalArgs w st1 [.reg 1] = some [spCfg.bfsCfgAddr] := by
      have hr1 : st1.regs 1 = spCfg.bfsCfgAddr := by simp [st1, hregs 1 (by decide)]
      simp [evalArgs, Expr.eval, hr1]
    obtain ⟨st2, c2, v2, hrun2, hpost2, hr2_21, hr2_oth, hc2⟩ :=
      runs_call_of_meetsContract (r := 21) hbfs_mc hbfs_args
        (by intro v hv; simp at hv; subst hv; omega) hbfs_pre ω
    simp only [bfsLayersContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpost2 hc2
    have hbfs_eq : bfsLayers adj V (S ∩ V) bfsCfg1.maxDist T = bfsLayers adj V S spCfg.d T := by
      dsimp only [bfsCfg1]; rw [hdisj.bfs_maxDist, bfsLayers_inter]
    rw [hbfs_eq] at hpost2 hc2
    set bfs := bfsLayers adj V S spCfg.d T
    rcases hpost2 with ⟨_, hbfs_out, hvis_untouch, hbfs_fr⟩
    dsimp only [bfsCfg1] at hvis_untouch
    have hbfs_inv := bfsLayers_inv adj V S spCfg.d T
    have hfr2 : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st2.mem a = mem0 a := by
      intro a ha
      rw [hbfs_fr a (fun hbw => ha (Or.inl hbw))]
      exact hfr1 a ha
    have hregs2 : ∀ r ≤ 20, st2.regs r = st1.regs r := fun r hr => hr2_oth r (by omega)
    have hvis2_le : ∀ v < X.card, st2.mem (bfsCfg.visStampAddr + v) ≤ bfsGen1 := by
      intro v hv
      by_cases hmem : origOf X v ∈ bfs.visited
      · have heq : st2.mem (bfsCfg.visStampAddr + v) = bfsGen1 := (hbfs_out.2.2.1 v hv).mpr hmem
        omega
      · rw [hvis_untouch v hv hmem]
        have hne15 : bfsCfg.visStampAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_vis with x | x <;> omega
        have hne12 : bfsCfg.visStampAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_vis with x | x <;> omega
        simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
        have := hinv.vis_le v hv; omega
    have hcur2_le : ∀ v < X.card, st2.mem (dfsCfg.curStampAddr + v) ≤ dfsGen := by
      intro v hv
      rw [hbfs_fr _ (hdisj.cs_bfsW _ ⟨by omega, by omega⟩)]
      have hne15 : dfsCfg.curStampAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_cs with x | x <;> omega
      have hne12 : dfsCfg.curStampAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_cs with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]; exact hinv.cur_le v hv
    have hused2_le : ∀ v < X.card, st2.mem (dfsCfg.usedStampAddr + v) ≤ dfsGen := by
      intro v hv
      rw [hbfs_fr _ (hdisj.us_bfsW _ ⟨by omega, by omega⟩)]
      have hne15 : dfsCfg.usedStampAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_us with x | x <;> omega
      have hne12 : dfsCfg.usedStampAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_us with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]; exact hinv.used_le v hv
    have hdead2_le : ∀ v < X.card, st2.mem (dfsCfg.deadStampAddr + v) ≤ dfsGen := by
      intro v hv
      rw [hbfs_fr _ (hdisj.ds_bfsW _ ⟨by omega, by omega⟩)]
      have hne15 : dfsCfg.deadStampAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_ds with x | x <;> omega
      have hne12 : dfsCfg.deadStampAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_ds with x | x <;> omega
      simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]; exact hinv.dead_le v hv
    have hmask2_eq : ∀ v < X.card, st2.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v) := by
      intro v hv
      have hro := hdisj.bfs_disj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (spCfg.maskArrAddr + v)
        ⟨by dsimp only; rw [hdisj.bfs_mask]; omega, by dsimp only; rw [hdisj.bfs_mask]; omega⟩
      rw [hbfs_fr _ hro]
      have hne15 : spCfg.maskArrAddr + v ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.mask_bcfg with x | x <;> omega
      have hne12 : spCfg.maskArrAddr + v ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.mask_bcfg with x | x <;> omega
      simp [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
    have hmask2 : ∀ v < X.card, st2.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V := by
      intro v hv; rw [hmask2_eq v hv]; exact hinv.mask_ok v hv
    have hsbuf2 : ListAt st2.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) := by
      intro j hj
      have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
      have hro := hdisj.bfs_disj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (spCfg.sBufAddr + j)
        ⟨by dsimp only; rw [hdisj.bfs_initPtr]; omega, by dsimp only; rw [hdisj.bfs_initPtr]; omega⟩
      rw [hbfs_fr _ hro]; exact hsbuf1 j hj
    have hchain2 : PathChainAt st2.mem X spCfg.heapIn heapPtr head tail acc :=
      hinv.chain.congr fun k hk1 hk2 => by
        have hhi : heapPtr ≤ spCfg.heapIn + 5 * X.card := by have := hinv.heap_hi; omega
        rw [hbfs_fr k (hdisj.hp10_bfsW k ⟨hk1, by omega⟩)]
        have hne15 : k ≠ spCfg.bfsCfgAddr + 15 := by rcases hdisj.bcfg_hp10 with x | x <;> omega
        have hne12 : k ≠ spCfg.bfsCfgAddr + 12 := by rcases hdisj.bcfg_hp10 with x | x <;> omega
        simp only [st1, Function.update_of_ne hne15, Function.update_of_ne hne12]
    -- Step 3: r22 := mem[r1 + 19] (bfsHit)
    set hitVal := if bfs.hitStop then 1 else 0
    have hhit_mem : st2.mem (spCfg.bfsCfgAddr + 19) = hitVal := hbfs_out.2.2.2.2.2.2.2.1
    set st3 : State := { st2 with regs := Function.update st2.regs 22 hitVal }
    have hrun3 : Runs w p ω (.assign 22 (.load (.bin .add (.reg 1) (.const 19)))) st2 .normal st3 5 := by
      have hr2_1 : st2.regs 1 = spCfg.bfsCfgAddr := (hregs2 1 (by decide)).trans
        (by simp [st1, hregs 1 (by decide)])
      have hev : (Expr.load (.bin .add (.reg 1) (.const 19))).eval w st2 = some hitVal := by
        simp [Expr.eval, BinOp.eval, hr2_1, show 19 < 2 ^ w by omega,
          show spCfg.bfsCfgAddr + 19 < 2 ^ w by omega, hhit_mem]
      exact runs_assign_iff.mpr ⟨hitVal, hev, rfl, rfl, rfl⟩
    -- Branch on bfs.hitStop
    cases hhit : bfs.hitStop with
    | false =>
      have hhit0 : hitVal = 0 := by simp [hitVal, hhit]
      set st4 : State := { st3 with regs := Function.update st3.regs 13 0 }
      have hrun_cond : Runs w p ω
          (.cond (.reg 22)
            (seqStmts
              [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
              , .assign 16 (.bin .add (.reg 16) (.const 1))
              , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
              , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
              , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
              , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
              , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
              , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
              , .store (.bin .add (.reg 2) (.const 23)) (.reg 19)
              , .call 24 bDfs [.reg 2]
              , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
              , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
              , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
              , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
              , .assign 20 (.bin .add (.reg 20) (.reg 25))
              , spIsolateLoopStmt
              , spFilterInPlaceStmt
              , .assign 14 (.reg 27)
              , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
            (.assign 13 (.const 0)))
          st3 .normal st4 ((Expr.reg 22).size + ((Expr.const 0).size + 1) + 1) := by
        refine runs_cond_iff.mpr ⟨0, (Expr.const 0).size + 1, by simp [Expr.eval, st3, hhit0], ?_, rfl⟩
        have ha : Runs w p ω (.assign 13 (.const 0)) st3 .normal st4 ((Expr.const 0).size + 1) :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
        simpa using ha
      have hrun_exit : Runs w p ω (spPhaseLoopStmt bBfs bDfs) st4 .normal st4 ((Expr.reg 13).size + 1) :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, st4], rfl, rfl, rfl⟩)
      -- Combine body execution st0 → st4
      have hbody_tail : Runs w p ω
          (seqStmts
            [ .call 21 bBfs [.reg 1]
            , .assign 22 (.load (.bin .add (.reg 1) (.const 19)))
            , .cond (.reg 22)
                (seqStmts
                  [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
                  , .assign 16 (.bin .add (.reg 16) (.const 1))
                  , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
                  , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
                  , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
                  , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
                  , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
                  , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
                  , .store (.bin .add (.reg 2) (.const 23)) (.reg 19)
                  , .call 24 bDfs [.reg 2]
                  , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
                  , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
                  , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
                  , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
                  , .assign 20 (.bin .add (.reg 20) (.reg 25))
                  , spIsolateLoopStmt
                  , spFilterInPlaceStmt
                  , .assign 14 (.reg 27)
                  , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
                (.assign 13 (.const 0)) ])
          st1 .normal st4 (c2 + (5 + ((Expr.reg 22).size + ((Expr.const 0).size + 1) + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hrun3, hrun_cond, rfl⟩), rfl⟩)
      obtain ⟨cB, hrunB, hcB⟩ := runs_seqStmts_append (by simp) (by simp) hrun1 hbody_tail
      have hrun_tot : Runs w p ω (spPhaseLoopStmt bBfs bDfs) st0 .normal st4
          ((Expr.reg 13).size + cB + ((Expr.reg 13).size + 1) + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨rem + 1, st4, cB, _, hev_guard, by omega, hrunB, hrun_exit, rfl⟩))
      have hres_eq : shortPathBlockLoop adj S T spCfg.d (rem + 1) V acc 0 =
          { paths := acc, remVerts := V, cost := 0 + bfs.cost + 1 } := by
        dsimp only [shortPathBlockLoop]
        rw [show bfsLayers adj V S spCfg.d T = bfs from rfl, hhit]; simp
      refine ⟨st4, _, hrun_tot, ?_, ?_⟩
      · rw [hres_eq]
        refine ⟨heapPtr, head, tail, bfsGen1, dfsGen,
          ⟨hinv.V_sub, hinv.paths_le, hinv.heap_lo, hinv.heap_hi, by have := hinv.bgen_lo; omega,
            by omega, hinv.dgen_lo, by have := hinv.dgen_hi; omega,
            hmask2, fun v hv => by rw [show st4.mem _ = st2.mem _ from rfl, hmask2_eq v hv]; exact hinv.mask_mono v hv,
            hsbuf2, hchain2, hvis2_le, hcur2_le, hused2_le, hdead2_le, hfr2⟩,
          ?_, by omega, le_rfl⟩
        intro r hr
        by_cases h13 : r = 13
        · subst h13; simp [st4]
        · by_cases h14 : r = 14
          · subst h14; rfl
          · have hr3 : st4.regs r = st1.regs r := by
              simp [st4, st3, Function.update_of_ne h13, Function.update_of_ne (by omega : r ≠ 22), hregs2 r hr]
            rw [hr3]
            by_cases h15 : r = 15
            · subst h15; simp [st1]
            · simp only [st1, Function.update_of_ne h15]
              have := hregs r hr; interval_cases r <;> first | exact this | omega
      · rw [hres_eq]
        have hbfs_pos : 1 ≤ bfs.cost := hbfs_inv.2.2.2.1
        simp only [bfsProgCost, Expr.size, argsSize, List.length_cons, List.length_nil] at hc1 hc2 hcB ⊢
        omega
    | true =>
      have hhit1 : hitVal = 1 := by simp [hitVal, hhit]
      set dfsGen1 := dfsGen + 1
      have hr3_of_le20 : ∀ r ≤ 20, st3.regs r =
          if r = 15 then bfsGen1 else st0.regs r := by
        intro r hr
        simp only [st3, Function.update_of_ne (by omega : r ≠ 22), hregs2 r hr, st1]
        by_cases h15 : r = 15
        · subst h15; simp
        · simp [h15]
      obtain ⟨st9, cT, outHeap, outHead, outTail, hrunT, hinv9, hregs9, hcT⟩ :=
        spPhaseHitStep_triple (p := p) (st3 := st3) hdfs_proc hV0X hadj_X hcsr0 hm2 hdisj hdfs_cfg0 hstop0
          hinv hregs hbfs_out hmask2 hmask2_eq hsbuf2 hchain2 hvis2_le hcur2_le hused2_le hdead2_le
          hfr2 hr3_of_le20 ω
      set dfs := dfsBlock adj V S T bfs.dist bfs.maxReached
      have hdfs_inv := dfsBlock_inv adj V S T bfs.dist bfs.maxReached
      -- Invoke IH on st9
      obtain ⟨stF, cIH, hrunIH, hpostIH, hcIH⟩ :=
        ih (V \ dfs.used) (dfs.paths ++ acc) outHeap outHead outTail bfsGen1 dfsGen1 st9 hinv9 hregs9 ω
      have hcond : Runs w p ω
          (.cond (.reg 22)
            (seqStmts
              [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
              , .assign 16 (.bin .add (.reg 16) (.const 1))
              , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
              , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
              , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
              , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
              , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
              , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
              , .store (.bin .add (.reg 2) (.const 23)) (.reg 19)
              , .call 24 bDfs [.reg 2]
              , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
              , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
              , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
              , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
              , .assign 20 (.bin .add (.reg 20) (.reg 25))
              , spIsolateLoopStmt
              , spFilterInPlaceStmt
              , .assign 14 (.reg 27)
              , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
            (.assign 13 (.const 0)))
          st3 .normal st9 ((Expr.reg 22).size + cT + 1) :=
        runs_cond_iff.mpr ⟨1, cT, by simp [Expr.eval, st3, hhit1], by simpa using hrunT, rfl⟩
      have hbody_tail : Runs w p ω
          (seqStmts
            [ .call 21 bBfs [.reg 1]
            , .assign 22 (.load (.bin .add (.reg 1) (.const 19)))
            , .cond (.reg 22)
                (seqStmts
                  [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
                  , .assign 16 (.bin .add (.reg 16) (.const 1))
                  , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
                  , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
                  , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
                  , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
                  , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
                  , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
                  , .store (.bin .add (.reg 2) (.const 23)) (.reg 19)
                  , .call 24 bDfs [.reg 2]
                  , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
                  , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
                  , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
                  , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
                  , .assign 20 (.bin .add (.reg 20) (.reg 25))
                  , spIsolateLoopStmt
                  , spFilterInPlaceStmt
                  , .assign 14 (.reg 27)
                  , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
                (.assign 13 (.const 0)) ])
          st1 .normal st9 (c2 + (5 + ((Expr.reg 22).size + cT + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hrun3, hcond, rfl⟩), rfl⟩)
      obtain ⟨cB, hrunB, hcB⟩ := runs_seqStmts_append (by simp) (by simp) hrun1 hbody_tail
      have hrun_tot : Runs w p ω (spPhaseLoopStmt bBfs bDfs) st0 .normal stF
          ((Expr.reg 13).size + cB + cIH + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨rem + 1, st9, cB, cIH, hev_guard, by omega, hrunB, hrunIH, rfl⟩))
      have hadd := shortPathBlockLoop_cost_add adj S T spCfg.d rem (V \ dfs.used) (dfs.paths ++ acc) 0
        (0 + bfs.cost + 1 + dfs.cost)
      simp only [Nat.zero_add] at hadd
      have hres_paths : (shortPathBlockLoop adj S T spCfg.d (rem + 1) V acc 0).paths =
          (shortPathBlockLoop adj S T spCfg.d rem (V \ dfs.used) (dfs.paths ++ acc) 0).paths := by
        dsimp only [shortPathBlockLoop]; rw [show bfsLayers adj V S spCfg.d T = bfs from rfl, hhit]
        simpa [dfs] using hadd.1
      have hres_rem : (shortPathBlockLoop adj S T spCfg.d (rem + 1) V acc 0).remVerts =
          (shortPathBlockLoop adj S T spCfg.d rem (V \ dfs.used) (dfs.paths ++ acc) 0).remVerts := by
        dsimp only [shortPathBlockLoop]; rw [show bfsLayers adj V S spCfg.d T = bfs from rfl, hhit]
        simpa [dfs] using hadd.2.1
      have hres_cost : (shortPathBlockLoop adj S T spCfg.d (rem + 1) V acc 0).cost =
          (shortPathBlockLoop adj S T spCfg.d rem (V \ dfs.used) (dfs.paths ++ acc) 0).cost +
            (bfs.cost + 1 + dfs.cost) := by
        dsimp only [shortPathBlockLoop]; rw [show bfsLayers adj V S spCfg.d T = bfs from rfl, hhit]
        simpa [dfs] using hadd.2.2
      refine ⟨stF, _, hrun_tot, ?_, ?_⟩
      · rcases hpostIH with ⟨hp', hd', tl', bg', dg', hinvF, hregsF, hbg_le, hdg_le⟩
        refine ⟨hp', hd', tl', bg', dg', ?_, ?_, by omega, by omega⟩
        · rw [hres_rem, hres_paths]; exact hinvF
        · rw [hres_paths]; exact hregsF
      · rw [hres_cost]
        have hbfs_pos : 1 ≤ bfs.cost := hbfs_inv.2.2.2.1
        have hSV_le_bfs : (S ∩ V).card ≤ bfs.cost := hbfs_inv.2.2.2.2.1 hhit
        have hused_le_dfs : dfs.used.card ≤ dfs.cost := hdfs_inv.2.1
        simp only [bfsProgCost, dfsProgCost, Expr.size, argsSize, List.length_cons, List.length_nil] at hc1 hc2 hcT hcB hcIH ⊢
        omega

/-! ## 3. Full Procedure Triple and Contract (`shortPathBlock_triple`, `shortPathBlock_meetsContract`) -/

theorem shortPathBlock_triple {w : ℕ} {p : Program} {bBfs bDfs : ℕ}
    {X V S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg} {spCfgAddr m2 : ℕ}
    {st0 : State}
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hVX : V ⊆ X)
    (hSX : S ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hsp_cfg : SpCfgAt st0.mem spCfgAddr spCfg)
    (hbfs_cfg : BfsCfgAt st0.mem spCfg.bfsCfgAddr bfsCfg)
    (hdfs_cfg : DfsCfgAt st0.mem spCfg.dfsCfgAddr dfsCfg)
    (hcsr : AdjCsrAt st0.mem bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hmask : ∀ v < X.card, st0.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : ∀ v < X.card, st0.mem (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T)
    (hsrc_list : ListAt st0.mem spCfg.srcInPtr ((S.sort (· ≤ ·)).map (locOf X)))
    (hsrc_len : spCfg.srcInLen = S.card)
    (hvis0 : ∀ v < X.card, st0.mem (bfsCfg.visStampAddr + v) ≤ spCfg.bfsGenIn)
    (hcur0 : ∀ v < X.card, st0.mem (dfsCfg.curStampAddr + v) ≤ spCfg.dfsGenIn)
    (hused0 : ∀ v < X.card, st0.mem (dfsCfg.usedStampAddr + v) ≤ spCfg.dfsGenIn)
    (hdead0 : ∀ v < X.card, st0.mem (dfsCfg.deadStampAddr + v) ≤ spCfg.dfsGenIn)
    (hr0 : st0.regs 0 = spCfgAddr) :
    let res := shortPathBlock adj V S T spCfg.d
    Triple w p (fun st => st = st0) (shortPathBlockProc bBfs bDfs)
      (retPost fun v st' =>
        v = res.paths.length ∧
        SpOutAt st'.mem X V spCfg bfsCfg dfsCfg spCfgAddr res ∧
        (∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st'.mem a = st0.mem a) ∧
        (∀ v < X.card, st'.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v) ∨
          st'.mem (spCfg.maskArrAddr + v) = spCfg.maskBadVal))
      (fun _ => spProgCost (shortPathBlock adj V S T spCfg.d).cost (S \ V).card) := by
  have hw_sp := hdisj.w_sp
  have hw_d := hdisj.w_d
  have hw_bgen := hdisj.w_bgen
  have hw_dgen := hdisj.w_dgen
  have hw_hp10 := hdisj.w_hp10
  have hw_mask : spCfg.maskArrAddr + X.card + 5 < 2 ^ w := by
    have := hdisj.dfs_disj.w_mask; dsimp only at this; rw [hdisj.dfs_mask] at this; exact this
  have hw_mb : spCfg.maskBadVal < 2 ^ w := by
    have := hdisj.dfs_disj.w_mb; dsimp only at this; rw [hdisj.dfs_bad] at this; exact this
  have hw_sbuf : spCfg.sBufAddr + X.card + 5 < 2 ^ w := by
    have := hdisj.dfs_disj.w_src; dsimp only at this; rw [hdisj.dfs_srcPtr] at this; exact this
  have hw4 := hdisj.dfs_disj.w4
  dsimp only
  wram_enter; subst st
  unfold shortPathBlockProc; dsimp only [seqStmts]
  refine runs_seq_triple_le (spLoadCfg_triple (p := p) hsp_cfg hr0 hw_sp) rfl (fun st1 hst1 => ?_)
  rcases hst1 with ⟨hmem1, hregs1⟩
  have h1_3 : st1.regs 3 = spCfg.maskArrAddr := hregs1 3 (by decide)
  have h1_4 : st1.regs 4 = spCfg.maskBadVal := hregs1 4 (by decide)
  have h1_6 : st1.regs 6 = spCfg.sBufAddr := hregs1 6 (by decide)
  have h1_7 : st1.regs 7 = spCfg.srcInPtr := hregs1 7 (by decide)
  have h1_8 : st1.regs 8 = spCfg.srcInLen := hregs1 8 (by decide)
  refine runs_seq_triple_le
    (spInitFilter_triple (p := p) (st0 := st1) hSX (hmem1 ▸ hsrc_list) hsrc_len (hmem1 ▸ hmask)
      hdisj.mask_sbuf hdisj.sbuf_src hw_mask hw_sbuf hdisj.w_srcIn hw_mb hw4
      h1_3 h1_4 h1_6 h1_7 h1_8) rfl (fun st2 hst2 => ?_)
  rcases hst2 with ⟨hregs2, h2_14, hsbuf2, hfr2⟩
  have h2_9 : st2.regs 9 = spCfg.d := (hregs2 9 (by decide)).trans (hregs1 9 (by decide))
  have h2_10 : st2.regs 10 = spCfg.bfsGenIn := (hregs2 10 (by decide)).trans (hregs1 10 (by decide))
  have h2_11 : st2.regs 11 = spCfg.dfsGenIn := (hregs2 11 (by decide)).trans (hregs1 11 (by decide))
  have h2_12 : st2.regs 12 = spCfg.heapIn := (hregs2 12 (by decide)).trans (hregs1 12 (by decide))
  refine runs_seq_assign_le (v := spCfg.d + 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := spCfg.bfsGenIn) (by eval_expr) ?_
  refine runs_seq_assign_le (v := spCfg.dfsGenIn) (by eval_expr) ?_
  refine runs_seq_assign_le (v := spCfg.heapIn) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st3 : State :=
    { mem := st2.mem
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update st2.regs 13 (spCfg.d + 1))
          15 spCfg.bfsGenIn) 16 spCfg.dfsGenIn) 17 spCfg.heapIn) 18 0) 19 0) 20 0
      pos := st2.pos }
  have hinv3 : SpLoopInv st3.mem st0.mem X V S spCfg bfsCfg dfsCfg spCfgAddr
      (spCfg.d + 1) V [] spCfg.heapIn 0 0 spCfg.bfsGenIn spCfg.dfsGenIn := by
    refine ⟨Finset.Subset.refl _, Nat.zero_le _, le_rfl, by simp, le_rfl, le_rfl, le_rfl, le_rfl,
      ?_, ?_, hsbuf2, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.mask_sbuf with x | x <;> omega), hmem1]
      exact hmask v hv
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.mask_sbuf with x | x <;> omega), hmem1]
      exact Or.inl rfl
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.sbuf_vis with x | x <;> omega), hmem1]
      exact hvis0 v hv
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.sbuf_cs with x | x <;> omega), hmem1]
      exact hcur0 v hv
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.sbuf_us with x | x <;> omega), hmem1]
      exact hused0 v hv
    · intro v hv
      rw [show st3.mem = st2.mem from rfl, hfr2 _ (by rcases hdisj.sbuf_ds with x | x <;> omega), hmem1]
      exact hdead0 v hv
    · intro a ha
      rw [show st3.mem = st2.mem from rfl,
        hfr2 a (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))),
        hmem1]
  have hregs3 : SpLoopRegs st3.regs spCfg spCfgAddr
      (spCfg.d + 1) (S ∩ V).card spCfg.bfsGenIn spCfg.dfsGenIn spCfg.heapIn 0 0 0 := by
    intro r hr
    by_cases h20 : r = 20; · subst h20; simp [st3]
    by_cases h19 : r = 19; · subst h19; simp [st3]
    by_cases h18 : r = 18; · subst h18; simp [st3]
    by_cases h17 : r = 17; · subst h17; simp [st3]
    by_cases h16 : r = 16; · subst h16; simp [st3]
    by_cases h15 : r = 15; · subst h15; simp [st3]
    by_cases h13 : r = 13; · subst h13; simp [st3]
    simp only [st3, Function.update_of_ne h20, Function.update_of_ne h19, Function.update_of_ne h18,
      Function.update_of_ne h17, Function.update_of_ne h16, Function.update_of_ne h15,
      Function.update_of_ne h13]
    by_cases h14 : r = 14
    · subst h14; exact h2_14
    · have := (hregs2 r (by omega)).trans (hregs1 r (by omega))
      interval_cases r <;> first | exact this | omega
  obtain ⟨st4, c4, hrun4, hpost4, hc4⟩ :=
    spPhaseLoop_triple (p := p) hbfs_proc hdfs_proc hVX hadj_X hcsr hm2 hdisj hbfs_cfg hdfs_cfg hstop
      (spCfg.d + 1) V [] spCfg.heapIn 0 0 spCfg.bfsGenIn spCfg.dfsGenIn st3 hinv3 hregs3 ω
  rcases hpost4 with ⟨hp4, hd4, tl4, bg4, dg4, hinv4, hregs4, _, _⟩
  have hr4_0 : st4.regs 0 = spCfgAddr := hregs4 0 (by decide)
  obtain ⟨o5, st5, c5, hrun5, hpost5, hc5⟩ := spWriteRet_triple (p := p) (st0 := st4) hr4_0 hw_sp st4 ω rfl
  cases o5 with
  | normal => exact hpost5.elim
  | returned v =>
  rcases hpost5 with ⟨hv, h12, h13, h14, h15, h16, h17, hfr5⟩
  set res := shortPathBlock adj V S T spCfg.d
  have hr4_15 : st4.regs 15 = bg4 := hregs4 15 (by decide)
  have hr4_16 : st4.regs 16 = dg4 := hregs4 16 (by decide)
  have hr4_17 : st4.regs 17 = hp4 := hregs4 17 (by decide)
  have hr4_18 : st4.regs 18 = hd4 := hregs4 18 (by decide)
  have hr4_19 : st4.regs 19 = tl4 := hregs4 19 (by decide)
  have hr4_20 : st4.regs 20 = res.paths.length := hregs4 20 (by decide)
  refine ⟨.returned v, st5, c4 + c5 + 1, runs_seq_iff.mpr (Or.inr ⟨st4, c4, c5, hrun4, hrun5, rfl⟩), ?_, ?_⟩
  · dsimp only [retPost]
    refine ⟨hv.trans hr4_20, ?_, ?_, ?_⟩
    · refine ⟨h15.trans hr4_20, by rw [h14, hr4_17]; exact hinv4.heap_lo,
        by rw [h14, hr4_17]; exact hinv4.heap_hi,
        by rw [h16, hr4_15]; exact hinv4.bgen_lo, by rw [h16, hr4_15]; have := hinv4.bgen_hi; omega,
        by rw [h17, hr4_16]; exact hinv4.dgen_lo, by rw [h17, hr4_16]; have := hinv4.dgen_hi; omega,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h12, h13, h14, hr4_18, hr4_19, hr4_17]
        exact hinv4.chain.congr fun k hk1 hk2 => hfr5 k (by
          have hhi : hp4 ≤ spCfg.heapIn + 5 * X.card := by
            have h1 := hinv4.heap_hi
            have h2 : (V \ res.remVerts).card ≤ X.card :=
              Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset hVX)
            change hp4 ≤ spCfg.heapIn + 5 * (V \ res.remVerts).card at h1
            omega
          rcases hdisj.sp_out_hp10 with x | x <;> omega)
      · intro u hu
        rw [hfr5 _ (by rcases hdisj.mask_sp with x | x <;> omega)]
        exact hinv4.mask_ok u hu
      · intro u hu
        rw [hfr5 _ (by rcases hdisj.sp_vis with x | x <;> omega), h16, hr4_15]
        exact hinv4.vis_le u hu
      · intro u hu
        rw [hfr5 _ (by rcases hdisj.sp_cs with x | x <;> omega), h17, hr4_16]
        exact hinv4.cur_le u hu
      · intro u hu
        rw [hfr5 _ (by rcases hdisj.sp_us with x | x <;> omega), h17, hr4_16]
        exact hinv4.used_le u hu
      · intro u hu
        rw [hfr5 _ (by rcases hdisj.sp_ds with x | x <;> omega), h17, hr4_16]
        exact hinv4.dead_le u hu
    · intro a ha
      rw [hfr5 a (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))))]
      exact hinv4.frame a ha
    · intro u hu
      rw [hfr5 _ (by rcases hdisj.mask_sp with x | x <;> omega)]
      exact hinv4.mask_mono u hu
  · have hS_split : S.card = (S ∩ V).card + (S \ V).card := (Finset.card_inter_add_card_sdiff S V).symm
    have hSV_le : (S ∩ V).card ≤ res.cost := shortPathBlock_inter_card_le_cost adj V S T spCfg.d
    have hres_cost : (shortPathBlockLoop adj S T spCfg.d (spCfg.d + 1) V [] 0).cost = res.cost := rfl
    rw [hres_cost] at hc4
    simp only [spProgCost, Expr.size] at hc4 hc5 ⊢
    omega

/-- Contract for `shortPathBlockProc` on argument `[spCfgAddr]`. -/
@[expose] def shortPathBlockContract (w : ℕ) (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ))
    (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg) (m2 : ℕ) : Contract where
  pre args mem :=
    args.length = 1 ∧
    let spCfgAddr := args.getD 0 0
    V ⊆ X ∧
    S ⊆ X ∧
    (∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X) ∧
    SpCfgAt mem spCfgAddr spCfg ∧
    BfsCfgAt mem spCfg.bfsCfgAddr bfsCfg ∧
    DfsCfgAt mem spCfg.dfsCfgAddr dfsCfg ∧
    AdjCsrAt mem bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj ∧
    adjCsrOff X adj X.card ≤ m2 ∧
    SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr ∧
    (∀ v < X.card, mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V) ∧
    (∀ v < X.card, mem (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T) ∧
    ListAt mem spCfg.srcInPtr ((S.sort (· ≤ ·)).map (locOf X)) ∧
    spCfg.srcInLen = S.card ∧
    (∀ v < X.card, mem (bfsCfg.visStampAddr + v) ≤ spCfg.bfsGenIn) ∧
    (∀ v < X.card, mem (dfsCfg.curStampAddr + v) ≤ spCfg.dfsGenIn) ∧
    (∀ v < X.card, mem (dfsCfg.usedStampAddr + v) ≤ spCfg.dfsGenIn) ∧
    (∀ v < X.card, mem (dfsCfg.deadStampAddr + v) ≤ spCfg.dfsGenIn)
  post args mem v mem' :=
    let spCfgAddr := args.getD 0 0
    let res := shortPathBlock adj V S T spCfg.d
    v = res.paths.length ∧
    SpOutAt mem' X V spCfg bfsCfg dfsCfg spCfgAddr res ∧
    (∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → mem' a = mem a) ∧
    (∀ v < X.card, mem' (spCfg.maskArrAddr + v) = mem (spCfg.maskArrAddr + v) ∨
      mem' (spCfg.maskArrAddr + v) = spCfg.maskBadVal)
  cost _ _ := spProgCost (shortPathBlock adj V S T spCfg.d).cost (S \ V).card

/-- `shortPathBlockProc` meets `shortPathBlockContract` deterministically. -/
theorem shortPathBlock_meetsContract {w : ℕ} {p : Program} {idx bBfs bDfs : ℕ}
    (hproc : p.procs[idx]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (X V S T : Finset ℕ) (adj : ℕ → List (ℕ × ℕ))
    (spCfg : SpCfg) (bfsCfg : BfsCfg) (dfsCfg : DfsCfg) (m2 : ℕ) :
    MeetsContract w p idx (shortPathBlockContract w X V S T adj spCfg bfsCfg dfsCfg m2) := by
  intro args mem pos ω _hwords hpre
  rcases hpre with ⟨hlen, hVX, hSX, hadj_X, hsp_cfg, hbfs_cfg, hdfs_cfg, hcsr, hm2, hdisj,
    hmask, hstop, hsrc_list, hsrc_len, hvis0, hcur0, hused0, hdead0⟩
  have htr := shortPathBlock_triple (w := w) (p := p) (st0 := startState args mem pos)
    hbfs_proc hdfs_proc hVX hSX hadj_X hsp_cfg hbfs_cfg hdfs_cfg hcsr hm2 hdisj
    hmask hstop hsrc_list hsrc_len hvis0 hcur0 hused0 hdead0 rfl
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := htr (startState args mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    exact ⟨shortPathBlockProc bBfs bDfs, hproc, .returned v, st', c, hrun, hpost, hc⟩

end MinCostFlow.ExpanderDecomp
