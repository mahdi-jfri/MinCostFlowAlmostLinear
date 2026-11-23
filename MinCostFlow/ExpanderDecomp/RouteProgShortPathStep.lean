module

public import MinCostFlow.ExpanderDecomp.RouteProgShortPathInv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Short-Path Blocking Hit-Branch Step (`RouteProgShortPathStep`)

Verifies the `hitStop = true` branch of `spPhaseLoopStmt`: sets up `DfsCfg`, invokes
`dfsBlockProc`, updates path-chain accumulators, isolates accepted path vertices in `maskArr`,
filters `sBuf` in place, and decrements the remaining-phase counter, preserving `SpLoopInv` and
`SpLoopRegs`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma spPhaseHitStep_triple {w : ℕ} {p : Program} {bDfs : ℕ}
    {X V0 V S T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {spCfg : SpCfg} {bfsCfg : BfsCfg} {dfsCfg : DfsCfg} {spCfgAddr m2 : ℕ}
    {mem0 : ℕ → ℕ} {rem : ℕ} {acc : List ((ℕ × ℕ) × List ℕ)}
    {heapPtr head tail bfsGen dfsGen : ℕ} {st0 st3 : State}
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hV0X : V0 ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcsr0 : AdjCsrAt mem0 bfsCfg.offAddr bfsCfg.nbAddr dfsCfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : SpDisj w X.card m2 spCfg bfsCfg dfsCfg spCfgAddr)
    (hdfs_cfg0 : DfsCfgAt mem0 spCfg.dfsCfgAddr dfsCfg)
    (hstop0 : ∀ v < X.card, mem0 (bfsCfg.stopArrAddr + v) = bfsCfg.stopVal ↔ origOf X v ∈ T)
    (hinv : SpLoopInv st0.mem mem0 X V0 S spCfg bfsCfg dfsCfg spCfgAddr
      (rem + 1) V acc heapPtr head tail bfsGen dfsGen)
    (hregs : SpLoopRegs st0.regs spCfg spCfgAddr
      (rem + 1) (S ∩ V).card bfsGen dfsGen heapPtr head tail acc.length)
    (hbfs_out : BfsOutAt st3.mem X
      ({ bfsCfg with bfsGen := bfsGen + 1, initLen := (S ∩ V).card })
      spCfg.bfsCfgAddr (bfsLayers adj V S spCfg.d T))
    (hmask2 : ∀ v < X.card, st3.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V)
    (hmask2_eq : ∀ v < X.card, st3.mem (spCfg.maskArrAddr + v) = st0.mem (spCfg.maskArrAddr + v))
    (hsbuf2 : ListAt st3.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)))
    (hchain2 : PathChainAt st3.mem X spCfg.heapIn heapPtr head tail acc)
    (hvis2_le : ∀ v < X.card, st3.mem (bfsCfg.visStampAddr + v) ≤ bfsGen + 1)
    (hcur2_le : ∀ v < X.card, st3.mem (dfsCfg.curStampAddr + v) ≤ dfsGen)
    (hused2_le : ∀ v < X.card, st3.mem (dfsCfg.usedStampAddr + v) ≤ dfsGen)
    (hdead2_le : ∀ v < X.card, st3.mem (dfsCfg.deadStampAddr + v) ≤ dfsGen)
    (hfr2 : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st3.mem a = mem0 a)
    (hr3_of_le20 : ∀ r ≤ 20, st3.regs r = if r = 15 then bfsGen + 1 else st0.regs r)
    (ω : ℕ → Bool) :
    let bfs := bfsLayers adj V S spCfg.d T
    let dfs := dfsBlock adj V S T bfs.dist bfs.maxReached
    ∃ st9 cT outHeap outHead outTail,
      Runs w p ω
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
        st3 .normal st9 cT ∧
      SpLoopInv st9.mem mem0 X V0 S spCfg bfsCfg dfsCfg spCfgAddr
        rem (V \ dfs.used) (dfs.paths ++ acc) outHeap outHead outTail (bfsGen + 1) (dfsGen + 1) ∧
      SpLoopRegs st9.regs spCfg spCfgAddr
        rem (S ∩ (V \ dfs.used)).card (bfsGen + 1) (dfsGen + 1) outHeap outHead outTail (dfs.paths ++ acc).length ∧
      cT ≤ dfsProgCost dfs.cost + 40 * dfs.used.card + 45 * (S ∩ V).card + 175 := by
  dsimp only
  have hVX : V ⊆ X := Finset.Subset.trans hinv.V_sub hV0X
  have hSV_le_X : (S ∩ V).card ≤ X.card :=
    Finset.card_le_card (Finset.Subset.trans Finset.inter_subset_right hVX)
  have hV0V_le_X : (V0 \ V).card ≤ X.card :=
    Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset hV0X)
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
  have hr13 : st0.regs 13 = rem + 1 := hregs 13 (by decide)
  set bfsGen1 := bfsGen + 1
  set bfs := bfsLayers adj V S spCfg.d T
  have hbfs_inv := bfsLayers_inv adj V S spCfg.d T
  -- Step 4: DFS setup (load bfsMaxR, dfsGen1 := dfsGen + 1, 7 stores into dfsCfg)
  set dfsGen1 := dfsGen + 1
  set dfsCfg1 : DfsCfg :=
    { dfsCfg with
      bfsGen := bfsGen1
      dfsGen := dfsGen1
      targetDepth := bfs.maxReached
      srcLen := (S ∩ V).card
      heapIn := heapPtr
      inHead := head
      inTail := tail }
  have hmr_mem : st3.mem (spCfg.bfsCfgAddr + 18) = bfs.maxReached := hbfs_out.2.2.2.2.2.2.1
  have hmr_le : bfs.maxReached ≤ spCfg.d := hbfs_inv.2.2.1
  set mem4 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update st3.mem
        (spCfg.dfsCfgAddr + 8) bfsGen1)
        (spCfg.dfsCfgAddr + 17) dfsGen1)
        (spCfg.dfsCfgAddr + 18) bfs.maxReached)
        (spCfg.dfsCfgAddr + 20) (S ∩ V).card)
        (spCfg.dfsCfgAddr + 21) heapPtr)
        (spCfg.dfsCfgAddr + 22) head)
        (spCfg.dfsCfgAddr + 23) tail
  set st4 : State :=
    { mem := mem4
      regs := Function.update (Function.update st3.regs 23 bfs.maxReached) 16 dfsGen1
      pos := st3.pos }
  have hheap_lt_w : heapPtr < 2 ^ w := by have := hinv.heap_hi; omega
  have hhead_lt_w : head < 2 ^ w := by
    have := pathChainAt_head_le hinv.chain
    have := hinv.heap_hi; omega
  have htail_lt_w : tail < 2 ^ w := by
    have := pathChainAt_tail_le hinv.chain
    have := hinv.heap_hi; omega
  have hdfs_setup : ∃ c4,
      Runs w p ω
        (seqStmts
          [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
          , .assign 16 (.bin .add (.reg 16) (.const 1))
          , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
          , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
          , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
          , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
          , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
          , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
          , .store (.bin .add (.reg 2) (.const 23)) (.reg 19) ])
        st3 .normal st4 c4 ∧ c4 ≤ 70 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 23 (.load (.bin .add (.reg 1) (.const 18)))
            , .assign 16 (.bin .add (.reg 16) (.const 1))
            , .store (.bin .add (.reg 2) (.const 8)) (.reg 15)
            , .store (.bin .add (.reg 2) (.const 17)) (.reg 16)
            , .store (.bin .add (.reg 2) (.const 18)) (.reg 23)
            , .store (.bin .add (.reg 2) (.const 20)) (.reg 14)
            , .store (.bin .add (.reg 2) (.const 21)) (.reg 17)
            , .store (.bin .add (.reg 2) (.const 22)) (.reg 18)
            , .store (.bin .add (.reg 2) (.const 23)) (.reg 19) ])
          st3 o s c ∧ (o = .normal ∧ s = st4) ∧ 0 + c ≤ 70 := by
      dsimp only [seqStmts]
      have h3_1 : st3.regs 1 = spCfg.bfsCfgAddr := by rw [hr3_of_le20 1 (by decide)]; exact hregs 1 (by decide)
      have h3_2 : st3.regs 2 = spCfg.dfsCfgAddr := by rw [hr3_of_le20 2 (by decide)]; exact hregs 2 (by decide)
      have h3_14 : st3.regs 14 = (S ∩ V).card := by rw [hr3_of_le20 14 (by decide)]; exact hregs 14 (by decide)
      have h3_15 : st3.regs 15 = bfsGen1 := by rw [hr3_of_le20 15 (by decide)]; rfl
      have h3_16 : st3.regs 16 = dfsGen := by rw [hr3_of_le20 16 (by decide)]; exact hregs 16 (by decide)
      have h3_17 : st3.regs 17 = heapPtr := by rw [hr3_of_le20 17 (by decide)]; exact hregs 17 (by decide)
      have h3_18 : st3.regs 18 = head := by rw [hr3_of_le20 18 (by decide)]; exact hregs 18 (by decide)
      have h3_19 : st3.regs 19 = tail := by rw [hr3_of_le20 19 (by decide)]; exact hregs 19 (by decide)
      refine runs_seq_assign_le (v := bfs.maxReached) (by rw [← hmr_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := dfsGen1) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 8) (v := bfsGen1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 17) (v := dfsGen1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 18) (v := bfs.maxReached) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 20) (v := (S ∩ V).card) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 21) (v := heapPtr) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := spCfg.dfsCfgAddr + 22) (v := head) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := spCfg.dfsCfgAddr + 23) (v := tail) (by eval_expr) (by eval_expr)
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c4, hrun4, ⟨rfl, rfl⟩, hc4⟩
    exact ⟨c4, hrun4, by omega⟩
  rcases hdfs_setup with ⟨c4, hrun4, hc4⟩
  have hmem4_fr : ∀ a, (a < spCfg.dfsCfgAddr ∨ spCfg.dfsCfgAddr + 29 ≤ a) → st4.mem a = st3.mem a := by
    intro a ha
    simp only [st4, mem4,
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 23),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 22),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 21),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 20),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 18),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 17),
      Function.update_of_ne (by omega : a ≠ spCfg.dfsCfgAddr + 8)]
  have hfr4 : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st4.mem a = mem0 a := by
    intro a ha
    have hne : a ≠ spCfg.dfsCfgAddr + 23 ∧ a ≠ spCfg.dfsCfgAddr + 22 ∧ a ≠ spCfg.dfsCfgAddr + 21 ∧
        a ≠ spCfg.dfsCfgAddr + 20 ∧ a ≠ spCfg.dfsCfgAddr + 18 ∧ a ≠ spCfg.dfsCfgAddr + 17 ∧
        a ≠ spCfg.dfsCfgAddr + 8 := by
      refine ⟨fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h.symm)))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h.symm))))))),
        fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h.symm))))))⟩
    simp only [st4, mem4, Function.update_of_ne hne.1, Function.update_of_ne hne.2.1,
      Function.update_of_ne hne.2.2.1, Function.update_of_ne hne.2.2.2.1,
      Function.update_of_ne hne.2.2.2.2.1, Function.update_of_ne hne.2.2.2.2.2.1,
      Function.update_of_ne hne.2.2.2.2.2.2]
    exact hfr2 a ha
  -- Step 5: call bDfs [r2]
  have hdfs_cfg1 : DfsCfgAt st4.mem spCfg.dfsCfgAddr dfsCfg1 := by
    rcases hdfs_cfg0 with ⟨d0, d1, d2, d3, d4, d5, d6, d7, _, d9, d10, d11, d12, d13, d14,
      d15, d16, _, _, d19, _, _, _, _⟩
    have hst : ∀ i < 20, i ≠ 8 → i ≠ 17 → i ≠ 18 →
        st4.mem (spCfg.dfsCfgAddr + i) = mem0 (spCfg.dfsCfgAddr + i) :=
      fun i hi h8 h17 h18 => dfsCfg_static_of_spFrame hdisj hfr4 hi h8 h17 h18
    refine ⟨(hst 0 (by decide) (by decide) (by decide) (by decide)).trans d0,
      (hst 1 (by decide) (by decide) (by decide) (by decide)).trans d1,
      (hst 2 (by decide) (by decide) (by decide) (by decide)).trans d2,
      (hst 3 (by decide) (by decide) (by decide) (by decide)).trans d3,
      (hst 4 (by decide) (by decide) (by decide) (by decide)).trans d4,
      (hst 5 (by decide) (by decide) (by decide) (by decide)).trans d5,
      (hst 6 (by decide) (by decide) (by decide) (by decide)).trans d6,
      (hst 7 (by decide) (by decide) (by decide) (by decide)).trans d7,
      by simp [st4, mem4, dfsCfg1],
      (hst 9 (by decide) (by decide) (by decide) (by decide)).trans d9,
      (hst 10 (by decide) (by decide) (by decide) (by decide)).trans d10,
      (hst 11 (by decide) (by decide) (by decide) (by decide)).trans d11,
      (hst 12 (by decide) (by decide) (by decide) (by decide)).trans d12,
      (hst 13 (by decide) (by decide) (by decide) (by decide)).trans d13,
      (hst 14 (by decide) (by decide) (by decide) (by decide)).trans d14,
      (hst 15 (by decide) (by decide) (by decide) (by decide)).trans d15,
      (hst 16 (by decide) (by decide) (by decide) (by decide)).trans d16,
      by simp [st4, mem4, dfsCfg1], by simp [st4, mem4, dfsCfg1],
      (hst 19 (by decide) (by decide) (by decide) (by decide)).trans d19,
      by simp [st4, mem4, dfsCfg1], by simp [st4, mem4, dfsCfg1],
      by simp [st4, mem4, dfsCfg1], by simp [st4, mem4, dfsCfg1]⟩
  have hdfs_disj1 : DfsDisj w X.card m2 dfsCfg1 spCfg.dfsCfgAddr :=
    DfsDisj.of_sp hdisj hbfs_gen_le hdfs_gen_le hmr_le hSV_le_X hinv.heap_lo
      (by have := hinv.heap_hi; omega)
  have hacc_disj4 : ∀ a, spCfg.heapIn ≤ a ∧ a < heapPtr →
      ¬ DfsWriteSet X.card dfsCfg1 spCfg.dfsCfgAddr a := by
    intro a ⟨ha1, ha2⟩ hdw
    have hhi : heapPtr ≤ spCfg.heapIn + 5 * X.card := by have := hinv.heap_hi; omega
    dsimp only [DfsWriteSet, dfsCfg1] at hdw
    rcases hdw with c | c | c | c | c | c | c | c | c
    · rcases hdisj.cs_hp10 with x | x <;> omega
    · rcases hdisj.cur_hp10 with x | x <;> omega
    · rcases hdisj.us_hp10 with x | x <;> omega
    · rcases hdisj.ds_hp10 with x | x <;> omega
    · rcases hdisj.sv_hp10 with x | x <;> omega
    · rcases hdisj.se_hp10 with x | x <;> omega
    · rcases hdisj.ul_hp10 with x | x <;> omega
    · rcases hdisj.dco_hp10 with x | x <;> omega
    · omega
  have hcsr4 : AdjCsrAt st4.mem dfsCfg1.offAddr dfsCfg1.nbAddr dfsCfg1.edgeAddr X adj := by
    dsimp only [dfsCfg1]; rw [hdisj.dfs_off, hdisj.dfs_nb]
    exact adjCsrAt_of_spFrame hdisj hm2 hcsr0 hfr4
  have hstop4 : ∀ v < X.card, st4.mem (dfsCfg1.stopArrAddr + v) = dfsCfg1.stopVal ↔ origOf X v ∈ T := by
    dsimp only [dfsCfg1]; rw [hdisj.dfs_stop, hdisj.dfs_stopVal]
    exact stop_of_spFrame hdisj hstop0 hfr4
  have hmask4 : ∀ v < X.card, st4.mem (dfsCfg1.maskArrAddr + v) ≠ dfsCfg1.maskBadVal ↔ origOf X v ∈ V := by
    intro v hv
    dsimp only [dfsCfg1]; rw [hdisj.dfs_mask, hdisj.dfs_bad]
    rw [hmem4_fr _ (by rcases hdisj.mask_dcfg with x | x <;> omega)]
    exact hmask2 v hv
  have hdist4 : ∀ v < X.card,
      (st4.mem (dfsCfg1.visStampAddr + v) = dfsCfg1.bfsGen ∧
        bfs.dist (origOf X v) = some (st4.mem (dfsCfg1.distAddr + v))) ∨
      (st4.mem (dfsCfg1.visStampAddr + v) ≠ dfsCfg1.bfsGen ∧
        bfs.dist (origOf X v) = none) := by
    intro v hv
    dsimp only [dfsCfg1]; rw [hdisj.dfs_vis, hdisj.dfs_dist]
    rw [hmem4_fr _ (by rcases hdisj.dcfg_vis with x | x <;> omega),
        hmem4_fr _ (by rcases hdisj.dcfg_dist with x | x <;> omega)]
    by_cases hmem : origOf X v ∈ bfs.visited
    · left; exact ⟨(hbfs_out.2.2.1 v hv).mpr hmem, hbfs_out.2.2.2.1 v hv hmem⟩
    · right; exact ⟨fun h => hmem ((hbfs_out.2.2.1 v hv).mp h), hbfs_inv.1 _ hmem⟩
  have hchain4 : PathChainAt st4.mem X spCfg.heapIn heapPtr head tail acc :=
    hchain2.congr fun k hk1 hk2 => hmem4_fr k (by
      have hhi : heapPtr ≤ spCfg.heapIn + 5 * X.card := by have := hinv.heap_hi; omega
      rcases hdisj.dcfg_hp10 with x | x
      · rcases hdisj.dco_hp10 with y | y <;> omega
      · omega)
  have hsbuf4 : ListAt st4.mem dfsCfg1.srcPtr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) := by
    intro j hj
    have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
    dsimp only [dfsCfg1]; rw [hdisj.dfs_srcPtr]
    rw [hmem4_fr _ (by rcases hdisj.sbuf_dcfg with x | x <;> omega)]
    exact hsbuf2 j hj
  have hcs4 : ∀ v < X.card, st4.mem (dfsCfg1.curStampAddr + v) ≠ dfsCfg1.dfsGen := by
    intro v hv; dsimp only [dfsCfg1]
    rw [hmem4_fr _ (by rcases hdisj.dcfg_cs with x | x <;> omega)]
    have := hcur2_le v hv; omega
  have hus4 : ∀ v < X.card, st4.mem (dfsCfg1.usedStampAddr + v) ≠ dfsCfg1.dfsGen := by
    intro v hv; dsimp only [dfsCfg1]
    rw [hmem4_fr _ (by rcases hdisj.dcfg_us with x | x <;> omega)]
    have := hused2_le v hv; omega
  have hds4 : ∀ v < X.card, st4.mem (dfsCfg1.deadStampAddr + v) ≠ dfsCfg1.dfsGen := by
    intro v hv; dsimp only [dfsCfg1]
    rw [hmem4_fr _ (by rcases hdisj.dcfg_ds with x | x <;> omega)]
    have := hdead2_le v hv; omega
  have hdfs_pre : (dfsBlockContract w X V (S ∩ V) T adj bfs.dist dfsCfg1 m2 spCfg.heapIn acc).pre
      [spCfg.dfsCfgAddr] st4.mem := by
    dsimp only [dfsBlockContract, List.getD]
    exact ⟨rfl, hVX, Finset.inter_subset_right, hadj_X, hdfs_cfg1, hcsr4, hm2, hdfs_disj1,
      hinv.heap_lo, hacc_disj4, hchain4, hmask4, hstop4, hdist4, hbfs_inv.2.1,
      hsbuf4, rfl, hcs4, hus4, hds4⟩
  have hdfs_mc := dfsBlock_meetsContract (w := w) hdfs_proc X V (S ∩ V) T adj bfs.dist dfsCfg1 m2 spCfg.heapIn acc
  have hdfs_args : evalArgs w st4 [.reg 2] = some [spCfg.dfsCfgAddr] := by
    have hr4_2 : st4.regs 2 = spCfg.dfsCfgAddr := by
      simp [st4, hr3_of_le20 2 (by decide), hregs 2 (by decide)]
    simp [evalArgs, Expr.eval, hr4_2]
  obtain ⟨st5, c5, v5, hrun5, hpost5, hr5_24, hr5_oth, hc5⟩ :=
    runs_call_of_meetsContract (r := 24) hdfs_mc hdfs_args
      (by intro v hv; simp at hv; subst hv; omega) hdfs_pre ω
  simp only [dfsBlockContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpost5 hc5
  have hdfs_eq : dfsBlock adj V (S ∩ V) T bfs.dist dfsCfg1.targetDepth =
      dfsBlock adj V S T bfs.dist bfs.maxReached := by
    dsimp only [dfsCfg1]; exact dfsBlock_inter adj V S T bfs.dist bfs.maxReached
  rw [hdfs_eq] at hpost5 hc5
  set dfs := dfsBlock adj V S T bfs.dist bfs.maxReached
  rcases hpost5 with ⟨hv5, hdfs_out, hcs5_m, hus5_m, hds5_m, hdfs_fr⟩
  dsimp only [dfsCfg1] at hcs5_m hus5_m hds5_m
  have hdfs_inv := dfsBlock_inv adj V S T bfs.dist bfs.maxReached
  have hdw_sub : ∀ a, DfsWriteSet X.card dfsCfg1 spCfg.dfsCfgAddr a →
      SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a := by
    intro a ha
    have hhi : heapPtr ≤ spCfg.heapIn + 5 * X.card := by have := hinv.heap_hi; omega
    dsimp only [DfsWriteSet, dfsCfg1] at ha
    rcases ha with c | c | c | c | c | c | c | c | c
    · exact Or.inr (Or.inl (Or.inl c))
    · exact Or.inr (Or.inl (Or.inr (Or.inl c)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl c))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl c)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))))))
    · exact Or.inr (Or.inr (Or.inl ⟨by have := hinv.heap_lo; omega, by omega⟩))
  have hfr5 : ∀ a, ¬ SpWriteSet X.card spCfg bfsCfg dfsCfg spCfgAddr a → st5.mem a = mem0 a := by
    intro a ha
    rw [hdfs_fr a (fun hdw => ha (hdw_sub a hdw))]
    exact hfr4 a ha
  -- Extract DFS outputs
  rcases hdfs_out with ⟨_, hd_pcnt, hd_hplo, hd_hphi, ⟨ul, hul_len, _, hul_sub, hul_cov, hul_at⟩,
    _, hchain5⟩
  dsimp only [dfsCfg1] at hd_hplo hd_hphi
  set outHead := st5.mem (spCfg.dfsCfgAddr + 26)
  set outTail := st5.mem (spCfg.dfsCfgAddr + 27)
  set outHeap := st5.mem (spCfg.dfsCfgAddr + 28)
  have hV2_card : (V0 \ (V \ dfs.used)).card = (V0 \ V).card + dfs.used.card :=
    card_sdiff_sdiff_eq hinv.V_sub hdfs_inv.1
  have hV2_le_X : (V0 \ (V \ dfs.used)).card ≤ X.card :=
    Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset hV0X)
  have houtHeap_hi : outHeap ≤ spCfg.heapIn + 5 * (V0 \ (V \ dfs.used)).card := by
    have := hinv.heap_hi; omega
  have houtHeap_lt_w : outHeap < 2 ^ w := by omega
  have houtHead_lt_w : outHead < 2 ^ w := by
    have := pathChainAt_head_le hchain5; omega
  have houtTail_lt_w : outTail < 2 ^ w := by
    have := pathChainAt_tail_le hchain5; omega
  have hpcnt_tot : acc.length + dfs.paths.length ≤ (V0 \ (V \ dfs.used)).card := by
    have h1 := hinv.paths_le
    have h2 : dfs.paths.length ≤ dfs.used.card := hdfs_inv.2.2
    omega
  -- Step 6: 5 post-DFS assigns (r25, r18, r19, r17, r20)
  set st6 : State :=
    { mem := st5.mem
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update st5.regs 25 dfs.paths.length) 18 outHead) 19 outTail) 17 outHeap)
        20 (acc.length + dfs.paths.length)
      pos := st5.pos }
  have hpost_dfs : ∃ c6,
      Runs w p ω
        (seqStmts
          [ .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
          , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
          , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
          , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
          , .assign 20 (.bin .add (.reg 20) (.reg 25)) ])
        st5 .normal st6 c6 ∧ c6 ≤ 40 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
            , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
            , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
            , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
            , .assign 20 (.bin .add (.reg 20) (.reg 25)) ])
          st5 o s c ∧ (o = .normal ∧ s = st6) ∧ 0 + c ≤ 40 := by
      dsimp only [seqStmts]
      have h5_2 : st5.regs 2 = spCfg.dfsCfgAddr := by
        rw [hr5_oth 2 (by decide)]; simp [st4, hr3_of_le20 2 (by decide), hregs 2 (by decide)]
      have h5_20 : st5.regs 20 = acc.length := by
        rw [hr5_oth 20 (by decide)]; simp [st4, hr3_of_le20 20 (by decide), hregs 20 (by decide)]
      refine runs_seq_assign_le (v := dfs.paths.length) (by rw [← hd_pcnt]; eval_expr) ?_
      refine runs_seq_assign_le (v := outHead) (by eval_expr) ?_
      refine runs_seq_assign_le (v := outTail) (by eval_expr) ?_
      refine runs_seq_assign_le (v := outHeap) (by eval_expr) ?_
      refine runs_assign_le (v := acc.length + dfs.paths.length) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c6, hrun6, ⟨rfl, rfl⟩, hc6⟩
    exact ⟨c6, hrun6, by omega⟩
  rcases hpost_dfs with ⟨c6, hrun6, hc6⟩
  -- Step 7: spIsolateLoopStmt
  have h6_3 : st6.regs 3 = spCfg.maskArrAddr := by
    simp [st6, Function.update_of_ne, hr5_oth 3 (by decide), st4, hr3_of_le20 3 (by decide), hregs 3 (by decide)]
  have h6_4 : st6.regs 4 = spCfg.maskBadVal := by
    simp [st6, Function.update_of_ne, hr5_oth 4 (by decide), st4, hr3_of_le20 4 (by decide), hregs 4 (by decide)]
  have h6_5 : st6.regs 5 = spCfg.usedListAddr := by
    simp [st6, Function.update_of_ne, hr5_oth 5 (by decide), st4, hr3_of_le20 5 (by decide), hregs 5 (by decide)]
  have h6_24 : st6.regs 24 = dfs.used.card := by
    simp [st6, Function.update_of_ne, hr5_24, hv5]
  obtain ⟨o7, st7, c7, hrun7, hpost7, hc7⟩ :=
    spIsolateLoop_triple (p := p) (st0 := st6) hul_len hul_sub hul_cov
      (by simpa [dfsCfg1, hdisj.dfs_usedList] using hul_at) hdisj.mask_ul
      hw_mask hw_ul hw_mb hw_nX hw4 h6_3 h6_4 h6_5 h6_24 st6 ω rfl
  cases o7 with
  | returned _ => exact hpost7.elim
  | normal =>
  rcases hpost7 with ⟨h7_regs, h7_set, h7_keep, h7_fr⟩
  have hmask7 : ∀ v < X.card,
      st7.mem (spCfg.maskArrAddr + v) ≠ spCfg.maskBadVal ↔ origOf X v ∈ V \ dfs.used := by
    intro v hv
    rw [Finset.mem_sdiff]
    by_cases hu : origOf X v ∈ dfs.used
    · rw [h7_set v hv hu]; simp [hu]
    · rw [h7_keep v hv hu]
      have hro_m := hdfs_disj1.ro_mask (spCfg.maskArrAddr + v)
        ⟨by dsimp only [dfsCfg1]; rw [hdisj.dfs_mask]; omega,
         by dsimp only [dfsCfg1]; rw [hdisj.dfs_mask]; omega⟩
      rw [hdfs_fr _ hro_m]
      have hm4 := hmask4 v hv
      dsimp only [dfsCfg1] at hm4; rw [hdisj.dfs_mask, hdisj.dfs_bad] at hm4
      rw [hm4]; simp [hu]
  -- Step 8: spFilterInPlaceStmt
  have hsbuf7 : ListAt st7.mem spCfg.sBufAddr (((S ∩ V).sort (· ≤ ·)).map (locOf X)) := by
    intro j hj
    have hj_lt : j < X.card := by simp only [List.length_map, Finset.length_sort] at hj; omega
    rw [h7_fr _ (by rcases hdisj.mask_sbuf with x | x <;> omega)]
    have hro_s := hdfs_disj1.ro_src (spCfg.sBufAddr + j)
      ⟨by dsimp only [dfsCfg1]; rw [hdisj.dfs_srcPtr]; omega,
       by dsimp only [dfsCfg1]; rw [hdisj.dfs_srcPtr]; simp only [List.length_map, Finset.length_sort] at hj; omega⟩
    rw [hdfs_fr _ hro_s]
    simpa [dfsCfg1, hdisj.dfs_srcPtr] using hsbuf4 j hj
  have h7_3 : st7.regs 3 = spCfg.maskArrAddr := (h7_regs 3 (by decide)).trans h6_3
  have h7_4 : st7.regs 4 = spCfg.maskBadVal := (h7_regs 4 (by decide)).trans h6_4
  have h7_6 : st7.regs 6 = spCfg.sBufAddr := (h7_regs 6 (by decide)).trans (by
    simp [st6, Function.update_of_ne, hr5_oth 6 (by decide), st4, hr3_of_le20 6 (by decide), hregs 6 (by decide)])
  have h7_14 : st7.regs 14 = (S ∩ V).card := (h7_regs 14 (by decide)).trans (by
    simp [st6, Function.update_of_ne, hr5_oth 14 (by decide), st4, hr3_of_le20 14 (by decide), hregs 14 (by decide)])
  obtain ⟨o8, st8, c8, hrun8, hpost8, hc8⟩ :=
    spFilterInPlace_triple (p := p) (st0 := st7) hVX Finset.sdiff_subset hsbuf7 hmask7
      hdisj.mask_sbuf hw_mask hw_sbuf hw_mb hw_nX hw4 h7_3 h7_4 h7_6 h7_14 st7 ω rfl
  cases o8 with
  | returned _ => exact hpost8.elim
  | normal =>
  rcases hpost8 with ⟨h8_regs, h8_27, hsbuf8, h8_fr⟩
  -- Step 9: r14 := r27; r13 := r13 - 1
  set st9 : State :=
    { mem := st8.mem
      regs := Function.update (Function.update st8.regs 14 (S ∩ (V \ dfs.used)).card) 13 rem
      pos := st8.pos }
  have htail_step : ∃ c9,
      Runs w p ω
        (seqStmts [ .assign 14 (.reg 27), .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
        st8 .normal st9 c9 ∧ c9 ≤ 10 := by
    have h0 : ∃ o s c,
        Runs w p ω
          (seqStmts [ .assign 14 (.reg 27), .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
          st8 o s c ∧ (o = .normal ∧ s = st9) ∧ 0 + c ≤ 10 := by
      dsimp only [seqStmts]
      have h8_13 : st8.regs 13 = rem + 1 := (h8_regs 13 (by decide)).trans ((h7_regs 13 (by decide)).trans (by
        simp [st6, Function.update_of_ne, hr5_oth 13 (by decide), st4, hr3_of_le20 13 (by decide), hr13]))
      have hrem_lt_w : rem + 1 < 2 ^ w := by have := hinv.bgen_hi; have := hinv.bgen_lo; omega
      have hremS_lt_w : (S ∩ (V \ dfs.used)).card < 2 ^ w := by
        have : (S ∩ (V \ dfs.used)).card ≤ X.card :=
          Finset.card_le_card (Finset.Subset.trans Finset.inter_subset_right (Finset.Subset.trans Finset.sdiff_subset hVX))
        omega
      refine runs_seq_assign_le (v := (S ∩ (V \ dfs.used)).card) (by eval_expr) ?_
      refine runs_assign_le (v := rem)
        (by simp [Expr.eval, BinOp.eval, h8_13, show 1 < 2 ^ w by omega]; omega) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0 with ⟨_, _, c9, hrun9, ⟨rfl, rfl⟩, hc9⟩
    exact ⟨c9, hrun9, by omega⟩
  rcases htail_step with ⟨c9, hrun9, hc9⟩
  -- Establish SpLoopInv and SpLoopRegs for st9
  have hinv9 : SpLoopInv st9.mem mem0 X V0 S spCfg bfsCfg dfsCfg spCfgAddr
      rem (V \ dfs.used) (dfs.paths ++ acc) outHeap outHead outTail bfsGen1 dfsGen1 := by
    refine ⟨Finset.Subset.trans Finset.sdiff_subset hinv.V_sub,
      by simp only [List.length_append]; omega,
      le_trans hinv.heap_lo hd_hplo, houtHeap_hi,
      by have := hinv.bgen_lo; omega, by have := hinv.bgen_hi; omega,
      by have := hinv.dgen_lo; omega, by have := hinv.dgen_hi; omega,
      ?_, ?_, hsbuf8, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [h8_fr _ (by rcases hdisj.mask_sbuf with x | x <;> omega)]
      exact hmask7 v hv
    · intro v hv
      rw [h8_fr _ (by rcases hdisj.mask_sbuf with x | x <;> omega)]
      by_cases hu : origOf X v ∈ dfs.used
      · exact Or.inr (h7_set v hv hu)
      · rw [h7_keep v hv hu]
        have hro_m := hdfs_disj1.ro_mask (spCfg.maskArrAddr + v)
          ⟨by dsimp only [dfsCfg1]; rw [hdisj.dfs_mask]; omega,
           by dsimp only [dfsCfg1]; rw [hdisj.dfs_mask]; omega⟩
        rw [show st6.mem _ = st5.mem _ from rfl, hdfs_fr _ hro_m,
            hmem4_fr _ (by rcases hdisj.mask_dcfg with x | x <;> omega),
            hmask2_eq v hv]
        exact hinv.mask_mono v hv
    · exact hchain5.congr fun k hk1 hk2 => by
        have hhi : outHeap ≤ spCfg.heapIn + 5 * X.card := by omega
        have hne_s : k < spCfg.sBufAddr ∨ spCfg.sBufAddr + X.card ≤ k := by
          rcases hdisj.sbuf_hp10 with x | x <;> omega
        have hne_m : k < spCfg.maskArrAddr ∨ spCfg.maskArrAddr + X.card ≤ k := by
          rcases hdisj.mask_hp10 with x | x <;> omega
        rw [show st9.mem k = st8.mem k from rfl, h8_fr k hne_s, h7_fr k hne_m]
    · intro v hv
      rw [show st9.mem _ = st8.mem _ from rfl,
          h8_fr _ (by rcases hdisj.sbuf_vis with x | x <;> omega),
          h7_fr _ (by rcases hdisj.mask_vis with x | x <;> omega)]
      have hro_v := hdfs_disj1.ro_vis (bfsCfg.visStampAddr + v)
        ⟨by dsimp only [dfsCfg1]; rw [hdisj.dfs_vis]; omega,
         by dsimp only [dfsCfg1]; rw [hdisj.dfs_vis]; omega⟩
      rw [show st6.mem _ = st5.mem _ from rfl, hdfs_fr _ hro_v,
          hmem4_fr _ (by rcases hdisj.dcfg_vis with x | x <;> omega)]
      exact hvis2_le v hv
    · intro v hv
      rw [show st9.mem _ = st8.mem _ from rfl,
          h8_fr _ (by rcases hdisj.sbuf_cs with x | x <;> omega),
          h7_fr _ (by rcases hdisj.mask_cs with x | x <;> omega)]
      rcases hcs5_m v hv with h | h
      · rw [show st6.mem _ = st5.mem _ from rfl, h, hmem4_fr _ (by rcases hdisj.dcfg_cs with x | x <;> omega)]
        have := hcur2_le v hv; omega
      · rw [show st6.mem _ = st5.mem _ from rfl, h]
    · intro v hv
      rw [show st9.mem _ = st8.mem _ from rfl,
          h8_fr _ (by rcases hdisj.sbuf_us with x | x <;> omega),
          h7_fr _ (by rcases hdisj.mask_us with x | x <;> omega)]
      rcases hus5_m v hv with h | h
      · rw [show st6.mem _ = st5.mem _ from rfl, h, hmem4_fr _ (by rcases hdisj.dcfg_us with x | x <;> omega)]
        have := hused2_le v hv; omega
      · rw [show st6.mem _ = st5.mem _ from rfl, h]
    · intro v hv
      rw [show st9.mem _ = st8.mem _ from rfl,
          h8_fr _ (by rcases hdisj.sbuf_ds with x | x <;> omega),
          h7_fr _ (by rcases hdisj.mask_ds with x | x <;> omega)]
      rcases hds5_m v hv with h | h
      · rw [show st6.mem _ = st5.mem _ from rfl, h, hmem4_fr _ (by rcases hdisj.dcfg_ds with x | x <;> omega)]
        have := hdead2_le v hv; omega
      · rw [show st6.mem _ = st5.mem _ from rfl, h]
    · intro a ha
      rw [show st9.mem a = st8.mem a from rfl,
          h8_fr a (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))),
          h7_fr a (by by_contra hc; push Not at hc; exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))))]
      exact hfr5 a ha
  have hregs9 : SpLoopRegs st9.regs spCfg spCfgAddr
      rem (S ∩ (V \ dfs.used)).card bfsGen1 dfsGen1 outHeap outHead outTail (dfs.paths ++ acc).length := by
    intro r hr
    by_cases h13 : r = 13
    · subst h13; simp [st9]
    · by_cases h14 : r = 14
      · subst h14; simp [st9]
      · simp only [st9, Function.update_of_ne h13, Function.update_of_ne h14]
        rw [h8_regs r (by omega), h7_regs r (by omega)]
        by_cases h20 : r = 20
        · subst h20; simp [st6, Nat.add_comm]
        · by_cases h17 : r = 17
          · subst h17; simp [st6]
          · by_cases h19 : r = 19
            · subst h19; simp [st6]
            · by_cases h18 : r = 18
              · subst h18; simp [st6]
              · simp only [st6, Function.update_of_ne h20, Function.update_of_ne h17,
                  Function.update_of_ne h19, Function.update_of_ne h18,
                  Function.update_of_ne (by omega : r ≠ 25)]
                rw [hr5_oth r (by omega)]
                by_cases h16 : r = 16
                · subst h16; simp [st4]
                · simp only [st4, Function.update_of_ne h16, Function.update_of_ne (by omega : r ≠ 23)]
                  rw [hr3_of_le20 r hr]
                  by_cases h15 : r = 15
                  · subst h15; simp
                  · simp only [h15, ↓reduceIte]
                    have := hregs r hr; interval_cases r <;> first | exact this | omega
  -- Compose st3 → st9
  have hrun_iso_tail : Runs w p ω
      (seqStmts [ spIsolateLoopStmt, spFilterInPlaceStmt,
        .assign 14 (.reg 27), .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
      st6 .normal st9 (c7 + (c8 + c9 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st7, c7, _, hrun7,
      runs_seq_iff.mpr (Or.inr ⟨st8, c8, c9, hrun8, hrun9, rfl⟩), rfl⟩)
  obtain ⟨c69, hrun69, hc69⟩ := runs_seqStmts_append (by simp) (by simp) hrun6 hrun_iso_tail
  have hrun59 : Runs w p ω
      (seqStmts
        [ .call 24 bDfs [.reg 2]
        , .assign 25 (.load (.bin .add (.reg 2) (.const 25)))
        , .assign 18 (.load (.bin .add (.reg 2) (.const 26)))
        , .assign 19 (.load (.bin .add (.reg 2) (.const 27)))
        , .assign 17 (.load (.bin .add (.reg 2) (.const 28)))
        , .assign 20 (.bin .add (.reg 20) (.reg 25))
        , spIsolateLoopStmt
        , spFilterInPlaceStmt
        , .assign 14 (.reg 27)
        , .assign 13 (.bin .sub (.reg 13) (.const 1)) ])
      st4 .normal st9 (c5 + c69 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st5, c5, c69, hrun5, hrun69, rfl⟩)
  obtain ⟨cT, hrunT, hcT⟩ := runs_seqStmts_append (by simp) (by simp) hrun4 hrun59
  refine ⟨st9, cT, outHeap, outHead, outTail, hrunT, hinv9, hregs9, ?_⟩
  simp only [Expr.size, argsSize, List.length_cons, List.length_nil] at hc4 hc5 hc6 hc7 hc8 hc9 hc69 hcT ⊢
  omega

end MinCostFlow.ExpanderDecomp
