module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Step — Short-Path Blocking Stage (`RouteProgBatchStepSp`)

Verifies Phases A–C of one iteration of `batchRouteLoopStmt`: configures `spCfg`/`bfsCfg`/`dfsCfg`,
invokes `shortPathBlockProc`, and loads its outputs into `stC`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma batch_not_spWriteSet_ws_hi {cfg : BatchCfg}
    {batchGen stopVal srcInPtr srcInLen bfsGen dfsGen heapIn pLo pHi a : ℕ}
    (hws_hp : DisjRange cfg.ws (batchScratchSize cfg.nX cfg.m2 cfg.k) pLo (pHi - pLo))
    (hhp_lo : pLo ≤ heapIn) (hhp_hi : heapIn + 10 * cfg.nX ≤ pHi)
    (ha1 : cfg.ws + 124 + cfg.nX ≤ a)
    (ha2 : a < cfg.ws + 124 + 2 * cfg.nX ∨
      (cfg.ws + 129 + 16 * cfg.nX + cfg.m2 + 3 * cfg.k ≤ a ∧
       a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k)) :
    ¬ SpWriteSet cfg.nX
      (mkBatchSpCfg cfg batchGen srcInPtr srcInLen bfsGen dfsGen heapIn)
      (mkBatchSpBfsCfg cfg batchGen stopVal)
      (mkBatchSpDfsCfg cfg batchGen stopVal) (wsSpCfg cfg.ws) a := by
  unfold DisjRange at hws_hp
  unfold batchScratchSize at hws_hp ha2
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by omega)
  intro hw
  simp only [SpWriteSet, BfsWriteSet, DfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg,
    wsSpCfg, wsBfsCfg, wsDfsCfg, wsIsoStamp, wsSBuf, wsVisStamp, wsDist, wsLayerOff, wsLayerData,
    wsTmpNxt, wsCurStamp, wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at hw
  rcases ha2 with ha2 | ⟨ha2a, ha2b⟩
  · rcases hw with (hw | hw | hw | hw | hw | hw) |
      (hw | hw | hw | hw | hw | hw | hw | hw | hw) | hw | (hw | hw) |
      (hw | hw | hw | hw) | hw | hw | hw <;> (try rcases hws_hp with x | x) <;> omega
  · rcases hw with (hw | hw | hw | hw | hw | hw) |
      (hw | hw | hw | hw | hw | hw | hw | hw | hw) | hw | (hw | hw) |
      (hw | hw | hw | hw) | hw | hw | hw <;> (try rcases hws_hp with x | x) <;> omega

private lemma dfsDisj_of_dyn {w nX m2 a : ℕ} {d : DfsCfg} {hd1 tl1 : ℕ}
    (h : DfsDisj w nX m2 d a) :
    DfsDisj w nX m2 ({ d with inHead := hd1, inTail := tl1 }) a := by
  cases h; constructor <;> assumption

private lemma spDisj_of_dyn {w nX m2 a : ℕ} {s : SpCfg} {b : BfsCfg} {d : DfsCfg}
    {bg1 il1 dbg1 dg1 td1 sl1 hp1 hd1 tl1 : ℕ}
    (h : SpDisj w nX m2 s b d a) :
    SpDisj w nX m2 s
      ({ b with bfsGen := bg1, initLen := il1 })
      ({ d with
          bfsGen := dbg1, dfsGen := dg1, targetDepth := td1, srcLen := sl1,
          heapIn := hp1, inHead := hd1, inTail := tl1 }) a := by
  have hd := dfsDisj_of_dyn (hd1 := hd1) (tl1 := tl1) h.dfs_disj
  cases h; constructor <;> assumption

private lemma batch_sp_r_ne {r : ℕ} (hr : r ≤ 17 ∨ r = 21 ∨ r = 29 ∨ r = 31 ∨ r = 32) :
    r ≠ 30 ∧ r ≠ 19 ∧ r ≠ 18 ∧ r ≠ 20 ∧ r ≠ 22 ∧ r ≠ 25 ∧ r ≠ 24 ∧ r ≠ 23 := by omega

private lemma batch_sub_of_spSetup {mem mem' : ℕ → ℕ} {cfg : BatchCfg} {hL : ℕ}
    (h : BatchSubCfgsInit mem cfg hL)
    (hmem_out : ∀ a, a ≠ wsSpCfg cfg.ws + 3 → a ≠ wsSpCfg cfg.ws + 6 →
      a ≠ wsSpCfg cfg.ws + 7 → a ≠ wsSpCfg cfg.ws + 9 →
      a ≠ wsSpCfg cfg.ws + 10 → a ≠ wsSpCfg cfg.ws + 11 →
      a ≠ wsBfsCfg cfg.ws + 3 → a ≠ wsBfsCfg cfg.ws + 6 →
      a ≠ wsDfsCfg cfg.ws + 4 → a ≠ wsDfsCfg cfg.ws + 6 → mem' a = mem a) :
    BatchSubCfgsInit mem' cfg hL :=
  h.of_agree fun off _ hnot =>
    hmem_out (cfg.ws + off)
      (by intro heq; simp only [wsSpCfg] at heq; have h3 : off = 3 := by { omega }; subst h3; exact hnot (by decide))
      (by intro heq; simp only [wsSpCfg] at heq; have h6 : off = 6 := by { omega }; subst h6; exact hnot (by decide))
      (by intro heq; simp only [wsSpCfg] at heq; have h7 : off = 7 := by { omega }; subst h7; exact hnot (by decide))
      (by intro heq; simp only [wsSpCfg] at heq; have h9 : off = 9 := by { omega }; subst h9; exact hnot (by decide))
      (by intro heq; simp only [wsSpCfg] at heq; have h10 : off = 10 := by { omega }; subst h10; exact hnot (by decide))
      (by intro heq; simp only [wsSpCfg] at heq; have h11 : off = 11 := by { omega }; subst h11; exact hnot (by decide))
      (by intro heq; simp only [wsBfsCfg] at heq; have h23 : off = 23 := by { omega }; subst h23; exact hnot (by decide))
      (by intro heq; simp only [wsBfsCfg] at heq; have h26 : off = 26 := by { omega }; subst h26; exact hnot (by decide))
      (by intro heq; simp only [wsDfsCfg] at heq; have h48 : off = 48 := by { omega }; subst h48; exact hnot (by decide))
      (by intro heq; simp only [wsDfsCfg] at heq; have h50 : off = 50 := by { omega }; subst h50; exact hnot (by decide))

/-- Phases A–C of one iteration of `batchRouteLoopStmt`: configure `spCfg/bfsCfg/dfsCfg`,
invoke `shortPathBlockProc`, and load output registers into `stC`. -/
lemma batchRouteStep_sp {w : ℕ} {p : Program} {bSp bBfs bDfs : ℕ}
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    {G : Graph} {X : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL : ℕ} {pairs curPairs : List (Finset ℕ × Finset ℕ)}
    {i : ℕ} {V M_acc : Finset ℕ} {A B : Finset ℕ}
    {accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ))}
    {bfsGen dfsGen pathHeap chunkHeap routed : ℕ} {mem0 : ℕ → ℕ} {st0 : State}
    (hnX : cfg.nX = X.card) (hk : cfg.k = pairs.length)
    (hdem_le : cfg.curDemandIn ≤ X.card)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hi_lt : i < pairs.length)
    (hinv_len : curPairs.length = pairs.length)
    (hcur_i : curPairs[i]'(by omega) = (A, B))
    (hinv : BatchRouteInv st0.mem mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
      pairs curPairs i V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed)
    (hregs : BatchRouteRegs st0.regs cfg cfgAddr bfsGen dfsGen pathHeap chunkHeap i routed)
    (hdem_drop : totalDemand (pairs.drop i) = A.card + totalDemand (pairs.drop (i + 1))) :
    ∀ ω,
      let sp := shortPathBlock (adjOf G X) V A B cfg.d
      ∃ stC cAC spHead pathHeap1 bfsGen1 dfsGen1,
        Runs w p ω (seqStmts (batchRouteStepSpStmts bSp)) st0 .normal stC cAC ∧
        (∀ r, r ≤ 17 ∨ r = 21 ∨ r = 29 ∨ r = 31 ∨ r = 32 → stC.regs r = st0.regs r) ∧
        stC.regs 18 = bfsGen1 ∧ stC.regs 19 = dfsGen1 ∧
        stC.regs 20 = pathHeap1 ∧ stC.regs 22 = spHead ∧
        stC.regs 25 = sp.paths.length ∧ stC.regs 30 = routed + sp.paths.length ∧
        pathHeap ≤ pathHeap1 ∧ pathHeap1 ≤ pathHeap + 5 * (V \ sp.remVerts).card ∧
        bfsGen ≤ bfsGen1 ∧ bfsGen1 ≤ bfsGen + cfg.d + 1 ∧
        dfsGen ≤ dfsGen1 ∧ dfsGen1 ≤ dfsGen + cfg.d + 1 ∧
        PathListAt stC.mem X pLo pathHeap1 spHead sp.paths ∧
        (∀ v < X.card, stC.mem (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔ origOf X v ∈ sp.remVerts) ∧
        (∀ v < X.card, stC.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1) ∧
        (∀ v < X.card, stC.mem (wsMatchAStamp cfg.ws cfg.nX + v) = st0.mem (wsMatchAStamp cfg.ws cfg.nX + v)) ∧
        (∀ v < X.card, stC.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen1) ∧
        (∀ v < X.card, stC.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen1) ∧
        (∀ v < X.card, stC.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen1) ∧
        (∀ v < X.card, stC.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen1) ∧
        (∀ v < X.card, stC.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) =
          st0.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v)) ∧
        (∀ v < X.card, stC.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) =
          st0.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v)) ∧
        BatchSubCfgsInit stC.mem cfg hL ∧
        (∀ j < pairs.length,
          ChunkChainAt stC.mem X pLo pathHeap1 cLo chunkHeap
            (stC.mem (cfg.accHeadAddr + j)) (stC.mem (cfg.accTailAddr + j)) (accCur j)) ∧
        ChunksDisj stC.mem cfg.accHeadAddr pairs.length (fun j => (accCur j).length) ∧
        (∀ a, ¬ ((cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨
                 (pathHeap ≤ a ∧ a < pathHeap + 10 * cfg.nX)) → stC.mem a = st0.mem a) ∧
        cAC ≤ spProgCost sp.cost (A \ V).card + 180 := by
  intro ω
  have hi_cur : i < curPairs.length := by omega
  have hvalid_i_sub : A ⊆ X ∧ B ⊆ X := by
    have := hinv.cur_valid.1 (curPairs[i]'hi_cur) (List.getElem_mem hi_cur)
    rw [hcur_i] at this; exact ⟨this.1, this.2.1⟩
  have hvalid_i_disj : Disjoint A B := by
    have := hinv.cur_valid.disjoint_pair (List.getElem_mem hi_cur)
    rwa [hcur_i] at this
  set sp := shortPathBlock (adjOf G X) V A B cfg.d
  have hsp_ep := shortPathBlock_paths_endpoints_subset G hinv.V_sub A B hvalid_i_disj cfg.d
  have hsp_len_le_A : sp.paths.length ≤ A.card := by
    have hML_sub : (sp.paths.map fun q => q.1.1).toFinset ⊆ A := by
      intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
      rcases hx with ⟨q, hq, rfl⟩; exact (hsp_ep.1 q hq).1
    rw [← hsp_ep.2.1]; exact Finset.card_le_card hML_sub
  rcases hinv.lp with ⟨hlp_b, hlp_a⟩
  have ha_i := hlp_a.2 i hi_cur
  dsimp only at ha_i; rw [hcur_i] at ha_i
  set aOff_i := st0.mem (cfg.aOffAddr + i)
  set aLen_i := st0.mem (cfg.aLenAddr + i)
  set aBase := cfg.aDataAddr + aOff_i
  have haLen_eq : aLen_i = A.card := ha_i.2.1
  have haOff_hi : aOff_i + aLen_i ≤ X.card := by
    have hmono := localAPairsAt_slot_bound hlp_a (i + 1) curPairs.length (by omega) le_rfl
    have h1 := ha_i.1
    rw [show cfg.aOffAddr + (i + 1) = cfg.aOffAddr + i + 1 by omega] at hmono
    have h2 := hlp_a.1
    omega
  rcases hregs with ⟨hr0, hr1, hr2, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16,
    hr17, hr18, hr19, hr20, hr21, hr29, hr30, hr31, hr32⟩
  have hw4 := hdisj.w_4
  have hw_ws := hdisj.w_ws; have hw_ao := hdisj.w_ao; have hw_al := hdisj.w_al
  have hw_ad := hdisj.w_ad; have hw_hp := hdisj.w_hp; have hw_ch := hdisj.w_ch
  have hw_nX4 := hdisj.w_nX4; have hw_k := hdisj.w_k; have hw_d := hdisj.w_d
  have hw_bgen := hdisj.w_bgen; have hw_bfsgen := hdisj.w_bfsgen; have hw_dfsgen := hdisj.w_dfsgen
  have hhp_le_pHi : pathHeap + 10 * cfg.nX ≤ pHi := by
    have h1 := hinv.php_hi
    have h2 : (X \ V).card ≤ X.card := Finset.card_le_card Finset.sdiff_subset
    have h3 := hdisj.hp_hi; omega
  have hhp_lo_pLo : pLo ≤ pathHeap := le_trans hdisj.hp_lo hinv.php_lo
  have hk_d1_le : i * (cfg.d + 1) ≤ cfg.k * (cfg.d + 1) := Nat.mul_le_mul_right _ (by omega)
  have hk_d1_le3 : cfg.k * (cfg.d + 1) ≤ cfg.k * (cfg.d + 3) := Nat.mul_le_mul_left _ (by omega)
  have hch_lo_cLo : cLo ≤ chunkHeap := le_trans hdisj.ch_lo hinv.chp_lo
  have hch_le_cHi : chunkHeap ≤ cHi := by
    have := hinv.chp_hi; have := hinv.routed_le; have := hdisj.ch_hi; omega
  have hbg_hi := hinv.bgen_hi
  have hdg_hi := hinv.dgen_hi
  -- Phase A: setup sub-configs
  obtain ⟨stA, cA, hrunA, hstA_regs, hsp3, hsp6, hsp7, hsp9, hsp10, hsp11,
    hbfs3, hbfs6, hdfs4, hdfs6, hmemA_out, hcA⟩ :=
    batchRouteSetup_triple (w := w) (p := p) (cfg := cfg)
      (aOff_i := aOff_i) (aLen_i := aLen_i) (bfsGen := bfsGen) (dfsGen := dfsGen)
      (pathHeap := pathHeap) (i := i)
      (by unfold batchScratchSize at hw_ws; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw4
      rfl rfl hr9 hr10 hr11 hr15 hr17 hr18 hr19 hr20 hr29 hr31 hr32 ω
  have hmemA_outside_68 : ∀ a, (a < cfg.ws ∨ cfg.ws + 68 ≤ a) → stA.mem a = st0.mem a := fun a ha =>
    hmemA_out a (by simp [wsSpCfg]; omega) (by simp [wsSpCfg]; omega) (by simp [wsSpCfg]; omega)
      (by simp [wsSpCfg]; omega) (by simp [wsSpCfg]; omega) (by simp [wsSpCfg]; omega)
      (by simp [wsBfsCfg]; omega) (by simp [wsBfsCfg]; omega)
      (by simp [wsDfsCfg]; omega) (by simp [wsDfsCfg]; omega)
  have hsubA : BatchSubCfgsInit stA.mem cfg hL :=
    batch_sub_of_spSetup hinv.sub_init hmemA_out
  -- Phase B: call shortPathBlockProc
  set spCfg := mkBatchSpCfg cfg (cfg.batchGenIn + 1) aBase aLen_i bfsGen dfsGen pathHeap
  set bfsCfg : BfsCfg :=
    { mkBatchSpBfsCfg cfg (cfg.batchGenIn + 1) (i + 1) with
      bfsGen := stA.mem (wsBfsCfg cfg.ws + 12)
      initLen := stA.mem (wsBfsCfg cfg.ws + 15) }
  set dfsCfg : DfsCfg :=
    { mkBatchSpDfsCfg cfg (cfg.batchGenIn + 1) (i + 1) with
      bfsGen := stA.mem (wsDfsCfg cfg.ws + 8)
      dfsGen := stA.mem (wsDfsCfg cfg.ws + 17)
      targetDepth := stA.mem (wsDfsCfg cfg.ws + 18)
      srcLen := stA.mem (wsDfsCfg cfg.ws + 20)
      heapIn := stA.mem (wsDfsCfg cfg.ws + 21)
      inHead := stA.mem (wsDfsCfg cfg.ws + 22)
      inTail := stA.mem (wsDfsCfg cfg.ws + 23) }
  have hspDisj : SpDisj w X.card cfg.m2 spCfg bfsCfg dfsCfg (wsSpCfg cfg.ws) := by
    rw [← hnX]
    exact spDisj_of_dyn (hdisj.to_spDisj (batchGen := cfg.batchGenIn + 1) (stopVal := i + 1)
      (srcInPtr := aBase) (srcInLen := aLen_i) (bfsGen := bfsGen) (dfsGen := dfsGen)
      (heapIn := pathHeap) le_rfl (by omega) ⟨by omega, by omega⟩
      (by omega) (by omega) hhp_lo_pLo hhp_le_pHi)
  have hspPre : (shortPathBlockContract w X V A B (adjOf G X) spCfg bfsCfg dfsCfg cfg.m2).pre
      [wsSpCfg cfg.ws] stA.mem := by
    refine ⟨rfl, hinv.V_sub, hvalid_i_sub.1, fun u _ e he => adjOf_fst_mem_X G X u e he,
      ?_, ?_, ?_, ?_, hm2, hspDisj, ?_, ?_, ?_, haLen_eq, ?_, ?_, ?_, ?_⟩
    · rcases hsubA with ⟨h0, h1, h2, h3, h4, h5, _⟩
      exact ⟨h0, h1, h2, hsp3, h3, h4, hsp6, hsp7, h5, hsp9, hsp10, hsp11⟩
    · rcases hsubA with ⟨_, _, _, _, _, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩
      exact ⟨h6, h7, h8, hbfs3, h9, h10, hbfs6, h11, h12, h13, h14, h15, rfl, h16, h17, rfl⟩
    · rcases hsubA with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, _⟩
      exact ⟨h18, h19, h20, h21, hdfs4, h22, hdfs6, h23, rfl, h24, h25, h26, h27, h28, h29, h30,
        h31, rfl, rfl, h32, rfl, rfl, rfl, rfl⟩
    · have h1 := hdisj.ro_off_ws; have h2 := hdisj.ro_nb_ws; have h3 := hdisj.ro_edge_ws
      unfold DisjRange batchScratchSize at h1 h2 h3
      exact hinv.csr.congr
        (fun k hk => hmemA_outside_68 (cfg.offAddr + k) (by rcases h1 with x | x <;> omega))
        (fun k hk => hmemA_outside_68 (cfg.nbAddr + k) (by rcases h2 with x | x <;> omega))
        (fun k hk => hmemA_outside_68 (cfg.edgeAddr + k) (by rcases h3 with x | x <;> omega))
    · intro v hv
      rw [hmemA_outside_68 _ (by simp [spCfg, mkBatchSpCfg, wsIsoStamp]; omega)]
      exact hinv.iso_ok v hv
    · have hpb_ws := hdisj.pb_ws; unfold DisjRange batchScratchSize at hpb_ws
      intro v hv
      rw [hmemA_outside_68 _ (by simp [bfsCfg, mkBatchSpBfsCfg]; rcases hpb_ws with x | x <;> omega)]
      have hbi := (hlp_b v hv).2 i hi_cur
      rw [hcur_i] at hbi
      exact hbi
    · have had_ws := hdisj.ad_ws; unfold DisjRange batchScratchSize at had_ws
      intro idx hidx
      have hidx_lt : idx < A.card := by simpa using hidx
      rw [hmemA_outside_68 _ (by simp [spCfg, mkBatchSpCfg]; rcases had_ws with x | x <;> omega)]
      exact ha_i.2.2 idx hidx
    · intro v hv; rw [hmemA_outside_68 _ (by simp [bfsCfg, mkBatchSpBfsCfg, wsVisStamp]; omega)]
      exact hinv.vis_le v hv
    · intro v hv; rw [hmemA_outside_68 _ (by simp [dfsCfg, mkBatchSpDfsCfg, wsCurStamp]; omega)]
      exact hinv.cur_le v hv
    · intro v hv; rw [hmemA_outside_68 _ (by simp [dfsCfg, mkBatchSpDfsCfg, wsUsedStamp]; omega)]
      exact hinv.used_le v hv
    · intro v hv; rw [hmemA_outside_68 _ (by simp [dfsCfg, mkBatchSpDfsCfg, wsDeadStamp]; omega)]
      exact hinv.dead_le v hv
  have hspMC := shortPathBlock_meetsContract (w := w) (p := p) hsp_proc hbfs_proc hdfs_proc
    X V A B (adjOf G X) spCfg bfsCfg dfsCfg cfg.m2
  have hsp_args : evalArgs w stA [.reg 15] = some [wsSpCfg cfg.ws] := by
    simp [evalArgs, Expr.eval, hstA_regs, hr15]
  obtain ⟨stB, cB, spRet, hrunB, hpostSp, hr25B, hrB_oth, hcB⟩ :=
    runs_call_of_meetsContract (r := 25) hspMC hsp_args
      (by intro x hx; simp at hx; subst hx; simp [wsSpCfg]; unfold batchScratchSize at hw_ws; omega)
      hspPre ω
  simp only [shortPathBlockContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpostSp hcB
  have hsp_eq_sp : shortPathBlock (adjOf G X) V A B spCfg.d = sp := rfl
  rw [hsp_eq_sp] at hpostSp hcB
  rcases hpostSp with ⟨hspRet_eq, hspOut, hspFrame, hspMask_mono⟩
  have hstB_r : stB.regs = Function.update stA.regs 25 spRet := by
    ext r; by_cases h : r = 25
    · subst h; simpa using hr25B
    · simp [h, hrB_oth r h]
  rcases hspOut with ⟨_, hspHeap_lo, hspHeap_hi,
    hspBfs_lo, hspBfs_hi, hspDfs_lo, hspDfs_hi, hspChain, hspMask_ok,
    hspVis_le, hspCur_le, hspUsed_le, hspDead_le⟩
  set spHead := stB.mem (wsSpCfg cfg.ws + 12)
  set pathHeap1 := stB.mem (wsSpCfg cfg.ws + 14)
  set bfsGen1 := stB.mem (wsSpCfg cfg.ws + 16)
  set dfsGen1 := stB.mem (wsSpCfg cfg.ws + 17)
  have hspPathList : PathListAt stB.mem X pLo pathHeap1 spHead sp.paths :=
    pathListAt_mono_lo hhp_lo_pLo hspChain.to_pathListAt
  -- Phase C: load output registers into stC
  set regsC := Function.update (Function.update (Function.update (Function.update
    (Function.update stB.regs 22 spHead) 20 pathHeap1) 18 bfsGen1) 19 dfsGen1)
    30 (routed + sp.paths.length)
  set stC : State := { mem := stB.mem, regs := regsC, pos := stB.pos }
  obtain ⟨cC, hrunC, hcC⟩ :=
    batchRouteLoadSp_triple (w := w) (p := p) (spCfgAddr := wsSpCfg cfg.ws)
      (routed := routed) (spLen := sp.paths.length)
      (by simp only [wsSpCfg]; unfold batchScratchSize at hw_ws; omega)
      (by have := hinv.routed_le; omega)
      (by unfold batchScratchSize at hw_ws; omega)
      (by simp [hstB_r, hstA_regs, hr15])
      (hr25B.trans hspRet_eq)
      (by simp [hstB_r, hstA_regs, hr30])
      rfl rfl rfl rfl ω
  -- Stitch Phases A + B + C
  obtain ⟨cAB, hrunAB, hcAB⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunA
    (show Runs w p ω (seqStmts [.call 25 bSp [.reg 15]]) stA .normal stB cB from hrunB)
  obtain ⟨cAC, hrunAC, hcAC⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunAB hrunC
  -- Frame of stC (= stB) relative to st0
  have hspFrame' : ∀ a,
      ¬ SpWriteSet cfg.nX
        (mkBatchSpCfg cfg (cfg.batchGenIn + 1) aBase aLen_i bfsGen dfsGen pathHeap)
        (mkBatchSpBfsCfg cfg (cfg.batchGenIn + 1) (i + 1))
        (mkBatchSpDfsCfg cfg (cfg.batchGenIn + 1) (i + 1)) (wsSpCfg cfg.ws) a →
      stB.mem a = stA.mem a := fun a ha => hspFrame a (by rw [← hnX]; exact ha)
  have hstC_fr : ∀ a,
      ¬ ((cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨
         (pathHeap ≤ a ∧ a < pathHeap + 10 * cfg.nX)) →
      stC.mem a = st0.mem a := by
    intro a ha
    have hnotSp : ¬ SpWriteSet cfg.nX
        (mkBatchSpCfg cfg (cfg.batchGenIn + 1) aBase aLen_i bfsGen dfsGen pathHeap)
        (mkBatchSpBfsCfg cfg (cfg.batchGenIn + 1) (i + 1))
        (mkBatchSpDfsCfg cfg (cfg.batchGenIn + 1) (i + 1)) (wsSpCfg cfg.ws) a := fun hw =>
      ha (batch_spWriteSet_in_ws_or_hp hw)
    have hnotWs : ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) :=
      fun h => ha (Or.inl h)
    have h68 : a < cfg.ws ∨ cfg.ws + 68 ≤ a := by
      have hS : 68 ≤ batchScratchSize cfg.nX cfg.m2 cfg.k := by unfold batchScratchSize; omega
      by_cases hlt : a < cfg.ws
      · exact Or.inl hlt
      · right; by_contra hlt2; exact hnotWs ⟨Nat.le_of_not_lt hlt, lt_of_lt_of_le (Nat.lt_of_not_le hlt2) (Nat.add_le_add_left hS cfg.ws)⟩
    exact (hspFrame' a hnotSp).trans (hmemA_outside_68 a h68)
  have hnotSp_ws_hi : ∀ a, cfg.ws + 124 + cfg.nX ≤ a → a < cfg.ws + 124 + 2 * cfg.nX ∨
      cfg.ws + 129 + 16 * cfg.nX + cfg.m2 + 3 * cfg.k ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k →
      stC.mem a = st0.mem a := by
    intro a ha1 ha2
    exact (hspFrame' a (batch_not_spWriteSet_ws_hi hdisj.ws_hp hhp_lo_pLo hhp_le_pHi ha1 ha2)).trans
      (hmemA_outside_68 a (by omega))
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by omega)
  have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' (by omega)
  dsimp only [batchRouteStepSpStmts]
  simp only [List.cons_append, List.nil_append] at hrunAC hcAC
  refine ⟨stC, cAC, spHead, pathHeap1, bfsGen1, dfsGen1, hrunAC,
    fun r hr => by
      rcases batch_sp_r_ne hr with ⟨h30, h19, h18, h20, h22, h25, h24, h23⟩
      simp only [stC, regsC, hstB_r, hstA_regs, Function.update_of_ne h30,
        Function.update_of_ne h19, Function.update_of_ne h18, Function.update_of_ne h20,
        Function.update_of_ne h22, Function.update_of_ne h25, Function.update_of_ne h24,
        Function.update_of_ne h23],
    by simp [stC, regsC], by simp [stC, regsC], by simp [stC, regsC], by simp [stC, regsC],
    by simp [stC, regsC, hstB_r, hspRet_eq], by simp [stC, regsC],
    hspHeap_lo, hspHeap_hi, hspBfs_lo, hspBfs_hi, hspDfs_lo, hspDfs_hi,
    hspPathList, hspMask_ok,
    fun v hv => by
      rcases hspMask_mono v hv with hsame | hbad
      · dsimp only [spCfg, mkBatchSpCfg] at hsame
        rw [show stC.mem _ = stB.mem _ from rfl, hsame,
          hmemA_outside_68 _ (by unfold wsIsoStamp; omega)]
        exact hinv.iso_le v hv
      · dsimp only [spCfg, mkBatchSpCfg] at hbad
        rw [show stC.mem _ = stB.mem _ from rfl, hbad],
    fun v hv => hnotSp_ws_hi _ (by unfold wsMatchAStamp; omega) (Or.inl (by unfold wsMatchAStamp; omega)),
    hspVis_le, hspCur_le, hspUsed_le, hspDead_le,
    fun v hv => hnotSp_ws_hi _ (by unfold wsBallStamp; omega) (Or.inr ⟨by unfold wsBallStamp; omega, by unfold wsBallStamp batchScratchSize; omega⟩),
    fun v hv => hnotSp_ws_hi _ (by unfold wsLiveStamp; omega) (Or.inr ⟨by unfold wsLiveStamp; omega, by unfold wsLiveStamp batchScratchSize; omega⟩),
    hsubA.of_spWriteSet hdisj hhp_lo_pLo hhp_le_pHi hspFrame',
    ?_, ?_, hstC_fr, ?_⟩
  · intro j hj
    have hah_ws := hdisj.ah_ws; have hah_hp := hdisj.ah_hp
    have hat_ws := hdisj.at_ws; have hat_hp := hdisj.at_hp
    have hws_ch := hdisj.ws_ch; have hhp_ch := hdisj.hp_ch; have hws_hp := hdisj.ws_hp
    unfold DisjRange at hah_ws hah_hp hat_ws hat_hp hws_ch hhp_ch hws_hp
    have hm_ah : stC.mem (cfg.accHeadAddr + j) = st0.mem (cfg.accHeadAddr + j) :=
      hstC_fr _ (by rcases hah_ws with x | x <;> rcases hah_hp with y | y <;> omega)
    have hm_at : stC.mem (cfg.accTailAddr + j) = st0.mem (cfg.accTailAddr + j) :=
      hstC_fr _ (by rcases hat_ws with x | x <;> rcases hat_hp with y | y <;> omega)
    rw [hm_ah, hm_at]
    exact ((hinv.chunks j hj).congr
      (fun a ha1 ha2 => hstC_fr a (by rcases hws_hp with x | x <;> omega))
      (fun a ha1 ha2 => hstC_fr a (by rcases hws_ch with x | x <;> rcases hhp_ch with y | y <;> omega))).mono_pHi hspHeap_lo
  · have hws_ch := hdisj.ws_ch; have hhp_ch := hdisj.hp_ch
    have hah_ws := hdisj.ah_ws; have hah_hp := hdisj.ah_hp; have hws_hp := hdisj.ws_hp
    unfold DisjRange at hws_ch hhp_ch hah_ws hah_hp hws_hp
    have hca_eq : ∀ j < pairs.length,
        chunkAddrs stC.mem (stC.mem (cfg.accHeadAddr + j)) (accCur j).length =
        chunkAddrs st0.mem (st0.mem (cfg.accHeadAddr + j)) (accCur j).length := by
      intro j hj
      have hm_ah : stC.mem (cfg.accHeadAddr + j) = st0.mem (cfg.accHeadAddr + j) :=
        hstC_fr _ (by rcases hah_ws with x | x <;> rcases hah_hp with y | y <;> omega)
      rw [hm_ah]
      exact ((hinv.chunks j hj).congr_addrs
        (fun a ha1 ha2 => hstC_fr a (by rcases hws_hp with x | x <;> omega))
        (fun a ha => by
          have hab := (hinv.chunks j hj).chunkAddrs_bounds a ha
          exact ⟨hstC_fr a (by rcases hws_ch with x | x <;> rcases hhp_ch with y | y <;> omega),
                 hstC_fr (a + 1) (by rcases hws_ch with x | x <;> rcases hhp_ch with y | y <;> omega)⟩)).2
    intro j1 hj1 j2 hj2 hne a ha b hb
    rw [hca_eq j1 hj1] at ha; rw [hca_eq j2 hj2] at hb
    exact hinv.chunks_disj j1 hj1 j2 hj2 hne a ha b hb
  · simp only [argsSize, Expr.size, List.length_cons, List.length_nil] at hcB hcAB hcAC
    omega


end MinCostFlow.ExpanderDecomp
