module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchStepUpd

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Loop Verification (`RouteProgBatchRoute`)

Inductive verification of `batchRouteLoopStmt` against `batchRoutePairs`, combining
`batchRouteStep_sp` (Phases A–C) and `batchRouteStep_upd` (Phases D–F).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Verification of the pair-routing loop `batchRouteLoopStmt` against `batchRoutePairs`. -/
theorem batchRouteLoop_triple {w : ℕ} {p : Program} {bSp bBfs bDfs : ℕ}
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    {G : Graph} {X : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hnX : cfg.nX = X.card) (hk : cfg.k = pairs.length)
    (hdem_le : cfg.curDemandIn ≤ X.card)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    {mem0 : ℕ → ℕ} (rem : ℕ) :
    ∀ (i : ℕ) (curPairs : List (Finset ℕ × Finset ℕ)) (V M_acc : Finset ℕ)
      (accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ)))
      (bfsGen dfsGen pathHeap chunkHeap routed : ℕ) (st0 : State),
      i + rem = pairs.length →
      BatchRouteInv st0.mem mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
        pairs curPairs i V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed →
      BatchRouteRegs st0.regs cfg cfgAddr bfsGen dfsGen pathHeap chunkHeap i routed →
      ∀ ω,
        let tail := batchRoutePairs (adjOf G X) cfg.d (pairs.drop i) V
        ∃ st' c,
          Runs w p ω (batchRouteLoopStmt bSp) st0 .normal st' c ∧
          (∀ r, r ≤ 17 ∨ r = 31 ∨ r = 32 → st'.regs r = st0.regs r) ∧
          st'.regs 29 = pairs.length ∧
          st'.regs 30 = routed + tail.routedCount ∧
          bfsGen ≤ st'.regs 18 ∧ st'.regs 18 ≤ bfsGen + rem * (cfg.d + 1) ∧
          dfsGen ≤ st'.regs 19 ∧ st'.regs 19 ≤ dfsGen + rem * (cfg.d + 1) ∧
          pathHeap ≤ st'.regs 20 ∧ st'.regs 20 ≤ pathHeap + 5 * (V \ tail.remVerts).card ∧
          chunkHeap ≤ st'.regs 21 ∧ st'.regs 21 ≤ chunkHeap + 2 * tail.routedCount ∧
          LocalPairsAt st'.mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr
            X (curPairs.take i ++ tail.remPairs) X.card ∧
          (∀ v < X.card, st'.mem (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔
            origOf X v ∈ tail.remVerts) ∧
          (∀ v < X.card, st'.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1) ∧
          (∀ v < X.card, st'.mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1) ∧
          (∀ v < X.card, st'.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ st'.regs 18) ∧
          (∀ v < X.card, st'.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ st'.regs 19) ∧
          (∀ v < X.card, st'.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ st'.regs 19) ∧
          (∀ v < X.card, st'.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ st'.regs 19) ∧
          (∀ v < X.card, st'.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.ballGenIn) ∧
          (∀ v < X.card, st'.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn) ∧
          BatchSubCfgsInit st'.mem cfg hL ∧
          AdjCsrAt st'.mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X) ∧
          (∀ j < pairs.length,
            let newCh :=
              if j < i then accCur j
              else
                let bp := tail.perPairPaths.getD (j - i) []
                if bp = [] then accCur j else accCur j ++ [bp]
            ChunkChainAt st'.mem X pLo (st'.regs 20) cLo (st'.regs 21)
              (st'.mem (cfg.accHeadAddr + j)) (st'.mem (cfg.accTailAddr + j)) newCh) ∧
          ChunksDisj st'.mem cfg.accHeadAddr pairs.length (fun j =>
            (if j < i then accCur j
             else
               let bp := tail.perPairPaths.getD (j - i) []
               if bp = [] then accCur j else accCur j ++ [bp]).length) ∧
          (∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → st'.mem a = mem0 a) ∧
          (∀ o < 26, st'.mem (cfgAddr + o) = mem0 (cfgAddr + o)) ∧
          c ≤ 1100 * tail.cost + 150 * ((pairs.drop i).map fun ab => (ab.1 \ tail.remVerts).card).sum + 20 := by
  have hw4 := hdisj.w_4
  have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
  induction rem with
  | zero =>
    intro i curPairs V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed st0 hi hinv hregs ω
    have hi_eq : i = pairs.length := by omega
    have hdrop : pairs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    have htake : curPairs.take i = curPairs := List.take_of_length_le (by have := hinv.cur_len; omega)
    rcases hregs with ⟨_, _, hr2, _, _, _, _, _, _, _, _, _, _, hr18, hr19, hr20, hr21, hr29, hr30, _, _⟩
    dsimp only; rw [hdrop]
    simp only [batchRoutePairs, List.append_nil, List.map_nil, List.sum_nil,
      Nat.add_zero, Nat.zero_mul, Nat.mul_zero, sdiff_self]
    refine ⟨st0, _, batch_runs_loop_zero (by simp [Expr.eval, BinOp.eval, hr29, hr2, hk, hi_eq]),
      fun _ _ => rfl, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by simpa [htake] using hinv.lp,
      hinv.iso_ok, hinv.iso_le, hinv.ma_le,
      by simpa [hr18] using hinv.vis_le, by simpa [hr19] using hinv.cur_le,
      by simpa [hr19] using hinv.used_le, by simpa [hr19] using hinv.dead_le,
      hinv.ball_le, hinv.live_le, hinv.sub_init, hinv.csr,
      fun j hj => by simp only [show j < i by omega, ↓reduceIte, hr20, hr21]; exact hinv.chunks j hj,
      fun j1 hj1 j2 hj2 hne => by
        simp only [show j1 < i by omega, show j2 < i by omega, ↓reduceIte]
        exact hinv.chunks_disj j1 hj1 j2 hj2 hne,
      hinv.frame, hinv.cfg_ro, by simp [Expr.size]⟩
  | succ rem ih =>
    intro i curPairs V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed st0 hi hinv hregs ω
    have hi_lt : i < pairs.length := by omega
    have hi_cur : i < curPairs.length := by have := hinv.cur_len; omega
    set ab := pairs[i]'hi_lt
    rcases hab_eq : ab with ⟨A, B⟩
    have hdrop_eq : pairs.drop i = (A, B) :: pairs.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi_lt, ← hab_eq]
    have hcur_i : curPairs[i]'hi_cur = (A, B) := by
      have h1 : (curPairs.drop i)[0]? = (pairs.drop i)[0]? := congrArg (·[0]?) hinv.cur_drop
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hi_cur,
          List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hi_lt] at h1
      exact (Option.some.inj h1).trans hab_eq
    have hdem_drop : totalDemand (pairs.drop i) = A.card + totalDemand (pairs.drop (i + 1)) := by
      rw [hdrop_eq]; simp [totalDemand]
    have hcond : (Expr.bin .lt (.reg 29) (.reg 2)).eval w st0 = some 1 := by
      simp [Expr.eval, BinOp.eval, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.1, hk, hi_lt, hw_ne]
    set sp := shortPathBlock (adjOf G X) V A B cfg.d
    set ML := (sp.paths.map fun q => q.1.1).toFinset
    set MR := (sp.paths.map fun q => q.1.2).toFinset
    set tailRest := batchRoutePairs (adjOf G X) cfg.d (pairs.drop (i + 1)) sp.remVerts
    have hsp_sub : sp.remVerts ⊆ V := (shortPathBlockLoop_remVerts_sub _ _ _ _ _ _ _ _).1
    have hsp_dc := shortPathBlock_diff_card_le_cost (adjOf G X) V A B cfg.d
    -- Phases A–C
    obtain ⟨stC, cAC, spHead, pathHeap1, bfsGen1, dfsGen1, hrunAC, hregsC_eq,
      hC18, hC19, hC20, hC22, hC25, hC30, hspHeap_lo, hspHeap_hi, hspBfs_lo, hspBfs_hi,
      hspDfs_lo, hspDfs_hi, hspPathList, hspMask_ok, hspMask_le, hma_C,
      hspVis_le, hspCur_le, hspUsed_le, hspDead_le, hball_C, hlive_C, hsubC, hch_C, hchDisj_C,
      hstC_fr, hcAC⟩ :=
      batchRouteStep_sp hsp_proc hbfs_proc hdfs_proc hnX hk hdem_le hm2 hdisj hi_lt
        hinv.cur_len hcur_i hinv hregs hdem_drop ω
    -- Phases D–F
    obtain ⟨st1, cDF, hrunDF, hregs1_eq, hinv1, hregs1, hcDF⟩ :=
      batchRouteStep_upd hnX hk hm2 hdisj hi_lt hinv.cur_len hcur_i hinv hregs hdem_drop
        hregsC_eq hC18 hC19 hC20 hC22 hC25 hC30 hspHeap_lo hspHeap_hi hspBfs_lo hspBfs_hi
        hspDfs_lo hspDfs_hi hspPathList hspMask_ok hspMask_le hma_C hspVis_le hspCur_le
        hspUsed_le hspDead_le hball_C hlive_C hsubC hch_C hchDisj_C hstC_fr ω
    -- Combine Phases A–C and D–F into loop body
    obtain ⟨cBody, hrunBody, hcBody⟩ :=
      batch_runs_seqStmts_append (by simp [batchRouteStepSpStmts]) (by simp [batchRouteStepUpdStmts]) hrunAC hrunDF
    -- Apply IH
    set curPairs1 := curPairs.set i (A \ ML, B \ MR)
    set chunkHeap1 := if sp.paths = [] then chunkHeap else chunkHeap + 2
    set accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
      if j = i then (if sp.paths = [] then accCur i else accCur i ++ [sp.paths]) else accCur j
    obtain ⟨stF, cIH, hrunIH, hregsIH, hr29F, hr30F, hbLoF, hbHiF, hdLoF, hdHiF,
      hpLoF, hpHiF, hcLoF, hcHiF, hlpF, hisoF, hisoLeF, hmaLeF, hvisF, hcurF, husedF, hdeadF,
      hballF, hliveF, hsubF, hcsrF, hchF, hchDisjF, hfrF, hcfgRoF, hcIH⟩ :=
      ih (i + 1) curPairs1 sp.remVerts (M_acc ∪ ML) accCur1 bfsGen1 dfsGen1 pathHeap1 chunkHeap1
        (routed + sp.paths.length) st1 (by omega) hinv1 hregs1 ω
    set tail := batchRoutePairs (adjOf G X) cfg.d (pairs.drop i) V
    have htail_per : tail.perPairPaths = sp.paths :: tailRest.perPairPaths := by
      dsimp only [tail]; rw [hdrop_eq]; simp [batchRoutePairs, sp, tailRest]
    have htail_rem : tail.remPairs = (A \ ML, B \ MR) :: tailRest.remPairs := by
      dsimp only [tail]; rw [hdrop_eq]; simp [batchRoutePairs, sp, tailRest, ML, MR]
    have htail_rc : tail.routedCount = sp.paths.length + tailRest.routedCount := by
      dsimp only [tail]; rw [hdrop_eq]; simp [batchRoutePairs, sp, tailRest]
    have htail_cost : tail.cost = sp.cost + tailRest.cost + 1 := by
      dsimp only [tail]; rw [hdrop_eq]; simp [batchRoutePairs, sp, tailRest]
    have htail_rv : tail.remVerts = tailRest.remVerts := by
      dsimp only [tail]; rw [hdrop_eq]; simp [batchRoutePairs, sp, tailRest]
    have htake_eq : curPairs1.take (i + 1) ++ tailRest.remPairs =
        curPairs.take i ++ tail.remPairs := by
      rw [htail_rem]
      have h1 : curPairs1.take (i + 1) = curPairs.take i ++ [(A \ ML, B \ MR)] := by
        rw [List.take_succ_eq_append_getElem (by simp [curPairs1]; omega)]
        simp only [curPairs1, List.getElem_set_self]
        congr 1; apply List.ext_getElem (by simp)
        intro j h1 h2; simp only [List.length_take] at h2
        simp only [List.getElem_take, List.getElem_set_ne (by omega : i ≠ j)]
      rw [h1, List.append_assoc, List.singleton_append]
    have hV_split : (V \ tail.remVerts).card = (V \ sp.remVerts).card + (sp.remVerts \ tailRest.remVerts).card := by
      rw [htail_rv]
      have hsubR : tailRest.remVerts ⊆ sp.remVerts := (batchRoutePairs_remVerts_sub _ _ _ _).1
      have hdj : Disjoint (V \ sp.remVerts) (sp.remVerts \ tailRest.remVerts) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
      have heq : V \ tailRest.remVerts = (V \ sp.remVerts) ∪ (sp.remVerts \ tailRest.remVerts) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro ⟨hxV, hnr⟩; by_cases hxS : x ∈ sp.remVerts
          · exact Or.inr ⟨hxS, hnr⟩
          · exact Or.inl ⟨hxV, hxS⟩
        · rintro (⟨hxV, hns⟩ | ⟨hxS, hnr⟩)
          · exact ⟨hxV, fun h => hns (hsubR h)⟩
          · exact ⟨hsp_sub hxS, hnr⟩
      rw [heq, Finset.card_union_of_disjoint hdj]
    have hch_eq_fn : ∀ j < pairs.length,
        (if j < i + 1 then accCur1 j
         else
           let bp := tailRest.perPairPaths.getD (j - (i + 1)) []
           if bp = [] then accCur1 j else accCur1 j ++ [bp]) =
        (if j < i then accCur j
         else
           let bp := tail.perPairPaths.getD (j - i) []
           if bp = [] then accCur j else accCur j ++ [bp]) := by
      intro j _
      rw [htail_per]
      by_cases hlt : j < i
      · have hne : j ≠ i := by omega
        simp [hlt, show j < i + 1 by omega, accCur1, hne]
      · by_cases heq : j = i
        · subst heq; simp [accCur1]
        · have hsub_eq : j - i = (j - (i + 1)) + 1 := by omega
          simp [show ¬ j < i + 1 by omega, show ¬ j < i by omega, accCur1, heq, hsub_eq]
    have hr30F' : stF.regs 30 = routed + sp.paths.length + tailRest.routedCount := hr30F
    have hspHeap_hi' : pathHeap1 ≤ pathHeap + 5 * (V \ sp.remVerts).card := hspHeap_hi
    have hpHiF' : stF.regs 20 ≤ pathHeap1 + 5 * (sp.remVerts \ tailRest.remVerts).card := hpHiF
    have hcHiF' : stF.regs 21 ≤ chunkHeap1 + 2 * tailRest.routedCount := hcHiF
    have hcIH' : cIH ≤ 1100 * tailRest.cost +
        150 * ((pairs.drop (i + 1)).map fun ab => (ab.1 \ tailRest.remVerts).card).sum + 20 := hcIH
    dsimp only
    refine ⟨stF, _, batch_runs_loop_step hcond (by decide) hrunBody hrunIH,
      fun r hr => (hregsIH r hr).trans (hregs1_eq r hr),
      hr29F, by rw [htail_rc]; omega,
      le_trans hspBfs_lo hbLoF, by rw [Nat.add_mul, Nat.one_mul]; omega,
      le_trans hspDfs_lo hdLoF, by rw [Nat.add_mul, Nat.one_mul]; omega,
      le_trans hspHeap_lo hpLoF, by omega,
      by simp only [chunkHeap1] at hcLoF; split_ifs at hcLoF <;> omega,
      by rw [htail_rc]; simp only [chunkHeap1] at hcHiF'; split_ifs at hcHiF' with hnil
         · omega
         · have := List.length_pos_of_ne_nil hnil; omega,
      by rwa [htake_eq] at hlpF,
      by rw [htail_rv]; exact hisoF, hisoLeF, hmaLeF, hvisF, hcurF, husedF, hdeadF, hballF, hliveF, hsubF, hcsrF,
      fun j hj => by rw [← hch_eq_fn j hj]; exact hchF j hj,
      fun j1 hj1 j2 hj2 hne a ha b hb => by
        dsimp only at ha hb
        rw [← hch_eq_fn j1 hj1] at ha
        rw [← hch_eq_fn j2 hj2] at hb
        exact hchDisjF j1 hj1 j2 hj2 hne a ha b hb,
      hfrF, hcfgRoF, ?_⟩
    have hsp_len_le_A : sp.paths.length ≤ A.card := by
      have hvalid_i := hinv.cur_valid.disjoint_pair (List.getElem_mem hi_cur)
      rw [hcur_i] at hvalid_i
      have hep := shortPathBlock_paths_endpoints_subset G hinv.V_sub A B hvalid_i cfg.d
      have hsub : (sp.paths.map fun q => q.1.1).toFinset ⊆ A := by
        intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
        rcases hx with ⟨q, hq, rfl⟩; exact (hep.1 q hq).1
      rw [← hep.2.1]; exact Finset.card_le_card hsub
    have hAV_le_Atail : (A \ V).card ≤ (A \ tailRest.remVerts).card := by
      have hsubR : tailRest.remVerts ⊆ V :=
        Finset.Subset.trans (batchRoutePairs_remVerts_sub _ _ _ _).1 hsp_sub
      exact Finset.card_le_card (Finset.sdiff_subset_sdiff le_rfl hsubR)
    have hA_split : A.card = (A ∩ V).card + (A \ V).card := (Finset.card_inter_add_card_sdiff A V).symm
    have hAV_inter_le : (A ∩ V).card ≤ sp.cost := shortPathBlock_inter_card_le_cost (adjOf G X) V A B cfg.d
    have hcAC' : cAC ≤ spProgCost sp.cost (A \ V).card + 180 := hcAC
    have hcDF' : cDF ≤ 45 * A.card + 40 * sp.paths.length + 140 := hcDF
    rw [htail_cost, htail_rv, hdrop_eq]
    simp only [spProgCost, List.map_cons, List.sum_cons, Expr.size, batchRouteStepSpStmts,
      List.length_cons, List.length_nil] at hcAC' hcDF' hcBody hcIH' ⊢
    omega

end MinCostFlow.ExpanderDecomp
