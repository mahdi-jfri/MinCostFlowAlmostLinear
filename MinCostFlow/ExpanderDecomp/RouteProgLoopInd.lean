module

public import MinCostFlow.ExpanderDecomp.RouteProgLoopInit
public import MinCostFlow.ExpanderDecomp.RouteProgLoopEmit

import Mathlib.Tactic.Ring

/-!
# Outer Batch-Loop Verification (`RouteProgLoop`)

Completes the deterministic Word-RAM verification of Procedure 5 (`routeOrCutCsrProc`),
implementing `routeOrCut` on prebuilt local CSR and local terminal pairs:
- Pure helpers on `routeBatches` and `runBatch` (`routeBatches_cost_add`, `runBatch_props`).
- `RouteLoopInv`: batch-loop invariant tracking remaining terminal pairs, accumulated chunk chains,
  monotonic stamp/heap cursors, and tight `pathHeapOut + 15 * nX` framing.
- `routeBatchesLoop_triple`: inductive verification of `routeBatchesLoopStmt` calling
  `runBatch_meetsContract`.
- `routeOrCutCsr_triple`, `routeOrCutCsrContract`, `routeOrCutCsr_meetsContract`: full contract
  writing `RouteOutAt` at `outAddr` and `WalksAt` at `walksAddr` (when matched), with literal
  cost bound `routeCsrProgCost (routeOrCutCost G X pairs Δ L b z)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helpers on `routeBatches` and `runBatch` -/

lemma routeBatches_cost_add (G : Graph) (X : Finset ℕ) (Δ b L z : ℕ) :
    ∀ (rem : ℕ) (curPairs : List (Finset ℕ × Finset ℕ))
      (acc : List (List ((ℕ × ℕ) × List ℕ))) (c0 c1 : ℕ),
      (routeBatches G X Δ b L z rem curPairs acc (c0 + c1)).1 =
        (routeBatches G X Δ b L z rem curPairs acc c0).1 ∧
      (routeBatches G X Δ b L z rem curPairs acc (c0 + c1)).2 =
        (routeBatches G X Δ b L z rem curPairs acc c0).2 + c1 := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _; simp [routeBatches]
  | succ rem ih =>
    intro curPairs acc c0 c1
    unfold routeBatches
    split_ifs
    · simp
    · dsimp only
      cases h : (runBatch G X Δ b L curPairs).outcome with
      | cut U => exact ⟨rfl, Nat.add_right_comm c0 c1 _⟩
      | matched batchPaths remPairs =>
        have h1 := ih remPairs (List.zipWith (· ++ ·) acc batchPaths) (c0 + (runBatch G X Δ b L curPairs).cost) c1
        rw [Nat.add_right_comm c0 c1]
        exact h1

lemma runBatch_props (G : Graph) {X : Finset ℕ} (Δ b L : ℕ)
    {pairs : List (Finset ℕ × Finset ℕ)} (hvalid : ValidTerminalPairs X pairs) :
    let br := runBatch G X Δ b L pairs
    pairs.length + 1 ≤ br.cost ∧
    match br.outcome with
    | .cut U => X.card + 2 * (G.inside X).length + pairs.length + 2 ≤ br.cost ∧ U ⊆ X
    | .matched batchPaths remPairs =>
        remPairs.length = pairs.length ∧
        batchPaths.length = pairs.length ∧
        ValidTerminalPairs X remPairs ∧
        totalDemand remPairs + batchPaths.flatten.length = totalDemand pairs ∧
        batchPaths.flatten.length ≤ br.cost := by
  unfold runBatch; dsimp only
  set d := routeD Δ b L
  set br0 := batchRoutePairs (adjOf G X) d pairs X
  obtain ⟨hsub_rv, hsub_dc, hsub_rc, hsub_pl, hsub_rl, hsub_fl⟩ :=
    batchRoutePairs_remVerts_sub (adjOf G X) d pairs X
  have hvd := batchRoutePairs_valid_and_demand G d pairs (routeTerminalPairs_of_validTerminalPairs hvalid) X le_rfl
  have hfl_le_cost : br0.perPairPaths.flatten.length ≤ br0.cost := by dsimp only [br0]; omega
  split_ifs with h
  · dsimp only
    refine ⟨by omega, hsub_rl, hsub_pl, validTerminalPairs_of_routeTerminalPairs hvd.1,
      by rw [← hsub_fl]; exact hvd.2, by omega⟩
  · dsimp only
    set baseC := br0.cost + pairs.length + 1 + (X.card + 2 * (G.inside X).length + 1)
    have hadd := batchBallLoop_cost_add (adjOf ⟨G.n, G.inside br0.remVerts⟩ X) X b (routeH Δ b) L br0.remPairs ∅ X 0 baseC
    simp only [Nat.zero_add] at hadd
    have hU : (batchBallLoop (adjOf ⟨G.n, G.inside br0.remVerts⟩ X) X b (routeH Δ b) L br0.remPairs ∅ X baseC).1 ⊆ X := by
      have hb : ∀ (ps : List (Finset ℕ × Finset ℕ)) (U V : Finset ℕ) (cost : ℕ),
          U ⊆ X → V ⊆ X →
          (batchBallLoop (adjOf ⟨G.n, G.inside br0.remVerts⟩ X) X b (routeH Δ b) L ps U V cost).1 ⊆ X := by
        intro ps; induction ps with
        | nil => intro U _ _ hUX _; exact hUX
        | cons ab rest ih =>
          intro U V cost hUX hVX
          dsimp only [batchBallLoop]
          split_ifs
          · exact hUX
          · exact ih U V _ hUX hVX
          · have hgb := growBall_ball_sub (adjOf ⟨G.n, G.inside br0.remVerts⟩ X) V (ab.1 ∩ V) (ab.2 ∩ V) b (routeH Δ b) L
            exact ih _ _ _ (Finset.union_subset hUX (Finset.Subset.trans hgb hVX)) (Finset.Subset.trans Finset.sdiff_subset hVX)
      exact hb _ ∅ X baseC (Finset.empty_subset _) le_rfl
    exact ⟨by omega, by omega, hU⟩

/-! ## 2. Batch-Loop Invariant and `routeBatchesLoop_triple` -/

/-- Invariant at the start of batch iteration `t` (with `t + rem = rcfg.R`). -/
structure RouteLoopInv (mem mem0 : ℕ → ℕ) (G : Graph) (X : Finset ℕ)
    (rcfg : RouteLoopCfg) (cfgAddr pLo pHi cLo cHi : ℕ)
    (initDem t : ℕ) (curPairs : List (Finset ℕ × Finset ℕ))
    (accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))) (costSoFar : ℕ) : Prop where
  k_pairs : curPairs.length = rcfg.batch.k
  k_chunks : accChunks.length = rcfg.batch.k
  valid : ValidTerminalPairs X curPairs
  dem_inv : (accChunks.map List.flatten).flatten.length + totalDemand curPairs = initDem
  flat_le_cost : (accChunks.map List.flatten).flatten.length ≤ costSoFar
  cfg_ro : ∀ o < 32, (o < 16 ∨ 26 ≤ o) → mem (cfgAddr + o) = mem0 (cfgAddr + o)
  dem_mem : mem (cfgAddr + 16) = totalDemand curPairs
  bgen_le : mem (cfgAddr + 17) ≤ rcfg.batch.batchGenIn + t
  bfs_le : mem (cfgAddr + 18) ≤ rcfg.batch.bfsGenIn + t * (rcfg.batch.k * (rcfg.batch.d + 3))
  dfs_le : mem (cfgAddr + 19) ≤ rcfg.batch.dfsGenIn + t * (rcfg.batch.k * (rcfg.batch.d + 1))
  ball_le : mem (cfgAddr + 20) ≤ rcfg.batch.ballGenIn + t * rcfg.batch.k
  live_le : mem (cfgAddr + 21) ≤ rcfg.batch.liveGenIn + t
  php_lo : rcfg.batch.pathHeapIn ≤ mem (cfgAddr + 22)
  php_hi : mem (cfgAddr + 22) ≤ rcfg.batch.pathHeapIn + 5 * costSoFar
  chp_lo : cLo ≤ mem (cfgAddr + 23)
  chp_hi : mem (cfgAddr + 23) + 2 * totalDemand curPairs ≤ cHi
  iso_le : ∀ v < X.card, mem (wsIsoStamp rcfg.batch.ws + v) ≤ mem (cfgAddr + 17)
  ma_le : ∀ v < X.card, mem (wsMatchAStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ mem (cfgAddr + 17)
  vis_le : ∀ v < X.card, mem (wsVisStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ mem (cfgAddr + 18)
  cur_le : ∀ v < X.card, mem (wsCurStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ mem (cfgAddr + 19)
  used_le : ∀ v < X.card, mem (wsUsedStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ mem (cfgAddr + 19)
  dead_le : ∀ v < X.card, mem (wsDeadStamp rcfg.batch.ws rcfg.batch.nX + v) ≤ mem (cfgAddr + 19)
  ball_s_le : ∀ v < X.card, mem (wsBallStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ mem (cfgAddr + 20)
  live_s_le : ∀ v < X.card, mem (wsLiveStamp rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k + v) ≤ mem (cfgAddr + 21)
  sub_init : BatchSubCfgsInit mem rcfg.batch rcfg.hL
  csr : AdjCsrAt mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X)
  lp : LocalPairsAt mem rcfg.batch.pairBAddr rcfg.batch.aOffAddr rcfg.batch.aLenAddr rcfg.batch.aDataAddr X curPairs X.card
  chunks : ∀ j < rcfg.batch.k,
    ChunkChainAt mem X pLo (mem (cfgAddr + 22)) cLo (mem (cfgAddr + 23))
      (mem (rcfg.batch.accHeadAddr + j)) (mem (rcfg.batch.accTailAddr + j)) (accChunks.getD j [])
  ch_disj : ChunksDisj mem rcfg.batch.accHeadAddr rcfg.batch.k (fun j => (accChunks.getD j []).length)
  frame : ∀ a, ¬ BatchWriteSet rcfg.batch cfgAddr (mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
    mem a = mem0 a

/-- Post-loop state predicate matching `res = routeBatches G X Δ b L rcfg.z rem curPairs (accChunks.map List.flatten) costSoFar`. -/
def RouteLoopPost (mem mem0 : ℕ → ℕ) (X : Finset ℕ) (rcfg : RouteLoopCfg)
    (cfgAddr pLo cLo cHi initDem : ℕ) (tag : ℕ) (res : RouteResult × ℕ) : Prop :=
  (∀ o < 32, (o < 16 ∨ 26 ≤ o) → mem (cfgAddr + o) = mem0 (cfgAddr + o)) ∧
  rcfg.batch.pathHeapIn ≤ mem (cfgAddr + 22) ∧
  mem (cfgAddr + 22) ≤ rcfg.batch.pathHeapIn + 5 * res.2 ∧
  (∀ a, ¬ BatchWriteSet rcfg.batch cfgAddr (mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
    mem a = mem0 a) ∧
  match res.1 with
  | .matched matchings emb =>
      tag = 0 ∧
      ∃ finChunks : List (List (List ((ℕ × ℕ) × List ℕ))),
        finChunks.length = rcfg.batch.k ∧
        (finChunks.map List.flatten).flatten.length ≤ initDem ∧
        (finChunks.map List.flatten).flatten.length ≤ res.2 ∧
        mkMatchedResult (finChunks.map List.flatten) = .matched matchings emb ∧
        (∀ j < rcfg.batch.k, ∃ tailPtr,
          ChunkChainAt mem X pLo (mem (cfgAddr + 22)) cLo cHi
            (mem (rcfg.batch.accHeadAddr + j)) tailPtr (finChunks.getD j []))
  | .cut U =>
      tag = 1 ∧
      mem (cfgAddr + 25) = U.card ∧
      X.card ≤ res.2 ∧
      ∃ ul : List ℕ,
        ul.length = U.card ∧ ul.Nodup ∧
        (∀ x ∈ ul, x < X.card ∧ origOf X x ∈ U) ∧
        (∀ v ∈ U, v ∈ X ∧ locOf X v ∈ ul) ∧
        ListAt mem (wsCutList rcfg.batch.ws rcfg.batch.nX rcfg.batch.m2 rcfg.batch.k) ul

private lemma eval_routeLoopGuard_zero {w : ℕ} {st : State} {cfgAddr R z t curDem tag : ℕ}
    (hw_cfg : cfgAddr + 36 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hr0 : st.regs 0 = cfgAddr) (hr2 : st.regs 2 = R) (hr3 : st.regs 3 = z)
    (hr4 : st.regs 4 = t) (hr5 : st.regs 5 = tag) (hm16 : st.mem (cfgAddr + 16) = curDem)
    (hstop : ¬ (t < R ∧ z < curDem ∧ tag = 0)) :
    routeLoopGuardExpr.eval w st = some 0 := by
  have h1 : (1 : ℕ) < 2 ^ w := by omega
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h16 : (16 : ℕ) < 2 ^ w := by omega
  have h16a : cfgAddr + 16 < 2 ^ w := by omega
  unfold routeLoopGuardExpr
  simp only [Expr.eval, BinOp.eval, hr0, hr2, hr3, hr4, hr5, h16, h16a, h0w, ↓reduceIte,
    Option.map_some, hm16]
  by_cases hA : t < R <;> by_cases hB : z < curDem <;> by_cases hC : tag = 0
  · exact absurd ⟨hA, hB, hC⟩ hstop
  all_goals simp [hA, hB, hC, h0w, h1]

private lemma eval_routeLoopGuard_one {w : ℕ} {st : State} {cfgAddr R z t curDem : ℕ}
    (hw_cfg : cfgAddr + 36 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hr0 : st.regs 0 = cfgAddr) (hr2 : st.regs 2 = R) (hr3 : st.regs 3 = z)
    (hr4 : st.regs 4 = t) (hr5 : st.regs 5 = 0) (hm16 : st.mem (cfgAddr + 16) = curDem)
    (hgo : t < R ∧ z < curDem) :
    routeLoopGuardExpr.eval w st = some 1 := by
  have h1 : (1 : ℕ) < 2 ^ w := by omega
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h16 : (16 : ℕ) < 2 ^ w := by omega
  have h16a : cfgAddr + 16 < 2 ^ w := by omega
  unfold routeLoopGuardExpr
  simp [Expr.eval, BinOp.eval, hr0, hr2, hr3, hr4, hr5, h16, h16a, h0w, h1, hm16, hgo.1, hgo.2]

theorem routeBatchesLoop_ind {w : ℕ} {p : Program}
    {bBatch bSp bBfs bDfs bRes bCurB bBall : ℕ}
    (hbatch_proc : p.procs[bBatch]? = some (runBatchProc bSp bRes bCurB bBall))
    (hsp_proc : p.procs[bSp]? = some (shortPathBlockProc bBfs bDfs))
    (hbfs_proc : p.procs[bBfs]? = some bfsLayersProc)
    (hdfs_proc : p.procs[bDfs]? = some dfsBlockProc)
    (hres_proc : p.procs[bRes]? = some buildResCsrProc)
    (hcurb_proc : p.procs[bCurB]? = some buildCurBProc)
    (hball_proc : p.procs[bBall]? = some (growBallProc bBfs))
    {G : Graph} {X : Finset ℕ} {Δ b L : ℕ}
    {rcfg : RouteLoopCfg} {cfgAddr pLo pHi cLo cHi initDem : ℕ} {mem0 : ℕ → ℕ}
    (hnX : rcfg.batch.nX = X.card) (hm2 : rcfg.batch.m2 = 2 * (G.inside X).length)
    (hd : rcfg.batch.d = routeD Δ b L) (hb : rcfg.batch.b = b)
    (hHb : rcfg.batch.Hbatch = routeHBatch Δ b L) (hhL : routeH Δ b * L = rcfg.hL)
    (hcfg0 : RouteLoopCfgAt mem0 cfgAddr rcfg)
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg)
    (rem : ℕ) :
    ∀ (t : ℕ) (curPairs : List (Finset ℕ × Finset ℕ))
      (accChunks : List (List (List ((ℕ × ℕ) × List ℕ)))) (costSoFar : ℕ) (st0 : State),
      t + rem = rcfg.R →
      let res := routeBatches G X Δ b L rcfg.z rem curPairs (accChunks.map List.flatten) costSoFar
      rcfg.batch.pathHeapIn + 5 * res.2 + 15 * rcfg.batch.nX ≤ pHi →
      RouteLoopInv st0.mem mem0 G X rcfg cfgAddr pLo pHi cLo cHi initDem t curPairs accChunks costSoFar →
      st0.regs 0 = cfgAddr → st0.regs 2 = rcfg.R → st0.regs 3 = rcfg.z →
      st0.regs 4 = t → st0.regs 5 = 0 →
      ∀ ω, ∃ stF cF,
        Runs w p ω
          (.loop routeLoopGuardExpr
            (seqStmts [ .call 5 bBatch [.reg 0], .assign 4 (.bin .add (.reg 4) (.const 1)) ]))
          st0 .normal stF cF ∧
        stF.regs 0 = cfgAddr ∧
        RouteLoopPost stF.mem mem0 X rcfg cfgAddr pLo cLo cHi initDem (stF.regs 5) res ∧
        cF ≤ 2050 * (res.2 - costSoFar) + 25 := by
  induction rem with
  | zero =>
    intro t curPairs accChunks costSoFar st0 ht res _ hinv hr0 hr2 hr3 hr4 hr5 ω
    have hstop : ¬ (t < rcfg.R ∧ rcfg.z < totalDemand curPairs ∧ 0 = 0) := by omega
    have hcond0 := eval_routeLoopGuard_zero hdisj.w_cfg hdisj.w_4 hr0 hr2 hr3 hr4 hr5 hinv.dem_mem hstop
    refine ⟨st0, _, batch_runs_loop_zero hcond0, hr0, ?_, by simp [routeLoopGuardExpr, Expr.size]⟩
    refine ⟨hinv.cfg_ro, hinv.php_lo, hinv.php_hi, hinv.frame, ?_⟩
    dsimp only [res, routeBatches, mkMatchedResult]
    refine ⟨hr5, accChunks, hinv.k_chunks, by have := hinv.dem_inv; omega, hinv.flat_le_cost, rfl, fun j hj => ?_⟩
    exact ⟨st0.mem (rcfg.batch.accTailAddr + j),
      (hinv.chunks j hj).mono_cHi (by have := hinv.chp_hi; omega)⟩
  | succ rem ih =>
    intro t curPairs accChunks costSoFar st0 ht res hpHi_res hinv hr0 hr2 hr3 hr4 hr5 ω
    by_cases hdem_le : totalDemand curPairs ≤ rcfg.z
    · have hstop : ¬ (t < rcfg.R ∧ rcfg.z < totalDemand curPairs ∧ 0 = 0) := by omega
      have hcond0 := eval_routeLoopGuard_zero hdisj.w_cfg hdisj.w_4 hr0 hr2 hr3 hr4 hr5 hinv.dem_mem hstop
      have hres_eq : res = (mkMatchedResult (accChunks.map List.flatten), costSoFar) := by
        dsimp only [res]; unfold routeBatches; simp [hdem_le]
      refine ⟨st0, _, batch_runs_loop_zero hcond0, hr0, ?_, by simp [routeLoopGuardExpr, Expr.size]⟩
      rw [hres_eq]
      refine ⟨hinv.cfg_ro, hinv.php_lo, hinv.php_hi, hinv.frame, ?_⟩
      dsimp only [mkMatchedResult]
      refine ⟨hr5, accChunks, hinv.k_chunks, by have := hinv.dem_inv; omega, hinv.flat_le_cost, rfl, fun j hj => ?_⟩
      exact ⟨st0.mem (rcfg.batch.accTailAddr + j),
        (hinv.chunks j hj).mono_cHi (by have := hinv.chp_hi; omega)⟩
    · have hgo : t < rcfg.R ∧ rcfg.z < totalDemand curPairs := by omega
      have hcond1 := eval_routeLoopGuard_one hdisj.w_cfg hdisj.w_4 hr0 hr2 hr3 hr4 hr5 hinv.dem_mem hgo
      set br := runBatch G X Δ b L curPairs
      have hbr_props := runBatch_props G Δ b L hinv.valid
      have hbr_cost_pos : 1 ≤ br.cost := by
        have h : curPairs.length + 1 ≤ br.cost := hbr_props.1
        omega
      -- Build BatchCfg and BatchDisj for this step with tight upper bound pHiStep = pathHeapCur + 15 * nX
      set cfgT : BatchCfg :=
        { rcfg.batch with
          curDemandIn := totalDemand curPairs
          batchGenIn := st0.mem (cfgAddr + 17)
          bfsGenIn := st0.mem (cfgAddr + 18)
          dfsGenIn := st0.mem (cfgAddr + 19)
          ballGenIn := st0.mem (cfgAddr + 20)
          liveGenIn := st0.mem (cfgAddr + 21)
          pathHeapIn := st0.mem (cfgAddr + 22)
          chunkHeapIn := st0.mem (cfgAddr + 23) }
      have hres_cost_ge : costSoFar + br.cost ≤ res.2 := by
        dsimp only [res]; unfold routeBatches
        rw [ite_eq_right (fun h => absurd h hdem_le)]
        dsimp only
        change costSoFar + br.cost ≤
          (match br.outcome with
           | .cut U => (RouteResult.cut U, costSoFar + br.cost)
           | .matched batchPaths remPairs =>
             routeBatches G X Δ b L rcfg.z rem remPairs
               (List.zipWith (· ++ ·) (accChunks.map List.flatten) batchPaths) (costSoFar + br.cost)).2
        cases h : br.outcome with
        | cut _ => exact le_rfl
        | matched bp rp =>
          dsimp only
          have hadd := routeBatches_cost_add G X Δ b L rcfg.z rem rp
            (List.zipWith (· ++ ·) (accChunks.map List.flatten) bp) 0 (costSoFar + br.cost)
          simp only [Nat.zero_add] at hadd; omega
      set pHiStep := st0.mem (cfgAddr + 22) + 15 * rcfg.batch.nX
      have hpHiStep_le : pHiStep ≤ pHi := by
        have := hinv.php_hi; omega
      have hbDisj0 := hdisj.toBatchDisj (t := t) (curDem := totalDemand curPairs)
        (batchGen := st0.mem (cfgAddr + 17)) (bfsGen := st0.mem (cfgAddr + 18))
        (dfsGen := st0.mem (cfgAddr + 19)) (ballGen := st0.mem (cfgAddr + 20))
        (liveGen := st0.mem (cfgAddr + 21)) (pathHeap := st0.mem (cfgAddr + 22))
        (chunkHeap := st0.mem (cfgAddr + 23))
        (by omega) (le_trans hdisj.hp_lo hinv.php_lo) (by omega)
        hinv.chp_lo hinv.chp_hi hinv.bgen_le hinv.bfs_le hinv.dfs_le hinv.ball_le hinv.live_le
      have hbDisj : BatchDisj w cfgAddr pLo pHiStep cLo cHi rcfg.hL cfgT := by
        have hshrink : ∀ {a l : ℕ}, DisjRange a l pLo (pHi - pLo) → DisjRange a l pLo (pHiStep - pLo) :=
          fun hd => by unfold DisjRange at hd ⊢; omega
        have hshrinkL : ∀ {a l : ℕ}, DisjRange pLo (pHi - pLo) a l → DisjRange pLo (pHiStep - pLo) a l :=
          fun hd => by unfold DisjRange at hd ⊢; omega
        exact
          { hp_pos := hbDisj0.hp_pos, hp_lo := hbDisj0.hp_lo, hp_hi := le_rfl,
            ch_pos := hbDisj0.ch_pos, ch_lo := hbDisj0.ch_lo, ch_hi := hbDisj0.ch_hi,
            ro_off_pb := hbDisj0.ro_off_pb, ro_off_al := hbDisj0.ro_off_al, ro_off_ad := hbDisj0.ro_off_ad,
            ro_off_ah := hbDisj0.ro_off_ah, ro_off_at := hbDisj0.ro_off_at, ro_off_cfg := hbDisj0.ro_off_cfg,
            ro_off_ws := hbDisj0.ro_off_ws, ro_off_hp := hshrink hbDisj0.ro_off_hp, ro_off_ch := hbDisj0.ro_off_ch,
            ro_nb_pb := hbDisj0.ro_nb_pb, ro_nb_al := hbDisj0.ro_nb_al, ro_nb_ad := hbDisj0.ro_nb_ad,
            ro_nb_ah := hbDisj0.ro_nb_ah, ro_nb_at := hbDisj0.ro_nb_at, ro_nb_cfg := hbDisj0.ro_nb_cfg,
            ro_nb_ws := hbDisj0.ro_nb_ws, ro_nb_hp := hshrink hbDisj0.ro_nb_hp, ro_nb_ch := hbDisj0.ro_nb_ch,
            ro_edge_pb := hbDisj0.ro_edge_pb, ro_edge_al := hbDisj0.ro_edge_al, ro_edge_ad := hbDisj0.ro_edge_ad,
            ro_edge_ah := hbDisj0.ro_edge_ah, ro_edge_at := hbDisj0.ro_edge_at, ro_edge_cfg := hbDisj0.ro_edge_cfg,
            ro_edge_ws := hbDisj0.ro_edge_ws, ro_edge_hp := hshrink hbDisj0.ro_edge_hp, ro_edge_ch := hbDisj0.ro_edge_ch,
            ro_ao_pb := hbDisj0.ro_ao_pb, ro_ao_al := hbDisj0.ro_ao_al, ro_ao_ad := hbDisj0.ro_ao_ad,
            ro_ao_ah := hbDisj0.ro_ao_ah, ro_ao_at := hbDisj0.ro_ao_at, ro_ao_cfg := hbDisj0.ro_ao_cfg,
            ro_ao_ws := hbDisj0.ro_ao_ws, ro_ao_hp := hshrink hbDisj0.ro_ao_hp, ro_ao_ch := hbDisj0.ro_ao_ch,
            pb_al := hbDisj0.pb_al, pb_ad := hbDisj0.pb_ad, pb_ah := hbDisj0.pb_ah, pb_at := hbDisj0.pb_at,
            pb_cfg := hbDisj0.pb_cfg, pb_ws := hbDisj0.pb_ws, pb_hp := hshrink hbDisj0.pb_hp, pb_ch := hbDisj0.pb_ch,
            al_ad := hbDisj0.al_ad, al_ah := hbDisj0.al_ah, al_at := hbDisj0.al_at, al_cfg := hbDisj0.al_cfg,
            al_ws := hbDisj0.al_ws, al_hp := hshrink hbDisj0.al_hp, al_ch := hbDisj0.al_ch,
            ad_ah := hbDisj0.ad_ah, ad_at := hbDisj0.ad_at, ad_cfg := hbDisj0.ad_cfg, ad_ws := hbDisj0.ad_ws,
            ad_hp := hshrink hbDisj0.ad_hp, ad_ch := hbDisj0.ad_ch,
            ah_at := hbDisj0.ah_at, ah_cfg := hbDisj0.ah_cfg, ah_ws := hbDisj0.ah_ws,
            ah_hp := hshrink hbDisj0.ah_hp, ah_ch := hbDisj0.ah_ch,
            at_cfg := hbDisj0.at_cfg, at_ws := hbDisj0.at_ws, at_hp := hshrink hbDisj0.at_hp, at_ch := hbDisj0.at_ch,
            cfg_ws := hbDisj0.cfg_ws, cfg_hp := hshrink hbDisj0.cfg_hp, cfg_ch := hbDisj0.cfg_ch,
            ws_hp := hshrink hbDisj0.ws_hp, ws_ch := hbDisj0.ws_ch, hp_ch := hshrinkL hbDisj0.hp_ch,
            w_off := hbDisj0.w_off, w_nb := hbDisj0.w_nb, w_edge := hbDisj0.w_edge, w_ao := hbDisj0.w_ao,
            w_pb := hbDisj0.w_pb, w_al := hbDisj0.w_al, w_ad := hbDisj0.w_ad, w_ah := hbDisj0.w_ah,
            w_at := hbDisj0.w_at, w_cfg := hbDisj0.w_cfg, w_ws := hbDisj0.w_ws,
            w_hp := by have := hbDisj0.w_hp; omega, w_ch := hbDisj0.w_ch,
            w_nX4 := hbDisj0.w_nX4, w_m2 := hbDisj0.w_m2, w_k := hbDisj0.w_k, w_d := hbDisj0.w_d,
            w_hL := hbDisj0.w_hL, w_Hbatch := hbDisj0.w_Hbatch, w_Hbatch_s := hbDisj0.w_Hbatch_s,
            w_bgen := hbDisj0.w_bgen, w_bfsgen := hbDisj0.w_bfsgen, w_dfsgen := hbDisj0.w_dfsgen,
            w_ballgen := hbDisj0.w_ballgen, w_livegen := hbDisj0.w_livegen,
            w_mul := hbDisj0.w_mul, w_b16 := hbDisj0.w_b16, w_4 := hbDisj0.w_4 }
      have hbCfg : BatchCfgAt st0.mem cfgAddr cfgT := by
        rcases hcfg0.1 with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, _⟩
        exact ⟨(hinv.cfg_ro 0 (by decide) (Or.inl (by decide))).trans m0,
          (hinv.cfg_ro 1 (by decide) (Or.inl (by decide))).trans m1,
          (hinv.cfg_ro 2 (by decide) (Or.inl (by decide))).trans m2,
          (hinv.cfg_ro 3 (by decide) (Or.inl (by decide))).trans m3,
          (hinv.cfg_ro 4 (by decide) (Or.inl (by decide))).trans m4,
          (hinv.cfg_ro 5 (by decide) (Or.inl (by decide))).trans m5,
          (hinv.cfg_ro 6 (by decide) (Or.inl (by decide))).trans m6,
          (hinv.cfg_ro 7 (by decide) (Or.inl (by decide))).trans m7,
          (hinv.cfg_ro 8 (by decide) (Or.inl (by decide))).trans m8,
          (hinv.cfg_ro 9 (by decide) (Or.inl (by decide))).trans m9,
          (hinv.cfg_ro 10 (by decide) (Or.inl (by decide))).trans m10,
          (hinv.cfg_ro 11 (by decide) (Or.inl (by decide))).trans m11,
          (hinv.cfg_ro 12 (by decide) (Or.inl (by decide))).trans m12,
          (hinv.cfg_ro 13 (by decide) (Or.inl (by decide))).trans m13,
          (hinv.cfg_ro 14 (by decide) (Or.inl (by decide))).trans m14,
          (hinv.cfg_ro 15 (by decide) (Or.inl (by decide))).trans m15,
          hinv.dem_mem, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hbMC := runBatch_meetsContract (w := w) hbatch_proc hsp_proc hbfs_proc hdfs_proc hres_proc hcurb_proc hball_proc
        G X Δ b L curPairs cfgT pLo pHiStep cLo cHi rcfg.hL accChunks
      have hbPre : (runBatchContract w G X Δ b L curPairs cfgT pLo pHiStep cLo cHi rcfg.hL accChunks).pre
          [cfgAddr] st0.mem :=
        ⟨rfl, hnX, hinv.k_pairs.symm, hm2, hd, hb, hHb, hhL, rfl, hinv.valid, hbCfg, hinv.sub_init,
          hbDisj, hinv.csr, hinv.lp, hinv.iso_le, hinv.ma_le, hinv.vis_le, hinv.cur_le,
          hinv.used_le, hinv.dead_le, hinv.ball_s_le, hinv.live_s_le,
          fun j hj => hinv.chunks j (by rw [← hinv.k_pairs]; exact hj), by rw [hinv.k_pairs]; exact hinv.ch_disj⟩
      have hcallArgs : evalArgs w st0 [.reg 0] = some [cfgAddr] := by simp [evalArgs, Expr.eval, hr0]
      have hcallW : ∀ v ∈ [cfgAddr], v < 2 ^ w := fun v hv => by
        simp only [List.mem_singleton] at hv; subst hv; have := hdisj.w_cfg; omega
      obtain ⟨st1, c1, tag1, hrun1, hpost1, hr1_5, hr1_oth, hc1⟩ :=
        runs_call_of_meetsContract (r := 5) hbMC hcallArgs hcallW hbPre ω
      simp only [runBatchContract, List.getD, List.getElem?_cons_zero, Option.getD_some] at hpost1 hc1
      rcases hpost1 with ⟨htag1, hbOut1, hfr1⟩
      rcases hbOut1 with ⟨hm17, hbfs_lo1, hbfs_hi1, hdfs_lo1, hdfs_hi1, hball_lo1, hball_hi1,
        hlive_lo1, hlive_hi1, hp_lo1, _hp_nX1, hp_cost1, hc_lo1, _hc_hi1,
        hiso1, hma1, hvis1, hcur1, hused1, hdead1, hball_s1, hlive_s1, hsub1, hrest1⟩
      change st0.mem (cfgAddr + 22) ≤ st1.mem (cfgAddr + 22) at hp_lo1
      change st1.mem (cfgAddr + 22) ≤ st0.mem (cfgAddr + 22) + 5 * br.cost at hp_cost1
      have hfr1_step : ∀ a, ¬ BatchWriteSet rcfg.batch cfgAddr (st1.mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
          st1.mem a = st0.mem a := fun a ha => by
        apply hfr1 a
        intro h1; apply ha
        rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_trans hinv.php_lo h1.1, by omega⟩)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))))
      have hfr1_comb : ∀ a, ¬ BatchWriteSet rcfg.batch cfgAddr (st1.mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a →
          st1.mem a = mem0 a := fun a ha => by
        have ha0 : ¬ BatchWriteSet rcfg.batch cfgAddr (st0.mem (cfgAddr + 22) + 15 * rcfg.batch.nX) cLo cHi a := by
          intro h0; apply ha
          rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
          · exact Or.inl h0
          · exact Or.inr (Or.inl h0)
          · exact Or.inr (Or.inr (Or.inl h0))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0.1, by omega⟩)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h0)))))))
        exact (hfr1_step a ha).trans (hinv.frame a ha0)
      have hp_le1 : st1.mem (cfgAddr + 22) + 15 * rcfg.batch.nX ≤ pHi := by
        have hph := hinv.php_hi
        dsimp only [res] at hres_cost_ge hpHi_res
        omega
      have hcfg_ro1 : ∀ o < 32, (o < 16 ∨ 26 ≤ o) → st1.mem (cfgAddr + o) = mem0 (cfgAddr + o) := fun o ho hside => by
        apply hfr1_comb
        have hp_lo' := hdisj.hp_lo; have hc_lo' := hdisj.ch_lo; have hc_hi' := hdisj.ch_hi
        intro hws
        rcases hws with h | h | h | h | h | h | h | h | h
        · exact disj_l (x := cfgAddr + o) hdisj.pb_cfg (by omega) (by omega) h
        · exact disj_l (x := cfgAddr + o) hdisj.al_cfg (by omega) (by omega) h
        · exact disj_l (x := cfgAddr + o) hdisj.ad_cfg (by omega) (by omega) h
        · exact disj_l (x := cfgAddr + o) hdisj.ah_cfg (by omega) (by omega) h
        · exact disj_l (x := cfgAddr + o) hdisj.at_cfg (by omega) (by omega) h
        · omega
        · exact disj_r (x := cfgAddr + o) hdisj.cfg_ws (by omega) (by omega) h
        · exact disj_r (x := cfgAddr + o) hdisj.cfg_hp (by omega) (by omega) ⟨by omega, by omega⟩
        · exact disj_r (x := cfgAddr + o) hdisj.cfg_ch (by omega) (by omega) ⟨h.1, by omega⟩
      -- Step 2 of loop body: reg 4 := reg 4 + 1
      have hr1_0 : st1.regs 0 = cfgAddr := (hr1_oth 0 (by decide)).trans hr0
      have hr1_2 : st1.regs 2 = rcfg.R := (hr1_oth 2 (by decide)).trans hr2
      have hr1_3 : st1.regs 3 = rcfg.z := (hr1_oth 3 (by decide)).trans hr3
      have hr1_4 : st1.regs 4 = t := (hr1_oth 4 (by decide)).trans hr4
      set st2 : State := { st1 with regs := Function.update st1.regs 4 (t + 1) }
      have hinc : ∃ c2, Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) st1 .normal st2 c2 ∧ c2 ≤ 8 := by
        have hw_R := hdisj.w_R; have hw4 := hdisj.w_4
        have h0 : ∃ o s c0, Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) st1 o s c0 ∧
            (o = .normal ∧ s = st2) ∧ 0 + c0 ≤ 8 :=
          runs_assign_le (v := t + 1) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, c2, h, ⟨rfl, rfl⟩, hc2⟩; exact ⟨c2, h, by omega⟩
      rcases hinc with ⟨c2, hrun2, hc2⟩
      have hrunBody : Runs w p ω (seqStmts [.call 5 bBatch [.reg 0], .assign 4 (.bin .add (.reg 4) (.const 1))])
          st0 .normal st2 (c1 + c2 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hrun1, hrun2, rfl⟩)
      -- Split on br.outcome
      dsimp only [cfgT] at hm17 hbfs_lo1 hbfs_hi1 hdfs_lo1 hdfs_hi1 hball_lo1 hball_hi1 hlive_lo1 hlive_hi1 hc_lo1
      dsimp only at hbr_props
      change c1 ≤ argsSize [.reg 0] + batchProgCost br.cost + 1 at hc1
      cases hbr_out : br.outcome with
      | cut U =>
        rw [hbr_out] at htag1 hrest1 hbr_props
        have hres_eq : res = (.cut U, costSoFar + br.cost) := by
          dsimp only [res]; unfold routeBatches
          rw [ite_eq_right (fun h => absurd h hdem_le)]; dsimp only; rw [hbr_out]
        have htag_eq : tag1 = 1 := htag1
        have hcond0 := eval_routeLoopGuard_zero (st := st2) (tag := 1) hdisj.w_cfg hdisj.w_4
          (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_0])
          rfl rfl rfl
          (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_5, htag_eq])
          rfl (by omega)
        refine ⟨st2, _, batch_runs_loop_step hcond1 (by decide) hrunBody (batch_runs_loop_zero hcond0),
          by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_0], ?_, ?_⟩
        · rw [hres_eq]
          refine ⟨hcfg_ro1, le_trans hinv.php_lo hp_lo1, by dsimp only [st2]; have := hinv.php_hi; omega, hfr1_comb, ?_⟩
          have hX_br : X.card + 2 * (G.inside X).length + curPairs.length + 2 ≤ br.cost := hbr_props.2.1
          refine ⟨by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_5, htag_eq],
            hrest1.2.1, by omega, hrest1.2.2⟩
        · rw [hres_eq]; dsimp only [batchProgCost, argsSize, routeLoopGuardExpr, Expr.size] at hc1 hc2 ⊢; omega
      | matched batchPaths remPairs =>
        rw [hbr_out] at htag1 hrest1 hbr_props
        rcases hbr_props with ⟨_, hrem_len, hbp_len, hrem_valid, hrem_dem, hbp_le_cost⟩
        rcases hrest1 with ⟨_, hm16_1, hc_hi_routed1, hlp1, hch1, hchDisj1⟩
        dsimp only [cfgT] at hc_hi_routed1
        change batchPaths.flatten.length ≤ br.cost at hbp_le_cost
        have hres_eq : res = routeBatches G X Δ b L rcfg.z rem remPairs
            (List.zipWith (· ++ ·) (accChunks.map List.flatten) batchPaths) (costSoFar + br.cost) := by
          dsimp only [res]
          conv_lhs => unfold routeBatches
          rw [ite_eq_right (fun h => absurd h hdem_le)]; dsimp only; rw [hbr_out]
        obtain ⟨hnc_len, hnc_getD, hnc_flat⟩ :=
          accChunks_step_flatten accChunks batchPaths (by have := hinv.k_chunks; have := hinv.k_pairs; omega)
        set nextChunks := List.ofFn fun j : Fin accChunks.length =>
          if batchPaths.getD j.1 [] = [] then accChunks.getD j.1 []
          else accChunks.getD j.1 [] ++ [batchPaths.getD j.1 []]
        have hnext_flat_len : (nextChunks.map List.flatten).flatten.length =
            (accChunks.map List.flatten).flatten.length + batchPaths.flatten.length := by
          rw [hnc_flat]
          have hzw : ∀ (xs ys : List (List ((ℕ × ℕ) × List ℕ))), xs.length = ys.length →
              (List.zipWith (· ++ ·) xs ys).flatten.length = xs.flatten.length + ys.flatten.length := by
            intro xs; induction xs with
            | nil => intro ys hy; cases ys with | nil => rfl | cons _ _ => simp at hy
            | cons x xr ihx =>
              intro ys hy; cases ys with
              | nil => simp at hy
              | cons y yr =>
                simp only [List.length_cons, Nat.add_right_cancel_iff] at hy
                simp only [List.zipWith_cons_cons, List.flatten_cons, List.length_append, ihx yr hy]; omega
          exact hzw _ _ (by simp [hinv.k_chunks, hbp_len, hinv.k_pairs])
        have hcsr1 : AdjCsrAt st1.mem rcfg.batch.offAddr rcfg.batch.nbAddr rcfg.batch.edgeAddr X (adjOf G X) := by
          have hp_lo' := hdisj.hp_lo; have hc_lo' := hdisj.ch_lo; have hc_hi' := hdisj.ch_hi
          have hcsr_m2 : adjCsrOff X (adjOf G X) X.card ≤ rcfg.batch.m2 := by rw [adjCsrOff_adjOf_card, hm2]
          exact hinv.csr.congr
            (fun j hj => hfr1_step _ (by
              intro hws; rcases hws with h | h | h | h | h | h | h | h | h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_pb (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_al (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_ad (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_ah (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_at (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_cfg (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_ws (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_hp (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.offAddr + j) hdisj.ro_off_ch (by omega) (by omega) ⟨h.1, by omega⟩))
            (fun j hj => hfr1_step _ (by
              intro hws; rcases hws with h | h | h | h | h | h | h | h | h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_pb (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_al (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_ad (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_ah (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_at (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_cfg (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_ws (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_hp (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.nbAddr + j) hdisj.ro_nb_ch (by omega) (by omega) ⟨h.1, by omega⟩))
            (fun j hj => hfr1_step _ (by
              intro hws; rcases hws with h | h | h | h | h | h | h | h | h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_pb (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_al (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_ad (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_ah (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_at (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_cfg (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_ws (by omega) (by omega) h
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_hp (by omega) (by omega) ⟨by omega, by omega⟩
              · exact disj_r (x := rcfg.batch.edgeAddr + j) hdisj.ro_edge_ch (by omega) (by omega) ⟨h.1, by omega⟩))
        have hbfs_mul : t * (rcfg.batch.k * (rcfg.batch.d + 3)) + rcfg.batch.k * (rcfg.batch.d + 3) =
            (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 3)) := by ring
        have hdfs_mul : t * (rcfg.batch.k * (rcfg.batch.d + 1)) + rcfg.batch.k * (rcfg.batch.d + 1) =
            (t + 1) * (rcfg.batch.k * (rcfg.batch.d + 1)) := by ring
        have hball_mul : t * rcfg.batch.k + rcfg.batch.k = (t + 1) * rcfg.batch.k := by ring
        have hk_rem : remPairs.length = rcfg.batch.k := hrem_len.trans hinv.k_pairs
        have hk_ac : accChunks.length = rcfg.batch.k := hinv.k_chunks
        have hinv2 : RouteLoopInv st1.mem mem0 G X rcfg cfgAddr pLo pHi cLo cHi initDem
            (t + 1) remPairs nextChunks (costSoFar + br.cost) :=
          { k_pairs := hk_rem,
            k_chunks := hnc_len.trans hk_ac,
            valid := hrem_valid,
            dem_inv := by have := hinv.dem_inv; omega,
            flat_le_cost := by have := hinv.flat_le_cost; omega,
            cfg_ro := hcfg_ro1,
            dem_mem := hm16_1,
            bgen_le := by have := hinv.bgen_le; omega,
            bfs_le := by have := hinv.bfs_le; omega,
            dfs_le := by have := hinv.dfs_le; omega,
            ball_le := by have := hinv.ball_le; omega,
            live_le := by have := hinv.live_le; omega,
            php_lo := le_trans hinv.php_lo hp_lo1,
            php_hi := by have := hinv.php_hi; omega,
            chp_lo := le_trans hinv.chp_lo hc_lo1,
            chp_hi := by have := hinv.chp_hi; omega,
            iso_le := hiso1, ma_le := hma1, vis_le := hvis1, cur_le := hcur1,
            used_le := hused1, dead_le := hdead1, ball_s_le := hball_s1, live_s_le := hlive_s1,
            sub_init := hsub1, csr := hcsr1, lp := hlp1,
            chunks := fun j hj => by
              have hj' : j < remPairs.length := by omega
              rw [hnc_getD j (by omega)]
              exact hch1 j hj',
            ch_disj := by
              intro j1 hj1 j2 hj2 hne a ha b hb
              dsimp only at ha hb
              rw [hnc_getD j1 (by omega)] at ha; rw [hnc_getD j2 (by omega)] at hb
              exact hchDisj1 j1 (by omega) j2 (by omega) hne a ha b hb,
            frame := hfr1_comb }
        obtain ⟨stF, cF, hrunF, hrF0, hpostF, hcF⟩ :=
          ih (t + 1) remPairs nextChunks (costSoFar + br.cost) st2 (by omega)
            (by rw [hnc_flat, ← hres_eq]; exact hpHi_res) hinv2
            (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_0])
            (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_2])
            (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_3])
            (by dsimp only [st2]; rw [Function.update_self])
            (by dsimp only [st2]; rw [Function.update_of_ne (by decide), hr1_5, htag1]) ω
        rw [hnc_flat, ← hres_eq] at hpostF hcF
        refine ⟨stF, _, batch_runs_loop_step hcond1 (by decide) hrunBody hrunF, hrF0, hpostF, ?_⟩
        dsimp only [batchProgCost, argsSize, routeLoopGuardExpr, Expr.size] at hc1 hc2 hcF ⊢
        omega


/-- Shrink the `pathHeap` upper limit in `RouteLoopDisj` from `pHi` to `pHi' ≤ pHi`. -/
lemma RouteLoopDisj.shrink_pHi {w cfgAddr pLo pHi pHi' cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (h : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg) (hle : pHi' ≤ pHi) :
    RouteLoopDisj w cfgAddr pLo pHi' cLo cHi rcfg := by
  have hsr : ∀ {a l : ℕ}, DisjRange a l pLo (pHi - pLo) → DisjRange a l pLo (pHi' - pLo) :=
    fun hd => by unfold DisjRange at hd ⊢; omega
  have hsl : ∀ {a l : ℕ}, DisjRange pLo (pHi - pLo) a l → DisjRange pLo (pHi' - pLo) a l :=
    fun hd => by unfold DisjRange at hd ⊢; omega
  exact
    { hp_pos := h.hp_pos, hp_lo := h.hp_lo, ch_pos := h.ch_pos, ch_lo := h.ch_lo, ch_hi := h.ch_hi,
      ro_off_pb := h.ro_off_pb, ro_off_al := h.ro_off_al, ro_off_ad := h.ro_off_ad,
      ro_off_ah := h.ro_off_ah, ro_off_at := h.ro_off_at, ro_off_cfg := h.ro_off_cfg,
      ro_off_ws := h.ro_off_ws, ro_off_hp := hsr h.ro_off_hp, ro_off_ch := h.ro_off_ch,
      ro_nb_pb := h.ro_nb_pb, ro_nb_al := h.ro_nb_al, ro_nb_ad := h.ro_nb_ad,
      ro_nb_ah := h.ro_nb_ah, ro_nb_at := h.ro_nb_at, ro_nb_cfg := h.ro_nb_cfg,
      ro_nb_ws := h.ro_nb_ws, ro_nb_hp := hsr h.ro_nb_hp, ro_nb_ch := h.ro_nb_ch,
      ro_edge_pb := h.ro_edge_pb, ro_edge_al := h.ro_edge_al, ro_edge_ad := h.ro_edge_ad,
      ro_edge_ah := h.ro_edge_ah, ro_edge_at := h.ro_edge_at, ro_edge_cfg := h.ro_edge_cfg,
      ro_edge_ws := h.ro_edge_ws, ro_edge_hp := hsr h.ro_edge_hp, ro_edge_ch := h.ro_edge_ch,
      ro_ao_pb := h.ro_ao_pb, ro_ao_al := h.ro_ao_al, ro_ao_ad := h.ro_ao_ad,
      ro_ao_ah := h.ro_ao_ah, ro_ao_at := h.ro_ao_at, ro_ao_cfg := h.ro_ao_cfg,
      ro_ao_ws := h.ro_ao_ws, ro_ao_hp := hsr h.ro_ao_hp, ro_ao_ch := h.ro_ao_ch,
      pb_al := h.pb_al, pb_ad := h.pb_ad, pb_ah := h.pb_ah, pb_at := h.pb_at,
      pb_cfg := h.pb_cfg, pb_ws := h.pb_ws, pb_hp := hsr h.pb_hp, pb_ch := h.pb_ch,
      al_ad := h.al_ad, al_ah := h.al_ah, al_at := h.al_at, al_cfg := h.al_cfg,
      al_ws := h.al_ws, al_hp := hsr h.al_hp, al_ch := h.al_ch,
      ad_ah := h.ad_ah, ad_at := h.ad_at, ad_cfg := h.ad_cfg, ad_ws := h.ad_ws,
      ad_hp := hsr h.ad_hp, ad_ch := h.ad_ch,
      ah_at := h.ah_at, ah_cfg := h.ah_cfg, ah_ws := h.ah_ws,
      ah_hp := hsr h.ah_hp, ah_ch := h.ah_ch,
      at_cfg := h.at_cfg, at_ws := h.at_ws, at_hp := hsr h.at_hp, at_ch := h.at_ch,
      cfg_ws := h.cfg_ws, cfg_hp := hsr h.cfg_hp, cfg_ch := h.cfg_ch,
      ws_hp := hsr h.ws_hp, ws_ch := h.ws_ch, hp_ch := hsl h.hp_ch,
      orig_pb := h.orig_pb, orig_al := h.orig_al, orig_ad := h.orig_ad,
      orig_ah := h.orig_ah, orig_at := h.orig_at, orig_cfg := h.orig_cfg,
      orig_ws := h.orig_ws, orig_hp := hsr h.orig_hp, orig_ch := h.orig_ch,
      orig_out := h.orig_out, orig_walks := h.orig_walks,
      out_ah := h.out_ah, out_cfg := h.out_cfg, out_ws := h.out_ws,
      out_hp := hsr h.out_hp, out_ch := h.out_ch, out_walks := h.out_walks,
      walks_ah := h.walks_ah, walks_cfg := h.walks_cfg, walks_ws := h.walks_ws,
      walks_hp := hsr h.walks_hp, walks_ch := h.walks_ch,
      w_off := h.w_off, w_nb := h.w_nb, w_edge := h.w_edge, w_pb := h.w_pb,
      w_ao := h.w_ao, w_al := h.w_al, w_ad := h.w_ad, w_ah := h.w_ah,
      w_at := h.w_at, w_cfg := h.w_cfg, w_ws := h.w_ws,
      w_hp := by have := h.w_hp; omega, w_ch := h.w_ch,
      w_orig := h.w_orig, w_out := h.w_out, w_walks := h.w_walks,
      w_bgen := h.w_bgen, w_bfsgen := h.w_bfsgen, w_dfsgen := h.w_dfsgen,
      w_ballgen := h.w_ballgen, w_livegen := h.w_livegen, w_hL := h.w_hL,
      w_d := h.w_d, w_m2 := h.w_m2, w_k := h.w_k, w_Hbatch := h.w_Hbatch,
      w_Hbatch_s := h.w_Hbatch_s, w_mul := h.w_mul, w_b16 := h.w_b16,
      w_nX4 := h.w_nX4, w_R := h.w_R, w_z := h.w_z, w_4 := h.w_4 }

/-- Any address inside `[origVertAddr, origVertAddr + nX)` is outside `BatchWriteSet`. -/
lemma not_batchWriteSet_orig {w cfgAddr pLo pHi pHi' cLo cHi : ℕ} {rcfg : RouteLoopCfg}
    (hdisj : RouteLoopDisj w cfgAddr pLo pHi cLo cHi rcfg) (hp' : pHi' ≤ pHi)
    {j : ℕ} (hj : j < rcfg.batch.nX) :
    ¬ BatchWriteSet rcfg.batch cfgAddr pHi' cLo cHi (rcfg.origVertAddr + j) := by
  intro hws
  have hp_lo := hdisj.hp_lo; have hc_lo := hdisj.ch_lo; have hc_hi := hdisj.ch_hi
  rcases hws with h | h | h | h | h | h | h | h | h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_pb (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_al (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_ad (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_ah (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_at (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_cfg (by omega) (by omega) ⟨by omega, by omega⟩
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_ws (by omega) (by omega) h
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_hp (by omega) (by omega) ⟨by omega, by omega⟩
  · exact disj_r (x := rcfg.origVertAddr + j) hdisj.orig_ch (by omega) (by omega) ⟨h.1, by omega⟩

end MinCostFlow.ExpanderDecomp
