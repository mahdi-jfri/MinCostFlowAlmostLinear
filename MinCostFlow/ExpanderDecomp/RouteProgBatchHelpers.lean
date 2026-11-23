module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Word-RAM Procedure (`runBatch_triple`, `runBatchContract`, `runBatch_meetsContract`)

Verifies `runBatchProc` against `runBatch`:
1. `batchRouteLoop_triple`: loops `i = 0 .. k - 1`, calling `shortPathBlock_meetsContract`,
   `batchAppendChunk_triple`, `batchMarkMatched_triple`, and `batchCompactA_triple`, maintaining
   `LocalPairsAt`, `ChunkChainAt` + `ChunksDisj`, and stamp bounds.
2. `batchBallLoop_triple`: on the failed-batch cut branch, loops `i = 0 .. k - 1` while
   `4 * |U| < |X|`, filtering live terminals via `batchFilterLive_triple`, calling
   `growBall_meetsContract`, and copying each ball to `cutList` via `batchCopyBall_triple`.
3. `batchCutBranch_triple`: builds residual CSR (`buildResCsr_meetsContract`) and sorted remaining
   targets (`buildCurB_meetsContract`), runs `batchBallLoop_triple`, and writes cut outputs.
4. `runBatch_triple`, `runBatchContract`, `runBatch_meetsContract`: assembles the full procedure
   with deterministic step bound `≤ batchProgCost (runBatch G X Δ b L pairs).cost`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Chaining, Frame, and Sub-Config Preservation Helpers -/

lemma batch_runs_seqStmts_append {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {l1 l2 : List Stmt} {st0 st1 st2 : State} {o2 : Outcome} {c1 c2 : ℕ}
    (h1 : l1 ≠ []) (h2 : l2 ≠ [])
    (hr1 : Runs w p ω (seqStmts l1) st0 .normal st1 c1)
    (hr2 : Runs w p ω (seqStmts l2) st1 o2 st2 c2) :
    ∃ c, Runs w p ω (seqStmts (l1 ++ l2)) st0 o2 st2 c ∧ c ≤ c1 + c2 + l1.length := by
  induction l1 generalizing st0 c1 with
  | nil => exact absurd rfl h1
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases l2 with
      | nil => exact absurd rfl h2
      | cons b rest2 =>
        exact ⟨c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hr1, hr2, rfl⟩), by simp⟩
    | cons b rest1 =>
      dsimp only [seqStmts] at hr1
      rcases runs_seq_iff.mp hr1 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
      · cases h
      obtain ⟨c', hrc', hc'⟩ := ih (by simp) hrb
      refine ⟨ca + c' + 1, ?_, by simp only [List.length_cons] at hc' ⊢; omega⟩
      have hne : ((b :: rest1) ++ l2) ≠ [] := by simp
      cases heq : (b :: rest1) ++ l2 with
      | nil => exact absurd heq hne
      | cons x xs =>
        rw [List.cons_append, heq]
        dsimp only [seqStmts]
        rw [← heq]
        exact runs_seq_iff.mpr (Or.inr ⟨sa, ca, c', hra, hrc', rfl⟩)

lemma batch_runs_cond_pos {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s1 s2 : Stmt}
    {st st' : State} {o : Outcome} {v c : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (hs : Runs w p ω s1 st o st' c) :
    Runs w p ω (.cond e s1 s2) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨v, c, he, by simp [hv, hs], rfl⟩

lemma batch_runs_cond_zero {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s1 s2 : Stmt}
    {st st' : State} {o : Outcome} {c : ℕ}
    (he : e.eval w st = some 0) (hs : Runs w p ω s2 st o st' c) :
    Runs w p ω (.cond e s1 s2) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨0, c, he, by simp [hs], rfl⟩

lemma BatchSubCfgsInit.of_agree {mem mem' : ℕ → ℕ} {cfg : BatchCfg} {hL : ℕ}
    (h : BatchSubCfgsInit mem cfg hL)
    (heq : ∀ off < 124,
      off ∉ ({3, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17,
              23, 26, 32, 35, 36, 37, 38, 39, 40,
              48, 50, 52, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72,
              80, 86, 88, 91, 92, 94, 95, 96,
              103, 109, 110, 112, 114, 115, 116, 117, 118, 119, 120} : Finset ℕ) →
      mem' (cfg.ws + off) = mem (cfg.ws + off)) :
    BatchSubCfgsInit mem' cfg hL := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55⟩
  unfold BatchSubCfgsInit wsSpCfg wsBfsCfg wsDfsCfg wsBallCfg wsBfsBallCfg at *
  simp only [Nat.add_assoc] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rwa [heq _ (by omega) (by decide)]

lemma BatchSubCfgsInit.of_outside_124 {mem mem' : ℕ → ℕ} {cfg : BatchCfg} {hL : ℕ}
    (h : BatchSubCfgsInit mem cfg hL)
    (heq : ∀ a, cfg.ws ≤ a → a < cfg.ws + 124 → mem' a = mem a) :
    BatchSubCfgsInit mem' cfg hL :=
  h.of_agree fun off hoff _ => heq (cfg.ws + off) (by omega) (by omega)

lemma BatchSubCfgsInit.of_spWriteSet {mem mem' : ℕ → ℕ} {cfg : BatchCfg}
    {batchGen stopVal srcInPtr srcInLen bfsGen dfsGen heapIn pLo pHi cLo cHi cfgAddr hL w : ℕ}
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hhp_lo : pLo ≤ heapIn) (hhp_hi : heapIn + 10 * cfg.nX ≤ pHi)
    (h : BatchSubCfgsInit mem cfg hL)
    (hfr : ∀ a, ¬ SpWriteSet cfg.nX
      (mkBatchSpCfg cfg batchGen srcInPtr srcInLen bfsGen dfsGen heapIn)
      (mkBatchSpBfsCfg cfg batchGen stopVal)
      (mkBatchSpDfsCfg cfg batchGen stopVal) (wsSpCfg cfg.ws) a → mem' a = mem a) :
    BatchSubCfgsInit mem' cfg hL := by
  have h_ws_hp := hdisj.ws_hp
  unfold DisjRange batchScratchSize at h_ws_hp
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by omega)
  refine h.of_agree fun off hoff hnot => hfr (cfg.ws + off) ?_
  intro hw
  simp only [SpWriteSet, BfsWriteSet, DfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg,
    wsSpCfg, wsBfsCfg, wsDfsCfg, wsIsoStamp, wsSBuf, wsVisStamp, wsDist, wsLayerOff, wsLayerData,
    wsTmpNxt, wsCurStamp, wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList] at hw
  rcases hw with (hw | hw | hw | hw | hw | hw) |
    (hw | hw | hw | hw | hw | hw | hw | hw | hw) | hw | (hw | hw) |
    (hw | hw | hw | hw) | hw | hw | hw
  all_goals
    try (rcases h_ws_hp with x | x <;> omega)
    try omega
  all_goals
    have : off ∈ ({3, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17,
              23, 26, 32, 35, 36, 37, 38, 39, 40,
              48, 50, 52, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72,
              80, 86, 88, 91, 92, 94, 95, 96,
              103, 109, 110, 112, 114, 115, 116, 117, 118, 119, 120} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    exact hnot this

lemma BatchSubCfgsInit.of_ballWriteSet {mem mem' : ℕ → ℕ} {cfg : BatchCfg}
    {liveGen sLen tLen bfsGen ballGen hL : ℕ}
    (h : BatchSubCfgsInit mem cfg hL)
    (hfr : ∀ a, ¬ BallWriteSet cfg.nX
      (mkBatchBallCfg cfg liveGen sLen tLen bfsGen ballGen)
      (mkBatchBallBfsCfg cfg liveGen hL) (wsBallCfg cfg.ws) a → mem' a = mem a) :
    BatchSubCfgsInit mem' cfg hL := by
  refine h.of_agree fun off hoff hnot => hfr (cfg.ws + off) ?_
  intro hw
  simp only [BallWriteSet, mkBatchBallCfg, mkBatchBallBfsCfg, wsBallCfg, wsBfsBallCfg,
    wsVisStamp, wsDist, wsLayerOffS, wsLayerDataS, wsLayerOffT, wsLayerDataT,
    wsTmpNxt, wsBallStamp, wsBallList] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals try omega
  all_goals
    have : off ∈ ({3, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17,
              23, 26, 32, 35, 36, 37, 38, 39, 40,
              48, 50, 52, 61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72,
              80, 86, 88, 91, 92, 94, 95, 96,
              103, 109, 110, 112, 114, 115, 116, 117, 118, 119, 120} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    exact hnot this

lemma batch_spWriteSet_in_ws_or_hp {cfg : BatchCfg}
    {batchGen stopVal srcInPtr srcInLen bfsGen dfsGen heapIn a : ℕ}
    (hw : SpWriteSet cfg.nX
      (mkBatchSpCfg cfg batchGen srcInPtr srcInLen bfsGen dfsGen heapIn)
      (mkBatchSpBfsCfg cfg batchGen stopVal)
      (mkBatchSpDfsCfg cfg batchGen stopVal) (wsSpCfg cfg.ws) a) :
    (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨
    (heapIn ≤ a ∧ a < heapIn + 10 * cfg.nX) := by
  simp only [SpWriteSet, BfsWriteSet, DfsWriteSet, mkBatchSpCfg, mkBatchSpBfsCfg, mkBatchSpDfsCfg,
    wsSpCfg, wsBfsCfg, wsDfsCfg, wsIsoStamp, wsSBuf, wsVisStamp, wsDist, wsLayerOff, wsLayerData,
    wsTmpNxt, wsCurStamp, wsCurPtr, wsUsedStamp, wsDeadStamp, wsStkVert, wsStkEdge, wsUsedList,
    batchScratchSize] at hw ⊢
  rcases hw with (hw | hw | hw | hw | hw | hw) |
    (hw | hw | hw | hw | hw | hw | hw | hw | hw) | hw | (hw | hw) |
    (hw | hw | hw | hw) | hw | hw | hw <;> omega

lemma batch_ballWriteSet_in_ws {cfg : BatchCfg}
    {liveGen sLen tLen bfsGen ballGen hL a : ℕ}
    (hw : BallWriteSet cfg.nX
      (mkBatchBallCfg cfg liveGen sLen tLen bfsGen ballGen)
      (mkBatchBallBfsCfg cfg liveGen hL) (wsBallCfg cfg.ws) a) :
    cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k := by
  simp only [BallWriteSet, mkBatchBallCfg, mkBatchBallBfsCfg, wsBallCfg, wsBfsBallCfg,
    wsVisStamp, wsDist, wsLayerOffS, wsLayerDataS, wsLayerOffT, wsLayerDataT,
    wsTmpNxt, wsBallStamp, wsBallList, batchScratchSize] at hw ⊢
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;> omega

lemma batch_resCsrWriteSet_in_ws {cfg : BatchCfg} {a : ℕ}
    (hw : ResCsrWriteSet cfg.nX cfg.m2 (wsResOff cfg.ws cfg.nX) (wsResNb cfg.ws cfg.nX) a) :
    cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k := by
  simp only [ResCsrWriteSet, wsResOff, wsResNb, batchScratchSize] at hw ⊢
  rcases hw with hw | hw <;> omega

lemma batch_curBWriteSet_in_ws {cfg : BatchCfg} {a : ℕ}
    (hw : CurBWriteSet cfg.nX cfg.k
      (wsBOff cfg.ws cfg.nX cfg.m2) (wsBLen cfg.ws cfg.nX cfg.m2 cfg.k)
      (wsBData cfg.ws cfg.nX cfg.m2 cfg.k) (wsBCur cfg.ws cfg.nX cfg.m2 cfg.k) a) :
    cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k := by
  simp only [CurBWriteSet, wsBOff, wsBLen, wsBData, wsBCur, batchScratchSize] at hw ⊢
  rcases hw with hw | hw | hw | hw <;> omega

lemma validTerminalPairs_set_sdiff {X : Finset ℕ}
    {ps : List (Finset ℕ × Finset ℕ)} (hvalid : ValidTerminalPairs X ps)
    {i : ℕ} (hi : i < ps.length) {ML MR : Finset ℕ}
    (hML : ML ⊆ (ps[i]'hi).1) (hMR : MR ⊆ (ps[i]'hi).2) (hcard : ML.card = MR.card) :
    ValidTerminalPairs X (ps.set i ((ps[i]'hi).1 \ ML, (ps[i]'hi).2 \ MR)) := by
  rcases hvalid with ⟨hsub, hpw⟩
  refine ⟨?_, ?_⟩
  · intro ab hab
    rw [List.mem_iff_getElem] at hab
    rcases hab with ⟨j, hj, rfl⟩
    simp only [List.length_set] at hj
    by_cases hji : j = i
    · subst hji; simp only [List.getElem_set_self]
      have h0 := hsub (ps[j]'hi) (List.getElem_mem hi)
      have h1 := Finset.card_sdiff_add_card_eq_card hML
      have h2 := Finset.card_sdiff_add_card_eq_card hMR
      exact ⟨Finset.Subset.trans Finset.sdiff_subset h0.1,
             Finset.Subset.trans Finset.sdiff_subset h0.2.1, by omega⟩
    · simp only [List.getElem_set_ne (Ne.symm hji)]
      exact hsub (ps[j]'hj) (List.getElem_mem hj)
  · have hflat_len : ∀ l : List (Finset ℕ × Finset ℕ),
        (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons _ _ ih => simp [List.flatMap_cons, ih]; omega
    have hflat_get : ∀ (l : List (Finset ℕ × Finset ℕ)) (t : ℕ) (ht : t < (l.flatMap fun p => [p.1, p.2]).length),
        (l.flatMap fun p => [p.1, p.2])[t]'ht =
          if t % 2 = 0 then (l[t / 2]'(by rw [hflat_len] at ht; omega)).1
          else (l[t / 2]'(by rw [hflat_len] at ht; omega)).2 := by
      intro l
      induction l with
      | nil => intro t ht; simp at ht
      | cons p rest ih =>
        intro t ht
        match t with
        | 0 => simp [List.flatMap_cons]
        | 1 => simp [List.flatMap_cons]
        | t + 2 =>
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
          have ht' : t < (rest.flatMap fun p => [p.1, p.2]).length := by
            rw [hflat_len] at ht ⊢; simp only [List.length_cons] at ht; omega
          rw [ih t ht']
          have hmod : (t + 2) % 2 = t % 2 := by omega
          have hdiv : (t + 2) / 2 = t / 2 + 1 := by omega
          simp [hmod, hdiv]
    rw [List.pairwise_iff_getElem] at hpw ⊢
    intro a b ha hb hab
    rw [hflat_get _ a ha, hflat_get _ b hb]
    have ha0 : a < (ps.flatMap fun p => [p.1, p.2]).length := by
      rw [hflat_len] at ha ⊢; simp only [List.length_set] at ha; exact ha
    have hb0 : b < (ps.flatMap fun p => [p.1, p.2]).length := by
      rw [hflat_len] at hb ⊢; simp only [List.length_set] at hb; exact hb
    have horig := hpw a b ha0 hb0 hab
    rw [hflat_get _ a ha0, hflat_get _ b hb0] at horig
    have hmono : ∀ (t : ℕ) (ht : t < (ps.set i ((ps[i]'hi).1 \ ML, (ps[i]'hi).2 \ MR)).length) (m : ℕ),
        (if m = 0 then ((ps.set i ((ps[i]'hi).1 \ ML, (ps[i]'hi).2 \ MR))[t]'ht).1
         else ((ps.set i ((ps[i]'hi).1 \ ML, (ps[i]'hi).2 \ MR))[t]'ht).2) ⊆
        (if m = 0 then (ps[t]'(by simp at ht; exact ht)).1
         else (ps[t]'(by simp at ht; exact ht)).2) := by
      intro t ht m
      by_cases hti : t = i
      · subst hti; simp only [List.getElem_set_self]
        split_ifs <;> exact Finset.sdiff_subset
      · simp only [List.getElem_set_ne (Ne.symm hti)]; exact le_rfl
    exact Disjoint.mono (hmono (a / 2) _ (a % 2)) (hmono (b / 2) _ (b % 2)) horig

lemma validTerminalPairs_sum_card_le {X : Finset ℕ} {ps : List (Finset ℕ × Finset ℕ)}
    (hvalid : ValidTerminalPairs X ps) :
    (ps.map fun ab => ab.1.card + ab.2.card).sum ≤ X.card := by
  have hrt : RouteTerminalPairs X ps := routeTerminalPairs_of_validTerminalPairs hvalid
  have hgen : ∀ (l : List (Finset ℕ × Finset ℕ)),
      RouteTerminalPairs X l →
      (l.map fun ab => ab.1.card + ab.2.card).sum =
        (l.foldr (fun (ab : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (ab.1 ∪ ab.2) ∪ acc) ∅).card ∧
      l.foldr (fun (ab : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (ab.1 ∪ ab.2) ∪ acc) ∅ ⊆ X := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons ab rest ih =>
      intro hv
      rcases hv with ⟨hmem, hpw⟩
      rw [List.pairwise_cons] at hpw
      have hv_rest : RouteTerminalPairs X rest :=
        ⟨fun p hp => hmem p (List.mem_cons_of_mem _ hp), hpw.2⟩
      obtain ⟨hsum, hsub_rest⟩ := ih hv_rest
      have hdisj_fold : ∀ (l' : List (Finset ℕ × Finset ℕ)),
          (∀ r ∈ l', Disjoint (ab.1 ∪ ab.2) (r.1 ∪ r.2)) →
          Disjoint (ab.1 ∪ ab.2)
            (l'.foldr (fun (p : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (p.1 ∪ p.2) ∪ acc) ∅) := by
        intro l'
        induction l' with
        | nil => intro _; simp
        | cons q qs ihq =>
          intro hall
          simp only [List.foldr_cons]
          exact Finset.disjoint_union_right.mpr
            ⟨hall q List.mem_cons_self, ihq fun r hr => hall r (List.mem_cons_of_mem _ hr)⟩
      have hdf := hdisj_fold rest hpw.1
      have hab := hmem ab List.mem_cons_self
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, List.foldr_cons,
          Finset.card_union_of_disjoint hdf, Finset.card_union_of_disjoint hab.2.2.2, hsum]
      · simp only [List.foldr_cons]
        exact Finset.union_subset (Finset.union_subset hab.1 hab.2.1) hsub_rest
  obtain ⟨heq, hsub⟩ := hgen ps hrt
  rw [heq]; exact Finset.card_le_card hsub

lemma totalDemand_le_card_X {X : Finset ℕ} {ps : List (Finset ℕ × Finset ℕ)}
    (hvalid : ValidTerminalPairs X ps) : totalDemand ps ≤ X.card := by
  have := two_mul_totalDemand_le (routeTerminalPairs_of_validTerminalPairs hvalid)
  omega

lemma sort_inter_map_locOf {X A V : Finset ℕ} (hAX : A ⊆ X) (_hVX : V ⊆ X) :
    ((A.sort (· ≤ ·)).map (locOf X)).filter (fun v => decide (origOf X v ∈ V)) =
    ((A ∩ V).sort (· ≤ ·)).map (locOf X) := by
  have hAV : A ∩ V = A \ (X \ V) := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro ⟨hA, hV⟩; exact ⟨hA, fun h => h.2 hV⟩
    · intro ⟨hA, hnot⟩
      refine ⟨hA, ?_⟩
      by_contra hV; exact hnot ⟨hAX hA, hV⟩
  rw [hAV, sort_sdiff_map_locOf hAX]
  refine List.filter_congr fun v hv => ?_
  rw [List.mem_map] at hv
  rcases hv with ⟨u, hu, rfl⟩
  have huX : u ∈ X := hAX ((Finset.mem_sort (· ≤ ·)).mp hu)
  simp [origOf_locOf huX, huX]

/-! ## 2. Routing Loop Verification (`batchRouteLoop_triple`) -/

structure BatchRouteInv (mem mem0 : ℕ → ℕ) (G : Graph) (X : Finset ℕ)
    (cfg : BatchCfg) (cfgAddr pLo pHi cLo cHi hL : ℕ)
    (pairs curPairs : List (Finset ℕ × Finset ℕ))
    (i : ℕ) (V M_acc : Finset ℕ)
    (accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ)))
    (bfsGen dfsGen pathHeap chunkHeap routed : ℕ) : Prop where
  cur_len : curPairs.length = pairs.length
  cur_drop : curPairs.drop i = pairs.drop i
  cur_valid : ValidTerminalPairs X curPairs
  V_sub : V ⊆ X
  M_sub : M_acc ⊆ X
  M_disj : ∀ j (_hij : i ≤ j) (hjk : j < curPairs.length), Disjoint M_acc (curPairs[j]'hjk).1
  routed_le : routed + totalDemand (pairs.drop i) ≤ cfg.curDemandIn
  bgen_lo : cfg.bfsGenIn ≤ bfsGen
  bgen_hi : bfsGen ≤ cfg.bfsGenIn + i * (cfg.d + 1)
  dgen_lo : cfg.dfsGenIn ≤ dfsGen
  dgen_hi : dfsGen ≤ cfg.dfsGenIn + i * (cfg.d + 1)
  php_lo : cfg.pathHeapIn ≤ pathHeap
  php_hi : pathHeap ≤ cfg.pathHeapIn + 5 * (X \ V).card
  chp_lo : cfg.chunkHeapIn ≤ chunkHeap
  chp_hi : chunkHeap ≤ cfg.chunkHeapIn + 2 * routed
  csr : AdjCsrAt mem cfg.offAddr cfg.nbAddr cfg.edgeAddr X (adjOf G X)
  lp : LocalPairsAt mem cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X curPairs X.card
  iso_ok : ∀ v < X.card, mem (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔ origOf X v ∈ V
  iso_le : ∀ v < X.card, mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1
  ma_ok : ∀ v < X.card, mem (wsMatchAStamp cfg.ws cfg.nX + v) = cfg.batchGenIn + 1 ↔ origOf X v ∈ M_acc
  ma_le : ∀ v < X.card, mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1
  vis_le : ∀ v < X.card, mem (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen
  cur_le : ∀ v < X.card, mem (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen
  used_le : ∀ v < X.card, mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen
  dead_le : ∀ v < X.card, mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen
  ball_le : ∀ v < X.card, mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.ballGenIn
  live_le : ∀ v < X.card, mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) ≤ cfg.liveGenIn
  sub_init : BatchSubCfgsInit mem cfg hL
  chunks : ∀ j < pairs.length,
    ChunkChainAt mem X pLo pathHeap cLo chunkHeap
      (mem (cfg.accHeadAddr + j)) (mem (cfg.accTailAddr + j)) (accCur j)
  chunks_disj : ChunksDisj mem cfg.accHeadAddr pairs.length (fun j => (accCur j).length)
  frame : ∀ a, ¬ BatchWriteSet cfg cfgAddr pHi cLo cHi a → mem a = mem0 a
  cfg_ro : ∀ o < 26, mem (cfgAddr + o) = mem0 (cfgAddr + o)

@[expose] def BatchRouteRegs (regs : ℕ → ℕ) (cfg : BatchCfg) (cfgAddr : ℕ)
    (bfsGen dfsGen pathHeap chunkHeap i routed : ℕ) : Prop :=
  regs 0 = cfgAddr ∧ regs 1 = cfg.nX ∧ regs 2 = cfg.k ∧
  regs 8 = cfg.pairBAddr ∧ regs 9 = cfg.aOffAddr ∧ regs 10 = cfg.aLenAddr ∧
  regs 11 = cfg.aDataAddr ∧ regs 12 = cfg.accHeadAddr ∧ regs 13 = cfg.accTailAddr ∧
  regs 14 = cfg.ws ∧ regs 15 = wsSpCfg cfg.ws ∧ regs 16 = wsMatchAStamp cfg.ws cfg.nX ∧
  regs 17 = cfg.batchGenIn + 1 ∧ regs 18 = bfsGen ∧ regs 19 = dfsGen ∧
  regs 20 = pathHeap ∧ regs 21 = chunkHeap ∧ regs 29 = i ∧ regs 30 = routed ∧
  regs 31 = wsBfsCfg cfg.ws ∧ regs 32 = wsDfsCfg cfg.ws

lemma batchRouteSetup_triple {w : ℕ} {p : Program}
    {cfg : BatchCfg} {aOff_i aLen_i bfsGen dfsGen pathHeap i : ℕ}
    (hw_ws : cfg.ws + 124 < 2 ^ w) (hw_ao : cfg.aOffAddr + i < 2 ^ w)
    (hw_al : cfg.aLenAddr + i < 2 ^ w) (hw_ab : cfg.aDataAddr + aOff_i < 2 ^ w)
    (_hw_alen : aLen_i < 2 ^ w) (_hw_bg : cfg.batchGenIn + 1 < 2 ^ w)
    (_hw_bfs : bfsGen < 2 ^ w) (_hw_dfs : dfsGen < 2 ^ w)
    (_hw_hp : pathHeap < 2 ^ w) (hw_i1 : i + 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    {st0 : State}
    (hao : st0.mem (cfg.aOffAddr + i) = aOff_i) (hal : st0.mem (cfg.aLenAddr + i) = aLen_i)
    (hr9 : st0.regs 9 = cfg.aOffAddr) (hr10 : st0.regs 10 = cfg.aLenAddr)
    (hr11 : st0.regs 11 = cfg.aDataAddr) (hr15 : st0.regs 15 = wsSpCfg cfg.ws)
    (hr17 : st0.regs 17 = cfg.batchGenIn + 1) (hr18 : st0.regs 18 = bfsGen)
    (hr19 : st0.regs 19 = dfsGen) (hr20 : st0.regs 20 = pathHeap)
    (hr29 : st0.regs 29 = i) (hr31 : st0.regs 31 = wsBfsCfg cfg.ws)
    (hr32 : st0.regs 32 = wsDfsCfg cfg.ws) :
    ∀ ω,
      ∃ stA cA,
        Runs w p ω
          (seqStmts
            [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
            , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
            , .store (.bin .add (.reg 15) (.const 3)) (.reg 17)
            , .store (.bin .add (.reg 15) (.const 6)) (.reg 23)
            , .store (.bin .add (.reg 15) (.const 7)) (.reg 24)
            , .store (.bin .add (.reg 15) (.const 9)) (.reg 18)
            , .store (.bin .add (.reg 15) (.const 10)) (.reg 19)
            , .store (.bin .add (.reg 15) (.const 11)) (.reg 20)
            , .store (.bin .add (.reg 31) (.const 3)) (.reg 17)
            , .store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 29) (.const 1))
            , .store (.bin .add (.reg 32) (.const 4)) (.reg 17)
            , .store (.bin .add (.reg 32) (.const 6)) (.bin .add (.reg 29) (.const 1)) ])
          st0 .normal stA cA ∧
        stA.regs = Function.update (Function.update st0.regs 23 (cfg.aDataAddr + aOff_i)) 24 aLen_i ∧
        stA.mem (wsSpCfg cfg.ws + 3) = cfg.batchGenIn + 1 ∧
        stA.mem (wsSpCfg cfg.ws + 6) = cfg.aDataAddr + aOff_i ∧
        stA.mem (wsSpCfg cfg.ws + 7) = aLen_i ∧
        stA.mem (wsSpCfg cfg.ws + 9) = bfsGen ∧
        stA.mem (wsSpCfg cfg.ws + 10) = dfsGen ∧
        stA.mem (wsSpCfg cfg.ws + 11) = pathHeap ∧
        stA.mem (wsBfsCfg cfg.ws + 3) = cfg.batchGenIn + 1 ∧
        stA.mem (wsBfsCfg cfg.ws + 6) = i + 1 ∧
        stA.mem (wsDfsCfg cfg.ws + 4) = cfg.batchGenIn + 1 ∧
        stA.mem (wsDfsCfg cfg.ws + 6) = i + 1 ∧
        (∀ a, a ≠ wsSpCfg cfg.ws + 3 → a ≠ wsSpCfg cfg.ws + 6 → a ≠ wsSpCfg cfg.ws + 7 →
              a ≠ wsSpCfg cfg.ws + 9 → a ≠ wsSpCfg cfg.ws + 10 → a ≠ wsSpCfg cfg.ws + 11 →
              a ≠ wsBfsCfg cfg.ws + 3 → a ≠ wsBfsCfg cfg.ws + 6 →
              a ≠ wsDfsCfg cfg.ws + 4 → a ≠ wsDfsCfg cfg.ws + 6 → stA.mem a = st0.mem a) ∧
        cA ≤ 110 := by
  intro ω
  have hsp_w : wsSpCfg cfg.ws + 12 < 2 ^ w := by simp [wsSpCfg]; omega
  have hbfs_w : wsBfsCfg cfg.ws + 7 < 2 ^ w := by simp [wsBfsCfg]; omega
  have hdfs_w : wsDfsCfg cfg.ws + 7 < 2 ^ w := by simp [wsDfsCfg]; omega
  set aBase := cfg.aDataAddr + aOff_i
  set regs1 := Function.update (Function.update st0.regs 23 aBase) 24 aLen_i
  set mem1 := Function.update (Function.update (Function.update (Function.update st0.mem
    (wsSpCfg cfg.ws + 3) (cfg.batchGenIn + 1)) (wsSpCfg cfg.ws + 6) aBase)
    (wsSpCfg cfg.ws + 7) aLen_i) (wsSpCfg cfg.ws + 9) bfsGen
  set st1 : State := { mem := mem1, regs := regs1, pos := st0.pos }
  have hr1 : ∃ c1,
      Runs w p ω
        (seqStmts
          [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
          , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
          , .store (.bin .add (.reg 15) (.const 3)) (.reg 17)
          , .store (.bin .add (.reg 15) (.const 6)) (.reg 23)
          , .store (.bin .add (.reg 15) (.const 7)) (.reg 24)
          , .store (.bin .add (.reg 15) (.const 9)) (.reg 18) ])
        st0 .normal st1 c1 ∧ c1 ≤ 50 := by
    have h0' : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
            , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
            , .store (.bin .add (.reg 15) (.const 3)) (.reg 17)
            , .store (.bin .add (.reg 15) (.const 6)) (.reg 23)
            , .store (.bin .add (.reg 15) (.const 7)) (.reg 24)
            , .store (.bin .add (.reg 15) (.const 9)) (.reg 18) ])
          st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 50 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := aBase)
        (by simp [Expr.eval, BinOp.eval, hr11, hr9, hr29, hw_ao, hao, hw_ab, aBase]) ?_
      refine runs_seq_assign_le (v := aLen_i)
        (by simp [Expr.eval, BinOp.eval, hr10, hr29, hw_al, hal]) ?_
      refine runs_seq_store_le (x := wsSpCfg cfg.ws + 3) (v := cfg.batchGenIn + 1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsSpCfg cfg.ws + 6) (v := aBase) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsSpCfg cfg.ws + 7) (v := aLen_i) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := wsSpCfg cfg.ws + 9) (v := bfsGen) (by eval_expr) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, c1, h, ⟨rfl, rfl⟩, hc1⟩; exact ⟨c1, h, by omega⟩
  set mem2 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update mem1
      (wsSpCfg cfg.ws + 10) dfsGen) (wsSpCfg cfg.ws + 11) pathHeap)
      (wsBfsCfg cfg.ws + 3) (cfg.batchGenIn + 1)) (wsBfsCfg cfg.ws + 6) (i + 1))
      (wsDfsCfg cfg.ws + 4) (cfg.batchGenIn + 1)) (wsDfsCfg cfg.ws + 6) (i + 1)
  set st2 : State := { mem := mem2, regs := regs1, pos := st0.pos }
  have hr2 : ∃ c2,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 15) (.const 10)) (.reg 19)
          , .store (.bin .add (.reg 15) (.const 11)) (.reg 20)
          , .store (.bin .add (.reg 31) (.const 3)) (.reg 17)
          , .store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 29) (.const 1))
          , .store (.bin .add (.reg 32) (.const 4)) (.reg 17)
          , .store (.bin .add (.reg 32) (.const 6)) (.bin .add (.reg 29) (.const 1)) ])
        st1 .normal st2 c2 ∧ c2 ≤ 50 := by
    have h1_15 : st1.regs 15 = wsSpCfg cfg.ws := by simp [st1, regs1, hr15]
    have h1_17 : st1.regs 17 = cfg.batchGenIn + 1 := by simp [st1, regs1, hr17]
    have h1_19 : st1.regs 19 = dfsGen := by simp [st1, regs1, hr19]
    have h1_20 : st1.regs 20 = pathHeap := by simp [st1, regs1, hr20]
    have h1_29 : st1.regs 29 = i := by simp [st1, regs1, hr29]
    have h1_31 : st1.regs 31 = wsBfsCfg cfg.ws := by simp [st1, regs1, hr31]
    have h1_32 : st1.regs 32 = wsDfsCfg cfg.ws := by simp [st1, regs1, hr32]
    have h0' : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 15) (.const 10)) (.reg 19)
            , .store (.bin .add (.reg 15) (.const 11)) (.reg 20)
            , .store (.bin .add (.reg 31) (.const 3)) (.reg 17)
            , .store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 29) (.const 1))
            , .store (.bin .add (.reg 32) (.const 4)) (.reg 17)
            , .store (.bin .add (.reg 32) (.const 6)) (.bin .add (.reg 29) (.const 1)) ])
          st1 o s c ∧ (o = .normal ∧ s = st2) ∧ 0 + c ≤ 50 := by
      dsimp only [seqStmts]
      refine runs_seq_store_le (x := wsSpCfg cfg.ws + 10) (v := dfsGen) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsSpCfg cfg.ws + 11) (v := pathHeap) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsBfsCfg cfg.ws + 3) (v := cfg.batchGenIn + 1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsBfsCfg cfg.ws + 6) (v := i + 1) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := wsDfsCfg cfg.ws + 4) (v := cfg.batchGenIn + 1) (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (x := wsDfsCfg cfg.ws + 6) (v := i + 1) (by eval_expr) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, c2, h, ⟨rfl, rfl⟩, hc2⟩; exact ⟨c2, h, by omega⟩
  rcases hr1 with ⟨c1, hrun1, hc1⟩
  rcases hr2 with ⟨c2, hrun2, hc2⟩
  obtain ⟨cA, hrunA, hcA⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun1 hrun2
  refine ⟨st2, cA, hrunA, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp at hcA; omega⟩
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · simp only [st2, mem2, mem1, wsSpCfg, wsBfsCfg, wsDfsCfg]
    rw [Function.update_self]
  · intro a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp only [st2, mem2, mem1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8,
      Function.update_of_ne h9, Function.update_of_ne h10]

lemma pathListAt_mono_lo {mem : ℕ → ℕ} {X : Finset ℕ} {lo lo' hi head : ℕ}
    {ps : List ((ℕ × ℕ) × List ℕ)} (hle : lo' ≤ lo)
    (h : PathListAt mem X lo hi head ps) : PathListAt mem X lo' hi head ps := by
  induction ps generalizing head with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨⟨s, t⟩, es⟩
    rcases h with ⟨hlo, hhi, hne, hsX, htX, hm0, hm1, hwlo, hwhi, hseq, hrest⟩
    exact ⟨by omega, hhi, hne, hsX, htX, hm0, hm1, by omega, hwhi, hseq, ih hrest⟩

lemma batchRouteLoadSp_triple {w : ℕ} {p : Program}
    {spCfgAddr spHead pathHeap1 bfsGen1 dfsGen1 routed spLen : ℕ}
    (hw_sp : spCfgAddr + 20 < 2 ^ w) (hw_r : routed + spLen < 2 ^ w)
    (hw17 : 17 < 2 ^ w) {stB : State}
    (hr15 : stB.regs 15 = spCfgAddr) (hr25 : stB.regs 25 = spLen) (hr30 : stB.regs 30 = routed)
    (hm12 : stB.mem (spCfgAddr + 12) = spHead) (hm14 : stB.mem (spCfgAddr + 14) = pathHeap1)
    (hm16 : stB.mem (spCfgAddr + 16) = bfsGen1) (hm17 : stB.mem (spCfgAddr + 17) = dfsGen1) :
    ∀ ω,
      let stC : State :=
        { mem := stB.mem
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update stB.regs 22 spHead) 20 pathHeap1) 18 bfsGen1) 19 dfsGen1)
            30 (routed + spLen)
          pos := stB.pos }
      ∃ cC,
        Runs w p ω
          (seqStmts
            [ .assign 22 (.load (.bin .add (.reg 15) (.const 12)))
            , .assign 20 (.load (.bin .add (.reg 15) (.const 14)))
            , .assign 18 (.load (.bin .add (.reg 15) (.const 16)))
            , .assign 19 (.load (.bin .add (.reg 15) (.const 17)))
            , .assign 30 (.bin .add (.reg 30) (.reg 25)) ])
          stB .normal stC cC ∧ cC ≤ 40 := by
  intro ω
  set stC : State :=
    { mem := stB.mem
      regs := Function.update (Function.update (Function.update (Function.update
        (Function.update stB.regs 22 spHead) 20 pathHeap1) 18 bfsGen1) 19 dfsGen1)
        30 (routed + spLen)
      pos := stB.pos }
  have h0' : ∃ o s c,
      Runs w p ω
        (seqStmts
          [ .assign 22 (.load (.bin .add (.reg 15) (.const 12)))
          , .assign 20 (.load (.bin .add (.reg 15) (.const 14)))
          , .assign 18 (.load (.bin .add (.reg 15) (.const 16)))
          , .assign 19 (.load (.bin .add (.reg 15) (.const 17)))
          , .assign 30 (.bin .add (.reg 30) (.reg 25)) ])
        stB o s c ∧ (o = .normal ∧ s = stC) ∧ 0 + c ≤ 40 := by
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := spHead)
      (by simp [Expr.eval, BinOp.eval, hr15, show 12 < 2 ^ w by omega, show spCfgAddr + 12 < 2 ^ w by omega, hm12]) ?_
    refine runs_seq_assign_le (v := pathHeap1)
      (by simp [Expr.eval, BinOp.eval, hr15, show 14 < 2 ^ w by omega, show spCfgAddr + 14 < 2 ^ w by omega, hm14]) ?_
    refine runs_seq_assign_le (v := bfsGen1)
      (by simp [Expr.eval, BinOp.eval, hr15, show 16 < 2 ^ w by omega, show spCfgAddr + 16 < 2 ^ w by omega, hm16]) ?_
    refine runs_seq_assign_le (v := dfsGen1)
      (by simp [Expr.eval, BinOp.eval, hr15, hw17, show spCfgAddr + 17 < 2 ^ w by omega, hm17]) ?_
    refine runs_assign_le (v := routed + spLen)
      (by simp [Expr.eval, BinOp.eval, hr30, hr25, hw_r]) ⟨rfl, rfl⟩ (by wram_cost)
  rcases h0' with ⟨_, _, cC, hrun, ⟨rfl, rfl⟩, hcC⟩
  exact ⟨cC, hrun, by omega⟩


@[expose] def batchRouteStepSpStmts (bSp : ℕ) : List Stmt :=
  [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
  , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
  , .store (.bin .add (.reg 15) (.const 3)) (.reg 17)
  , .store (.bin .add (.reg 15) (.const 6)) (.reg 23)
  , .store (.bin .add (.reg 15) (.const 7)) (.reg 24)
  , .store (.bin .add (.reg 15) (.const 9)) (.reg 18)
  , .store (.bin .add (.reg 15) (.const 10)) (.reg 19)
  , .store (.bin .add (.reg 15) (.const 11)) (.reg 20)
  , .store (.bin .add (.reg 31) (.const 3)) (.reg 17)
  , .store (.bin .add (.reg 31) (.const 6)) (.bin .add (.reg 29) (.const 1))
  , .store (.bin .add (.reg 32) (.const 4)) (.reg 17)
  , .store (.bin .add (.reg 32) (.const 6)) (.bin .add (.reg 29) (.const 1))
  , .call 25 bSp [.reg 15]
  , .assign 22 (.load (.bin .add (.reg 15) (.const 12)))
  , .assign 20 (.load (.bin .add (.reg 15) (.const 14)))
  , .assign 18 (.load (.bin .add (.reg 15) (.const 16)))
  , .assign 19 (.load (.bin .add (.reg 15) (.const 17)))
  , .assign 30 (.bin .add (.reg 30) (.reg 25)) ]

@[expose] def batchRouteStepUpdStmts : List Stmt :=
  [ batchAppendChunkStmt
  , batchMarkMatchedStmt
  , .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
  , .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))
  , batchCompactAStmt
  , .store (.bin .add (.reg 10) (.reg 29)) (.reg 25)
  , .assign 29 (.bin .add (.reg 29) (.const 1)) ]

lemma localAPairsAt_slot_bound {mem : ℕ → ℕ} {aOffAddr aLenAddr aDataAddr : ℕ}
    {X : Finset ℕ} {curPairs : List (Finset ℕ × Finset ℕ)} {cap : ℕ}
    (hla : LocalAPairsAt mem aOffAddr aLenAddr aDataAddr X curPairs cap) :
    ∀ u v, u ≤ v → v ≤ curPairs.length → mem (aOffAddr + u) ≤ mem (aOffAddr + v) := by
  intro u v huv hv
  have hstep : ∀ d, u + d ≤ curPairs.length → mem (aOffAddr + u) ≤ mem (aOffAddr + (u + d)) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ihd =>
      intro hd
      have hlt : u + d < curPairs.length := by omega
      have h1 := (hla.2 (u + d) hlt).1
      rw [show aOffAddr + (u + (d + 1)) = aOffAddr + (u + d) + 1 by omega]
      exact le_trans (ihd (by omega)) (by omega)
  have := hstep (v - u) (by omega)
  rwa [show u + (v - u) = v by omega] at this

lemma disj_l {a la b lb x : ℕ} (h : DisjRange a la b lb)
    (hx1 : b ≤ x) (hx2 : x < b + lb) : ¬ (a ≤ x ∧ x < a + la) := by
  unfold DisjRange at h; omega

lemma disj_r {a la b lb x : ℕ} (h : DisjRange a la b lb)
    (hx1 : a ≤ x) (hx2 : x < a + la) : ¬ (b ≤ x ∧ x < b + lb) := by
  unfold DisjRange at h; omega

lemma disj_ne_l {a la b lb x y : ℕ} (h : DisjRange a la b lb)
    (hx1 : b ≤ x) (hx2 : x < b + lb) (hy1 : a ≤ y) (hy2 : y < a + la) : x ≠ y := by
  unfold DisjRange at h; omega

lemma disj_ne_r {a la b lb x y : ℕ} (h : DisjRange a la b lb)
    (hx1 : a ≤ x) (hx2 : x < a + la) (hy1 : b ≤ y) (hy2 : y < b + lb) : x ≠ y := by
  unfold DisjRange at h; omega

lemma sub_not_in {a la b e x : ℕ} (h1 : a ≤ b) (h2 : e ≤ a + la)
    (hnot : ¬ (a ≤ x ∧ x < a + la)) : ¬ (b ≤ x ∧ x < e) := by omega

lemma ws_ma_sub (ws nX m2 k : ℕ) :
    ws ≤ wsMatchAStamp ws nX ∧ wsMatchAStamp ws nX + nX ≤ ws + batchScratchSize nX m2 k := by
  unfold wsMatchAStamp batchScratchSize; omega

lemma ws_nonma_stamps {mem1 mem2 : ℕ → ℕ} {ws nX m2 k : ℕ}
    (h : ∀ a, ws ≤ a → a < ws + batchScratchSize nX m2 k →
      (a < wsMatchAStamp ws nX ∨ wsMatchAStamp ws nX + nX ≤ a) → mem1 a = mem2 a)
    {v : ℕ} (hv : v < nX) :
    mem1 (wsIsoStamp ws + v) = mem2 (wsIsoStamp ws + v) ∧
    mem1 (wsVisStamp ws nX + v) = mem2 (wsVisStamp ws nX + v) ∧
    mem1 (wsCurStamp ws nX + v) = mem2 (wsCurStamp ws nX + v) ∧
    mem1 (wsUsedStamp ws nX + v) = mem2 (wsUsedStamp ws nX + v) ∧
    mem1 (wsDeadStamp ws nX + v) = mem2 (wsDeadStamp ws nX + v) ∧
    mem1 (wsBallStamp ws nX m2 k + v) = mem2 (wsBallStamp ws nX m2 k + v) ∧
    mem1 (wsLiveStamp ws nX m2 k + v) = mem2 (wsLiveStamp ws nX m2 k + v) := by
  refine ⟨h _ ?_ ?_ (Or.inl ?_), h _ ?_ ?_ (Or.inr ?_), h _ ?_ ?_ (Or.inr ?_),
          h _ ?_ ?_ (Or.inr ?_), h _ ?_ ?_ (Or.inr ?_), h _ ?_ ?_ (Or.inr ?_),
          h _ ?_ ?_ (Or.inr ?_)⟩ <;>
    simp only [wsIsoStamp, wsMatchAStamp, wsVisStamp, wsCurStamp, wsUsedStamp,
      wsDeadStamp, wsBallStamp, wsLiveStamp, batchScratchSize] <;> omega

lemma batchRouteStep_upd_lp
    {X A B ML MR : Finset ℕ} {cfg : BatchCfg} {curPairs : List (Finset ℕ × Finset ℕ)}
    {i : ℕ} {mem0 mem1 : ℕ → ℕ}
    (hnX : cfg.nX = X.card) (hi_cur : i < curPairs.length) (hcur_i : curPairs[i]'hi_cur = (A, B))
    (hvalid : ValidTerminalPairs X curPairs) (hMR_sub : MR ⊆ B)
    (hlp : LocalPairsAt mem0 cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr X curPairs X.card)
    (hpb1 : ∀ v < X.card, mem1 (cfg.pairBAddr + v) = if origOf X v ∈ MR then 0 else mem0 (cfg.pairBAddr + v))
    (hao_eq : ∀ u ≤ curPairs.length, mem1 (cfg.aOffAddr + u) = mem0 (cfg.aOffAddr + u))
    (hal_i : mem1 (cfg.aLenAddr + i) = (A \ ML).card)
    (hal_ne : ∀ j < curPairs.length, j ≠ i → mem1 (cfg.aLenAddr + j) = mem0 (cfg.aLenAddr + j))
    (had_i : ListAt mem1 (cfg.aDataAddr + mem0 (cfg.aOffAddr + i)) (((A \ ML).sort (· ≤ ·)).map (locOf X)))
    (had_ne : ∀ a, cfg.aDataAddr ≤ a → a < cfg.aDataAddr + cfg.nX →
      ¬ (cfg.aDataAddr + mem0 (cfg.aOffAddr + i) ≤ a ∧
         a < cfg.aDataAddr + mem0 (cfg.aOffAddr + i) + A.card) → mem1 a = mem0 a) :
    LocalPairsAt mem1 cfg.pairBAddr cfg.aOffAddr cfg.aLenAddr cfg.aDataAddr
      X (curPairs.set i (A \ ML, B \ MR)) X.card := by
  rcases hlp with ⟨hlp_b, hlp_a⟩
  have ha_i := hlp_a.2 i hi_cur; dsimp only at ha_i; rw [hcur_i] at ha_i; dsimp only at ha_i
  constructor
  · intro v hv; rw [hpb1 v hv]
    by_cases hmr : origOf X v ∈ MR
    · simp only [hmr, ↓reduceIte]
      refine ⟨Nat.zero_le _, fun j hj => ?_⟩
      have hj' : j < curPairs.length := by simpa using hj
      refine ⟨fun h0 => absurd h0 (by omega), fun hvBj => ?_⟩
      by_cases hji : j = i
      · subst hji; simp only [List.getElem_set_self] at hvBj; exact False.elim ((Finset.mem_sdiff.mp hvBj).2 hmr)
      · simp only [List.getElem_set_ne (Ne.symm hji)] at hvBj
        have hpw := List.pairwise_iff_getElem.mp (routeTerminalPairs_of_validTerminalPairs hvalid).2
        have hdisj_ij : Disjoint (curPairs[i]'hi_cur).2 (curPairs[j]'hj').2 := by
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · exact Disjoint.mono Finset.subset_union_right Finset.subset_union_right (hpw j i hj' hi_cur hlt).symm
          · exact Disjoint.mono Finset.subset_union_right Finset.subset_union_right (hpw i j hi_cur hj' hgt)
        rw [hcur_i] at hdisj_ij; exact absurd (Finset.disjoint_left.mp hdisj_ij (hMR_sub hmr) hvBj) id
    · simp only [hmr, ↓reduceIte]
      refine ⟨by simpa using (hlp_b v hv).1, fun j hj => ?_⟩
      have hj' : j < curPairs.length := by simpa using hj
      rw [(hlp_b v hv).2 j hj']
      by_cases hji : j = i
      · subst hji; simp only [List.getElem_set_self, hcur_i, Finset.mem_sdiff, hmr, not_false_eq_true, and_true]
      · simp only [List.getElem_set_ne (Ne.symm hji)]
  · refine ⟨by simpa [hao_eq curPairs.length le_rfl] using hlp_a.1, ?_⟩
    intro j hj
    have hj' : j < curPairs.length := by simpa using hj
    have hao_j := hao_eq j (by omega); have hao_j1 := hao_eq (j + 1) (by omega)
    rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hao_j1
    by_cases hji : j = i
    · subst hji; simp only [List.getElem_set_self]
      refine ⟨by rw [hao_j, hal_i, hao_j1]; have := Finset.card_le_card (Finset.sdiff_subset (s := A) (t := ML)); have := ha_i.1; have := ha_i.2.1; omega,
              hal_i, by rw [hao_j]; exact had_i⟩
    · simp only [List.getElem_set_ne (Ne.symm hji)]
      have hsj := hlp_a.2 j hj'
      have hal_j := hal_ne j hj' hji
      refine ⟨by rw [hao_j, hal_j, hao_j1]; exact hsj.1, by rw [hal_j]; exact hsj.2.1, ?_⟩
      rw [hao_j]; intro idx hidx
      have hidx_lt : idx < (curPairs[j]'hj').1.card := by simpa using hidx
      have hdisj_slice : ¬ (cfg.aDataAddr + mem0 (cfg.aOffAddr + i) ≤ cfg.aDataAddr + mem0 (cfg.aOffAddr + j) + idx ∧
          cfg.aDataAddr + mem0 (cfg.aOffAddr + j) + idx < cfg.aDataAddr + mem0 (cfg.aOffAddr + i) + A.card) := by
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · have hle1 := hsj.1; have hlenj := hsj.2.1
          have hle2 := localAPairsAt_slot_bound hlp_a (j + 1) i (by omega) (by omega)
          rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hle2; omega
        · have hle1 := ha_i.1; have hleni := ha_i.2.1
          have hle2 := localAPairsAt_slot_bound hlp_a (i + 1) j (by omega) (by omega)
          rw [show cfg.aOffAddr + (i + 1) = cfg.aOffAddr + i + 1 by omega] at hle2; omega
      have hbound_j : mem0 (cfg.aOffAddr + j) + idx < X.card := by
        have hle1 := hsj.1; have hlenj := hsj.2.1
        have hmono := localAPairsAt_slot_bound hlp_a (j + 1) curPairs.length (by omega) le_rfl
        rw [show cfg.aOffAddr + (j + 1) = cfg.aOffAddr + j + 1 by omega] at hmono
        have := hlp_a.1; omega
      rw [had_ne _ (by omega) (by omega) hdisj_slice]
      exact hsj.2.2 idx hidx

end MinCostFlow.ExpanderDecomp
