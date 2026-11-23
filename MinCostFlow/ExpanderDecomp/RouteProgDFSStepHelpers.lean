module

public import MinCostFlow.ExpanderDecomp.RouteProgDFSAccept

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking DFS Neighbor Eligibility Check Helpers (`RouteProgDFSStepHelpers`)

Verifies `dfsStepLoopStmt` against `dfsStep` by induction on `dfsPot V ds`,
using `dfsAccept_triple` and `dfsBacktrack_triple` from `RouteProgDFSAccept.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Helper: 5-Way Neighbor Eligibility Check + Push -/

def dfsPushCheckStmt : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 33))) (.reg 5))
    .nop
    (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 33))) (.reg 18))
      .nop
      (.cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 33))) (.reg 18))
        .nop
        (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 33))) (.reg 9))
          (.cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 33)))
                    (.bin .add (.reg 30) (.const 1)))
            (seqStmts
              [ .store (.bin .add (.reg 16) (.reg 30)) (.reg 34)
              , .assign 30 (.bin .add (.reg 30) (.const 1))
              , .store (.bin .add (.reg 15) (.reg 30)) (.reg 33)
              , .assign 31 (.reg 33) ])
            .nop)
          .nop)))

lemma dfsPushCheck_true {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds1 : DFSState} {ul : List ℕ}
    {s u r wn en : ℕ} {trail : List (ℕ × ℕ)} {mem0 : ℕ → ℕ} {st3 : State}
    (hVX : V ⊆ X)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hinv3 : DfsStateAt st3.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul)
    (hstk3 : DfsStackAt st3.mem X V dist cfg ds1 s u r trail)
    (hregs3 : DfsRegsAt st3.regs cfg cfgAddr heapPtr pathsHead pathsTail ds1.used.card ds1.paths.length)
    (hr28 : st3.regs 28 = locOf X s) (hr29 : st3.regs 29 = 1)
    (hr30 : st3.regs 30 = r) (hr33 : st3.regs 33 = locOf X wn) (hr34 : st3.regs 34 = en)
    (hwnX : wn ∈ X)
    (hwnV : wn ∈ V) (hwnU : wn ∉ ds1.used) (hwnD : wn ∉ ds1.dead)
    (hr_lt : r < cfg.targetDepth) (hwnDist : dist wn = some (r + 1))
    (hwn_V_iff : st3.mem (cfg.maskArrAddr + locOf X wn) ≠ cfg.maskBadVal ↔ wn ∈ V)
    (hwn_dist_iff :
      (st3.mem (cfg.visStampAddr + locOf X wn) = cfg.bfsGen ∧
       st3.mem (cfg.distAddr + locOf X wn) = r + 1) ↔ dist wn = some (r + 1)) :
    Triple w p (fun st => st = st3) dfsPushCheckStmt
      (normalPost fun st4 =>
        DfsStateAt st4.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul ∧
        DfsStackAt st4.mem X V dist cfg ds1 s wn (r + 1) ((u, en) :: trail) ∧
        DfsRegsAt st4.regs cfg cfgAddr heapPtr pathsHead pathsTail ds1.used.card ds1.paths.length ∧
        st4.regs 27 = st3.regs 27 ∧ st4.regs 28 = locOf X s ∧ st4.regs 29 = 1 ∧
        st4.regs 30 = r + 1 ∧ st4.regs 31 = locOf X wn)
      (fun _ => 60) := by
  have hwn_loc_lt : locOf X wn < X.card := locOf_lt hwnX
  have hnd_new : ((stackVerts wn ((u, en) :: trail)).reverse).Nodup := by
    apply stackVerts_nodup_of_dist
    intro k hk
    simp only [stackVerts_reverse_push, List.length_append, List.length_singleton,
      List.length_reverse, stackVerts_length, hstk3.trail_len] at hk
    by_cases hke : k = r + 1
    · subst k
      simp only [stackVerts_reverse_push]
      rw [List.getElem_append_right (by simp [stackVerts, hstk3.trail_len])]
      simp only [List.length_reverse, stackVerts_length, hstk3.trail_len, Nat.sub_self, List.getElem_cons_zero]
      exact hwnDist
    · simp only [stackVerts_reverse_push]
      rw [List.getElem_append_left (by simp [stackVerts, hstk3.trail_len]; omega)]
      exact (hstk3.stack_ok k (by simp [stackVerts, hstk3.trail_len]; omega)).2.2.2
  have hr1_lt_X : r + 1 < X.card := by
    have hsub : (stackVerts wn ((u, en) :: trail)).reverse.toFinset ⊆ X := by
      intro x hx
      rw [List.mem_toFinset, stackVerts_reverse_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx1 | rfl
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx1
        exact hVX (hstk3.stack_ok k hk).1
      · exact hwnX
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd_new] at hcard
    simp only [stackVerts_reverse_push, List.length_append, List.length_singleton,
      List.length_reverse, stackVerts_length, hstk3.trail_len] at hcard
    omega
  have h1 : st3.mem (cfg.maskArrAddr + locOf X wn) ≠ cfg.maskBadVal := hwn_V_iff.mpr hwnV
  have h2 : st3.mem (cfg.usedStampAddr + locOf X wn) ≠ cfg.dfsGen := by
    intro h; exact hwnU (by have := (hinv3.used_stamp _ hwn_loc_lt).mp h; rwa [origOf_locOf hwnX] at this)
  have h3 : st3.mem (cfg.deadStampAddr + locOf X wn) ≠ cfg.dfsGen := by
    intro h; exact hwnD (by have := (hinv3.dead_stamp _ hwn_loc_lt).mp h; rwa [origOf_locOf hwnX] at this)
  have h45 := hwn_dist_iff.mpr hwnDist
  have h3_4 := hregs3 4 (by decide); have h3_5 := hregs3 5 (by decide)
  have h3_8 := hregs3 8 (by decide); have h3_9 := hregs3 9 (by decide)
  have h3_10 := hregs3 10 (by decide); have h3_13 := hregs3 13 (by decide)
  have h3_14 := hregs3 14 (by decide); have h3_15 := hregs3 15 (by decide)
  have h3_16 := hregs3 16 (by decide); have h3_18 := hregs3 18 (by decide)
  have hw_mask := hdisj.w_mask; have hw_us := hdisj.w_us; have hw_ds := hdisj.w_ds
  have hw_vis := hdisj.w_vis; have hw_dist := hdisj.w_dist; have hw_mb := hdisj.w_mb
  have hw_dg := hdisj.w_dgen; have hw_bg := hdisj.w_bgen; have hw_td := hdisj.w_td
  have hw_sv := hdisj.w_sv; have hw_se := hdisj.w_se; have hw4 := hdisj.w4
  set mem4 := Function.update
    (Function.update st3.mem (cfg.stkEdgeAddr + r) en)
    (cfg.stkVertAddr + (r + 1)) (locOf X wn)
  have hfr_m4 : ∀ a, a ≠ cfg.stkEdgeAddr + r → a ≠ cfg.stkVertAddr + (r + 1) → mem4 a = st3.mem a :=
    fun a ha1 ha2 => by simp [mem4, Function.update_of_ne ha2, Function.update_of_ne ha1]
  wram_enter; subst st; unfold dfsPushCheckStmt
  refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_4, h3_5, hr33, h1, show cfg.maskArrAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
  refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_13, h3_18, hr33, h2, show cfg.usedStampAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
  refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_14, h3_18, hr33, h3, show cfg.deadStampAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
  refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_8, h3_9, hr33, h45.1, show cfg.visStampAddr + locOf X wn < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
  refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_10, hr30, hr33, h45.2, show 1 < 2 ^ w by omega, show r + 1 < 2 ^ w by omega, show cfg.distAddr + locOf X wn < 2 ^ w by omega]) (by omega) ?_
  dsimp only [seqStmts]
  refine runs_seq_store_le (x := cfg.stkEdgeAddr + r) (v := en) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := r + 1) (by eval_expr) ?_
  refine runs_seq_store_le (x := cfg.stkVertAddr + (r + 1)) (v := locOf X wn) (by eval_expr) (by eval_expr) ?_
  refine runs_assign_le (v := locOf X wn) (by eval_expr) ?_ (by wram_cost)
  dsimp only [normalPost]
  refine ⟨?_, ?_,
    fun k hk => by simp [Function.update_of_ne (by omega : k ≠ 30), Function.update_of_ne (by omega : k ≠ 31), hregs3 k hk],
    by simp, by simp [hr28], by simp [hr29], by simp, by simp⟩
  · change DfsStateAt mem4 mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul
    refine ⟨hinv3.used_sub, hinv3.dead_sub, hinv3.paths_le, ?_, ?_, ?_,
      hinv3.ul_len, hinv3.ul_nd, hinv3.ul_sub, hinv3.ul_cov, ?_, hinv3.heap_lo, hinv3.heap_hi,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.us_se hv (by omega : r < X.card); omega)
                   (by have := disjRange_ne hdisj.us_sv hv hr1_lt_X; omega)]
      exact hinv3.used_stamp v hv
    · intro v hv
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.ds_se hv (by omega : r < X.card); omega)
                   (by have := disjRange_ne hdisj.ds_sv hv hr1_lt_X; omega)]
      exact hinv3.dead_stamp v hv
    · intro v hv
      have h1' : mem4 (cfg.curStampAddr + v) = st3.mem (cfg.curStampAddr + v) :=
        hfr_m4 _ (by have := disjRange_ne hdisj.cs_se hv (by omega : r < X.card); omega)
                 (by have := disjRange_ne hdisj.cs_sv hv hr1_lt_X; omega)
      have h2' : mem4 (cfg.curAddr + v) = st3.mem (cfg.curAddr + v) :=
        hfr_m4 _ (by have := disjRange_ne hdisj.cur_se hv (by omega : r < X.card); omega)
                 (by have := disjRange_ne hdisj.cur_sv hv hr1_lt_X; omega)
      rw [h1', h2']
      exact hinv3.cur_inv v hv
    · intro j hj
      have hle : ul.length ≤ X.card := by
        rw [hinv3.ul_len]; exact Finset.card_le_card (Finset.Subset.trans hinv3.used_sub hVX)
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.se_ul (by omega : r < X.card) (by omega : j < X.card); omega)
                   (by have := disjRange_ne hdisj.sv_ul hr1_lt_X (by omega : j < X.card); omega)]
      exact hinv3.ul_at j hj
    · exact hinv3.chain.congr (fun k hk1 hk2 => hfr_m4 k
        (by by_cases hlt : k < cfg.heapIn
            · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
            · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                have := hinv3.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv3.used_sub hVX); omega
              have := disjRange_ne hdisj.se_hp (by omega : r < X.card) (by omega : k - cfg.heapIn < 5 * X.card); omega)
        (by by_cases hlt : k < cfg.heapIn
            · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
            · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                have := hinv3.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv3.used_sub hVX); omega
              have := disjRange_ne hdisj.sv_hp hr1_lt_X (by omega : k - cfg.heapIn < 5 * X.card); omega))
    · intro a ha
      rw [hfr_m4 a (fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
                   (fun h => ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))]
      exact hinv3.frame_out a ha
    · intro a ha
      rw [hfr_m4 a (by rcases hdisj.se_co with h | h <;> omega)
                   (by rcases hdisj.sv_co with h | h <;> omega)]
      exact hinv3.frame_cfgOut a ha
    · intro v hv
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.cs_se hv (by omega : r < X.card); omega)
                   (by have := disjRange_ne hdisj.cs_sv hv hr1_lt_X; omega)]
      exact hinv3.stamp_cur v hv
    · intro v hv
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.us_se hv (by omega : r < X.card); omega)
                   (by have := disjRange_ne hdisj.us_sv hv hr1_lt_X; omega)]
      exact hinv3.stamp_used v hv
    · intro v hv
      rw [hfr_m4 _ (by have := disjRange_ne hdisj.ds_se hv (by omega : r < X.card); omega)
                   (by have := disjRange_ne hdisj.ds_sv hv hr1_lt_X; omega)]
      exact hinv3.stamp_dead v hv
  · refine ⟨by omega, by simp [hstk3.trail_len], ?_, ?_, ?_, ?_⟩
    · simp only [stackVerts_reverse_push,
        List.getElem_append_left (by simp [stackVerts] : 0 < (stackVerts u trail).reverse.length)]
      exact hstk3.s_eq
    · intro k hk
      simp only [stackVerts_reverse_push, List.map_append, List.map_singleton,
        List.length_append, List.length_map, List.length_reverse, stackVerts_length,
        hstk3.trail_len, List.length_singleton] at hk ⊢
      by_cases hke : k = r + 1
      · subst k
        simp only [Function.update_self]
        rw [List.getElem_append_right (by simp [stackVerts, hstk3.trail_len])]
        simp [stackVerts_length, hstk3.trail_len]
      · have hk_lt : k < r + 1 := by omega
        change mem4 (cfg.stkVertAddr + k) = _
        rw [hfr_m4 _ (by have := disjRange_ne hdisj.sv_se (by omega : k < X.card) (by omega : r < X.card); omega) (by omega),
            List.getElem_append_left (by simp [stackVerts, hstk3.trail_len]; omega)]
        exact hstk3.vert_at k (by simp [stackVerts, hstk3.trail_len, hk_lt])
    · intro k hk
      simp only [trail_edges_reverse_push, List.length_append, List.length_reverse,
        List.length_map, hstk3.trail_len, List.length_singleton] at hk ⊢
      by_cases hke : k = r
      · subst k
        have hne : cfg.stkEdgeAddr + r ≠ cfg.stkVertAddr + (r + 1) := by
          have := disjRange_ne hdisj.sv_se hr1_lt_X (by omega : r < X.card); omega
        simp only [Function.update_of_ne hne, Function.update_self]
        rw [List.getElem_append_right (by simp [hstk3.trail_len])]
        simp [hstk3.trail_len]
      · have hk_lt : k < r := by omega
        change mem4 (cfg.stkEdgeAddr + k) = _
        rw [hfr_m4 _ (by omega) (by have := disjRange_ne hdisj.sv_se hr1_lt_X (by omega : k < X.card); omega),
            List.getElem_append_left (by simp [hstk3.trail_len]; omega)]
        exact hstk3.edge_at k (by simp [hstk3.trail_len, hk_lt])
    · intro k hk
      simp only [stackVerts_reverse_push, List.length_append, List.length_singleton,
        List.length_reverse, stackVerts_length, hstk3.trail_len] at hk
      by_cases hke : k = r + 1
      · rcases hke with rfl
        simp only [stackVerts_reverse_push]
        rw [List.getElem_append_right (by simp [stackVerts, hstk3.trail_len] : (stackVerts u trail).reverse.length ≤ r + 1)]
        simp only [List.length_reverse, stackVerts_length, hstk3.trail_len, Nat.sub_self, List.getElem_cons_zero]
        exact ⟨hwnV, hwnU, hwnD, hwnDist⟩
      · simp only [stackVerts_reverse_push]
        rw [List.getElem_append_left (by simp [stackVerts, hstk3.trail_len]; omega)]
        exact hstk3.stack_ok k (by simp [stackVerts, hstk3.trail_len]; omega)

lemma dfsPushCheck_false {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds1 : DFSState} {ul : List ℕ}
    {r wn : ℕ} {mem0 : ℕ → ℕ} {st3 : State}
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hinv3 : DfsStateAt st3.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul)
    (hregs3 : DfsRegsAt st3.regs cfg cfgAddr heapPtr pathsHead pathsTail ds1.used.card ds1.paths.length)
    (hr30 : st3.regs 30 = r) (hr33 : st3.regs 33 = locOf X wn)
    (hwnX : wn ∈ X) (hr_lt : r < cfg.targetDepth)
    (hwn_V_iff : st3.mem (cfg.maskArrAddr + locOf X wn) ≠ cfg.maskBadVal ↔ wn ∈ V)
    (hwn_dist_iff :
      (st3.mem (cfg.visStampAddr + locOf X wn) = cfg.bfsGen ∧
       st3.mem (cfg.distAddr + locOf X wn) = r + 1) ↔ dist wn = some (r + 1))
    (hnot : ¬ (wn ∈ V ∧ wn ∉ ds1.used ∧ wn ∉ ds1.dead ∧ r < cfg.targetDepth ∧ dist wn = some (r + 1))) :
    Triple w p (fun st => st = st3) dfsPushCheckStmt (normalPost fun st => st = st3) (fun _ => 40) := by
  have hwn_loc_lt : locOf X wn < X.card := locOf_lt hwnX
  have hwn_used_iff : st3.mem (cfg.usedStampAddr + locOf X wn) = cfg.dfsGen ↔ wn ∈ ds1.used := by
    simpa [origOf_locOf hwnX] using hinv3.used_stamp (locOf X wn) hwn_loc_lt
  have hwn_dead_iff : st3.mem (cfg.deadStampAddr + locOf X wn) = cfg.dfsGen ↔ wn ∈ ds1.dead := by
    simpa [origOf_locOf hwnX] using hinv3.dead_stamp (locOf X wn) hwn_loc_lt
  have h3_4 := hregs3 4 (by decide); have h3_5 := hregs3 5 (by decide)
  have h3_8 := hregs3 8 (by decide); have h3_9 := hregs3 9 (by decide)
  have h3_10 := hregs3 10 (by decide); have h3_13 := hregs3 13 (by decide)
  have h3_14 := hregs3 14 (by decide); have h3_18 := hregs3 18 (by decide)
  have hw_mask := hdisj.w_mask; have hw_us := hdisj.w_us; have hw_ds := hdisj.w_ds
  have hw_vis := hdisj.w_vis; have hw_dist := hdisj.w_dist; have hw_mb := hdisj.w_mb
  have hw_dg := hdisj.w_dgen; have hw_bg := hdisj.w_bgen; have hw_td := hdisj.w_td
  have hw4 := hdisj.w4
  wram_enter; subst st; unfold dfsPushCheckStmt
  by_cases hwnV : wn ∈ V
  · have h1 : st3.mem (cfg.maskArrAddr + locOf X wn) ≠ cfg.maskBadVal := hwn_V_iff.mpr hwnV
    refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_4, h3_5, hr33, h1, show cfg.maskArrAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
    by_cases hwnU : wn ∈ ds1.used
    · have h2 : st3.mem (cfg.usedStampAddr + locOf X wn) = cfg.dfsGen := hwn_used_iff.mpr hwnU
      refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_13, h3_18, hr33, h2, show cfg.usedStampAddr + locOf X wn < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
      exact runs_nop_le rfl (by wram_cost)
    · have h2 : st3.mem (cfg.usedStampAddr + locOf X wn) ≠ cfg.dfsGen := mt hwn_used_iff.mp hwnU
      refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_13, h3_18, hr33, h2, show cfg.usedStampAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
      by_cases hwnD : wn ∈ ds1.dead
      · have h3 : st3.mem (cfg.deadStampAddr + locOf X wn) = cfg.dfsGen := hwn_dead_iff.mpr hwnD
        refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_14, h3_18, hr33, h3, show cfg.deadStampAddr + locOf X wn < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
        exact runs_nop_le rfl (by wram_cost)
      · have h3 : st3.mem (cfg.deadStampAddr + locOf X wn) ≠ cfg.dfsGen := mt hwn_dead_iff.mp hwnD
        refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_14, h3_18, hr33, h3, show cfg.deadStampAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
        have hwn_ndist : dist wn ≠ some (r + 1) := fun hd => hnot ⟨hwnV, hwnU, hwnD, hr_lt, hd⟩
        by_cases hvis : st3.mem (cfg.visStampAddr + locOf X wn) = cfg.bfsGen
        · refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_8, h3_9, hr33, hvis, show cfg.visStampAddr + locOf X wn < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
          have hne_d : st3.mem (cfg.distAddr + locOf X wn) ≠ r + 1 := fun hd =>
            hwn_ndist (hwn_dist_iff.mp ⟨hvis, hd⟩)
          refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_10, hr30, hr33, hne_d, show 1 < 2 ^ w by omega, show r + 1 < 2 ^ w by omega, show cfg.distAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
          exact runs_nop_le rfl (by wram_cost)
        · refine runs_cond_zero_le (by simp [Expr.eval, BinOp.eval, h3_8, h3_9, hr33, hvis, show cfg.visStampAddr + locOf X wn < 2 ^ w by omega, show 0 < 2 ^ w by omega]) ?_
          exact runs_nop_le rfl (by wram_cost)
  · have h1 : st3.mem (cfg.maskArrAddr + locOf X wn) = cfg.maskBadVal := by
      by_contra h; exact hwnV (hwn_V_iff.mp h)
    refine runs_cond_pos_le (v := 1) (by simp [Expr.eval, BinOp.eval, h3_4, h3_5, hr33, h1, show cfg.maskArrAddr + locOf X wn < 2 ^ w by omega, show 1 < 2 ^ w by omega]) (by omega) ?_
    exact runs_nop_le rfl (by wram_cost)


end MinCostFlow.ExpanderDecomp
