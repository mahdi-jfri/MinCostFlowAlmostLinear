module

public import MinCostFlow.ExpanderDecomp.RouteProgDFSAccept
import MinCostFlow.ExpanderDecomp.RouteProgDFSStepHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking DFS Inner Loop Verification (`dfsStepLoop_triple`)

Verifies `dfsStepLoopStmt` against `dfsStep` by induction on `dfsPot V ds`,
using `dfsAccept_triple`, `dfsBacktrack_triple`, and `dfsPushCheck_true`/`dfsPushCheck_false`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Main Inner DFS Stack Loop (`dfsStepLoop_triple`) -/

private lemma DfsStateAt.cost_irrel {mem mem0 : ℕ → ℕ} {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : DfsCfg} {cfgAddr heapLo heapPtr pathsHead pathsTail : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {ds1 ds2 : DFSState} {ul : List ℕ}
    (h : DfsStateAt mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul)
    (hu : ds1.used = ds2.used) (hd : ds1.dead = ds2.dead)
    (hc : ds1.cursor = ds2.cursor) (hp : ds1.paths = ds2.paths) :
    DfsStateAt mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds2 ul := by
  cases ds1; cases ds2; simp only at hu hd hc hp; subst hu; subst hd; subst hc; subst hp
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩

theorem dfsStepLoop_triple {w : ℕ} {p : Program}
    {X V T : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {dist : ℕ → Option ℕ}
    {cfg : DfsCfg} {cfgAddr m2 heapLo : ℕ}
    {acc : List ((ℕ × ℕ) × List ℕ)} {mem0 : ℕ → ℕ}
    (hVX : V ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcsr : AdjCsrAt mem0 cfg.offAddr cfg.nbAddr cfg.edgeAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : DfsDisj w X.card m2 cfg cfgAddr)
    (hheap_lo : heapLo ≤ cfg.heapIn)
    (hacc_disj : ∀ a, heapLo ≤ a ∧ a < cfg.heapIn → ¬ DfsWriteSet X.card cfg cfgAddr a)
    (hmask : ∀ v < X.card, mem0 (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : ∀ v < X.card, mem0 (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ T)
    (hdist_mem : ∀ v < X.card,
      (mem0 (cfg.visStampAddr + v) = cfg.bfsGen ∧ dist (origOf X v) = some (mem0 (cfg.distAddr + v))) ∨
      (mem0 (cfg.visStampAddr + v) ≠ cfg.bfsGen ∧ dist (origOf X v) = none))
    (pot fuel s : ℕ) :
    ∀ (u r : ℕ) (trail : List (ℕ × ℕ)) (ds : DFSState) (ul : List ℕ)
      (heapPtr pathsHead pathsTail : ℕ) (st0 : State),
      dfsPot V ds = pot →
      pot < fuel →
      DfsStateAt st0.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul →
      DfsStackAt st0.mem X V dist cfg ds s u r trail →
      DfsRegsAt st0.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length →
      st0.regs 28 = locOf X s →
      st0.regs 29 = 1 →
      st0.regs 30 = r →
      st0.regs 31 = locOf X u →
      ∀ ω,
        let dsF := dfsStep V T dist cfg.targetDepth s fuel u r trail { ds with cost := 0 }
        ∃ st' c,
          Runs w p ω dfsStepLoopStmt st0 .normal st' c ∧
          (∃ heapPtr' pathsHead' pathsTail' ul',
            DfsStateAt st'.mem mem0 X V adj cfg cfgAddr heapLo heapPtr' pathsHead' pathsTail' acc dsF ul' ∧
            DfsRegsAt st'.regs cfg cfgAddr heapPtr' pathsHead' pathsTail' dsF.used.card dsF.paths.length ∧
            st'.regs 27 = st0.regs 27 ∧
            st'.regs 29 = 0) ∧
          c ≤ 150 * dsF.cost + 5 := by
  induction pot generalizing fuel with
  | zero =>
    intro u r trail ds ul heapPtr pathsHead pathsTail st0 hpot hfuel hinv hstk _ _ _ _ _ ω
    have huV : u ∈ V := by
      have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).1
      rwa [stackVerts_reverse_getLast u trail] at hl
    have huD : u ∉ ds.dead := by
      have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).2.2.1
      rwa [stackVerts_reverse_getLast u trail] at hl
    have hpos : 1 ≤ (V \ ds.dead).card := Finset.one_le_card.mpr ⟨u, Finset.mem_sdiff.mpr ⟨huV, huD⟩⟩
    unfold dfsPot at hpot; omega
  | succ pot' ih =>
    intro u r trail ds ul heapPtr pathsHead pathsTail st0 hpot hfuel hinv hstk hregs hr28 hr29 hr30 hr31 ω
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have huV : u ∈ V := by
        have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).1
        rwa [stackVerts_reverse_getLast u trail] at hl
      have huD : u ∉ ds.dead := by
        have hl := (hstk.stack_ok trail.length (by simp [stackVerts])).2.2.1
        rwa [stackVerts_reverse_getLast u trail] at hl
      have huX : u ∈ X := hVX huV
      have hu_loc_lt : locOf X u < X.card := locOf_lt huX
      have hstop_u : st0.mem (cfg.stopArrAddr + locOf X u) = cfg.stopVal ↔ u ∈ T := by
        rw [hinv.frame_out _ (hdisj.ro_stop _ ⟨by omega, by omega⟩), hstop _ hu_loc_lt, origOf_locOf huX]
      have hr6 : st0.regs 6 = cfg.stopArrAddr := hregs 6 (by decide)
      have hr7 : st0.regs 7 = cfg.stopVal := hregs 7 (by decide)
      have hw_stop : cfg.stopArrAddr + X.card + 5 < 2 ^ w := hdisj.w_stop
      have hw_svv : cfg.stopVal < 2 ^ w := hdisj.w_sv_val
      have hw4 : 4 ≤ 2 ^ w := hdisj.w4
      have hloop_guard : (Expr.reg 29).eval w st0 = some 1 := by simp [Expr.eval, hr29]
      -- Case 1: u ∈ T
      by_cases huT : u ∈ T
      · have hev_T : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).eval w st0 = some 1 := by
          have hmem_T : st0.mem (cfg.stopArrAddr + locOf X u) = cfg.stopVal := hstop_u.mpr huT
          simp [Expr.eval, BinOp.eval, hr6, hr7, hr31, hmem_T,
            show cfg.stopArrAddr + locOf X u < 2 ^ w by omega, show 1 < 2 ^ w by omega]
        obtain ⟨o1, st1, c1, hrun1, hpost1, hc1⟩ :=
          dfsAccept_triple (p := p) hVX hdisj hheap_lo hacc_disj hinv hstk hregs hr28 hr30 hr31 st0 ω rfl
        cases o1 with
        | returned _ => exact hpost1.elim
        | normal =>
          rcases hpost1 with ⟨hp1, ph1, pt1, ul1, hinv1, hregs1, hr1_27, hr1_29⟩
          have hbody : Runs w p ω dfsStepBodyStmt st0 .normal st1
              ((Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).size + c1 + 1) := by
            unfold dfsStepBodyStmt
            exact runs_cond_iff.mpr ⟨1, c1, hev_T, by simpa using hrun1, rfl⟩
          have hexit : Runs w p ω dfsStepLoopStmt st1 .normal st1 ((Expr.reg 29).size + 1) :=
            runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr1_29], rfl, rfl, rfl⟩)
          refine ⟨st1, _,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, _, _, hloop_guard, by omega, hbody, hexit, rfl⟩)),
            ?_, ?_⟩
          · simp only [dfsStep, huT, ↓reduceIte]
            exact ⟨hp1, ph1, pt1, ul1, hinv1.cost_irrel rfl rfl rfl rfl, hregs1, hr1_27, hr1_29⟩
          · simp only [dfsStep, huT, ↓reduceIte, stackVerts_length, hstk.trail_len, Expr.size] at hc1 ⊢
            omega
      · -- u ∉ T
        have hev_nT : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).eval w st0 = some 0 := by
          have hmem_nT : st0.mem (cfg.stopArrAddr + locOf X u) ≠ cfg.stopVal := mt hstop_u.mp huT
          simp [Expr.eval, BinOp.eval, hr6, hr7, hr31, hmem_nT,
            show cfg.stopArrAddr + locOf X u < 2 ^ w by omega, show 0 < 2 ^ w by omega]
        have hr19 : st0.regs 19 = cfg.targetDepth := hregs 19 (by decide)
        -- Case 2: r = targetDepth
        by_cases hrj : r = cfg.targetDepth
        · have hev_rj : (Expr.bin .eq (.reg 30) (.reg 19)).eval w st0 = some 1 := by
            simp [Expr.eval, BinOp.eval, hr30, hr19, hrj, show 1 < 2 ^ w by omega]
          obtain ⟨o1, st1, c1, hrun1, hpost1, hc1⟩ :=
            dfsBacktrack_triple (p := p) hVX hdisj hheap_lo hacc_disj hinv hstk hregs hr28 hr29 hr30 hr31 st0 ω rfl
          cases o1 with
          | returned _ => exact hpost1.elim
          | normal =>
            rcases hpost1 with ⟨hinv1, hregs1, hr1_27, hr1_28, hbt⟩
            have hbody : Runs w p ω dfsStepBodyStmt st0 .normal st1
                ((Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).size +
                  ((Expr.bin .eq (.reg 30) (.reg 19)).size + c1 + 1) + 1) := by
              unfold dfsStepBodyStmt
              refine runs_cond_iff.mpr ⟨0, _, hev_nT, ?_, rfl⟩
              simp only [↓reduceIte]
              exact runs_cond_iff.mpr ⟨1, c1, hev_rj, by simpa using hrun1, rfl⟩
            cases trail with
            | nil =>
              have hexit : Runs w p ω dfsStepLoopStmt st1 .normal st1 ((Expr.reg 29).size + 1) :=
                runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hbt], rfl, rfl, rfl⟩)
              refine ⟨st1, _,
                runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, _, _, hloop_guard, by omega, hbody, hexit, rfl⟩)),
                ?_, ?_⟩
              · simp only [dfsStep, huT, ↓reduceIte, hrj]
                exact ⟨heapPtr, pathsHead, pathsTail, ul, hinv1.cost_irrel rfl rfl rfl rfl, hregs1, hr1_27, hbt⟩
              · simp only [dfsStep, huT, ↓reduceIte, hrj, Expr.size] at hc1 ⊢; omega
            | cons pe rest =>
              rcases pe with ⟨par, e⟩
              rcases hbt with ⟨hr1_29, hr1_30, hr1_31, hstk1⟩
              set ds1 : DFSState := { ds with dead := insert u ds.dead, cost := ds.cost + 1 }
              have hpot1 : dfsPot V ds1 = pot' := by
                have := dfsPot_insert_dead_eq V ds huV huD; dsimp only [ds1]; omega
              obtain ⟨st2, c2, hrun2, hpost2, hc2⟩ :=
                ih (fuel := fuel') par (r - 1) rest ds1 ul heapPtr pathsHead pathsTail st1
                  hpot1 (by omega) hinv1 hstk1 hregs1 hr1_28 hr1_29 hr1_30 hr1_31 ω
              have hadd := dfsStep_cost_add V T dist cfg.targetDepth s fuel' par (r - 1) rest
                { ds1 with cost := 0 } 1
              set dsA := dfsStep V T dist cfg.targetDepth s fuel' par (r - 1) rest { ds1 with cost := 1 }
              set dsB := dfsStep V T dist cfg.targetDepth s fuel' par (r - 1) rest { ds1 with cost := 0 }
              have hAB : dsA = { dsB with cost := dsB.cost + 1 } := by
                rcases hadd with ⟨h1, h2, h3, h4, h5⟩
                cases hA : dsA; cases hB : dsB
                simp only [dsA, dsB, hA, hB] at h1 h2 h3 h4 h5
                simp only [h1, h2, h3, h4, h5]
              have hstep_eq :
                  dfsStep V T dist cfg.targetDepth s (fuel' + 1) u r ((par, e) :: rest) { ds with cost := 0 } =
                    { dsB with cost := dsB.cost + 1 } := by
                rw [← hAB]; simp only [dfsStep, huT, ↓reduceIte, hrj, dsA, ds1]
              refine ⟨st2, _,
                runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, _, c2, hloop_guard, by omega, hbody, hrun2, rfl⟩)),
                ?_, ?_⟩
              · rw [hstep_eq]
                rcases hpost2 with ⟨hp2, ph2, pt2, ul2, hinv2, hregs2, hr2_27, hr2_29⟩
                exact ⟨hp2, ph2, pt2, ul2, hinv2.cost_irrel rfl rfl rfl rfl, hregs2, hr2_27.trans hr1_27, hr2_29⟩
              · rw [hstep_eq]
                simp only [Expr.size] at hc1 hc2 ⊢; omega
        · -- Case 3: u ∉ T and r < targetDepth
          have hr_lt_j : r < cfg.targetDepth := by have := hstk.r_le; omega
          have hev_nrj : (Expr.bin .eq (.reg 30) (.reg 19)).eval w st0 = some 0 := by
            simp [Expr.eval, BinOp.eval, hr30, hr19, hrj, show 0 < 2 ^ w by omega]
          have hr1 : st0.regs 1 = cfg.offAddr := hregs 1 (by decide)
          have hr11 : st0.regs 11 = cfg.curStampAddr := hregs 11 (by decide)
          have hr12 : st0.regs 12 = cfg.curAddr := hregs 12 (by decide)
          have hr18 : st0.regs 18 = cfg.dfsGen := hregs 18 (by decide)
          have hoff_u : st0.mem (cfg.offAddr + locOf X u) = adjCsrOff X adj (locOf X u) := by
            rw [hinv.frame_out _ (hdisj.ro_off _ ⟨by omega, by omega⟩)]
            exact hcsr.1.1 (locOf X u) (le_of_lt hu_loc_lt)
          -- Step 3.1: lazy cursor initialization
          have hlazy :
              ∃ st1 c1,
                Runs w p ω
                  (.cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 31))) (.reg 18))
                    .nop
                    (seqStmts
                      [ .store (.bin .add (.reg 11) (.reg 31)) (.reg 18)
                      , .store (.bin .add (.reg 12) (.reg 31)) (.load (.bin .add (.reg 1) (.reg 31))) ]))
                  st0 .normal st1 c1 ∧
                c1 ≤ 22 ∧
                st1.regs = st0.regs ∧
                st1.mem (cfg.curStampAddr + locOf X u) = cfg.dfsGen ∧
                adjCsrOff X adj (locOf X u) ≤ st1.mem (cfg.curAddr + locOf X u) ∧
                st1.mem (cfg.curAddr + locOf X u) ≤ adjCsrOff X adj (locOf X u + 1) ∧
                ds.cursor u = (adj u).drop (st1.mem (cfg.curAddr + locOf X u) - adjCsrOff X adj (locOf X u)) ∧
                DfsStateAt st1.mem mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul ∧
                DfsStackAt st1.mem X V dist cfg ds s u r trail := by
            have hw_cs := hdisj.w_cs; have hw_cur := hdisj.w_cur; have hw_off := hdisj.w_off
            have hw_dg := hdisj.w_dgen
            by_cases hcs : st0.mem (cfg.curStampAddr + locOf X u) = cfg.dfsGen
            · have hc_inv := (hinv.cur_inv (locOf X u) hu_loc_lt).2 hcs
              rw [origOf_locOf huX] at hc_inv
              have hev : (Expr.bin .eq (.load (.bin .add (.reg 11) (.reg 31))) (.reg 18)).eval w st0 = some 1 := by
                simp [Expr.eval, BinOp.eval, hr11, hr18, hr31, hcs,
                  show cfg.curStampAddr + locOf X u < 2 ^ w by omega, show 1 < 2 ^ w by omega]
              refine ⟨st0, _, runs_cond_iff.mpr ⟨1, 1, hev, by simp [runs_nop_iff], rfl⟩,
                by simp [Expr.size], rfl, hcs, hc_inv.1, hc_inv.2.1, hc_inv.2.2, hinv, hstk⟩
            · have hc_inv := (hinv.cur_inv (locOf X u) hu_loc_lt).1 hcs
              rw [origOf_locOf huX] at hc_inv
              set mem1 := Function.update
                (Function.update st0.mem (cfg.curStampAddr + locOf X u) cfg.dfsGen)
                (cfg.curAddr + locOf X u) (adjCsrOff X adj (locOf X u))
              have hrun_init : Triple w p (fun st => st = st0)
                  (seqStmts
                    [ .store (.bin .add (.reg 11) (.reg 31)) (.reg 18)
                    , .store (.bin .add (.reg 12) (.reg 31)) (.load (.bin .add (.reg 1) (.reg 31))) ])
                  (normalPost fun st => st = { st0 with mem := mem1 }) (fun _ => 15) := by
                wram_enter; subst st; dsimp only [seqStmts]
                refine runs_seq_store_le (x := cfg.curStampAddr + locOf X u) (v := cfg.dfsGen)
                  (by eval_expr) (by eval_expr) ?_
                have hne_off : cfg.offAddr + locOf X u ≠ cfg.curStampAddr + locOf X u := fun heq =>
                  hdisj.ro_off (cfg.offAddr + locOf X u) ⟨by omega, by omega⟩ (Or.inl ⟨by omega, by omega⟩)
                refine runs_store_le (x := cfg.curAddr + locOf X u) (v := adjCsrOff X adj (locOf X u))
                  (by eval_expr)
                  (by rw [← hoff_u, ← Function.update_of_ne hne_off cfg.dfsGen st0.mem]; eval_expr)
                  rfl (by wram_cost)
              obtain ⟨o1, st1, c1, hr_init, hp1, hc1⟩ := hrun_init st0 ω rfl
              cases o1 with
              | returned _ => exact hp1.elim
              | normal =>
                subst hp1
                have hev : (Expr.bin .eq (.load (.bin .add (.reg 11) (.reg 31))) (.reg 18)).eval w st0 = some 0 := by
                  simp [Expr.eval, BinOp.eval, hr11, hr18, hr31, hcs,
                    show cfg.curStampAddr + locOf X u < 2 ^ w by omega, show 0 < 2 ^ w by omega]
                have hne_cc : cfg.curStampAddr + locOf X u ≠ cfg.curAddr + locOf X u := by
                  have := disjRange_ne hdisj.cs_cur hu_loc_lt hu_loc_lt; omega
                have hfr_m1 : ∀ a, a ≠ cfg.curStampAddr + locOf X u → a ≠ cfg.curAddr + locOf X u →
                    mem1 a = st0.mem a := fun a h1 h2 => by simp [mem1, Function.update_of_ne h2, Function.update_of_ne h1]
                refine ⟨{ st0 with mem := mem1 }, _,
                  runs_cond_iff.mpr ⟨0, c1, hev, by simpa using hr_init, rfl⟩,
                  by simp only [Expr.size] at hc1 ⊢; omega, rfl,
                  by simp [mem1, Function.update_of_ne hne_cc], by simp [mem1],
                  by simp only [mem1, Function.update_self]; rw [adjCsrOff_succ X adj (locOf X u)]; omega,
                  by simp [mem1, hc_inv], ?_, ?_⟩
                · change DfsStateAt mem1 mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds ul
                  refine ⟨hinv.used_sub, hinv.dead_sub, hinv.paths_le, ?_, ?_, ?_,
                    hinv.ul_len, hinv.ul_nd, hinv.ul_sub, hinv.ul_cov, ?_, hinv.heap_lo, hinv.heap_hi,
                    ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro v hv
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_us hu_loc_lt hv; omega)
                                 (by have := disjRange_ne hdisj.cur_us hu_loc_lt hv; omega)]
                    exact hinv.used_stamp v hv
                  · intro v hv
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_ds hu_loc_lt hv; omega)
                                 (by have := disjRange_ne hdisj.cur_ds hu_loc_lt hv; omega)]
                    exact hinv.dead_stamp v hv
                  · intro v hv
                    by_cases hveq : v = locOf X u
                    · subst hveq
                      refine ⟨fun h => absurd (by simp [mem1, Function.update_of_ne hne_cc]) h, fun _ => ?_⟩
                      simp only [mem1, Function.update_self, Nat.sub_self, List.drop_zero]
                      exact ⟨le_rfl, by rw [adjCsrOff_succ X adj (locOf X u)]; omega, by rw [origOf_locOf huX]; exact hc_inv⟩
                    · rw [hfr_m1 _ (by omega) (by have := disjRange_ne hdisj.cs_cur hv hu_loc_lt; omega),
                          hfr_m1 _ (by have := disjRange_ne hdisj.cs_cur hu_loc_lt hv; omega) (by omega)]
                      exact hinv.cur_inv v hv
                  · intro j hj
                    have hle : ul.length ≤ X.card := by
                      rw [hinv.ul_len]; exact Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX)
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_ul hu_loc_lt (by omega : j < X.card); omega)
                                 (by have := disjRange_ne hdisj.cur_ul hu_loc_lt (by omega : j < X.card); omega)]
                    exact hinv.ul_at j hj
                  · exact hinv.chain.congr (fun k hk1 hk2 => hfr_m1 k
                      (by by_cases hlt : k < cfg.heapIn
                          · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inl ⟨by omega, by omega⟩)
                          · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                              have := hinv.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX); omega
                            have := disjRange_ne hdisj.cs_hp hu_loc_lt (by omega : k - cfg.heapIn < 5 * X.card); omega)
                      (by by_cases hlt : k < cfg.heapIn
                          · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inl ⟨by omega, by omega⟩))
                          · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                              have := hinv.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv.used_sub hVX); omega
                            have := disjRange_ne hdisj.cur_hp hu_loc_lt (by omega : k - cfg.heapIn < 5 * X.card); omega))
                  · intro a ha
                    rw [hfr_m1 a (fun h => ha (Or.inl ⟨by omega, by omega⟩))
                                 (fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
                    exact hinv.frame_out a ha
                  · intro a ha
                    rw [hfr_m1 a (by rcases hdisj.cs_co with h | h <;> omega)
                                 (by rcases hdisj.cur_co with h | h <;> omega)]
                    exact hinv.frame_cfgOut a ha
                  · intro v hv
                    by_cases hveq : v = locOf X u
                    · subst hveq
                      exact Or.inr (by simp [mem1, Function.update_of_ne hne_cc])
                    · rw [hfr_m1 _ (by omega) (by have := disjRange_ne hdisj.cs_cur hv hu_loc_lt; omega)]
                      exact hinv.stamp_cur v hv
                  · intro v hv
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_us hu_loc_lt hv; omega)
                                 (by have := disjRange_ne hdisj.cur_us hu_loc_lt hv; omega)]
                    exact hinv.stamp_used v hv
                  · intro v hv
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_ds hu_loc_lt hv; omega)
                                 (by have := disjRange_ne hdisj.cur_ds hu_loc_lt hv; omega)]
                    exact hinv.stamp_dead v hv
                · change DfsStackAt mem1 X V dist cfg ds s u r trail
                  have hlen_sv : (stackVerts u trail).reverse.length ≤ X.card := by
                    have hnd := stackVerts_nodup_of_dist fun k hk => (hstk.stack_ok k hk).2.2.2
                    have hsub : (stackVerts u trail).reverse.toFinset ⊆ X := fun x hx => by
                      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
                      exact hVX (hstk.stack_ok k hk).1
                    have := Finset.card_le_card hsub
                    rwa [List.toFinset_card_of_nodup hnd] at this
                  refine ⟨hstk.r_le, hstk.trail_len, hstk.s_eq, ?_, ?_, hstk.stack_ok⟩
                  · intro j hj
                    simp only [List.length_map] at hj
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_sv hu_loc_lt (by omega : j < X.card); omega)
                                 (by have := disjRange_ne hdisj.cur_sv hu_loc_lt (by omega : j < X.card); omega)]
                    exact hstk.vert_at j (by simpa using hj)
                  · intro j hj
                    simp only [List.length_reverse, List.length_map, hstk.trail_len] at hj
                    have hr_lt : r < X.card := by simp [stackVerts, hstk.trail_len] at hlen_sv; omega
                    rw [hfr_m1 _ (by have := disjRange_ne hdisj.cs_se hu_loc_lt (by omega : j < X.card); omega)
                                 (by have := disjRange_ne hdisj.cur_se hu_loc_lt (by omega : j < X.card); omega)]
                    exact hstk.edge_at j (by simp [hstk.trail_len, hj])
          rcases hlazy with ⟨st1, c1, hrun1, hc1, hr1_eq, hst1_cs, hptr_lo, hptr_hi, hcur_drop, hinv1, hstk1⟩
          set ptr := st1.mem (cfg.curAddr + locOf X u)
          set endPtr := adjCsrOff X adj (locOf X u + 1)
          have hst1_off1 : st1.mem (cfg.offAddr + (locOf X u + 1)) = endPtr := by
            rw [hinv1.frame_out _ (hdisj.ro_off _ ⟨by omega, by omega⟩)]
            exact hcsr.1.1 (locOf X u + 1) hu_loc_lt
          set st2 : State := { mem := st1.mem, regs := Function.update (Function.update st1.regs 32 ptr) 33 endPtr, pos := st1.pos }
          have hload2 : ∃ c2,
              Runs w p ω
                (.seq (.assign 32 (.load (.bin .add (.reg 12) (.reg 31))))
                      (.assign 33 (.load (.bin .add (.reg 1) (.bin .add (.reg 31) (.const 1))))))
                st1 .normal st2 c2 ∧ c2 ≤ 15 := by
            have hw_cur := hdisj.w_cur; have hw_off := hdisj.w_off; have hw_nX := hdisj.w_nX
            have htr : Triple w p (fun st => st = st1)
                (.seq (.assign 32 (.load (.bin .add (.reg 12) (.reg 31))))
                      (.assign 33 (.load (.bin .add (.reg 1) (.bin .add (.reg 31) (.const 1))))))
                (normalPost fun st => st = st2) (fun _ => 15) := by
              wram_enter; subst st
              refine runs_seq_assign_le (v := ptr) (by simp [Expr.eval, BinOp.eval, hr1_eq, hr12, hr31, show cfg.curAddr + locOf X u < 2 ^ w by omega, ptr]) ?_
              refine runs_assign_le (v := endPtr)
                (by simp [Expr.eval, BinOp.eval, hr1_eq, hr1, hr31, hst1_off1,
                      show 1 < 2 ^ w by omega, show locOf X u + 1 < 2 ^ w by omega,
                      show cfg.offAddr + (locOf X u + 1) < 2 ^ w by omega])
                rfl (by wram_cost)
            obtain ⟨o2, st2', c2, hr2', hp2, hc2⟩ := htr st1 ω rfl
            cases o2 with | returned _ => exact hp2.elim | normal => subst hp2; exact ⟨c2, hr2', hc2⟩
          rcases hload2 with ⟨c2, hrun2, hc2⟩
          have hst2_regs_inv : DfsRegsAt st2.regs cfg cfgAddr heapPtr pathsHead pathsTail ds.used.card ds.paths.length :=
            fun k hk => by simp [st2, Function.update_of_ne (by omega : k ≠ 32), Function.update_of_ne (by omega : k ≠ 33), hr1_eq, hregs k hk]
          have hst2_r27 : st2.regs 27 = st0.regs 27 := by simp [st2, hr1_eq]
          have hst2_r28 : st2.regs 28 = locOf X s := by simp [st2, hr1_eq, hr28]
          have hst2_r29 : st2.regs 29 = 1 := by simp [st2, hr1_eq, hr29]
          have hst2_r30 : st2.regs 30 = r := by simp [st2, hr1_eq, hr30]
          have hst2_r31 : st2.regs 31 = locOf X u := by simp [st2, hr1_eq, hr31]
          have hst2_r32 : st2.regs 32 = ptr := by simp [st2]
          have hst2_r33 : st2.regs 33 = endPtr := by simp [st2]
          have hlen_adju : (adj u).length = endPtr - adjCsrOff X adj (locOf X u) := by
            have := adjCsrOff_succ X adj (locOf X u)
            rw [origOf_locOf huX] at this; omega
          -- Case 3a: ptr = endPtr (cursor empty)
          by_cases hptr_eq : ptr = endPtr
          · have hcur_nil : ds.cursor u = [] := by
              rw [hcur_drop, List.drop_eq_nil_iff]; omega
            obtain ⟨o3, st3, c3, hrun3, hpost3, hc3⟩ :=
              dfsBacktrack_triple (p := p) (st0 := st2) hVX hdisj hheap_lo hacc_disj hinv1 hstk1 hst2_regs_inv
                hst2_r28 hst2_r29 hst2_r30 hst2_r31 st2 ω rfl
            cases o3 with
            | returned _ => exact hpost3.elim
            | normal =>
              rcases hpost3 with ⟨hinv3, hregs3, hr3_27, hr3_28, hbt⟩
              have hev_pe : (Expr.bin .eq (.reg 32) (.reg 33)).eval w st2 = some 1 := by
                simp [Expr.eval, BinOp.eval, hst2_r32, hst2_r33, hptr_eq, show 1 < 2 ^ w by omega]
              have hcond_ptr : Runs w p ω
                  (.cond (.bin .eq (.reg 32) (.reg 33)) dfsBacktrackStmt
                    (seqStmts
                      [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
                      , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
                      , .assign 34 (.load (.bin .add (.reg 3) (.reg 32)))
                      , dfsPushCheckStmt ])) st2 .normal st3
                  ((Expr.bin .eq (.reg 32) (.reg 33)).size + c3 + 1) :=
                runs_cond_iff.mpr ⟨1, c3, hev_pe, by simpa using hrun3, rfl⟩
              rcases runs_seq_iff.mp hrun2 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
              · cases h
              have hbody : ∃ cB, Runs w p ω dfsStepBodyStmt st0 .normal st3 cB ∧ cB ≤ c1 + (ca + cb + 1) + c3 + 20 := by
                refine ⟨(Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).size +
                  ((Expr.bin .eq (.reg 30) (.reg 19)).size +
                    (c1 + (ca + (cb + ((Expr.bin .eq (.reg 32) (.reg 33)).size + c3 + 1) + 1) + 1) + 1) + 1) + 1, ?_, ?_⟩
                · unfold dfsStepBodyStmt
                  refine runs_cond_iff.mpr ⟨0, _, hev_nT, ?_, rfl⟩
                  simp only [↓reduceIte]
                  refine runs_cond_iff.mpr ⟨0, _, hev_nrj, ?_, rfl⟩
                  simp only [↓reduceIte]; dsimp only [seqStmts]
                  exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
                    runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
                      runs_seq_iff.mpr (Or.inr ⟨st2, cb, _, hrb, hcond_ptr, rfl⟩), rfl⟩), rfl⟩)
                · simp only [Expr.size]; omega
              rcases hbody with ⟨cB, hrunB, hcB⟩
              cases trail with
              | nil =>
                have hexit : Runs w p ω dfsStepLoopStmt st3 .normal st3 ((Expr.reg 29).size + 1) :=
                  runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hbt], rfl, rfl, rfl⟩)
                refine ⟨st3, _,
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, cB, _, hloop_guard, by omega, hrunB, hexit, rfl⟩)),
                  ?_, ?_⟩
                · simp only [dfsStep, huT, ↓reduceIte, hrj, hcur_nil]
                  exact ⟨heapPtr, pathsHead, pathsTail, ul, hinv3.cost_irrel rfl rfl rfl rfl, hregs3,
                    hr3_27.trans hst2_r27, hbt⟩
                · simp only [dfsStep, huT, ↓reduceIte, hrj, hcur_nil, Expr.size] at hc1 hc2 hc3 hcB ⊢; omega
              | cons pe rest =>
                rcases pe with ⟨par, e⟩
                rcases hbt with ⟨hr3_29, hr3_30, hr3_31, hstk3⟩
                set ds1 : DFSState := { ds with dead := insert u ds.dead, cost := ds.cost + 1 }
                have hpot1 : dfsPot V ds1 = pot' := by
                  have := dfsPot_insert_dead_eq V ds huV huD; dsimp only [ds1]; omega
                obtain ⟨st4, c4, hrun4, hpost4, hc4⟩ :=
                  ih (fuel := fuel') par (r - 1) rest ds1 ul heapPtr pathsHead pathsTail st3
                    hpot1 (by omega) hinv3 hstk3 hregs3 hr3_28 hr3_29 hr3_30 hr3_31 ω
                have hadd := dfsStep_cost_add V T dist cfg.targetDepth s fuel' par (r - 1) rest
                  { ds1 with cost := 0 } 1
                set dsA := dfsStep V T dist cfg.targetDepth s fuel' par (r - 1) rest { ds1 with cost := 1 }
                set dsB := dfsStep V T dist cfg.targetDepth s fuel' par (r - 1) rest { ds1 with cost := 0 }
                have hAB : dsA = { dsB with cost := dsB.cost + 1 } := by
                  rcases hadd with ⟨h1, h2, h3, h4, h5⟩
                  cases hA : dsA; cases hB : dsB
                  simp only [dsA, dsB, hA, hB] at h1 h2 h3 h4 h5
                  simp only [h1, h2, h3, h4, h5]
                have hstep_eq :
                    dfsStep V T dist cfg.targetDepth s (fuel' + 1) u r ((par, e) :: rest) { ds with cost := 0 } =
                      { dsB with cost := dsB.cost + 1 } := by
                  rw [← hAB]; simp only [dfsStep, huT, ↓reduceIte, hrj, hcur_nil, dsA, ds1]
                refine ⟨st4, _,
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, cB, c4, hloop_guard, by omega, hrunB, hrun4, rfl⟩)),
                  ?_, ?_⟩
                · rw [hstep_eq]
                  rcases hpost4 with ⟨hp4, ph4, pt4, ul4, hinv4, hregs4, hr4_27, hr4_29⟩
                  exact ⟨hp4, ph4, pt4, ul4, hinv4.cost_irrel rfl rfl rfl rfl, hregs4,
                    hr4_27.trans (hr3_27.trans hst2_r27), hr4_29⟩
                · rw [hstep_eq]
                  simp only [Expr.size] at hc1 hc2 hc3 hcB hc4 ⊢; omega
          · -- Case 3b: ptr < endPtr (advance cursor and inspect (wn, en))
            have hptr_lt : ptr < endPtr := by omega
            set idx := ptr - adjCsrOff X adj (locOf X u)
            have hidx_lt : idx < (adj u).length := by omega
            set we := (adj u)[idx]'hidx_lt
            set wn := we.1
            set en := we.2
            have hcur_cons : ds.cursor u = (wn, en) :: (adj u).drop (idx + 1) := by
              rw [hcur_drop, List.drop_eq_getElem_cons hidx_lt]
            have hwn_X : wn ∈ X := hadj_X u huX we (List.getElem_mem hidx_lt)
            have hwn_loc_lt : locOf X wn < X.card := locOf_lt hwn_X
            have hptr_lt_m2 : ptr < m2 := by
              have hle_end : endPtr ≤ adjCsrOff X adj X.card := adjCsrOff_mono X adj (by omega)
              omega
            have hnb_ptr : st2.mem (cfg.nbAddr + ptr) = locOf X wn := by
              have hfr_nb : st2.mem (cfg.nbAddr + ptr) = mem0 (cfg.nbAddr + ptr) :=
                hinv1.frame_out _ (hdisj.ro_nb _ ⟨by omega, by omega⟩)
              rw [hfr_nb]
              have h2 := hcsr.1.2 (locOf X u) hu_loc_lt idx (by rw [origOf_locOf huX]; exact hidx_lt)
              have hadd_eq : cfg.nbAddr + adjCsrOff X adj (locOf X u) + idx = cfg.nbAddr + ptr := by omega
              rw [hadd_eq] at h2
              simpa [origOf_locOf huX, wn, we] using h2
            have hedge_ptr : st2.mem (cfg.edgeAddr + ptr) = en := by
              have hfr_e : st2.mem (cfg.edgeAddr + ptr) = mem0 (cfg.edgeAddr + ptr) :=
                hinv1.frame_out _ (hdisj.ro_edge _ ⟨by omega, by omega⟩)
              rw [hfr_e]
              have h2 := hcsr.2 (locOf X u) hu_loc_lt idx (by rw [origOf_locOf huX]; exact hidx_lt)
              have hadd_eq : cfg.edgeAddr + adjCsrOff X adj (locOf X u) + idx = cfg.edgeAddr + ptr := by omega
              rw [hadd_eq] at h2
              simpa [origOf_locOf huX, en, we] using h2
            set mem3 := Function.update st2.mem (cfg.curAddr + locOf X u) (ptr + 1)
            set st3 : State :=
              { mem := mem3, regs := Function.update (Function.update st2.regs 33 (locOf X wn)) 34 en, pos := st2.pos }
            have hadv : ∃ c3,
                Runs w p ω
                  (seqStmts
                    [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
                    , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
                    , .assign 34 (.load (.bin .add (.reg 3) (.reg 32))) ])
                  st2 .normal st3 c3 ∧ c3 ≤ 24 := by
              have hw_cur := hdisj.w_cur; have hw_nb := hdisj.w_nb; have hw_edge := hdisj.w_edge
              have hw_m2 := hdisj.w_m2
              have hne_nb : cfg.nbAddr + ptr ≠ cfg.curAddr + locOf X u := fun heq =>
                hdisj.ro_nb (cfg.nbAddr + ptr) ⟨by omega, by omega⟩ (Or.inr (Or.inl ⟨by omega, by omega⟩))
              have hne_ed : cfg.edgeAddr + ptr ≠ cfg.curAddr + locOf X u := fun heq =>
                hdisj.ro_edge (cfg.edgeAddr + ptr) ⟨by omega, by omega⟩ (Or.inr (Or.inl ⟨by omega, by omega⟩))
              have htr : Triple w p (fun st => st = st2)
                  (seqStmts
                    [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
                    , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
                    , .assign 34 (.load (.bin .add (.reg 3) (.reg 32))) ])
                  (normalPost fun st => st = st3) (fun _ => 24) := by
                wram_enter; subst st; dsimp only [seqStmts]
                have h2_12 : st2.regs 12 = cfg.curAddr := hst2_regs_inv 12 (by decide)
                have h2_2 : st2.regs 2 = cfg.nbAddr := hst2_regs_inv 2 (by decide)
                have h2_3 : st2.regs 3 = cfg.edgeAddr := hst2_regs_inv 3 (by decide)
                refine runs_seq_store_le (x := cfg.curAddr + locOf X u) (v := ptr + 1)
                  (by eval_expr) (by eval_expr) ?_
                refine runs_seq_assign_le (v := locOf X wn)
                  (by rw [← hnb_ptr, ← Function.update_of_ne hne_nb (ptr + 1) st2.mem]; eval_expr) ?_
                refine runs_assign_le (v := en)
                  (by rw [← hedge_ptr, ← Function.update_of_ne hne_ed (ptr + 1) st2.mem]; eval_expr)
                  rfl (by wram_cost)
              obtain ⟨o3, st3', c3, hr3', hp3, hc3⟩ := htr st2 ω rfl
              cases o3 with | returned _ => exact hp3.elim | normal => subst hp3; exact ⟨c3, hr3', hc3⟩
            rcases hadv with ⟨c3, hrun3, hc3⟩
            set ds1 : DFSState :=
              { ds with cursor := Function.update ds.cursor u ((adj u).drop (idx + 1)), cost := ds.cost + 1 }
            have hinv3 : DfsStateAt mem3 mem0 X V adj cfg cfgAddr heapLo heapPtr pathsHead pathsTail acc ds1 ul := by
              have hfr_m3 : ∀ a, a ≠ cfg.curAddr + locOf X u → mem3 a = st1.mem a :=
                fun a h => Function.update_of_ne h _ _
              refine ⟨hinv1.used_sub, hinv1.dead_sub, hinv1.paths_le, ?_, ?_, ?_,
                hinv1.ul_len, hinv1.ul_nd, hinv1.ul_sub, hinv1.ul_cov, ?_, hinv1.heap_lo, hinv1.heap_hi,
                ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro v hv
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cur_us hu_loc_lt hv; omega)]
                exact hinv1.used_stamp v hv
              · intro v hv
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cur_ds hu_loc_lt hv; omega)]
                exact hinv1.dead_stamp v hv
              · intro v hv
                by_cases hveq : v = locOf X u
                · subst hveq
                  have hcs3 : mem3 (cfg.curStampAddr + locOf X u) = cfg.dfsGen := by
                    rw [hfr_m3 _ (by have := disjRange_ne hdisj.cs_cur hu_loc_lt hu_loc_lt; omega)]; exact hst1_cs
                  refine ⟨fun h => absurd hcs3 h, fun _ => ?_⟩
                  simp only [mem3, Function.update_self, ds1, origOf_locOf huX]
                  exact ⟨by omega, by omega, by rw [show ptr + 1 - adjCsrOff X adj (locOf X u) = idx + 1 by omega]⟩
                · have hne_orig : origOf X v ≠ u := fun h => hveq (by rw [← h, locOf_origOf hv])
                  rw [hfr_m3 _ (by have := disjRange_ne hdisj.cs_cur hv hu_loc_lt; omega),
                      hfr_m3 _ (by omega)]
                  simpa [ds1, Function.update_of_ne hne_orig] using hinv1.cur_inv v hv
              · intro j hj
                have hle : ul.length ≤ X.card := by
                  rw [hinv1.ul_len]; exact Finset.card_le_card (Finset.Subset.trans hinv1.used_sub hVX)
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cur_ul hu_loc_lt (by omega : j < X.card); omega)]
                exact hinv1.ul_at j hj
              · exact hinv1.chain.congr (fun k hk1 hk2 => hfr_m3 k (by
                  by_cases hlt : k < cfg.heapIn
                  · intro h; subst h; exact hacc_disj _ ⟨hk1, hlt⟩ (Or.inr (Or.inl ⟨by omega, by omega⟩))
                  · have hhi : heapPtr ≤ cfg.heapIn + 5 * X.card := by
                      have := hinv1.heap_hi; have := Finset.card_le_card (Finset.Subset.trans hinv1.used_sub hVX); omega
                    have := disjRange_ne hdisj.cur_hp hu_loc_lt (by omega : k - cfg.heapIn < 5 * X.card); omega))
              · intro a ha
                rw [hfr_m3 a (fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
                exact hinv1.frame_out a ha
              · intro a ha
                rw [hfr_m3 a (by rcases hdisj.cur_co with h | h <;> omega)]
                exact hinv1.frame_cfgOut a ha
              · intro v hv
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cs_cur hv hu_loc_lt; omega)]
                exact hinv1.stamp_cur v hv
              · intro v hv
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cur_us hu_loc_lt hv; omega)]
                exact hinv1.stamp_used v hv
              · intro v hv
                rw [hfr_m3 _ (by have := disjRange_ne hdisj.cur_ds hu_loc_lt hv; omega)]
                exact hinv1.stamp_dead v hv
            have hstk3 : DfsStackAt mem3 X V dist cfg ds1 s u r trail := by
              have hlen_sv : (stackVerts u trail).reverse.length ≤ X.card := by
                have hnd := stackVerts_nodup_of_dist fun k hk => (hstk1.stack_ok k hk).2.2.2
                have hsub : (stackVerts u trail).reverse.toFinset ⊆ X := fun x hx => by
                  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
                  exact hVX (hstk1.stack_ok k hk).1
                have := Finset.card_le_card hsub; rwa [List.toFinset_card_of_nodup hnd] at this
              refine ⟨hstk1.r_le, hstk1.trail_len, hstk1.s_eq, ?_, ?_, hstk1.stack_ok⟩
              · intro j hj; simp only [List.length_map] at hj
                dsimp only [mem3]
                rw [Function.update_of_ne (by have := disjRange_ne hdisj.cur_sv hu_loc_lt (by omega : j < X.card); omega)]
                exact hstk1.vert_at j (by simpa using hj)
              · intro j hj; simp only [List.length_reverse, List.length_map, hstk1.trail_len] at hj
                have hr_lt : r < X.card := by simp [stackVerts, hstk1.trail_len] at hlen_sv; omega
                dsimp only [mem3]
                rw [Function.update_of_ne (by have := disjRange_ne hdisj.cur_se hu_loc_lt (by omega : j < X.card); omega)]
                exact hstk1.edge_at j (by simp [hstk1.trail_len, hj])
            have hwn_V_iff : mem3 (cfg.maskArrAddr + locOf X wn) ≠ cfg.maskBadVal ↔ wn ∈ V := by
              rw [hinv3.frame_out _ (hdisj.ro_mask _ ⟨by omega, by omega⟩), hmask _ hwn_loc_lt, origOf_locOf hwn_X]
            have hwn_dist_iff :
                (mem3 (cfg.visStampAddr + locOf X wn) = cfg.bfsGen ∧
                 mem3 (cfg.distAddr + locOf X wn) = r + 1) ↔ dist wn = some (r + 1) := by
              rw [hinv3.frame_out _ (hdisj.ro_vis _ ⟨by omega, by omega⟩),
                  hinv3.frame_out _ (hdisj.ro_dist _ ⟨by omega, by omega⟩)]
              rcases hdist_mem (locOf X wn) hwn_loc_lt with ⟨hv, hd⟩ | ⟨hv, hd⟩
              · rw [origOf_locOf hwn_X] at hd; simp [hv, hd]
              · rw [origOf_locOf hwn_X] at hd; simp [hv, hd]
            have hst3_regs : DfsRegsAt st3.regs cfg cfgAddr heapPtr pathsHead pathsTail ds1.used.card ds1.paths.length :=
              fun k hk => by
                simp only [st3, Function.update_of_ne (by omega : k ≠ 34), Function.update_of_ne (by omega : k ≠ 33)]
                exact hst2_regs_inv k hk
            have hst3_r27 : st3.regs 27 = st0.regs 27 := by simp [st3, hst2_r27]
            have hst3_r28 : st3.regs 28 = locOf X s := by simp [st3, hst2_r28]
            have hst3_r29 : st3.regs 29 = 1 := by simp [st3, hst2_r29]
            have hst3_r30 : st3.regs 30 = r := by simp [st3, hst2_r30]
            have hst3_r31 : st3.regs 31 = locOf X u := by simp [st3, hst2_r31]
            have hst3_r33 : st3.regs 33 = locOf X wn := by simp [st3]
            have hst3_r34 : st3.regs 34 = en := by simp [st3]
            have hpot1 : dfsPot V ds1 = pot' := by
              have := dfsPot_update_cursor_tail V ds huV hcur_cons
              dsimp only [ds1]; omega
            have hev_pne : (Expr.bin .eq (.reg 32) (.reg 33)).eval w st2 = some 0 := by
              simp [Expr.eval, BinOp.eval, hst2_r32, hst2_r33, hptr_eq, show 0 < 2 ^ w by omega]
            rcases runs_seq_iff.mp hrun2 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
            · cases h
            rcases runs_seq_iff.mp hrun3 with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩
            · cases h
            rcases runs_seq_iff.mp hrb2 with ⟨_, _, _, h, _⟩ | ⟨sc, cc1, cc2, hrc1, hrc2, rfl⟩
            · cases h
            have hstitch : ∀ {st4 c4}, Runs w p ω dfsPushCheckStmt st3 .normal st4 c4 → c4 ≤ 60 →
                ∃ cB, Runs w p ω dfsStepBodyStmt st0 .normal st4 cB ∧ cB ≤ 144 := by
              intro st4 c4 hrun4 hc4
              have hbranch : Runs w p ω
                  (seqStmts
                    [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
                    , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
                    , .assign 34 (.load (.bin .add (.reg 3) (.reg 32)))
                    , dfsPushCheckStmt ])
                  st2 .normal st4 (cb1 + (cc1 + (cc2 + c4 + 1) + 1) + 1) := by
                dsimp only [seqStmts]
                exact runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
                  runs_seq_iff.mpr (Or.inr ⟨sc, cc1, _, hrc1,
                    runs_seq_iff.mpr (Or.inr ⟨st3, cc2, _, hrc2, hrun4, rfl⟩), rfl⟩), rfl⟩)
              have hcond_ptr : Runs w p ω
                  (.cond (.bin .eq (.reg 32) (.reg 33)) dfsBacktrackStmt
                    (seqStmts
                      [ .store (.bin .add (.reg 12) (.reg 31)) (.bin .add (.reg 32) (.const 1))
                      , .assign 33 (.load (.bin .add (.reg 2) (.reg 32)))
                      , .assign 34 (.load (.bin .add (.reg 3) (.reg 32)))
                      , dfsPushCheckStmt ])) st2 .normal st4
                  ((Expr.bin .eq (.reg 32) (.reg 33)).size + (cb1 + (cc1 + (cc2 + c4 + 1) + 1) + 1) + 1) :=
                runs_cond_iff.mpr ⟨0, _, hev_pne, by simpa using hbranch, rfl⟩
              refine ⟨(Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 31))) (.reg 7)).size +
                ((Expr.bin .eq (.reg 30) (.reg 19)).size +
                  (c1 + (ca + (cb + ((Expr.bin .eq (.reg 32) (.reg 33)).size + (cb1 + (cc1 + (cc2 + c4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1, ?_, ?_⟩
              · unfold dfsStepBodyStmt
                refine runs_cond_iff.mpr ⟨0, _, hev_nT, ?_, rfl⟩
                simp only [↓reduceIte]
                refine runs_cond_iff.mpr ⟨0, _, hev_nrj, ?_, rfl⟩
                simp only [↓reduceIte]; dsimp only [seqStmts]
                exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1,
                  runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
                    runs_seq_iff.mpr (Or.inr ⟨st2, cb, _, hrb, hcond_ptr, rfl⟩), rfl⟩), rfl⟩)
              · simp only [Expr.size] at hc1 hc2 hc3 hc4 ⊢; omega
            by_cases hcond : wn ∈ V ∧ wn ∉ ds.used ∧ wn ∉ ds.dead ∧ r < cfg.targetDepth ∧ dist wn = some (r + 1)
            · obtain ⟨o4, st4, c4, hrun4, hpost4, hc4⟩ :=
                dfsPushCheck_true (p := p) hVX hdisj hacc_disj hinv3 hstk3 hst3_regs
                  hst3_r28 hst3_r29 hst3_r30 hst3_r33 hst3_r34 hwn_X
                  hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2.1 hcond.2.2.2.2 hwn_V_iff hwn_dist_iff st3 ω rfl
              cases o4 with
              | returned _ => exact hpost4.elim
              | normal =>
                rcases hpost4 with ⟨hinv4, hstk4, hregs4, hr4_27, hr4_28, hr4_29, hr4_30, hr4_31⟩
                obtain ⟨cB, hrunB, hcB⟩ := hstitch hrun4 hc4
                obtain ⟨st5, c5, hrun5, hpost5, hc5⟩ :=
                  ih (fuel := fuel') wn (r + 1) ((u, en) :: trail) ds1 ul heapPtr pathsHead pathsTail st4
                    hpot1 (by omega) hinv4 hstk4 hregs4 hr4_28 hr4_29 hr4_30 hr4_31 ω
                have hadd := dfsStep_cost_add V T dist cfg.targetDepth s fuel' wn (r + 1) ((u, en) :: trail)
                  { ds1 with cost := 0 } 1
                set dsA := dfsStep V T dist cfg.targetDepth s fuel' wn (r + 1) ((u, en) :: trail) { ds1 with cost := 1 }
                set dsB := dfsStep V T dist cfg.targetDepth s fuel' wn (r + 1) ((u, en) :: trail) { ds1 with cost := 0 }
                have hAB : dsA = { dsB with cost := dsB.cost + 1 } := by
                  rcases hadd with ⟨h1, h2, h3, h4, h5⟩
                  cases hA : dsA; cases hB : dsB
                  simp only [dsA, dsB, hA, hB] at h1 h2 h3 h4 h5
                  simp only [h1, h2, h3, h4, h5]
                have hstep_eq :
                    dfsStep V T dist cfg.targetDepth s (fuel' + 1) u r trail { ds with cost := 0 } =
                      { dsB with cost := dsB.cost + 1 } := by
                  rw [← hAB]
                  simp only [dfsStep, huT, hrj, hcur_cons, hcond, not_false_eq_true, and_self, ↓reduceIte, dsA, ds1]
                refine ⟨st5, _,
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st4, cB, c5, hloop_guard, by omega, hrunB, hrun5, rfl⟩)),
                  ?_, ?_⟩
                · rw [hstep_eq]
                  rcases hpost5 with ⟨hp5, ph5, pt5, ul5, hinv5, hregs5, hr5_27, hr5_29⟩
                  exact ⟨hp5, ph5, pt5, ul5, hinv5.cost_irrel rfl rfl rfl rfl, hregs5,
                    hr5_27.trans (hr4_27.trans hst3_r27), hr5_29⟩
                · rw [hstep_eq]
                  simp only [Expr.size] at hcB hc5 ⊢; omega
            · obtain ⟨o4, st4, c4, hrun4, hpost4, hc4⟩ :=
                dfsPushCheck_false (p := p) hdisj hinv3 hst3_regs hst3_r30 hst3_r33 hwn_X hr_lt_j
                  hwn_V_iff hwn_dist_iff hcond st3 ω rfl
              cases o4 with
              | returned _ => exact hpost4.elim
              | normal =>
                subst hpost4
                obtain ⟨cB, hrunB, hcB⟩ := hstitch hrun4 (by dsimp only at hc4; omega)
                obtain ⟨st5, c5, hrun5, hpost5, hc5⟩ :=
                  ih (fuel := fuel') u r trail ds1 ul heapPtr pathsHead pathsTail st3
                    hpot1 (by omega) hinv3 hstk3 hst3_regs hst3_r28 hst3_r29 hst3_r30 hst3_r31 ω
                have hadd := dfsStep_cost_add V T dist cfg.targetDepth s fuel' u r trail
                  { ds1 with cost := 0 } 1
                set dsA := dfsStep V T dist cfg.targetDepth s fuel' u r trail { ds1 with cost := 1 }
                set dsB := dfsStep V T dist cfg.targetDepth s fuel' u r trail { ds1 with cost := 0 }
                have hAB : dsA = { dsB with cost := dsB.cost + 1 } := by
                  rcases hadd with ⟨h1, h2, h3, h4, h5⟩
                  cases hA : dsA; cases hB : dsB
                  simp only [dsA, dsB, hA, hB] at h1 h2 h3 h4 h5
                  simp only [h1, h2, h3, h4, h5]
                have hstep_eq :
                    dfsStep V T dist cfg.targetDepth s (fuel' + 1) u r trail { ds with cost := 0 } =
                      { dsB with cost := dsB.cost + 1 } := by
                  rw [← hAB]
                  simp only [dfsStep, huT, hrj, hcur_cons, hcond, ↓reduceIte, dsA, ds1]
                refine ⟨st5, _,
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, cB, c5, hloop_guard, by omega, hrunB, hrun5, rfl⟩)),
                  ?_, ?_⟩
                · rw [hstep_eq]
                  rcases hpost5 with ⟨hp5, ph5, pt5, ul5, hinv5, hregs5, hr5_27, hr5_29⟩
                  exact ⟨hp5, ph5, pt5, ul5, hinv5.cost_irrel rfl rfl rfl rfl, hregs5,
                    hr5_27.trans hst3_r27, hr5_29⟩
                · rw [hstep_eq]
                  simp only [Expr.size] at hcB hc5 ⊢; omega

end MinCostFlow.ExpanderDecomp
