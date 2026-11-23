module

public import MinCostFlow.Spanner.ProgTask2StepsMiddlePre
public import MinCostFlow.Spanner.ProgTask2StepsDrain

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Helper definitions and execution lemmas for `t2MiddleStage34` -/

/-- Register-and-memory state after lines 378–389 of `t2MiddleEdgeBody` (preamble of `t2MiddleStage34`). -/
def t2MiddlePreState (st : State) (v1 qid_next wVal embJHAddr ewA vcA psA τ₁Val η₁ qA : ℕ) : State :=
  { mem := Function.update st.mem (v1 + 26) qid_next
    regs :=
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update st.regs 25 qid_next)
            26 wVal) 27 embJHAddr) 28 ewA) 29 vcA) 30 psA)
            31 τ₁Val) 32 η₁) 33 qA) 34 0) 35 0
    pos := st.pos }

/-- Memory state after lines 413–418 of `t2MiddleEdgeBody` (postamble of `t2MiddleStage34`). -/
def t2MiddlePostMem (mem : ℕ → ℕ)
    (embWJAddr eW v1 arenaPtr encLen gpCnt newVcong newCard qlen : ℕ) : ℕ → ℕ :=
  let m0 := Function.update mem (embWJAddr + eW) arenaPtr
  let m1 := Function.update m0 (v1 + 25) (arenaPtr + encLen)
  let m2 := Function.update m1 (v1 + 4) (gpCnt + 1)
  let m3 := Function.update m2 (v1 + 6) newVcong
  let m4 := Function.update m3 (v1 + 30) newCard
  Function.update m4 (v1 + 27) qlen

private lemma runs_assign_v1_ld {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (r k v inp_v1 : ℕ) (hk : k < 2 ^ w) (haddr : inp_v1 + k < 2 ^ w)
    (hr0 : st.regs 0 = inp_v1) (hm : st.mem (inp_v1 + k) = v) :
    Runs w p ω (Stmt.assign r (t2Ld (.reg 0) (.const k))) st .normal
      { st with regs := Function.update st.regs r v } 5 := by
  have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0) (Expr.eval_const hk) haddr
  have hl : (t2Ld (.reg 0) (.const k)).eval w st = some v := hm ▸ Expr.eval_load ha
  exact runs_assign_iff.mpr ⟨v, hl, rfl, rfl, by simp [Expr.size]⟩

lemma t2Middle_stage34_pre_run {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {ci eL eW arena0 : ℕ}
    (hci : ci < ctx.wd.comps.length) (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hqid_w : g₀.queryId + 1 < 2 ^ w) (hwWNum_w : msf.wWNumAddr + eW < 2 ^ w)
    (hw14_w : ctx.wInp.h + 14 < 2 ^ w) (hv1_w : inp.v1 + 32 < 2 ^ w)
    (har_lo : stc.nodesEnd ≤ arena0) (P_sub_vlen : ℕ)
    (st : State) (ω : ℕ → Bool)
    (hr0 : st.regs 0 = inp.v1) (hr3 : st.regs 3 = eW) (hr10 : st.regs 10 = ctx.wInp.h)
    (hm_start : ∀ a < stc.dsBaseAddr, ¬(arena0 ≤ a ∧ a ≤ arena0 + 1 + P_sub_vlen) →
      st.mem a = memStart a)
    (cont : Stmt) {o : Outcome} {stF : State} {c_cont : ℕ}
    (hcont : Runs w p ω cont
      (t2MiddlePreState st inp.v1 (g₀.queryId + 1) (memStart (msf.wWNumAddr + eW)) inp.embJHAddr
        (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (memStart (inp.v1 + 28)) g₀.η₁
        (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)) o stF c_cont) :
    Runs w p ω
      (Stmt.assign 25 (t2Add (t2Ld (.reg 0) (.const 26)) (.const 1)) ;;
       t2St (.reg 0) (.const 26) (.reg 25) ;;
       Stmt.assign 26 (t2Ld (t2Ld (.reg 10) (.const 14)) (.reg 3)) ;;
       Stmt.assign 27 (t2Ld (.reg 0) (.const 12)) ;;
       Stmt.assign 28 (t2Ld (.reg 0) (.const 23)) ;;
       Stmt.assign 29 (t2Ld (.reg 0) (.const 21)) ;;
       Stmt.assign 30 (t2Ld (.reg 0) (.const 22)) ;;
       Stmt.assign 31 (t2Ld (.reg 0) (.const 28)) ;;
       Stmt.assign 32 (t2Ld (.reg 0) (.const 1)) ;;
       Stmt.assign 33 (t2Ld (.reg 0) (.const 24)) ;;
       Stmt.assign 34 (.const 0) ;;
       Stmt.assign 35 (.const 0) ;; cont) st o stF (71 + c_cont) := by
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc
  have hw1 := db.h_w1
  have hst_v1 : ∀ k < 32, st.mem (inp.v1 + k) = memStart (inp.v1 + k) := fun k hk =>
    hm_start (inp.v1 + k) (by omega) (by omega)
  have hw26_addr : inp.v1 + 26 < 2 ^ w := by omega
  set s25 : State := { st with regs := Function.update st.regs 25 (g₀.queryId + 1) }
  have hr25_st : Runs w p ω (Stmt.assign 25 (t2Add (t2Ld (.reg 0) (.const 26)) (.const 1))) st .normal s25 7 := by
    have h1 : st.mem (inp.v1 + 26) = g₀.queryId := (hst_v1 26 (by omega)).trans hS.h26
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 26 < 2 ^ w)) hw26_addr
    have hl : (t2Ld (.reg 0) (.const 26)).eval w st = some g₀.queryId := h1 ▸ Expr.eval_load ha
    have ha2 := Expr.eval_add (w := w) hl (Expr.eval_const hw1) hqid_w
    exact runs_assign_iff.mpr ⟨g₀.queryId + 1, ha2, rfl, rfl, by simp [Expr.size]⟩
  set mq := Function.update st.mem (inp.v1 + 26) (g₀.queryId + 1)
  set smq : State := { s25 with mem := mq }
  have hs25_0 : s25.regs 0 = inp.v1 := by
    change Function.update st.regs 25 (g₀.queryId + 1) 0 = inp.v1
    rw [Function.update_of_ne (by omega)]; exact hr0
  have hm_q : Runs w p ω (t2St (.reg 0) (.const 26) (.reg 25)) s25 .normal smq 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hs25_0)
      (Expr.eval_const (by omega : 26 < 2 ^ w)) hw26_addr
    exact runs_store_iff.mpr ⟨inp.v1 + 26, g₀.queryId + 1, ha,
      Expr.eval_reg_of_eq (by change Function.update st.regs 25 (g₀.queryId + 1) 25 = _; exact Function.update_self _ _ _),
      rfl, rfl, by simp [Expr.size]⟩
  have hmq_v1 : ∀ k < 32, k ≠ 26 → mq (inp.v1 + k) = memStart (inp.v1 + k) := fun k hk hne => by
    dsimp only [mq]; rw [Function.update_of_ne (by omega)]; exact hst_v1 k hk
  set s26 : State := { smq with regs := Function.update smq.regs 26 (memStart (msf.wWNumAddr + eW)) }
  have hr26_st : Runs w p ω (Stmt.assign 26 (t2Ld (t2Ld (.reg 10) (.const 14)) (.reg 3))) smq .normal s26 8 := by
    have hm := mkW_W_edges_comp (pds := impl.pathDS.params) ctx.hws hci heL
    have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
    have hw_lt_v1 : msf.wWNumAddr + eW < inp.v1 := by have := msf.hwWNum_lt; omega
    have h14_lt_v1 : ctx.wInp.h + 14 < inp.v1 := by
      have ⟨_, _, _, _, _, _, _, hstOut⟩ := ctx.agrees_preserves_static hS.agr_pre
      have ⟨_, _, _, _, _, _, _, _, _, _, _, ha1, _⟩ := hstOut
      have : ctx.wInp.h + 20 ≤ msf.aCompExt := by rwa [← msf.haCompExt_ptr]
      have := msf.haCompExt_lt; have := msf.hwWNum_lt; omega
    have h14_eq : smq.mem (ctx.wInp.h + 14) = msf.wWNumAddr := by
      dsimp only [smq, mq]; rw [Function.update_of_ne (by omega), hm_start _ (by omega) (by omega)]
      exact msf.hwWNum_ptr
    have hw_eq : smq.mem (msf.wWNumAddr + eW) = memStart (msf.wWNumAddr + eW) := by
      dsimp only [smq, mq]; rw [Function.update_of_ne (by omega)]; exact hm_start _ (by omega) (by omega)
    have hsmq_10 : smq.regs 10 = ctx.wInp.h := by
      change Function.update st.regs 25 (g₀.queryId + 1) 10 = ctx.wInp.h
      rw [Function.update_of_ne (by omega)]; exact hr10
    have hsmq_3 : smq.regs 3 = eW := by
      change Function.update st.regs 25 (g₀.queryId + 1) 3 = eW
      rw [Function.update_of_ne (by omega)]; exact hr3
    have ha1 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hsmq_10)
      (Expr.eval_const (by omega : 14 < 2 ^ w)) hw14_w
    have hl1 : (t2Ld (.reg 10) (.const 14)).eval w smq = some msf.wWNumAddr :=
      h14_eq ▸ Expr.eval_load ha1
    have ha2 := Expr.eval_add (w := w) hl1 (Expr.eval_reg_of_eq hsmq_3) hwWNum_w
    have hl2 : (t2Ld (t2Ld (.reg 10) (.const 14)) (.reg 3)).eval w smq =
        some (memStart (msf.wWNumAddr + eW)) := hw_eq ▸ Expr.eval_load ha2
    exact runs_assign_iff.mpr ⟨memStart (msf.wWNumAddr + eW), hl2, rfl, rfl, by simp [Expr.size]⟩
  set s27 := { s26 with regs := Function.update s26.regs 27 inp.embJHAddr }
  have hr27_st : Runs w p ω (Stmt.assign 27 (t2Ld (.reg 0) (.const 12))) s26 .normal s27 5 :=
    runs_assign_v1_ld s26 27 12 inp.embJHAddr inp.v1 (by omega) (by omega)
      (by dsimp only [s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 12 (by omega) (by omega)).trans hS.h12)
  set s28 := { s27 with regs := Function.update s27.regs 28 (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr28_st : Runs w p ω (Stmt.assign 28 (t2Ld (.reg 0) (.const 23))) s27 .normal s28 5 :=
    runs_assign_v1_ld s27 28 23 _ inp.v1 (by omega) (by omega)
      (by dsimp only [s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 23 (by omega) (by omega)).trans hS.h23)
  set s29 := { s28 with regs := Function.update s28.regs 29 (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr29_st : Runs w p ω (Stmt.assign 29 (t2Ld (.reg 0) (.const 21))) s28 .normal s29 5 :=
    runs_assign_v1_ld s28 29 21 _ inp.v1 (by omega) (by omega)
      (by dsimp only [s28, s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 21 (by omega) (by omega)).trans hS.h21)
  set s30 := { s29 with regs := Function.update s29.regs 30 (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr30_st : Runs w p ω (Stmt.assign 30 (t2Ld (.reg 0) (.const 22))) s29 .normal s30 5 :=
    runs_assign_v1_ld s29 30 22 _ inp.v1 (by omega) (by omega)
      (by dsimp only [s29, s28, s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 22 (by omega) (by omega)).trans hS.h22)
  set s31 := { s30 with regs := Function.update s30.regs 31 (memStart (inp.v1 + 28)) }
  have hr31_st : Runs w p ω (Stmt.assign 31 (t2Ld (.reg 0) (.const 28))) s30 .normal s31 5 :=
    runs_assign_v1_ld s30 31 28 _ inp.v1 (by omega) (by omega)
      (by dsimp only [s30, s29, s28, s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      (hmq_v1 28 (by omega) (by omega))
  set s32 := { s31 with regs := Function.update s31.regs 32 g₀.η₁ }
  have hr32_st : Runs w p ω (Stmt.assign 32 (t2Ld (.reg 0) (.const 1))) s31 .normal s32 5 :=
    runs_assign_v1_ld s31 32 1 g₀.η₁ inp.v1 (by omega) (by omega)
      (by dsimp only [s31, s30, s29, s28, s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 1 (by omega) (by omega)).trans hS.h1)
  set s33 := { s32 with regs := Function.update s32.regs 33 (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr33_st : Runs w p ω (Stmt.assign 33 (t2Ld (.reg 0) (.const 24))) s32 .normal s33 5 :=
    runs_assign_v1_ld s32 33 24 _ inp.v1 (by omega) (by omega)
      (by dsimp only [s32, s31, s30, s29, s28, s27, s26, smq, s25]; simp [Function.update_of_ne, hr0])
      ((hmq_v1 24 (by omega) (by omega)).trans hS.h24)
  set s34 := { s33 with regs := Function.update s33.regs 34 0 }
  have hr34_st : Runs w p ω (Stmt.assign 34 (.const 0)) s33 .normal s34 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
  set s35 := { s34 with regs := Function.update s34.regs 35 0 }
  have hr35_st : Runs w p ω (Stmt.assign 35 (.const 0)) s34 .normal s35 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
  have hrun := runs_seq_iff.mpr (Or.inr ⟨s25, 7, _, hr25_st,
    runs_seq_iff.mpr (Or.inr ⟨smq, 5, _, hm_q,
      runs_seq_iff.mpr (Or.inr ⟨s26, 8, _, hr26_st,
        runs_seq_iff.mpr (Or.inr ⟨s27, 5, _, hr27_st,
          runs_seq_iff.mpr (Or.inr ⟨s28, 5, _, hr28_st,
            runs_seq_iff.mpr (Or.inr ⟨s29, 5, _, hr29_st,
              runs_seq_iff.mpr (Or.inr ⟨s30, 5, _, hr30_st,
                runs_seq_iff.mpr (Or.inr ⟨s31, 5, _, hr31_st,
                  runs_seq_iff.mpr (Or.inr ⟨s32, 5, _, hr32_st,
                    runs_seq_iff.mpr (Or.inr ⟨s33, 5, _, hr33_st,
                      runs_seq_iff.mpr (Or.inr ⟨s34, 2, _, hr34_st,
                        runs_seq_iff.mpr (Or.inr ⟨s35, 2, c_cont, hr35_st, hcont, rfl⟩),
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  simpa only [show 7 + (5 + (8 + (5 + (5 + (5 + (5 + (5 + (5 + (5 + (2 + (2 + c_cont + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 71 + c_cont by omega] using hrun

lemma t2Middle_stage34_post_run {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {ci eL eW updV qlen : ℕ} {P_sub : Walk}
    (hci : ci < ctx.wd.comps.length) (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hPsub_le_γ : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    (hup_bd : updV ≤ P_sub.edges.length * (length inp.J inp.embJH + 1))
    (har_v1_w : g₀.arenaPtr + 1 + P_sub.verts.length + 1 < 2 ^ w)
    (har_enc_w : g₀.arenaPtr + 1 + P_sub.verts.length + 1 + P_sub.edges.length < 2 ^ w)
    (st : State) (ω : ℕ → Bool)
    (hr0 : st.regs 0 = inp.v1) (hr3 : st.regs 3 = eW) (hr18 : st.regs 18 = g₀.arenaPtr)
    (hr21 : st.regs 21 = P_sub.edges.length)
    (hr24 : st.regs 24 = g₀.arenaPtr + 1 + P_sub.verts.length)
    (hr34 : st.regs 34 = qlen) (hr35 : st.regs 35 = updV)
    (hv1_agr : ∀ k < 32, k ≠ 26 → st.mem (inp.v1 + k) = memStart (inp.v1 + k))
    (cont : Stmt) {o : Outcome} {stF : State} {c_cont : ℕ}
    (hcont : Runs w p ω cont
      { st with mem := (t2MiddlePostMem st.mem inp.embWJAddr eW inp.v1 g₀.arenaPtr
          (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).encode.length g₀.getPathCountJ
          (g₀.vcongUpdates + updV) ((unembeddedSetPure ctx.wd g₀.emb).card - 1) qlen) }
      o stF c_cont) :
    Runs w p ω
      (t2St (.load (.reg 0)) (.reg 3) (.reg 18) ;;
       t2St (.reg 0) (.const 25) (t2Add (t2Add (.reg 24) (.const 1)) (.reg 21)) ;;
       t2St (.reg 0) (.const 4) (t2Add (t2Ld (.reg 0) (.const 4)) (.const 1)) ;;
       t2St (.reg 0) (.const 6) (t2Add (t2Ld (.reg 0) (.const 6)) (.reg 35)) ;;
       t2St (.reg 0) (.const 30) (t2Sub (t2Ld (.reg 0) (.const 30)) (.const 1)) ;;
       t2St (.reg 0) (.const 27) (.reg 34) ;; cont) st o stF (56 + c_cont) := by
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mwb
  have hw1 := db.h_w1
  have hm := mkW_W_edges_comp (pds := impl.pathDS.params) ctx.hws hci heL
  have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
  set P_J := liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub
  have hP_J_enc : P_J.encode.length = 2 + P_sub.verts.length + P_sub.edges.length := by
    simp [P_J, liftJSubWalk, Walk.encode]; omega
  set m50 := Function.update st.mem (inp.embWJAddr + eW) g₀.arenaPtr
  set sm50 : State := { st with mem := m50 }
  have hm50_st : Runs w p ω (t2St (.load (.reg 0)) (.reg 3) (.reg 18)) st .normal sm50 6 := by
    have hv1_val : st.mem inp.v1 = inp.embWJAddr := by
      simpa using (hv1_agr 0 (by omega) (by omega)).trans hS.h0
    have hl : (Expr.load (.reg 0)).eval w st = some inp.embWJAddr :=
      hv1_val ▸ Expr.eval_load (Expr.eval_reg_of_eq hr0)
    have ha := Expr.eval_add (w := w) hl (Expr.eval_reg_of_eq hr3) (by omega)
    exact runs_store_iff.mpr ⟨inp.embWJAddr + eW, g₀.arenaPtr, ha,
      Expr.eval_reg_of_eq hr18, rfl, rfl, by simp [Expr.size]⟩
  set m51 := Function.update m50 (inp.v1 + 25) (g₀.arenaPtr + P_J.encode.length)
  set sm51 : State := { sm50 with mem := m51 }
  have hm51_st : Runs w p ω (t2St (.reg 0) (.const 25) (t2Add (t2Add (.reg 24) (.const 1)) (.reg 21))) sm50 .normal sm51 9 := by
    have ha_addr := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 25 < 2 ^ w)) (by omega)
    have ha1 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr24) (Expr.eval_const hw1) har_v1_w
    have ha2 := Expr.eval_add (w := w) ha1 (Expr.eval_reg_of_eq hr21) har_enc_w
    have heq_len : g₀.arenaPtr + 1 + P_sub.verts.length + 1 + P_sub.edges.length =
        g₀.arenaPtr + P_J.encode.length := by omega
    exact runs_store_iff.mpr ⟨inp.v1 + 25, g₀.arenaPtr + P_J.encode.length, ha_addr,
      heq_len ▸ ha2, rfl, rfl, by simp [Expr.size]⟩
  set m52 := Function.update m51 (inp.v1 + 4) (g₀.getPathCountJ + 1)
  set sm52 : State := { sm51 with mem := m52 }
  have hm52_st : Runs w p ω (t2St (.reg 0) (.const 4) (t2Add (t2Ld (.reg 0) (.const 4)) (.const 1))) sm51 .normal sm52 10 := by
    have h4_eq : sm51.mem (inp.v1 + 4) = g₀.getPathCountJ := by
      dsimp only [sm51, m51, sm50, m50]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hv1_agr 4 (by omega) (by omega)).trans hS.h4
    have ha_addr := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 4 < 2 ^ w)) (by omega)
    have hl : (t2Ld (.reg 0) (.const 4)).eval w sm51 = some g₀.getPathCountJ :=
      h4_eq ▸ Expr.eval_load ha_addr
    have hgp_w : g₀.getPathCountJ + 1 < 2 ^ w := by have := msf.hgp_succ; have := msf.hW_m_w; omega
    have ha_val := Expr.eval_add (w := w) hl (Expr.eval_const hw1) hgp_w
    exact runs_store_iff.mpr ⟨inp.v1 + 4, g₀.getPathCountJ + 1, ha_addr, ha_val,
      rfl, rfl, by simp [Expr.size]⟩
  set m53 := Function.update m52 (inp.v1 + 6) (g₀.vcongUpdates + updV)
  set sm53 : State := { sm52 with mem := m53 }
  have hm53_st : Runs w p ω (t2St (.reg 0) (.const 6) (t2Add (t2Ld (.reg 0) (.const 6)) (.reg 35))) sm52 .normal sm53 10 := by
    have h6_eq : sm52.mem (inp.v1 + 6) = g₀.vcongUpdates := by
      dsimp only [sm52, m52, sm51, m51, sm50, m50]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hv1_agr 6 (by omega) (by omega)).trans hS.h6
    have ha_addr := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 6 < 2 ^ w)) (by omega)
    have hl : (t2Ld (.reg 0) (.const 6)).eval w sm52 = some g₀.vcongUpdates :=
      h6_eq ▸ Expr.eval_load ha_addr
    have hup_lt : g₀.vcongUpdates + updV < 2 ^ w := by
      have hm := Nat.mul_le_mul_right (length inp.J inp.embJH + 1) hPsub_le_γ
      have := msf.hup_w; omega
    have ha_val := Expr.eval_add (w := w) hl (Expr.eval_reg_of_eq hr35) hup_lt
    exact runs_store_iff.mpr ⟨inp.v1 + 6, g₀.vcongUpdates + updV, ha_addr, ha_val,
      rfl, rfl, by simp [Expr.size]⟩
  set m54 := Function.update m53 (inp.v1 + 30) ((unembeddedSetPure ctx.wd g₀.emb).card - 1)
  set sm54 : State := { sm53 with mem := m54 }
  have hm54_st : Runs w p ω (t2St (.reg 0) (.const 30) (t2Sub (t2Ld (.reg 0) (.const 30)) (.const 1))) sm53 .normal sm54 10 := by
    have h30_eq : sm53.mem (inp.v1 + 30) = (unembeddedSetPure ctx.wd g₀.emb).card := by
      dsimp only [sm53, m53, sm52, m52, sm51, m51, sm50, m50]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hv1_agr 30 (by omega) (by omega)).trans hS.h30
    have ha_addr := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 30 < 2 ^ w)) (by omega)
    have hl : (t2Ld (.reg 0) (.const 30)).eval w sm53 = some (unembeddedSetPure ctx.wd g₀.emb).card :=
      h30_eq ▸ Expr.eval_load ha_addr
    have hcard_w : (unembeddedSetPure ctx.wd g₀.emb).card < 2 ^ w := by
      have := hS.hGetC; have := msf.hW_m_w; omega
    have ha_val := Expr.eval_sub (w := w) hl (Expr.eval_const hw1) hcard_w
    exact runs_store_iff.mpr ⟨inp.v1 + 30, (unembeddedSetPure ctx.wd g₀.emb).card - 1, ha_addr, ha_val,
      rfl, rfl, by simp [Expr.size]⟩
  set m55 := Function.update m54 (inp.v1 + 27) qlen
  set sm55 : State := { sm54 with mem := m55 }
  have hm55_st : Runs w p ω (t2St (.reg 0) (.const 27) (.reg 34)) sm54 .normal sm55 5 := by
    have ha_addr := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega : 27 < 2 ^ w)) (by omega)
    exact runs_store_iff.mpr ⟨inp.v1 + 27, qlen, ha_addr,
      Expr.eval_reg_of_eq hr34, rfl, rfl, by simp [Expr.size]⟩
  have hrun := runs_seq_iff.mpr (Or.inr ⟨sm50, 6, _, hm50_st,
    runs_seq_iff.mpr (Or.inr ⟨sm51, 9, _, hm51_st,
      runs_seq_iff.mpr (Or.inr ⟨sm52, 10, _, hm52_st,
        runs_seq_iff.mpr (Or.inr ⟨sm53, 10, _, hm53_st,
          runs_seq_iff.mpr (Or.inr ⟨sm54, 10, _, hm54_st,
            runs_seq_iff.mpr (Or.inr ⟨sm55, 5, c_cont, hm55_st, hcont, rfl⟩),
            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  simpa only [show 6 + (9 + (10 + (10 + (10 + (5 + c_cont + 1) + 1) + 1) + 1) + 1) + 1 = 56 + c_cont by omega] using hrun

lemma t2Middle_stage34_mem_facts {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart mem_gp memSt memOut : ℕ → ℕ}
    (db : DrainBounds ctx stc) (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    {ci eL eW updV wVal : ℕ} (hci : ci < ctx.wd.comps.length)
    (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m) (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    {P_sub : Walk}
    (res : Finset ℕ × List ℕ) (vcong0 : ℕ → ℕ)
    (hm_vlen : memSt g₀.arenaPtr = (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.length)
    (hm_verts : ∀ j < P_sub.verts.length, memSt (g₀.arenaPtr + 1 + j) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.getD j 0)
    (hm_elen : memSt (g₀.arenaPtr + 1 + P_sub.verts.length) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges.length)
    (hm_agr : ∀ a, ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
      memSt a = mem_gp a)
    (hro_mem_agr : ∀ a, ¬(g₀.arenaPtr + 2 + P_sub.verts.length ≤ a ∧
        a < g₀.arenaPtr + 2 + P_sub.verts.length + P_sub.edges.length) →
      ¬(inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
        a < inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n) →
      memOut a = Function.update memSt (inp.v1 + 26) (g₀.queryId + 1) a)
    (hro_edges : ∀ k < P_sub.edges.length,
      memOut (g₀.arenaPtr + 2 + P_sub.verts.length + k) =
        (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges.getD k 0)
    (hro_res1_sub : res.1 ⊆ Finset.range inp.H'.n) (hro_res2_sub : res.2.toFinset ⊆ res.1)
    (hro_res2_nd : res.2.Nodup)
    (hro_ew : ∀ x < inp.H'.n,
      memOut (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        if x ∈ res.1 then g₀.queryId + 1 else memStart (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hro_vc : ∀ x < inp.H'.n,
      memOut (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) = vcong0 x + if x ∈ res.1 then wVal else 0)
    (hro_ps : ∀ x < inp.H'.n,
      memOut (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        if x ∈ res.2 then g₀.η₁ else memStart (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hro_q : ∀ k (hk : k < res.2.length),
      memOut (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + k) = res.2[k]) :
    let P_J := liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub
    let vcA := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
    let psA := inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length
    let ewA := inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length
    let qA := inp.queueAddr ctx.wd.W.m ctx.wd.comps.length
    let m55 := t2MiddlePostMem memOut inp.embWJAddr eW inp.v1 g₀.arenaPtr P_J.encode.length
      g₀.getPathCountJ (g₀.vcongUpdates + updV) ((unembeddedSetPure ctx.wd g₀.emb).card - 1) res.2.length
    (∀ a, ¬(g₀.arenaPtr ≤ a ∧ a < g₀.arenaPtr + P_J.encode.length) →
      ¬(vcA ≤ a ∧ a < qA + inp.H'.n) →
      a ≠ inp.embWJAddr + eW → a ≠ inp.v1 + 25 → a ≠ inp.v1 + 26 →
      a ≠ inp.v1 + 4 → a ≠ inp.v1 + 6 → a ≠ inp.v1 + 30 → a ≠ inp.v1 + 27 →
      m55 a = mem_gp a) ∧
    WalkAt m55 g₀.arenaPtr P_J ∧
    m55 (inp.embWJAddr + eW) = g₀.arenaPtr ∧
    m55 (inp.v1 + 25) = g₀.arenaPtr + P_J.encode.length ∧
    m55 (inp.v1 + 26) = g₀.queryId + 1 ∧
    m55 (inp.v1 + 4) = g₀.getPathCountJ + 1 ∧
    m55 (inp.v1 + 6) = g₀.vcongUpdates + updV ∧
    m55 (inp.v1 + 30) = (unembeddedSetPure ctx.wd g₀.emb).card - 1 ∧
    m55 (inp.v1 + 27) = res.2.length ∧
    (∀ x < inp.H'.n, m55 (ewA + x) = if x ∈ res.1 then g₀.queryId + 1 else memStart (ewA + x)) ∧
    (∀ x < inp.H'.n, m55 (vcA + x) = vcong0 x + if x ∈ res.1 then wVal else 0) ∧
    (∀ x < inp.H'.n, m55 (psA + x) = if x ∈ res.2 then g₀.η₁ else memStart (psA + x)) ∧
    (∀ k (hk : k < res.2.length), m55 (qA + k) = res.2[k]) := by
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc
  have hm := mkW_W_edges_comp (pds := impl.pathDS.params) ctx.hws hci heL
  have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
  intro P_J vcA psA ewA qA m55
  have hP_verts_eq : P_J.verts.length = P_sub.verts.length := by simp [P_J, liftJSubWalk]
  have hP_J_enc : P_J.encode.length = 2 + P_sub.verts.length + P_sub.edges.length := by
    simp [P_J, liftJSubWalk, Walk.encode]; omega
  have hm55_out : ∀ a, g₀.arenaPtr ≤ a → a < g₀.arenaPtr + P_J.encode.length → m55 a = memOut a := by
    intro a ha1 ha2; dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm55_range : ∀ a, vcA ≤ a → a < qA + inp.H'.n → m55 a = memOut a := by
    intro a ha1 ha2; dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm_out_lt : ∀ a, g₀.arenaPtr ≤ a → a ≤ g₀.arenaPtr + 1 + P_sub.verts.length →
      memOut a = memSt a := by
    intro a ha1 ha2
    rw [hro_mem_agr a (by omega) (by omega), Function.update_of_ne (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hna hnv hneE hne25 hne26 hne4 hne6 hne30 hne27
    dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne hne27, Function.update_of_ne hne30, Function.update_of_ne hne6,
        Function.update_of_ne hne4, Function.update_of_ne hne25, Function.update_of_ne hneE,
        hro_mem_agr a (fun h => hna (by omega)) hnv, Function.update_of_ne hne26]
    exact hm_agr a (fun h => hna (by omega))
  · rw [walkAt_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm55_out g₀.arenaPtr (by omega) (by omega), hm_out_lt g₀.arenaPtr (by omega) (by omega), hm_vlen]
    · intro k hk
      have hk' : k < P_sub.verts.length := hP_verts_eq ▸ hk
      rw [hm55_out (g₀.arenaPtr + 1 + k) (by omega) (by omega),
          hm_out_lt (g₀.arenaPtr + 1 + k) (by omega) (by omega), ← List.getD_eq_getElem _ 0 hk]
      exact hm_verts k hk'
    · rw [hP_verts_eq, hm55_out (g₀.arenaPtr + 1 + P_sub.verts.length) (by omega) (by omega),
          hm_out_lt (g₀.arenaPtr + 1 + P_sub.verts.length) (by omega) (by omega)]
      exact hm_elen
    · intro k hk
      have hk' : k < P_sub.edges.length := by simpa only [P_J, liftJSubWalk, List.length_map] using hk
      rw [hP_verts_eq, hm55_out (g₀.arenaPtr + 2 + P_sub.verts.length + k) (by omega) (by omega),
          ← List.getD_eq_getElem _ 0 hk]
      exact hro_edges k hk'
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hro_mem_agr (inp.v1 + 26) (by omega) (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]
    rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · dsimp only [m55, t2MiddlePostMem]; exact Function.update_self _ _ _
  · intro x hx; rw [hm55_range (ewA + x) (by omega) (by omega)]; exact hro_ew x hx
  · intro x hx; rw [hm55_range (vcA + x) (by omega) (by omega)]; exact hro_vc x hx
  · intro x hx; rw [hm55_range (psA + x) (by omega) (by omega)]; exact hro_ps x hx
  · intro k hk
    have hk_n : k < inp.H'.n := by
      have hnd_len : res.2.length = res.2.toFinset.card := (List.toFinset_card_of_nodup hro_res2_nd).symm
      have hcard_le : res.2.toFinset.card ≤ (Finset.range inp.H'.n).card :=
        Finset.card_le_card (Finset.Subset.trans hro_res2_sub hro_res1_sub)
      simp only [Finset.card_range] at hcard_le; omega
    rw [hm55_range (qA + k) (by omega) (by omega)]; exact hro_q k hk

end MinCostFlow.Spanner
