module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleStage34Helpers

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM execution of Stages 3 and 4 of `t2MiddleEdgeBody` -/

/-- Lines 378–420 of `t2MiddleEdgeBody` after `t2MiddleStage2`. -/
def t2MiddleStage34 (drainBase : ℕ) : Stmt :=
  Stmt.assign 25 (t2Add (t2Ld (.reg 0) (.const 26)) (.const 1)) ;;
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
  Stmt.assign 35 (.const 0) ;;
  forRange 22 (.const 0) (.reg 21) (
    Stmt.assign 36 (t2Ld (.reg 20) (t2Add (.const 1) (.reg 22))) ;;
    Stmt.assign 37 (t2Ld (.reg 9) (.reg 36)) ;;
    t2St (.reg 24) (t2Add (.const 1) (.reg 22)) (.reg 37) ;;
    Stmt.assign 38 (t2Ld (.reg 27) (.reg 37)) ;;
    Stmt.assign 39 (.load (.reg 38)) ;;
    Stmt.assign 35 (t2Add (.reg 35) (.reg 39)) ;;
    forRange 40 (.const 0) (.reg 39) (
      Stmt.assign 41 (t2Ld (.reg 38) (t2Add (.const 1) (.reg 40))) ;;
      Stmt.cond (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)) (
        t2St (.reg 28) (.reg 41) (.reg 25) ;;
        Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26)) ;;
        t2St (.reg 29) (.reg 41) (.reg 42) ;;
        Stmt.cond (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)) (
          Stmt.cond (t2Le (.reg 31) (.reg 42)) (
            t2St (.reg 30) (.reg 41) (.reg 32) ;;
            t2St (.reg 33) (.reg 34) (.reg 41) ;;
            Stmt.assign 34 (t2Add (.reg 34) (.const 1))
          ) Stmt.nop
        ) Stmt.nop
      ) Stmt.nop
    )
  ) ;;
  t2St (.load (.reg 0)) (.reg 3) (.reg 18) ;;
  t2St (.reg 0) (.const 25) (t2Add (t2Add (.reg 24) (.const 1)) (.reg 21)) ;;
  t2St (.reg 0) (.const 4) (t2Add (t2Ld (.reg 0) (.const 4)) (.const 1)) ;;
  t2St (.reg 0) (.const 6) (t2Add (t2Ld (.reg 0) (.const 6)) (.reg 35)) ;;
  t2St (.reg 0) (.const 30) (t2Sub (t2Ld (.reg 0) (.const 30)) (.const 1)) ;;
  t2St (.reg 0) (.const 27) (.reg 34) ;;
  Stmt.call 4 drainBase [.reg 0, .reg 4] ;;
  Stmt.ret (.reg 4)

lemma t2Middle_stage34_run {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase drainBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_drain : p.procs[drainBase]? = some (t2DrainQueueBody dsBase))
    {g₀ : T2Ghost impl.pathDS} {memStart mem_gp : ℕ → ℕ}
    (hS : T2StepInv ctx stc g₀ memStart) (hV : T2VcongRoundInv ctx g₀)
    (hq_empty : g₀.queue = []) (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    {ci eL eW hCurNew : ℕ} {P_sub : Walk} {rep' : impl.pathDS.R.τ}
    (hci : ci < ctx.wd.comps.length) (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL) (hnone : g₀.emb eW = none)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hcw_sub : P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub msf.u_loc msf.v_loc)
    (hPsub_nd : P_sub.verts.Nodup)
    (hPsub_len : (P_sub.edges.length : ℝ) ≤
      impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
        ctx.wd.J0_strip.m)
    (hPsub_le_γ : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (hPsub_undel : ∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted)
    (hCur_le : g₀.hCur ≤ hCurNew)
    (hCur_sp : hCurNew ≤ g₀.hCur +
      impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m ctx.wd.J0_strip.m)
    (hCur_hi : hCurNew ≤ Task2Input.maxHeapEnd impl inp)
    (hDS_gp : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) hCurNew mem_gp
      ctx.wd.comps.length g₀.states (Function.update g₀.reps ci rep'))
    (hgp_below : ∀ a < stc.dsBaseAddr, mem_gp a = memStart a)
    (hwk_sub : WalkAt mem_gp g₀.hCur P_sub)
    (st : State)
    (hregs : ∀ r ≤ 21, st.regs r =
      if r = 18 then g₀.arenaPtr else if r = 19 then P_sub.verts.length
      else if r = 20 then g₀.hCur + 1 + P_sub.verts.length
      else if r = 21 then P_sub.edges.length
      else if r = 0 then inp.v1 else if r = 3 then eW else if r = 4 then hCurNew
      else if r = 9 then msf.cJOrigPtr else if r = 10 then ctx.wInp.h else st.regs r)
    (hr24 : st.regs 24 = g₀.arenaPtr + 1 + P_sub.verts.length)
    (hm_vlen : st.mem g₀.arenaPtr = (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.length)
    (hm_verts : ∀ j < P_sub.verts.length, st.mem (g₀.arenaPtr + 1 + j) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.getD j 0)
    (hm_elen : st.mem (g₀.arenaPtr + 1 + P_sub.verts.length) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges.length)
    (hm_agr : ∀ a, ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
      st.mem a = mem_gp a)
    (ω : ℕ → Bool) :
    let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    ∃ g' st' c_run,
      Runs w p ω (t2MiddleStage34 drainBase) st (.returned g'.hCur) st' c_run ∧
      hCurNew ≤ g'.hCur ∧ g'.η₁ = g₀.η₁ ∧
      g'.emb = Function.update g₀.emb eW (some (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub)) ∧
      g'.emb_prev = g₀.emb_prev ∧ g'.drained = g'.procVerts ∧ g'.queue = [] ∧
      g'.initCountJ = g₀.initCountJ ∧ g'.initEdgesJ = g₀.initEdgesJ ∧
      g'.getPathCountJ = g₀.getPathCountJ + 1 ∧ g'.prevDelCountJ = g₀.prevDelCountJ ∧
      g₀.arenaPtr ≤ g'.arenaPtr ∧ stc.nodesEnd ≤ g'.arenaPtr ∧
      g'.queryId = g₀.queryId + 1 ∧
      (∀ k, (g₀.states k).deleted ⊆ (g'.states k).deleted) ∧
      (∀ k, (g₀.states k).Vhat ⊆ (g'.states k).Vhat) ∧
      T2StepInv ctx stc g' st'.mem ∧
      T2VcongRoundInv ctx g' ∧
      c_run + t2StepPhi ctx stc g' st'.mem ≤
        P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 55) +
          25 * (γJ * (length inp.J inp.embJH + 1)) + 250 +
          t2RoundPhi impl.pathDS (t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec
              ctx.wInp.prep.phiDen_dec ctx.wd.J0_strip.m)
            t2KVhatStep t2KNodeStep (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
            (t2UndelRem ctx g₀) (t2VhatRem ctx g₀) (t2NodeRem ctx stc g₀)
            (Function.update g₀.reps ci rep') mem_gp := by
  intro γJ
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  have hmwb := db.h_mwb
  have hr0 : st.regs 0 = inp.v1 := by simpa using hregs 0 (by omega)
  have hr3 : st.regs 3 = eW := by simpa using hregs 3 (by omega)
  have hr4 : st.regs 4 = hCurNew := by simpa using hregs 4 (by omega)
  have hr9 : st.regs 9 = msf.cJOrigPtr := by simpa using hregs 9 (by omega)
  have hr10 : st.regs 10 = ctx.wInp.h := by simpa using hregs 10 (by omega)
  have hr18 : st.regs 18 = g₀.arenaPtr := by simpa using hregs 18 (by omega)
  have hr20 : st.regs 20 = g₀.hCur + 1 + P_sub.verts.length := by simpa using hregs 20 (by omega)
  have hr21 : st.regs 21 = P_sub.edges.length := by simpa using hregs 21 (by omega)
  have hm := mkW_W_edges_comp (pds := impl.pathDS.params) ctx.hws hci heL
  have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
  have hm_start : ∀ a < stc.dsBaseAddr, ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
      st.mem a = memStart a := fun a ha hno => (hm_agr a hno).trans (hgp_below a ha)
  have hqid_w : g₀.queryId + 1 < 2 ^ w := by have := hS.hQid; have := msf.hgp_succ; have := msf.hW_m_w; omega
  have hwWNum_w : msf.wWNumAddr + eW < 2 ^ w := by have := msf.hwWNum_lt; omega
  have hw14_w : ctx.wInp.h + 14 < 2 ^ w := by
    have ⟨_, _, _, _, _, _, _, hstOut⟩ := ctx.agrees_preserves_static hS.agr_pre
    have ⟨_, _, _, _, _, _, _, _, _, _, _, ha1, _⟩ := hstOut
    have : ctx.wInp.h + 20 ≤ msf.aCompExt := by rwa [← msf.haCompExt_ptr]
    have := msf.haCompExt_lt; have := msf.hwWNum_lt; omega
  have hv1_w : inp.v1 + 32 < 2 ^ w := by omega
  have har_next := msf.har_next
  have hPsub_verts_le : P_sub.verts.length ≤ P_sub.edges.length + 1 := t2_isWalk_verts_length_le hcw_sub
  have har_end_ds : g₀.arenaPtr + 2 + P_sub.verts.length + P_sub.edges.length ≤ stc.dsBaseAddr := by omega
  have har_v1_w : g₀.arenaPtr + 1 + P_sub.verts.length + 1 < 2 ^ w := by omega
  have har_enc_w : g₀.arenaPtr + 1 + P_sub.verts.length + 1 + P_sub.edges.length < 2 ^ w := by omega
  let s35 := t2MiddlePreState st inp.v1 (g₀.queryId + 1) (memStart (msf.wWNumAddr + eW)) inp.embJHAddr
    (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (memStart (inp.v1 + 28)) g₀.η₁
    (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
  have hwk_mq : WalkAt s35.mem g₀.hCur P_sub := by
    have hagr_gp : ∀ a ≥ stc.dsBaseAddr, s35.mem a = mem_gp a := fun a ha => by
      dsimp only [s35, t2MiddlePreState]; rw [Function.update_of_ne (by omega)]; exact hm_agr a (by omega)
    rw [walkAt_iff]
    have hds_hc : stc.dsBaseAddr ≤ g₀.hCur := hS.hDS.h_ge
    exact ⟨(hagr_gp g₀.hCur (by omega)).trans hwk_sub.verts_len,
      fun k hk => (hagr_gp (g₀.hCur + 1 + k) (by omega)).trans (hwk_sub.verts_listAt k hk),
      (hagr_gp (g₀.hCur + 1 + P_sub.verts.length) (by omega)).trans hwk_sub.edges_len,
      fun k hk => (hagr_gp (g₀.hCur + 2 + P_sub.verts.length + k) (by omega)).trans (hwk_sub.edges_listAt k hk)⟩
  have hz_mq : WordRAM.ZeroFrom s35.mem hCurNew := fun a ha => by
    have hds_hc : stc.dsBaseAddr ≤ g₀.hCur := hS.hDS.h_ge
    dsimp only [s35, t2MiddlePreState]; rw [Function.update_of_ne (by omega), hm_agr a (by omega)]
    exact hDS_gp.zero_from a ha
  have hm_s35_agr : ∀ a < stc.dsBaseAddr, a ≠ inp.v1 + 26 →
      ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
      s35.mem a = memStart a := fun a ha hne hno => by
    dsimp only [s35, t2MiddlePreState]; rw [Function.update_of_ne hne]; exact hm_start a ha hno
  have hr_s35_21 : ∀ r ≤ 21, s35.regs r = st.regs r := fun r hr => by
    dsimp only [s35, t2MiddlePreState]
    simp [Function.update_of_ne (by omega : r ≠ 35), Function.update_of_ne (by omega : r ≠ 34),
      Function.update_of_ne (by omega : r ≠ 33), Function.update_of_ne (by omega : r ≠ 32),
      Function.update_of_ne (by omega : r ≠ 31), Function.update_of_ne (by omega : r ≠ 30),
      Function.update_of_ne (by omega : r ≠ 29), Function.update_of_ne (by omega : r ≠ 28),
      Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 26),
      Function.update_of_ne (by omega : r ≠ 25)]
  obtain ⟨st_out, c_out, hr_out, hro_regs, hro_24, hro_34, hro_35, hro_mem_agr, hro_edges,
      hro_res1, hro_res1_sub, hro_res2_sub, hro_res2_nd, hro_res2, hro_ew, hro_vc, hro_ps, hro_q,
      hro_updV_bd, hc_out⟩ :=
    t2Middle_outerEdges_forRange ctx stc hS hci heL heW_eq msf hcw_sub hPsub_nd hPsub_le_γ
      s35.mem hwk_mq hz_mq hCur_le hCur_hi hS.hDS.h_ge har_lo har_end_ds hm_s35_agr
      s35.regs
      (by rw [hr_s35_21 9 (by omega)]; exact hr9)
      (by rw [hr_s35_21 20 (by omega)]; exact hr20)
      (by rw [hr_s35_21 21 (by omega)]; exact hr21)
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne, hr24])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; simp [Function.update_of_ne])
      (by dsimp only [s35, t2MiddlePreState]; exact Function.update_self _ _ _)
      s35.pos ω
  let c := ctx.wd.comps[ci]'hci
  let P_J := liftJSubWalk c P_sub
  let vcA := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
  let res := t2MiddleOuterFold inp.embJH g₀.procVerts (fun x => memStart (vcA + x))
    (memStart (inp.v1 + 28)) (memStart (msf.wWNumAddr + eW))
    c.jSubOrigEdges P_sub.edges P_sub.edges.length
  let updV := t2MiddleUpdVerts inp.embJH c.jSubOrigEdges P_sub.edges P_sub.edges.length
  have hr_o0 : st_out.regs 0 = inp.v1 := (hro_regs 0 (by omega)).trans ((hr_s35_21 0 (by omega)).trans hr0)
  have hr_o3 : st_out.regs 3 = eW := (hro_regs 3 (by omega)).trans ((hr_s35_21 3 (by omega)).trans hr3)
  have hr_o4 : st_out.regs 4 = hCurNew := (hro_regs 4 (by omega)).trans ((hr_s35_21 4 (by omega)).trans hr4)
  have hr_o18 : st_out.regs 18 = g₀.arenaPtr := (hro_regs 18 (by omega)).trans ((hr_s35_21 18 (by omega)).trans hr18)
  have hr_o21 : st_out.regs 21 = P_sub.edges.length := (hro_regs 21 (by omega)).trans ((hr_s35_21 21 (by omega)).trans hr21)
  have hst_out_v1_agr : ∀ k < 32, k ≠ 26 → st_out.mem (inp.v1 + k) = memStart (inp.v1 + k) := fun k hk hk26 => by
    rw [hro_mem_agr (inp.v1 + k) (by omega) (by omega)]
    dsimp only [s35, t2MiddlePreState]
    rw [Function.update_of_ne (by omega)]
    exact hm_start (inp.v1 + k) (by omega) (by omega)
  obtain ⟨hm55_below, hwk_m55, hm55_eb, hm55_25, hm55_26, hm55_4, hm55_6, hm55_30, hm55_27,
      hm55_ew, hm55_vc, hm55_ps, hm55_q⟩ :=
    t2Middle_stage34_mem_facts ctx stc db har_lo hci heL heW_eq res (fun x => memStart (vcA + x))
      hm_vlen hm_verts hm_elen hm_agr hro_mem_agr hro_edges hro_res1_sub hro_res2_sub hro_res2_nd
      hro_ew hro_vc hro_ps hro_q
  let m55 := t2MiddlePostMem st_out.mem inp.embWJAddr eW inp.v1 g₀.arenaPtr P_J.encode.length
    g₀.getPathCountJ (g₀.vcongUpdates + updV) ((unembeddedSetPure ctx.wd g₀.emb).card - 1) res.2.length
  let sm55 : State := { st_out with mem := m55 }
  let g₁ : T2Ghost impl.pathDS :=
    { η₁ := g₀.η₁, emb := Function.update g₀.emb eW (some P_J), emb_prev := g₀.emb_prev
      states := g₀.states, reps := Function.update g₀.reps ci rep', drained := g₀.drained
      procVerts := g₀.procVerts ∪ res.2.toFinset, queue := res.2
      initCountJ := g₀.initCountJ, initEdgesJ := g₀.initEdgesJ
      getPathCountJ := g₀.getPathCountJ + 1, deleteCountJ := g₀.deleteCountJ
      prevDelCountJ := g₀.prevDelCountJ, vcongUpdates := g₀.vcongUpdates + updV
      innerIters1 := g₀.innerIters1, arenaPtr := g₀.arenaPtr + P_J.encode.length
      queryId := g₀.queryId + 1, hCur := hCurNew }
  obtain ⟨hS1, hV1, har1, hq_len, hdsPhi, hUndel, hVhat, hNode⟩ :=
    t2Middle_stepInv_mid ctx stc hSpec hS hV hq_empty har_lo hci heL heW_eq hnone msf
      hcw_sub ⟨rfl, rfl⟩ hPsub_len hPsub_undel hCur_sp hDS_gp hgp_below hm55_below res updV
      hro_res1 hro_res1_sub hro_res2_sub hro_res2_nd hro_res2 hwk_m55
      hm55_eb hm55_25 hm55_26 hm55_4 hm55_6 hm55_30 hm55_27
      hro_updV_bd hm55_ew hm55_vc hm55_ps hm55_q
  have hDrain := t2DrainQueue_ptriple ctx stc hSpec g₁
  obtain ⟨o_dr, st_dr, c_dr, Φ_dr, hr_dr, hq_dr, hc_dr⟩ :=
    hDrain (WordRAM.startState [inp.v1, hCurNew] sm55.mem sm55.pos)
      (t2StepPhi ctx stc g₁ sm55.mem) ω ⟨rfl, rfl, hS1, rfl⟩
  rcases o_dr with _ | ⟨v_dr⟩
  · exact False.elim hq_dr
  obtain ⟨g', rfl, hg'_hc, hg'_η, hg'_emb, hg'_ep, hg'_dr, hg'_pv, hg'_q, hg'_ic, hg'_ie,
      hg'_gp, hg'_pd, _hg'_vu, _hg'_ii, hg'_ar, hg'_qid, hg'_del, hg'_vh, hSg', hΦ_dr⟩ := hq_dr
  let st_final : State := { mem := st_dr.mem, regs := Function.update sm55.regs 4 g'.hCur, pos := st_dr.pos }
  have hm55_call : Runs w p ω (Stmt.call 4 drainBase [.reg 0, .reg 4]) sm55 .normal
      st_final (argsSize [.reg 0, .reg 4] + c_dr + 1) := by
    refine runs_call_iff.mpr ⟨[inp.v1, hCurNew], t2DrainQueueBody dsBase, .returned g'.hCur, st_dr, c_dr,
      ?_, hp_drain, hr_dr, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval_reg_of_eq (show sm55.regs 0 = inp.v1 from hr_o0),
      Expr.eval_reg_of_eq (show sm55.regs 4 = hCurNew from hr_o4)]
  have hret_st : Runs w p ω (Stmt.ret (.reg 4)) st_final (.returned g'.hCur) st_final 2 :=
    runs_ret_iff.mpr ⟨g'.hCur, Expr.eval_reg_of_eq (by dsimp only [st_final]; exact Function.update_self _ _ _),
      rfl, rfl, by simp [Expr.size]⟩
  have hcall_ret : Runs w p ω (Stmt.call 4 drainBase [.reg 0, .reg 4] ;; Stmt.ret (.reg 4))
      sm55 (.returned g'.hCur) st_final ((argsSize [.reg 0, .reg 4] + c_dr + 1) + 2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st_final, argsSize [.reg 0, .reg 4] + c_dr + 1, 2, hm55_call, hret_st, rfl⟩)
  have hr_post := t2Middle_stage34_post_run ctx stc hS hci heL heW_eq msf hPsub_le_γ har_lo
    hro_updV_bd har_v1_w har_enc_w st_out ω hr_o0 hr_o3 hr_o18 hr_o21 hro_24 hro_34 hro_35 hst_out_v1_agr
    (Stmt.call 4 drainBase [.reg 0, .reg 4] ;; Stmt.ret (.reg 4)) hcall_ret
  have hr_out_post : Runs w p ω _ s35 (.returned g'.hCur) st_final
      (c_out + (56 + ((argsSize [.reg 0, .reg 4] + c_dr + 1) + 2 + 1)) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st_out, c_out, _, hr_out, hr_post, rfl⟩)
  have hrun_full : Runs w p ω (t2MiddleStage34 drainBase) st (.returned g'.hCur) st_final
      (71 + (c_out + (56 + ((argsSize [.reg 0, .reg 4] + c_dr + 1) + 2 + 1)) + 1)) := by
    dsimp only [t2MiddleStage34]
    exact t2Middle_stage34_pre_run ctx stc hS hci heL heW_eq msf hqid_w hwWNum_w
      hw14_w hv1_w har_lo P_sub.verts.length st ω hr0 hr3 hr10 hm_start _ hr_out_post
  have hVg' : T2VcongRoundInv ctx g' := t2VcongRoundInv_drain ctx hV1 hg'_η hg'_emb hg'_pv
  have hPsub_le_γJ : P_sub.edges.length ≤ γJ := by
    have h1 : (P_sub.edges.length : ℝ) ≤ (⌈impl.pathDS.params.γ_ExpPath
        ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m⌉₊ : ℝ) :=
      le_trans hPsub_len (Nat.le_ceil _)
    have h2 : (P_sub.edges.length : ℝ) ≤ (γJ : ℝ) :=
      le_trans h1 (by exact_mod_cast ctx.ds_bounds.2.2.2.2.2.2.2.2.1)
    exact_mod_cast h2
  have hqlen_le : g₁.queue.length ≤ γJ * (length inp.J inp.embJH + 1) :=
    le_trans hq_len (Nat.mul_le_mul_right _ hPsub_le_γJ)
  have hΦ1_eq : t2StepPhi ctx stc g₁ sm55.mem =
      t2RoundPhi impl.pathDS (t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec
          ctx.wInp.prep.phiDen_dec ctx.wd.J0_strip.m)
        t2KVhatStep t2KNodeStep (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
        (t2UndelRem ctx g₀) (t2VhatRem ctx g₀) (t2NodeRem ctx stc g₀)
        (Function.update g₀.reps ci rep') mem_gp := by
    dsimp only [t2StepPhi, t2RoundPhi]; rw [hdsPhi, hUndel, hVhat, hNode]
  have hargs_eq : argsSize [.reg 0, .reg 4] = 2 := by simp [argsSize, Expr.size]
  refine ⟨g', st_final, _, hrun_full, hg'_hc, hg'_η, hg'_emb, hg'_ep, hg'_dr.trans hg'_pv.symm, hg'_q,
    hg'_ic, hg'_ie, hg'_gp, hg'_pd, le_trans (Nat.le_add_right _ _) hg'_ar.symm.le,
    le_trans har1 hg'_ar.symm.le, hg'_qid, hg'_del, hg'_vh, hSg', hVg', ?_⟩
  rw [hΦ_dr] at hc_dr
  rw [hargs_eq, ← hΦ1_eq]
  have h1 : 25 * g₁.queue.length ≤ 25 * (γJ * (length inp.J inp.embJH + 1)) := Nat.mul_le_mul_left 25 hqlen_le
  have h2 : c_out ≤ P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 55) + 7 := hc_out
  linarith only [hc_dr, h1, h2]

end MinCostFlow.Spanner
