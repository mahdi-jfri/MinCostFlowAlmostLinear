module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleStage34

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM `PTriple` for `t2MiddleEdgeBody` (Task 2 middle-loop step) -/

/-- End-to-end Word-RAM `PTriple` for `t2MiddleEdgeBody` (Task 2 middle-loop step). -/
lemma t2MiddleEdge_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase drainBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_drain : p.procs[drainBase]? = some (t2DrainQueueBody dsBase))
    (g₀ : T2Ghost impl.pathDS) (hV : T2VcongRoundInv ctx g₀)
    (hq_empty : g₀.queue = []) (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    {ci eL eW : ℕ} (hci : ci < ctx.wd.comps.length) (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL) (hnone : g₀.emb eW = none)
    (hu_vh : ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1 ∉ (g₀.states ci).Vhat)
    (hv_vh : ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 ∉ (g₀.states ci).Vhat) :
    let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    PTriple w p
      (fun st Φ => st.regs 0 = inp.v1 ∧ st.regs 1 = ci ∧ st.regs 2 = eL ∧
        st.regs 3 = eW ∧ st.regs 4 = g₀.hCur ∧
        T2StepInv ctx stc g₀ st.mem ∧ Φ = t2StepPhi ctx stc g₀ st.mem)
      (t2MiddleEdgeBody dsBase drainBase)
      (fun o st' Φ' => match o with
        | .normal => False
        | .returned v => ∃ g', v = g'.hCur ∧ g₀.hCur ≤ g'.hCur ∧
            g'.η₁ = g₀.η₁ ∧
            (∃ P_sub : Walk, P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub
                ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1
                ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 ∧
              P_sub.verts.Nodup ∧
              (P_sub.edges.length : ℝ) ≤ impl.pathDS.params.γ_ExpPath
                ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m ∧
              (∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted) ∧
              g'.emb = Function.update g₀.emb eW (some (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub))) ∧
            g'.emb_prev = g₀.emb_prev ∧ g'.drained = g'.procVerts ∧ g'.queue = [] ∧
            g'.initCountJ = g₀.initCountJ ∧ g'.initEdgesJ = g₀.initEdgesJ ∧
            g'.getPathCountJ = g₀.getPathCountJ + 1 ∧ g'.prevDelCountJ = g₀.prevDelCountJ ∧
            g₀.arenaPtr ≤ g'.arenaPtr ∧ stc.nodesEnd ≤ g'.arenaPtr ∧
            g'.queryId = g₀.queryId + 1 ∧
            (∀ k, (g₀.states k).deleted ⊆ (g'.states k).deleted) ∧
            (∀ k, (g₀.states k).Vhat ⊆ (g'.states k).Vhat) ∧
            T2StepInv ctx stc g' st'.mem ∧ T2VcongRoundInv ctx g' ∧
            Φ' = t2StepPhi ctx stc g' st'.mem)
      (fun _ => 200 * γJ * (length inp.J inp.embJH + 1) +
        ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ + 500) := by
  intro γJ st Φ ω ⟨hr0, hr1, hr2, hr3, hr4, hS, hΦ⟩
  have msf : MiddleStaticFacts ctx stc g₀ ci eL eW st.mem :=
    middle_static_facts ctx stc hS hci heL heW_eq hnone
  have hu_def : msf.u_loc = ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1 := by
    have h := congrArg Prod.fst msf.huv_eq; rwa [List.getD_eq_getElem _ _ hci] at h
  have hv_def : msf.v_loc = ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 := by
    have h := congrArg Prod.snd msf.huv_eq; rwa [List.getD_eq_getElem _ _ hci] at h
  have hu_vh' : msf.u_loc ∉ (g₀.states ci).Vhat := by simpa only [hu_def] using hu_vh
  have hv_vh' : msf.v_loc ∉ (g₀.states ci).Vhat := by simpa only [hv_def] using hv_vh
  have hbody : t2MiddleEdgeBody dsBase drainBase =
      t2MiddleStage1 dsBase (t2MiddleStage2 (t2MiddleStage34 drainBase)) := rfl
  rw [hbody]
  let Q1 : Outcome → State → ℕ → ℕ → Prop := fun o st' c_gp c_cont =>
    ∃ g' : T2Ghost impl.pathDS,
      o = .returned g'.hCur ∧ g₀.hCur ≤ g'.hCur ∧ g'.η₁ = g₀.η₁ ∧
      (∃ P_sub : Walk, P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub
          ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1
          ((ctx.wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 ∧
        P_sub.verts.Nodup ∧
        (P_sub.edges.length : ℝ) ≤ impl.pathDS.params.γ_ExpPath
          ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m ∧
        (∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted) ∧
        g'.emb = Function.update g₀.emb eW (some (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub))) ∧
      g'.emb_prev = g₀.emb_prev ∧ g'.drained = g'.procVerts ∧ g'.queue = [] ∧
      g'.initCountJ = g₀.initCountJ ∧ g'.initEdgesJ = g₀.initEdgesJ ∧
      g'.getPathCountJ = g₀.getPathCountJ + 1 ∧ g'.prevDelCountJ = g₀.prevDelCountJ ∧
      g₀.arenaPtr ≤ g'.arenaPtr ∧ stc.nodesEnd ≤ g'.arenaPtr ∧
      g'.queryId = g₀.queryId + 1 ∧
      (∀ k, (g₀.states k).deleted ⊆ (g'.states k).deleted) ∧
      (∀ k, (g₀.states k).Vhat ⊆ (g'.states k).Vhat) ∧
      T2StepInv ctx stc g' st'.mem ∧ T2VcongRoundInv ctx g' ∧
      c_gp + c_cont + t2StepPhi ctx stc g' st'.mem ≤
        200 * γJ * (length inp.J inp.embJH + 1) +
          ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ + 380 + Φ
  obtain ⟨o, stF, c_gp, c_cont, c_tot, hr_tot, hQ1, hc_tot⟩ :=
    t2Middle_stage1_cps ctx stc hSpec hS hci heL msf hu_vh' hv_vh'
      st hr0 hr1 hr2 hr3 hr4 rfl (t2MiddleStage2 (t2MiddleStage34 drainBase)) ω Q1
      (fun o_gp st_gp c_gp rep' P_sub hgp_ge hgp_le hgp_hi hgp_below hwk_sub hcw_sub
          hPsub_nd hPsub_undel _hPsub_vh hPsub_len hPsub_le_γ hDS_gp hgp_phi
          st_post hm_post hrp0 hrp1 _hrp2 hrp3 hrp4 hrp8 hrp9 hrp10 hrp17 => by
        let Q2 : Outcome → State → ℕ → ℕ → Prop := fun o stF c_wv c_s34 =>
          ∃ g' : T2Ghost impl.pathDS,
            o = .returned g'.hCur ∧ g₀.hCur ≤ g'.hCur ∧ g'.η₁ = g₀.η₁ ∧
            (g'.emb = Function.update g₀.emb eW (some (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub))) ∧
            g'.emb_prev = g₀.emb_prev ∧ g'.drained = g'.procVerts ∧ g'.queue = [] ∧
            g'.initCountJ = g₀.initCountJ ∧ g'.initEdgesJ = g₀.initEdgesJ ∧
            g'.getPathCountJ = g₀.getPathCountJ + 1 ∧ g'.prevDelCountJ = g₀.prevDelCountJ ∧
            g₀.arenaPtr ≤ g'.arenaPtr ∧ stc.nodesEnd ≤ g'.arenaPtr ∧
            g'.queryId = g₀.queryId + 1 ∧
            (∀ k, (g₀.states k).deleted ⊆ (g'.states k).deleted) ∧
            (∀ k, (g₀.states k).Vhat ⊆ (g'.states k).Vhat) ∧
            T2StepInv ctx stc g' stF.mem ∧ T2VcongRoundInv ctx g' ∧
            c_wv + c_s34 + t2StepPhi ctx stc g' stF.mem ≤
              P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 82) +
                25 * (γJ * (length inp.J inp.embJH + 1)) + 300 +
                t2RoundPhi impl.pathDS (t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec
                    ctx.wInp.prep.phiDen_dec ctx.wd.J0_strip.m)
                  t2KVhatStep t2KNodeStep (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
                  (t2UndelRem ctx g₀) (t2VhatRem ctx g₀) (t2NodeRem ctx stc g₀)
                  (Function.update g₀.reps ci rep') st_gp.mem
        obtain ⟨o, stF, c_wv, c_s34, c_234, hr_234, hQ2, hc_234⟩ :=
          t2Middle_stage2_cps ctx stc hS har_lo hci msf hcw_sub hPsub_nd hPsub_le_γ
            hwk_sub hDS_gp.zero_from hgp_ge hgp_hi hgp_below
            st_post hm_post hrp0 hrp1 hrp4 hrp8 hrp17 (t2MiddleStage34 drainBase) ω Q2
            (fun st_2 c_wv hc_wv hr2_regs hr2_24 hm_vlen hm_verts hm_elen hm_agr => by
              have hregs_s34 : ∀ r ≤ 21, st_2.regs r =
                  if r = 18 then g₀.arenaPtr else if r = 19 then P_sub.verts.length
                  else if r = 20 then g₀.hCur + 1 + P_sub.verts.length
                  else if r = 21 then P_sub.edges.length
                  else if r = 0 then inp.v1 else if r = 3 then eW else if r = 4 then o_gp.value
                  else if r = 9 then msf.cJOrigPtr else if r = 10 then ctx.wInp.h else st_2.regs r := by
                intro r hr; rw [hr2_regs r hr]
                split_ifs with h18 h19 h20 h21 h0 h3 h4 h9 h10
                · rfl
                · rfl
                · rfl
                · rfl
                · exact h0 ▸ hrp0
                · exact h3 ▸ hrp3
                · exact h4 ▸ hrp4
                · exact h9 ▸ hrp9
                · exact h10 ▸ hrp10
                · rfl
              obtain ⟨g', stF, c_s34, hr_s34, hg'_hc, hg'_η, hg'_emb, hg'_ep, hg'_dr, hg'_q,
                  hg'_ic, hg'_ie, hg'_gp, hg'_pd, hg'_ar, hstc_ar, hg'_qid, hg'_del, hg'_vh,
                  hSg', hVg', hc_s34⟩ :=
                t2Middle_stage34_run ctx stc hSpec hp_drain hS hV hq_empty har_lo hci heL heW_eq hnone
                  msf hcw_sub hPsub_nd hPsub_len hPsub_le_γ hPsub_undel hgp_ge hgp_le hgp_hi
                  hDS_gp hgp_below hwk_sub st_2 hregs_s34 hr2_24
                  hm_vlen hm_verts hm_elen hm_agr ω
              have hP_v_le : P_sub.verts.length ≤ P_sub.edges.length + 1 := t2_isWalk_verts_length_le hcw_sub
              have hc_wv' : c_wv ≤ P_sub.edges.length * 27 + 34 := by omega
              have hγJ_eq : impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m = γJ := rfl
              have h_edge_add :
                  P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 55) + 27 * P_sub.edges.length =
                    P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 82) := by ring
              rw [hγJ_eq] at hc_s34
              refine ⟨.returned g'.hCur, stF, c_s34, hr_s34, g', rfl, le_trans hgp_ge hg'_hc,
                hg'_η, hg'_emb, hg'_ep, hg'_dr, hg'_q, hg'_ic, hg'_ie, hg'_gp, hg'_pd,
                hg'_ar, hstc_ar, hg'_qid, hg'_del, hg'_vh, hSg', hVg', ?_⟩
              omega)
        rcases hQ2 with ⟨g', rfl, hg'_hc, hg'_η, hg'_emb, hg'_ep, hg'_dr, hg'_q,
          hg'_ic, hg'_ie, hg'_gp, hg'_pd, hg'_ar, hstc_ar, hg'_qid, hg'_del, hg'_vh,
          hSg', hVg', hc_q2⟩
        have hPsub_le_γJ : P_sub.edges.length ≤ γJ := by
          have h1 : (P_sub.edges.length : ℝ) ≤ (⌈impl.pathDS.params.γ_ExpPath
              ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m⌉₊ : ℝ) :=
            le_trans hPsub_len (Nat.le_ceil _)
          have h2 : (P_sub.edges.length : ℝ) ≤ (γJ : ℝ) :=
            le_trans h1 (by exact_mod_cast ctx.ds_bounds.2.2.2.2.2.2.2.2.1)
          exact_mod_cast h2
        have hmul1 : P_sub.edges.length * ((length inp.J inp.embJH + 1) * 75 + 82) ≤
            γJ * ((length inp.J inp.embJH + 1) * 157) := by
          have h82 : (length inp.J inp.embJH + 1) * 75 + 82 ≤ (length inp.J inp.embJH + 1) * 157 := by omega
          exact le_trans (Nat.mul_le_mul_left _ h82) (Nat.mul_le_mul_right _ hPsub_le_γJ)
        have h182 : γJ * ((length inp.J inp.embJH + 1) * 157) +
            25 * (γJ * (length inp.J inp.embJH + 1)) ≤
            200 * γJ * (length inp.J inp.embJH + 1) := by
          have hlin : γJ * ((length inp.J inp.embJH + 1) * 157) +
              25 * (γJ * (length inp.J inp.embJH + 1)) =
              γJ * ((length inp.J inp.embJH + 1) * 182) := by ring
          have h200 : 200 * γJ * (length inp.J inp.embJH + 1) =
              γJ * ((length inp.J inp.embJH + 1) * 200) := by ring
          rw [hlin, h200]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        have hKq_le : ⌈impl.pathDS.params.K_query * impl.pathDS.params.γ_query
            ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m⌉₊ ≤
            ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ := ctx.ds_bounds.2.2.1
        have hstep_gp : c_gp + t2RoundPhi impl.pathDS (t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec
              ctx.wInp.prep.phiDen_dec ctx.wd.J0_strip.m)
            t2KVhatStep t2KNodeStep (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
            (t2UndelRem ctx g₀) (t2VhatRem ctx g₀) (t2NodeRem ctx stc g₀)
            (Function.update g₀.reps ci rep') st_gp.mem ≤
            ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ + Φ := by
          rw [hΦ]
          dsimp only [t2StepPhi, t2RoundPhi] at hgp_phi ⊢
          omega
        refine ⟨.returned g'.hCur, stF, c_234, hr_234, g', rfl, hg'_hc, hg'_η,
          ⟨P_sub, by simpa only [← hu_def, ← hv_def] using hcw_sub,
            hPsub_nd, hPsub_len, hPsub_undel, hg'_emb⟩,
          hg'_ep, hg'_dr, hg'_q, hg'_ic, hg'_ie, hg'_gp, hg'_pd, hg'_ar, hstc_ar,
          hg'_qid, hg'_del, hg'_vh, hSg', hVg', ?_⟩
        omega)
  rcases hQ1 with ⟨g', rfl, hg'_hc, hg'_η, hPsub_ex, hg'_ep, hg'_dr, hg'_q,
    hg'_ic, hg'_ie, hg'_gp, hg'_pd, hg'_ar, hstc_ar, hg'_qid, hg'_del, hg'_vh,
    hSg', hVg', hc_q1⟩
  refine ⟨.returned g'.hCur, stF, c_tot, t2StepPhi ctx stc g' stF.mem, hr_tot,
    ⟨g', rfl, hg'_hc, hg'_η, hPsub_ex, hg'_ep, hg'_dr, hg'_q, hg'_ic, hg'_ie, hg'_gp, hg'_pd,
      hg'_ar, hstc_ar, hg'_qid, hg'_del, hg'_vh, hSg', hVg', rfl⟩,
    ?_⟩
  dsimp only; omega

end MinCostFlow.Spanner
