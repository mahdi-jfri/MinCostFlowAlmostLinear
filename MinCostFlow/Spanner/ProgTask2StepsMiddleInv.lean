module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleOuter

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Mid-step invariant & `t2StepPhi` transition for `t2MiddleEdgeBody` (before `t2DrainQueue`) -/

private lemma t2Mid_composeAux_congr {J₁ J₂ : Graph} {emb₁ emb₂ : ℕ → Walk}
    (hJe : J₁.edges = J₂.edges) :
    ∀ (vs es : List ℕ), (∀ e ∈ es, emb₁ e = emb₂ e) →
      composeAux J₁ emb₁ vs es = composeAux J₂ emb₂ vs es
  | vs, [], _ => by cases vs with
    | nil => rfl
    | cons _ vs' => cases vs' <;> simp [composeAux]
  | [], _ :: _, _ => rfl
  | [_], _ :: _, _ => rfl
  | _ :: v :: vs, e :: es, he => by
    have he1 := he e List.mem_cons_self
    have ih := t2Mid_composeAux_congr hJe (v :: vs) es fun e' he' => he e' (List.mem_cons_of_mem e he')
    simp only [composeAux, hJe, he1, ih]

lemma t2Middle_stepInv_mid {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ} {p : Program}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {g₀ : T2Ghost impl.pathDS} {memStart mem_gp memMid : ℕ → ℕ}
    (hS : T2StepInv ctx stc g₀ memStart)
    (hV : T2VcongRoundInv ctx g₀)
    (hq_empty : g₀.queue = [])
    (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    {ci eL eW hCurNew u_loc v_loc : ℕ} {P_sub : Walk} {rep' : impl.pathDS.R.τ}
    (hci : ci < ctx.wd.comps.length)
    (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    (hnone : g₀.emb eW = none)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hcw_sub : P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub u_loc v_loc)
    (huv_eq : u_loc = msf.u_loc ∧ v_loc = msf.v_loc)
    (hPsub_len : (P_sub.edges.length : ℝ) ≤
      impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
        ctx.wd.J0_strip.m)
    (hPsub_undel : ∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted)
    (hCur_sp : hCurNew ≤ g₀.hCur +
      impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m ctx.wd.J0_strip.m)
    (hDS_gp : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) hCurNew mem_gp
      ctx.wd.comps.length g₀.states (Function.update g₀.reps ci rep'))
    (hgp_below : ∀ a < stc.dsBaseAddr, mem_gp a = memStart a)
    (hmid_agr : ∀ a,
      ¬(g₀.arenaPtr ≤ a ∧ a < g₀.arenaPtr + (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).encode.length) →
      ¬(inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
        a < inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n) →
      a ≠ inp.embWJAddr + eW → a ≠ inp.v1 + 25 → a ≠ inp.v1 + 26 →
      a ≠ inp.v1 + 4 → a ≠ inp.v1 + 6 → a ≠ inp.v1 + 30 → a ≠ inp.v1 + 27 →
      memMid a = mem_gp a)
    (res : Finset ℕ × List ℕ) (updV : ℕ)
    (hres1_mem : ∀ x, x ∈ res.1 ↔
      ∃ j ∈ (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges, x ∈ (inp.embJH j).verts)
    (hres1_sub : res.1 ⊆ Finset.range inp.H'.n)
    (hres2_sub : res.2.toFinset ⊆ res.1)
    (hres2_nd : res.2.Nodup)
    (hres2_spec : ∀ x, x ∈ res.2 ↔
      x ∈ res.1 ∧ x ∉ g₀.procVerts ∧
      memStart (inp.v1 + 28) ≤ memStart (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) +
        memStart (msf.wWNumAddr + eW))
    (hwk_PJ : WalkAt memMid g₀.arenaPtr (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub))
    (hm_emb : memMid (inp.embWJAddr + eW) = g₀.arenaPtr)
    (hm_25 : memMid (inp.v1 + 25) = g₀.arenaPtr + (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).encode.length)
    (hm_26 : memMid (inp.v1 + 26) = g₀.queryId + 1)
    (hm_4 : memMid (inp.v1 + 4) = g₀.getPathCountJ + 1)
    (hm_6 : memMid (inp.v1 + 6) = g₀.vcongUpdates + updV)
    (hm_30 : memMid (inp.v1 + 30) = (unembeddedSetPure ctx.wd g₀.emb).card - 1)
    (hm_27 : memMid (inp.v1 + 27) = res.2.length)
    (hupd_le : updV ≤ P_sub.edges.length * (length inp.J inp.embJH + 1))
    (hm_ew : ∀ x < inp.H'.n,
      memMid (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        if x ∈ res.1 then g₀.queryId + 1 else memStart (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hm_vc : ∀ x < inp.H'.n,
      memMid (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        memStart (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) +
          (if x ∈ res.1 then memStart (msf.wWNumAddr + eW) else 0))
    (hm_ps : ∀ x < inp.H'.n,
      memMid (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        if x ∈ res.2 then g₀.η₁ else memStart (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x))
    (hm_q : ∀ (k : ℕ) (hk : k < res.2.length),
      memMid (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + k) = res.2[k]'hk) :
    let c := ctx.wd.comps[ci]'hci
    let P_J := liftJSubWalk c P_sub
    let g₁ : T2Ghost impl.pathDS :=
      { g₀ with
        reps := Function.update g₀.reps ci rep'
        emb := Function.update g₀.emb eW (some P_J)
        procVerts := g₀.procVerts ∪ res.2.toFinset
        queue := res.2
        getPathCountJ := g₀.getPathCountJ + 1
        vcongUpdates := g₀.vcongUpdates + updV
        arenaPtr := g₀.arenaPtr + P_J.encode.length
        queryId := g₀.queryId + 1
        hCur := hCurNew }
    T2StepInv ctx stc g₁ memMid ∧
    T2VcongRoundInv ctx g₁ ∧
    stc.nodesEnd ≤ g₁.arenaPtr ∧
    res.2.length ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) ∧
    dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length g₁.reps memMid =
      dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
        (Function.update g₀.reps ci rep') mem_gp ∧
    t2UndelRem ctx g₁ = t2UndelRem ctx g₀ ∧
    t2VhatRem ctx g₁ = t2VhatRem ctx g₀ ∧
    t2NodeRem ctx stc g₁ = t2NodeRem ctx stc g₀ := by
  intro c P_J g₁
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  rcases huv_eq with ⟨rfl, rfl⟩
  have hcw_uv : P_sub.IsWalk c.J_sub msf.u_loc msf.v_loc := by simpa [c] using hcw_sub
  have hWe_e : ctx.wd.W.edges.getD eW (0, 0) =
      (ctx.wd.comps[ci].verts.getD msf.u_loc 0, ctx.wd.comps[ci].verts.getD msf.v_loc 0) := by
    simpa only [List.getD_eq_getElem _ _ hci] using msf.hWe_edge
  have hlift := t2_liftJSubWalk_spec ctx hS hci heL heW_eq hnone hWe_e hcw_uv hPsub_len hPsub_undel
  dsimp only at hlift
  rcases hlift with ⟨heW_m, _, hPJ_elen, hPJ_enc, hPJ_γ, hPJ_walk, _, _, hPJ_eb,
    _, hproc_disj, hPart', hELen'⟩
  have hDr_eq : g₀.drained = g₀.procVerts := by
    ext y
    refine ⟨fun hy => hS.hDr_sub hy, fun hy => ?_⟩
    by_contra hnd
    have hq_mem := (hS.hQ_mem y hy).mpr hnd
    rw [hq_empty] at hq_mem
    simp at hq_mem
  have har_new_ds : g₀.arenaPtr + P_J.encode.length ≤ stc.dsBaseAddr :=
    le_trans (Nat.add_le_add_left hPJ_enc _) msf.har_next
  have hmid_below_vc : ∀ a < inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length,
      a ≠ inp.embWJAddr + eW → a ≠ inp.v1 + 25 → a ≠ inp.v1 + 26 →
      a ≠ inp.v1 + 4 → a ≠ inp.v1 + 6 → a ≠ inp.v1 + 30 → a ≠ inp.v1 + 27 →
      memMid a = memStart a := fun a ha h0 h1 h2 h3 h4 h5 h6 =>
    (hmid_agr a (by omega) (by omega) h0 h1 h2 h3 h4 h5 h6).trans (hgp_below a (by omega))
  have hmid_lt_nodes : ∀ a < stc.nodesEnd,
      ¬(inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length ≤ a ∧
        a < inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n) →
      a ≠ inp.embWJAddr + eW → a ≠ inp.v1 + 25 → a ≠ inp.v1 + 26 →
      a ≠ inp.v1 + 4 → a ≠ inp.v1 + 6 → a ≠ inp.v1 + 30 → a ≠ inp.v1 + 27 →
      memMid a = memStart a := fun a ha hvc h0 h1 h2 h3 h4 h5 h6 =>
    (hmid_agr a (by omega) hvc h0 h1 h2 h3 h4 h5 h6).trans (hgp_below a (lt_of_lt_of_le ha db.h_nds))
  have hmid_pre : ∀ a < inp.v1, memMid a = memStart a := fun a ha =>
    hmid_below_vc a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hmid_dsH_to_vc : ∀ a, inp.dsHandlesAddr ctx.wd.W.m ≤ a →
      a < inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length →
      memMid a = memStart a := fun a h1 h2 =>
    hmid_below_vc a h2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hm_slot : ∀ k ≤ 31, k ≠ 4 → k ≠ 6 → k ≠ 25 → k ≠ 26 → k ≠ 27 → k ≠ 30 →
      memMid (inp.v1 + k) = memStart (inp.v1 + k) := fun k hk h4 h6 h25 h26 h27 h30 =>
    hmid_below_vc (inp.v1 + k) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have hmid_ds_hdl : ∀ k < ctx.wd.comps.length,
      memMid (inp.dsHandlesAddr ctx.wd.W.m + k) = mem_gp (inp.dsHandlesAddr ctx.wd.W.m + k) := fun k hk =>
    hmid_agr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hmid_ds_ge : ∀ a, stc.dsBaseAddr ≤ a → memMid a = mem_gp a := fun a ha =>
    hmid_agr a (fun ⟨h1, h2⟩ => absurd (lt_of_le_of_lt (le_trans har_new_ds ha) h2) (lt_irrefl _))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hunemb := t2_unembedded_erase_card (wd := ctx.wd) (P := P_J) heW_m hnone
  have hGetC' : g₁.getPathCountJ + (unembeddedSetPure ctx.wd g₁.emb).card =
      ctx.wd.W.m - ctx.wd.j0Edges.length := by
    have := hS.hGetC; dsimp only [g₁]; omega
  have h30' : memMid (inp.v1 + 30) = (unembeddedSetPure ctx.wd g₁.emb).card := by
    rw [hm_30]; dsimp only [g₁]; omega
  have hres1_card : res.1.card ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := by
    set S_b := (List.range P_J.edges.length).toFinset.biUnion
      fun idx => (inp.embJH (P_J.edges.getD idx 0)).verts.toFinset
    have hsub : res.1 ⊆ S_b := by
      intro x hx
      rw [hres1_mem] at hx
      rcases hx with ⟨j, hj, hxv⟩
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hj
      rw [Finset.mem_biUnion]
      refine ⟨idx, List.mem_toFinset.mpr (List.mem_range.mpr hidx), List.mem_toFinset.mpr ?_⟩
      rwa [List.getD_eq_getElem _ _ hidx]
    have hcard_b : S_b.card ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := by
      calc S_b.card ≤ ∑ idx ∈ (List.range P_J.edges.length).toFinset,
              ((inp.embJH (P_J.edges.getD idx 0)).verts.toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ (List.range P_J.edges.length).toFinset, (length inp.J inp.embJH + 1) := by
            refine Finset.sum_le_sum fun idx hidx => ?_
            rw [List.mem_toFinset, List.mem_range] at hidx
            have he_mem : P_J.edges.getD idx 0 ∈ P_J.edges := by
              rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem hidx
            exact le_trans (List.toFinset_card_le _) (hPJ_eb _ he_mem).2.2
        _ = (List.range P_J.edges.length).toFinset.card * (length inp.J inp.embJH + 1) := by
            simp
        _ ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := by
            have h1 : (List.range P_J.edges.length).toFinset.card ≤ P_J.edges.length := by
              have := List.toFinset_card_le (List.range P_J.edges.length)
              simpa using this
            rw [← hPJ_elen]
            exact Nat.mul_le_mul_right _ h1
    exact le_trans (Finset.card_le_card hsub) hcard_b
  have hQlen_le : res.2.length ≤ P_sub.edges.length * (length inp.J inp.embJH + 1) := by
    rw [← List.toFinset_card_of_nodup hres2_nd]
    exact le_trans (Finset.card_le_card hres2_sub) hres1_card
  have hVcUpd' : (g₁.vcongUpdates : ℝ) ≤
      (g₁.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) := by
    dsimp only [g₁]; push_cast
    have hPsub_γ : (P_sub.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath := by
      simpa [P_J, hPJ_elen] using hPJ_γ
    have h1 : (updV : ℝ) ≤ ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1) := by
      have hu : (updV : ℝ) ≤ (P_sub.edges.length : ℝ) * ((length inp.J inp.embJH : ℝ) + 1) := by
        exact_mod_cast hupd_le
      have hlen_nn : (0 : ℝ) ≤ (length inp.J inp.embJH : ℝ) + 1 := by positivity
      exact le_trans hu (mul_le_mul_of_nonneg_right hPsub_γ hlen_nn)
    linarith [hS.hVcUpd]
  have hInner' : (g₁.innerIters1 + g₁.queue.length : ℝ) ≤
      (g₁.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) := by
    dsimp only [g₁]; push_cast
    have hq0 : g₀.queue.length = 0 := by simp [hq_empty]
    have hPsub_γ : (P_sub.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath := by
      simpa [P_J, hPJ_elen] using hPJ_γ
    have h1 : (res.2.length : ℝ) ≤ ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1) := by
      have hq_r : (res.2.length : ℝ) ≤ (P_sub.edges.length : ℝ) * ((length inp.J inp.embJH : ℝ) + 1) := by
        exact_mod_cast hQlen_le
      have hlen_nn : (0 : ℝ) ≤ (length inp.J inp.embJH : ℝ) + 1 := by positivity
      exact le_trans hq_r (mul_le_mul_of_nonneg_right hPsub_γ hlen_nn)
    have hSin := hS.hInner
    rw [hq0, Nat.cast_zero, add_zero] at hSin
    linarith
  have hInc' : ∀ x < inp.H'.n,
      IncChainBound memMid (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
        (memMid (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
      (∀ p ∈ stc.L_inc x, ∃ (hp : p.1 < ctx.wd.comps.length),
        p.2 < (ctx.wd.comps[p.1]'hp).J_sub.m ∧
        x ∈ (inp.embJH ((ctx.wd.comps[p.1]'hp).jSubOrigEdges.getD p.2 0)).verts) ∧
      (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
        x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x) := by
    intro x hx
    have h0 := hS.hInc x hx
    refine ⟨?_, h0.2⟩
    have hvh_eq : memMid (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        memStart (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) :=
      hmid_dsH_to_vc _ (by omega) (by omega)
    rw [hvh_eq]
    exact h0.1.mono fun a ha1 ha2 =>
      hmid_lt_nodes a ha2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hEmb' : EmbInv memMid inp.embWJAddr ctx.wd.W.m stc.nodesEnd g₁.arenaPtr g₁.emb := by
    intro e' he'
    by_cases he : e' = eW
    · subst he
      dsimp only [g₁]
      rw [Function.update_self, hm_emb]
      exact ⟨har_lo, le_refl _, hwk_PJ⟩
    · dsimp only [g₁]
      rw [Function.update_of_ne he]
      have hm_ptr : memMid (inp.embWJAddr + e') = memStart (inp.embWJAddr + e') :=
        hmid_below_vc _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hold := hS.hEmb e' he'
      cases hge : g₀.emb e' with
      | none =>
        rw [hge] at hold; rwa [hm_ptr]
      | some P =>
        rw [hge] at hold
        rcases hold with ⟨h1, h2, hwk⟩
        rw [hm_ptr]
        refine ⟨h1, le_trans h2 (Nat.le_add_right _ _), ?_⟩
        have ha_w : ∀ offset, offset < 2 + P.verts.length + P.edges.length →
            memMid (memStart (inp.embWJAddr + e') + offset) =
              memStart (memStart (inp.embWJAddr + e') + offset) := fun offset hoff => by
          have hlen_p : P.encode.length = 2 + P.verts.length + P.edges.length := walk_encode_length P
          exact (hmid_agr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)).trans (hgp_below _ (by omega))
        refine walkAt_iff.mpr ⟨(ha_w 0 (by omega)).trans hwk.verts_len, ?_, ?_, ?_⟩
        · intro k hk
          rw [show memStart (inp.embWJAddr + e') + 1 + k =
              memStart (inp.embWJAddr + e') + (1 + k) by omega,
            ha_w (1 + k) (by omega)]
          simpa only [Nat.add_assoc] using hwk.verts_listAt k hk
        · rw [Nat.add_assoc, ha_w (1 + P.verts.length) (by omega), ← Nat.add_assoc]
          exact hwk.edges_len
        · intro k hk
          rw [show memStart (inp.embWJAddr + e') + 2 + P.verts.length + k =
              memStart (inp.embWJAddr + e') + (2 + P.verts.length + k) by omega,
            ha_w (2 + P.verts.length + k) (by omega)]
          simpa only [Nat.add_assoc] using hwk.edges_listAt k hk
  have hAr_le' : g₁.arenaPtr ≤ stc.nodesEnd +
      (ctx.wd.j0Edges.length + g₁.getPathCountJ) *
        (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) := by
    dsimp only [g₁]
    rw [← Nat.add_assoc, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]
    exact Nat.add_le_add hS.hAr_le hPJ_enc
  have hDS_pair := hDS_gp.frame_below (mem' := memMid) hSpec.1 hmid_ds_hdl hmid_ds_ge
  have ⟨_, _, _, _, _, _, _, hstOut⟩ := ctx.agrees_preserves_static hS.agr_pre
  have ⟨_, _, _, _, _, _, _, _, _, _, _, ha1, _⟩ := hstOut
  have hw14_lt : ctx.wInp.h + 14 < inp.v1 := by
    have : ctx.wInp.h + 20 ≤ msf.aCompExt := by rwa [← msf.haCompExt_ptr]
    have : msf.wWNumAddr + ctx.wd.W.m ≤ inp.v1 := msf.hwWNum_lt
    have : msf.aCompExt + 6 * ci + 5 < msf.wWNumAddr := msf.haCompExt_lt
    omega
  have hwN₀ : ∀ e' < ctx.wd.W.m,
      (mem₀ (mem₀ (ctx.wInp.h + 14) + e') : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW e' := by
    intro e' he'
    have hptr : mem₀ (ctx.wInp.h + 14) = memStart (ctx.wInp.h + 14) :=
      (hS.agr_pre (ctx.wInp.h + 14) hw14_lt).symm
    have hval : mem₀ (mem₀ (ctx.wInp.h + 14) + e') = memStart (msf.wWNumAddr + e') := by
      rw [hptr, msf.hwWNum_ptr]
      exact (hS.agr_pre (msf.wWNumAddr + e') (Nat.lt_of_lt_of_le (Nat.add_lt_add_left he' _) msf.hwWNum_lt)).symm
    rw [hval]; exact (msf.hwWNum_val e' he').1
  have hwN_val : memStart (msf.wWNumAddr + eW) = mem₀ (mem₀ (ctx.wInp.h + 14) + eW) := by
    have hptr : mem₀ (ctx.wInp.h + 14) = memStart (ctx.wInp.h + 14) :=
      (hS.agr_pre (ctx.wInp.h + 14) hw14_lt).symm
    rw [hptr, msf.hwWNum_ptr]
    exact hS.agr_pre (msf.wWNumAddr + eW) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left heW_m _) msf.hwWNum_lt)
  have hcomp_res1 : ∀ x, x ∈ (compose inp.J inp.embJH (partialToWalk g₁.emb) eW).verts ↔ x ∈ res.1 := by
    intro x
    rw [t2_compose_partial_mem_verts_iff ctx.hembJH (emb' := g₁.emb)
      (u := (ctx.wd.W.edges.getD eW (0, 0)).1)
      (v := (ctx.wd.W.edges.getD eW (0, 0)).2)
      (Function.update_self eW (some P_J) g₀.emb) hPJ_walk x]
    exact (hres1_mem x).symm
  have hVc' : ∀ x < inp.H'.n,
      memMid (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₁.emb x := by
    intro x hx
    rw [hm_vc x hx, hS.hVc x hx, t2_vcongNumPure_update_none ctx heW_m hnone x, hwN_val]
    simp only [hcomp_res1 x, g₁]
  have hcomp_wInp_eq : ∀ e' < ctx.wd.W.m,
      compose inp.J inp.embJH (partialToWalk g₁.emb) e' =
        compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk g₁.emb) e' := by
    intro e' he'
    unfold compose
    refine t2Mid_composeAux_congr (congrArg Graph.edges ctx.hWInpJ.symm) _ _ fun e he => ?_
    cases h0 : g₁.emb e' with
    | none => simp [partialToWalk, h0, Walk.empty] at he
    | some P =>
      have hw := hPart'.2 e' he' P h0
      rw [partialToWalk, h0] at he
      have hm : e < inp.J.m := hw.2.2.elim (fun h => by simp [h.2.1] at he) (fun h => h.2.2.2.2.1 e he)
      exact (ctx.hWInpEmb e hm).symm
  have hvcongNum_wInp_eq : ∀ x,
      vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₁.emb x =
        vcongNumPure ctx.wd ctx.wInp.prep.J ctx.wInp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₁.emb x := by
    intro x; unfold vcongNumPure
    refine Finset.sum_congr rfl fun e' he' => ?_
    simp only [hcomp_wInp_eq e' (Finset.mem_range.mp he')]
  have hvcongAt_wInp_eq : ∀ x,
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g₁.emb)) x =
        vcongAt ctx.wd.W ctx.wd.wW (compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk g₁.emb)) x := by
    intro x; unfold vcongAt; rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e' he' => ?_
    simp only [hcomp_wInp_eq e' (Finset.mem_range.mp he')]
  have hEwSt' : ∀ x < inp.H'.n,
      memMid (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ g₁.queryId := fun x hx => by
    rw [hm_ew x hx]
    dsimp only [g₁]
    split_ifs
    · exact le_refl _
    · have := hS.hEwSt x hx; omega
  have hProcS' : ∀ x < inp.H'.n,
      memMid (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ g₁.η₁ ∧
      (memMid (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = g₁.η₁ ↔ x ∈ g₁.procVerts) := by
    intro x hx
    rw [hm_ps x hx]
    dsimp only [g₁]
    have hps0 := hS.hProcS x hx
    split_ifs with hq
    · exact ⟨le_refl _, iff_of_true rfl (Finset.mem_union_right _ (List.mem_toFinset.mpr hq))⟩
    · refine ⟨hps0.1, ?_⟩
      rw [hps0.2]
      simp [Finset.mem_union, List.mem_toFinset, hq]
  have hProcSub' : ∀ x ∈ g₁.procVerts, x < inp.H'.n ∧
      (g₁.η₁ : ℝ) * ctx.wd.τ₁ ≤
        vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g₁.emb)) x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx0 | hxr
    · have h0 := hS.hProcSub x hx0
      refine ⟨h0.1, ?_⟩
      dsimp only [g₁]
      rw [t2_vcongAt_update_none ctx heW_m hnone x]
      have hwnn : 0 ≤ (if x ∈ (compose inp.J inp.embJH (partialToWalk g₁.emb) eW).verts then ctx.wd.wW eW else 0) := by
        split_ifs
        · exact (mkW_wW_pos ctx.hw_okW ctx.hws heW_m).le
        · exact le_refl _
      linarith
    · rw [List.mem_toFinset, hres2_spec] at hxr
      have hxH : x < inp.H'.n := Finset.mem_range.mp (hres1_sub hxr.1)
      refine ⟨hxH, ?_⟩
      rw [hvcongAt_wInp_eq x, vcongNumPure_ge_iff ctx.hstat hwN₀ g₁.emb x g₁.η₁,
        ← hvcongNum_wInp_eq x, ← hVc' x hxH, hm_vc x hxH]
      have hif : x ∈ res.1 := hxr.1
      simp only [hif, ↓reduceIte]
      have hthr := hxr.2.2
      rw [hS.h28] at hthr
      exact hthr
  have hQ_sub' : ∀ x ∈ g₁.queue, x < inp.H'.n ∧ x ∈ g₁.procVerts ∧ x ∉ g₁.drained := by
    intro x hx
    have hsp := (hres2_spec x).mp hx
    refine ⟨Finset.mem_range.mp (hres1_sub hsp.1), Finset.mem_union_right _ (List.mem_toFinset.mpr hx), ?_⟩
    rw [hDr_eq]; exact hsp.2.1
  have hQ_mem' : ∀ x ∈ g₁.procVerts, x ∈ g₁.queue ↔ x ∉ g₁.drained := by
    intro x hx
    dsimp only [g₁] at hx ⊢
    rw [hDr_eq]
    rcases Finset.mem_union.mp hx with hx0 | hxr
    · constructor
      · intro hq; exact absurd hx0 ((hres2_spec x).mp hq).2.1
      · intro hn; exact absurd hx0 hn
    · exact iff_of_true (List.mem_toFinset.mp hxr)
        fun hn => absurd hn ((hres2_spec x).mp (List.mem_toFinset.mp hxr)).2.1
  have hHCur' : hCurNew ≤ stc.dsBaseAddr +
      (g₁.initCountJ + g₁.deleteCountJ + g₁.getPathCountJ) * t2DsOne impl inp.J := by
    have hq_le := (ctx.ds_bounds.1 ci hci).2.2.1
    dsimp only [g₁]
    have h1 := hS.hHCur_le
    rw [show g₀.initCountJ + g₀.deleteCountJ + (g₀.getPathCountJ + 1) =
        (g₀.initCountJ + g₀.deleteCountJ + g₀.getPathCountJ) + 1 by omega,
      Nat.add_mul, Nat.one_mul]
    omega
  have hMono' : ∀ e' < ctx.wd.W.m, g₁.emb_prev e' = none ∨ g₁.emb e' = g₁.emb_prev e' := by
    intro e' he'
    by_cases he : e' = eW
    · subst he
      left
      dsimp only [g₁]
      rcases hS.hMono e' he' with hp | hp
      · exact hp
      · rw [← hp, hnone]
    · dsimp only [g₁]; rw [Function.update_of_ne he]; exact hS.hMono e' he'
  have hj0' : ∀ e' < ctx.wd.j0Edges.length, (g₁.emb e').isSome = true := by
    intro e' he'
    by_cases he : e' = eW
    · subst he
      exfalso
      have h0 := hS.hj0 e' he'
      rw [hnone] at h0; simp at h0
    · dsimp only [g₁]; rw [Function.update_of_ne he]; exact hS.hj0 e' he'
  have hslot_sub : ∀ k ≤ 31, k ≠ 4 → k ≠ 6 → k ≠ 25 → k ≠ 26 → k ≠ 27 → k ≠ 30 →
      memMid (inp.v1 + k) = memStart (inp.v1 + k) := hm_slot
  have hSumJ : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m :=
    le_trans (Nat.le_add_left _ _) (ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws)
  have hVhSum := ctx.hvhatSum_le
  have hS₁ : T2StepInv ctx stc g₁ memMid :=
    { agr_pre := fun a ha => (hmid_pre a ha).trans (hS.agr_pre a ha)
      h0 := (hslot_sub 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h0
      h1 := (hslot_sub 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h1
      hη_pos := hS.hη_pos
      hη_bd := hS.hη_bd
      h2 := (hslot_sub 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h2
      hInitC := hS.hInitC
      h3 := (hslot_sub 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h3
      hInitE := hS.hInitE
      h4 := hm_4
      hGetC := hGetC'
      h5 := (hslot_sub 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h5
      hDelEq := hS.hDelEq
      hPrevDel := hS.hPrevDel
      h6 := hm_6
      hVcUpd := hVcUpd'
      h7 := (hslot_sub 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h7
      hInner := hInner'
      h8 := (hslot_sub 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h8
      h9 := (hslot_sub 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h9
      h10 := (hslot_sub 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h10
      h12 := (hslot_sub 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h12
      h13 := (hslot_sub 13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h13
      h14 := (hslot_sub 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h14
      h15 := (hslot_sub 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h15
      h16 := (hslot_sub 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h16
      h17 := (hslot_sub 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h17
      h18 := (hslot_sub 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h18
      h19 := (hslot_sub 19 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h19
      h20 := (hslot_sub 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h20
      h21 := (hslot_sub 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h21
      h22 := (hslot_sub 22 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h22
      h23 := (hslot_sub 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h23
      h24 := (hslot_sub 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h24
      h25 := hm_25
      h26 := hm_26
      hQid := by dsimp only [g₁]; rw [hS.hQid, Nat.add_assoc]
      h27 := hm_27
      h28 := (hslot_sub 28 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h28
      h29 := (hslot_sub 29 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h29
      h30 := h30'
      h31 := (hslot_sub 31 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hS.h31
      hCeb := fun k hk =>
        (hmid_dsH_to_vc _ (by omega) (by omega)).trans (hS.hCeb k hk)
      hVho := fun k hk =>
        (hmid_dsH_to_vc _ (by omega) (by omega)).trans (hS.hVho k hk)
      hInc := hInc'
      hEmb := hEmb'
      hAr_le := hAr_le'
      hDS := hDS_pair.1
      hDelR := fun k hk b hb => by
        have ha1 := compEdgeBase_add_le hk
        have ha2 : compEdgeBase ctx.wd (k + 1) ≤ (ctx.wd.comps.map fun c => c.J_sub.m).sum :=
          compEdgeBase_le_sum (wd := ctx.wd) (by omega)
        rw [hmid_dsH_to_vc _ (by omega) (by omega)]
        exact hS.hDelR k hk b hb
      hVhatS := fun k hk y hy => by
        have ha1 := vhatBase_add_le hk
        have ha2 : vhatBase ctx.wd (k + 1) ≤ (ctx.wd.comps.map fun c => c.J_sub.n).sum :=
          vhatBase_le_sum (wd := ctx.wd) (by omega)
        rw [hmid_dsH_to_vc _ (by omega) (by omega)]
        exact hS.hVhatS k hk y hy
      hDelSub := fun k hk b hb => by
        rcases hS.hDelSub k hk b hb with ⟨hm, x, hx, hxv⟩
        exact ⟨hm, x, Finset.mem_union_left _ hx, hxv⟩
      hVc := hVc'
      hEwSt := hEwSt'
      hProcS := hProcS'
      hProcSub := hProcSub'
      hQ_nd := hres2_nd
      hQ_sub := hQ_sub'
      hDr_sub := Finset.Subset.trans hS.hDr_sub Finset.subset_union_left
      hQ_mem := hQ_mem'
      hQ_at := hm_q
      hDr_del := hS.hDr_del
      hPart := hPart'
      hMono := hMono'
      hj0 := hj0'
      hELen := hELen'
      hVc_prev := hS.hVc_prev
      hVol_prev := hS.hVol_prev
      hHCur_le := hHCur' }
  have hV₁ : T2VcongRoundInv ctx g₁ := by
    refine ⟨fun x hx => ?_, fun x hx hx_np => ?_⟩
    · by_cases hxr : x ∈ (compose inp.J inp.embJH (partialToWalk g₁.emb) eW).verts
      · have hnp : x ∉ g₀.procVerts := fun hp => (hproc_disj x hp hDr_eq).1 (by simpa [g₁] using hxr)
        have h1 := hV.2 x hx hnp
        have h2 := t2_wW_le_tau1_half ctx heW_m
        dsimp only [g₁] at hxr ⊢
        rw [t2_vcongAt_update_none ctx heW_m hnone x]
        simp only [hxr, ↓reduceIte]
        linarith only [h1, h2]
      · dsimp only [g₁] at hxr ⊢
        rw [t2_vcongAt_update_none ctx heW_m hnone x]
        simp only [hxr, ↓reduceIte, add_zero]
        exact hV.1 x hx
    · dsimp only [g₁] at hx_np ⊢
      have hnp0 : x ∉ g₀.procVerts := fun hp => hx_np (Finset.mem_union_left _ hp)
      have hnr2 : x ∉ res.2 := fun hr => hx_np (Finset.mem_union_right _ (List.mem_toFinset.mpr hr))
      by_cases hxr : x ∈ res.1
      · have hlt_thr : memStart (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) +
            memStart (msf.wWNumAddr + eW) < memStart (inp.v1 + 28) := by
          by_contra hge
          exact hnr2 ((hres2_spec x).mpr ⟨hxr, hnp0, le_of_not_gt hge⟩)
        have hle_vc : vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₁.emb x ≤
            g₁.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec := by
          rw [← hVc' x hx, hm_vc x hx, ← hS.h28]
          simp only [hxr, ↓reduceIte]
          omega
        rw [hvcongAt_wInp_eq x]
        exact (vcongNumPure_le_iff ctx.hstat hwN₀ g₁.emb x g₁.η₁).mpr (hvcongNum_wInp_eq x ▸ hle_vc)
      · rw [t2_vcongAt_update_none ctx heW_m hnone x]
        have hx_nf : x ∉ (compose inp.J inp.embJH (partialToWalk g₁.emb) eW).verts :=
          fun h => hxr ((hcomp_res1 x).mp h)
        dsimp only [g₁] at hx_nf
        simp only [hx_nf, ↓reduceIte, add_zero]
        exact hV.2 x hx hnp0
  refine ⟨hS₁, hV₁, le_trans har_lo (Nat.le_add_right _ _), hQlen_le, hDS_pair.2,
    rfl, rfl, rfl⟩

end MinCostFlow.Spanner
