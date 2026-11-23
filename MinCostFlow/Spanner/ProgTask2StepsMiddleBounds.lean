module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleBase

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Static pointers, word bounds, and `T2StepInv` step-middle preservation helpers -/

structure MiddleStaticFacts {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g₀ : T2Ghost impl.pathDS)
    (ci eL eW : ℕ) (mem : ℕ → ℕ) where
  aComps : ℕ
  cVertsPtr : ℕ
  cJOrigPtr : ℕ
  aCompExt : ℕ
  wAddr : ℕ
  wSubPtr : ℕ
  wWNumAddr : ℕ
  u_loc : ℕ
  v_loc : ℕ
  db : DrainBounds ctx stc
  hprep13 : mem (inp.v1 + 13) = ctx.wInp.prep.h
  haComps_ptr : mem (ctx.wInp.prep.h + 3) = aComps
  haComps_lt : aComps + 7 * ci + 6 < inp.v1
  h7ci_w : 7 * ci < 2 ^ w
  hcVerts_ptr : mem (aComps + 7 * ci + 2) = cVertsPtr
  hcJOrig_ptr : mem (aComps + 7 * ci + 4) = cJOrigPtr
  hcVerts_list : ListAt mem cVertsPtr (ctx.wd.comps.getD ci defaultCompInfo).verts
  hcJOrig_list : ListAt mem cJOrigPtr (ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges
  hwH14 : mem (inp.v1 + 14) = ctx.wInp.h
  haCompExt_ptr : mem (ctx.wInp.h + 12) = aCompExt
  haCompExt_lt : aCompExt + 6 * ci + 5 < wWNumAddr
  h6ci_w : 6 * ci < 2 ^ w
  hwWNum_lt : wWNumAddr + ctx.wd.W.m ≤ inp.v1
  hwSub_ptr : mem (aCompExt + 6 * ci + 1) = wSubPtr
  hwSub_gt : aCompExt + 6 * ctx.wd.comps.length ≤ wSubPtr
  hwSub_lt : wSubPtr + (2 + 2 * (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m) ≤ wAddr
  hwSub_g : GraphAt mem wSubPtr (ctx.wd.comps.getD ci defaultCompInfo).W_sub
  huv_eq : (u_loc, v_loc) = (ctx.wd.comps.getD ci defaultCompInfo).W_sub.edges.getD eL (0, 0)
  hu_lt : u_loc < (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n
  hv_lt : v_loc < (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n
  hu_mem : mem (wSubPtr + (2 + 2 * eL)) = u_loc
  hv_mem : mem (wSubPtr + (3 + 2 * eL)) = v_loc
  hwWNum_ptr : mem (ctx.wInp.h + 14) = wWNumAddr
  hwWNum_val : ∀ eW' < ctx.wd.W.m,
    (mem (wWNumAddr + eW') : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW' ∧
    1 ≤ mem (wWNumAddr + eW')
  hWe_edge : ctx.wd.W.edges.getD eW (0, 0) =
    ((ctx.wd.comps.getD ci defaultCompInfo).verts.getD u_loc 0,
     (ctx.wd.comps.getD ci defaultCompInfo).verts.getD v_loc 0)
  hembJH_at : EmbAt mem inp.embJHAddr inp.J.m inp.embJH
  hembJH_bd : EmbBounded mem inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr
  ht1_v1 : inp.t1OutAddr ≤ inp.v1
  hW_m_w : ctx.wd.W.m < 2 ^ w
  hgp_succ : g₀.getPathCountJ + 1 ≤ ctx.wd.W.m - ctx.wd.j0Edges.length
  har_next : g₀.arenaPtr + (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) ≤
    stc.dsBaseAddr
  hCur_space : g₀.hCur +
    impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n
      (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m ctx.wd.J0_strip.m ≤
    Task2Input.maxHeapEnd impl inp
  hCur_max : g₀.hCur ≤ Task2Input.maxHeapEnd impl inp
  hmax_3 : Task2Input.maxHeapEnd impl inp + 3 ≤ Task2Input.maxWordBound impl inp
  hcw_ci : impl.pathDS.params.cw * (Nat.log 2 ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.n +
    (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m + ctx.wInp.prep.phiDen_dec + ctx.wd.J0_strip.m +
    ⌈impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
      ctx.wd.J0_strip.m⌉₊ + 2) + 1) ≤ w
  hτ₁_w : (g₀.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
    ctx.wInp.prep.phiDen_dec) + 2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec + 2 ≤
    Task2Input.maxWordBound impl inp
  hup_w : g₀.vcongUpdates + ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
    (length inp.J inp.embJH + 1) ≤ Task2Input.maxWordBound impl inp
  hVc_w : ∀ x < inp.H'.n,
    mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) + mem (wWNumAddr + eW) < 2 ^ w

noncomputable def middle_static_facts {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) {g₀ : T2Ghost impl.pathDS}
    {mem : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ mem)
    {ci eL eW : ℕ} (hci : ci < ctx.wd.comps.length)
    (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m) (heW_eq : eW = (ctx.wd.comps[ci]'hci).wStart + eL)
    (hnone : g₀.emb eW = none) :
    MiddleStaticFacts ctx stc g₀ ci eL eW mem := by
  have db := drain_bounds ctx stc
  have hag := ctx.agrees_preserves_static hS.agr_pre
  rcases hag with ⟨_, _, hEmbJH, hEBJH, hpst, hcdt, _, hstOut⟩
  rcases hstOut with ⟨_, _, _, _, _, _, _, _, _, _, _, ha1, ha2, ha3, hv1_bd, hce, _, hwwn⟩
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_r : ci < ctx.wInp.prep.rawComps.length := by
    simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen] using hci
  have hchain := t2_prep_chain_bounds ctx
  have hptrs := t2_prep_comp_ptrs_le ctx hci
  have hcd_ci := hcdt ci hci_r
  have hrc_props := ctx.hstat.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hci_r)
  have hraw := rawComps_recordAt (mem := mem) ctx.hstat.toValid_zeroTail
    (fun x hx => by
      have h_ag := hS.agr_pre x (by omega)
      simp [hx]; exact h_ag) hci_r
  have hgf := ctx.wInp.buildCompsFrom_getElem_full ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1 ci hci_r
  have hverts_eq : (ctx.wd.comps.getD ci defaultCompInfo).verts = ctx.wInp.prep.rawComps[ci].2 := by
    rw [List.getD_eq_getElem _ _ hci]
    show ((ctx.wInp.buildCompsFrom ctx.wInp.prep.j0Edges.length ctx.wInp.prep.rawComps ctx.WSubs)[ci]'(hlen ▸ hci_r)).verts =
      ctx.wInp.prep.rawComps[ci].2
    rw [hgf.2.2.1]
    exact vertsOf_toFinset_of_pairwise_lt hrc_props.2.2.1
  have hjorig_eq : (ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges =
      ctx.wInp.prep.cJOrig ctx.wInp.prep.rawComps[ci] := by
    rw [List.getD_eq_getElem _ _ hci]; exact (t2_prep_cJSub_m_eq ctx hci).2.1
  have hc_bang : ctx.wInp.prep.rawComps[ci]! = ctx.wInp.prep.rawComps[ci] := by
    simp [hci_r]
  rw [hc_bang] at hcd_ci
  have hce_ci := hce ci hci
  have hwSub_g : GraphAt mem (mem (mem (ctx.wInp.h + 12) + 6 * ci + 1))
      (ctx.wd.comps.getD ci defaultCompInfo).W_sub := by
    rw [List.getD_eq_getElem _ _ hci]; exact hce_ci.2.2.2.2.2.1
  have hprops := ctx.hw_okW.comp_props ci hci
  rcases hprops with ⟨_, _, _, _, _, hc_Jn, _, _, _, _, _, hc_Wn, hc_Wvalid, _⟩
  set c := ctx.wd.comps[ci]'hci
  set eLoc := c.W_sub.edges.getD eL (0, 0)
  have heLoc_lt : eLoc.1 < c.J_sub.n ∧ eLoc.2 < c.J_sub.n := by
    have hmem : eLoc ∈ c.W_sub.edges := by
      dsimp only [eLoc]; rw [List.getD_eq_getElem _ _ heL]; exact List.getElem_mem heL
    have hv := hc_Wvalid eLoc hmem
    omega
  have hu_mem : mem (mem (mem (ctx.wInp.h + 12) + 6 * ci + 1) + (2 + 2 * eL)) = eLoc.1 := by
    have hf := graphAt_edge_fst hce_ci.2.2.2.2.2.1 heL
    dsimp only [eLoc]
    rw [List.getD_eq_getElem _ _ heL]
    simpa [Nat.add_assoc] using hf
  have hv_mem : mem (mem (mem (ctx.wInp.h + 12) + 6 * ci + 1) + (3 + 2 * eL)) = eLoc.2 := by
    have hs := graphAt_edge_snd hce_ci.2.2.2.2.2.1 heL
    dsimp only [eLoc]
    rw [List.getD_eq_getElem _ _ heL]
    simpa [Nat.add_assoc] using hs
  have hm := mkW_W_edges_comp ctx.hws hci heL
  have heW_m : eW < ctx.wd.W.m := heW_eq ▸ hm.1
  have hWe_edge : ctx.wd.W.edges.getD eW (0, 0) =
      ((ctx.wd.comps.getD ci defaultCompInfo).verts.getD eLoc.1 0,
       (ctx.wd.comps.getD ci defaultCompInfo).verts.getD eLoc.2 0) := by
    rw [List.getD_eq_getElem _ _ hci, heW_eq]
    exact hm.2.2.1
  have hmW_le := ctx.hmW_le
  have hW_m_w : ctx.wd.W.m < 2 ^ w := by
    have : Task1Input.mwCap impl inp.J ≤ inp.v1 + 32 + Task1Input.mwCap impl inp.J := by omega
    have h1 := db.e_emb; have h2 := db.e_hdl; have h3 := db.e_ceb; have h4 := db.e_vho
    have h5 := db.e_del; have h6 := db.e_vh; have h7 := db.e_vhd; have h8 := db.e_vc
    have h9 := db.e_ps; have h10 := db.e_ew; have h11 := db.e_q
    have := db.h_nlo; have := db.h_nds; have := db.h_dsc; have := db.h_stc; have := db.h_mhe; have := db.h_mwb
    omega
  have hgp_succ : g₀.getPathCountJ + 1 ≤ ctx.wd.W.m - ctx.wd.j0Edges.length := by
    have he_unemb : eW ∈ unembeddedSetPure ctx.wd g₀.emb := by
      simp [unembeddedSetPure, heW_m, hnone]
    have hcard : 1 ≤ (unembeddedSetPure ctx.wd g₀.emb).card := Finset.card_pos.mpr ⟨eW, he_unemb⟩
    have := hS.hGetC; omega
  have har_next : g₀.arenaPtr + (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) ≤
      stc.dsBaseAddr := by
    have hj0_le : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
    have hle1 : ctx.wd.j0Edges.length + (g₀.getPathCountJ + 1) ≤ ctx.wd.W.m := by omega
    have hmul := Nat.mul_le_mul_right (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) hle1
    have har := hS.hAr_le
    dsimp only [T2StaticData.dsBaseAddr]
    have : (ctx.wd.j0Edges.length + g₀.getPathCountJ) *
        (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) +
        (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) =
        (ctx.wd.j0Edges.length + (g₀.getPathCountJ + 1)) *
        (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) := by ring
    omega
  have hmax_3 : Task2Input.maxHeapEnd impl inp + 3 ≤ Task2Input.maxWordBound impl inp := by
    unfold Task2Input.maxWordBound; exact le_max_left _ _
  have hCur_max := hS.hCur_le_maxHeap
  have hdsb := ctx.ds_bounds
  have hds_ci := hdsb.1 ci hci
  have hCur_space : g₀.hCur + impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m
      ctx.wd.J0_strip.m ≤ Task2Input.maxHeapEnd impl inp := by
    have hη₁ : 1 ≤ g₀.η₁ := hS.hη_pos
    have hη₁_cap : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J :=
      ctx.hWInpJ ▸ task2_eta1Bound_le_cap ctx.hstat ctx.hφ_lb
    have hK := ctx.hK_le
    have hinit_le : g₀.initCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
      rw [hS.hInitC]; exact Nat.mul_le_mul (le_trans hS.hη_bd hη₁_cap) hK
    have hdel_cur : ∑ k ∈ Finset.range ctx.wd.comps.length, (g₀.states k).deleted.card ≤ inp.J.m :=
      drain_del_family_card_le_J ctx (fun k => (g₀.states k).deleted)
        (fun k hk b hb => (hS.hDelSub k hk b hb).1)
    have hdel_tot : g₀.deleteCountJ ≤ g₀.η₁ * inp.J.m := by
      rw [hS.hDelEq]
      have hmul : (g₀.η₁ - 1) * inp.J.m + inp.J.m = g₀.η₁ * inp.J.m := by
        calc (g₀.η₁ - 1) * inp.J.m + inp.J.m = (g₀.η₁ - 1 + 1) * inp.J.m := by ring
          _ = g₀.η₁ * inp.J.m := by rw [Nat.sub_add_cancel hη₁]
      linarith [hS.hPrevDel]
    have hdel_le : g₀.deleteCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
      le_trans hdel_tot (Nat.mul_le_mul_right _ (le_trans hS.hη_bd hη₁_cap))
    have hgp_le : g₀.getPathCountJ + 1 ≤ Task1Input.mwCap impl inp.J := by omega
    have hq_le : impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m
        ctx.wd.J0_strip.m ≤ t2DsOne impl inp.J := by
      rw [List.getD_eq_getElem _ _ hci]; exact hds_ci.2.2.1
    have htot := Nat.mul_le_mul_right (t2DsOne impl inp.J)
      (show g₀.initCountJ + g₀.deleteCountJ + (g₀.getPathCountJ + 1) ≤
        Task2Input.eta1Cap impl inp.J * inp.J.m + Task2Input.eta1Cap impl inp.J * inp.J.m +
          Task1Input.mwCap impl inp.J by omega)
    have hadd_m : (g₀.initCountJ + g₀.deleteCountJ + g₀.getPathCountJ) * t2DsOne impl inp.J +
        t2DsOne impl inp.J =
        (g₀.initCountJ + g₀.deleteCountJ + (g₀.getPathCountJ + 1)) * t2DsOne impl inp.J := by ring
    have hadd_cap : (Task2Input.eta1Cap impl inp.J * inp.J.m + Task2Input.eta1Cap impl inp.J * inp.J.m +
        Task1Input.mwCap impl inp.J) * t2DsOne impl inp.J =
        Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
          Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := by ring
    unfold Task2Input.maxHeapEnd
    change g₀.hCur + _ ≤ Task2Input.staticEndCap impl inp +
      Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
      Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
      Task1Input.mwCap impl inp.J * t2DsOne impl inp.J
    linarith [hS.hHCur_le, stc.dsBaseAddr_le_cap]
  have hcw_ci : impl.pathDS.params.cw * (Nat.log 2 ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.n +
      (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m + ctx.wInp.prep.phiDen_dec + ctx.wd.J0_strip.m +
      ⌈impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
        ctx.wd.J0_strip.m⌉₊ + 2) + 1) ≤ w := by
    rw [List.getD_eq_getElem _ _ hci]; exact hds_ci.2.2.2.1
  have hcaps := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hstat ctx.hφ_lb
  have hη₁_cap : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J :=
    ctx.hWInpJ ▸ task2_eta1Bound_le_cap ctx.hstat ctx.hφ_lb
  have htau1_le := ctx.tau1Int_le_cap
  have hpd_le : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J :=
    ctx.hWInpJ ▸ task2_phiDen_le_cap ctx.hstat ctx.hφ_cap
  have hτ₁_w : (g₀.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec) + 2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec + 2 ≤
      Task2Input.maxWordBound impl inp := by
    have hmul1 : g₀.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec ≤
        Task2Input.eta1Cap impl inp.J * _ * Task1Input.phiDenCap impl inp.J :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_trans hS.hη_bd hη₁_cap) htau1_le) hpd_le
    have hmul2 : 2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec ≤
        2 * Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hmW_le)) hpd_le
    unfold Task2Input.maxWordBound
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add hmul1 hmul2) 2) ?_
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hup_w : g₀.vcongUpdates + ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
      (length inp.J inp.embJH + 1) ≤ Task2Input.maxWordBound impl inp := by
    have hgp_r : (g₀.getPathCountJ + 1 : ℝ) ≤ (Task1Input.mwCap impl inp.J : ℝ) := by
      exact_mod_cast (show g₀.getPathCountJ + 1 ≤ Task1Input.mwCap impl inp.J by omega)
    have hγ_r : ctx.wd.γ_ExpPath ≤ (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params : ℝ) := by
      have := ctx.wInp.mkWitnessData_scalars impl.constructExpander impl.pathDS.params ctx.WSubs ctx.hstat
      linarith [this.2.2.1]
    have hlen_nn : 0 ≤ (length inp.J inp.embJH : ℝ) + 1 := by positivity
    have hvc_r : (g₀.vcongUpdates : ℝ) +
        (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params : ℝ) *
          ((length inp.J inp.embJH : ℝ) + 1) ≤
        (Task1Input.mwCap impl inp.J : ℝ) *
          ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) := by
      have h1 := hS.hVcUpd
      have hγc : (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params : ℝ) ≤
          (Task2Input.gammaExpCap impl inp.J : ℝ) := by exact_mod_cast hcaps.1
      have h2 : (g₀.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) +
          (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params : ℝ) *
            ((length inp.J inp.embJH : ℝ) + 1) ≤
          ((g₀.getPathCountJ : ℝ) + 1) *
            ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) := by
        have hmul_a : ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1) ≤
            (Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_trans hγ_r hγc) hlen_nn
        have hmul_b : (g₀.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) ≤
            (g₀.getPathCountJ : ℝ) * ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hmul_a (by positivity)
        have hmul_c : (ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params : ℝ) *
            ((length inp.J inp.embJH : ℝ) + 1) ≤
            1 * ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hγc hlen_nn
        linarith
      have h3 : ((g₀.getPathCountJ : ℝ) + 1) *
            ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) ≤
          (Task1Input.mwCap impl inp.J : ℝ) *
            ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hgp_r (by positivity)
      linarith
    have hnat : g₀.vcongUpdates + ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
        (length inp.J inp.embJH + 1) ≤
        Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J * (length inp.J inp.embJH + 1) := by
      have hnat_r : ((g₀.vcongUpdates + ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params *
          (length inp.J inp.embJH + 1) : ℕ) : ℝ) ≤
          ((Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J * (length inp.J inp.embJH + 1) : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hnat_r
    have hmwb : Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
        (length inp.J inp.embJH + 1) ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      refine le_trans ?_ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      omega
    omega
  have hv1_w : inp.v1 < 2 ^ w := by
    have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
    have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc
    have := db.e_ps; have := db.e_ew; have := db.e_q
    have := db.h_nlo; have := db.h_nds; have := db.h_dsc; have := db.h_stc
    have := db.h_mhe; have := db.h_mwb
    omega
  have hw14_lt : ctx.wInp.h + 14 < inp.v1 := by
    have : ctx.wInp.h + 20 ≤ mem (ctx.wInp.h + 12) := ha1
    have : mem (ctx.wInp.h + 14) + ctx.wd.W.m ≤ inp.v1 := hv1_bd
    omega
  have h14_mem : mem (ctx.wInp.h + 14) = mem₀ (ctx.wInp.h + 14) :=
    hS.agr_pre (ctx.wInp.h + 14) hw14_lt
  have haComps_lt : ctx.wInp.prep.aComps + 7 * ci + 6 < inp.v1 :=
    Nat.lt_of_lt_of_le hptrs.1 hchain.2.2.2
  have h7ci_w : 7 * ci < 2 ^ w :=
    Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ 6)) haComps_lt) hv1_w
  have haCompExt_lt : mem (ctx.wInp.h + 12) + 6 * ci + 5 < mem (ctx.wInp.h + 14) := by omega
  have h6ci_w : 6 * ci < 2 ^ w := by
    have : mem (ctx.wInp.h + 12) + 6 * ci + 5 < inp.v1 := by omega
    omega
  have ht1_v1 : inp.t1OutAddr ≤ inp.v1 := by omega
  have hVc_w : ∀ x < inp.H'.n,
      mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) + mem (mem (ctx.wInp.h + 14) + eW) < 2 ^ w := by
    intro x hx
    rw [hS.hVc x hx]
    have hwN₀ : ∀ e' < ctx.wd.W.m,
        (mem₀ (mem₀ (ctx.wInp.h + 14) + e') : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW e' := by
      intro e' he'
      have heq_m : mem₀ (mem₀ (ctx.wInp.h + 14) + e') = mem (mem (ctx.wInp.h + 14) + e') := by
        rw [← h14_mem]
        exact (hS.agr_pre _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left he' _) hv1_bd)).symm
      rw [heq_m]
      exact (hwwn e' he').1
    have heW_eq : mem (mem (ctx.wInp.h + 14) + eW) = mem₀ (mem₀ (ctx.wInp.h + 14) + eW) := by
      rw [← h14_mem]
      exact hS.agr_pre _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left heW_m _) hv1_bd)
    have h1 := t2_vcongNumPure_le ctx (wWNum := fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) hwN₀ g₀.emb x
    rw [← Nat.mul_assoc] at h1
    have h2 := t2_wWNum_le_maxDeg ctx hwN₀ heW_m
    have hm_ge1 : 1 ≤ ctx.wd.W.m := Nat.lt_of_le_of_lt (Nat.zero_le eW) heW_m
    have h2' : mem₀ (mem₀ (ctx.wInp.h + 14) + eW) ≤ ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
      refine le_trans h2 ?_
      have hmul : 1 * maxDeg inp.J * ctx.wInp.prep.phiDen_dec ≤
          ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm_ge1)
      simpa [Nat.one_mul] using hmul
    have hsum : vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₀.emb x +
        mem (mem (ctx.wInp.h + 14) + eW) ≤
        2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
      rw [heW_eq]
      calc vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g₀.emb x +
            mem₀ (mem₀ (ctx.wInp.h + 14) + eW)
          ≤ ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec +
            ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec := Nat.add_le_add h1 h2'
        _ = 2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by ring
    have hlt_pow : 2 * ctx.wd.W.m * maxDeg inp.J * ctx.wInp.prep.phiDen_dec < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ 2) hτ₁_w)) db.h_mwb
    exact Nat.lt_of_le_of_lt hsum hlt_pow
  exact ⟨ctx.wInp.prep.aComps, ctx.wInp.prep.cVertsPtr ci, ctx.wInp.prep.cJOrigPtr ci,
    mem (ctx.wInp.h + 12), mem (ctx.wInp.h + 13), mem (mem (ctx.wInp.h + 12) + 6 * ci + 1),
    mem (ctx.wInp.h + 14), eLoc.1, eLoc.2, db, hS.h13,
    hpst.2.2.2.2.1,
    haComps_lt, h7ci_w, hcd_ci.2.2.1, hcd_ci.2.2.2.2.1,
    by rw [hverts_eq]; exact hraw.2.2,
    by rw [hjorig_eq]; exact hcd_ci.2.2.2.2.2.2.2.2.1,
    hS.h14, rfl, haCompExt_lt, h6ci_w, hv1_bd, rfl, hce_ci.2.2.2.2.2.2.1,
    by rw [List.getD_eq_getElem _ _ hci]; exact hce_ci.2.2.2.2.2.2.2,
    hwSub_g, by rw [List.getD_eq_getElem _ _ hci],
    by rw [List.getD_eq_getElem _ _ hci]; exact heLoc_lt.1,
    by rw [List.getD_eq_getElem _ _ hci]; exact heLoc_lt.2,
    hu_mem, hv_mem, rfl, hwwn,
    hWe_edge, hEmbJH, hEBJH, ht1_v1, hW_m_w, hgp_succ, har_next, hCur_space, hCur_max, hmax_3,
    hcw_ci, hτ₁_w, hup_w, hVc_w⟩

end MinCostFlow.Spanner