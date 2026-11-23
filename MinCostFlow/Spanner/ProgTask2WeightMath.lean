module

public import MinCostFlow.Spanner.ProgTask2Math
public import MinCostFlow.Spanner.Claim87

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Component degree and witness-edge weight bounds for `mkWitnessData` -/

lemma comp_jSub_deg_le_J_deg {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let c := wd.comps[ci]
    ∀ k < c.X.card, c.J_sub.deg k ≤ inp.prep.J.deg (c.verts.getD k 0) := by
  intro wd c k hk
  have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_r : ci < inp.prep.rawComps.length := by simpa [wd, WitnessCoreInput.mkWitnessData, hlen] using hci
  have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r
  have hlvl : c.level = (inp.prep.rawComps[ci]'hci_r).1 := hgf.1
  have hX : c.X = (inp.prep.rawComps[ci]'hci_r).2.toFinset := hgf.2.1
  have hJsub : c.J_sub = inp.prep.cJSub (inp.prep.rawComps[ci]'hci_r) := hgf.2.2.2.1
  have hprops := hok.comp_props ci hci
  have hc_verts_eq : c.verts = vertsOf c.X := hprops.2.2.2.2.1
  have hc_XJ : c.X ⊆ inp.prep.J.verts := hprops.2.2.1
  have hc_deg_sub : c.J_sub.deg k =
      (DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp c.level).degIn c.X (c.verts.getD k 0) := by
    rw [hJsub]; dsimp only [PrepInput.cJSub]
    rw [← hX, ← hlvl, hc_verts_eq]
    exact inducedSubgraph_deg hk
  rw [hc_deg_sub]
  have h1 : (DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp c.level).degIn c.X (c.verts.getD k 0) ≤
      (DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp c.level).deg (c.verts.getD k 0) := by
    unfold Graph.deg
    exact degIn_mono_right (fun x hx => by
      simpa [DecomposeOutput.graphAt, Graph.verts, hs.2.2.1, stripLoops] using hc_XJ hx) _
  have hJ0_valid : inp.prep.J0_strip.IsValid := by
    rw [hs.2.2.1]; exact stripLoops_isValid hs.1
  have h2 : (DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp c.level).deg (c.verts.getD k 0) ≤
      inp.prep.J0_strip.deg (c.verts.getD k 0) :=
    graphAt_deg_le hJ0_valid inp.prep.decomp c.level _
  have h3 : inp.prep.J0_strip.deg (c.verts.getD k 0) ≤ inp.prep.J.deg (c.verts.getD k 0) := by
    rw [hs.2.2.1]; exact stripLoops_deg_le hs.1 _
  omega

lemma mkW_wW_pos {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW : ℕ} (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    0 < (inp.mkWitnessData ce pds WSubs).wW eW := by
  have hφ := hok.φ_dec_pos
  rcases mkW_W_edge_cases hws heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · rw [(mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0).2.2]
    exact hφ
  · rw [(mkW_W_edges_comp hws hci heL).2.2.2]
    positivity

lemma mkW_wW_ge_phi {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW : ℕ} (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    (inp.mkWitnessData ce pds WSubs).φ_dec ≤ (inp.mkWitnessData ce pds WSubs).wW eW := by
  have hφ := hok.φ_dec_pos
  rcases mkW_W_edge_cases hws heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · rw [(mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0).2.2]
  · rw [(mkW_W_edges_comp hws hci heL).2.2.2]
    have h1 : (1 : ℝ) ≤ (2 ^ (inp.mkWitnessData ce pds WSubs).comps[ci].level : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    nlinarith

lemma mkW_wW_ge_two_phi_comp {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW : ℕ} (hge : (inp.mkWitnessData ce pds WSubs).j0Edges.length ≤ eW)
    (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    2 * (inp.mkWitnessData ce pds WSubs).φ_dec ≤ (inp.mkWitnessData ce pds WSubs).wW eW := by
  have hφ := hok.φ_dec_pos
  rcases mkW_W_edge_cases hws heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · omega
  · rw [(mkW_W_edges_comp hws hci heL).2.2.2]
    have hpos := (hok.comp_props ci hci).1
    have h2pow : (2 : ℝ) ≤ (2 ^ (inp.mkWitnessData ce pds WSubs).comps[ci].level : ℝ) := by
      exact_mod_cast Nat.le_self_pow hpos.ne' 2
    nlinarith

lemma mkW_wW_le_maxDeg {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW : ℕ} (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    (inp.mkWitnessData ce pds WSubs).wW eW ≤ (maxDeg inp.prep.J : ℝ) := by
  have hJ : inp.prep.J.IsValid := hs.1
  rcases mkW_W_edge_cases hws heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · rw [(mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0).2.2]
    have hj_lt := hok.j0_lt _ (List.getElem_mem (by simpa [WitnessCoreInput.mkWitnessData] using hj0))
    have hm : (inp.mkWitnessData ce pds WSubs).j0Edges[eW]'hj0 < inp.prep.J.edges.length := by
      simpa [Graph.m] using hj_lt
    set e := inp.prep.J.edges[(inp.mkWitnessData ce pds WSubs).j0Edges[eW]'hj0]'hm
    have he_mem : e ∈ inp.prep.J.edges := List.getElem_mem hm
    have hv1 : e.1 < inp.prep.J.n := (hJ e he_mem).1
    have hdeg1 : 1 ≤ inp.prep.J.deg e.1 := by
      rw [deg_eq_filter_edges hJ e.1]
      have hpos : 0 < (inp.prep.J.edges.filter fun x => decide (x.1 = e.1)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨e, List.mem_filter.mpr ⟨he_mem, decide_eq_true rfl⟩⟩
      omega
    have hle : 1 ≤ maxDeg inp.prep.J := le_trans hdeg1 (deg_le_maxDeg hv1)
    exact le_trans hok.φ_dec_le (by exact_mod_cast hle)
  · rw [(mkW_W_edges_comp hws hci heL).2.2.2]
    set wd := inp.mkWitnessData ce pds WSubs
    set c := wd.comps[ci]
    have hprops := hok.comp_props ci hci
    have hX2 : 2 ≤ c.X.card := hprops.2.2.2.1
    have hc_XJ : c.X ⊆ inp.prep.J.verts := hprops.2.2.1
    have hc_verts_eq : c.verts = vertsOf c.X := hprops.2.2.2.2.1
    have hdeg_ge_phi := hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h0lt : 0 < c.X.card := by omega
    have hφ_le_Jsub : wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg 0 : ℝ) := hdeg_ge_phi 0 h0lt
    have hv0_X : c.verts.getD 0 0 ∈ c.X := by rw [hc_verts_eq]; exact getD_vertsOf_mem h0lt
    have hv0_J : c.verts.getD 0 0 < inp.prep.J.n := Finset.mem_range.mp (hc_XJ hv0_X)
    have hdeg_le : c.J_sub.deg 0 ≤ inp.prep.J.deg (c.verts.getD 0 0) :=
      comp_jSub_deg_le_J_deg hs hok hws hci 0 h0lt
    have hmax : inp.prep.J.deg (c.verts.getD 0 0) ≤ maxDeg inp.prep.J := deg_le_maxDeg hv0_J
    exact le_trans hφ_le_Jsub (by exact_mod_cast (le_trans hdeg_le hmax))

lemma mkW_maxDeg_le_tau_half {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hlen : 1 ≤ length inp.prep.J inp.embJH) :
    (maxDeg inp.prep.J : ℝ) ≤ (inp.mkWitnessData ce pds WSubs).τ₁ / 2 := by
  have hsc := inp.mkWitnessData_scalars ce pds WSubs hs
  have htau : (inp.mkWitnessData ce pds WSubs).τ₁ = (inp.tau1Int ce pds : ℝ) := hsc.2.2.2.2.2
  have hφ_pos : (0 : ℝ) < inp.phiDsDenInt ce pds := by
    have h1 := hok.φ_ds_pos; rw [hsc.2.1] at h1
    exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h1)
  have hds_ge2 : 2 ≤ inp.phiDsDenInt ce pds := by
    have hhalf : (1 : ℝ) / (inp.phiDsDenInt ce pds : ℝ) ≤ 1 / 2 := hsc.2.1 ▸ hok.φ_ds_half
    have h2r : (2 : ℝ) ≤ (inp.phiDsDenInt ce pds : ℝ) := by
      have : 2 * (1 : ℝ) ≤ (inp.phiDsDenInt ce pds : ℝ) := by
        calc 2 * (1 : ℝ) = (1 / 2 : ℝ)⁻¹ := by norm_num
          _ ≤ (1 / (inp.phiDsDenInt ce pds : ℝ))⁻¹ :=
            inv_anti₀ (by rw [← hsc.2.1]; exact hok.φ_ds_pos) hhalf
          _ = (inp.phiDsDenInt ce pds : ℝ) := by field_simp
      linarith
    exact_mod_cast h2r
  have hγE_ge1 : 1 ≤ inp.γExpInt ce pds := by
    have hle := hok.γ_ExpPath_ge
    rw [hsc.2.1, hsc.2.2.1] at hle
    have h2 : (2 : ℝ) ≤ (inp.γExpInt ce pds : ℝ) := by
      have hhalf : (2 : ℝ) ≤ 1 / (1 / (inp.phiDsDenInt ce pds : ℝ)) := by
        rw [one_div_one_div]; exact_mod_cast hds_ge2
      linarith
    exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 2) h2)
  have hγD_ge1 : 1 ≤ inp.γDelInt ce pds := by
    have h1 := hok.γ_del_ge; rw [hsc.2.2.2.1] at h1; exact_mod_cast h1
  have htau2_ge1 : 1 ≤ inp.tau2Int ce pds := by
    unfold WitnessCoreInput.tau2Int
    exact Nat.le_trans (by omega) (Nat.mul_le_mul (Nat.mul_le_mul hγE_ge1 hγD_ge1) hds_ge2)
  have h2m : 2 * maxDeg inp.prep.J ≤ inp.tau1Int ce pds := by
    unfold WitnessCoreInput.tau1Int
    have hprod : 1 ≤ inp.tau2Int ce pds * length inp.prep.J inp.embJH :=
      Nat.le_trans (by decide) (Nat.mul_le_mul htau2_ge1 hlen)
    nlinarith
  have h2r : (2 : ℝ) * (maxDeg inp.prep.J : ℝ) ≤ (inp.tau1Int ce pds : ℝ) := by exact_mod_cast h2m
  linarith [htau]

lemma mkW_maxDeg_pos_of_W_pos {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    (hembJH : IsEmbedding inp.prep.J inp.H' inp.embJH)
    (hWpos : 0 < (inp.mkWitnessData ce pds WSubs).W.m) :
    1 ≤ maxDeg inp.prep.J ∧ 1 ≤ length inp.prep.J inp.embJH := by
  have hJ : inp.prep.J.IsValid := hs.1
  have hfrom : ∀ {eJ : ℕ}, eJ < inp.prep.J.m →
      (inp.prep.J.edges.getD eJ (0, 0)).1 ≠ (inp.prep.J.edges.getD eJ (0, 0)).2 →
      1 ≤ maxDeg inp.prep.J ∧ 1 ≤ length inp.prep.J inp.embJH := by
    intro eJ heJ hne
    have hm : eJ < inp.prep.J.edges.length := heJ
    set e := inp.prep.J.edges[eJ]'hm
    have he_mem : e ∈ inp.prep.J.edges := List.getElem_mem hm
    have hv1 : e.1 < inp.prep.J.n := (hJ e he_mem).1
    have hdeg1 : 1 ≤ inp.prep.J.deg e.1 := by
      rw [deg_eq_filter_edges hJ e.1]
      have hpos : 0 < (inp.prep.J.edges.filter fun x => decide (x.1 = e.1)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨e, List.mem_filter.mpr ⟨he_mem, decide_eq_true rfl⟩⟩
      omega
    have hle_m : 1 ≤ maxDeg inp.prep.J := le_trans hdeg1 (deg_le_maxDeg hv1)
    have hne_e : (inp.embJH eJ).edges ≠ [] := isWalk_nonloop_edges_ne hembJH heJ hne
    have hlen_e : 1 ≤ (inp.embJH eJ).edges.length := List.length_pos_iff_ne_nil.mpr hne_e
    have hlen_emb : (inp.embJH eJ).edges.length ≤ length inp.prep.J inp.embJH := by
      unfold length
      exact Finset.le_sup (f := fun e => (inp.embJH e).edges.length) (Finset.mem_range.mpr heJ)
    exact ⟨hle_m, le_trans hlen_e hlen_emb⟩
  rcases mkW_W_edge_cases hws hWpos with hj0 | ⟨ci, hci, _, _, _⟩
  · have hnl := mkW_j0_nonloop hs hj0
    exact hfrom hnl.1 hnl.2
  · have hprops := hok.comp_props ci hci
    have hj_pos : 0 < (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.length := by
      rw [hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact hprops.2.2.2.2.2.2.2.1
    have hnl := mkW_comp_jOrig_nonloop hs hws hci hj_pos
    exact hfrom hnl.1 hnl.2

lemma mkW_sum_comp_j_m_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ wd.J0_strip.m := by
  intro wd
  have hnl_eq : wd.nlIdx = nonloopIndices inp.prep.J := hs.2.2.2.2.1
  have hJ0_eq : wd.J0_strip = stripLoops inp.prep.J := hs.2.2.1
  have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
    rw [hnl_eq, hJ0_eq]; simp [stripLoops, Graph.m]
  have hnl_nodup : wd.nlIdx.Nodup := by
    rw [hnl_eq]; exact nonloopIndices_nodup inp.prep.J
  have hunion : (wd.j0Edges.toFinset ∪
      (Finset.range wd.comps.length).biUnion fun ci =>
        if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅) ⊆
      wd.nlIdx.toFinset := by
    intro jOrig hj
    rcases Finset.mem_union.mp hj with hj0 | hjc
    · rw [List.mem_toFinset] at hj0 ⊢
      dsimp only [wd, WitnessCoreInput.mkWitnessData, PrepInput.j0Edges] at hj0
      rw [List.mem_map] at hj0
      rcases hj0 with ⟨b, hb, rfl⟩
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
      have hb' : b < inp.prep.nlIdx.length := hnl_len.symm ▸ hb.1
      change inp.prep.nlIdx.getD b 0 ∈ inp.prep.nlIdx
      rw [List.getD_eq_getElem _ _ hb']
      exact List.getElem_mem hb'
    · rcases Finset.mem_biUnion.mp hjc with ⟨ci, hci_r, hjci⟩
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      split_ifs at hjci
      rw [List.mem_toFinset] at hjci
      have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
      have hci_r' : ci < inp.prep.rawComps.length := by simpa [wd, WitnessCoreInput.mkWitnessData, hlen] using hci
      have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r'
      have hgf_orig : (wd.comps[ci]'hci).jSubOrigEdges = inp.prep.cJOrig (inp.prep.rawComps[ci]'hci_r') :=
        hgf.2.2.2.2.1
      rw [hgf_orig, PrepInput.cJOrig, List.mem_map] at hjci
      rcases hjci with ⟨a, ha, rfl⟩
      have ha_lt := (mem_insideIndices.mp ha).1
      have ha_ed : a < (inp.prep.decomp.edgesAt inp.prep.J0_strip (inp.prep.rawComps[ci]'hci_r').1).length := by
        simpa [DecomposeOutput.graphAt, Graph.m] using ha_lt
      rw [List.getD_eq_getElem _ _ ha_ed]
      have hb_mem : (inp.prep.decomp.edgesAt inp.prep.J0_strip (inp.prep.rawComps[ci]'hci_r').1)[a]'ha_ed ∈
          inp.prep.decomp.edgesAt inp.prep.J0_strip (inp.prep.rawComps[ci]'hci_r').1 := List.getElem_mem _
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
      have hb_nl : (inp.prep.decomp.edgesAt inp.prep.J0_strip (inp.prep.rawComps[ci]'hci_r').1)[a]'ha_ed < inp.prep.nlIdx.length :=
        hnl_len.symm ▸ hb_mem.1
      change inp.prep.nlIdx.getD _ 0 ∈ inp.prep.nlIdx.toFinset
      rw [List.getD_eq_getElem _ _ hb_nl, List.mem_toFinset]
      exact List.getElem_mem hb_nl
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint, Finset.card_biUnion] at hcard
  · have hj0_card : wd.j0Edges.toFinset.card = wd.j0Edges.length := List.toFinset_card_of_nodup hok.j0_nodup
    have hnl_card : wd.nlIdx.toFinset.card = wd.nlIdx.length := List.toFinset_card_of_nodup hnl_nodup
    have hsum_eq : (∑ ci ∈ Finset.range wd.comps.length,
        (if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅).card) =
        (wd.comps.map fun c => c.J_sub.m).sum := by
      have hcongr : (∑ ci ∈ Finset.range wd.comps.length,
          (if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅).card) =
          ∑ ci ∈ Finset.range wd.comps.length, (wd.comps.getD ci defaultCompInfo).J_sub.m := by
        refine Finset.sum_congr rfl fun ci hci_r => ?_
        have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
        rcases hok.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, hjNodup, _, _, _⟩
        split_ifs
        rw [List.toFinset_card_of_nodup hjNodup, hjLen, List.getD_eq_getElem _ _ hci]
      rw [hcongr, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
    rw [hj0_card, hnl_card, hsum_eq, hnl_len] at hcard
    exact hcard
  · intro ci₁ h1 ci₂ h2 hne
    change Disjoint _ _
    have h1' := Finset.mem_range.mp h1
    have h2' := Finset.mem_range.mp h2
    dsimp only
    split_ifs
    exact hok.comp_disjoint ci₁ ci₂ h1' h2' hne
  · rw [Finset.disjoint_left]
    intro jOrig hj0 hjc
    rcases Finset.mem_biUnion.mp hjc with ⟨ci, hci_r, hjci⟩
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    split_ifs at hjci
    exact Finset.disjoint_left.mp (hok.comp_disjoint_j0 ci hci) hjci hj0

lemma mkW_sum_comp_j_m_le_J {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    wd.j0Edges.length + (wd.comps.map fun c => c.J_sub.m).sum ≤ inp.prep.J.m := by
  intro wd
  have h1 := mkW_sum_comp_j_m_le hs hok hws
  have h2 : wd.J0_strip.m ≤ inp.prep.J.m := by
    rw [show wd.J0_strip = stripLoops inp.prep.J from hs.2.2.1]
    exact stripLoops_m_le inp.prep.J
  exact le_trans h1 h2

private lemma sum_Ico_comps_eq (wFn : ℕ → ℝ) (φ : ℝ) :
    ∀ (offset : ℕ) (cs : List CompInfo), CompsAligned offset cs →
      (∀ (ci : ℕ) (hci : ci < cs.length) (eL : ℕ), eL < cs[ci].W_sub.m →
        wFn (cs[ci].wStart + eL) = φ * (2 ^ cs[ci].level : ℝ)) →
      ∑ eW ∈ Finset.Ico offset (offset + (cs.map fun c => c.W_sub.m).sum), wFn eW =
        (cs.map fun c => (c.W_sub.m : ℝ) * (φ * (2 ^ c.level : ℝ))).sum := by
  intro offset cs
  induction cs generalizing offset with
  | nil => intro _ _; simp
  | cons c rest ih =>
    intro hal hw_eq
    change c.wStart = offset ∧ CompsAligned (offset + c.W_sub.m) rest at hal
    rcases hal with ⟨hwStart, hrest⟩
    have hsplit : offset + (c.W_sub.m + (rest.map fun c => c.W_sub.m).sum) =
        offset + c.W_sub.m + (rest.map fun c => c.W_sub.m).sum := by omega
    simp only [List.map_cons, List.sum_cons, hsplit]
    rw [← Finset.sum_Ico_consecutive wFn (by omega : offset ≤ offset + c.W_sub.m) (by omega)]
    have hhead : ∑ eW ∈ Finset.Ico offset (offset + c.W_sub.m), wFn eW =
        (c.W_sub.m : ℝ) * (φ * (2 ^ c.level : ℝ)) := by
      have hcongr : ∑ eW ∈ Finset.Ico offset (offset + c.W_sub.m), wFn eW =
          ∑ _eW ∈ Finset.Ico offset (offset + c.W_sub.m), (φ * (2 ^ c.level : ℝ)) := by
        refine Finset.sum_congr rfl fun eW heW => ?_
        have hmem := Finset.mem_Ico.mp heW
        have heq := hw_eq 0 (by simp) (eW - offset) (by simp; omega)
        simp only [List.getElem_cons_zero, hwStart] at heq
        rw [← heq]; congr 1; omega
      rw [hcongr, Finset.sum_const, Nat.card_Ico, show offset + c.W_sub.m - offset = c.W_sub.m by omega,
        nsmul_eq_mul]
    have htail : ∑ eW ∈ Finset.Ico (offset + c.W_sub.m) (offset + c.W_sub.m + (rest.map fun c => c.W_sub.m).sum), wFn eW =
        (rest.map fun c => (c.W_sub.m : ℝ) * (φ * (2 ^ c.level : ℝ))).sum :=
      ih (offset + c.W_sub.m) hrest fun ci hci eL heL =>
        hw_eq (ci + 1) (by simpa using Nat.succ_lt_succ hci) eL heL
    rw [hhead, htail]

lemma mkW_comp_W_m_mul_weight_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let c := wd.comps[ci]
    (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)) ≤ wd.c_deg * (c.J_sub.m : ℝ) := by
  intro wd c
  rcases hok.comp_props ci hci with
    ⟨_, _, _, _, _, hJn, hJvalid, _, _, _, _, hWn, hWvalid, _, _, _, _, hdegSand, _⟩
  have hφ : 0 < wd.φ_dec := hok.φ_dec_pos
  have h2W : (2 * (c.W_sub.m : ℝ)) = ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ) := by
    have hvol := vol_verts_eq_two_mul_m hWvalid
    have hnat : 2 * c.W_sub.m = ∑ k ∈ Finset.range c.X.card, c.W_sub.deg k := by
      rw [← hvol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hWn]
    exact_mod_cast hnat
  have h2J : (2 * (c.J_sub.m : ℝ)) = ∑ k ∈ Finset.range c.X.card, (c.J_sub.deg k : ℝ) := by
    have hvol := vol_verts_eq_two_mul_m hJvalid
    have hnat : 2 * c.J_sub.m = ∑ k ∈ Finset.range c.X.card, c.J_sub.deg k := by
      rw [← hvol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hJn]
    exact_mod_cast hnat
  have hsum_le : (2 * (c.W_sub.m : ℝ)) ≤
      wd.c_deg * (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
    rw [h2W]
    calc ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ)
        ≤ ∑ k ∈ Finset.range c.X.card,
            wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))) :=
          Finset.sum_le_sum fun k hk => (hdegSand k (Finset.mem_range.mp hk)).2
      _ = wd.c_deg * ((∑ k ∈ Finset.range c.X.card, (c.J_sub.deg k : ℝ)) /
            (wd.φ_dec * (2 ^ c.level : ℝ))) := by
          rw [← Finset.mul_sum]; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
      _ = wd.c_deg * (2 * (c.J_sub.m : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
          rw [h2J]; ring
  have hmul : (2 * (c.W_sub.m : ℝ)) * (wd.φ_dec * (2 ^ c.level : ℝ)) ≤
      wd.c_deg * (2 * (c.J_sub.m : ℝ)) :=
    (le_div_iff₀ (by positivity)).mp hsum_le
  linarith

lemma mkW_sum_wW_comp_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    ∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m, wd.wW eW ≤ wd.c_deg * (inp.prep.J.m : ℝ) := by
  intro wd
  have hWm := hok.W_m_eq
  rw [hWm, sum_Ico_comps_eq wd.wW wd.φ_dec wd.j0Edges.length wd.comps hok.aligned
    (fun ci hci eL heL => (mkW_W_edges_comp hws hci heL).2.2.2)]
  rw [← sum_range_getD_real wd.comps defaultCompInfo
    (fun c => (c.W_sub.m : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ)))]
  have hle1 : ∑ ci ∈ Finset.range wd.comps.length,
      ((wd.comps.getD ci defaultCompInfo).W_sub.m : ℝ) *
        (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) ≤
      ∑ ci ∈ Finset.range wd.comps.length,
        wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) := by
    refine Finset.sum_le_sum fun ci hci_r => ?_
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    rw [List.getD_eq_getElem _ _ hci]
    exact mkW_comp_W_m_mul_weight_le hok hci
  have heq2 : ∑ ci ∈ Finset.range wd.comps.length,
      wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) =
      wd.c_deg * (((wd.comps.map fun c => c.J_sub.m).sum : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.J_sub.m)]
  have hjm : (wd.comps.map fun c => c.J_sub.m).sum ≤ inp.prep.J.m :=
    le_trans (Nat.le_add_left _ _) (mkW_sum_comp_j_m_le_J hs hok hws)
  have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hok.c_deg_ge
  exact le_trans hle1 (heq2 ▸ mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hjm) hc)

lemma mkW_W_m_le_n {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    (wd.W.m : ℝ) ≤ (inp.prep.J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec := by
  intro wd
  have hdp := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJ0 : wd.J0_strip = stripLoops inp.prep.J := hs.2.2.1
  have hJ0n : wd.J0_strip.n = inp.prep.J.n := by rw [hJ0]; rfl
  have hφ := hok.φ_dec_pos
  have hc : 0 ≤ wd.c_deg := le_trans (by norm_num) hok.c_deg_ge
  have hj0_le : wd.j0Edges.length ≤ inp.prep.J.n := by
    have hm0 : (wd.decomp.graphAt wd.J0_strip 0).m ≤ 2 ^ 0 * wd.J0_strip.n := hdp.2.2.1 0 (Nat.zero_le _)
    have hlen0 : wd.j0Edges.length = (wd.decomp.graphAt wd.J0_strip 0).m := by
      simp [wd, WitnessCoreInput.mkWitnessData, PrepInput.j0Edges, DecomposeOutput.graphAt, Graph.m]
    omega
  have hsum_comp : (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) ≤
      (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec := by
    have h1 : (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ) ≤
        ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) := by
      rw [← sum_range_getD_nat wd.comps defaultCompInfo (fun c => c.W_sub.m), Nat.cast_sum]
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      rw [List.getD_eq_getElem _ _ hci, le_div_iff₀ (by positivity)]
      exact mkW_comp_W_m_mul_weight_le hok hci
    have hfib : ∑ ci ∈ Finset.range wd.comps.length,
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) =
        ∑ i ∈ Finset.Icc 1 wd.decomp.ℓ,
          ∑ ci ∈ (Finset.range wd.comps.length).filter
              (fun ci => (wd.comps.getD ci defaultCompInfo).level = i),
            wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
              (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) := by
      symm
      refine Finset.sum_fiberwise_of_maps_to (fun ci hci_r => ?_) _
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      rw [List.getD_eq_getElem _ _ hci, Finset.mem_Icc]
      exact ⟨(hok.comp_props ci hci).1, (hok.comp_props ci hci).2.1⟩
    have hlev_le : ∀ i ∈ Finset.Icc 1 wd.decomp.ℓ,
        ∑ ci ∈ (Finset.range wd.comps.length).filter
            (fun ci => (wd.comps.getD ci defaultCompInfo).level = i),
          wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) ≤
          wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec := by
      intro i hi
      have hiℓ : i ≤ wd.decomp.ℓ := (Finset.mem_Icc.mp hi).2
      set S := (Finset.range wd.comps.length).filter
        (fun ci => (wd.comps.getD ci defaultCompInfo).level = i)
      have hcongr : ∑ ci ∈ S,
            wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
              (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) =
          wd.c_deg * ((∑ ci ∈ S, (wd.comps.getD ci defaultCompInfo).J_sub.m : ℕ) : ℝ) /
            (wd.φ_dec * (2 ^ i : ℝ)) := by
        rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun ci hci_S => ?_
        rw [(Finset.mem_filter.mp hci_S).2]
      rw [hcongr]
      have hnat_le : ∑ ci ∈ S, (wd.comps.getD ci defaultCompInfo).J_sub.m ≤ 2 ^ i * inp.prep.J.n := by
        set img := ((wd.decomp.edgesAt wd.J0_strip i).map fun b => inp.prep.nlIdx.getD b 0).toFinset
        have hsub : (S.biUnion fun ci =>
            if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅) ⊆ img := by
          intro x hx
          rcases Finset.mem_biUnion.mp hx with ⟨ci, hci_S, hxci⟩
          have hci : ci < wd.comps.length := Finset.mem_range.mp (Finset.mem_filter.mp hci_S).1
          have hlev_eq : (wd.comps[ci]'hci).level = i := by
            have := (Finset.mem_filter.mp hci_S).2
            rwa [List.getD_eq_getElem _ _ hci] at this
          split_ifs at hxci
          rw [List.mem_toFinset] at hxci
          have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
          have hci_r' : ci < inp.prep.rawComps.length := by
            simpa [wd, WitnessCoreInput.mkWitnessData, hlen] using hci
          have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r'
          have hlev_raw : (inp.prep.rawComps[ci]'hci_r').1 = i := hgf.1.symm.trans hlev_eq
          have horig : (wd.comps[ci]'hci).jSubOrigEdges = inp.prep.cJOrig (inp.prep.rawComps[ci]'hci_r') :=
            hgf.2.2.2.2.1
          rw [horig, PrepInput.cJOrig, List.mem_map] at hxci
          rcases hxci with ⟨a, ha, rfl⟩
          have ha_lt : a < (wd.decomp.edgesAt wd.J0_strip i).length := by
            have := (mem_insideIndices.mp ha).1
            simpa [DecomposeOutput.graphAt, Graph.m, hlev_raw, wd, WitnessCoreInput.mkWitnessData] using this
          simp only [img, List.mem_toFinset, List.mem_map]
          refine ⟨(wd.decomp.edgesAt wd.J0_strip i).getD a 0, ?_, by rw [hlev_raw]; rfl⟩
          rw [List.getD_eq_getElem _ _ ha_lt]
          exact List.getElem_mem ha_lt
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_biUnion] at hcard
        · have hsum_card : (∑ ci ∈ S,
              (if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅).card) =
              ∑ ci ∈ S, (wd.comps.getD ci defaultCompInfo).J_sub.m := by
            refine Finset.sum_congr rfl fun ci hci_S => ?_
            have hci : ci < wd.comps.length := Finset.mem_range.mp (Finset.mem_filter.mp hci_S).1
            rcases hok.comp_props ci hci with
              ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, hjNodup, _, _, _⟩
            split_ifs
            rw [List.toFinset_card_of_nodup hjNodup, hjLen, List.getD_eq_getElem _ _ hci]
          rw [hsum_card] at hcard
          have himg_le : img.card ≤ (wd.decomp.graphAt wd.J0_strip i).m := by
            calc img.card ≤ ((wd.decomp.edgesAt wd.J0_strip i).map fun b => inp.prep.nlIdx.getD b 0).length :=
                  List.toFinset_card_le _
              _ = (wd.decomp.graphAt wd.J0_strip i).m := by
                  simp [DecomposeOutput.graphAt, Graph.m]
          have hgi_le : (wd.decomp.graphAt wd.J0_strip i).m ≤ 2 ^ i * inp.prep.J.n := by
            rw [← hJ0n]
            exact hdp.2.2.1 i hiℓ
          exact le_trans hcard (le_trans himg_le hgi_le)
        · intro ci₁ h1 ci₂ h2 hne
          have h1' : ci₁ < wd.comps.length := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
          have h2' : ci₂ < wd.comps.length := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
          change Disjoint (if h : ci₁ < wd.comps.length then _ else _) (if h : ci₂ < wd.comps.length then _ else _)
          split_ifs
          exact hok.comp_disjoint ci₁ ci₂ h1' h2' hne
      have hreal_le : ((∑ ci ∈ S, (wd.comps.getD ci defaultCompInfo).J_sub.m : ℕ) : ℝ) ≤
          (2 ^ i : ℝ) * (inp.prep.J.n : ℝ) := by exact_mod_cast hnat_le
      calc wd.c_deg * ((∑ ci ∈ S, (wd.comps.getD ci defaultCompInfo).J_sub.m : ℕ) : ℝ) /
            (wd.φ_dec * (2 ^ i : ℝ))
          ≤ wd.c_deg * ((2 ^ i : ℝ) * (inp.prep.J.n : ℝ)) / (wd.φ_dec * (2 ^ i : ℝ)) := by gcongr
        _ = wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec := by
            have hpow : (2 ^ i : ℝ) ≠ 0 := by positivity
            field_simp [hpow]
    calc (((wd.comps.map fun c => c.W_sub.m).sum : ℕ) : ℝ)
        ≤ ∑ i ∈ Finset.Icc 1 wd.decomp.ℓ,
            ∑ ci ∈ (Finset.range wd.comps.length).filter
                (fun ci => (wd.comps.getD ci defaultCompInfo).level = i),
              wd.c_deg * ((wd.comps.getD ci defaultCompInfo).J_sub.m : ℝ) /
                (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ)) := hfib ▸ h1
      _ ≤ ∑ _i ∈ Finset.Icc 1 wd.decomp.ℓ, (wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec) :=
          Finset.sum_le_sum hlev_le
      _ = (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.prep.J.n : ℝ) / wd.φ_dec := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  rw [hok.W_m_eq, Nat.cast_add]
  exact add_le_add (by exact_mod_cast hj0_le) hsum_comp

end MinCostFlow.Spanner
