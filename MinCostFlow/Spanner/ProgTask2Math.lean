module

public import MinCostFlow.Spanner.ProgTask2
public import MinCostFlow.Spanner.ProgTask1Proof
public import MinCostFlow.Spanner.Vacuity

/-!
# Cap bounds and structural lifting lemmas for Word-RAM Task 2

This module provides:
1. Monotonicity comparisons bounding actual `WitnessCoreInput` scalars and `eta1Bound` against the
   uniform `Task2Input.*Cap` caps (`task2_phiDen_le_cap`, `task2_dJ_le_cap`, etc.).
2. Structural characterizations of `wd := wInp.mkWitnessData ce pds WSubs` (`mkW_W_edges_j0`,
   `mkW_W_edges_comp`, `mkW_W_edge_cases`, `mkW_comp_jOrig_edge`, `mkW_isWalk_liftJSubWalk`).
3. Exact non-loop composition equivalence (`compose_nonloop_mem_verts_iff`).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Cap and word-width comparison lemmas -/

lemma task2_phiDen_le_cap {impl : SpannerToolImpl} {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hφ_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m) :
    wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl wInp.prep.J := by
  simpa [Task1Input.phiDenCap, hs.2.2.1] using hφ_cap

lemma task2_dJ_le_cap {impl : SpannerToolImpl} {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤ (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    wInp.dJInt ≤ Task1Input.dJCap impl wInp.prep.J := by
  rw [WitnessCoreInput.dJInt_eq wInp hs]
  dsimp only [Task1Input.dJCap]
  have hJ0 := hs.2.2.1
  rw [← hJ0]
  exact Nat.ceil_mono (one_div_le_one_div_of_le (impl.decompose.hφ_lb_pos _) hφ_lb)

lemma task2_mw_le_cap {impl : SpannerToolImpl} {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤ (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    wInp.mwInt impl.constructExpander ≤ Task1Input.mwCap impl wInp.prep.J := by
  rw [WitnessCoreInput.mwInt_eq wInp impl.constructExpander hs]
  dsimp only [Task1Input.mwCap]
  have hJ0 := hs.2.2.1
  have hφ_pos : 0 < impl.decompose.φ_lb (stripLoops wInp.prep.J).m := impl.decompose.hφ_lb_pos _
  have hφ_lb' : impl.decompose.φ_lb (stripLoops wInp.prep.J).m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec := by rwa [← hJ0]
  rw [← hJ0]
  have h1 : (2 * (impl.constructExpander.c_deg_int : ℝ)) * (wInp.prep.J0_strip.m : ℝ) /
      ((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) ≤
      (2 * (impl.constructExpander.c_deg_int : ℝ)) * (wInp.prep.J0_strip.m : ℝ) /
        impl.decompose.φ_lb wInp.prep.J0_strip.m :=
    div_le_div_of_nonneg_left (by positivity) (hJ0 ▸ hφ_pos) hφ_lb
  exact Nat.add_le_add_right (Nat.ceil_mono h1) 1

lemma task2_eta1Bound_le_cap {impl : SpannerToolImpl} {wInp : WitnessCoreInput} {WSubs : List Graph}
    {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤ (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    eta1Bound (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs) wInp.prep.J ≤
      Task2Input.eta1Cap impl wInp.prep.J := by
  dsimp only [eta1Bound, Task2Input.eta1Cap, WitnessCoreInput.mkWitnessData]
  have hJ0 := hs.2.2.1
  have hφ_pos : 0 < impl.decompose.φ_lb (stripLoops wInp.prep.J).m := impl.decompose.hφ_lb_pos _
  have hdiv : 2 * (impl.constructExpander.c_deg_int : ℝ) * (wInp.prep.J.m : ℝ) /
      (2 * ((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec)) ≤
      2 * (impl.constructExpander.c_deg_int : ℝ) * (wInp.prep.J.m : ℝ) /
        (2 * impl.decompose.φ_lb (stripLoops wInp.prep.J).m) := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    rw [hJ0] at hφ_lb
    linarith
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.log_mono_right (Nat.add_le_add_right (Nat.ceil_mono hdiv) 1)) 1)) 1

lemma task2_scalars_le_caps {impl : SpannerToolImpl} {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : wInp.prep.StaticValid mem w)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤ (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    let m0 := (stripLoops wInp.prep.J).m
    let pds := impl.pathDS.params
    let ce := impl.constructExpander
    let dJ := Task1Input.dJCap impl wInp.prep.J
    let mw := Task1Input.mwCap impl wInp.prep.J
    let dW := WitnessCoreInput.dWInt ce
    wInp.γExpInt ce pds ≤ Task2Input.gammaExpCap impl wInp.prep.J ∧
      wInp.γDelInt ce pds ≤ max (pds.gDel dJ m0) (pds.gDel dW mw) ∧
      wInp.phiDsDenInt ce pds ≤ max (pds.phiOutDen dJ m0) (pds.phiOutDen dW mw) := by
  intro m0 pds ce dJ mw dW
  have hpn := hs.2.2.2.2.2.2.2.2.1
  have hpnd := hs.2.2.2.2.2.2.2.2.2.1
  have hdJ_ge : 1 ≤ wInp.dJInt := by
    dsimp only [WitnessCoreInput.dJInt]
    exact Nat.div_pos (by omega) hpn
  have hdW_ge : 1 ≤ dW := by
    dsimp only [WitnessCoreInput.dWInt, dW]
    have h1 := ce.hphi_pos; have h2 := ce.hphi_le
    exact Nat.div_pos (by omega) h1
  have hdJ_le := task2_dJ_le_cap hs hφ_lb
  have hmw_le := task2_mw_le_cap hs hφ_lb
  have hm0_eq : wInp.prep.J0_strip.m = m0 := by rw [hs.2.2.1]
  refine ⟨max_le_max ?_ ?_, max_le_max ?_ ?_, max_le_max ?_ ?_⟩
  · rw [hm0_eq]; exact pds.hgExp_mono hdJ_ge hdJ_le le_rfl
  · exact pds.hgExp_mono hdW_ge le_rfl hmw_le
  · rw [hm0_eq]; exact pds.hgDel_mono hdJ_ge hdJ_le le_rfl
  · exact pds.hgDel_mono hdW_ge le_rfl hmw_le
  · rw [hm0_eq]; exact pds.hphiOutDen_mono hdJ_ge hdJ_le le_rfl
  · exact pds.hphiOutDen_mono hdW_ge le_rfl hmw_le

/-! ## Structural & lifting lemmas for `WitnessCoreInput.mkWitnessData` -/

lemma mkW_W_edges_j0 {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {eW : ℕ} (heW : eW < inp.prep.j0Edges.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    eW < wd.W.m ∧
      wd.W.edges.getD eW (0, 0) = inp.prep.J.edges.getD (wd.j0Edges.getD eW 0) (0, 0) ∧
      wd.wW eW = wd.φ_dec := by
  intro wd
  have heW' : eW < wd.j0Edges.length := heW
  have heW_m : eW < wd.W.m := by
    change eW < (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
      wd.comps.flatMap compWEdges).length
    rw [List.length_append, List.length_map]
    exact Nat.lt_of_lt_of_le heW' (Nat.le_add_right _ _)
  refine ⟨heW_m, ?_, ?_⟩
  · change (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).getD eW (0, 0) = _
    have hlt : eW < (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0))).length := by
      simpa using heW'
    have hlt_app : eW < (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length := by
      rw [List.length_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    rw [List.getD_eq_getElem _ _ hlt_app, List.getElem_append_left hlt, List.getElem_map,
      ← List.getD_eq_getElem wd.j0Edges 0 heW']
  · exact inp.mkWitnessData_wW_j0 heW

private lemma mkW_comp_flatMap_getD {offset : ℕ} (cs : List CompInfo) :
    CompsAligned offset cs →
    ∀ {ci eL : ℕ} (hci : ci < cs.length), eL < cs[ci].W_sub.m →
      let eW := cs[ci].wStart + eL
      offset ≤ eW ∧
      eW - offset < (cs.flatMap compWEdges).length ∧
      (cs.flatMap compWEdges).getD (eW - offset) (0, 0) =
        (compWEdges cs[ci]).getD eL (0, 0) := by
  intro hal
  induction cs generalizing offset with
  | nil => intro ci eL hci; simp at hci
  | cons c rest ih =>
    intro ci eL hci heL
    change c.wStart = offset ∧ CompsAligned (offset + c.W_sub.m) rest at hal
    rcases hal with ⟨hw, hrest⟩
    cases ci with
    | zero =>
      simp only [List.getElem_cons_zero] at heL ⊢
      have heW : c.wStart + eL - offset = eL := by omega
      have hcomp_len : (compWEdges c).length = c.W_sub.m := by simp [compWEdges, Graph.m]
      have hlt_fm : eL < (compWEdges c ++ rest.flatMap compWEdges).length := by
        rw [List.length_append, hcomp_len]; exact Nat.lt_of_lt_of_le heL (Nat.le_add_right _ _)
      refine ⟨by omega, by simpa [List.flatMap_cons, heW] using hlt_fm, ?_⟩
      simp only [List.flatMap_cons, heW]
      rw [List.getD_eq_getElem _ _ hlt_fm, List.getElem_append_left (by omega : eL < (compWEdges c).length),
        ← List.getD_eq_getElem (compWEdges c) (0, 0) (by omega : eL < (compWEdges c).length)]
    | succ ci' =>
      have hci' : ci' < rest.length := by simpa using hci
      have ih' := ih hrest (ci := ci') (eL := eL) hci' heL
      simp only [List.getElem_cons_succ] at ih' ⊢
      have hcomp_len : (compWEdges c).length = c.W_sub.m := by simp [compWEdges, Graph.m]
      have h_ge : offset + c.W_sub.m ≤ rest[ci'].wStart + eL := ih'.1
      have hsub : rest[ci'].wStart + eL - offset = c.W_sub.m + (rest[ci'].wStart + eL - (offset + c.W_sub.m)) := by
        omega
      refine ⟨by omega, ?_, ?_⟩
      · simpa [List.flatMap_cons, List.length_append, hcomp_len, hsub] using ih'.2.1
      · simp only [List.flatMap_cons, hsub]
        have hlt_all : c.W_sub.m + (rest[ci'].wStart + eL - (offset + c.W_sub.m)) <
            (compWEdges c ++ rest.flatMap compWEdges).length := by
          rw [List.length_append, hcomp_len]; exact Nat.add_lt_add_left ih'.2.1 _
        rw [List.getD_eq_getElem _ _ hlt_all, List.getElem_append_right (by omega : (compWEdges c).length ≤ _)]
        have heq_elem : (rest.flatMap compWEdges)[c.W_sub.m + (rest[ci'].wStart + eL - (offset + c.W_sub.m)) -
            (compWEdges c).length]'(by omega) =
            (rest.flatMap compWEdges)[rest[ci'].wStart + eL - (offset + c.W_sub.m)]'(ih'.2.1) := by
          congr 1; omega
        rw [heq_elem, ← List.getD_eq_getElem _ _ ih'.2.1]
        exact ih'.2.2

lemma mkW_W_edges_comp {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} (hws : inp.ValidWSubs ce WSubs)
    {ci eL : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    (heL : eL < (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.m) :
    let wd := inp.mkWitnessData ce pds WSubs
    have c := wd.comps[ci]
    have eW := c.wStart + eL
    eW < wd.W.m ∧
      wd.j0Edges.length ≤ eW ∧
      wd.W.edges.getD eW (0, 0) =
        (c.verts.getD (c.W_sub.edges.getD eL (0, 0)).1 0,
         c.verts.getD (c.W_sub.edges.getD eL (0, 0)).2 0) ∧
      wd.wW eW = wd.φ_dec * 2 ^ c.level := by
  intro wd c eW
  have hal : CompsAligned wd.j0Edges.length wd.comps :=
    inp.buildCompsFrom_aligned inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hfm := mkW_comp_flatMap_getD wd.comps hal hci heL
  have hj0_len : (wd.j0Edges.map fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)).length =
      wd.j0Edges.length := List.length_map _
  have heW_m : eW < wd.W.m := by
    change eW < (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
      wd.comps.flatMap compWEdges).length
    rw [List.length_append, hj0_len]
    dsimp only [eW, c, wd] at hfm ⊢
    omega
  refine ⟨heW_m, hfm.1, ?_, ?_⟩
  · change (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).getD eW (0, 0) = _
    have hge_j0 : wd.j0Edges.length ≤ eW := hfm.1
    have heW_len : eW < (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length := heW_m
    rw [List.getD_eq_getElem _ _ heW_len, List.getElem_append_right (by omega : _ ≤ eW),
      ← List.getD_eq_getElem _ _ (by rw [hj0_len]; exact hfm.2.1), hj0_len]
    dsimp only [eW, c, wd] at hfm ⊢
    rw [hfm.2.2]
    dsimp only [compWEdges]
    have hlt_e : eL < (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.edges.length := by
      simpa [Graph.m] using heL
    have hlt_m : eL < ((inp.mkWitnessData ce pds WSubs).comps[ci].W_sub.edges.map fun e =>
        ((inp.mkWitnessData ce pds WSubs).comps[ci].verts.getD e.1 0,
         (inp.mkWitnessData ce pds WSubs).comps[ci].verts.getD e.2 0)).length := by
      simpa using hlt_e
    rw [List.getD_eq_getElem _ _ hlt_m, List.getElem_map, ← List.getD_eq_getElem _ (0, 0) hlt_e]
  · have hww := inp.mkWitnessData_wW_comp hws hci heL
    dsimp only [wd, WitnessCoreInput.mkWitnessData, c, eW] at hww ⊢
    rw [hww]; push_cast; ring

private lemma mkW_edge_cases_aux (offset : ℕ) (cs : List CompInfo) (hal : CompsAligned offset cs) :
    ∀ {eW : ℕ}, offset ≤ eW → eW < offset + (cs.map fun c => c.W_sub.m).sum →
      ∃ ci, ∃ (_ : ci < cs.length), ∃ eL < cs[ci].W_sub.m, eW = cs[ci].wStart + eL := by
  induction cs generalizing offset with
  | nil => intro eW h1 h2; simp at h1 h2; omega
  | cons c rest ih =>
    intro eW h1 h2
    change c.wStart = offset ∧ CompsAligned (offset + c.W_sub.m) rest at hal
    rcases hal with ⟨hw, hrest⟩
    simp only [List.map_cons, List.sum_cons] at h2
    by_cases hlt : eW < offset + c.W_sub.m
    · exact ⟨0, by simp, eW - offset, by dsimp; omega, by dsimp [hw]; omega⟩
    · obtain ⟨ci, hci, eL, heL, heq⟩ := ih (offset + c.W_sub.m) hrest (eW := eW) (by omega) (by omega)
      exact ⟨ci + 1, by simpa using Nat.succ_lt_succ hci, eL, by simp; exact heL, by simp; exact heq⟩

lemma mkW_W_edge_cases {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} (hws : inp.ValidWSubs ce WSubs) {eW : ℕ}
    (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    let wd := inp.mkWitnessData ce pds WSubs
    eW < wd.j0Edges.length ∨
      ∃ ci, ∃ (_ : ci < wd.comps.length), ∃ eL < wd.comps[ci].W_sub.m, eW = wd.comps[ci].wStart + eL := by
  intro wd
  by_cases hlt : eW < wd.j0Edges.length
  · exact Or.inl hlt
  · right
    have hal : CompsAligned wd.j0Edges.length wd.comps :=
      inp.buildCompsFrom_aligned inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
    have hWm : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
      have hfm : ∀ cs : List CompInfo, (cs.flatMap compWEdges).length = (cs.map fun c => c.W_sub.m).sum := by
        intro cs; induction cs with
        | nil => simp
        | cons c rs ih => simp [List.flatMap_cons, compWEdges, Graph.m, ih]
      change (wd.j0Edges.map (fun jOrig => inp.prep.J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length = _
      rw [List.length_append, List.length_map, hfm]
    exact mkW_edge_cases_aux wd.j0Edges.length wd.comps hal (Nat.le_of_not_lt hlt) (hWm ▸ heW)

private lemma mkW_comp_eq {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {ci : ℕ}
    (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) :
    (inp.mkWitnessData ce pds WSubs).comps[ci] =
      (inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[ci]'(by
        simpa [WitnessCoreInput.mkWitnessData] using hci) := rfl

lemma mkW_c_verts_eq {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w) (hws : inp.ValidWSubs ce WSubs)
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) :
    (inp.mkWitnessData ce pds WSubs).comps[ci].verts =
      (inp.prep.rawComps[ci]'(by
        have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
        simpa [WitnessCoreInput.mkWitnessData, hlen] using hci)).2 := by
  have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_r : ci < inp.prep.rawComps.length := by simpa [WitnessCoreInput.mkWitnessData, hlen] using hci
  have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r
  have hmem := hs.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hci_r)
  rw [mkW_comp_eq hci, hgf.2.2.1]
  exact vertsOf_toFinset_of_pairwise_lt hmem.2.2.1

lemma mkW_comp_jOrig_edge {tools : LocalSpannerTools 0 0}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK tools inp.H' inp.prep.J inp.embJH (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let c := wd.comps[ci]
    ∀ b < c.J_sub.m,
      c.jSubOrigEdges.getD b 0 < inp.prep.J.m ∧
      inp.prep.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0) =
        (c.verts.getD (c.J_sub.edges.getD b (0, 0)).1 0,
         c.verts.getD (c.J_sub.edges.getD b (0, 0)).2 0) := by
  intro wd c b hb
  have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_r : ci < inp.prep.rawComps.length := by simpa [wd, WitnessCoreInput.mkWitnessData, hlen] using hci
  have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r
  set rc := inp.prep.rawComps[ci]'hci_r
  rcases hok.comp_props ci hci with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, _, hj_lt, _, _⟩
  rcases hgf with ⟨_, hX, _, hJsub, hjOrig, _⟩
  have hc_verts_eq : c.verts = vertsOf c.X := hok.comp_props ci hci |>.2.2.2.2.1
  have hc_jOrig_eq : c.jSubOrigEdges = inp.prep.cJOrig rc := hjOrig
  have hc_Jsub_eq : c.J_sub = inp.prep.cJSub rc := hJsub
  have hc_X_eq : c.X = rc.2.toFinset := hX
  have hjLen_c : c.jSubOrigEdges.length = c.J_sub.m := hjLen
  have hb_orig : b < c.jSubOrigEdges.length := by rw [hjLen_c]; exact hb
  have hj_lt_b : c.jSubOrigEdges.getD b 0 < inp.prep.J.m := by
    rw [List.getD_eq_getElem _ _ hb_orig]
    exact hj_lt _ (List.getElem_mem hb_orig)
  refine ⟨hj_lt_b, ?_⟩
  set G_i := DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp rc.1
  have hidx_len : b < (insideIndices G_i c.X).length := by
    rw [hc_X_eq]; simpa [hc_jOrig_eq, PrepInput.cJOrig] using hb_orig
  set a := (insideIndices G_i c.X).getD b 0
  have ha_in : a ∈ insideIndices G_i c.X := by
    dsimp only [a]; rw [List.getD_eq_getElem _ _ hidx_len]; exact List.getElem_mem hidx_len
  obtain ⟨ha_m, ha_1, ha_2⟩ := mem_insideIndices.mp ha_in
  have ha_ed : a < (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1).length := by
    simpa [G_i, DecomposeOutput.graphAt, Graph.m] using ha_m
  set b_nl := (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1).getD a 0
  have hbnl_mem : b_nl ∈ DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1 := by
    dsimp only [b_nl]; rw [List.getD_eq_getElem _ _ ha_ed]; exact List.getElem_mem ha_ed
  have hnl_eq : inp.prep.nlIdx = nonloopIndices inp.prep.J := hs.2.2.2.2.1
  have hJ0_eq : inp.prep.J0_strip = stripLoops inp.prep.J := hs.2.2.1
  have hbnl_st : b_nl < inp.prep.J0_strip.m := by
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hbnl_mem; exact hbnl_mem.1
  have hc_orig_def : c.jSubOrigEdges.getD b 0 = inp.prep.nlIdx.getD b_nl 0 := by
    rw [hc_jOrig_eq]; dsimp only [PrepInput.cJOrig]
    have hb_in : b < (insideIndices G_i rc.2.toFinset).length := by
      simpa [hc_X_eq] using hidx_len
    rw [List.getD_eq_getElem _ _ (by simp; exact hb_in), List.getElem_map,
      ← List.getD_eq_getElem (insideIndices G_i rc.2.toFinset) 0 hb_in]
    simp only [G_i, ← hc_X_eq]; rfl
  have hb_st_edge : inp.prep.J0_strip.edges.getD b_nl (0, 0) =
      inp.prep.J.edges.getD (inp.prep.nlIdx.getD b_nl 0) (0, 0) := by
    have hb_st : b_nl < (stripLoops inp.prep.J).m := by rwa [← hJ0_eq]
    have hbnl_nl : b_nl < (nonloopIndices inp.prep.J).length := by simpa [stripLoops, Graph.m] using hb_st
    have hlt_s : b_nl < ((nonloopIndices inp.prep.J).map fun j => inp.prep.J.edges.getD j (0, 0)).length :=
      hb_st
    rw [hJ0_eq, hnl_eq]; dsimp only [stripLoops]
    rw [List.getD_eq_getElem _ _ hlt_s, List.getElem_map,
      ← List.getD_eq_getElem (nonloopIndices inp.prep.J) 0 hbnl_nl]
  have hG_i_edge : G_i.edges.getD a (0, 0) = inp.prep.J.edges.getD (c.jSubOrigEdges.getD b 0) (0, 0) := by
    rw [hc_orig_def]; dsimp only [G_i, DecomposeOutput.graphAt]
    have hlt_map : a < ((DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1).map
        fun j => inp.prep.J0_strip.edges.getD j (0, 0)).length := by simpa using ha_ed
    rw [List.getD_eq_getElem _ _ hlt_map, List.getElem_map, ← List.getD_eq_getElem _ _ ha_ed]
    exact hb_st_edge
  have hJsub_edge : c.J_sub.edges.getD b (0, 0) =
      ((vertsOf c.X).idxOf (G_i.edges.getD a (0, 0)).1,
       (vertsOf c.X).idxOf (G_i.edges.getD a (0, 0)).2) := by
    rw [hc_Jsub_eq]; dsimp only [PrepInput.cJSub, inducedSubgraph]; rw [← hc_X_eq]
    have hlt_m : b < ((insideIndices G_i c.X).map fun e =>
        ((vertsOf c.X).idxOf (G_i.edges.getD e (0, 0)).1,
         (vertsOf c.X).idxOf (G_i.edges.getD e (0, 0)).2)).length := by simpa using hidx_len
    rw [List.getD_eq_getElem _ _ hlt_m, List.getElem_map, ← List.getD_eq_getElem _ _ hidx_len]
  rw [← hG_i_edge, hJsub_edge]
  have hidx1 : (vertsOf c.X).idxOf (G_i.edges.getD a (0, 0)).1 < (vertsOf c.X).length :=
    List.idxOf_lt_length_of_mem ((Finset.mem_sort _).mpr ha_1)
  have hidx2 : (vertsOf c.X).idxOf (G_i.edges.getD a (0, 0)).2 < (vertsOf c.X).length :=
    List.idxOf_lt_length_of_mem ((Finset.mem_sort _).mpr ha_2)
  rw [hc_verts_eq, List.getD_eq_getElem _ _ hidx1, List.getD_eq_getElem _ _ hidx2,
    List.getElem_idxOf hidx1, List.getElem_idxOf hidx2]

lemma mkW_isWalk_liftJSubWalk {tools : LocalSpannerTools 0 0}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK tools inp.H' inp.prep.J inp.embJH (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {ci u' v' : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    {P : Walk} (hP : P.IsWalk (inp.mkWitnessData ce pds WSubs).comps[ci].J_sub u' v') :
    let wd := inp.mkWitnessData ce pds WSubs
    let c := wd.comps[ci]
    (liftJSubWalk c P).IsWalk inp.prep.J (c.verts.getD u' 0) (c.verts.getD v' 0) := by
  intro wd c
  have hsub_props := hok.comp_props ci hci
  have hc_verts_eq : c.verts = vertsOf c.X := hsub_props.2.2.2.2.1
  have hc_Jn : c.J_sub.n = c.X.card := hsub_props.2.2.2.2.2.1
  have hc_vlen : c.verts.length = c.J_sub.n := by rw [hc_verts_eq, vertsOf, Finset.length_sort, hc_Jn]
  have hv_lt_J : ∀ k < c.verts.length, c.verts.getD k 0 < inp.prep.J.n := fun k hk => by
    have hk' : k < (vertsOf c.X).length := hc_verts_eq ▸ hk
    have hmem : c.verts.getD k 0 ∈ c.X := by
      rw [List.getD_eq_getElem _ _ hk]
      have hge : c.verts[k]'hk = (vertsOf c.X)[k]'hk' := by simp [hc_verts_eq]
      rw [hge]
      exact (Finset.mem_sort _).mp (List.getElem_mem hk')
    exact Finset.mem_range.mp (hsub_props.2.2.1 hmem)
  have hf := mkW_comp_jOrig_edge hs hok hws hci
  rcases hP with ⟨hu', hv', ⟨hPv, hPe, rfl⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · have huv := hv_lt_J u' (hc_vlen.symm ▸ hu')
    exact ⟨huv, huv, Or.inl ⟨by simp [liftJSubWalk, hPv], by simp [liftJSubWalk, hPe], rfl⟩⟩
  · have hu_c : u' < c.verts.length := hc_vlen.symm ▸ hu'
    have hv_c : v' < c.verts.length := hc_vlen.symm ▸ hv'
    refine ⟨hv_lt_J u' hu_c, hv_lt_J v' hv_c, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [liftJSubWalk] using hne
    · simpa [liftJSubWalk] using hlen
    · cases hPv' : P.verts with
      | nil => simp [hPv'] at hhead
      | cons pu pt =>
        simp only [liftJSubWalk, hPv', List.map_cons, List.head?_cons]
        simp only [hPv', List.head?_cons, Option.some.injEq] at hhead
        rw [hhead, List.getD_eq_getElem _ _ hu_c]
    · rw [liftJSubWalk]; simp only [List.getLast?_map]
      rw [hlast]; simp only [Option.map_some, List.getD_eq_getElem _ _ hv_c]
    · intro j hj
      simp only [liftJSubWalk, List.mem_map] at hj
      rcases hj with ⟨b, hb, rfl⟩
      exact (hf b (hedges b hb)).1
    · intro i hi
      simp only [liftJSubWalk, List.length_map] at hi ⊢
      have hb_m : P.edges.getD i 0 < c.J_sub.m := by
        rw [List.getD_eq_getElem _ _ hi]; exact hedges _ (List.getElem_mem hi)
      have hmap_e : (P.edges.map fun b => c.jSubOrigEdges.getD b 0).getD i 0 =
          c.jSubOrigEdges.getD (P.edges.getD i 0) 0 := by
        have hm : i < (P.edges.map fun b => c.jSubOrigEdges.getD b 0).length := by simpa using hi
        rw [List.getD_eq_getElem _ _ hm, List.getElem_map, ← List.getD_eq_getElem P.edges 0 hi]
      have hmap_v1 : (P.verts.map fun k => c.verts.getD k 0).getD i 0 =
          c.verts.getD (P.verts.getD i 0) 0 := by
        have hm1 : i < (P.verts.map fun k => c.verts.getD k 0).length := by rw [List.length_map]; omega
        rw [List.getD_eq_getElem _ _ hm1, List.getElem_map,
          ← List.getD_eq_getElem P.verts 0 (by omega : i < P.verts.length)]
      have hmap_v2 : (P.verts.map fun k => c.verts.getD k 0).getD (i + 1) 0 =
          c.verts.getD (P.verts.getD (i + 1) 0) 0 := by
        have hm2 : i + 1 < (P.verts.map fun k => c.verts.getD k 0).length := by rw [List.length_map]; omega
        rw [List.getD_eq_getElem _ _ hm2, List.getElem_map,
          ← List.getD_eq_getElem P.verts 0 (by omega : i + 1 < P.verts.length)]
      rw [hmap_e, (hf _ hb_m).2, hmap_v1, hmap_v2]
      rcases hstep i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg (fun k => c.verts.getD k 0) h1, congrArg (fun k => c.verts.getD k 0) h2⟩
      · exact Or.inr ⟨congrArg (fun k => c.verts.getD k 0) h1, congrArg (fun k => c.verts.getD k 0) h2⟩

/-! ## Non-loop walk composition & vertex membership -/

lemma mkW_j0_nonloop {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w) {eW : ℕ} (heW : eW < inp.prep.j0Edges.length) :
    let eJ := inp.prep.j0Edges.getD eW 0
    eJ < inp.prep.J.m ∧
      (inp.prep.J.edges.getD eJ (0, 0)).1 ≠ (inp.prep.J.edges.getD eJ (0, 0)).2 := by
  have heJ_mem : inp.prep.j0Edges.getD eW 0 ∈ inp.prep.j0Edges := by
    rw [List.getD_eq_getElem _ _ heW]; exact List.getElem_mem heW
  have hnl : inp.prep.j0Edges.getD eW 0 ∈ nonloopIndices inp.prep.J := by
    have hnl_eq := hs.2.2.2.2.1
    have hJ0_eq := hs.2.2.1
    dsimp only [PrepInput.j0Edges] at heJ_mem
    rw [List.mem_map] at heJ_mem
    rcases heJ_mem with ⟨a, ha, ha_eq⟩
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at ha
    have hlen : inp.prep.J0_strip.m = inp.prep.nlIdx.length := by
      rw [hJ0_eq, hnl_eq]; simp [stripLoops, Graph.m]
    have hm : a < inp.prep.nlIdx.length := by omega
    dsimp only [PrepInput.j0Edges]
    rw [← ha_eq, ← hnl_eq, List.getD_eq_getElem _ _ hm]
    exact List.getElem_mem hm
  exact mem_nonloopIndices.mp hnl

lemma mkW_comp_jOrig_nonloop {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w) (hws : inp.ValidWSubs ce WSubs)
    {ci b : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    (hb : b < (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.length) :
    let eJ := (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD b 0
    eJ < inp.prep.J.m ∧
      (inp.prep.J.edges.getD eJ (0, 0)).1 ≠ (inp.prep.J.edges.getD eJ (0, 0)).2 := by
  have hlen := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_r : ci < inp.prep.rawComps.length := by simpa [WitnessCoreInput.mkWitnessData, hlen] using hci
  have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r
  have heJ_mem : (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD b 0 ∈
      (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges := by
    rw [List.getD_eq_getElem _ _ hb]; exact List.getElem_mem hb
  rw [mkW_comp_eq hci, hgf.2.2.2.2.1] at heJ_mem
  dsimp only [PrepInput.cJOrig] at heJ_mem
  rw [List.mem_map] at heJ_mem
  rcases heJ_mem with ⟨a, ha, ha_eq⟩
  obtain ⟨ha_m, _, _⟩ := mem_insideIndices.mp ha
  have ha_ed : a < (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp (inp.prep.rawComps[ci]'hci_r).1).length := by
    simpa [DecomposeOutput.graphAt, Graph.m] using ha_m
  set b_nl := (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp (inp.prep.rawComps[ci]'hci_r).1).getD a 0
  have hbnl_mem : b_nl ∈ DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp (inp.prep.rawComps[ci]'hci_r).1 := by
    dsimp only [b_nl]; rw [List.getD_eq_getElem _ _ ha_ed]; exact List.getElem_mem ha_ed
  simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hbnl_mem
  have hnl_eq : inp.prep.nlIdx = nonloopIndices inp.prep.J := hs.2.2.2.2.1
  have hJ0_eq : inp.prep.J0_strip = stripLoops inp.prep.J := hs.2.2.1
  have hbnl_lt : b_nl < inp.prep.nlIdx.length := by
    rw [hnl_eq]; have h1 := hbnl_mem.1; rw [hJ0_eq] at h1
    simpa [stripLoops, Graph.m] using h1
  have heJ_nl : inp.prep.nlIdx.getD b_nl 0 ∈ nonloopIndices inp.prep.J := by
    rw [List.getD_eq_getElem _ _ hbnl_lt, ← hnl_eq]; exact List.getElem_mem hbnl_lt
  have hgoal : (inp.mkWitnessData ce pds WSubs).comps[ci].jSubOrigEdges.getD b 0 = inp.prep.nlIdx.getD b_nl 0 := by
    rw [mkW_comp_eq hci, hgf.2.2.2.2.1]; dsimp only [PrepInput.cJOrig]; exact ha_eq.symm
  dsimp only []
  rw [hgoal]
  exact mem_nonloopIndices.mp heJ_nl

lemma isWalk_nonloop_edges_ne {J H' : Graph} {embJH : ℕ → Walk}
    (hembJH : IsEmbedding J H' embJH) {eJ : ℕ} (heJ : eJ < J.m)
    (hne : (J.edges.getD eJ (0, 0)).1 ≠ (J.edges.getD eJ (0, 0)).2) :
    (embJH eJ).edges ≠ [] := by
  intro hempty
  have hw := hembJH.2 eJ heJ
  rcases hw.2.2 with ⟨_, _, huv⟩ | ⟨h, _⟩
  · rw [List.getD_eq_getElem _ _ heJ] at hne; exact hne huv
  · exact h hempty

lemma compose_nonloop_mem_verts_iff {J H' : Graph} {embJH : ℕ → Walk}
    (hembJH : IsEmbedding J H' embJH) :
    ∀ (vs js : List ℕ) {u v : ℕ},
      vs.length = js.length + 1 →
      (∀ e' ∈ js, e' < J.m ∧ (J.edges.getD e' (0, 0)).1 ≠ (J.edges.getD e' (0, 0)).2) →
      (∀ i < js.length, Walk.EdgeMatches (J.edges.getD (js.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      vs.head? = some u → vs.getLast? = some v → v < J.n →
      ∀ x, x ∈ (composeAux J embJH vs js).verts ↔ ∃ e' ∈ js, x ∈ (embJH e').verts := by
  intro vs js
  induction js generalizing vs with
  | nil =>
    intro u v hlen _ _ _ _ _ x
    cases vs with
    | nil => simp at hlen
    | cons a vs' => cases vs' with
      | nil => simp [composeAux, Walk.empty]
      | cons _ _ => simp at hlen
  | cons j js ih =>
    intro u v hlen hjs hstep hhead hlast hv x
    cases vs with
    | nil => simp at hlen
    | cons a vs' => cases vs' with
      | nil => simp at hlen
      | cons b vs'' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        have hj := hjs j List.mem_cons_self
        have hstep0 := hstep 0 (by simp)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at hstep0
        rw [← List.getD_eq_getElem?_getD] at hstep0
        have hJe : J.edges.getD j (0, 0) = J.edges[j]'hj.1 := List.getD_eq_getElem _ _ hj.1
        have hw_j := hembJH.2 j hj.1
        set step := if (J.edges.getD j (0, 0)).1 = u ∧ (J.edges.getD j (0, 0)).2 = b then
          embJH j else (embJH j).reverse
        have hstep_walk : step.IsWalk H' u b := by
          dsimp only [step]
          rw [hJe] at hstep0 ⊢
          rcases hstep0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [h1, h2, and_self, ↓reduceIte]; simpa [h1, h2] using hw_j
          · split_ifs with hc
            · rw [hc.1, hc.2] at hw_j; exact hw_j
            · rw [← h1, ← h2]; exact Walk.isWalk_reverse hw_j
        have hstep_verts : ∀ y, y ∈ step.verts ↔ y ∈ (embJH j).verts := by
          intro y; dsimp only [step]; split_ifs <;> simp [Walk.reverse]
        have hlast' : (b :: vs'').getLast? = some v := by simpa [List.getLast?_cons_cons] using hlast
        have hstep' : ∀ i < js.length, Walk.EdgeMatches (J.edges.getD (js.getD i 0) (0, 0))
            ((b :: vs'').getD i 0) ((b :: vs'').getD (i + 1) 0) := fun i hi => by
          simpa [List.getD_eq_getElem?_getD] using hstep (i + 1) (by simpa using Nat.succ_lt_succ hi)
        have hjs' := fun e' he' => hjs e' (List.mem_cons_of_mem j he')
        have ih_verts := ih (b :: vs'') (by simpa using hlen) hjs' hstep' rfl hlast' hv
        have htail_walk : (composeAux J embJH (b :: vs'') js).IsWalk H' b v :=
          composeAux_isWalk hembJH js (b :: vs'') b v (by simpa using hlen) rfl hlast'
            (fun e' he' => (hjs' e' he').1) hstep' hv
        change x ∈ (step.append (composeAux J embJH (b :: vs'') js)).verts ↔ _
        rw [Walk.mem_verts_append_iff hstep_walk htail_walk x, hstep_verts x, ih_verts x]
        simp [List.mem_cons]

end MinCostFlow.Spanner
