module

public import MinCostFlow.Spanner.Task2Invs

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Task 2 Base: Inner Loop and Middle Step

Proves `task2InnerLoop_spec`, `nonloop_edge_witness_bounds`, `findReadyWEdge_spec`,
and `task2MiddleStep_inv` for Task 2 of Algorithm 4.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

theorem task2InnerLoop_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task2State tools.pathDS.State}
    (hinv : Task2CoreInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s)
    (hrel : Task2RoundRel tools.pathDS (buildWitness tools H' J embJH) s_prev s) :
    let wd := buildWitness tools H' J embJH
    let s_out := whileFuel H'.n (task2InnerCond H' J embJH wd)
      (task2InnerStep tools.pathDS H' J embJH wd) s
    Task2LoopInv tools.pathDS H' J embJH wd s_out ∧
    Task2RoundRel tools.pathDS wd s_prev s_out ∧
    s_out.embWJ = s.embWJ ∧
    s_out.getPathCountJ = s.getPathCountJ ∧
    s_out.middleIters1 = s.middleIters1 ∧
    s_out.vcongUpdates = s.vcongUpdates ∧
    s_out.initCountJ = s.initCountJ ∧
    s_out.initEdgesJ = s.initEdgesJ := by
  intro wd s_out
  let P : Task2State tools.pathDS.State → Prop := fun st =>
    Task2CoreInv tools.pathDS H' J embJH wd st ∧
    Task2RoundRel tools.pathDS wd s_prev st ∧
    st.embWJ = s.embWJ ∧
    st.getPathCountJ = s.getPathCountJ ∧
    st.middleIters1 = s.middleIters1 ∧
    st.vcongUpdates = s.vcongUpdates ∧
    st.initCountJ = s.initCountJ ∧
    st.initEdgesJ = s.initEdgesJ
  let meas : Task2State tools.pathDS.State → ℕ :=
    fun st => H'.n - (st.processedVerts ∩ Finset.range H'.n).card
  have hstep : ∀ st, P st → task2InnerCond H' J embJH wd st = true →
      P (task2InnerStep tools.pathDS H' J embJH wd st) ∧
        meas (task2InnerStep tools.pathDS H' J embJH wd st) < meas st := by
    intro st ⟨hst_inv, hst_rel, hrest⟩ hc
    obtain ⟨h1, h2, h3⟩ := task2InnerStep_inv tools H' J embJH hw hst_inv hst_rel hc
    refine ⟨⟨h1, h2, ?_⟩, h3⟩
    unfold task2InnerCond at hc
    cases hf : findCongestedVertex H' J embJH wd st with
    | none => rw [hf] at hc; simp at hc
    | some x => simpa [task2InnerStep, hf] using hrest
  have hinv_out : P s_out :=
    whileFuel_inv P (task2InnerCond H' J embJH wd)
      (task2InnerStep tools.pathDS H' J embJH wd) (fun st h c => (hstep st h c).1) H'.n s
      ⟨hinv, hrel, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdone : task2InnerCond H' J embJH wd s_out = false :=
    whileFuel_done P meas (task2InnerCond H' J embJH wd)
      (task2InnerStep tools.pathDS H' J embJH wd) hstep H'.n s
      ⟨hinv, hrel, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.sub_le _ _)
  have hinactive : ∀ x < H'.n, x ∉ s_out.processedVerts →
      vcongAt wd.W wd.wW (compose J embJH (partialToWalk s_out.embWJ)) x ≤ (s_out.η₁ : ℝ) * wd.τ₁ := by
    intro x hx hnotin
    unfold task2InnerCond at hdone
    rw [Bool.eq_false_iff, ne_eq, Option.isSome_iff_exists] at hdone
    have hnone : findCongestedVertex H' J embJH wd s_out = none := by
      cases hf : findCongestedVertex H' J embJH wd s_out with
      | none => rfl
      | some a => exact False.elim (hdone ⟨a, hf⟩)
    unfold findCongestedVertex at hnone
    have hfalse := find?_none_iff.mp hnone x (List.mem_range.mpr hx)
    simp only [decide_eq_false_iff_not, not_and, not_le] at hfalse
    exact (hfalse hnotin).le
  exact ⟨⟨hinv_out.1, hinactive⟩, hinv_out.2⟩

/-! ## Middle loop (`task2MiddleStep` and `task2MiddleLoop`) -/

theorem nonloop_edge_witness_bounds {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length) :
    1 ≤ maxDeg J ∧ 1 ≤ length J embJH := by
  set wd := buildWitness tools H' J embJH
  set c := wd.comps[ci]'hci
  rcases hw.comp_props ci hci with ⟨_, _, _, _, _, _, _, hJm_pos, _, _, _, _, _, _, _, _, _, _, _, hjLen, _, _, _, _⟩
  have hj0_len : 0 < c.jSubOrigEdges.length := by rw [hjLen]; exact hJm_pos
  set eJ := c.jSubOrigEdges[0]'hj0_len
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  obtain ⟨_, _, _, hjOrig_eq, _⟩ :=
    buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
      (List.getElem_mem hci)
  have heJ_mem : eJ ∈ c.jSubOrigEdges := List.getElem_mem hj0_len
  rw [hjOrig_eq, List.mem_map] at heJ_mem
  rcases heJ_mem with ⟨a, ha, ha_eq⟩
  have ha_m : a < (wd.decomp.graphAt wd.J0_strip c.level).m := (mem_insideIndices.mp ha).1
  have ha_ed : a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
    simpa [DecomposeOutput.graphAt, Graph.m] using ha_m
  set b := (wd.decomp.edgesAt wd.J0_strip c.level).getD a 0
  have hb_mem : b ∈ wd.decomp.edgesAt wd.J0_strip c.level := by
    dsimp only [b]; rw [List.getD_eq_getElem _ _ ha_ed]; exact List.getElem_mem ha_ed
  simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
  have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
    simp [wd, buildWitness, stripLoops, Graph.m]
  have hb_nl : b < wd.nlIdx.length := by omega
  have heJ_nl : eJ ∈ wd.nlIdx := by
    rw [← ha_eq, List.getD_eq_getElem _ _ hb_nl]
    exact List.getElem_mem hb_nl
  obtain ⟨heJ_m, hne_loop⟩ := mem_nonloopIndices.mp heJ_nl
  have hJedge : J.edges.getD eJ (0, 0) = J.edges[eJ]'(by simpa [Graph.m] using heJ_m) :=
    List.getD_eq_getElem _ _ (by simpa [Graph.m] using heJ_m)
  rw [hJedge] at hne_loop
  have hmaxDeg : 1 ≤ maxDeg J := by
    have he_mem : J.edges[eJ]'(by simpa [Graph.m] using heJ_m) ∈ J.edges := List.getElem_mem _
    set v1 := (J.edges[eJ]'(by simpa [Graph.m] using heJ_m)).1
    have hv1 : v1 < J.n := (hJ _ he_mem).1
    have hdeg1 : 1 ≤ J.deg v1 := by
      rw [deg_eq_filter_edges hJ]
      have hpos : 0 < (J.edges.filter fun x => decide (x.1 = v1)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨_, List.mem_filter.mpr ⟨he_mem, decide_eq_true rfl⟩⟩
      omega
    exact le_trans hdeg1 (deg_le_maxDeg hv1)
  have hlen : 1 ≤ length J embJH := by
    have hw_j := hembJH.2 eJ heJ_m
    have hne_edges : (embJH eJ).edges ≠ [] := by
      intro hempty
      rcases hw_j.2.2 with ⟨_, _, huv⟩ | ⟨hne, _⟩
      · exact hne_loop huv
      · exact hne hempty
    have hpos : 1 ≤ (embJH eJ).edges.length := List.length_pos_iff_ne_nil.mpr hne_edges
    exact le_trans hpos (edges_length_le_length embJH heJ_m)
  exact ⟨hmaxDeg, hlen⟩

theorem findReadyWEdge_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (_hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s : Task2State tools.pathDS.State}
    (hj0 : ∀ eW < (buildWitness tools H' J embJH).j0Edges.length, (s.embWJ eW).isSome = true)
    {eW ci eLocal : ℕ}
    (hfind : findReadyWEdge tools.pathDS (buildWitness tools H' J embJH) s = some (eW, ci, eLocal)) :
    let wd := buildWitness tools H' J embJH
    eW < wd.W.m ∧ s.embWJ eW = none ∧
    ∃ (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      eLocal < c.W_sub.m ∧ eW = c.wStart + eLocal ∧
      wd.wSources.getD eW (WEdgeSource.fromJ0 0) = WEdgeSource.fromComp ci eLocal ∧
      (c.W_sub.edges.getD eLocal (0, 0)).1 ∉ tools.pathDS.Vhat (s.dsJ.getD ci (tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩)) ∧
      (c.W_sub.edges.getD eLocal (0, 0)).2 ∉ tools.pathDS.Vhat (s.dsJ.getD ci (tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩)) := by
  intro wd
  unfold findReadyWEdge at hfind
  have hmem := head?_some_mem hfind
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨eW', heW'_range, hres⟩
  have heW'_m : eW' < wd.W.m := List.mem_range.mp heW'_range
  dsimp only at hres
  split_ifs at hres with hisNone
  · have hnone' : s.embWJ eW' = none := Option.isNone_iff_eq_none.mp hisNone
    have hge_j0 : wd.j0Edges.length ≤ eW' := by
      by_contra hlt
      have hsome := hj0 eW' (Nat.lt_of_not_ge hlt)
      rw [hnone'] at hsome
      simp at hsome
    rcases W_edge_cases tools H' J embJH heW'_m with hlt0 | ⟨ci', hci', eL', heL', rfl⟩
    · exact absurd hlt0 (Nat.not_lt_of_ge hge_j0)
    · have hspec := W_edges_getD_comp tools H' J embJH hci' heL'
      rw [hspec.2.2.2.1] at hres
      dsimp only at hres
      split_ifs at hres with hnot
      simp only [Option.some.injEq, Prod.mk.injEq] at hres
      rcases hres with ⟨rfl, rfl, rfl⟩
      refine ⟨hspec.1, hnone', hci', heL', rfl, hspec.2.2.2.1, ?_⟩
      have hc_eq : (buildWitness tools H' J embJH).comps.getD ci' defaultCompInfo =
          wd.comps[ci']'hci' := List.getD_eq_getElem _ _ hci'
      rw [hc_eq] at hnot
      exact hnot

theorem task2MiddleStep_inv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s_prev s : Task2State tools.pathDS.State}
    (hinv : Task2LoopInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s)
    (hrel : Task2RoundRel tools.pathDS (buildWitness tools H' J embJH) s_prev s)
    (hcond : task2MiddleCond tools.pathDS (buildWitness tools H' J embJH) s = true) :
    let wd := buildWitness tools H' J embJH
    let s' := task2MiddleStep tools.pathDS H' J embJH wd s
    Task2LoopInv tools.pathDS H' J embJH wd s' ∧
    Task2RoundRel tools.pathDS wd s_prev s' ∧
    unembeddedCount1 wd s' < unembeddedCount1 wd s := by
  intro wd s'
  unfold task2MiddleCond at hcond
  cases hf : findReadyWEdge tools.pathDS wd s with
  | none => rw [hf] at hcond; simp at hcond
  | some p =>
    rcases p with ⟨eW, ci, eLocal⟩
    obtain ⟨heW_m, hnone, hci, heL_m, heW_eq, _, hnot1, hnot2⟩ :=
      findReadyWEdge_spec tools H' J embJH hw hinv.j0_embedded hf
    set c := wd.comps[ci]'hci
    set dsDef := tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
    set ds := s.dsJ.getD ci dsDef
    have hci_ds : ci < s.dsJ.length := by rw [hinv.ds_len]; exact hci
    have hds_eq : ds = s.dsJ[ci]'hci_ds := List.getD_eq_getElem _ _ hci_ds
    have hc_getD : wd.comps.getD ci defaultCompInfo = c := List.getD_eq_getElem _ _ hci
    set eLoc := c.W_sub.edges.getD eLocal (0, 0)
    set P_sub := tools.pathDS.getPath ds eLoc.1 eLoc.2
    set P_J := liftJSubWalk c P_sub
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hc_Jn, hc_Jvalid, hc_Jm_pos, hc_Jm_le, hc_Jdeg, hc_Jexp,
       hc_Wn, hc_Wvalid, _, _, _, _, _, _, _, _, _, _, _⟩
    have heLoc_mem : eLoc ∈ c.W_sub.edges := by
      dsimp only [eLoc]; rw [List.getD_eq_getElem _ _ heL_m]; exact List.getElem_mem heL_m
    have heLoc_lt := hc_Wvalid eLoc heLoc_mem
    have heLoc1_J : eLoc.1 ∈ c.J_sub.verts := by
      rw [Graph.verts, hc_Jn, ← hc_Wn]; exact Finset.mem_range.mpr heLoc_lt.1
    have heLoc2_J : eLoc.2 ∈ c.J_sub.verts := by
      rw [Graph.verts, hc_Jn, ← hc_Wn]; exact Finset.mem_range.mpr heLoc_lt.2
    have hnot1' : eLoc.1 ∉ tools.pathDS.Vhat (s.dsJ[ci]'hci_ds) := by rw [← hds_eq]; exact hnot1
    have hnot2' : eLoc.2 ∉ tools.pathDS.Vhat (s.dsJ[ci]'hci_ds) := by rw [← hds_eq]; exact hnot2
    have hgp := tools.pathDS.getPath_spec wd.φ_dec wd.J0_strip.m c.J_sub
      (s.dsJ[ci]'hci_ds) eLoc.1 eLoc.2 hw.φ_dec_pos hw.φ_dec_le hc_Jvalid hc_Jm_pos hc_Jm_le
      (fun v hv => hc_Jdeg v (hc_Jn ▸ hv))
      hc_Jexp (hinv.ds_inv ci hci)
      (Finset.mem_sdiff.mpr ⟨heLoc1_J, hnot1'⟩) (Finset.mem_sdiff.mpr ⟨heLoc2_J, hnot2'⟩)
    rw [← hds_eq] at hgp
    rcases hgp with ⟨hPsub_walk, _, hPsub_notdel, _, hPsub_len⟩
    have hWe_len : eW < wd.W.edges.length := heW_m
    have hPJ_walk : P_J.IsWalk J (wd.W.edges[eW]'hWe_len).1
        (wd.W.edges[eW]'hWe_len).2 := by
      have hLift := isWalk_liftJSubWalk tools H' J embJH hw hci hPsub_walk
      have hWe := (W_edges_getD_comp tools H' J embJH hci heL_m).2.2.1
      rw [← heW_eq] at hWe
      have hWe' : wd.W.edges[eW]'hWe_len = (c.verts.getD eLoc.1 0, c.verts.getD eLoc.2 0) := by
        rw [← List.getD_eq_getElem _ _ hWe_len]
        exact hWe
      rw [hWe']
      exact hLift
    have hP_len_le : (P_J.edges.length : ℝ) ≤ wd.γ_ExpPath := by
      rw [liftJSubWalk_edges_length]
      exact le_trans hPsub_len (le_max_left _ _)
    have ⟨hmaxDeg, hlenJH⟩ := nonloop_edge_witness_bounds tools H' J embJH hJ hembJH hw hci
    have hwW_le_half : wd.wW eW ≤ wd.τ₁ / 2 := by
      have hwW_le_deg := wW_le_maxDeg tools H' J embJH hJ hw heW_m
      have hγE : 2 ≤ wd.γ_ExpPath := by
        have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
          rw [le_div_iff₀ hw.φ_ds_pos]
          nlinarith [hw.φ_ds_half]
        exact le_trans h1 hw.γ_ExpPath_ge
      have hlen_r : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hlenJH
      have hφ_inv : (2 : ℝ) ≤ 1 / wd.φ_ds := by
        rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
      have hvcong_nn : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
      have hτ₁_half : wd.τ₁ / 2 =
          wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by
        change (2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
          (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) / 2 = _
        ring
      have hmul_ge : (maxDeg J : ℝ) ≤
          wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by
        have h1 : (maxDeg J : ℝ) ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by linarith
        have h2 : (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) * (1 / wd.φ_ds) ≥
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := by
          have hnn : 0 ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) := by positivity
          nlinarith
        have h_prod : 1 ≤ wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del := by
          have h3 : 1 ≤ wd.γ_del := hw.γ_del_ge
          have h12 : 2 ≤ wd.γ_ExpPath * (length J embJH : ℝ) := by nlinarith
          nlinarith
        have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
        have h3 : 0 ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by positivity
        calc (maxDeg J : ℝ)
            ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) := h1
          _ ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) * (1 / wd.φ_ds) := h2
          _ = (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by ring
          _ ≤ (wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del) *
                ((vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) := by
              nlinarith
          _ = wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
                (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by ring
      rw [hτ₁_half]
      exact le_trans hwW_le_deg hmul_ge
    let updVerts := (P_J.edges.map fun e' => (embJH e').verts.length).sum
    let s1 : Task2State tools.pathDS.State :=
      { s with
        embWJ := Function.update s.embWJ eW (some P_J)
        getPathCountJ := s.getPathCountJ + 1
        vcongUpdates := s.vcongUpdates + updVerts
        middleIters1 := s.middleIters1 + 1 }
    have hs'_eq : s' = whileFuel H'.n (task2InnerCond H' J embJH wd)
        (task2InnerStep tools.pathDS H' J embJH wd) s1 := by
      simp only [s', task2MiddleStep, hf]
      congr 1
      simp only [s1, P_J, P_sub, eLoc, updVerts]
      rw [hc_getD]
    have hnot_in_comp : ∀ x ∈ s.processedVerts,
        x ∉ (composeAux J embJH P_J.verts P_J.edges).verts := by
      intro x hx hmem_v
      obtain ⟨eJ, heJ_mem, hx_eJ⟩ := mem_verts_composeAux P_J.verts P_J.edges hmem_v
      rw [mem_edges_liftJSubWalk] at heJ_mem
      rcases heJ_mem with ⟨b, hb_edges, rfl⟩
      have hb_m : b < c.J_sub.m := hPsub_walk.2.2.elim
        (fun h => by dsimp only [P_sub] at hb_edges; rw [h.2.1] at hb_edges; simp at hb_edges)
        (fun h => h.2.2.2.2.1 b hb_edges)
      have hb_del := hinv.processed_deleted x hx ci hci b hb_m hx_eJ
      rw [← hds_eq] at hb_del
      exact hPsub_notdel b hb_edges hb_del
    have hcore1 : Task2CoreInv tools.pathDS H' J embJH wd s1 :=
      { ds_len := hinv.ds_len
        ds_inv := hinv.ds_inv
        Vhat_sub := hinv.Vhat_sub
        Vhat_vol := hinv.Vhat_vol
        partial_emb := by
          refine ⟨hinv.partial_emb.1, fun j hj Q hQ => ?_⟩
          dsimp only [s1] at hQ
          by_cases hj_eq : j = eW
          · subst hj_eq
            rw [Function.update_self] at hQ
            simp only [Option.some.injEq] at hQ
            subst hQ
            exact hPJ_walk
          · rw [Function.update_of_ne hj_eq] at hQ
            exact hinv.partial_emb.2 j hj Q hQ
        j0_embedded := by
          intro e0 he0
          by_cases h0 : e0 = eW
          · subst h0; simp [s1, Function.update_self]
          · simp [s1, Function.update_of_ne h0, hinv.j0_embedded e0 he0]
        emb_len := by
          intro e0 he0
          by_cases h0 : e0 = eW
          · subst h0
            simp only [s1, partialToWalk, Function.update_self, Option.getD_some]
            exact hP_len_le
          · simp only [s1, partialToWalk, Function.update_of_ne h0]
            exact hinv.emb_len e0 he0
        vcong_half := by
          intro x hx
          by_cases hx_proc : x ∈ s.processedVerts
          · have hnot := hnot_in_comp x hx_proc
            have hveq := vcongAt_update_none wd.W H' J wd.wW embJH s.embWJ heW_m hnone P_J x
            simp only [hnot, ↓reduceIte, add_zero] at hveq
            simpa [s1, hveq] using hinv.vcong_half x hx
          · have hinact := hinv.inactive_uncongested x hx hx_proc
            have hvle := vcongAt_update_none_le wd.W H' J wd.wW embJH s.embWJ heW_m hnone
              (wW_pos tools H' J embJH hw heW_m).le P_J x
            have hadd : (s.η₁ : ℝ) * wd.τ₁ + wd.τ₁ / 2 = (s.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by ring
            have hle : vcongAt wd.W wd.wW (compose J embJH (partialToWalk s1.embWJ)) x ≤
                (s.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by
              calc vcongAt wd.W wd.wW (compose J embJH (partialToWalk s1.embWJ)) x
                  ≤ vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x + wd.wW eW := hvle
                _ ≤ (s.η₁ : ℝ) * wd.τ₁ + wd.τ₁ / 2 := add_le_add hinact hwW_le_half
                _ = (s.η₁ + 1 / 2 : ℝ) * wd.τ₁ := hadd
            exact hle
        processed_sub := by
          intro x hx
          have hnot := hnot_in_comp x hx
          have hveq := vcongAt_update_none wd.W H' J wd.wW embJH s.embWJ heW_m hnone P_J x
          simp only [hnot, ↓reduceIte, add_zero] at hveq
          simpa [s1, hveq] using hinv.processed_sub x hx
        processed_deleted := hinv.processed_deleted
        deleted_sub_processed := hinv.deleted_sub_processed
        initCount_eq := hinv.initCount_eq
        initEdges_eq := hinv.initEdges_eq
        middle_eq := by simp [s1, hinv.middle_eq]
        unemb_eq := by
          have hun : unembeddedCount1 wd s1 + 1 = unembeddedCount1 wd s :=
            (unembeddedCount1_update_none wd s heW_m hnone P_J).2
          have horig : s.getPathCountJ + unembeddedCount1 wd s = wd.W.m - wd.j0Edges.length :=
            hinv.unemb_eq
          have h1 : s1.getPathCountJ = s.getPathCountJ + 1 := rfl
          omega
        vcongUpdates_le := by
          have hPJ_edges : ∀ e' ∈ P_J.edges, e' < J.m :=
            hPJ_walk.2.2.elim (fun h => by simp [h.2.1]) (fun h => h.2.2.2.2.1)
          have hupd_le : (updVerts : ℝ) ≤ wd.γ_ExpPath * ((length J embJH : ℝ) + 1) := by
            have hsum_nat : updVerts ≤ P_J.edges.length * (length J embJH + 1) := by
              have helems : ∀ e' ∈ P_J.edges, (embJH e').verts.length ≤ length J embJH + 1 := by
                intro e' he'
                have hw' := hembJH.2 e' (hPJ_edges e' he')
                have hv_le := walk_verts_length_le_edges_succ hw'
                have he_le := edges_length_le_length embJH (hPJ_edges e' he')
                omega
              have hlist : ∀ l : List ℕ, (∀ e' ∈ l, (embJH e').verts.length ≤ length J embJH + 1) →
                  (l.map fun e' => (embJH e').verts.length).sum ≤ l.length * (length J embJH + 1) := by
                intro l hl
                induction l with
                | nil => simp
                | cons e' es ih =>
                  simp only [List.map_cons, List.sum_cons, List.length_cons]
                  calc (embJH e').verts.length + (es.map fun x => (embJH x).verts.length).sum
                      ≤ (length J embJH + 1) + es.length * (length J embJH + 1) :=
                        Nat.add_le_add (hl e' List.mem_cons_self)
                          (ih fun k hk => hl k (List.mem_cons_of_mem e' hk))
                    _ = (es.length + 1) * (length J embJH + 1) := by ring
              exact hlist P_J.edges helems
            have hsum_r : (updVerts : ℝ) ≤ (P_J.edges.length : ℝ) * ((length J embJH : ℝ) + 1) := by
              exact_mod_cast hsum_nat
            exact le_trans hsum_r (mul_le_mul_of_nonneg_right hP_len_le (by positivity))
          dsimp only [s1]
          push_cast
          calc (s.vcongUpdates : ℝ) + (updVerts : ℝ)
              ≤ (s.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) +
                  wd.γ_ExpPath * ((length J embJH : ℝ) + 1) := add_le_add hinv.vcongUpdates_le hupd_le
            _ = ((s.getPathCountJ : ℝ) + 1) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1)) := by ring }
    have hrel1 : Task2RoundRel tools.pathDS wd s_prev s1 :=
      { emb_mono := by
          intro e0 he0
          by_cases h0 : e0 = eW
          · rcases hrel.emb_mono e0 he0 with hprev | hsame
            · exact Or.inl hprev
            · rw [h0, hnone] at hsame
              exact Or.inl (by rw [h0]; exact hsame.symm)
          · simp only [s1, Function.update_of_ne h0]
            exact hrel.emb_mono e0 he0
        inner_eq := hrel.inner_eq
        del_eq := hrel.del_eq }
    obtain ⟨hloop', hrel', _, _, _, _, _, _⟩ :=
      task2InnerLoop_spec tools H' J embJH hw hcore1 hrel1
    rw [← hs'_eq] at hloop' hrel'
    have hunemb_lt : unembeddedCount1 wd s' < unembeddedCount1 wd s := by
      have h1 : s'.getPathCountJ + unembeddedCount1 wd s' = wd.W.m - wd.j0Edges.length := hloop'.unemb_eq
      have h0 : s.getPathCountJ + unembeddedCount1 wd s = wd.W.m - wd.j0Edges.length := hinv.unemb_eq
      have hgp_eq : s'.getPathCountJ = s.getPathCountJ + 1 := by
        rw [hs'_eq]
        exact (task2InnerLoop_spec tools H' J embJH hw hcore1 hrel1).2.2.2.1
      omega
    exact ⟨hloop', hrel', hunemb_lt⟩

/-! ## Task 2 round invariant (`invariant_1`), Claim 8.7 (`claim_8_7`), and Corollary 8.8 -/


end MinCostFlow.Spanner
