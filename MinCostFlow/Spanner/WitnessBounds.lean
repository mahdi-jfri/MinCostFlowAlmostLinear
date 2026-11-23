module

public import MinCostFlow.Spanner.WitnessOK

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Witness bounds and edge/source characterizations for Task 1

Proves exact edge-index and source characterizations (`wSources_length`, `W_edge_cases`,
`jSources_cases`) and weight/edge-count bounds (`wW_pos`, `wW_ge_phi`, `wW_le_maxDeg`,
`sum_comp_j_m_le`) for `buildWitness`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Edge and source characterizations for `buildWitness` -/

theorem wSources_length {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk) :
    (buildWitness tools H' J embJH).wSources.length = (buildWitness tools H' J embJH).W.m := by
  let wd := buildWitness tools H' J embJH
  have hsum : ∀ (l : List CompInfo) (k : ℕ),
      ((l.zipIdx k).flatMap fun (c, ci) =>
        (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal).length =
      (l.map fun c => c.W_sub.m).sum := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons c cs ih =>
      intro k
      simp [List.zipIdx_cons, List.flatMap_cons, ih (k + 1)]
  change (wd.j0Edges.map WEdgeSource.fromJ0 ++
      (wd.comps.zipIdx.flatMap fun (c, ci) =>
        (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal)).length =
    (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++ wd.comps.flatMap compWEdges).length
  rw [List.length_append, List.length_append, List.length_map, List.length_map,
    ← compsAligned_sum_m, hsum wd.comps 0]

theorem W_edges_getD_j0 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).j0Edges.length) :
    let wd := buildWitness tools H' J embJH
    eW < wd.W.m ∧
    wd.W.edges.getD eW (0, 0) = J.edges.getD (wd.j0Edges.getD eW 0) (0, 0) ∧
    wd.wSources.getD eW (WEdgeSource.fromJ0 0) = WEdgeSource.fromJ0 (wd.j0Edges.getD eW 0) ∧
    wd.wW eW = wd.φ_dec := by
  intro wd
  have heW_lt : eW < wd.j0Edges.length := heW
  have heW_m : eW < wd.W.m := by
    change eW < (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++ wd.comps.flatMap compWEdges).length
    rw [List.length_append, List.length_map]
    exact Nat.lt_of_lt_of_le heW_lt (Nat.le_add_right _ _)
  refine ⟨heW_m, ?_, ?_, ?_⟩
  · change (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).getD eW (0, 0) = _
    have hlt : eW < (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0))).length := by
      simpa using heW_lt
    have hlt_app : eW < (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length := by
      rw [List.length_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    rw [List.getD_eq_getElem _ _ hlt_app, List.getElem_append_left hlt,
        List.getElem_map, List.getD_eq_getElem _ _ heW_lt]
  · change (wd.j0Edges.map WEdgeSource.fromJ0 ++
        (wd.comps.zipIdx.flatMap fun (c, ci) =>
          (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal)).getD eW
          (WEdgeSource.fromJ0 0) = _
    have hlt : eW < (wd.j0Edges.map WEdgeSource.fromJ0).length := by simpa using heW_lt
    have hlt_app : eW < (wd.j0Edges.map WEdgeSource.fromJ0 ++
        (wd.comps.zipIdx.flatMap fun (c, ci) =>
          (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal)).length := by
      rw [List.length_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    rw [List.getD_eq_getElem _ _ hlt_app, List.getElem_append_left hlt,
        List.getElem_map, List.getD_eq_getElem _ _ heW_lt]
  · change witnessWeight wd.φ_dec wd.j0Edges.length wd.comps eW = wd.φ_dec
    unfold witnessWeight
    split_ifs
    rfl

theorem W_edges_getD_comp {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {ci eL : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length)
    (heL : eL < ((buildWitness tools H' J embJH).comps[ci]'hci).W_sub.m) :
    let wd := buildWitness tools H' J embJH
    let c := wd.comps[ci]'hci
    let eW := c.wStart + eL
    eW < wd.W.m ∧
    wd.j0Edges.length ≤ eW ∧
    wd.W.edges.getD eW (0, 0) =
      (c.verts.getD (c.W_sub.edges.getD eL (0, 0)).1 0,
       c.verts.getD (c.W_sub.edges.getD eL (0, 0)).2 0) ∧
    wd.wSources.getD eW (WEdgeSource.fromJ0 0) = WEdgeSource.fromComp ci eL ∧
    wd.wW eW = wd.φ_dec * (2 ^ c.level : ℝ) := by
  intro wd c eW
  have heL' : eL < c.W_sub.m := heL
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  have haligned : CompsAligned wd.j0Edges.length wd.comps :=
    buildComps_aligned tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
  have hwStart_ge : wd.j0Edges.length ≤ c.wStart :=
    compsAligned_wStart_ge haligned c (List.getElem_mem hci)
  have hWm : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
    change (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length = _
    rw [List.length_append, List.length_map, compsAligned_sum_m]
  have hwEnd_le : c.wStart + c.W_sub.m ≤ wd.W.m := by
    rw [hWm]; exact compsAligned_wEnd_le haligned ci hci
  have heW_lt : eW < wd.W.m := lt_of_lt_of_le (Nat.add_lt_add_left heL' c.wStart) hwEnd_le
  have hj0_le : wd.j0Edges.length ≤ eW := le_trans hwStart_ge (Nat.le_add_right _ _)
  have hnot_lt : ¬ eW < wd.j0Edges.length := Nat.not_lt_of_ge hj0_le
  obtain ⟨hidx1, heq1⟩ := compsAligned_flatMap_getElem haligned ci hci eL heL'
  obtain ⟨hidx2, heq2⟩ := compsAligned_flatMap_wSources haligned (base := 0) ci hci eL heL'
  have hsub_e : c.wStart - wd.j0Edges.length + eL = eW - wd.j0Edges.length := by omega
  refine ⟨heW_lt, hj0_le, ?_, ?_, ?_⟩
  · have heW_app : eW < (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).length := heW_lt
    change (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges).getD eW (0, 0) = _
    have hlen_j0 : (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0))).length =
        wd.j0Edges.length := List.length_map _
    rw [List.getD_eq_getElem _ _ heW_app,
        List.getElem_append_right (by rw [hlen_j0]; exact hj0_le)]
    simp_rw [hlen_j0, ← hsub_e]
    rw [heq1, List.getD_eq_getElem _ _ heL']
  · have hlen_w : eW < wd.wSources.length := by
      rw [wSources_length tools H' J embJH]; exact heW_lt
    have hlen_app : eW < (wd.j0Edges.map WEdgeSource.fromJ0 ++
        (wd.comps.zipIdx.flatMap fun (c', ci') =>
          (List.range c'.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci' eLocal)).length := hlen_w
    change (wd.j0Edges.map WEdgeSource.fromJ0 ++
        (wd.comps.zipIdx.flatMap fun (c', ci') =>
          (List.range c'.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci' eLocal)).getD eW
          (WEdgeSource.fromJ0 0) = _
    have hlen_j0 : (wd.j0Edges.map WEdgeSource.fromJ0).length = wd.j0Edges.length := List.length_map _
    rw [List.getD_eq_getElem _ _ hlen_app,
        List.getElem_append_right (by rw [hlen_j0]; exact hj0_le)]
    simp_rw [hlen_j0, ← hsub_e]
    simpa [Nat.zero_add] using heq2
  · have hfind := find?_comp_unique haligned hci (eW := eW) (Nat.le_add_right _ _)
      (Nat.add_lt_add_left heL' c.wStart)
    change witnessWeight wd.φ_dec wd.j0Edges.length wd.comps eW = _
    unfold witnessWeight
    split_ifs
    rw [hfind]

theorem W_edge_cases {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).W.m) :
    let wd := buildWitness tools H' J embJH
    eW < wd.j0Edges.length ∨
      ∃ (ci : ℕ) (hci : ci < wd.comps.length) (eL : ℕ),
        eL < (wd.comps[ci]'hci).W_sub.m ∧ eW = (wd.comps[ci]'hci).wStart + eL := by
  intro wd
  have heW' : eW < wd.W.m := heW
  by_cases hlt : eW < wd.j0Edges.length
  · exact Or.inl hlt
  · right
    set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
      (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
    have haligned : CompsAligned wd.j0Edges.length wd.comps :=
      buildComps_aligned tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
    have hWm : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
      change (wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
          wd.comps.flatMap compWEdges).length = _
      rw [List.length_append, List.length_map, compsAligned_sum_m]
    obtain ⟨ci, hci, h1, h2⟩ :=
      compsAligned_find_wStart haligned eW (Nat.le_of_not_lt hlt) (by rw [← hWm]; exact heW')
    refine ⟨ci, hci, eW - (wd.comps[ci]'hci).wStart, by omega, by omega⟩

theorem jSources_length {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk) :
    (buildWitness tools H' J embJH).jSources.length = J.m := by
  simp [buildWitness]

private theorem mem_j0Edges_iff {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {eJ : ℕ} :
    let wd := buildWitness tools H' J embJH
    eJ ∈ wd.j0Edges ↔ ∃ (b : ℕ) (_hb : b < wd.J0_strip.m),
      wd.decomp.level b = 0 ∧ wd.nlIdx.getD b 0 = eJ := by
  intro wd
  simp only [wd, buildWitness, DecomposeOutput.edgesAt, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨hb, hlvl⟩, rfl⟩
    exact ⟨b, hb, hlvl, rfl⟩
  · rintro ⟨b, hb, hlvl, rfl⟩
    exact ⟨b, ⟨hb, hlvl⟩, rfl⟩

theorem jSources_cases {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {eJ : ℕ} (heJ : eJ < J.m) :
    let wd := buildWitness tools H' J embJH
    match wd.jSources.getD eJ JEdgeSource.isLoop with
    | JEdgeSource.isLoop =>
        (J.edges.getD eJ (0, 0)).1 = (J.edges.getD eJ (0, 0)).2
    | JEdgeSource.inJ0 eW =>
        eW < wd.j0Edges.length ∧ wd.j0Edges.getD eW 0 = eJ ∧
        eW < wd.W.m ∧ wd.W.edges.getD eW (0, 0) = J.edges.getD eJ (0, 0) ∧
        wd.wW eW = wd.φ_dec
    | JEdgeSource.inComp ci jLocal =>
        ∃ (hci : ci < wd.comps.length) (hj : jLocal < (wd.comps[ci]'hci).jSubOrigEdges.length),
          let c := wd.comps[ci]'hci
          c.jSubOrigEdges[jLocal]'hj = eJ ∧ jLocal < c.J_sub.m ∧
          J.edges.getD eJ (0, 0) =
            (c.verts.getD (c.J_sub.edges.getD jLocal (0, 0)).1 0,
             c.verts.getD (c.J_sub.edges.getD jLocal (0, 0)).2 0) := by
  intro wd
  have hlen : wd.jSources.length = J.m := jSources_length tools H' J embJH
  have hget : wd.jSources.getD eJ JEdgeSource.isLoop =
      if eJ ∈ wd.j0Edges then JEdgeSource.inJ0 (wd.j0Edges.idxOf eJ)
      else match findJCompEdge eJ wd.comps 0 with
        | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
        | none => JEdgeSource.isLoop := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact heJ)]
    change ((List.range J.m).map fun eJ' =>
      if eJ' ∈ wd.j0Edges then JEdgeSource.inJ0 (wd.j0Edges.idxOf eJ')
      else match findJCompEdge eJ' wd.comps 0 with
        | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
        | none => JEdgeSource.isLoop)[eJ]'(by simp [heJ]) = _
    rw [List.getElem_map, List.getElem_range]
  rw [hget]
  split_ifs with hj0
  · set eW := wd.j0Edges.idxOf eJ
    have heW_len : eW < wd.j0Edges.length := List.idxOf_lt_length_iff.mpr hj0
    have heW_getD : wd.j0Edges.getD eW 0 = eJ := by
      rw [List.getD_eq_getElem _ _ heW_len]; exact List.getElem_idxOf heW_len
    obtain ⟨heW_m, hWe, _, hWw⟩ := W_edges_getD_j0 tools H' J embJH heW_len
    rw [heW_getD] at hWe
    exact ⟨heW_len, heW_getD, heW_m, hWe, hWw⟩
  · have hspec := findJCompEdge_spec eJ wd.comps 0
    cases hf : findJCompEdge eJ wd.comps 0 with
    | some p =>
      rw [hf] at hspec
      rcases hspec with ⟨hci, hj, _, horig⟩
      have hci' : p.1 < wd.comps.length := by simpa using hci
      have hj' : p.2 < (wd.comps[p.1]'hci').jSubOrigEdges.length := by simpa using hj
      set c := wd.comps[p.1]'hci'
      have horig' : c.jSubOrigEdges[p.2]'hj' = eJ := by simpa [c] using horig
      rcases hw.comp_props p.1 hci' with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, _, _, _, _⟩
      have hj_sub : p.2 < c.J_sub.m := by rw [← hjLen]; exact hj'
      set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
        (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
      obtain ⟨_, hverts_eq, hJsub_eq, hjOrig_eq, _⟩ :=
        buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
          (List.getElem_mem hci')
      set J_i := wd.decomp.graphAt wd.J0_strip c.level
      have hJ_sub_m : p.2 < (J_i.inside c.X).length := by
        rw [← inducedSubgraph_m J_i c.X, ← hJsub_eq]; exact hj_sub
      have hidx_len : p.2 < (insideIndices J_i c.X).length := by
        have hlen := congrArg List.length (insideIndices_map_eq_inside J_i c.X)
        rw [List.length_map] at hlen
        omega
      set a := (insideIndices J_i c.X)[p.2]'hidx_len
      have ha_mem : a ∈ insideIndices J_i c.X := List.getElem_mem hidx_len
      have ha_lt : a < J_i.m := (mem_insideIndices.mp ha_mem).1
      have ha_inX := (mem_insideIndices.mp ha_mem).2
      have ha_ed_len : a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
        simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha_lt
      set b := (wd.decomp.edgesAt wd.J0_strip c.level)[a]'ha_ed_len
      have hb_mem : b ∈ wd.decomp.edgesAt wd.J0_strip c.level := List.getElem_mem ha_ed_len
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb_mem
      have hb_m : b < wd.J0_strip.m := hb_mem.1
      have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
        simp [wd, buildWitness, stripLoops, Graph.m]
      have hb_nl : b < wd.nlIdx.length := by omega
      have horig_eq : eJ = wd.nlIdx[b]'hb_nl := by
        have hgetD_eJ : c.jSubOrigEdges.getD p.2 0 = eJ := by
          rw [List.getD_eq_getElem _ _ hj']; exact horig'
        rw [← hgetD_eJ, hjOrig_eq, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hidx_len),
          List.getElem_map]
        change wd.nlIdx.getD ((wd.decomp.edgesAt wd.J0_strip c.level).getD a 0) 0 = _
        rw [List.getD_eq_getElem _ _ ha_ed_len, List.getD_eq_getElem _ _ hb_nl]
      have hJ_edge : J.edges.getD eJ (0, 0) = J_i.edges.getD a (0, 0) := by
        have ha_ed' : a < ((wd.decomp.edgesAt wd.J0_strip c.level).map
            (fun j => wd.J0_strip.edges.getD j (0, 0))).length := by
          rw [List.length_map]; exact ha_ed_len
        have hb_strip : b < wd.J0_strip.edges.length := by simpa [Graph.m] using hb_m
        have hb_ed' : b < ((nonloopIndices J).map fun j => J.edges.getD j (0, 0)).length := by
          rw [List.length_map]; simpa [wd, buildWitness] using hb_nl
        simp only [J_i, DecomposeOutput.graphAt]
        rw [List.getD_eq_getElem _ _ ha_ed', List.getElem_map]
        change J.edges.getD eJ (0, 0) = wd.J0_strip.edges.getD b (0, 0)
        change J.edges.getD eJ (0, 0) =
          ((nonloopIndices J).map fun j => J.edges.getD j (0, 0)).getD b (0, 0)
        rw [List.getD_eq_getElem _ _ hb_ed', List.getElem_map]
        have horig_raw : eJ = (nonloopIndices J)[b]'(by simpa [wd, buildWitness] using hb_nl) :=
          horig_eq
        rw [horig_raw]
      have hSub_edge : c.J_sub.edges.getD p.2 (0, 0) =
          (c.verts.idxOf (J_i.edges.getD a (0, 0)).1, c.verts.idxOf (J_i.edges.getD a (0, 0)).2) := by
        rw [hJsub_eq, hverts_eq]
        have hp2_ind : p.2 < (inducedSubgraph J_i c.X).edges.length := by
          simpa [inducedSubgraph, Graph.m] using hidx_len
        change (inducedSubgraph J_i c.X).edges.getD p.2 (0, 0) = _
        rw [List.getD_eq_getElem _ _ hp2_ind]
        simp only [inducedSubgraph, List.getElem_map]
        change ((vertsOf c.X).idxOf (J_i.edges.getD a (0, 0)).1,
                (vertsOf c.X).idxOf (J_i.edges.getD a (0, 0)).2) = _
        rfl
      refine ⟨hci', hj', horig', hj_sub, ?_⟩
      rw [hJ_edge, hSub_edge, hverts_eq]
      dsimp only
      rw [getD_vertsOf_idxOf ha_inX.1, getD_vertsOf_idxOf ha_inX.2]
    | none =>
      rw [hf] at hspec
      by_contra hne
      have hmem_nl : eJ ∈ wd.nlIdx := mem_nonloopIndices.mpr ⟨heJ, hne⟩
      obtain ⟨b, hb_nl, hb_eq⟩ := List.mem_iff_getElem.mp hmem_nl
      have hnl_len : (nonloopIndices J).length = wd.J0_strip.m := by
        simp [wd, buildWitness, stripLoops, Graph.m]
      have hb_m : b < wd.J0_strip.m := by
        have hb_len : b < (nonloopIndices J).length := hb_nl
        exact hnl_len ▸ hb_len
      have hdec := tools.decompose.decompose_spec wd.J0_strip (stripLoops_isValid hJ) (stripLoops_isLoopless J)
      have hlvl_le : wd.decomp.level b ≤ wd.decomp.ℓ := hdec.2.1 b hb_m
      cases hlvl : wd.decomp.level b with
      | zero =>
        apply hj0
        refine (mem_j0Edges_iff tools H' J embJH).mpr ⟨b, hb_m, hlvl, ?_⟩
        rw [List.getD_eq_getElem _ _ (by simpa [wd, buildWitness] using hb_nl)]
        exact hb_eq
      | succ i' =>
        have hi0 : 0 < i' + 1 := Nat.zero_lt_succ i'
        have hiℓ : i' + 1 ≤ wd.decomp.ℓ := by omega
        set J_i := wd.decomp.graphAt wd.J0_strip (i' + 1)
        have hb_ed : b ∈ wd.decomp.edgesAt wd.J0_strip (i' + 1) := by
          simp [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, hb_m, hlvl]
        have he_Ji : wd.J0_strip.edges.getD b (0, 0) ∈ J_i.edges := by
          simp only [J_i, DecomposeOutput.graphAt, List.mem_map]
          exact ⟨b, hb_ed, rfl⟩
        obtain ⟨X, hXcomp, hXends⟩ := (hdec.2.2.2 (i' + 1) hi0 hiℓ).2.2 _ he_Ji
        set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
          (wd.decomp.comps (i' + 1)).map fun Y => (i' + 1, Y)
        have hraw_mem : (i' + 1, X) ∈ rawComps := rawComps_mem_iff.mpr ⟨hi0, hiℓ, hXcomp⟩
        rcases List.mem_iff_getElem.mp hraw_mem with ⟨ci, hci_r, hci_eq⟩
        have hclen : wd.comps.length = rawComps.length :=
          buildComps_length tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
        have hci : ci < wd.comps.length := by omega
        have hpair := buildComps_getElem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
          wd.j0Edges.length rawComps ci hci_r
        rw [hci_eq] at hpair
        set c := wd.comps[ci]'hci
        obtain ⟨_, _, _, hjOrig_eq, _⟩ :=
          buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
            (List.getElem_mem hci)
        have hclvl : c.level = i' + 1 := congrArg Prod.fst hpair
        have hcX : c.X = X := congrArg Prod.snd hpair
        rcases List.mem_iff_getElem.mp hb_ed with ⟨a, ha_ed, ha_eq⟩
        have ha_m : a < J_i.m := by simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha_ed
        have ha_inside : a ∈ insideIndices (wd.decomp.graphAt wd.J0_strip c.level) c.X := by
          rw [hclvl, hcX]
          refine mem_insideIndices.mpr ⟨ha_m, ?_⟩
          have ha_ed' : a < ((wd.decomp.edgesAt wd.J0_strip (i' + 1)).map
              (fun j => wd.J0_strip.edges.getD j (0, 0))).length := by
            rw [List.length_map]; exact ha_ed
          have hJied : J_i.edges.getD a (0, 0) = wd.J0_strip.edges.getD b (0, 0) := by
            simp only [J_i, DecomposeOutput.graphAt]
            rw [List.getD_eq_getElem _ _ ha_ed', List.getElem_map, ha_eq]
          rw [hJied]
          exact hXends
        have hj_in_c : eJ ∈ c.jSubOrigEdges := by
          rw [hjOrig_eq, List.mem_map]
          refine ⟨a, ha_inside, ?_⟩
          have ha_ed' : a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
            rw [hclvl]; exact ha_ed
          rw [List.getD_eq_getElem _ _ ha_ed']
          have ha_eq' : (wd.decomp.edgesAt wd.J0_strip c.level)[a]'ha_ed' = b := by
            simp_rw [hclvl]; exact ha_eq
          rw [ha_eq', List.getD_eq_getElem _ _ (by simpa [wd, buildWitness] using hb_nl)]
          exact hb_eq
        exact hspec c (List.getElem_mem hci) hj_in_c

/-! ## Task 1 weight, edge-count, and degree bounds -/

theorem wW_pos {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).W.m) :
    0 < (buildWitness tools H' J embJH).wW eW := by
  let wd := buildWitness tools H' J embJH
  rcases W_edge_cases tools H' J embJH heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · have := (W_edges_getD_j0 tools H' J embJH hj0).2.2.2
    rw [this]
    exact hw.φ_dec_pos
  · have := (W_edges_getD_comp tools H' J embJH hci heL).2.2.2.2
    rw [this]
    have hφ := hw.φ_dec_pos
    positivity

theorem wW_ge_phi {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).W.m) :
    (buildWitness tools H' J embJH).φ_dec ≤ (buildWitness tools H' J embJH).wW eW := by
  let wd := buildWitness tools H' J embJH
  rcases W_edge_cases tools H' J embJH heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · rw [(W_edges_getD_j0 tools H' J embJH hj0).2.2.2]
  · rw [(W_edges_getD_comp tools H' J embJH hci heL).2.2.2.2]
    have hφ := hw.φ_dec_pos
    have h1 : (1 : ℝ) ≤ (2 ^ (wd.comps[ci]'hci).level : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    nlinarith

theorem wW_ge_two_phi_comp {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {eW : ℕ} (hge : (buildWitness tools H' J embJH).j0Edges.length ≤ eW)
    (heW : eW < (buildWitness tools H' J embJH).W.m) :
    2 * (buildWitness tools H' J embJH).φ_dec ≤ (buildWitness tools H' J embJH).wW eW := by
  let wd := buildWitness tools H' J embJH
  rcases W_edge_cases tools H' J embJH heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · omega
  · rw [(W_edges_getD_comp tools H' J embJH hci heL).2.2.2.2]
    have hpos := (hw.comp_props ci hci).1
    have h2pow : (2 : ℝ) ≤ (2 ^ (wd.comps[ci]'hci).level : ℝ) := by
      exact_mod_cast Nat.le_self_pow hpos.ne' 2
    have hφ := hw.φ_dec_pos
    nlinarith

theorem wW_le_maxDeg {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).W.m) :
    (buildWitness tools H' J embJH).wW eW ≤ (maxDeg J : ℝ) := by
  let wd := buildWitness tools H' J embJH
  rcases W_edge_cases tools H' J embJH heW with hj0 | ⟨ci, hci, eL, heL, rfl⟩
  · rw [(W_edges_getD_j0 tools H' J embJH hj0).2.2.2]
    have hj_lt := hw.j0_lt _ (List.getElem_mem hj0)
    set e := J.edges[wd.j0Edges[eW]'hj0]'(by simpa [Graph.m] using hj_lt)
    have he_mem : e ∈ J.edges := List.getElem_mem _
    have hv1 : e.1 < J.n := (hJ e he_mem).1
    have hdeg1 : 1 ≤ J.deg e.1 := by
      rw [deg_eq_filter_edges hJ e.1]
      have : 0 < (J.edges.filter fun x => decide (x.1 = e.1)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨e, List.mem_filter.mpr ⟨he_mem, decide_eq_true rfl⟩⟩
      omega
    have hle : 1 ≤ maxDeg J := le_trans hdeg1 (deg_le_maxDeg hv1)
    have h1 : (1 : ℝ) ≤ (maxDeg J : ℝ) := by exact_mod_cast hle
    exact le_trans hw.φ_dec_le h1
  · rw [(W_edges_getD_comp tools H' J embJH hci heL).2.2.2.2]
    rcases hw.comp_props ci hci with
      ⟨_, _, hXJ_c, hX2_c, hverts_c, _, _, _, _, _, _, _, _, _, _, _, _, _, hdeg_ge_phi_c, _⟩
    set c := wd.comps[ci]'hci
    have h0lt : 0 < c.X.card := by omega
    have hφ_le_Jsub : wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg 0 : ℝ) :=
      hdeg_ge_phi_c 0 h0lt
    set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
      (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
    obtain ⟨_, hverts_eq, hJsub_eq, _, _⟩ :=
      buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps c
        (List.getElem_mem hci)
    set v0 := c.verts.getD 0 0
    have hv0_X : v0 ∈ c.X := by dsimp only [v0]; rw [hverts_eq]; exact getD_vertsOf_mem h0lt
    have hv0_J : v0 < J.n := Finset.mem_range.mp (hXJ_c hv0_X)
    have hJsub_deg : c.J_sub.deg 0 = (wd.decomp.graphAt wd.J0_strip c.level).degIn c.X v0 := by
      rw [hJsub_eq]; dsimp only [v0]; rw [hverts_eq]; exact inducedSubgraph_deg h0lt
    have hdeg_le : (wd.decomp.graphAt wd.J0_strip c.level).degIn c.X v0 ≤ J.deg v0 := by
      have h1 : (wd.decomp.graphAt wd.J0_strip c.level).degIn c.X v0 ≤
          (wd.decomp.graphAt wd.J0_strip c.level).deg v0 := by
        unfold Graph.deg
        exact degIn_mono_right (fun x hx => Finset.mem_range.mpr
          (Finset.mem_range.mp (hXJ_c hx))) v0
      have h2 : (wd.decomp.graphAt wd.J0_strip c.level).deg v0 ≤ wd.J0_strip.deg v0 :=
        graphAt_deg_le (stripLoops_isValid hJ) wd.decomp c.level v0
      have h3 : wd.J0_strip.deg v0 ≤ J.deg v0 := stripLoops_deg_le hJ v0
      omega
    have hmax : J.deg v0 ≤ maxDeg J := deg_le_maxDeg hv0_J
    have hnat : c.J_sub.deg 0 ≤ maxDeg J := by omega
    exact le_trans hφ_le_Jsub (by exact_mod_cast hnat)

private theorem sum_range_getD {α M : Type*} [AddCommMonoid M] (l : List α) (d : α) (f : α → M) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ', add_comm, List.map_cons, List.sum_cons]
    have h0 : (a :: as).getD 0 d = a := rfl
    have hs : ∀ i, (a :: as).getD (i + 1) d = as.getD i d := fun _ => rfl
    simp_rw [hs]
    rw [h0, ih]

theorem sum_comp_j_m_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    (buildWitness tools H' J embJH).j0Edges.length +
      ((buildWitness tools H' J embJH).comps.map fun c => c.J_sub.m).sum ≤
        (buildWitness tools H' J embJH).J0_strip.m := by
  let wd := buildWitness tools H' J embJH
  have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
    simp [wd, buildWitness, stripLoops, Graph.m]
  have hnl_nodup : wd.nlIdx.Nodup := nonloopIndices_nodup J
  have hunion : (wd.j0Edges.toFinset ∪
      (Finset.range wd.comps.length).biUnion fun ci =>
        if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅) ⊆
      wd.nlIdx.toFinset := by
    intro jOrig hj
    rcases Finset.mem_union.mp hj with hj0 | hjc
    · rw [List.mem_toFinset] at hj0 ⊢
      change jOrig ∈ (wd.decomp.edgesAt wd.J0_strip 0).map (fun k => wd.nlIdx.getD k 0) at hj0
      simp only [DecomposeOutput.edgesAt, List.mem_map, List.mem_filter, List.mem_range] at hj0
      rcases hj0 with ⟨b, ⟨hb, _⟩, rfl⟩
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    · rcases Finset.mem_biUnion.mp hjc with ⟨ci, hci_r, hjci⟩
      have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
      split_ifs at hjci
      rw [List.mem_toFinset] at hjci
      set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
        (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
      obtain ⟨_, _, hJsub_eq, hjOrig_eq, _⟩ :=
        buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
          (wd.comps[ci]'hci) (List.getElem_mem hci)
      rw [hjOrig_eq, List.mem_map] at hjci
      rcases hjci with ⟨a, ha, rfl⟩
      have ha_lt := (mem_insideIndices.mp ha).1
      have ha_ed : a < (wd.decomp.edgesAt wd.J0_strip (wd.comps[ci]'hci).level).length := by
        simpa [DecomposeOutput.graphAt, Graph.m] using ha_lt
      rw [List.getD_eq_getElem _ _ ha_ed]
      have hb_mem : (wd.decomp.edgesAt wd.J0_strip (wd.comps[ci]'hci).level)[a]'ha_ed ∈
          wd.decomp.edgesAt wd.J0_strip (wd.comps[ci]'hci).level := List.getElem_mem _
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb_mem
      have hb_nl : (wd.decomp.edgesAt wd.J0_strip (wd.comps[ci]'hci).level)[a]'ha_ed < wd.nlIdx.length := by
        rw [hnl_len]; exact hb_mem.1
      rw [List.getD_eq_getElem _ _ hb_nl, List.mem_toFinset]
      exact List.getElem_mem _
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint, Finset.card_biUnion] at hcard
  · have hj0_card : wd.j0Edges.toFinset.card = wd.j0Edges.length :=
      List.toFinset_card_of_nodup hw.j0_nodup
    have hnl_card : wd.nlIdx.toFinset.card = wd.nlIdx.length :=
      List.toFinset_card_of_nodup hnl_nodup
    have hsum_eq : (∑ ci ∈ Finset.range wd.comps.length,
        (if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅).card) =
        (wd.comps.map fun c => c.J_sub.m).sum := by
      have hcongr : (∑ ci ∈ Finset.range wd.comps.length,
          (if h : ci < wd.comps.length then (wd.comps[ci]'h).jSubOrigEdges.toFinset else ∅).card) =
          ∑ ci ∈ Finset.range wd.comps.length, (wd.comps.getD ci defaultCompInfo).J_sub.m := by
        refine Finset.sum_congr rfl fun ci hci_r => ?_
        have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
        rcases hw.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, hjNodup, _, _, _⟩
        split_ifs
        rw [List.toFinset_card_of_nodup hjNodup, hjLen, List.getD_eq_getElem _ _ hci]
      rw [hcongr, sum_range_getD wd.comps defaultCompInfo (fun c => c.J_sub.m)]
    rw [hj0_card, hnl_card, hsum_eq, hnl_len] at hcard
    exact hcard
  · intro ci₁ h1 ci₂ h2 hne
    change Disjoint _ _
    have h1' := Finset.mem_range.mp h1
    have h2' := Finset.mem_range.mp h2
    dsimp only
    split_ifs
    exact hw.comp_disjoint ci₁ ci₂ h1' h2' hne
  · rw [Finset.disjoint_left]
    intro jOrig hj0 hjc
    rcases Finset.mem_biUnion.mp hjc with ⟨ci, hci_r, hjci⟩
    have hci : ci < wd.comps.length := Finset.mem_range.mp hci_r
    split_ifs at hjci
    exact Finset.disjoint_left.mp (hw.comp_disjoint_j0 ci hci) hjci hj0

end MinCostFlow.Spanner

