module

public import MinCostFlow.Machine.WideWord.LSSTReductionBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic `IsLSST` reduction theorem for `[AN19]` output

This file completes the constructive proof of Theorem 2.2 (page 7) without `Classical.choose`:

* `concreteLSST_isLSST`: for any valid `(V_list, B, mult, δ, w_orig)` and any `[AN19]` tree `out`
  on `buildGAug G V_list B mult w_orig`, `concreteLSSTTree G V_list B mult out` satisfies
  `MinCostFlow.LSF.IsLSST`.
* `concreteLSSTRun` and `concreteLSSTRun_isLSST`: explicit deterministic tree obtained by running
  `P_AN` for `fuel` steps on all-false random bits (`fun _ => false`).
-/

@[expose] public section

namespace MinCostFlow.WideWord

open MinCostFlow
open MinCostFlow.LSF

private lemma traw_proj_lsst {G : IndexedGraph} {ℓ v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v T_gv T_raw : MGraph} {V_list B out : List ℕ} {mult w_orig : ℕ → ℕ} {δ K_AN K₁ : ℝ}
    (hG : G.Valid)
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hℓ : ∀ e ∈ G.toMGraph.E, 0 < ℓ e)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_nd : V_list.Nodup)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts G_v V_act (V_list.headD 0) B)
    (hmult : ∀ e ∈ nonloopEdges G, mult e = edgeMult G_nl v e)
    (hδ_pos : 0 < δ)
    (hw_orig_ge : ∀ e ∈ nonloopEdges G, 4 ≤ w_orig e)
    (hℓ_upper : ∀ e ∈ nonloopEdges G, ℓ e ≤ δ * ((w_orig e : ℝ) + 1))
    (hℓ_lower : ∀ e ∈ nonloopEdges G, δ * (w_orig e : ℝ) ≤ ℓ e)
    (hδ_Vact : ∀ e ∈ nonloopEdges G, δ * (V_act.card : ℝ) ≤ ℓ e / 2)
    (hout_st : (buildGAug G V_list B mult w_orig).IsSpanningTree out)
    (htot_st : (buildGAug G V_list B mult w_orig).totalStretch out ≤
      K_AN * ((buildGAug G V_list B mult w_orig).m : ℝ) *
        Cited.logLogFactor (buildGAug G V_list B mult w_orig).n)
    (hK₁ : 1 ≤ K₁) (hKAN : K_AN ≤ K₁)
    (hT_gv_def : T_gv =
      { V := V_act
        E := out.toFinset.image (fun j =>
          if hj : j < (copyEdgeList G mult).length then (copyEdgeList G mult)[j]'hj
          else (copyMod G.toMGraph + copyMod G_v) + (j - (copyEdgeList G mult).length))
        tail := fun f => if f ∈ G_v.E then G_v.tail f else V_list.headD 0
        head := fun f => if f ∈ G_v.E then G_v.head f else
          B.getD (f - (copyMod G.toMGraph + copyMod G_v)) 0 })
    (hT_raw_def : T_raw =
      { V := G_v.V
        E := T_gv.E ∪ (List.range (inactiveVertsList G.n V_list).length).toFinset.image
          (fun idx => (copyMod G.toMGraph + copyMod G_v + B.length) + idx)
        tail := fun f => if f < (copyMod G.toMGraph + copyMod G_v + B.length) then T_gv.tail f
          else V_list.headD 0
        head := fun f => if f < (copyMod G.toMGraph + copyMod G_v + B.length) then T_gv.head f
          else (inactiveVertsList G.n V_list).getD
            (f - (copyMod G.toMGraph + copyMod G_v + B.length)) 0 }) :
    G_v.V = Finset.range G.n ∧
    (∀ e' ∈ G_v.E, origEdge (copyMod G_nl) e' ∈ nonloopEdges G) ∧
    (∀ f ∈ T_gv.E, f ∉ G_v.E →
      ∃ k, k < B.length ∧ (copyEdgeList G mult).length + k ∈ out ∧
        f = (copyMod G.toMGraph + copyMod G_v) + k ∧
        T_gv.tail f = V_list.headD 0 ∧ T_gv.head f = B.getD k 0) ∧
    (∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G.toMGraph ≤ f) ∧
    (∀ e', e' ∈ copyEdgeList G mult ↔ e' ∈ G_v.E) ∧
    IsLSST G.toMGraph ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2)
      (projectTree G_nl v T_raw) := by
  have hE_eq : (nonloopEdges G).toFinset = G.toMGraph.E.filter fun e => G.tail e ≠ G.head e := by
    ext e
    simp only [Finset.mem_filter, IndexedGraph.toMGraph, Finset.mem_range,
      List.mem_toFinset, mem_nonloopEdges_iff]
  have hG_nl_def : G_nl = { G.toMGraph with E := G.toMGraph.E.filter fun e => G.tail e ≠ G.head e } := by
    rw [hG_nl_eq, hE_eq]
  have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
  have hV_ne : V_list ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (activeVertsList_nonempty_of_nonloop hG hnl_ne)
    exact List.ne_nil_of_mem ((hV_mem x).mpr hx)
  have hlen_pos : 0 < V_list.length := List.length_pos_of_ne_nil hV_ne
  let r₀ := V_list.headD 0
  have hr₀_eq : r₀ = V_list[0]'hlen_pos := headD_eq_getElem_zero V_list hlen_pos
  have hr₀_act : r₀ ∈ V_act :=
    (hV_act r₀).mp ((hV_mem r₀).mp (hr₀_eq ▸ List.getElem_mem hlen_pos))
  obtain ⟨hT_gv_V, hT_gv_val, hT_gv_st, hT_gv_lt, hT_gv_nGv, hT_gv_lift, hT_gv_no_bridges⟩ :=
    tgV_props hG hG_nl_eq hG_v_eq hnl_ne hv hV_nd hV_mem hV_act hB hmult hout_st
  rw [← hT_gv_def] at hT_gv_V hT_gv_val hT_gv_st hT_gv_lt hT_gv_nGv hT_gv_lift hT_gv_no_bridges
  let E_list := copyEdgeList G mult
  let baseB := copyMod G.toMGraph + copyMod G_v
  let baseInact := baseB + B.length
  let inact := inactiveVertsList G.n V_list
  have hV_len_eq : V_list.length = V_act.card := by
    rw [← List.toFinset_card_of_nodup hV_nd]
    congr 1; ext x; rw [List.mem_toFinset, hV_mem, hV_act]
  have hAct_sub : V_act ⊆ Finset.range G.n := fun x hx =>
    Finset.mem_range.mpr (mem_activeVertsList_iff.mp ((hV_act x).mpr hx)).1
  have hGv_V : G_v.V = Finset.range G.n := by
    rw [hG_v_eq, weightedCopyGraph, ite_eq_left hnl_ne', hG_nl_eq]; rfl
  have hT_raw_V : T_raw.V = G_v.V := by rw [hT_raw_def]
  have hT_sub_raw : T_raw.IsSubgraph T_gv := by
    refine ⟨?_, ?_, fun f hf => ?_⟩
    · rw [hT_raw_V, hGv_V, hT_gv_V]; exact hAct_sub
    · rw [hT_raw_def]; exact Finset.subset_union_left
    · have hflt := hT_gv_lt f hf
      rw [hT_raw_def]; dsimp only
      rw [ite_eq_left hflt, ite_eq_left hflt]
      exact ⟨rfl, rfl⟩
  have hT_raw_val : T_raw.IsValid := by
    intro f hf
    rw [hT_raw_def] at hf ⊢; dsimp only at hf ⊢
    rw [Finset.mem_union] at hf
    rcases hf with hf1 | hf2
    · have hv1 := hT_gv_val f hf1
      have hflt := hT_gv_lt f hf1
      rw [ite_eq_left hflt, ite_eq_left hflt, hGv_V]
      exact ⟨hAct_sub (hT_gv_V ▸ hv1.1), hAct_sub (hT_gv_V ▸ hv1.2)⟩
    · rw [Finset.mem_image] at hf2
      obtain ⟨idx, hidx, rfl⟩ := hf2
      have hidx_lt : idx < inact.length := List.mem_range.mp (List.mem_toFinset.mp hidx)
      have hnot : ¬ baseInact + idx < baseInact := by omega
      rw [ite_eq_right hnot, ite_eq_right hnot, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ hidx_lt, hGv_V]
      have hw_mem := (mem_inactiveVertsList_iff.mp (List.getElem_mem hidx_lt)).1
      exact ⟨hAct_sub hr₀_act, Finset.mem_range.mpr hw_mem⟩
  have hT_raw_conn : ∀ u ∈ G_v.V, ∀ v' ∈ G_v.V, T_raw.Connected u v' := by
    have hto_r₀ : ∀ x ∈ G_v.V, T_raw.Connected r₀ x := by
      intro x hx
      rw [hGv_V, Finset.mem_range] at hx
      by_cases hxV : x ∈ V_act
      · exact connected_of_subgraph hT_sub_raw (hT_gv_st.2.2 r₀ hr₀_act x hxV)
      · have hx_nVl : x ∉ V_list := fun h => hxV ((hV_act x).mp ((hV_mem x).mp h))
        have hx_inact : x ∈ inact := mem_inactiveVertsList_iff.mpr ⟨hx, hx_nVl⟩
        let idx := inact.idxOf x
        have hidx_lt : idx < inact.length := List.idxOf_lt_length_of_mem hx_inact
        have he_mem : baseInact + idx ∈ T_raw.E := by
          rw [hT_raw_def]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
            (List.mem_toFinset.mpr (List.mem_range.mpr hidx_lt)))
        have hnot : ¬ baseInact + idx < baseInact := by omega
        have htail : T_raw.tail (baseInact + idx) = r₀ := by
          rw [hT_raw_def]; dsimp only; exact ite_eq_right hnot
        have hhead : T_raw.head (baseInact + idx) = x := by
          rw [hT_raw_def]; dsimp only; rw [ite_eq_right hnot, Nat.add_sub_cancel_left,
            List.getD_eq_getElem _ _ hidx_lt]
          exact List.getElem_idxOf hidx_lt
        exact ⟨[(baseInact + idx, true)], .cons he_mem (by simp [MGraph.src, htail])
          (by simpa [MGraph.dst, hhead] using .nil x)⟩
    intro u hu v' hv'
    exact connected_trans (connected_symm (hto_r₀ u hu)) (hto_r₀ v' hv')
  have hinact_card : V_act.card + inact.length = G.n := by
    have hin_nd : inact.Nodup := inactiveVertsList_nodup G.n V_list
    have hunion : V_act ∪ inact.toFinset = Finset.range G.n := by
      ext x
      simp only [inact, Finset.mem_union, List.mem_toFinset, mem_inactiveVertsList_iff,
        Finset.mem_range]
      rw [← hV_act x, ← hV_mem x]
      constructor
      · rintro (h | ⟨hx, _⟩)
        · exact (mem_activeVertsList_iff.mp ((hV_mem x).mp h)).1
        · exact hx
      · intro hx
        by_cases h : x ∈ V_list <;> [exact Or.inl h; exact Or.inr ⟨hx, h⟩]
    have hdisj : Disjoint V_act inact.toFinset := Finset.disjoint_left.mpr fun x hxV hxin =>
      (mem_inactiveVertsList_iff.mp (List.mem_toFinset.mp hxin)).2
        ((hV_mem x).mpr ((hV_act x).mpr hxV))
    calc V_act.card + inact.length
        = V_act.card + inact.toFinset.card := by rw [List.toFinset_card_of_nodup hin_nd]
      _ = (V_act ∪ inact.toFinset).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = (Finset.range G.n).card := by rw [hunion]
      _ = G.n := Finset.card_range G.n
  have hAct_pos : 1 ≤ V_act.card := Finset.card_pos.mpr ⟨r₀, hr₀_act⟩
  have hT_raw_card : T_raw.E.card ≤ G_v.V.card - 1 := by
    have hcard_gv : T_gv.E.card ≤ V_act.card - 1 := by
      rw [hT_gv_def]; dsimp only
      calc (out.toFinset.image _).card ≤ out.toFinset.card := Finset.card_image_le
        _ ≤ out.length := List.toFinset_card_le _
        _ = V_list.length - 1 := hout_st.2.2.1
        _ = V_act.card - 1 := by rw [hV_len_eq]
    rw [hT_raw_def]; dsimp only
    calc (T_gv.E ∪ _).card
        ≤ T_gv.E.card + ((List.range inact.length).toFinset.image (fun idx => baseInact + idx)).card :=
          Finset.card_union_le _ _
      _ ≤ (V_act.card - 1) + (List.range inact.length).toFinset.card :=
          Nat.add_le_add hcard_gv Finset.card_image_le
      _ = (V_act.card - 1) + inact.length := by
          rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
      _ = G.n - 1 := by omega
      _ = G_v.V.card - 1 := by rw [hGv_V, Finset.card_range]
  have hT_raw_forest : T_raw.IsForest :=
    isForest_of_connected_card_le hT_raw_val
      (by rw [hT_raw_V, hGv_V]; exact ⟨r₀, hAct_sub hr₀_act⟩)
      (fun u hu v' hv' => hT_raw_conn u (hT_raw_V ▸ hu) v' (hT_raw_V ▸ hv'))
      (by rw [hT_raw_V]; exact hT_raw_card)
  have hT_raw_st : T_raw.IsSpanningTreeOn G_v.V := ⟨hT_raw_forest, hT_raw_V, hT_raw_conn⟩
  have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl_eq]
  have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
  have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
  have hT_raw_path_eq : ∀ e' ∈ G_v.E,
      T_raw.forestPath (G_v.tail e') (G_v.head e') =
        T_gv.forestPath (G_v.tail e') (G_v.head e') := by
    intro e' he'
    have hGv_end_e' : G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act := by
      have hm := weightedCopyGraph_origEdge_mem hnl_ne' (hG_v_eq ▸ he')
      have horig : origEdge (copyMod G_nl) e' ∈ nonloopEdges G := by
        have h1 := hm.1; rw [hnl_E] at h1; exact List.mem_toFinset.mp h1
      have hlt := (mem_nonloopEdges_iff.mp horig).1
      have htail : G_v.tail e' = G.tail (origEdge (copyMod G_nl) e') := by
        rw [hG_v_eq, hm.2.1, hnl_tail]
      have hhead : G_v.head e' = G.head (origEdge (copyMod G_nl) e') := by
        rw [hG_v_eq, hm.2.2, hnl_head]
      exact ⟨htail ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hlt).1, _, horig, Or.inl rfl⟩),
        hhead ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hlt).2, _, horig, Or.inr rfl⟩)⟩
    have hP_gv := forestPath_isPath hT_gv_st.1 (hT_gv_st.2.2 _ hGv_end_e'.1 _ hGv_end_e'.2)
    have hP_raw : T_raw.IsPath (G_v.tail e') (G_v.head e')
        (T_gv.forestPath (G_v.tail e') (G_v.head e')) :=
      ⟨isWalk_of_subgraph hT_sub_raw hP_gv.1,
        by rw [walkVertices_of_subgraph hT_sub_raw hP_gv.1]; exact hP_gv.2⟩
    exact forestPath_eq_of_isPath hT_raw_forest hP_raw
  have hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G.toMGraph ≤ f := by
    intro f hf hfnG
    rw [hT_raw_def] at hf; dsimp only at hf
    rw [Finset.mem_union] at hf
    rcases hf with hf1 | hf2
    · obtain ⟨_, _, _, rfl, _, _⟩ := hT_gv_nGv f hf1 hfnG
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    · rw [Finset.mem_image] at hf2
      obtain ⟨idx, _, rfl⟩ := hf2
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hT_raw_G : ∀ f ∈ T_raw.E, f ∈ G_v.E → T_raw.tail f = G_v.tail f ∧ T_raw.head f = G_v.head f := by
    intro f _ hfG
    have hflt : f < baseInact := Nat.lt_of_lt_of_le (lt_copyMod hfG)
      (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
    rw [hT_raw_def, hT_gv_def]; dsimp only
    rw [ite_eq_left hflt, ite_eq_left hflt, ite_eq_left hfG, ite_eq_left hfG]
    exact ⟨rfl, rfl⟩
  have hT_raw_paths : ∀ e' ∈ G_v.E,
      ∀ f ∈ walkEdges (T_raw.forestPath (G_v.tail e') (G_v.head e')), f ∈ G_v.E := by
    intro e' he' f hf
    rw [hT_raw_path_eq e' he'] at hf
    exact hT_gv_no_bridges e' he' hf
  have hE_nd : E_list.Nodup := copyEdgeList_nodup G mult
  have hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E := fun e' =>
    mem_copyEdgeList_iff hG_nl_eq hG_v_eq hnl_ne hmult
  have hE_len : E_list.length = G_v.E.card := by
    rw [← List.toFinset_card_of_nodup hE_nd]
    congr 1; ext x; rw [List.mem_toFinset, hE_mem]
  have hV_len_act : V_list.length = (activeVertsList G).length := by
    rw [← List.toFinset_card_of_nodup hV_nd, ← List.toFinset_card_of_nodup (activeVertsList_nodup G)]
    congr 1; ext x; simp only [List.mem_toFinset, hV_mem]
  have hact_bds := activeVertsList_card_bounds hG hnl_ne
  rw [← hV_len_act, hV_len_eq] at hact_bds
  have hB_len_lt : B.length + 1 ≤ G_v.E.card :=
    have hbl := isBridgeVerts_length_le hG_nl_eq hG_v_eq hnl_ne hv (hV_act) hr₀_act hB
    Nat.le_trans hbl.1 hbl.2
  have hGv_end : ∀ e' ∈ G_v.E, G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act := by
    intro e' he'
    have hm := weightedCopyGraph_origEdge_mem hnl_ne' (hG_v_eq ▸ he')
    have horig : origEdge (copyMod G_nl) e' ∈ nonloopEdges G := by
      have h1 := hm.1; rw [hnl_E] at h1; exact List.mem_toFinset.mp h1
    have hlt := (mem_nonloopEdges_iff.mp horig).1
    have htail : G_v.tail e' = G.tail (origEdge (copyMod G_nl) e') := by
      rw [hG_v_eq, hm.2.1, hnl_tail]
    have hhead : G_v.head e' = G.head (origEdge (copyMod G_nl) e') := by
      rw [hG_v_eq, hm.2.2, hnl_head]
    exact ⟨htail ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hlt).1, _, horig, Or.inl rfl⟩),
      hhead ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr ⟨(hG.2 _ hlt).2, _, horig, Or.inr rfl⟩)⟩
  let w_int : ℕ → ℕ := fun e' => w_orig (origEdge (copyMod G_nl) e')
  have horig_of : ∀ e' ∈ G_v.E, origEdge (copyMod G_nl) e' ∈ nonloopEdges G := fun e' he' => by
    have h1 := (weightedCopyGraph_origEdge_mem hnl_ne' (hG_v_eq ▸ he')).1
    rw [hnl_E] at h1; exact List.mem_toFinset.mp h1
  let edgeIdGv : ℕ → ℕ := fun j =>
    if hj : j < E_list.length then E_list[j]'hj else baseB + (j - E_list.length)
  have hsum_gv : ∑ e' ∈ G_v.E, treeStretch G_v T_raw (weightedCopyLen G_nl ℓ) e' ≤
      (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G_v.norm1 (fun _ => 1) :=
    an19_stretch_sum_bound_gen hG.1 (by omega) (by rw [← hV_len_eq]; omega)
      hV_len_eq (fun x => by rw [hV_mem, hV_act]) hGv_end hB_len_lt hE_len hE_nd hE_mem
      hδ_pos (fun e' he' => hw_orig_ge _ (horig_of e' he'))
      (fun e' he' => hℓ _ (Finset.mem_range.mpr (mem_nonloopEdges_iff.mp (horig_of e' he')).1))
      (fun e' he' => hℓ_upper _ (horig_of e' he'))
      (fun e' he' => hℓ_lower _ (horig_of e' he'))
      (fun e' he' => hδ_Vact _ (horig_of e' he'))
      (buildGAug_n G V_list B mult w_orig) (buildGAug_m G V_list B mult w_orig)
      (fun j hj => by
        simpa only [w_int, E_list] using buildGAug_edge_E (V_list := V_list) (B := B)
          (w_orig := w_orig) hG_nl_eq hG_v_eq hnl_ne j hj)
      (fun k hk => buildGAug_edge_B G V_list B mult w_orig k hk)
      hout_st.2.2.2 htot_st hK₁ hKAN
      (fun j hj => by rw [dite_eq_left hj]; exact (hE_mem _).mp (List.getElem_mem hj))
      (fun j hj => dite_eq_left hj)
      (fun k _ hnk hfGv => by
        rw [dite_eq_right hnk] at hfGv
        have hlt := lt_copyMod hfGv
        omega)
      hT_gv_V hT_gv_val hT_gv_st hT_gv_st.2.2 hT_gv_lift hT_gv_no_bridges hT_raw_path_eq
  have hlsst_raw : IsLSST G_v (weightedCopyLen G_nl ℓ) (fun _ => 1)
      ((2 * K₁ + 2) * (Real.log ((G.toMGraph.n : ℝ) + 2)) ^ 2) T_raw := by
    rw [IndexedGraph.toMGraph_n]
    exact ⟨hT_raw_st, hT_raw_G, hT_raw_paths, by simpa using hsum_gv⟩
  have hlsst_proj : IsLSST G.toMGraph ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2)
      (projectTree G_nl v T_raw) := by
    have hp := lsst_of_projectTree_gen (IndexedGraph.toMGraph_isValid hG)
      (IndexedGraph.toMGraph_V_nonempty hG) hK₁ hG_nl_def hG_v_eq hnl_ne' hℓ hv
      hT_raw_nonGv hlsst_raw
    rwa [IndexedGraph.toMGraph_n] at hp
  exact ⟨hGv_V, horig_of, hT_gv_nGv, hT_raw_nonGv, hE_mem, hlsst_proj⟩

theorem concreteLSST_isLSST {G : IndexedGraph} {ℓ v : ℕ → ℝ} {V_act : Finset ℕ}
    {V_list B out : List ℕ} {mult w_orig : ℕ → ℕ} {δ K_AN K₁ : ℝ}
    (hG : G.Valid)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hℓ : ∀ e ∈ G.toMGraph.E, 0 < ℓ e)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_nd : V_list.Nodup)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts (weightedCopyGraph { G.toMGraph with E := (nonloopEdges G).toFinset } v)
      V_act (V_list.headD 0) B)
    (hmult : ∀ e ∈ nonloopEdges G,
      mult e = edgeMult { G.toMGraph with E := (nonloopEdges G).toFinset } v e)
    (hδ_pos : 0 < δ)
    (hw_orig_ge : ∀ e ∈ nonloopEdges G, 4 ≤ w_orig e)
    (hℓ_upper : ∀ e ∈ nonloopEdges G, ℓ e ≤ δ * ((w_orig e : ℝ) + 1))
    (hℓ_lower : ∀ e ∈ nonloopEdges G, δ * (w_orig e : ℝ) ≤ ℓ e)
    (hδ_Vact : ∀ e ∈ nonloopEdges G, δ * (V_act.card : ℝ) ≤ ℓ e / 2)
    (hout_st : (buildGAug G V_list B mult w_orig).IsSpanningTree out)
    (htot_st : (buildGAug G V_list B mult w_orig).totalStretch out ≤
      K_AN * ((buildGAug G V_list B mult w_orig).m : ℝ) *
        Cited.logLogFactor (buildGAug G V_list B mult w_orig).n)
    (hK₁ : 1 ≤ K₁) (hKAN : K_AN ≤ K₁) :
    IsLSST G.toMGraph ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2)
      (concreteLSSTTree G V_list B mult out) := by
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  let G_v := weightedCopyGraph G_nl v
  let E_list := copyEdgeList G mult
  let baseB := copyMod G.toMGraph + copyMod G_v
  let baseInact := baseB + B.length
  let inact := inactiveVertsList G.n V_list
  let T_gv : MGraph :=
    { V := V_act
      E := out.toFinset.image (fun j =>
        if hj : j < E_list.length then E_list[j]'hj else baseB + (j - E_list.length))
      tail := fun f => if f ∈ G_v.E then G_v.tail f else V_list.headD 0
      head := fun f => if f ∈ G_v.E then G_v.head f else B.getD (f - baseB) 0 }
  let T_raw : MGraph :=
    { V := G_v.V
      E := T_gv.E ∪ (List.range inact.length).toFinset.image (fun idx => baseInact + idx)
      tail := fun f => if f < baseInact then T_gv.tail f else V_list.headD 0
      head := fun f => if f < baseInact then T_gv.head f else inact.getD (f - baseInact) 0 }
  obtain ⟨hGv_V, horig_of, hT_gv_nGv, hT_raw_nonGv, hE_mem, hlsst_proj⟩ :=
    traw_proj_lsst (G_nl := G_nl) (G_v := G_v) (T_gv := T_gv) (T_raw := T_raw)
      hG rfl rfl hnl_ne hℓ hv hV_nd hV_mem hV_act hB hmult hδ_pos hw_orig_ge hℓ_upper
      hℓ_lower hδ_Vact hout_st htot_st hK₁ hKAN rfl rfl
  have hne_list : (nonloopEdges G).isEmpty = false := by
    obtain ⟨e₀, he₀⟩ := hnl_ne
    rw [Bool.eq_false_iff]; intro h
    rw [List.isEmpty_iff] at h
    exact List.not_mem_nil (h ▸ List.mem_toFinset.mp he₀)
  have hconcrete_eq : concreteLSSTTree G V_list B mult out =
      decodedTree G.n G.m G.tail G.head
        (decodeAN19Output G V_list B mult out).1
        (decodeAN19Output G V_list B mult out).2 := by
    dsimp only [concreteLSSTTree]; rw [hne_list]; rfl
  rw [hconcrete_eq]
  exact projectTree_decoded_isLSST hG rfl rfl hnl_ne hout_st.1 hGv_V horig_of
    rfl hT_gv_nGv rfl hT_raw_nonGv hE_mem hlsst_proj

/-- Explicit deterministic LSST construction running `[AN19]`'s program `P_AN` on all-false
randomness (`fun _ => false`) for `fuel` steps and projecting the resulting tree back to `G`. -/
def concreteLSSTRun (P_AN : WordRAM.Program) (c_AN : ℕ) (G : IndexedGraph)
    (mult w_orig : ℕ → ℕ) (fuel : ℕ) : MGraph :=
  if (nonloopEdges G).isEmpty then
    decodedTree G.n G.m G.tail G.head [] ((List.range (G.n - 1)).map fun i => (0, i + 1))
  else
    let V_list := activeVertsList G
    let B := computeBridgeVerts G V_list
    let G_aug := buildGAug G V_list B mult w_orig
    let out := match WordRAM.run (WordRAM.wordSize c_AN G_aug.encode) P_AN (fun _ => false)
        G_aug.encode fuel with
      | some (out, _) => out
      | none => []
    concreteLSSTTree G V_list B mult out

theorem concreteLSSTRun_isLSST {G : IndexedGraph} {ℓ v : ℕ → ℝ} {K_AN K₁ : ℝ}
    {P_AN : WordRAM.Program} {c_AN fuel : ℕ} {mult w_orig : ℕ → ℕ} {δ : ℝ} {out : List ℕ} {cost : ℕ}
    (hG : G.Valid)
    (hℓ : ∀ e ∈ G.toMGraph.E, 0 < ℓ e)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hK₁ : 1 ≤ K₁) (hKAN : K_AN ≤ K₁)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty →
      (∀ e ∈ nonloopEdges G,
        mult e = edgeMult { G.toMGraph with E := (nonloopEdges G).toFinset } v e) ∧
      0 < δ ∧
      (∀ e ∈ nonloopEdges G, 4 ≤ w_orig e) ∧
      (∀ e ∈ nonloopEdges G, ℓ e ≤ δ * ((w_orig e : ℝ) + 1)) ∧
      (∀ e ∈ nonloopEdges G, δ * (w_orig e : ℝ) ≤ ℓ e) ∧
      (∀ e ∈ nonloopEdges G, δ * ((activeVertsList G).length : ℝ) ≤ ℓ e / 2) ∧
      let V_list := activeVertsList G
      let B := computeBridgeVerts G V_list
      let G_aug := buildGAug G V_list B mult w_orig
      WordRAM.run (WordRAM.wordSize c_AN G_aug.encode) P_AN (fun _ => false) G_aug.encode fuel =
        some (out, cost) ∧
      G_aug.IsSpanningTree out ∧
      G_aug.totalStretch out ≤ K_AN * (G_aug.m : ℝ) * Cited.logLogFactor G_aug.n) :
    IsLSST G.toMGraph ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2)
      (concreteLSSTRun P_AN c_AN G mult w_orig fuel) := by
  by_cases hne : (nonloopEdges G).toFinset.Nonempty
  · obtain ⟨hmult, hδ_pos, hw_ge, hℓ_up, hℓ_lo, hδ_V, hrun, hout_st, htot_st⟩ := hnl_ne hne
    have hnl_ne_list : (nonloopEdges G).isEmpty = false := by
      obtain ⟨e₀, he₀⟩ := hne
      rw [Bool.eq_false_iff]; intro h
      rw [List.isEmpty_iff] at h
      exact List.not_mem_nil (h ▸ List.mem_toFinset.mp he₀)
    let V_list := activeVertsList G
    let B := computeBridgeVerts G V_list
    have hV_ne : V_list ≠ [] := activeVertsList_nonempty_of_nonloop hG hne
    obtain ⟨r₀, rest, hVl⟩ := List.exists_cons_of_ne_nil hV_ne
    have hB := computeBridgeVerts_isBridgeVerts hG rfl rfl hne hv
      (fun _ => List.mem_toFinset.symm) hVl
    have hr₀_head : r₀ = V_list.headD 0 := by rw [hVl]; rfl
    have hB' : IsBridgeVerts
        (weightedCopyGraph { G.toMGraph with E := (nonloopEdges G).toFinset } v)
        V_list.toFinset (V_list.headD 0) B := by
      rw [← hr₀_head]
      exact hB
    have hcard_eq : V_list.toFinset.card = V_list.length :=
      List.toFinset_card_of_nodup (activeVertsList_nodup G)
    have hδ_V' : ∀ e ∈ nonloopEdges G, δ * (V_list.toFinset.card : ℝ) ≤ ℓ e / 2 := fun e he => by
      rw [hcard_eq]; exact hδ_V e he
    have hlsst := concreteLSST_isLSST hG hne hℓ hv (activeVertsList_nodup G)
      (fun _ => Iff.rfl) (fun _ => List.mem_toFinset.symm) hB' hmult hδ_pos hw_ge hℓ_up hℓ_lo
      hδ_V' hout_st htot_st hK₁ hKAN
    have hrun_eq : concreteLSSTRun P_AN c_AN G mult w_orig fuel =
        concreteLSSTTree G V_list B mult out := by
      dsimp only [concreteLSSTRun]
      rw [ite_eq_right (by rw [hnl_ne_list]; simp)]
      dsimp only [V_list, B]
      rw [hrun]
    rwa [hrun_eq]
  · have hloop : ∀ e ∈ G.toMGraph.E, G.toMGraph.tail e = G.toMGraph.head e := by
      intro e he
      by_contra hne_th
      exact hne ⟨e, List.mem_toFinset.mpr (mem_nonloopEdges_iff.mpr ⟨Finset.mem_range.mp he, hne_th⟩)⟩
    have hemp : (nonloopEdges G).isEmpty = true := by
      rw [List.isEmpty_iff]
      by_contra hne_list
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne_list
      exact hne ⟨e, List.mem_toFinset.mpr he⟩
    have hstar : concreteLSSTRun P_AN c_AN G mult w_orig fuel =
        decodedTree G.n G.m G.tail G.head [] ((List.range (G.n - 1)).map fun i => (0, i + 1)) := by
      dsimp only [concreteLSSTRun]; exact ite_eq_left (by simp [hemp])
    rw [hstar]
    exact lsst_star_no_nonloop hG hv hloop hK₁

end MinCostFlow.WideWord
