module

public import MinCostFlow.Machine.WideWord.LSSTGAug
public import WordRAM.Model
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

lemma isWalk_of_subgraph {G H : MGraph} (hsub : G.IsSubgraph H) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → G.IsWalk u v P
  | _, _, _, .nil s => .nil s
  | _, _, y :: _, .cons hyE hsy hrest => by
    have hm := hsub.2.2 y.1 hyE
    have hsrc : G.src y = H.src y := by
      cases y.2 <;> simp [MGraph.src, hm.1, hm.2]
    have hdst : G.dst y = H.dst y := by
      cases y.2 <;> simp [MGraph.dst, hm.1, hm.2]
    exact .cons (hsub.2.1 hyE) (hsrc.trans hsy) (hdst ▸ isWalk_of_subgraph hsub hrest)

lemma walkVertices_of_subgraph {G H : MGraph} (hsub : G.IsSubgraph H) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → G.walkVertices u P = H.walkVertices u P
  | u, _, P, hW => by
    dsimp only [MGraph.walkVertices]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    have hm := hsub.2.2 x.1 (IsWalk_edges_mem hW hx)
    cases x.2 <;> simp [MGraph.dst, hm.1, hm.2]

open Classical in
lemma tgV_props {G : IndexedGraph} {v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v : MGraph} {V_list B out : List ℕ} {mult w_orig : ℕ → ℕ}
    (hG : G.Valid)
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_nd : V_list.Nodup)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts G_v V_act (V_list.headD 0) B)
    (hmult : ∀ e ∈ nonloopEdges G, mult e = edgeMult G_nl v e)
    (hout_st : (buildGAug G V_list B mult w_orig).IsSpanningTree out) :
    let E_list := copyEdgeList G mult
    let baseB := copyMod G.toMGraph + copyMod G_v
    let edgeIdGv : ℕ → ℕ := fun j =>
      if hj : j < E_list.length then E_list[j]'hj else baseB + (j - E_list.length)
    let T_gv : MGraph :=
      { V := V_act
        E := out.toFinset.image edgeIdGv
        tail := fun f => if f ∈ G_v.E then G_v.tail f else V_list.headD 0
        head := fun f => if f ∈ G_v.E then G_v.head f else B.getD (f - baseB) 0 }
    T_gv.V = V_act ∧
    T_gv.IsValid ∧
    T_gv.IsSpanningTreeOn V_act ∧
    (∀ f ∈ T_gv.E, f < baseB + B.length) ∧
    (∀ f ∈ T_gv.E, f ∉ G_v.E →
      ∃ k, k < B.length ∧ E_list.length + k ∈ out ∧
        f = baseB + k ∧ T_gv.tail f = V_list.headD 0 ∧ T_gv.head f = B.getD k 0) ∧
    (∀ {a b : ℕ} {es : List ℕ},
      (buildGAug G V_list B mult w_orig).IsWalkIn out a b es →
      ∀ u ∈ V_act, ∀ v' ∈ V_act, V_list.idxOf u = a → V_list.idxOf v' = b →
      ∃ P : List (ℕ × Bool), T_gv.IsWalk u v' P ∧ P.map Prod.fst = es.map edgeIdGv) ∧
    (∀ e' ∈ G_v.E, walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E) := by
  intro E_list baseB edgeIdGv T_gv
  have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
  have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl_eq]
  have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
  have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
  have hV_ne : V_list ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (activeVertsList_nonempty_of_nonloop hG hnl_ne)
    exact List.ne_nil_of_mem ((hV_mem x).mpr hx)
  have hlen_pos : 0 < V_list.length := List.length_pos_of_ne_nil hV_ne
  let r₀ := V_list.headD 0
  have hr₀_eq : r₀ = V_list[0]'hlen_pos := headD_eq_getElem_zero V_list hlen_pos
  have hr₀_mem : r₀ ∈ V_list := hr₀_eq ▸ List.getElem_mem hlen_pos
  have hr₀_act : r₀ ∈ V_act := (hV_act r₀).mp ((hV_mem r₀).mp hr₀_mem)
  have hidx0 : V_list.idxOf r₀ = 0 := by
    rw [hr₀_eq]; exact idxOf_getElem_of_nodup hV_nd hlen_pos
  have hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E := fun e' =>
    mem_copyEdgeList_iff hG_nl_eq hG_v_eq hnl_ne hmult
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
    exact ⟨htail ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr
        ⟨(hG.2 _ hlt).1, _, horig, Or.inl rfl⟩),
      hhead ▸ (hV_act _).mp (mem_activeVertsList_iff.mpr
        ⟨(hG.2 _ hlt).2, _, horig, Or.inr rfl⟩)⟩
  have hlt_baseB : ∀ f ∈ G_v.E, f < baseB := fun f hf =>
    Nat.lt_of_lt_of_le (lt_copyMod hf) (Nat.le_add_left _ _)
  have hE_lt : ∀ j (hj : j < E_list.length), edgeIdGv j ∈ G_v.E := fun j hj => by
    dsimp only [edgeIdGv]; rw [dite_eq_left hj]; exact (hE_mem _).mp (List.getElem_mem hj)
  have hB_ge : ∀ j, ¬ j < E_list.length → edgeIdGv j ∉ G_v.E := fun j hnj hf => by
    dsimp only [edgeIdGv] at hf
    rw [dite_eq_right hnj] at hf
    exact Nat.not_lt_of_ge (Nat.le_add_right baseB _) (hlt_baseB _ hf)
  have hT_val : T_gv.IsValid := by
    intro f hf
    dsimp only [T_gv] at hf ⊢
    rw [Finset.mem_image] at hf
    obtain ⟨j, hj_out, rfl⟩ := hf
    have hj_mem : j ∈ out := List.mem_toFinset.mp hj_out
    have hj_m : j < E_list.length + B.length := by
      have h := hout_st.2.1 j hj_mem
      rwa [buildGAug_m] at h
    by_cases hjl : j < E_list.length
    · have hfG := hE_lt j hjl
      rw [ite_eq_left hfG, ite_eq_left hfG]
      exact hGv_end _ hfG
    · have hfnG := hB_ge j hjl
      have hjB : j - E_list.length < B.length := by omega
      have hfeq : edgeIdGv j = baseB + (j - E_list.length) := dite_eq_right hjl
      rw [ite_eq_right hfnG, ite_eq_right hfnG, hfeq, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ hjB]
      exact ⟨hr₀_act, hB.2.1 _ (List.getElem_mem hjB)⟩
  have hT_lift : ∀ {a b : ℕ} {es : List ℕ},
      (buildGAug G V_list B mult w_orig).IsWalkIn out a b es →
      ∀ u ∈ V_act, ∀ v' ∈ V_act, V_list.idxOf u = a → V_list.idxOf v' = b →
      ∃ P : List (ℕ × Bool), T_gv.IsWalk u v' P ∧ P.map Prod.fst = es.map edgeIdGv := by
    intro a b es hW
    induction hW with
    | nil s =>
      intro u hu v' hv' ha hb
      have huv : u = v' := idxOf_inj_of_mem ((hV_mem u).mpr ((hV_act u).mpr hu))
        ((hV_mem v').mpr ((hV_act v').mpr hv')) (ha.trans hb.symm)
      subst huv
      exact ⟨[], .nil _, rfl⟩
    | @cons u_i x_i b_i k ks hkout hkm hpair _ ih =>
      intro u hu v' hv' ha hb
      have hmult_pos : ∀ e ∈ nonloopEdges G, 1 ≤ mult e := fun e he => by
        rw [hmult e he]
        exact edgeMult_pos hnl_ne' (fun g hg =>
          hv g (Finset.mem_range.mpr (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp
            (hnl_E ▸ hg))).1)) (hnl_E ▸ List.mem_toFinset.mpr he)
      have hval_aug := buildGAug_graph_isValid (mult := mult) (w_orig := w_orig) hG hnl_ne hV_mem hV_act hB
      have hkx_lt : k < (buildGAug G V_list B mult w_orig).edges.length := hkm
      have hedge_mem : ((buildGAug G V_list B mult w_orig).edges[k].1,
          (buildGAug G V_list B mult w_orig).edges[k].2.1) ∈
          (buildGAug G V_list B mult w_orig).graph.edges :=
        List.mem_map.mpr ⟨_, List.getElem_mem hkx_lt, rfl⟩
      have hend_lt := hval_aug _ hedge_mem
      have hx_lt : x_i < V_list.length := by
        rcases hpair with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [rw [← h2]; rw [← h1]] <;>
          [exact hend_lt.2; exact hend_lt.1]
      let x := V_list[x_i]'hx_lt
      have hx_act : x ∈ V_act := (hV_act _).mp ((hV_mem _).mp (List.getElem_mem hx_lt))
      have hx_idx : V_list.idxOf x = x_i := idxOf_getElem_of_nodup hV_nd hx_lt
      obtain ⟨P', hWP', hmap'⟩ := ih x hx_act v' hv' hx_idx hb
      let f := edgeIdGv k
      have hfT : f ∈ T_gv.E := Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hkout)
      have hf_endpoints :
          (buildGAug G V_list B mult w_orig).edges[k].1 = V_list.idxOf (T_gv.tail f) ∧
          (buildGAug G V_list B mult w_orig).edges[k].2.1 = V_list.idxOf (T_gv.head f) ∧
          T_gv.tail f ∈ V_act ∧ T_gv.head f ∈ V_act := by
        by_cases hkl : k < E_list.length
        · have hf_eq : f = E_list[k]'hkl := dite_eq_left hkl
          have hfG : f ∈ G_v.E := hf_eq ▸ (hE_mem _).mp (List.getElem_mem hkl)
          have hge := buildGAug_edge_E (V_list := V_list) (B := B) (w_orig := w_orig)
            hG_nl_eq hG_v_eq hnl_ne k hkl
          have hged_k : (buildGAug G V_list B mult w_orig).edges[k] =
              (V_list.idxOf (G_v.tail f), V_list.idxOf (G_v.head f),
                w_orig (origEdge (copyMod G_nl) f)) := by
            simpa [E_list, hf_eq] using hge
          have htf : T_gv.tail f = G_v.tail f := by dsimp [T_gv]; exact ite_eq_left hfG
          have hhf : T_gv.head f = G_v.head f := by dsimp [T_gv]; exact ite_eq_left hfG
          rw [hged_k, htf, hhf]
          exact ⟨rfl, rfl, hGv_end f hfG⟩
        · have hkm' : k < E_list.length + B.length := by rwa [buildGAug_m] at hkm
          have hkB : k - E_list.length < B.length := by omega
          have hf_eq : f = baseB + (k - E_list.length) := dite_eq_right hkl
          have hfnG : f ∉ G_v.E := hB_ge k hkl
          have hgb := buildGAug_edge_B G V_list B mult w_orig (k - E_list.length) hkB
          have hadd : E_list.length + (k - E_list.length) = k := by omega
          have hged_k : (buildGAug G V_list B mult w_orig).edges[k] =
              (0, V_list.idxOf (B[k - E_list.length]'hkB), 1) := by
            simpa only [E_list, hadd] using hgb
          have htf : T_gv.tail f = r₀ := by dsimp [T_gv]; exact ite_eq_right hfnG
          have hhf : T_gv.head f = B[k - E_list.length]'hkB := by
            dsimp [T_gv]; rw [ite_eq_right hfnG, hf_eq, Nat.add_sub_cancel_left]
            exact List.getD_eq_getElem _ _ hkB
          rw [hged_k, htf, hhf, hidx0]
          exact ⟨rfl, rfl, hr₀_act, hB.2.1 _ (List.getElem_mem hkB)⟩
      rcases hf_endpoints with ⟨he1, he2, htfV, hhfV⟩
      have injV : ∀ p q, p ∈ V_act → q ∈ V_act → V_list.idxOf p = V_list.idxOf q → p = q :=
        fun p q hp hq => idxOf_inj_of_mem ((hV_mem p).mpr ((hV_act p).mpr hp))
          ((hV_mem q).mpr ((hV_act q).mpr hq))
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have htu : T_gv.tail f = u := injV _ _ htfV hu (he1.symm.trans (h1.trans ha.symm))
        have hhx : T_gv.head f = x := injV _ _ hhfV hx_act (he2.symm.trans (h2.trans hx_idx.symm))
        refine ⟨(f, true) :: P', .cons hfT (by simp [MGraph.src, htu])
          (by simp [MGraph.dst, hhx]; exact hWP'), by simp [f, hmap']⟩
      · have htx : T_gv.tail f = x := injV _ _ htfV hx_act (he1.symm.trans (h1.trans hx_idx.symm))
        have hhu : T_gv.head f = u := injV _ _ hhfV hu (he2.symm.trans (h2.trans ha.symm))
        refine ⟨(f, false) :: P', .cons hfT (by simp [MGraph.src, hhu])
          (by simp [MGraph.dst, htx]; exact hWP'), by simp [f, hmap']⟩
  have hT_conn : ∀ u ∈ V_act, ∀ v' ∈ V_act, T_gv.Connected u v' := by
    intro u hu v' hv'
    have hu_lt : V_list.idxOf u < (buildGAug G V_list B mult w_orig).n :=
      List.idxOf_lt_length_of_mem ((hV_mem u).mpr ((hV_act u).mpr hu))
    have hv_lt : V_list.idxOf v' < (buildGAug G V_list B mult w_orig).n :=
      List.idxOf_lt_length_of_mem ((hV_mem v').mpr ((hV_act v').mpr hv'))
    obtain ⟨es, hes⟩ := hout_st.2.2.2 _ hu_lt _ hv_lt
    obtain ⟨P, hWP, _⟩ := hT_lift hes u hu v' hv' rfl rfl
    exact ⟨P, hWP⟩
  have hT_card : T_gv.E.card ≤ T_gv.V.card - 1 := by
    have hV_eq_set : V_list.toFinset = V_act := by
      ext x; rw [List.mem_toFinset, hV_mem, hV_act]
    dsimp only [T_gv]
    calc (out.toFinset.image edgeIdGv).card ≤ out.toFinset.card := Finset.card_image_le
      _ ≤ out.length := List.toFinset_card_le _
      _ = V_list.length - 1 := hout_st.2.2.1
      _ = V_act.card - 1 := by rw [← List.toFinset_card_of_nodup hV_nd, hV_eq_set]
  have hT_forest : T_gv.IsForest :=
    isForest_of_connected_card_le hT_val ⟨r₀, hr₀_act⟩ hT_conn hT_card
  have hT_st : T_gv.IsSpanningTreeOn V_act := ⟨hT_forest, rfl, hT_conn⟩
  have hT_lt_bound : ∀ f ∈ T_gv.E, f < baseB + B.length := by
    intro f hf
    dsimp only [T_gv] at hf
    rw [Finset.mem_image] at hf
    obtain ⟨j, hj, rfl⟩ := hf
    have hj_m : j < E_list.length + B.length := by
      have h := hout_st.2.1 j (List.mem_toFinset.mp hj)
      rwa [buildGAug_m] at h
    by_cases hjl : j < E_list.length
    · exact Nat.lt_of_lt_of_le (hlt_baseB _ (hE_lt j hjl)) (Nat.le_add_right _ _)
    · dsimp only [edgeIdGv]; rw [dite_eq_right hjl]; omega
  have hT_nGv : ∀ f ∈ T_gv.E, f ∉ G_v.E →
      ∃ k, k < B.length ∧ E_list.length + k ∈ out ∧
        f = baseB + k ∧ T_gv.tail f = r₀ ∧ T_gv.head f = B.getD k 0 := by
    intro f hf hfnG
    dsimp only [T_gv] at hf ⊢
    rw [Finset.mem_image] at hf
    obtain ⟨j, hj, rfl⟩ := hf
    have hj_mem : j ∈ out := List.mem_toFinset.mp hj
    have hj_m : j < E_list.length + B.length := by
      have h := hout_st.2.1 j hj_mem
      rwa [buildGAug_m] at h
    have hnj : ¬ j < E_list.length := fun hjl => hfnG (hE_lt j hjl)
    have hfeq : edgeIdGv j = baseB + (j - E_list.length) := dite_eq_right hnj
    refine ⟨j - E_list.length, by omega, by rwa [show E_list.length + (j - E_list.length) = j by omega],
      hfeq, ite_eq_right hfnG, ?_⟩
    rw [ite_eq_right hfnG, hfeq, Nat.add_sub_cancel_left]
  have hno_bridges : ∀ e' ∈ G_v.E,
      walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E := by
    intro e' he' f hf
    by_contra hfnG
    have he'_V := hGv_end e' he'
    have hP_path : T_gv.IsPath (G_v.tail e') (G_v.head e')
        (T_gv.forestPath (G_v.tail e') (G_v.head e')) :=
      forestPath_isPath hT_forest (hT_conn _ he'_V.1 _ he'_V.2)
    obtain ⟨dir, hdir⟩ := mem_walkEdges_iff.mp hf
    have hfT : f ∈ T_gv.E := IsWalk_edges_mem hP_path.1 hdir
    obtain ⟨k, hkB, _, rfl, _, _⟩ := hT_nGv f hfT hfnG
    let b := B[k]'hkB
    let S := V_act.filter fun x => G_v.Connected b x
    have hend_e' : G_v.Connected (G_v.tail e') (G_v.head e') :=
      ⟨[(e', true)], .cons he' (by simp [MGraph.src]) (by simp [MGraph.dst]; exact .nil _)⟩
    have hside : G_v.tail e' ∈ S ↔ G_v.head e' ∈ S := by
      simp only [S, Finset.mem_filter, he'_V.1, he'_V.2, true_and]
      exact ⟨fun h => connected_trans h hend_e', fun h => connected_trans h (connected_symm hend_e')⟩
    have hother : ∀ g ∈ walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')),
        g ≠ baseB + k → (T_gv.tail g ∈ S ↔ T_gv.head g ∈ S) := by
      intro g hg hne
      obtain ⟨d, hd⟩ := mem_walkEdges_iff.mp hg
      have hgT : g ∈ T_gv.E := IsWalk_edges_mem hP_path.1 hd
      by_cases hgG : g ∈ G_v.E
      · have hg_V := hGv_end g hgG
        have hconn_g : G_v.Connected (G_v.tail g) (G_v.head g) :=
          ⟨[(g, true)], .cons hgG (by simp [MGraph.src]) (by simp [MGraph.dst]; exact .nil _)⟩
        have htg : T_gv.tail g = G_v.tail g := by dsimp [T_gv]; exact ite_eq_left hgG
        have hhg : T_gv.head g = G_v.head g := by dsimp [T_gv]; exact ite_eq_left hgG
        rw [htg, hhg]
        simp only [S, Finset.mem_filter, hg_V.1, hg_V.2, true_and]
        exact ⟨fun h => connected_trans h hconn_g,
          fun h => connected_trans h (connected_symm hconn_g)⟩
      · obtain ⟨k', hk'B, _, rfl, htg, hhg⟩ := hT_nGv g hgT hgG
        have hk_ne : k' ≠ k := fun h => hne (by rw [h])
        have hb'_ne_b : B[k']'hk'B ≠ b := fun h => hk_ne ((List.Nodup.getElem_inj hB.1).mp h)
        have hb_mem : b ∈ B := List.getElem_mem hkB
        have hb'_mem : B[k']'hk'B ∈ B := List.getElem_mem hk'B
        have hbr₀ : ¬ G_v.Connected b r₀ :=
          hB.2.2.2.2 b (List.mem_cons_of_mem _ hb_mem) r₀ List.mem_cons_self
            fun h => hB.2.2.1 (by dsimp only [r₀] at h; rw [← h]; exact hb_mem)
        have hbb' : ¬ G_v.Connected b (B[k']'hk'B) :=
          hB.2.2.2.2 b (List.mem_cons_of_mem _ hb_mem)
            (B[k']'hk'B) (List.mem_cons_of_mem _ hb'_mem) hb'_ne_b.symm
        rw [htg, hhg, List.getD_eq_getElem _ _ hk'B]
        simp only [S, Finset.mem_filter, hbr₀, hbb', and_false]
    have hcut : ¬ (T_gv.tail (baseB + k) ∈ S ↔ T_gv.head (baseB + k) ∈ S) := by
      have htf : T_gv.tail (baseB + k) = r₀ := by dsimp [T_gv]; exact ite_eq_right hfnG
      have hhf : T_gv.head (baseB + k) = b := by
        dsimp [T_gv]; rw [ite_eq_right hfnG, Nat.add_sub_cancel_left]
        exact List.getD_eq_getElem _ _ hkB
      have hb_mem : b ∈ B := List.getElem_mem hkB
      have hbr₀ : ¬ G_v.Connected b r₀ :=
        hB.2.2.2.2 b (List.mem_cons_of_mem _ hb_mem) r₀ List.mem_cons_self
          fun h => hB.2.2.1 (by dsimp only [r₀] at h; rw [← h]; exact hb_mem)
      have hbb : G_v.Connected b b := connected_refl G_v b
      rw [htf, hhf]
      simp [S, hbr₀, hbb, hB.2.1 b hb_mem]
    exact isPath_no_unique_cut_edge hP_path hside hother hcut hf
  exact ⟨rfl, hT_val, hT_st, hT_lt_bound, hT_nGv, hT_lift, hno_bridges⟩

lemma projectTree_decoded_isLSST {G : IndexedGraph} {ℓ v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v T_gv T_raw : MGraph} {V_list B out : List ℕ} {mult : ℕ → ℕ} {γ : ℝ}
    (hG : G.Valid) (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hout_nd : out.Nodup)
    (hGv_V : G_v.V = Finset.range G.n)
    (horig_of : ∀ e' ∈ G_v.E, origEdge (copyMod G_nl) e' ∈ nonloopEdges G)
    (hT_gv_def : T_gv =
      { V := V_act
        E := out.toFinset.image (fun j =>
          if hj : j < (copyEdgeList G mult).length then (copyEdgeList G mult)[j]'hj
          else (copyMod G.toMGraph + copyMod G_v) + (j - (copyEdgeList G mult).length))
        tail := fun f => if f ∈ G_v.E then G_v.tail f else V_list.headD 0
        head := fun f => if f ∈ G_v.E then G_v.head f else
          B.getD (f - (copyMod G.toMGraph + copyMod G_v)) 0 })
    (hT_gv_nGv : ∀ f ∈ T_gv.E, f ∉ G_v.E →
      ∃ k, k < B.length ∧ (copyEdgeList G mult).length + k ∈ out ∧
        f = (copyMod G.toMGraph + copyMod G_v) + k ∧
        T_gv.tail f = V_list.headD 0 ∧ T_gv.head f = B.getD k 0)
    (hT_raw_def : T_raw =
      { V := G_v.V
        E := T_gv.E ∪ (List.range (inactiveVertsList G.n V_list).length).toFinset.image
          (fun idx => (copyMod G.toMGraph + copyMod G_v + B.length) + idx)
        tail := fun f => if f < (copyMod G.toMGraph + copyMod G_v + B.length) then T_gv.tail f
          else V_list.headD 0
        head := fun f => if f < (copyMod G.toMGraph + copyMod G_v + B.length) then T_gv.head f
          else (inactiveVertsList G.n V_list).getD
            (f - (copyMod G.toMGraph + copyMod G_v + B.length)) 0 })
    (hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G.toMGraph ≤ f)
    (hE_mem : ∀ e', e' ∈ copyEdgeList G mult ↔ e' ∈ G_v.E)
    (hlsst_proj : IsLSST G.toMGraph ℓ v γ (projectTree G_nl v T_raw)) :
    let res := decodeAN19Output G V_list B mult out
    IsLSST G.toMGraph ℓ v γ (decodedTree G.n G.m G.tail G.head res.1 res.2) := by
  intro res
  let E_list := copyEdgeList G mult
  let baseB := copyMod G.toMGraph + copyMod G_v
  let baseInact := baseB + B.length
  let inact := inactiveVertsList G.n V_list
  let r₀ := V_list.headD 0
  have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
  have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl_eq]
  have hproj_left : ∀ x ∈ G_v.E, projectEdge G_nl v x = origEdge (copyMod G_nl) x := by
    intro x hx; rw [hG_v_eq] at hx; dsimp [projectEdge]; exact ite_eq_left hx
  have hproj_right : ∀ x, x ∉ G_v.E → projectEdge G_nl v x = x + copyMod G_nl := by
    intro x hx; rw [hG_v_eq] at hx; dsimp [projectEdge]; exact ite_eq_right hx
  let bridgeOutIdx := out.filter fun j =>
    decide (E_list.length ≤ j ∧ j < E_list.length + B.length)
  let C₁ := copyMod G_nl + baseB
  let C₂ := copyMod G_nl + baseInact
  let φ : ℕ → ℕ := fun f' =>
    if f' < G.m then f'
    else if f' < C₂ then G.m + bridgeOutIdx.idxOf (E_list.length + (f' - C₁))
    else G.m + bridgeOutIdx.length + (f' - C₂)
  let T₁ := projectTree G_nl v T_raw
  let T₂ := decodedTree G.n G.m G.tail G.head res.1 res.2
  have hGm_pos : 0 < G.m := by
    obtain ⟨e₀, he₀⟩ := hnl_ne
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp he₀)).1
  have hGm_le_cG : G.m ≤ copyMod G.toMGraph := by
    have hlt := lt_copyMod (show G.m - 1 ∈ G.toMGraph.E from Finset.mem_range.mpr (by omega))
    omega
  have hcGnl_pos : 1 ≤ copyMod G_nl := by
    obtain ⟨e₀, he₀⟩ := hnl_ne'
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_copyMod he₀))
  have hGm_lt_C₁ : G.m < C₁ := by dsimp only [C₁, baseB]; omega
  have hOrigMap' : E_list.map (origEdge (copyMod G_nl)) = origOfCopy G mult := by
    dsimp only [E_list]
    rw [hG_nl_eq]
    exact origOfCopy_eq_map G mult
  have hm₁_eq : ((nonloopEdges G).map mult).sum = E_list.length := (copyEdgeList_length G mult).symm
  have hT₁_eq : ∀ f, f ∈ T₁.E ↔ ∃ x ∈ T_raw.E, projectEdge G_nl v x = f := by
    intro f; dsimp only [T₁, projectTree]; rw [ite_eq_left hnl_ne', Finset.mem_image]
  have hres2_len : res.2.length = bridgeOutIdx.length + inact.length := by
    dsimp only [res, decodeAN19Output, bridgeOutIdx, inact]
    simp [hm₁_eq]
  have hbridge_nd : bridgeOutIdx.Nodup := List.Nodup.filter _ hout_nd
  have hT₁_V : T₂.V = T₁.V := by
    dsimp only [T₁, projectTree, T₂, decodedTree]
    rw [ite_eq_left hnl_ne']
    dsimp only
    rw [hT_raw_def]
    exact hGv_V.symm
  refine isLSST_of_edgeMap (φ := φ) (IndexedGraph.toMGraph_isValid hG) hT₁_V ?_ ?_ ?_ ?_ ?_ hlsst_proj
  · -- hmem
    intro f' hf'
    rw [hT₁_eq] at hf'
    obtain ⟨x, hx, rfl⟩ := hf'
    by_cases hxG : x ∈ G_v.E
    · have hp_eq : projectEdge G_nl v x = origEdge (copyMod G_nl) x := hproj_left x hxG
      have horig_lt : origEdge (copyMod G_nl) x < G.m :=
        (mem_nonloopEdges_iff.mp (horig_of x hxG)).1
      rw [hp_eq]
      dsimp only [φ]; rw [ite_eq_left horig_lt]
      rw [hT_raw_def] at hx; dsimp only at hx
      rw [Finset.mem_union] at hx
      rcases hx with hx1 | hx2
      · rw [hT_gv_def] at hx1; dsimp only at hx1
        rw [Finset.mem_image] at hx1
        obtain ⟨j, hj_out, rfl⟩ := hx1
        have hj_mem := List.mem_toFinset.mp hj_out
        have hjl : j < E_list.length := by
          by_contra hnj
          have hx' := hxG
          rw [dite_eq_right hnj] at hx'
          have hlt := lt_copyMod hx'
          omega
        dsimp only [T₂, decodedTree]
        refine Finset.mem_union_left _ (List.mem_toFinset.mpr ?_)
        dsimp only [res, decodeAN19Output]
        rw [List.mem_map]
        refine ⟨j, List.mem_filter.mpr ⟨hj_mem, by simpa [hm₁_eq] using hjl⟩, ?_⟩
        rw [List.getD_eq_getElem _ _ (by rw [origOfCopy_length]; exact hjl)]
        have hget : (origOfCopy G mult)[j]'(by rw [origOfCopy_length]; exact hjl) =
            origEdge (copyMod G_nl) (E_list[j]'hjl) := by
          have h1 : (origOfCopy G mult)[j]'(by rw [origOfCopy_length]; exact hjl) =
              (E_list.map (origEdge (copyMod G_nl)))[j]'(by rw [List.length_map]; exact hjl) := by
            congr 1; exact hOrigMap'.symm
          rw [h1, List.getElem_map]
        change (origOfCopy G mult)[j]'(by rw [origOfCopy_length]; exact hjl) = _
        rw [hget, dite_eq_left hjl]
      · exfalso
        rw [Finset.mem_image] at hx2
        obtain ⟨idx, _, rfl⟩ := hx2
        have hlt := lt_copyMod hxG
        omega
    · have hp_eq : projectEdge G_nl v x = x + copyMod G_nl := hproj_right x hxG
      have hx' : x ∈ T_gv.E ∪ (List.range inact.length).toFinset.image (fun idx => baseInact + idx) := by
        rw [hT_raw_def] at hx; exact hx
      rw [Finset.mem_union] at hx'
      rcases hx' with hx1 | hx2
      · obtain ⟨k, hkB, hkout, rfl, _, _⟩ := hT_gv_nGv x hx1 hxG
        have heq_f' : projectEdge G_nl v (baseB + k) = C₁ + k := by
          rw [hp_eq]; dsimp [C₁]; omega
        have hf'_ge : ¬ C₁ + k < G.m := by dsimp [C₁]; omega
        have hf'_lt : C₁ + k < C₂ := by dsimp [C₂, baseInact, C₁]; omega
        have hjk : E_list.length + k ∈ bridgeOutIdx := by
          rw [List.mem_filter]; refine ⟨hkout, ?_⟩
          simp; omega
        have hidx_lt : bridgeOutIdx.idxOf (E_list.length + k) < res.2.length := by
          rw [hres2_len]
          exact Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hjk) (Nat.le_add_right _ _)
        rw [heq_f']; dsimp only [φ]
        rw [ite_eq_right hf'_ge, ite_eq_left hf'_lt, show C₁ + k - C₁ = k by omega]
        dsimp only [T₂, decodedTree]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (List.mem_toFinset.mpr (List.mem_range.mpr hidx_lt)))
      · rw [Finset.mem_image] at hx2
        obtain ⟨idx, hidx, rfl⟩ := hx2
        have hidx_lt : idx < inact.length := List.mem_range.mp (List.mem_toFinset.mp hidx)
        have heq_f' : projectEdge G_nl v (baseInact + idx) = C₂ + idx := by
          rw [hp_eq]; dsimp [C₂]; omega
        have hf'_ge : ¬ C₂ + idx < G.m := by dsimp [C₂, baseInact, C₁] at *; omega
        have hf'_nlt : ¬ C₂ + idx < C₂ := by omega
        have hidx_len : bridgeOutIdx.length + idx < res.2.length := by
          rw [hres2_len]; omega
        rw [heq_f']; dsimp only [φ]
        rw [ite_eq_right hf'_ge, ite_eq_right hf'_nlt, Nat.add_sub_cancel_left]
        dsimp only [T₂, decodedTree]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨bridgeOutIdx.length + idx, List.mem_toFinset.mpr (List.mem_range.mpr hidx_len), by omega⟩)
  · -- hsurj
    intro f' hf'
    dsimp only [T₂, decodedTree] at hf'
    rw [Finset.mem_union] at hf'
    rcases hf' with h_orig | h_br
    · rw [List.mem_toFinset] at h_orig
      dsimp only [res, decodeAN19Output] at h_orig
      rw [List.mem_map] at h_orig
      obtain ⟨j, hjf, rfl⟩ := h_orig
      rw [List.mem_filter] at hjf
      have hj_out := hjf.1
      have hj_lt : j < E_list.length := by simpa [hm₁_eq] using hjf.2
      let x := E_list[j]'hj_lt
      have hx_gv : x ∈ G_v.E := (hE_mem _).mp (List.getElem_mem hj_lt)
      have hx_gv_E : x ∈ T_gv.E := by
        rw [hT_gv_def]; exact Finset.mem_image.mpr
          ⟨j, List.mem_toFinset.mpr hj_out, by dsimp [x]; exact dite_eq_left hj_lt⟩
      have hx_raw : x ∈ T_raw.E := by
        rw [hT_raw_def]; exact Finset.mem_union_left _ hx_gv_E
      have hmap_j : (origOfCopy G mult)[j]'(by rw [origOfCopy_length]; exact hj_lt) =
          origEdge (copyMod G_nl) x := by
        have h1 : (origOfCopy G mult)[j]'(by rw [origOfCopy_length]; exact hj_lt) =
            (E_list.map (origEdge (copyMod G_nl)))[j]'(by rw [List.length_map]; exact hj_lt) := by
          congr 1; exact hOrigMap'.symm
        rw [h1, List.getElem_map]
      have hproj_x : projectEdge G_nl v x = (origOfCopy G mult).getD j 0 := by
        rw [hproj_left x hx_gv, List.getD_eq_getElem _ _ (by rw [origOfCopy_length]; exact hj_lt),
          hmap_j]
      have hlt_Gm : (origOfCopy G mult).getD j 0 < G.m := by
        rw [← hproj_x, hproj_left x hx_gv]; exact (mem_nonloopEdges_iff.mp (horig_of x hx_gv)).1
      refine ⟨projectEdge G_nl v x, (hT₁_eq _).mpr ⟨x, hx_raw, rfl⟩, ?_⟩
      dsimp only [φ]; rw [ite_eq_left (hproj_x ▸ hlt_Gm), hproj_x]
    · rw [Finset.mem_image] at h_br
      obtain ⟨p, hp, rfl⟩ := h_br
      have hp_lt : p < res.2.length := List.mem_range.mp (List.mem_toFinset.mp hp)
      rw [hres2_len] at hp_lt
      by_cases hpb : p < bridgeOutIdx.length
      · let j := bridgeOutIdx[p]'hpb
        have hj_mem : j ∈ bridgeOutIdx := List.getElem_mem hpb
        have hjf := List.mem_filter.mp hj_mem
        have hj_out : j ∈ out := hjf.1
        have hj_bds : E_list.length ≤ j ∧ j < E_list.length + B.length := by
          simpa using hjf.2
        let k := j - E_list.length
        have hkB : k < B.length := by omega
        let x := baseB + k
        have hx_gv : x ∉ G_v.E := by
          intro h
          have hlt := lt_copyMod h
          dsimp only [x, baseB] at hlt
          omega
        have hx_gv_E : x ∈ T_gv.E := by
          rw [hT_gv_def]; refine Finset.mem_image.mpr ⟨j, List.mem_toFinset.mpr hj_out, ?_⟩
          have hnj : ¬ j < E_list.length := by omega
          rw [dite_eq_right hnj]
        have hx_raw : x ∈ T_raw.E := by
          rw [hT_raw_def]; exact Finset.mem_union_left _ hx_gv_E
        have hp_eq : projectEdge G_nl v x = C₁ + k := by
          rw [hproj_right x hx_gv]; dsimp [C₁, x]; omega
        refine ⟨projectEdge G_nl v x, (hT₁_eq _).mpr ⟨x, hx_raw, rfl⟩, ?_⟩
        rw [hp_eq]; dsimp only [φ]
        have hge : ¬ C₁ + k < G.m := by dsimp [C₁]; omega
        have hlt : C₁ + k < C₂ := by dsimp [C₂, baseInact, C₁]; omega
        rw [ite_eq_right hge, ite_eq_left hlt,
          show C₁ + k - C₁ = k by omega, show E_list.length + k = j by omega,
          idxOf_getElem_of_nodup hbridge_nd hpb]
      · let idx := p - bridgeOutIdx.length
        have hidx_lt : idx < inact.length := by omega
        let x := baseInact + idx
        have hx_gv : x ∉ G_v.E := by
          intro h
          have hlt := lt_copyMod h
          dsimp only [x, baseInact, baseB] at hlt
          omega
        have hx_raw : x ∈ T_raw.E := by
          rw [hT_raw_def]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
            (List.mem_toFinset.mpr (List.mem_range.mpr hidx_lt)))
        have hp_eq : projectEdge G_nl v x = C₂ + idx := by
          rw [hproj_right x hx_gv]; dsimp [C₂, x]; omega
        refine ⟨projectEdge G_nl v x, (hT₁_eq _).mpr ⟨x, hx_raw, rfl⟩, ?_⟩
        rw [hp_eq]; dsimp only [φ]
        have hge : ¬ C₂ + idx < G.m := by dsimp [C₂, baseInact, C₁]; omega
        have hnlt : ¬ C₂ + idx < C₂ := by omega
        rw [ite_eq_right hge, ite_eq_right hnlt, Nat.add_sub_cancel_left]
        omega
  · -- hfix
    intro f' _ hf'G
    have hf'_lt : f' < G.m := Finset.mem_range.mp hf'G
    dsimp only [φ]; exact ite_eq_left hf'_lt
  · -- hnotG
    intro f' _ hf'nG
    have hf'_nlt : ¬ f' < G.m := fun h => hf'nG (Finset.mem_range.mpr h)
    dsimp only [φ]
    rw [ite_eq_right hf'_nlt]
    by_cases hC₂ : f' < C₂
    · simp [hC₂, IndexedGraph.toMGraph]
    · simp [hC₂, IndexedGraph.toMGraph]; omega
  · -- hend
    intro f' hf'
    rw [hT₁_eq] at hf'
    obtain ⟨x, hx, rfl⟩ := hf'
    by_cases hxG : x ∈ G_v.E
    · have hp_eq : projectEdge G_nl v x = origEdge (copyMod G_nl) x := hproj_left x hxG
      have horig := horig_of x hxG
      have hnl : origEdge (copyMod G_nl) x ∈ G_nl.E := hnl_E ▸ List.mem_toFinset.mpr horig
      have hlt : origEdge (copyMod G_nl) x < G.m := (mem_nonloopEdges_iff.mp horig).1
      rw [hp_eq]; dsimp only [φ]; rw [ite_eq_left hlt]
      dsimp only [T₂, decodedTree, T₁, projectTree]
      rw [ite_eq_left hlt, ite_eq_left hlt, ite_eq_left hnl_ne']
      dsimp only
      rw [ite_eq_left hnl, ite_eq_left hnl]
      have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
      have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
      rw [hnl_tail, hnl_head]; exact ⟨rfl, rfl⟩
    · have hp_eq : projectEdge G_nl v x = x + copyMod G_nl := hproj_right x hxG
      have hx_ge : copyMod G.toMGraph ≤ x := hT_raw_nonGv x hx hxG
      have hnot_nl : x + copyMod G_nl ∉ G_nl.E := fun h =>
        Nat.not_lt_of_ge (Nat.le_add_left _ _) (lt_copyMod h)
      have hT₁_th : T₁.tail (x + copyMod G_nl) = T_raw.tail x ∧
          T₁.head (x + copyMod G_nl) = T_raw.head x := by
        dsimp only [T₁, projectTree]
        rw [ite_eq_left hnl_ne']
        dsimp only
        rw [ite_eq_right hnot_nl, ite_eq_right hnot_nl, Nat.add_sub_cancel]
        exact ⟨rfl, rfl⟩
      rw [hp_eq, hT₁_th.1, hT₁_th.2]
      have hx' : x ∈ T_gv.E ∪ (List.range inact.length).toFinset.image (fun idx => baseInact + idx) := by
        rw [hT_raw_def] at hx; exact hx
      rw [Finset.mem_union] at hx'
      rcases hx' with hx1 | hx2
      · obtain ⟨k, hkB, hkout, rfl, htx, hhx⟩ := hT_gv_nGv x hx1 hxG
        have heq_f' : baseB + k + copyMod G_nl = C₁ + k := by dsimp [C₁]; omega
        have hf'_ge : ¬ C₁ + k < G.m := by dsimp [C₁]; omega
        have hf'_lt : C₁ + k < C₂ := by dsimp [C₂, baseInact, C₁]; omega
        have hjk : E_list.length + k ∈ bridgeOutIdx := by
          rw [List.mem_filter]; refine ⟨hkout, ?_⟩
          simp; omega
        have hx_lt_baseInact : baseB + k < baseInact := by dsimp [baseInact]; omega
        have hTraw_t : T_raw.tail (baseB + k) = r₀ := by
          rw [hT_raw_def]; dsimp; rw [ite_eq_left hx_lt_baseInact]; exact htx
        have hTraw_h : T_raw.head (baseB + k) = B[k]'hkB := by
          rw [hT_raw_def]; dsimp; rw [ite_eq_left hx_lt_baseInact]
          exact hhx.trans (List.getD_eq_getElem _ _ hkB)
        rw [heq_f', hTraw_t, hTraw_h]
        dsimp only [φ]
        rw [ite_eq_right hf'_ge, ite_eq_left hf'_lt, show C₁ + k - C₁ = k by omega]
        have hnot_Gm : ¬ G.m + bridgeOutIdx.idxOf (E_list.length + k) < G.m := by omega
        dsimp only [T₂, decodedTree]
        rw [ite_eq_right hnot_Gm, ite_eq_right hnot_Gm, Nat.add_sub_cancel_left]
        have hidx_lt : bridgeOutIdx.idxOf (E_list.length + k) < bridgeOutIdx.length :=
          List.idxOf_lt_length_of_mem hjk
        have hres_lt : bridgeOutIdx.idxOf (E_list.length + k) < res.2.length := by
          rw [hres2_len]; exact Nat.lt_of_lt_of_le hidx_lt (Nat.le_add_right _ _)
        rw [List.getD_eq_getElem _ _ hres_lt]
        have hres_eq : res.2[bridgeOutIdx.idxOf (E_list.length + k)]'hres_lt =
            ((bridgeOutIdx.map fun j => (r₀, B.getD (j - E_list.length) 0))[bridgeOutIdx.idxOf (E_list.length + k)]'(by
              rw [List.length_map]; exact hidx_lt)) := by
          let lhs := (out.filter fun j =>
            decide (((nonloopEdges G).map mult).sum ≤ j ∧
              j < ((nonloopEdges G).map mult).sum + B.length)).map
            (fun j => (V_list.headD 0, B.getD (j - ((nonloopEdges G).map mult).sum) 0))
          let rhs := inact.map fun w => (r₀, w)
          have hmap_eq : lhs = bridgeOutIdx.map fun j => (r₀, B.getD (j - E_list.length) 0) := by
            dsimp only [lhs, bridgeOutIdx, r₀]; simp only [hm₁_eq]
          have hlhs_lt : bridgeOutIdx.idxOf (E_list.length + k) < lhs.length := by
            rw [hmap_eq, List.length_map]; exact hidx_lt
          have hcat_lt : bridgeOutIdx.idxOf (E_list.length + k) < (lhs ++ rhs).length := by
            rw [List.length_append]; exact Nat.lt_of_lt_of_le hlhs_lt (Nat.le_add_right _ _)
          have h1 : res.2[bridgeOutIdx.idxOf (E_list.length + k)]'hres_lt =
              (lhs ++ rhs)[bridgeOutIdx.idxOf (E_list.length + k)]'hcat_lt := rfl
          have h2 : lhs[bridgeOutIdx.idxOf (E_list.length + k)]'hlhs_lt =
              ((bridgeOutIdx.map fun j => (r₀, B.getD (j - E_list.length) 0))[bridgeOutIdx.idxOf (E_list.length + k)]'(by
                rw [List.length_map]; exact hidx_lt)) := by
            congr 1
          rw [h1, List.getElem_append_left hlhs_lt, h2]
        rw [hres_eq, List.getElem_map, List.getElem_idxOf hidx_lt, Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ hkB]
        exact ⟨rfl, rfl⟩
      · rw [Finset.mem_image] at hx2
        obtain ⟨idx, hidx, rfl⟩ := hx2
        have hidx_lt : idx < inact.length := List.mem_range.mp (List.mem_toFinset.mp hidx)
        have heq_f' : baseInact + idx + copyMod G_nl = C₂ + idx := by dsimp [C₂]; omega
        have hf'_ge : ¬ C₂ + idx < G.m := by dsimp [C₂, baseInact, C₁]; omega
        have hf'_nlt : ¬ C₂ + idx < C₂ := by omega
        have hnot_bi : ¬ baseInact + idx < baseInact := by omega
        have hTraw_t : T_raw.tail (baseInact + idx) = r₀ := by
          rw [hT_raw_def]; dsimp; exact ite_eq_right hnot_bi
        have hTraw_h : T_raw.head (baseInact + idx) = inact[idx]'hidx_lt := by
          rw [hT_raw_def]; dsimp; rw [ite_eq_right hnot_bi, Nat.add_sub_cancel_left]
          exact List.getD_eq_getElem _ _ hidx_lt
        rw [heq_f', hTraw_t, hTraw_h]
        dsimp only [φ]
        rw [ite_eq_right hf'_ge, ite_eq_right hf'_nlt, Nat.add_sub_cancel_left]
        have hnot_Gm : ¬ G.m + bridgeOutIdx.length + idx < G.m := by omega
        dsimp only [T₂, decodedTree]
        rw [ite_eq_right hnot_Gm, ite_eq_right hnot_Gm,
          show G.m + bridgeOutIdx.length + idx - G.m = bridgeOutIdx.length + idx by omega]
        have hres_lt : bridgeOutIdx.length + idx < res.2.length := by rw [hres2_len]; omega
        rw [List.getD_eq_getElem _ _ hres_lt]
        have hres_eq : res.2[bridgeOutIdx.length + idx]'hres_lt =
            ((inact.map fun w => (r₀, w))[idx]'(by rw [List.length_map]; exact hidx_lt)) := by
          let lhs := (out.filter fun j =>
            decide (((nonloopEdges G).map mult).sum ≤ j ∧
              j < ((nonloopEdges G).map mult).sum + B.length)).map
            fun j => (V_list.headD 0, B.getD (j - ((nonloopEdges G).map mult).sum) 0)
          let rhs := inact.map fun w => (r₀, w)
          have hlhs_len : lhs.length = bridgeOutIdx.length := by
            dsimp only [lhs, bridgeOutIdx]
            rw [List.length_map]
            simp only [hm₁_eq]
          have hcat_lt : bridgeOutIdx.length + idx < (lhs ++ rhs).length := by
            rw [List.length_append, hlhs_len, List.length_map]; omega
          have h1 : res.2[bridgeOutIdx.length + idx]'hres_lt =
              (lhs ++ rhs)[bridgeOutIdx.length + idx]'hcat_lt := rfl
          have hle : lhs.length ≤ bridgeOutIdx.length + idx := by omega
          rw [h1, List.getElem_append_right hle]
          congr 1; omega
        rw [hres_eq, List.getElem_map]
        exact ⟨rfl, rfl⟩


end MinCostFlow.WideWord
