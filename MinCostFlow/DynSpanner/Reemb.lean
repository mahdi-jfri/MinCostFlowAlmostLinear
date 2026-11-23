module

public import MinCostFlow.DynSpanner.ReembDefs

import MinCostFlow.DynSpanner.ReembAux
import Mathlib.Tactic.Linarith

/-!
# Coverage of `reembList` and `updateReembList` (`DynSpanner.Reemb`)

Proves that every surviving edge whose `piTotal` embedding changes in `DynSpanner.step` or
`DynSpanner.update` belongs to `stepReembSet` / `reembList` (single step) and
`updateReembSet` / `updateReembList` (batch). Definitions and cost bounds live in
`MinCostFlow/DynSpanner/ReembDefs.lean`.
-/

namespace MinCostFlow.DynSpanner

public section

/-- **Single-step embedding invariance outside `stepReembSet`.** For any surviving edge
`e ∈ st'.G.E` not in `stepReembSet st u`, its total embedding is unchanged:
`piTotal st' e = piTotal st e`. -/
theorem piTotal_eq_of_not_mem_stepReembSet {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    let st := runState (L := L) G₀ q sparsify us k
    let u := us[k]'hk
    let st' := (step st u sparsify).state
    ∀ e ∈ st'.G.E, e ∉ stepReembSet st u → piTotal st' e = piTotal st e := by
  intro st u st' e heG' hnot
  have hu_some : us[k]? = some u := List.getElem?_eq_getElem hk
  have hst'_eq : st' = runState (L := L) G₀ q sparsify us (k + 1) := by
    simp [st', runState, hu_some, st, u]
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)).1
  have hk1_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk)).1
  have hG'_eq : st'.G = G₀.applyBatch (us.take (k + 1)) := by
    rw [hst'_eq]; exact hk1_inv.G_eq
  have heG'_bat : e ∈ (G₀.applyBatch (us.take (k + 1))).E := hG'_eq ▸ heG'
  have hch_st : chooseLevel L st.q (st.t + 1) = chooseLevel L q (k + 1) := by
    rw [hk_inv.q_eq, hk_inv.t_eq]
  by_cases hj0 : chooseLevel L q (k + 1) = 0
  · exfalso
    apply hnot
    rw [stepReembSet_eq_zero st u (hch_st.trans hj0)]
    have hst'G : st'.G = st.G.applyUpdate u := by
      simp [st', step, hch_st, hj0, initAt]
    exact hst'G ▸ heG'
  · set j := chooseLevel L q (k + 1)
    have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
    obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
    obtain ⟨hBV_k, hds_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
    obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
    have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
    set Gk := G₀.applyBatch (us.take k)
    set G' := G₀.applyBatch (us.take (k + 1))
    have hVGk : Gk.IsValid := (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).1
    have hG'_app : G' = Gk.applyUpdate u := by
      simp [G', Gk, htake_succ, MGraph.applyBatch]
    have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_app]
    have hVG' : G'.IsValid := (batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBV_k1 hds_k1).1
    have hG'E_sub : G'.E ⊆ Gk.E := by
      have h1 := (batch_delOrSplit_invariants [u] Gk hVGk
        ⟨hu_valid, True.intro⟩ (fun x hx => by simp at hx; rwa [hx])).2.1
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
      rwa [← hG'_app] at h1
    set r := lastRebuild q L (j - 1) (k + 1)
    have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ k + 1 := by
      intro hdvd
      have := (chooseLevel_le_iff_dvd hq (le_trans (Nat.sub_le j 1) hj_le)).mpr hdvd
      omega
    have hr_eq_k : r = lastRebuild q L (j - 1) k := lastRebuild_eq_of_not_dvd hr_not_dvd
    have hr_le_k : r ≤ k := by rw [hr_eq_k]; exact lastRebuild_le q L (j - 1) k
    have hInv_r := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r
      (le_trans hr_le_k (Nat.le_of_lt hk))).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
    set st_r := runState (L := L) G₀ q sparsify us r
    set G_r := G₀.applyBatch (us.take r)
    set delta := (us.take (k + 1)).drop r
    have htake_k1 : us.take (k + 1) = us.take r ++ delta := by
      have h1 : (us.take (k + 1)).take r = us.take r := by
        rw [List.take_take, min_eq_left (le_trans hr_le_k (Nat.le_succ k))]
      rw [← h1]; exact (List.take_append_drop r (us.take (k + 1))).symm
    have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (htake_k1 ▸ hBV_k1)
    have hBV_r : G₀.BatchIsValid (us.take r) := hBV_split.1
    have hBV_d : G_r.BatchIsValid delta := hBV_split.2
    have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_right _ hx)
    have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_left _ hx)
    have hVG_r : G_r.IsValid := (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r).1
    have hG'_delta : G' = G_r.applyBatch delta := by
      dsimp only [G', G_r]; rw [htake_k1, applyBatch_append]
    have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
    have hrk_eq_lt : ∀ {m : ℕ}, m < j →
        lastRebuild q L m (k + 1) = lastRebuild q L m k ∧
        lastRebuild q L m r = lastRebuild q L m k := fun {m} hm => by
      have hm_le : m ≤ j - 1 := Nat.le_pred_of_lt hm
      have h1 : lastRebuild q L m (k + 1) = lastRebuild q L m k := by
        refine lastRebuild_eq_of_not_dvd fun hdvd => hr_not_dvd ?_
        exact dvd_trans (phasePeriod_dvd_of_le hm_le (le_trans (Nat.sub_le j 1) hj_le)) hdvd
      have hmr_le : lastRebuild q L m k ≤ r := by
        rw [hr_eq_k]
        exact lastRebuild_mono_level hq hm_le (le_trans (Nat.sub_le j 1) hj_le)
      exact ⟨h1, lastRebuild_idempotent_le hq hmr_le hr_le_k⟩
    set H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    have hH_mid_props : ∀ i : Fin (L + 1),
        G'.IsSubgraph (H_mid i) ∧ (H_mid i).V = G'.V ∧ (H_mid i).E = (st.H_level i).E ∩ G'.E :=
      fun i => by
        obtain ⟨_, h1, h2, h3, _, _⟩ :=
          isSubgraph_restrictUpdate (hk_inv.H_level_sub i) (hk_inv.H_level_V i) hu_valid hdu
        exact ⟨hG'_app ▸ h1, hG'_app ▸ h2, hG'_app ▸ h3⟩
    set H_lt := unionGraphLt G' H_mid j
    set H_lt_r := unionGraphLt G_r st_r.H_level j
    have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
      refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      intro e' he'
      simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] at he'
      rcases he' with ⟨i, _, hei⟩
      exact (hInv_r.H_level_sub i).2.1 hei
    have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
      ext e'
      simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hij, hei⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2] at hei
        have hei' := Finset.mem_inter.mp hei
        have hei1 := Finset.mem_inter.mp hei'.1
        have hei_r : e' ∈ (st_r.H_level i).E := by
          rw [hInv_r.H_level_E i]
          exact Finset.mem_inter.mpr ⟨hei1.1, hinv_d.2.1 (hG'_delta ▸ hei'.2)⟩
        exact ⟨⟨i, hij, hei_r⟩, hei'.2⟩
      · rintro ⟨⟨i, hij, hei_r⟩, he''⟩
        refine ⟨i, hij, ?_⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2]
        rw [hInv_r.H_level_E i, Finset.mem_inter] at hei_r
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hei_r.1, hG'E_sub he''⟩, he''⟩
    have hSub_lt : G'.IsSubgraph H_lt := ⟨Finset.Subset.rfl, hHLt_E ▸ Finset.inter_subset_right,
      fun _ _ => ⟨rfl, rfl⟩⟩
    set inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    set piLt_mid : Embedding := piLtFrom st.Pi_level inDom_mid j
    set S_prev : Finset ℕ := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
    set E_aff := affectedEdges G' H_lt piLt_mid S_prev
    have heNotAff : e ∉ E_aff := by
      have hsr := stepReembSet_eq_pos st u (by rw [hch_st]; exact hj0)
      dsimp only at hsr
      simp only [hch_st, hstG'] at hsr
      rwa [hsr] at hnot
    have hS_prev_eq : S_prev = allTouched G_r delta := by
      dsimp only [S_prev]
      rw [hk_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_k]
      have hdrop_app : (us.take (k + 1)).drop r = (us.take k).drop r ++ [u] := by
        rw [htake_succ, List.drop_append_of_le_length]
        rw [List.length_take]; exact le_trans hr_le_k (Nat.le_min.mpr ⟨le_rfl, Nat.le_of_lt hk⟩)
      have hGapp : G_r.applyBatch ((us.take k).drop r) = Gk := by
        have htk : us.take k = us.take r ++ (us.take k).drop r := by
          have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_k]
          rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
        dsimp only [Gk, G_r]; conv_rhs => rw [htk]
        exact (applyBatch_append _ _ _).symm
      dsimp only [delta]
      rw [hdrop_app, allTouched_append, hGapp]
      dsimp only [Gk, G_r]
      rw [hk_inv.G_eq]
      simp [allTouched]
    have hpi_eq : piLt_mid e = piLe st_r (j - 1) e := by
      change piLtFrom st.Pi_level inDom_mid j e = piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e
      rw [Nat.sub_add_cancel hj_pos]
      have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
        dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]
        exact ⟨hG'E_sub heG'_bat, heG'_bat⟩
      have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
        rw [hInv_r.inDom0]; exact hinv_d.2.1 (hG'_delta ▸ heG'_bat)
      have hcongr_in : ∀ m : Fin (L + 1), m.1 < j → (e ∈ inDom_mid m ↔ e ∈ st_r.inDom m) := by
        intro m hm
        have h1 := hk_inv.inDom_eq m
        have h2 := hInv_r.inDom_eq m
        rw [← (hrk_eq_lt hm).2] at h1
        have heGk : e ∈ Gk.E := hG'E_sub heG'_bat
        have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heG'_bat)
        constructor
        · intro h; rw [Finset.mem_inter] at h; have h' := h.1; rw [h1, Finset.mem_inter] at h'
          rw [h2]; exact Finset.mem_inter.mpr ⟨h'.1, heGr⟩
        · intro h; rw [h2, Finset.mem_inter] at h
          refine Finset.mem_inter.mpr ⟨?_, heG'_bat⟩
          rw [h1]; exact Finset.mem_inter.mpr ⟨h.1, heGk⟩
      obtain ⟨m₁, hm₁j, hm₁d, hm₁none, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
      obtain ⟨m₂, hm₂j, hm₂d, hm₂none, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
      have hm_eq : m₁ = m₂ := by
        by_contra hne
        rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
        · exact hm₁none m₂ hlt hm₂j ((hcongr_in m₂ hm₂j).mpr hm₂d)
        · exact hm₂none m₁ hlt hm₁j ((hcongr_in m₁ hm₁j).mp hm₁d)
      rw [heq₁, heq₂, hm_eq, hk_inv.Pi_level_eq m₂, ← (hrk_eq_lt hm₂j).2, hInv_r.Pi_level_eq m₂]
    -- `piTotal st' e = piLt_mid e = p_r`.
    have hres_st_Pi : ∀ l : Fin (L + 1), l.1 < j → st'.Pi_level l = st.Pi_level l := fun l hl => by
      dsimp only [st', step]
      simp only [hch_st, hj0, ↓reduceDIte, hl, ↓reduceIte]
    have hres_st_inDom : ∀ l : Fin (L + 1), st'.inDom l =
        if l.1 < j then inDom_mid l else if l.1 = j then E_aff else ∅ := fun l => by
      dsimp only [st', step]
      simp only [hch_st, hj0, ↓reduceDIte, hstG', E_aff, S_prev, piLt_mid, inDom_mid, H_lt, H_mid]
    have hpiTot' : piTotal st' e = piLt_mid e := by
      have he0' : e ∈ st'.inDom ⟨0, Nat.zero_lt_succ L⟩ := hst'_eq ▸ hk1_inv.inDom0 ▸ heG'_bat
      have hlt_L := piLtFrom_eq_of_lt st'.Pi_level st'.inDom (Nat.succ_pos j) (Nat.succ_le_succ hj_le)
        he0' fun l hl1 _ => by
          rw [hres_st_inDom l]
          simp [Nat.not_lt.mpr (Nat.le_of_succ_le hl1),
            Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hl1)]
      change piLtFrom st'.Pi_level st'.inDom (L + 1) e = _
      rw [hlt_L]
      have hj_not : e ∉ st'.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
        rw [hres_st_inDom]; simp [heNotAff]
      rw [piLtFrom_eq_prev_of_not_mem st'.Pi_level st'.inDom
        (j := ⟨j, Nat.lt_succ_of_le hj_le⟩) hj_pos he0' hj_not]
      have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
        dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]
        exact ⟨hG'E_sub heG'_bat, heG'_bat⟩
      obtain ⟨m, hmj, hmd, hm_none, heqm⟩ := piLtFrom_eq st'.Pi_level st'.inDom hj_pos he0'
      obtain ⟨m', hm'j, hm'd, hm'_none, heqm'⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
      have hmm' : m = m' := by
        by_contra hne
        rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
        · exact hm_none m' hlt hm'j (by rw [hres_st_inDom]; simp [hm'j, hm'd])
        · exact hm'_none m hlt hmj (by rw [hres_st_inDom] at hmd; simpa [hmj] using hmd)
      dsimp only [piLt_mid]
      rw [heqm, heqm', hmm', hres_st_Pi m' hm'j]
    -- Show `p_r` is a walk in `G'` from `G'.tail e` to `G'.head e` avoiding `allTouched G_r delta`.
    set p_r := piLe st_r (j - 1) e
    have hdisj_G' : ∀ z ∈ G'.walkVertices (G'.tail e) p_r, z ∉ allTouched G_r delta := by
      intro z hz hzS
      apply heNotAff
      refine Finset.mem_filter.mpr ⟨heG'_bat, decide_eq_true ⟨z, ?_, hS_prev_eq.symm ▸ hzS⟩⟩
      rwa [hpi_eq]
    have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
    dsimp only at hEmbr
    rw [Nat.sub_add_cancel hj_pos] at hEmbr
    have hw_r : H_lt_r.IsWalk (G_r.tail e) (G_r.head e) p_r :=
      hEmbr.2 e (hinv_d.2.1 (hG'_delta ▸ heG'_bat))
    have hanc_ends := hinv_d.2.2.2.2.2.2 e (hinv_d.2.1 (hG'_delta ▸ heG'_bat))
    have hV_tail : G'.tail e ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' e heG'_bat).1
    have hV_head : G'.head e ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' e heG'_bat).2
    have hp₁_prop := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hSub_lt)
      (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
      (fun _ _ => by simp [H_lt, unionGraphLt, hG'_delta]) Finset.Subset.rfl p_r
      (G_r.tail e) (G_r.head e) (G'.tail e)
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'_bat))).1
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'_bat))).2
      hw_r hV_tail (hG'_delta ▸ hanc_ends.1)
    have hdis1 : Disjoint (H_lt.walkVertices (G'.tail e) p_r).toFinset (allTouched G_r delta) := by
      rw [Finset.disjoint_left]
      intro z hz
      exact hdisj_G' z (List.mem_toFinset.mp hz)
    have hw_G'_Gr : G'.IsWalk (G'.tail e) (G_r.head e) p_r :=
      IsWalk.of_isSubgraph hSub_lt (hp₁_prop.1 hdis1).2.1
    -- Also `G'.head e = G_r.head e` because `G_r.head e` is the last vertex of `p_r`, untouched!
    have hhead_mem : G_r.head e ∈ G'.walkVertices (G'.tail e) p_r :=
      mem_walkVertices_end hw_G'_Gr
    have hhead_eq : G'.head e = G_r.head e := by
      have hnot_h : G_r.head e ∉ allTouched G_r delta := hdisj_G' _ hhead_mem
      by_contra hne
      have hanc_h : batchAnc delta (G'.head e) = G_r.head e := by
        rw [hG'_delta]; exact hanc_ends.2
      have hmem : batchAnc delta (G'.head e) ∈ allTouched G_r delta :=
        batchAnc_mem_allTouched_of_ne delta G_r hVG_r hBV_d hds_d (G'.head e) hV_head
          (by rw [hanc_h]; exact Ne.symm hne)
      rw [hanc_h] at hmem
      exact hnot_h hmem
    have hp_walk : G'.IsWalk (G'.tail e) (G'.head e) p_r := hhead_eq.symm ▸ hw_G'_Gr
    have hback := piLe_eq_of_not_affected hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le rfl
      heG'_bat hp_walk hdisj_G' k hr_le_k le_rfl ⟨L, Nat.lt_succ_self L⟩
      (le_trans (Nat.sub_le j 1) hj_le)
    rw [hpiTot', hpi_eq]
    exact hback.symm

/-- Contrapositive form for `reembList`: every surviving edge whose `piTotal` embedding changed in
one step lies in `reembList st u`. -/
theorem mem_reembList_of_piTotal_ne {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    let st := runState (L := L) G₀ q sparsify us k
    let u := us[k]'hk
    let st' := (step st u sparsify).state
    ∀ e ∈ st'.G.E, piTotal st' e ≠ piTotal st e → e ∈ reembList st u := by
  intro st u st' e heG' hne
  rw [mem_reembList]
  by_contra hnot
  exact hne (piTotal_eq_of_not_mem_stepReembSet hVG₀ hL hq hGm₀ hSpec hBV hds hk e heG' hnot)

/-- **Batch embedding invariance outside `updateReembSet`.** For a batch `U` matching the slice
`us[k₀ .. k₀ + U.length)`, every surviving edge `e ∈ st_end.G.E` not in `updateReembSet` keeps
its exact `piTotal` embedding across the whole batch. -/
theorem piTotal_eq_of_not_mem_updateReembSet {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us U : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let st₀ := runState (L := L) G₀ q sparsify us k₀
    let out := update st₀ U sparsify
    ∀ e ∈ out.state.G.E, e ∉ updateReembSet st₀ U sparsify →
      piTotal out.state e = piTotal st₀ e := by
  intro st₀ out e heG hnot
  have hout := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ [] ∅ 0
    hlen hmatch
  have hst_end : out.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) := by
    dsimp only [out, update]; rw [hout]
  have hr_eq := updateReembSet_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ hmatch
  rw [hst_end] at heG ⊢
  have hnot_step : ∀ i (hi : i < U.length),
      e ∉ stepReembSet (runState (L := L) G₀ q sparsify us (k₀ + i)) (U[i]'hi) := by
    intro i hi hmem
    apply hnot
    rw [hr_eq, Finset.mem_inter]
    refine ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩, heG⟩
    simp only [runStepReembSet, hmatch i hi]
    exact hmem
  -- By induction on `m ≤ U.length`, `piTotal (st (k₀ + m)) e = piTotal (st k₀) e` for `e ∈ G_{k₀ + m}.E`.
  suffices h : ∀ m ≤ U.length,
      e ∈ (runState (L := L) G₀ q sparsify us (k₀ + m)).G.E →
      piTotal (runState (L := L) G₀ q sparsify us (k₀ + m)) e = piTotal st₀ e from
    h U.length le_rfl heG
  intro m
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm hem1
    have hm_lt : m < U.length := Nat.lt_of_succ_le hm
    have hk_lt : k₀ + m < us.length := by omega
    have hu_some : us[k₀ + m]? = some (U[m]'hm_lt) := hmatch m hm_lt
    have hu_eq : us[k₀ + m]'hk_lt = U[m]'hm_lt := by
      have h1 := List.getElem?_eq_getElem hk_lt
      rw [hu_some] at h1
      exact Option.some.inj h1.symm
    have hst_step : runState (L := L) G₀ q sparsify us (k₀ + (m + 1)) =
        (step (runState (L := L) G₀ q sparsify us (k₀ + m)) (us[k₀ + m]'hk_lt) sparsify).state := by
      rw [show k₀ + (m + 1) = (k₀ + m) + 1 by omega]
      simp [runState, List.getElem?_eq_getElem hk_lt]
    have hstep_eq : piTotal (runState (L := L) G₀ q sparsify us (k₀ + (m + 1))) e =
        piTotal (runState (L := L) G₀ q sparsify us (k₀ + m)) e := by
      rw [hst_step]
      refine piTotal_eq_of_not_mem_stepReembSet hVG₀ hL hq hGm₀ hSpec hBV hds hk_lt e
        (hst_step ▸ hem1) ?_
      rw [hu_eq]
      exact hnot_step m hm_lt
    -- Also `e ∈ G_{k₀ + m}.E` since `u` is a deletion or split.
    have hem0 : e ∈ (runState (L := L) G₀ q sparsify us (k₀ + m)).G.E := by
      have hdu : isDelOrSplit (us[k₀ + m]'hk_lt) := hds _ (List.getElem_mem hk_lt)
      have hG_step : (runState (L := L) G₀ q sparsify us (k₀ + (m + 1))).G =
          (runState (L := L) G₀ q sparsify us (k₀ + m)).G.applyUpdate (us[k₀ + m]'hk_lt) := by
        rw [hst_step]; unfold step; dsimp only; split_ifs <;> simp [initAt]
      rw [hG_step] at hem1
      exact E_applyUpdate_subset hdu hem1
    exact hstep_eq.trans (ih (Nat.le_of_lt hm_lt) hem0)

/-- Contrapositive form for `updateReembList`: every surviving edge whose `piTotal` embedding
changed during a batch lies in `updateReembList`. -/
theorem mem_updateReembList_of_piTotal_ne {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us U : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let st₀ := runState (L := L) G₀ q sparsify us k₀
    let out := update st₀ U sparsify
    ∀ e ∈ out.state.G.E, piTotal out.state e ≠ piTotal st₀ e →
      e ∈ updateReembList st₀ U sparsify := by
  intro st₀ out e heG hne
  rw [mem_updateReembList]
  by_contra hnot
  exact hne (piTotal_eq_of_not_mem_updateReembSet hVG₀ hL hq hGm₀ hSpec hBV hds hlen hmatch
    e heG hnot)

end

end MinCostFlow.DynSpanner
