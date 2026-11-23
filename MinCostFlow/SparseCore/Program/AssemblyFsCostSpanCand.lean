module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4LoopDefs
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot

import MinCostFlow.SparseCore.Program.AssemblyFsCostSpanDom
import Mathlib.Tactic

/-!
# Copy-buffer candidates are contained in `updateReembSet` (`AssemblyFsCostSpanCand`)

* `runStepH_left_sub_reemb`: `((runState k).H.E \ (runState (k + 1)).H.E) ∩ (runState (k + 1)).G.E ⊆ runStepReembSet k`.
* `uhDelFinset_step_inter_G_sub_left`: every surviving edge deleted in `(runStepOut k).UH` left `H` at step `k`.
* `p4CopyCand_sub_updateReembSet`: `p4CopyCand P d U ⊆ updateReembSet (d.state P) U (canonicalSparsify P.impl)`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

/-- **Single-step leaving-`H` coverage.** Every surviving edge that leaves `H` at step `k`
belongs to `runStepReembSet k`. -/
theorem runStepH_left_sub_reemb {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    ((runState (L := L) G₀ q sparsify us k).H.E \
        (runState (L := L) G₀ q sparsify us (k + 1)).H.E) ∩
      (runState (L := L) G₀ q sparsify us (k + 1)).G.E ⊆
      runStepReembSet (L := L) G₀ q sparsify us k := by
  intro e he
  obtain ⟨heDiff, heG'⟩ := Finset.mem_inter.mp he
  obtain ⟨heH, heNotH'⟩ := Finset.mem_sdiff.mp heDiff
  set u := us[k]'hk
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le).1
  have hk1_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hk).1
  set st := runState (L := L) G₀ q sparsify us k
  set st' := runState (L := L) G₀ q sparsify us (k + 1)
  have hst' : st' = (step st u sparsify).state := by simp [st', runState, hu]; rfl
  have hch : chooseLevel L st.q (st.t + 1) = chooseLevel L q (k + 1) := by
    rw [hk_inv.q_eq, hk_inv.t_eq]
  rcases Nat.eq_zero_or_pos (chooseLevel L q (k + 1)) with hj0 | hj_pos
  · have hR : runStepReembSet (L := L) G₀ q sparsify us k = (st.G.applyUpdate u).E := by
      simp only [runStepReembSet, hu]
      exact stepReembSet_eq_zero st u (hch.trans hj0)
    rw [hR]
    have hG' : st'.G = st.G.applyUpdate u := by
      rw [hst']; dsimp only [step]; rw [dite_eq_left_of_eq_true (eq_true (hch.trans hj0))]; rfl
    rwa [← hG']
  · by_contra hnot
    set j := chooseLevel L q (k + 1)
    have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
    have hj0 : ¬ j = 0 := Nat.ne_of_gt hj_pos
    have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu
    obtain ⟨hBV_k, hds_k, hu_map⟩ := batchIsValid_take us G₀ k hBV hds
    obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
    obtain ⟨hu_valid, hdu⟩ := hu_map u hu
    set Gk := G₀.applyBatch (us.take k)
    set G' := G₀.applyBatch (us.take (k + 1))
    have hVGk : Gk.IsValid := (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).1
    have hG'_app : G' = Gk.applyUpdate u := by simp [G', Gk, htake_succ, MGraph.applyBatch]
    have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_app]
    have hVG' : G'.IsValid := (batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBV_k1 hds_k1).1
    have hG'E_sub : G'.E ⊆ Gk.E := by
      have h1 := (batch_delOrSplit_invariants [u] Gk hVGk
        ⟨hu_valid, True.intro⟩ (fun x hx => by simp at hx; rwa [hx])).2.1
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
      rwa [← hG'_app] at h1
    have heG'_bat : e ∈ G'.E := by
      show e ∈ (G₀.applyBatch (us.take (k + 1))).E
      rwa [← hk1_inv.G_eq]
    -- `e ∈ st.H.E` comes from some level `l`.
    rw [hk_inv.H_E] at heH
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at heH
    obtain ⟨l, -, hel⟩ := heH
    by_cases hlj : l.1 < j
    · -- Level `l < j` is preserved on surviving edges, contradicting `e ∉ st'.H.E`.
      apply heNotH'
      rw [hk1_inv.H_E]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨l, l.2, ?_⟩
      have hHl : st'.H_level l = (st.H_level l).applyBatch (restrictUpdate u (st.H_level l)) := by
        rw [hst']; dsimp only [step]
        simp only [hch, hj0, ↓reduceDIte, hlj, ↓reduceIte]
      rw [hHl]
      have hsub := (isSubgraph_restrictUpdate (hk_inv.H_level_sub l) (hk_inv.H_level_V l)
        hu_valid hdu).2.2.2.1
      rw [hsub, ← hG'_app]
      exact Finset.mem_inter.mpr ⟨hel, heG'_bat⟩
    · -- Level `l ≥ j`: `e ∈ st.inDom l`, contradicting `not_mem_inDom_of_not_affected`.
      have heDom : e ∈ st.inDom l :=
        runState_H_level_sub_inDom hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le l hel
      have hjl : j ≤ l.1 := Nat.le_of_not_lt hlj
      -- Build `hp_walk` and `hp_disj` from `e ∉ runStepReembSet k` (as in `Reemb.lean`).
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
      have hBV_split := (MinCostFlow.DynSpanner.batchIsValid_append G₀ (us.take r) delta).mp
        (htake_k1 ▸ hBV_k1)
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
        simp only [runStepReembSet, hu] at hnot
        have hsr := stepReembSet_eq_pos st u (by rw [hch]; exact hj0)
        dsimp only at hsr
        simp only [hch, hstG'] at hsr
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
      exact not_mem_inDom_of_not_affected hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le rfl
        heG'_bat hp_walk hdisj_G' k hr_le_k le_rfl l hjl heDom

/-- Every surviving edge deleted by `(runStepOut k).UH` left `H` at step `k`. -/
theorem uhDelFinset_step_inter_G_sub_left {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    uhDelFinset (runStepOut (L := L) G₀ q sparsify us k).UH ∩
        (runState (L := L) G₀ q sparsify us (k + 1)).G.E ⊆
      ((runState (L := L) G₀ q sparsify us k).H.E \
        (runState (L := L) G₀ q sparsify us (k + 1)).H.E) ∩
      (runState (L := L) G₀ q sparsify us (k + 1)).G.E := by
  intro e he
  obtain ⟨heDel, heG'⟩ := Finset.mem_inter.mp he
  refine Finset.mem_inter.mpr ⟨?_, heG'⟩
  set u := us[k]'hk
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le).1
  have hk1_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hk).1
  set st := runState (L := L) G₀ q sparsify us k
  set st' := runState (L := L) G₀ q sparsify us (k + 1)
  have hst' : st' = (step st u sparsify).state := by simp [st', runState, hu]; rfl
  have hout : (runStepOut (L := L) G₀ q sparsify us k).UH = (step st u sparsify).UH := by
    simp [runStepOut, hu]; rfl
  rw [hout] at heDel
  simp only [uhDelFinset, List.mem_toFinset, List.mem_filterMap] at heDel
  obtain ⟨upd, hupd_mem, hupd_eq⟩ := heDel
  have hupd_del : upd = .delete e := by
    cases upd with
    | insert _ _ _ => simp at hupd_eq
    | delete e' => simp at hupd_eq; subst hupd_eq; rfl
    | split _ _ _ _ => simp at hupd_eq
  subst hupd_del
  obtain ⟨-, -, hU_val⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_val u hu
  have hG'_eq : st'.G = st.G.applyUpdate u := by
    rw [hst']; dsimp only [step]
    split_ifs <;> rfl
  have hnot_pref : Update.delete e ∉ restrictUpdate u st.H := by
    intro hmem
    rcases u with ⟨e', a, b⟩ | e' | ⟨v, v', St, Sh⟩
    · exact absurd hdu id
    · simp only [restrictUpdate] at hmem
      split_ifs at hmem with he'
      · simp only [List.mem_singleton, Update.delete.injEq] at hmem
        subst hmem
        rw [hG'_eq] at heG'
        simp [MGraph.applyUpdate] at heG'
      · simp at hmem
    · simp [restrictUpdate] at hmem
  have hMidE : (st.H.applyBatch (restrictUpdate u st.H)).E = st.H.E ∩ (st.G.applyUpdate u).E := by
    rw [hk_inv.G_eq]
    exact (isSubgraph_restrictUpdate hk_inv.H_sub hk_inv.H_V hu_val hdu).2.2.2.1
  have hstep_uh : ∃ H_new_E : Finset ℕ,
      st'.H.E = H_new_E ∧
      e ∈ (st.H.applyBatch (restrictUpdate u st.H)).E \ H_new_E := by
    by_cases hj0 : chooseLevel L st.q (st.t + 1) = 0
    · dsimp only [step] at hupd_mem
      rw [dite_eq_left_of_eq_true (eq_true hj0)] at hupd_mem
      dsimp only at hupd_mem
      simp only [List.mem_append] at hupd_mem
      rcases hupd_mem with (h1 | h2) | h3
      · exact absurd h1 hnot_pref
      · simp only [List.mem_map, Update.delete.injEq, Finset.mem_sort] at h2
        obtain ⟨e', he', rfl⟩ := h2
        refine ⟨(initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify).state.H.E, ?_, he'⟩
        have hlev : st'.H_level =
            (initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify).state.H_level := by
          rw [hst']; dsimp only [step]; rw [dite_eq_left_of_eq_true (eq_true hj0)]
        rw [hk1_inv.H_E, hlev]
        ext x
        simp only [unionEdgesLt, initAt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨i, -, hi⟩
          by_cases hi0 : i.1 = 0
          · simpa [hi0] using hi
          · simp [hi0, emptyGraphOn] at hi
        · intro hx
          exact ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, by simpa using hx⟩
      · simp only [List.mem_map] at h3
        obtain ⟨_, _, hne⟩ := h3
        cases hne
    · dsimp only [step] at hupd_mem
      rw [dite_eq_right_of_eq_false (eq_false hj0)] at hupd_mem
      dsimp only at hupd_mem
      simp only [List.mem_append] at hupd_mem
      rcases hupd_mem with (h1 | h2) | h3
      · exact absurd h1 hnot_pref
      · simp only [List.mem_map, Update.delete.injEq, Finset.mem_sort] at h2
        obtain ⟨e', he', rfl⟩ := h2
        refine ⟨_, ?_, he'⟩
        have hlev : st'.H_level = (step st u sparsify).state.H_level := by rw [hst']
        rw [hk1_inv.H_E, hlev]
        dsimp only [step]
        rw [dite_eq_right_of_eq_false (eq_false hj0)]
      · simp only [List.mem_map] at h3
        obtain ⟨_, _, hne⟩ := h3
        cases hne
  obtain ⟨H_new_E, hst'E, heMid⟩ := hstep_uh
  rw [hMidE] at heMid
  rw [hst'E]
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp heMid).1).1,
    (Finset.mem_sdiff.mp heMid).2⟩

/-- **Copy-buffer candidate containment (`p4CopyCand ⊆ updateReembSet`)**:
every surviving edge deleted from `H` or re-embedded during a batch `U` belongs to
`updateReembSet (d.state P) U (canonicalSparsify P.impl)`. -/
theorem p4CopyCand_sub_updateReembSet (P : DSParams) (d : DSHist) (U : List Update)
    (hVG₀ : d.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hBV : d.G₀.BatchIsValid (d.flat ++ U)) (hds : ∀ u ∈ d.flat ++ U, isDelOrSplit u) :
    p4CopyCand P d U ⊆ updateReembSet (d.state P) U (canonicalSparsify P.impl) := by
  intro e he
  unfold p4CopyCand at he
  obtain ⟨heInter, _⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heUnion, heG'⟩ := Finset.mem_inter.mp heInter
  rcases Finset.mem_union.mp heUnion with heUH | heReemb
  · have hq : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
    set sp := canonicalSparsify P.impl
    have hSpec := canonicalSparsify_spec_absorb P.impl P.mMax
    have hst : d.state P = runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) d.flat.length := by
      rw [runState_append d.G₀ (d.q P) sp d.flat U d.flat.length le_rfl]; rfl
    have hst' : (⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P =
        runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) (d.flat.length + U.length) := by
      simp only [DSHist.state, dsHist_flat_append, List.length_append]; rfl
    have hmatch : ∀ (i : ℕ) (hi : i < U.length),
        (d.flat ++ U)[d.flat.length + i]? = some (U[i]'hi) := by
      intro i hi
      simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact List.getElem?_eq_getElem hi
    have hrun := updateGo_run_eq (L := P.L) (q := d.q P) (sparsify := sp) d.G₀ (d.flat ++ U) U
      d.flat.length [] ∅ 0 (by simp) hmatch
    have hUH_eq : (update (d.state P) U sp).UH =
        (List.range U.length).flatMap fun i =>
          (runStepOut (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) (d.flat.length + i)).UH := by
      rw [hst]; dsimp only [update]; rw [hrun]; simp
    rw [hUH_eq] at heUH
    simp only [uhDelFinset, List.mem_toFinset, List.mem_filterMap, List.mem_flatMap,
      List.mem_range] at heUH
    obtain ⟨upd, ⟨i, hi, hupd_i⟩, hupd_eq⟩ := heUH
    have hupd_del : upd = .delete e := by
      cases upd with
      | insert _ _ _ => simp at hupd_eq
      | delete e' => simp at hupd_eq; subst hupd_eq; rfl
      | split _ _ _ _ => simp at hupd_eq
    subst hupd_del
    have heDel_i : e ∈ uhDelFinset
        (runStepOut (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) (d.flat.length + i)).UH := by
      simp only [uhDelFinset, List.mem_toFinset, List.mem_filterMap]
      exact ⟨.delete e, hupd_i, rfl⟩
    rw [hst'] at heG'
    -- `e` is in `G.E` at step `d.flat.length + i + 1` because deletions/splits only shrink `G.E`.
    have heG_i1 : e ∈ (runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U)
        (d.flat.length + i + 1)).G.E := by
      have hmono : ∀ m, d.flat.length + i + 1 + m ≤ (d.flat ++ U).length →
          e ∈ (runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) (d.flat.length + i + 1 + m)).G.E →
          e ∈ (runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U) (d.flat.length + i + 1)).G.E := by
        intro m
        induction m with
        | zero => intro _ h; exact h
        | succ t iht =>
          intro hlen ht
          apply iht (by omega)
          have hkt : d.flat.length + i + 1 + t < (d.flat ++ U).length := by omega
          have hut : (d.flat ++ U)[d.flat.length + i + 1 + t]? =
              some ((d.flat ++ U)[d.flat.length + i + 1 + t]'hkt) := List.getElem?_eq_getElem hkt
          have hI0 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds
            (d.flat.length + i + 1 + t) hkt.le).1.G_eq
          have hI1 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds
            (d.flat.length + i + 1 + t + 1) hkt).1.G_eq
          have hsub : (runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U)
              (d.flat.length + i + 1 + t + 1)).G.E ⊆
            (runState (L := P.L) d.G₀ (d.q P) sp (d.flat ++ U)
              (d.flat.length + i + 1 + t)).G.E := by
            rw [hI1, hI0, take_succ_of_getElem? hut, applyBatch_append]
            exact applyUpdate_E_subset_of_delOrSplit (hds _ (List.getElem_mem hkt))
          exact hsub ht
      have hlen_eq : d.flat.length + i + 1 + (U.length - (i + 1)) = d.flat.length + U.length := by
        omega
      exact hmono (U.length - (i + 1)) (by rw [hlen_eq, List.length_append]) (by rwa [hlen_eq])
    have hk_lt : d.flat.length + i < (d.flat ++ U).length := by simp; omega
    have hleft := uhDelFinset_step_inter_G_sub_left hVG₀ hL hq hGm₀ hSpec hBV hds hk_lt
      (Finset.mem_inter.mpr ⟨heDel_i, heG_i1⟩)
    have hreemb_i := runStepH_left_sub_reemb hVG₀ hL hq hGm₀ hSpec hBV hds hk_lt hleft
    rw [hst, updateReembSet_run_eq d.G₀ (d.flat ++ U) U d.flat.length hmatch]
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hreemb_i⟩, heG'⟩
  · exact heReemb

end

end MinCostFlow.SparseCore.Program
