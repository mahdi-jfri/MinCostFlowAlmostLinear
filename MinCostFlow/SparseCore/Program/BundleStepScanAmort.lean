module

public import MinCostFlow.SparseCore.Program.BundleStepScanProofs

/-!
# Exactness and potential telescoping for Phase 2 (`BundleStepScanAmort`)

Proves:
* `scanCands_eq_exactSplitCands`: Phase 2 finds the exact set `exactSplitCands` for every active
  slot.
* `scanNonMaxSum_le_tourPot_drop`: the smaller-side root-scan work telescopes into the drop of
  `tourPot R cord`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- When each `G ∈ gs` is a nodup split group of final core vertices and every bundle `b ∈ B₀.vertices`
either has all its surviving ends in a single group `G ∈ gs` or maps to at most one final core vertex,
Phase 2 starting from `cand₀ = fun _ => ∅` finds the exact set `exactSplitCands`. -/
theorem scanCands_eq_exactSplitCands {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {j : Fin slotCap} {B₀ : BundleState}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    (hS₀j : S₀ j = some B₀)
    (_hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hcord_nd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup)
    (hmax_lt : ∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length)
    (hsrc_iff : ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w)
    (hbundle_in_group : ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x ∈ gs[gi].toFinset) :
    let S := tableDelEdges S₀ D
    addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) gs.length j =
      (exactSplitCands B₀ (B₀.edges \ D) src').toFinset := by
  intro S
  set B := ({ B₀ with edges := B₀.edges \ D } : BundleState)
  have hSj : S j = some B := by simp [S, tableDelEdges, hS₀j, B]
  have hends_eq : ∀ b, B.ends b = survivingEnds B₀ (B₀.edges \ D) b := fun b => by
    ext x; simp only [survivingEnds, BundleState.mem_ends, Finset.mem_filter, Finset.mem_sdiff, B]; tauto
  have hfilt_eq : ∀ b w,
      (B.ends b).filter (fun x => x ∈ cord' w) =
        (survivingEnds B₀ (B₀.edges \ D) b).filter (fun x => src' x = w) := fun b w => by
    rw [hends_eq b]; ext x; simp only [Finset.mem_filter]
    exact ⟨fun ⟨hx, hxw⟩ => ⟨hx, (hsrc_iff x ((mem_edgeEnds _ _).mpr (Finset.mem_filter.mp hx).2) w).mp hxw⟩,
      fun ⟨hx, hxw⟩ => ⟨hx, (hsrc_iff x ((mem_edgeEnds _ _).mpr (Finset.mem_filter.mp hx).2) w).mpr hxw⟩⟩
  have hBV_eq : B.vertices = B₀.vertices := rfl
  ext b
  rw [mem_addCandsForGroups_iff hSj hcord_nd gs.length (le_refl _) b, hBV_eq]
  simp only [Finset.notMem_empty, false_or, exactSplitCands, List.mem_toFinset, List.mem_filter,
    Finset.mem_sort, decide_eq_true_eq]
  constructor
  · rintro ⟨hbV, gi, _, hgi, t, ht, _, hpos, hlt⟩
    refine ⟨hbV, ?_⟩
    rw [hfilt_eq b (gs[gi][t])] at hpos hlt
    rw [hends_eq b] at hlt
    have h1 : ∃ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x = gs[gi][t] := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos; exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have h2 : ∃ y ∈ survivingEnds B₀ (B₀.edges \ D) b, src' y ≠ gs[gi][t] := by
      by_contra hall; push Not at hall
      have heq : (survivingEnds B₀ (B₀.edges \ D) b).filter (fun x => src' x = gs[gi][t]) =
          survivingEnds B₀ (B₀.edges \ D) b := by
        ext z; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hall z
      rw [heq] at hlt; exact lt_irrefl _ hlt
    obtain ⟨x, hx, hxw⟩ := h1; obtain ⟨y, hy, hyw⟩ := h2
    exact Finset.one_lt_card.mpr ⟨src' x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      src' y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, by rw [hxw]; exact hyw.symm⟩
  · rintro ⟨hbV, h2⟩
    obtain ⟨gi, hgi, hG⟩ := hbundle_in_group b hbV h2
    have hmlt := hmax_lt gi hgi
    have hiff := splitCands_exact_iff (w_max := gs[gi][maxIdxs.getD gi 0]'hmlt) hG
    obtain ⟨w, hw_er, hpos, hlt⟩ := hiff.mp h2
    obtain ⟨hw_ne, hw_mem⟩ := Finset.mem_erase.mp hw_er
    obtain ⟨t, ht, htw⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw_mem)
    have hne_t : t ≠ maxIdxs.getD gi 0 := fun h => hw_ne (by rw [← htw]; congr 1)
    refine ⟨hbV, gi, hgi, hgi, t, ht, hne_t, ?_, ?_⟩
    · rw [hfilt_eq b (gs[gi][t]), htw]; exact hpos
    · rw [hfilt_eq b (gs[gi][t]), hends_eq b, htw]; exact hlt

/-- Telescoping of the smaller-side root-scan work into `tourPot R_old cord - tourPot R_new cord'`
via `tourPotTerm_sum_split` (`BundlePotBridge.lean`). -/
theorem scanNonMaxSum_le_tourPot_drop
    {R_old R_new : Finset ℕ} {cord cord' : ℕ → List End}
    {gs : List (List ℕ)} {oldRoots maxIdxs : List ℕ}
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ w ∈ G, w ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hmax_spec : ∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
      ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length)
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ w ∈ gs[gi].toFinset, (cord' w).length) ≤ (cord (oldRoots[gi]'(by omega))).length)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧ (cord' r).length ≤ (cord r).length) :
    tourPot R_new cord' + totalNonMaxLen cord' gs maxIdxs ≤ tourPot R_old cord := by
  have hgrp_ineq : ∀ gi (hgi : gi < gs.length),
      (∑ w ∈ gs[gi].toFinset, tourPotTerm (cord' w).length) +
        (∑ j ∈ (Finset.range gs[gi].length).erase (maxIdxs.getD gi 0), (cord' (gs[gi].getD j 0)).length) ≤
      tourPotTerm (cord (oldRoots[gi]'(by omega))).length := by
    intro gi hgi
    obtain ⟨hm, hmax⟩ := hmax_spec gi hgi
    set wMax := gs[gi][maxIdxs.getD gi 0]'hm
    have hnd := hgs_nd gs[gi] (List.getElem_mem hgi)
    have hsum_er :
        (∑ j ∈ (Finset.range gs[gi].length).erase (maxIdxs.getD gi 0), (cord' (gs[gi].getD j 0)).length) =
          ∑ w ∈ gs[gi].toFinset.erase wMax, (cord' w).length := by
      refine Finset.sum_bij (fun j _ => gs[gi].getD j 0) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro j hj
        obtain ⟨hj_ne, hj_r⟩ := Finset.mem_erase.mp hj
        have hj_lt := Finset.mem_range.mp hj_r
        rw [List.getD_eq_getElem _ _ hj_lt]
        refine Finset.mem_erase.mpr ⟨fun heq => hj_ne (hnd.getElem_inj_iff.mp heq),
          List.mem_toFinset.mpr (List.getElem_mem hj_lt)⟩
      · intro j1 hj1 j2 hj2 heq
        have h1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj1)
        have h2 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj2)
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at heq
        exact hnd.getElem_inj_iff.mp heq
      · intro w hw
        obtain ⟨hw_ne, hw_in⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw_in)
        exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hw_ne (by simp [wMax, h]), Finset.mem_range.mpr hj⟩,
          List.getD_eq_getElem _ _ hj⟩
    rw [hsum_er]
    have hsplit := tourPotTerm_sum_split (G := gs[gi].toFinset) (L := fun w => (cord' w).length) (w_max := wMax)
      (List.mem_toFinset.mpr (List.getElem_mem hm))
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
        exact hmax j hj)
    exact le_trans hsplit (tourPotTerm_mono (hgroup_sum_le gi hgi))
  set U := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
  have hU_sub : U ⊆ R_new := by
    intro w hw
    obtain ⟨gi, hgi, hw'⟩ := Finset.mem_biUnion.mp hw
    have hlt := Finset.mem_range.mp hgi
    rw [List.getD_eq_getElem gs [] hlt, List.mem_toFinset] at hw'
    exact hgs_sub _ (List.getElem_mem hlt) w hw'
  have hU_sum : ∑ w ∈ U, tourPotTerm (cord' w).length =
      ∑ gi ∈ Finset.range gs.length, ∑ w ∈ (gs.getD gi []).toFinset, tourPotTerm (cord' w).length := by
    refine Finset.sum_biUnion fun i hi j hj hij => ?_
    have hi' := Finset.mem_range.mp hi; have hj' := Finset.mem_range.mp hj
    change Disjoint (gs.getD i []).toFinset (gs.getD j []).toFinset
    rw [List.getD_eq_getElem gs [] hi', List.getD_eq_getElem gs [] hj']
    exact hgs_disj i hi' j hj' hij
  have hRnew_split : tourPot R_new cord' =
      (∑ w ∈ U, tourPotTerm (cord' w).length) + (∑ r ∈ R_new \ U, tourPotTerm (cord' r).length) := by
    unfold tourPot
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hU_sub]
  have hold_sum : ∑ gi ∈ Finset.range gs.length, tourPotTerm (cord (oldRoots.getD gi 0)).length =
      ∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length := by
    refine Finset.sum_bij (fun gi _ => oldRoots.getD gi 0) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro gi hgi
      have hlt : gi < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hgi
      rw [List.getD_eq_getElem _ _ hlt, List.mem_toFinset]; exact List.getElem_mem hlt
    · intro i hi j hj heq
      have hi' : i < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hi
      have hj' : j < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hj
      rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at heq
      exact hold_nd.getElem_inj_iff.mp heq
    · intro r hr
      obtain ⟨gi, hgi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hr)
      exact ⟨gi, Finset.mem_range.mpr (by omega), List.getD_eq_getElem _ _ hgi⟩
  have hsum_groups : (∑ w ∈ U, tourPotTerm (cord' w).length) + totalNonMaxLen cord' gs maxIdxs ≤
      ∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length := by
    rw [hU_sum, ← hold_sum, totalNonMaxLen, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun gi hgi => ?_
    have hlt := Finset.mem_range.mp hgi
    rw [List.getD_eq_getElem gs [] hlt, List.getD_eq_getElem oldRoots 0 (by omega)]
    exact hgrp_ineq gi hlt
  have hrest_sub : R_new \ U ⊆ R_old \ oldRoots.toFinset := by
    intro r hr
    obtain ⟨hrN, hrU⟩ := Finset.mem_sdiff.mp hr
    have hnot : ∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset := fun gi hgi hmem =>
      hrU (Finset.mem_biUnion.mpr ⟨gi, Finset.mem_range.mpr hgi, by rwa [List.getD_eq_getElem gs [] hgi]⟩)
    obtain ⟨hrO, hrNO, _⟩ := hrest_le r hrN hnot
    exact Finset.mem_sdiff.mpr ⟨hrO, fun h => hrNO (List.mem_toFinset.mp h)⟩
  have hrest_sum : ∑ r ∈ R_new \ U, tourPotTerm (cord' r).length ≤
      ∑ r ∈ R_old \ oldRoots.toFinset, tourPotTerm (cord r).length := by
    refine le_trans (Finset.sum_le_sum fun r hr => ?_) (Finset.sum_le_sum_of_subset hrest_sub)
    obtain ⟨hrN, hrU⟩ := Finset.mem_sdiff.mp hr
    have hnot : ∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset := fun gi hgi hmem =>
      hrU (Finset.mem_biUnion.mpr ⟨gi, Finset.mem_range.mpr hgi, by rwa [List.getD_eq_getElem gs [] hgi]⟩)
    exact tourPotTerm_mono (hrest_le r hrN hnot).2.2
  have hold_fin_sub : oldRoots.toFinset ⊆ R_old := fun r hr => hold_sub r (List.mem_toFinset.mp hr)
  have hRold_split : tourPot R_old cord =
      (∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length) +
        (∑ r ∈ R_old \ oldRoots.toFinset, tourPotTerm (cord r).length) := by
    unfold tourPot
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hold_fin_sub]
  rw [hRnew_split, hRold_split]
  omega

/-- Generalization of `scanNonMaxSum_le_tourPot_drop` allowing added ends (`addG` per split group,
`addR` per unsplit root, e.g. from insertions, re-inserted edges, or released tree edges in the
same batch) with maximum post-batch tour length bounded by `maxLen`. -/
theorem scanNonMaxSum_le_tourPot_drop_with_adds
    {R_old R_new : Finset ℕ} {cord cord' : ℕ → List End}
    {gs : List (List ℕ)} {oldRoots maxIdxs : List ℕ}
    {addG : ℕ → ℕ} {addR : ℕ → ℕ} {maxLen : ℕ}
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ w ∈ G, w ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hmax_spec : ∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
      ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length)
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ w ∈ gs[gi].toFinset, (cord' w).length) ≤ (cord (oldRoots[gi]'(by omega))).length + addG gi ∧
      (cord (oldRoots[gi]'(by omega))).length + addG gi ≤ maxLen)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧ (cord' r).length ≤ (cord r).length + addR r ∧
      (cord r).length + addR r ≤ maxLen) :
    let U := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    let totalAdded := (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U, addR r
    tourPot R_new cord' + totalNonMaxLen cord' gs maxIdxs ≤
      tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2) := by
  intro U totalAdded
  have hgrp_ineq : ∀ gi (hgi : gi < gs.length),
      (∑ w ∈ gs[gi].toFinset, tourPotTerm (cord' w).length) +
        (∑ j ∈ (Finset.range gs[gi].length).erase (maxIdxs.getD gi 0), (cord' (gs[gi].getD j 0)).length) ≤
      tourPotTerm (cord (oldRoots[gi]'(by omega))).length + addG gi * (Nat.log 2 maxLen + 2) := by
    intro gi hgi
    obtain ⟨hm, hmax⟩ := hmax_spec gi hgi
    set wMax := gs[gi][maxIdxs.getD gi 0]'hm
    have hnd := hgs_nd gs[gi] (List.getElem_mem hgi)
    have hsum_er :
        (∑ j ∈ (Finset.range gs[gi].length).erase (maxIdxs.getD gi 0), (cord' (gs[gi].getD j 0)).length) =
          ∑ w ∈ gs[gi].toFinset.erase wMax, (cord' w).length := by
      refine Finset.sum_bij (fun j _ => gs[gi].getD j 0) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro j hj
        obtain ⟨hj_ne, hj_r⟩ := Finset.mem_erase.mp hj
        have hj_lt := Finset.mem_range.mp hj_r
        rw [List.getD_eq_getElem _ _ hj_lt]
        refine Finset.mem_erase.mpr ⟨fun heq => hj_ne (hnd.getElem_inj_iff.mp heq),
          List.mem_toFinset.mpr (List.getElem_mem hj_lt)⟩
      · intro j1 hj1 j2 hj2 heq
        have h1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj1)
        have h2 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj2)
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at heq
        exact hnd.getElem_inj_iff.mp heq
      · intro w hw
        obtain ⟨hw_ne, hw_in⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw_in)
        exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hw_ne (by simp [wMax, h]), Finset.mem_range.mpr hj⟩,
          List.getD_eq_getElem _ _ hj⟩
    rw [hsum_er]
    have hsplit := tourPotTerm_sum_split (G := gs[gi].toFinset) (L := fun w => (cord' w).length) (w_max := wMax)
      (List.mem_toFinset.mpr (List.getElem_mem hm))
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
        exact hmax j hj)
    obtain ⟨hsum_le, hmax_le⟩ := hgroup_sum_le gi hgi
    have hadd := tourPotTerm_add_le (cord (oldRoots[gi]'(by omega))).length (addG gi)
    have hlog_le : addG gi * (Nat.log 2 ((cord (oldRoots[gi]'(by omega))).length + addG gi) + 2) ≤
        addG gi * (Nat.log 2 maxLen + 2) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right hmax_le) 2)
    exact (le_trans hsplit (tourPotTerm_mono hsum_le)).trans (hadd.trans (Nat.add_le_add_left hlog_le _))
  have hU_sub : U ⊆ R_new := by
    intro w hw
    obtain ⟨gi, hgi, hw'⟩ := Finset.mem_biUnion.mp hw
    have hlt := Finset.mem_range.mp hgi
    rw [List.getD_eq_getElem gs [] hlt, List.mem_toFinset] at hw'
    exact hgs_sub _ (List.getElem_mem hlt) w hw'
  have hU_sum : ∑ w ∈ U, tourPotTerm (cord' w).length =
      ∑ gi ∈ Finset.range gs.length, ∑ w ∈ (gs.getD gi []).toFinset, tourPotTerm (cord' w).length := by
    refine Finset.sum_biUnion fun i hi j hj hij => ?_
    have hi' := Finset.mem_range.mp hi; have hj' := Finset.mem_range.mp hj
    change Disjoint (gs.getD i []).toFinset (gs.getD j []).toFinset
    rw [List.getD_eq_getElem gs [] hi', List.getD_eq_getElem gs [] hj']
    exact hgs_disj i hi' j hj' hij
  have hRnew_split : tourPot R_new cord' =
      (∑ w ∈ U, tourPotTerm (cord' w).length) + (∑ r ∈ R_new \ U, tourPotTerm (cord' r).length) := by
    unfold tourPot
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hU_sub]
  have hold_sum : ∑ gi ∈ Finset.range gs.length, tourPotTerm (cord (oldRoots.getD gi 0)).length =
      ∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length := by
    refine Finset.sum_bij (fun gi _ => oldRoots.getD gi 0) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro gi hgi
      have hlt : gi < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hgi
      rw [List.getD_eq_getElem _ _ hlt, List.mem_toFinset]; exact List.getElem_mem hlt
    · intro i hi j hj heq
      have hi' : i < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hi
      have hj' : j < oldRoots.length := by rw [hold_len]; exact Finset.mem_range.mp hj
      rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at heq
      exact hold_nd.getElem_inj_iff.mp heq
    · intro r hr
      obtain ⟨gi, hgi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hr)
      exact ⟨gi, Finset.mem_range.mpr (by omega), List.getD_eq_getElem _ _ hgi⟩
  have hsum_groups : (∑ w ∈ U, tourPotTerm (cord' w).length) + totalNonMaxLen cord' gs maxIdxs ≤
      (∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length) +
        (∑ gi ∈ Finset.range gs.length, addG gi) * (Nat.log 2 maxLen + 2) := by
    rw [hU_sum, ← hold_sum, totalNonMaxLen, ← Finset.sum_add_distrib, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun gi hgi => ?_
    have hlt := Finset.mem_range.mp hgi
    rw [List.getD_eq_getElem gs [] hlt, List.getD_eq_getElem oldRoots 0 (by omega)]
    exact hgrp_ineq gi hlt
  have hrest_sub : R_new \ U ⊆ R_old \ oldRoots.toFinset := by
    intro r hr
    obtain ⟨hrN, hrU⟩ := Finset.mem_sdiff.mp hr
    have hnot : ∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset := fun gi hgi hmem =>
      hrU (Finset.mem_biUnion.mpr ⟨gi, Finset.mem_range.mpr hgi, by rwa [List.getD_eq_getElem gs [] hgi]⟩)
    obtain ⟨hrO, hrNO, _, _⟩ := hrest_le r hrN hnot
    exact Finset.mem_sdiff.mpr ⟨hrO, fun h => hrNO (List.mem_toFinset.mp h)⟩
  have hrest_sum : ∑ r ∈ R_new \ U, tourPotTerm (cord' r).length ≤
      (∑ r ∈ R_old \ oldRoots.toFinset, tourPotTerm (cord r).length) +
        (∑ r ∈ R_new \ U, addR r) * (Nat.log 2 maxLen + 2) := by
    have h1 : ∑ r ∈ R_new \ U, tourPotTerm (cord' r).length ≤
        ∑ r ∈ R_new \ U, (tourPotTerm (cord r).length + addR r * (Nat.log 2 maxLen + 2)) := by
      refine Finset.sum_le_sum fun r hr => ?_
      obtain ⟨hrN, hrU⟩ := Finset.mem_sdiff.mp hr
      have hnot : ∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset := fun gi hgi hmem =>
        hrU (Finset.mem_biUnion.mpr ⟨gi, Finset.mem_range.mpr hgi, by rwa [List.getD_eq_getElem gs [] hgi]⟩)
      obtain ⟨_, _, hlen_le, hmax_le⟩ := hrest_le r hrN hnot
      have hadd := tourPotTerm_add_le (cord r).length (addR r)
      have hlog_le : addR r * (Nat.log 2 ((cord r).length + addR r) + 2) ≤
          addR r * (Nat.log 2 maxLen + 2) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right hmax_le) 2)
      exact (tourPotTerm_mono hlen_le).trans (hadd.trans (Nat.add_le_add_left hlog_le _))
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    exact h1.trans (Nat.add_le_add_right (Finset.sum_le_sum_of_subset hrest_sub) _)
  have hold_fin_sub : oldRoots.toFinset ⊆ R_old := fun r hr => hold_sub r (List.mem_toFinset.mp hr)
  have hRold_split : tourPot R_old cord =
      (∑ r ∈ oldRoots.toFinset, tourPotTerm (cord r).length) +
        (∑ r ∈ R_old \ oldRoots.toFinset, tourPotTerm (cord r).length) := by
    unfold tourPot
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hold_fin_sub]
  rw [hRnew_split, hRold_split]
  have hdist : totalAdded * (Nat.log 2 maxLen + 2) =
      (∑ gi ∈ Finset.range gs.length, addG gi) * (Nat.log 2 maxLen + 2) +
      (∑ r ∈ R_new \ U, addR r) * (Nat.log 2 maxLen + 2) := Nat.add_mul _ _ _
  omega

end

end MinCostFlow.SparseCore.Program
