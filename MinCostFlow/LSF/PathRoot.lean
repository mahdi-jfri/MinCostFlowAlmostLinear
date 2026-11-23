module

public import MinCostFlow.LSF.LemmaB9
public import Mathlib.Data.Finset.Max

/-!
# Path-Root theorem and level-set stretch upper bounds

This file proves the Key Path-Root theorem and stretch overestimates `wstr_e` underlying
`[chen2022maximum, Lemma 6.5 / Appendix B.3]` and Lemma 5.4:
* `lca_heavyChain_common_ancestor_on_path`: for any `u, v ∈ V(T)`, there is a common
  `T_H`-ancestor `z*` of `u` and `v` lying on `T[u, v]`.
* `levelRoots T r i`: the prefix `{w ∈ V(T) | depth T_H r w ≤ i}` (`B_i` in `[chen2022maximum]`).
* `root_mem_forestPath_of_agree`: when `u` and `v` share a root in `F_i` (`i = deepestRootDepth`)
  and either `root^F_u ≠ root^F_v` or `v ∈ R^{↑ T_H}`, we have `root^F_u ∈ T[u, v]`.
* `endpoint_stretch_le_level`: `1 + len(T[u, root^F_u]) / ℓ_e ≤ str^{F_i, ℓ}_e` when `v` and `u`
  have different roots in `F` or `v ∈ R^{↑ T_H}`.
* `levelStretchBound`: the `wstr` bound `2 * ∑_{i=0}^D str^{F_i, ℓ}_e` (`[chen2022maximum, (B.3)]`).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Common `T_H`-ancestor on `T[u, v]` -/

lemma lca_isAncestor_TH_left_or_right {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    IsAncestor (hldAuxTree T r) r (lca T r u v) u ∨
      IsAncestor (hldAuxTree T r) r (lca T r u v) v := by
  have hbf := upClosure_isBranchFree hT (R := {u, v}) (by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hu_mem : u ∈ upClosure (hldAuxTree T r) r {u, v} :=
    subset_upClosure (Finset.mem_insert_self u {v})
  have hv_mem : v ∈ upClosure (hldAuxTree T r) r {u, v} :=
    subset_upClosure (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  have hlca := hbf.2 u hu_mem v hv_mem
  rw [mem_upClosure_iff] at hlca
  obtain ⟨x, hx, hanc⟩ := hlca
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Or.inl hanc
  · exact Or.inr hanc

lemma lca_heavyChain_common_ancestor_on_path {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) :
    ∃ zstar ∈ T.V, IsAncestor (hldAuxTree T r) r zstar u ∧ IsAncestor (hldAuxTree T r) r zstar v ∧
      zstar ∈ T.walkVertices u (T.forestPath u v) := by
  classical
  have hTH := hldAuxTree_isRootedTree hT
  have hwV : lca T r u v ∈ T.V := lca_mem hT hu hv
  have hwu : IsAncestor T r (lca T r u v) u := lca_isAncestor_left hT hu hv
  have hwv : IsAncestor T r (lca T r u v) v := lca_isAncestor_right hT hu hv
  let Cw := chainOf T r (lca T r u v)
  have hCw : Cw ∈ heavyChains T r := chainOf_mem_heavyChains hwV
  have hwCw : lca T r u v ∈ Cw := mem_chainOf_self hwV
  have hside : ∀ {x : ℕ}, x ∈ T.V → IsAncestor T r (lca T r u v) x →
      ∃ zstar ∈ T.V, IsAncestor (hldAuxTree T r) r zstar (lca T r u v) ∧
        IsAncestor (hldAuxTree T r) r zstar x ∧
        IsAncestor T r (lca T r u v) zstar ∧ IsAncestor T r zstar x := by
    intro x hxV hwx
    let S := Cw.filter (fun z => IsAncestor T r z x)
    have hSne : S.Nonempty := ⟨lca T r u v, Finset.mem_filter.mpr ⟨hwCw, hwx⟩⟩
    obtain ⟨b, hbS, hbmax⟩ := Finset.exists_max_image S (depth T r) hSne
    rw [Finset.mem_filter] at hbS
    have hbV := (heavyChain_subset hCw).2 hbS.1
    have hb_TH : IsAncestor (hldAuxTree T r) r b x :=
      light_transition_isAncestor_TH hT _ x Cw b rfl hxV hCw hbS.1 hbS.2
        (fun q hqC hqx => hbmax q (Finset.mem_filter.mpr ⟨hqC, hqx⟩))
    obtain ⟨hzC, hlo, hhi⟩ := lca_TH_in_chain_depth_between hT hCw hwCw hbS.1
    have hzV := (heavyChain_subset hCw).2 hzC
    have hzw_TH := lca_isAncestor_left hTH hwV hbV
    have hzb_TH := lca_isAncestor_right hTH hwV hbV
    have hwb_T : IsAncestor T r (lca T r u v) b := by
      rcases isAncestor_total_on_ancestors hT hxV hwx hbS.2 with h1 | h2
      · exact h1
      · have hdw := hbmax (lca T r u v) (Finset.mem_filter.mpr ⟨hwCw, hwx⟩)
        have hd1 := isAncestor_depth_le hT hwV h2
        rw [(isAncestor_eq_iff_depth hT hwV h2).mp (Nat.le_antisymm hd1 hdw)]
        exact isAncestor_refl _ _ _
    have hz_wb := heavyChain_mem_forestPath_of_depth_between hT hCw hwCw hbS.1 hzC hlo hhi
    rw [forestPath_rev hT.isForest (hT.connected hbV hwV), walkVertices_walkRev
      (forestPath_isPath hT.isForest (hT.connected hbV hwV)).1, List.mem_reverse,
      mem_walkVertices_ancestorPath_iff hT hbV hwb_T] at hz_wb
    exact ⟨lca (hldAuxTree T r) r (lca T r u v) b, hzV, hzw_TH,
      isAncestor_trans hTH hxV hzb_TH hb_TH, hz_wb.1, isAncestor_trans hT hxV hz_wb.2 hbS.2⟩
  rcases lca_isAncestor_TH_left_or_right hT hu hv with hwu_TH | hwv_TH
  · obtain ⟨zstar, hzV, hzw_TH, hzv_TH, hzw_T, hzv_T⟩ := hside hv hwv
    exact ⟨zstar, hzV, isAncestor_trans hTH hu hzw_TH hwu_TH, hzv_TH,
      (mem_walkVertices_forestPath_iff hT hu hv).mpr ⟨hzw_T, Or.inr hzv_T⟩⟩
  · obtain ⟨zstar, hzV, hzw_TH, hzu_TH, hzw_T, hzu_T⟩ := hside hu hwu
    exact ⟨zstar, hzV, hzu_TH, isAncestor_trans hTH hv hzw_TH hwv_TH,
      (mem_walkVertices_forestPath_iff hT hu hv).mpr ⟨hzw_T, Or.inl hzu_T⟩⟩

/-! ## Level root sets `B_i` and the Key Path-Root Theorem -/

/-- `levelRoots T r i = B_i = {w ∈ V(T) | depth T_H r w ≤ i}` (`[chen2022maximum, Appendix B.3]`). -/
noncomputable def levelRoots (T : MGraph) (r i : ℕ) : Finset ℕ :=
  open Classical in
  T.V.filter (fun w => depth (hldAuxTree T r) r w ≤ i)

lemma levelRoots_subset {T : MGraph} {r i : ℕ} : levelRoots T r i ⊆ T.V := by
  classical
  exact Finset.filter_subset _ _

lemma root_mem_levelRoots {T : MGraph} {r i : ℕ} (hT : IsRootedTree T r) :
    r ∈ levelRoots T r i := by
  classical
  refine Finset.mem_filter.mpr ⟨hT.2, ?_⟩
  unfold depth
  rw [forestPath_self (hldAuxTree_isRootedTree hT).isForest r, List.length_nil]
  exact Nat.zero_le _

lemma levelRoots_zero {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    levelRoots T r 0 = {r} := by
  classical
  have hTH := hldAuxTree_isRootedTree hT
  apply Finset.ext
  intro w
  simp only [levelRoots, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hwV, hdw⟩
    have hrw := isAncestor_root hTH (show w ∈ (hldAuxTree T r).V from hwV)
    have hdr : depth (hldAuxTree T r) r r = 0 := by
      unfold depth; rw [forestPath_self hTH.isForest r, List.length_nil]
    exact (isAncestor_eq_iff_depth hTH hwV hrw).mp (by omega) |>.symm
  · intro hEq
    rw [hEq]
    refine ⟨hT.2, ?_⟩
    unfold depth; rw [forestPath_self hTH.isForest r, List.length_nil]

lemma upClosure_levelRoots {T : MGraph} {r i : ℕ} (hT : IsRootedTree T r) :
    upClosure (hldAuxTree T r) r (levelRoots T r i) = levelRoots T r i := by
  classical
  have hTH := hldAuxTree_isRootedTree hT
  apply Finset.Subset.antisymm _ subset_upClosure
  intro w hw
  rw [mem_upClosure_iff] at hw
  obtain ⟨u, hu, hwu⟩ := hw
  rw [levelRoots, Finset.mem_filter] at hu ⊢
  have huTH : u ∈ (hldAuxTree T r).V := hu.1
  have hwTH : w ∈ (hldAuxTree T r).V := isAncestor_mem hTH huTH hwu
  exact ⟨hwTH, le_trans (isAncestor_depth_le hTH huTH hwu) hu.2⟩

lemma forestGivenRoots_levelZero {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (π : ℕ → ℕ) :
    forestGivenRoots T r (levelRoots T r 0) π = T ∧
      ∀ u ∈ T.V, (rootedForestGivenRoots T r (levelRoots T r 0) π).root u = r := by
  rw [levelRoots_zero hT]
  have hbf : IsBranchFree T r {r} := ⟨Finset.singleton_subset_iff.mpr hT.2, by
    intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy, lca_self hT hT.2]
    exact Finset.mem_singleton_self r⟩
  have hdel : deletedEdges T r {r} π = ∅ := by
    classical
    unfold deletedEdges
    rw [ite_eq_left_iff.mpr (fun h => absurd (Finset.singleton_nonempty r) h)]
    have htop : topRoot T r {r} = r :=
      Finset.mem_singleton.mp (topRoot_spec hT hbf (Finset.singleton_nonempty r)).1
    rw [htop, Finset.erase_singleton, Finset.image_empty]
  have hF : forestGivenRoots T r {r} π = T := by
    unfold forestGivenRoots
    rw [hdel]
    cases T; simp [Finset.sdiff_empty]
  refine ⟨hF, fun u hu => ?_⟩
  exact forestGivenRoots_root_eq_of_connected hT hbf (Finset.singleton_nonempty r) π hu
    (Finset.mem_singleton_self r) (by rw [hF]; exact hT.connected hu hT.2)

/-- The deepest `T_H`-depth of any vertex in `R' ∩ u^{↑ T_H}`. -/
noncomputable def deepestRootDepth (T : MGraph) (r : ℕ) (R' : Finset ℕ) (u : ℕ) : ℕ :=
  open Classical in
  if h : (R' ∩ ancestors (hldAuxTree T r) r u).Nonempty then
    ((R' ∩ ancestors (hldAuxTree T r) r u).image (depth (hldAuxTree T r) r)).max'
      (Finset.Nonempty.image h _)
  else 0

lemma deepestRootDepth_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R' : Finset ℕ} {u : ℕ} (hu : u ∈ T.V) :
    deepestRootDepth T r R' u ≤ depth (hldAuxTree T r) r u := by
  classical
  have hTH := hldAuxTree_isRootedTree hT
  unfold deepestRootDepth
  split_ifs with hne
  · apply Finset.max'_le
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    rw [Finset.mem_inter, mem_ancestors_iff] at hw
    exact isAncestor_depth_le hTH hu hw.2
  · exact Nat.zero_le _

lemma inter_ancestors_eq_levelRoots {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty) {u : ℕ} (hu : u ∈ T.V) :
    let R' := upClosure (hldAuxTree T r) r R
    let i := deepestRootDepth T r R' u
    R' ∩ ancestors (hldAuxTree T r) r u = levelRoots T r i ∩ ancestors (hldAuxTree T r) r u := by
  classical
  have hTH := hldAuxTree_isRootedTree hT
  let R' := upClosure (hldAuxTree T r) r R
  have hr_R' : r ∈ R' := by
    obtain ⟨x, hxR⟩ := hRne
    exact mem_upClosure_iff.mpr ⟨x, hxR, isAncestor_root hTH (hR hxR)⟩
  have hne : (R' ∩ ancestors (hldAuxTree T r) r u).Nonempty :=
    ⟨r, Finset.mem_inter.mpr ⟨hr_R', mem_ancestors_iff.mpr (isAncestor_root hTH hu)⟩⟩
  have hi_def : deepestRootDepth T r R' u =
      ((R' ∩ ancestors (hldAuxTree T r) r u).image (depth (hldAuxTree T r) r)).max'
        (Finset.Nonempty.image hne _) := by
    unfold deepestRootDepth; exact dite_eq_left_of_eq_true (eq_true hne)
  have hi_mem : deepestRootDepth T r R' u ∈
      (R' ∩ ancestors (hldAuxTree T r) r u).image (depth (hldAuxTree T r) r) := by
    rw [hi_def]; exact Finset.max'_mem _ _
  rw [Finset.mem_image] at hi_mem
  obtain ⟨x, hx_inter, hdx⟩ := hi_mem
  rw [Finset.mem_inter, mem_ancestors_iff] at hx_inter
  apply Finset.ext
  intro w
  simp only [Finset.mem_inter, levelRoots, Finset.mem_filter, mem_ancestors_iff]
  constructor
  · rintro ⟨hwR, hwu⟩
    have hwTH : w ∈ (hldAuxTree T r).V := isAncestor_mem hTH (hu : u ∈ (hldAuxTree T r).V) hwu
    refine ⟨⟨hwTH, ?_⟩, hwu⟩
    rw [hi_def]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_inter.mpr ⟨hwR, mem_ancestors_iff.mpr hwu⟩))
  · rintro ⟨⟨_, hdw⟩, hwu⟩
    have hwTH : w ∈ (hldAuxTree T r).V := isAncestor_mem hTH (hu : u ∈ (hldAuxTree T r).V) hwu
    have hwx : IsAncestor (hldAuxTree T r) r w x := by
      rcases isAncestor_total_on_ancestors hTH hu hwu hx_inter.2 with h1 | h2
      · exact h1
      · have hle := isAncestor_depth_le hTH hwTH h2
        have hdw_le_x : depth (hldAuxTree T r) r w ≤ depth (hldAuxTree T r) r x := by
          rw [← hdx] at hdw; exact hdw
        have hd_eq : depth (hldAuxTree T r) r x = depth (hldAuxTree T r) r w :=
          Nat.le_antisymm hle hdw_le_x
        rw [← (isAncestor_eq_iff_depth hTH hwTH h2).mp hd_eq]
        exact isAncestor_refl _ _ _
    exact ⟨upClosure_isUpwardClosed hTH hR hx_inter.1 hwx, hwu⟩

/-- **Key Path-Root Theorem**: let `R' = R^{↑ T_H}`, `F = F_T(R', π)`, and
`i = deepestRootDepth T r R' u`. If `u` and `v` share a root in `F_i = F_T(B_i, π)`, and either
`root^F_u ≠ root^F_v` or `v ∈ R'`, then `root^F_u ∈ T[u, v]`. -/
lemma root_mem_forestPath_of_agree {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V) :
    let R' := upClosure (hldAuxTree T r) r R
    let i := deepestRootDepth T r R' u
    let RF := rootedForestGivenRoots T r R' π
    let RFi := rootedForestGivenRoots T r (levelRoots T r i) π
    RFi.root u = RFi.root v → (RF.root u ≠ RF.root v ∨ v ∈ R') →
    RF.root u ∈ T.walkVertices u (T.forestPath u v) := by
  intro R' i RF RFi h_same hcond
  classical
  have hTH := hldAuxTree_isRootedTree hT
  have hR'V : R' ⊆ T.V := upClosure_subset hTH hR
  have hBiV : levelRoots T r i ⊆ T.V := levelRoots_subset
  have hBi_ne : (levelRoots T r i).Nonempty := ⟨r, root_mem_levelRoots hT⟩
  have hR'bf : IsBranchFree T r R' := upClosure_isBranchFree hT hR
  have hBibf : IsBranchFree T r (levelRoots T r i) :=
    upClosure_levelRoots hT ▸ upClosure_isBranchFree hT levelRoots_subset
  have hR'ne : R'.Nonempty := ⟨r, by
    obtain ⟨q, hq⟩ := hRne; exact mem_upClosure_iff.mpr ⟨q, hq, isAncestor_root hTH (hR hq)⟩⟩
  have hinter_u := inter_ancestors_eq_levelRoots hT hR hRne hu
  have hroot_u : RF.root u = RFi.root u := by
    have h1 := upClosure_root_eq_of_inter_eq hT hord hR hBiV hRne hBi_ne hu
      (by rwa [upClosure_levelRoots hT])
    simpa only [upClosure_levelRoots hT] using h1
  obtain ⟨zstar, hzV, hzu_TH, hzv_TH, hz_path⟩ :=
    lca_heavyChain_common_ancestor_on_path hT hu hv
  have hz_R' : zstar ∈ R' := by
    rcases hcond with hdiff | hvR'
    · by_contra hz_not_R'
      have hv_inter : R' ∩ ancestors (hldAuxTree T r) r v =
          levelRoots T r i ∩ ancestors (hldAuxTree T r) r v := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_inter, mem_ancestors_iff]
        constructor
        · rintro ⟨hwR, hwv⟩
          have hwz : IsAncestor (hldAuxTree T r) r w zstar := by
            rcases isAncestor_total_on_ancestors hTH hv hwv hzv_TH with h1 | h2
            · exact h1
            · exact absurd (upClosure_isUpwardClosed hTH hR hwR h2) hz_not_R'
          have hwu := isAncestor_trans hTH hu hwz hzu_TH
          have hmem := Finset.mem_inter.mpr ⟨hwR, mem_ancestors_iff.mpr hwu⟩
          rw [hinter_u, Finset.mem_inter] at hmem
          exact ⟨hmem.1, hwv⟩
        · rintro ⟨hwBi, hwv⟩
          have hdw : depth (hldAuxTree T r) r w ≤ i := (Finset.mem_filter.mp hwBi).2
          have hwz : IsAncestor (hldAuxTree T r) r w zstar := by
            rcases isAncestor_total_on_ancestors hTH hv hwv hzv_TH with h1 | h2
            · exact h1
            · exfalso
              have hle_z := isAncestor_depth_le hTH (isAncestor_mem hTH hv hwv) h2
              have hne_u : (R' ∩ ancestors (hldAuxTree T r) r u).Nonempty := ⟨r, Finset.mem_inter.mpr
                ⟨by obtain ⟨q, hq⟩ := hRne; exact mem_upClosure_iff.mpr ⟨q, hq, isAncestor_root hTH (hR hq)⟩,
                 mem_ancestors_iff.mpr (isAncestor_root hTH hu)⟩⟩
              have hi_def : i = ((R' ∩ ancestors (hldAuxTree T r) r u).image (depth (hldAuxTree T r) r)).max'
                  (Finset.Nonempty.image hne_u _) := by
                change deepestRootDepth T r R' u = _
                unfold deepestRootDepth; exact dite_eq_left_of_eq_true (eq_true hne_u)
              have hi_mem : i ∈ (R' ∩ ancestors (hldAuxTree T r) r u).image (depth (hldAuxTree T r) r) := by
                rw [hi_def]; exact Finset.max'_mem _ _
              rw [Finset.mem_image] at hi_mem
              obtain ⟨x, hx_in, hdx⟩ := hi_mem
              rw [Finset.mem_inter, mem_ancestors_iff] at hx_in
              have hzx : IsAncestor (hldAuxTree T r) r zstar x := by
                rcases isAncestor_total_on_ancestors hTH hu hzu_TH hx_in.2 with h1' | h2'
                · exact h1'
                · have := isAncestor_depth_le hTH hzV h2'
                  have hd_eq : depth (hldAuxTree T r) r zstar = depth (hldAuxTree T r) r x := by omega
                  rw [(isAncestor_eq_iff_depth hTH hzV h2').mp hd_eq.symm]
                  exact isAncestor_refl _ _ _
              exact hz_not_R' (upClosure_isUpwardClosed hTH hR hx_in.1 hzx)
          have hwu := isAncestor_trans hTH hu hwz hzu_TH
          have hmem := Finset.mem_inter.mpr ⟨hwBi, mem_ancestors_iff.mpr hwu⟩
          rw [← hinter_u, Finset.mem_inter] at hmem
          exact ⟨hmem.1, hwv⟩
      have hroot_v : RF.root v = RFi.root v := by
        have h1 := upClosure_root_eq_of_inter_eq hT hord hR hBiV hRne hBi_ne hv
          (by rwa [upClosure_levelRoots hT])
        simpa only [upClosure_levelRoots hT] using h1
      exact absurd (hroot_u.trans (h_same.trans hroot_v.symm)) hdiff
    · exact upClosure_isUpwardClosed hTH hR hvR' hzv_TH
  have hz_Bi : zstar ∈ levelRoots T r i := by
    have hmem := Finset.mem_inter.mpr ⟨hz_R', mem_ancestors_iff.mpr hzu_TH⟩
    rw [hinter_u, Finset.mem_inter] at hmem
    exact hmem.1
  have hRSi := forestGivenRoots_isRootedSpanningForest hT hBibf hBi_ne π
  have hru_Bi : RFi.root u ∈ levelRoots T r i := (rootedForest_root_spec hRSi hu).1
  have hconn_uz : (forestGivenRoots T r (levelRoots T r i) π).Connected u zstar := by
    have hconn_ur := (rootedForest_root_spec hRSi hu).2
    have hconn_vr := (rootedForest_root_spec hRSi hv).2
    have hconn_uv : (forestGivenRoots T r (levelRoots T r i) π).Connected u v :=
      connected_trans hconn_ur (connected_symm (h_same ▸ hconn_vr))
    exact (forest_connected_along_path hT π hu hv hconn_uv hz_path).1
  have hz_eq : RFi.root u = zstar := by
    by_contra hne
    have hconn_rz := connected_trans (connected_symm (rootedForest_root_spec hRSi hu).2) hconn_uz
    exact forestGivenRoots_not_connected_roots hT hBibf hBi_ne π hru_Bi hz_Bi hne hconn_rz
  rw [hroot_u, hz_eq]
  exact hz_path

/-! ## Endpoint stretch and `levelStretchBound` -/

lemma forestPath_walkLength_le_of_mem {T : MGraph} {ℓ : ℕ → ℝ} (hT : T.IsForest)
    (hℓ : ∀ e ∈ T.E, 0 ≤ ℓ e) {u v z : ℕ} (hconn : T.Connected u v)
    (hz : z ∈ T.walkVertices u (T.forestPath u v)) :
    walkLength ℓ (T.forestPath u z) ≤ walkLength ℓ (T.forestPath u v) := by
  have hP := forestPath_isPath hT hconn
  obtain ⟨hsplit, _⟩ := forestPath_mem_walkVertices_split hT hconn hz
  have hsub : walkEdges (T.forestPath u z) ⊆ walkEdges (T.forestPath u v) := by
    intro e he; rw [hsplit, walkEdges_append, Finset.mem_union]; exact Or.inl he
  have hconn_uz : T.Connected u z := by
    obtain ⟨P₁, _, _, h1, _⟩ := walkVertices_mem_split hP.1 hz
    exact ⟨P₁, h1⟩
  rw [walkLength_eq_sum_of_isPath ℓ (forestPath_isPath hT hconn_uz),
      walkLength_eq_sum_of_isPath ℓ hP]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ => hℓ e ?_)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  exact IsWalk_edges_mem hP.1 hx

lemma rootedForest_stretch_ge_one {RF : RootedForest} {G : MGraph} (hF : RF.F.IsForest)
    {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ RF.F.E, 0 ≤ ℓ f) {e : ℕ} (hℓe : 0 < ℓ e) :
    1 ≤ RF.stretch G ℓ e := by
  unfold RootedForest.stretch
  dsimp only
  have hwl : ∀ a b, 0 ≤ walkLength ℓ (RF.F.forestPath a b) := by
    intro a b
    by_cases h : RF.F.Connected a b
    · have hP := forestPath_isPath hF h
      exact walkLength_nonneg_of_nonneg ℓ (fun f hf => hℓ f (by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
        exact IsWalk_edges_mem hP.1 hx))
    · have hfp : RF.F.forestPath a b = [] := by
        unfold MGraph.forestPath
        rw [dite_eq_right_of_eq_false (eq_false (fun ⟨Q, hQ⟩ => h ⟨Q, hQ.1⟩))]
      rw [hfp]; simp [walkLength, walkEdges]
  split_ifs
  · exact le_add_of_nonneg_right (div_nonneg (hwl _ _) hℓe.le)
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg (hwl _ _) (hwl _ _)) hℓe.le)

lemma stretch_swap_eq (RF : RootedForest) (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ)
    (hF : RF.F.IsForest) :
    RF.stretch { G with tail := Function.update G.tail e (G.head e),
                         head := Function.update G.head e (G.tail e) } ℓ e =
      RF.stretch G ℓ e := by
  unfold RootedForest.stretch
  dsimp only
  simp only [Function.update_self]
  by_cases hEq : RF.root (G.head e) = RF.root (G.tail e)
  · rw [ite_eq_left_iff.mpr (fun h => absurd hEq h),
        ite_eq_left_iff.mpr (fun h => absurd hEq.symm h)]
    have hlen : walkLength ℓ (RF.F.forestPath (G.head e) (G.tail e)) =
        walkLength ℓ (RF.F.forestPath (G.tail e) (G.head e)) := by
      by_cases hc : RF.F.Connected (G.tail e) (G.head e)
      · rw [forestPath_rev hF hc]
        have hP := forestPath_isPath hF hc
        rw [walkLength_eq_sum_of_isPath ℓ hP, walkLength_eq_sum_of_isPath ℓ (IsPath_walkRev hP),
            walkEdges_walkRev]
      · have h1 : RF.F.forestPath (G.head e) (G.tail e) = [] := by
          unfold MGraph.forestPath
          exact dite_eq_right_of_eq_false (eq_false (fun ⟨Q, hQ⟩ => hc ⟨walkRev Q, (IsPath_walkRev hQ).1⟩))
        have h2 : RF.F.forestPath (G.tail e) (G.head e) = [] := by
          unfold MGraph.forestPath
          exact dite_eq_right_of_eq_false (eq_false (fun ⟨Q, hQ⟩ => hc ⟨Q, hQ.1⟩))
        rw [h1, h2]
    rw [hlen]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hEq),
        ite_eq_right_iff.mpr (fun h => absurd h.symm hEq), add_comm (walkLength _ _)]

lemma endpoint_stretch_le_level {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V)
    {G : MGraph} {e : ℕ} (htail : G.tail e = u) (hhead : G.head e = v)
    {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ T.E, 0 ≤ ℓ f) (hℓe : 0 < ℓ e) :
    let R' := upClosure (hldAuxTree T r) r R
    let i := deepestRootDepth T r R' u
    let RF := rootedForestGivenRoots T r R' π
    let RFi := rootedForestGivenRoots T r (levelRoots T r i) π
    (RF.root u ≠ RF.root v ∨ v ∈ R') →
    1 + walkLength ℓ (T.forestPath u (RF.root u)) / ℓ e ≤ RFi.stretch G ℓ e := by
  intro R' i RF RFi hcond
  have hTH := hldAuxTree_isRootedTree hT
  have hBiV : levelRoots T r i ⊆ T.V := levelRoots_subset
  have hBi_ne : (levelRoots T r i).Nonempty := ⟨r, root_mem_levelRoots hT⟩
  have hBibf : IsBranchFree T r (levelRoots T r i) :=
    upClosure_levelRoots hT ▸ upClosure_isBranchFree hT levelRoots_subset
  have hRSi := forestGivenRoots_isRootedSpanningForest hT hBibf hBi_ne π
  have hsub_i : T.IsSubgraph RFi.F :=
    ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  have hroot_u : RF.root u = RFi.root u := by
    have h1 := upClosure_root_eq_of_inter_eq hT hord hR hBiV hRne hBi_ne hu
      (by rw [upClosure_levelRoots hT]; exact inter_ancestors_eq_levelRoots hT hR hRne hu)
    simpa only [upClosure_levelRoots hT] using h1
  unfold RootedForest.stretch
  dsimp only
  rw [htail, hhead]
  by_cases h_same : RFi.root u = RFi.root v
  · rw [ite_eq_left_iff.mpr (fun h => absurd h_same h)]
    have hz_mem := root_mem_forestPath_of_agree hT hord hR hRne hu hv h_same hcond
    have hconn_i : RFi.F.Connected u v :=
      connected_trans (rootedForest_root_spec hRSi hu).2
        (connected_symm (h_same ▸ (rootedForest_root_spec hRSi hv).2))
    rw [forestPath_subgraph hT.isForest hsub_i hconn_i]
    have hle := forestPath_walkLength_le_of_mem hT.isForest hℓ (hT.connected hu hv) hz_mem
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hle hℓe.le)
  · rw [ite_eq_right_iff.mpr (fun h => absurd h h_same)]
    have hconn_ur : RFi.F.Connected u (RFi.root u) := (rootedForest_root_spec hRSi hu).2
    rw [hroot_u, forestPath_subgraph hT.isForest hsub_i hconn_ur]
    have hnonneg : 0 ≤ walkLength ℓ (RFi.F.forestPath v (RFi.root v)) := by
      have hP := forestPath_isPath hRSi.1 (rootedForest_root_spec hRSi hv).2
      exact walkLength_nonneg_of_nonneg ℓ (fun f hf => hℓ f (hsub_i.2.1 (by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
        exact IsWalk_edges_mem hP.1 hx)))
    have hle : walkLength ℓ (T.forestPath u (RFi.root u)) ≤
        walkLength ℓ (T.forestPath u (RFi.root u)) +
          walkLength ℓ (RFi.F.forestPath v (RFi.root v)) := le_add_of_nonneg_right hnonneg
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hle hℓe.le)

/-- The level-set stretch bound `wstr_e = 2 * ∑_{i=0}^D str^{F_T(B_i, π), ℓ}_e`
(`[chen2022maximum, (B.3)]`). -/
noncomputable def levelStretchBound (T : MGraph) (r : ℕ) (π : ℕ → ℕ)
    (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  let D := (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2)
  2 * ∑ i ∈ Finset.range (D + 1),
    (rootedForestGivenRoots T r (levelRoots T r i) π).stretch G ℓ e

lemma levelStretchBound_ge_two {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (π : ℕ → ℕ) (G : MGraph) {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ T.E, 0 ≤ ℓ f)
    {e : ℕ} (hℓe : 0 < ℓ e) :
    2 ≤ levelStretchBound T r π G ℓ e := by
  unfold levelStretchBound
  dsimp only
  have h0_mem : 0 ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  have hterm : ∀ i, 1 ≤ (rootedForestGivenRoots T r (levelRoots T r i) π).stretch G ℓ e := by
    intro i
    have hFsub : T.IsSubgraph (forestGivenRoots T r (levelRoots T r i) π) :=
      ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hF_valid : (forestGivenRoots T r (levelRoots T r i) π).IsValid := by
      intro f hf; exact hT.isForest.1 f (hFsub.2.1 hf)
    have hF : (forestGivenRoots T r (levelRoots T r i) π).IsForest :=
      isForest_subgraph hT.isForest hFsub hF_valid
    exact rootedForest_stretch_ge_one hF (fun f hf => hℓ f (hFsub.2.1 hf)) hℓe
  have h0_le : 1 ≤ ∑ i ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1),
      (rootedForestGivenRoots T r (levelRoots T r i) π).stretch G ℓ e :=
    (hterm 0).trans (Finset.single_le_sum (fun i _ => (zero_le_one.trans (hterm i))) h0_mem)
  have hm := mul_le_mul_of_nonneg_left h0_le zero_le_two
  rwa [mul_one] at hm

lemma endpoint_stretch_le_half_levelStretchBound {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty)
    {u v : ℕ} (hu : u ∈ T.V) (hv : v ∈ T.V)
    {G : MGraph} {e : ℕ} (htail : G.tail e = u) (hhead : G.head e = v)
    {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ T.E, 0 ≤ ℓ f) (hℓe : 0 < ℓ e)
    (hcond : (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R) π).root u ≠
        (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R) π).root v ∨
      v ∈ upClosure (hldAuxTree T r) r R) :
    1 + walkLength ℓ (T.forestPath u
        ((rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R) π).root u)) / ℓ e ≤
      levelStretchBound T r π G ℓ e / 2 := by
  have hstep := endpoint_stretch_le_level hT hord hR hRne hu hv htail hhead hℓ hℓe hcond
  set i := deepestRootDepth T r (upClosure (hldAuxTree T r) r R) u
  have hi_le : i ≤ (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) :=
    (deepestRootDepth_le hT hu).trans (hldAuxTree_height hT hu)
  have hi_mem : i ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le)
  have hnonneg : ∀ j ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1),
      0 ≤ (rootedForestGivenRoots T r (levelRoots T r j) π).stretch G ℓ e := by
    intro j _
    have hFsub : T.IsSubgraph (forestGivenRoots T r (levelRoots T r j) π) :=
      ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hF : (forestGivenRoots T r (levelRoots T r j) π).IsForest :=
      isForest_subgraph hT.isForest hFsub (fun f hf => hT.isForest.1 f (hFsub.2.1 hf))
    exact zero_le_one.trans (rootedForest_stretch_ge_one hF (fun f hf => hℓ f (hFsub.2.1 hf)) hℓe)
  have hsum := Finset.single_le_sum hnonneg hi_mem
  unfold levelStretchBound
  dsimp only
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact hstep.trans hsum

lemma stretch_le_levelStretchBound {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty)
    {G : MGraph} {e : ℕ} (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V)
    {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ T.E, 0 ≤ ℓ f) (hℓe : 0 < ℓ e) :
    (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R) π).stretch G ℓ e ≤
      levelStretchBound T r π G ℓ e := by
  let R' := upClosure (hldAuxTree T r) r R
  let RF := rootedForestGivenRoots T r R' π
  have hTH := hldAuxTree_isRootedTree hT
  have hR'bf := upClosure_isBranchFree hT hR
  have hR'ne : R'.Nonempty := ⟨r, by
    obtain ⟨q, hq⟩ := hRne; exact mem_upClosure_iff.mpr ⟨q, hq, isAncestor_root hTH (hR hq)⟩⟩
  have hRS := forestGivenRoots_isRootedSpanningForest hT hR'bf hR'ne π
  have hsub : T.IsSubgraph RF.F := ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
  by_cases h_eq : RF.root (G.tail e) = RF.root (G.head e)
  · unfold RootedForest.stretch
    dsimp only
    rw [ite_eq_left_iff.mpr (fun h => absurd h_eq h)]
    have hconn : RF.F.Connected (G.tail e) (G.head e) :=
      connected_trans (rootedForest_root_spec hRS hu).2
        (connected_symm (h_eq ▸ (rootedForest_root_spec hRS hv).2))
    rw [forestPath_subgraph hT.isForest hsub hconn]
    obtain ⟨hF0, hr0⟩ := forestGivenRoots_levelZero hT π
    have h0_mem : 0 ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    have h0_str : (rootedForestGivenRoots T r (levelRoots T r 0) π).stretch G ℓ e =
        1 + walkLength ℓ (T.forestPath (G.tail e) (G.head e)) / ℓ e := by
      unfold RootedForest.stretch
      dsimp only
      rw [hr0 _ hu, hr0 _ hv, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      change 1 + walkLength ℓ ((forestGivenRoots T r (levelRoots T r 0) π).forestPath _ _) / ℓ e = _
      rw [hF0]
    have hnonneg : ∀ j ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1),
        0 ≤ (rootedForestGivenRoots T r (levelRoots T r j) π).stretch G ℓ e := by
      intro j _
      have hFsub : T.IsSubgraph (forestGivenRoots T r (levelRoots T r j) π) :=
        ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
      have hF : (forestGivenRoots T r (levelRoots T r j) π).IsForest :=
        isForest_subgraph hT.isForest hFsub (fun f hf => hT.isForest.1 f (hFsub.2.1 hf))
      exact zero_le_one.trans (rootedForest_stretch_ge_one hF (fun f hf => hℓ f (hFsub.2.1 hf)) hℓe)
    have hsum := Finset.single_le_sum hnonneg h0_mem
    have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range ((Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) + 1),
        (rootedForestGivenRoots T r (levelRoots T r j) π).stretch G ℓ e :=
      Finset.sum_nonneg hnonneg
    unfold levelStretchBound
    dsimp only
    rw [← h0_str]
    exact hsum.trans (le_mul_of_one_le_left hsum_nonneg one_le_two)
  · have h_u := endpoint_stretch_le_half_levelStretchBound hT hord hR hRne hu hv rfl rfl hℓ hℓe
      (Or.inl h_eq)
    let Gswap : MGraph := { G with tail := Function.update G.tail e (G.head e),
                                   head := Function.update G.head e (G.tail e) }
    have h_v := endpoint_stretch_le_half_levelStretchBound hT hord hR hRne hv hu
      (G := Gswap) (e := e) (Function.update_self _ _ G.tail) (Function.update_self _ _ G.head)
      hℓ hℓe (Or.inl (Ne.symm h_eq))
    have hlsb_swap : levelStretchBound T r π Gswap ℓ e = levelStretchBound T r π G ℓ e := by
      unfold levelStretchBound
      dsimp only
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hFsub : T.IsSubgraph (forestGivenRoots T r (levelRoots T r i) π) :=
        ⟨Finset.Subset.refl _, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
      have hF := isForest_subgraph hT.isForest hFsub (fun f hf => hT.isForest.1 f (hFsub.2.1 hf))
      exact stretch_swap_eq _ G ℓ e hF
    rw [hlsb_swap] at h_v
    unfold RootedForest.stretch
    dsimp only
    rw [ite_eq_right_iff.mpr (fun h => absurd h h_eq)]
    have hconn_ur := (rootedForest_root_spec hRS hu).2
    have hconn_vr := (rootedForest_root_spec hRS hv).2
    rw [forestPath_subgraph hT.isForest hsub hconn_ur, forestPath_subgraph hT.isForest hsub hconn_vr,
        add_div]
    have h12 : 1 + (walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) / ℓ e +
          walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e))) / ℓ e) ≤
        (1 + walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) / ℓ e) +
          (1 + walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e))) / ℓ e) := by
      calc 1 + (walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) / ℓ e +
            walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e))) / ℓ e)
          = (1 + walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) / ℓ e) +
              walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e))) / ℓ e := by
            rw [add_assoc]
        _ ≤ _ := add_le_add le_rfl (le_add_of_nonneg_left zero_le_one)
    calc 1 + (walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) / ℓ e +
          walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e))) / ℓ e)
        ≤ _ := h12
      _ ≤ levelStretchBound T r π G ℓ e / 2 + levelStretchBound T r π G ℓ e / 2 := add_le_add h_u h_v
      _ = levelStretchBound T r π G ℓ e := add_halves _

end MinCostFlow.LSF
