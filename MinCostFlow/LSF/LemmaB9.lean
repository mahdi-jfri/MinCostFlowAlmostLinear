module

public import MinCostFlow.LSF.AuxiliaryTreeProps
import Mathlib.Data.Finset.Max

/-!
# Lemma B.9: Conditions 2, 3, and 4 ([chen2022maximum] Appendix B.3)

This file proves Conditions 2, 3, and 4 of `[chen2022maximum, Lemma B.9]` and bundles them with
Condition 1 (`hldAuxTree_height`) in `lemma_B_9`:
* `upClosure_isBranchFree` (Condition 2): `R^{↑ T_H}` is branch-free in `(T, r)`.
* `upClosure_root_mem_ancestors` (Condition 3): `root^F_u ∈ u^{↑ T_H}`.
* `upClosure_root_eq_of_inter_eq` (Condition 4): `root^{F₁}_u = root^{F₂}_u` when
  `R₁^{↑ T_H} ∩ u^{↑ T_H} = R₂^{↑ T_H} ∩ u^{↑ T_H}`.
* `lemma_B_9`: full statement of `[chen2022maximum, Lemma B.9]`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow
/-! ## Conditions 2, 3, and 4 and Lemma B.9 -/

private lemma exists_child_of_proper_ancestor {T : MGraph} {r a u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hanc : IsAncestor T r a u) (hne : a ≠ u) :
    ∃ c ∈ T.V, c ≠ r ∧ IsAncestor T r c u ∧ parent T r c = a := by
  have h_ind : ∀ d w, depth T r w = d → w ∈ T.V → IsAncestor T r a w → a ≠ w →
      ∃ c ∈ T.V, c ≠ r ∧ IsAncestor T r c w ∧ parent T r c = a := by
    intro d
    induction d with
    | zero =>
      intro w hdw hw hwa hne'
      have hwr : w = r := by
        by_contra hwr'
        obtain ⟨_, hEq, _⟩ := forestPath_parent hT hw hwr'
        unfold depth at hdw; rw [hEq, List.length_cons] at hdw; omega
      rw [hwr] at hwa hne'
      exact absurd (isAncestor_antisymm hT (isAncestor_mem hT hT.2 hwa) hT.2 hwa
        (isAncestor_root hT (isAncestor_mem hT hT.2 hwa))) hne'
    | succ d' ih =>
      intro w hdw hw hwa hne'
      have hwr : w ≠ r := by
        intro hEq; unfold depth at hdw
        rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hdw; omega
      rcases (isAncestor_iff_eq_or_parent hT hw).mp hwa with hEq | ⟨_, hp⟩
      · exact absurd hEq hne'
      · by_cases hap : a = parent T r w
        · exact ⟨w, hw, hwr, isAncestor_refl T r w, hap.symm⟩
        · have hdp := depth_parent hT hw hwr
          obtain ⟨c, hcV, hcr, hcp, hpa⟩ := ih (parent T r w) (by omega) (parent_mem hT hw) hp hap
          exact ⟨c, hcV, hcr, isAncestor_trans hT hw hcp (isAncestor_parent hT hw hwr), hpa⟩
  exact h_ind (depth T r u) u rfl hu hanc hne

private lemma exists_boundary_below_lca {T : MGraph} {r l w : ℕ} (hT : IsRootedTree T r)
    (P : Finset ℕ) (hlP : l ∈ P) (hwP : w ∉ P) (hwV : w ∈ T.V) (hlw : IsAncestor T r l w) :
    ∃ a ∈ T.V, a ≠ r ∧ IsAncestor T r l a ∧ IsAncestor T r a w ∧ a ∉ P ∧ parent T r a ∈ P := by
  have h_ind : ∀ d x, depth T r x = d → x ∈ T.V → x ∉ P → IsAncestor T r l x →
      ∃ a ∈ T.V, a ≠ r ∧ IsAncestor T r l a ∧ IsAncestor T r a x ∧ a ∉ P ∧ parent T r a ∈ P := by
    intro d
    induction d with
    | zero =>
      intro x hdx hx hxP hlx
      have hxr : x = r := by
        by_contra hxr'
        obtain ⟨_, hEq, _⟩ := forestPath_parent hT hx hxr'
        unfold depth at hdx; rw [hEq, List.length_cons] at hdx; omega
      rw [hxr] at hlx hxP
      have hl_eq := isAncestor_antisymm hT (isAncestor_mem hT hT.2 hlx) hT.2 hlx
        (isAncestor_root hT (isAncestor_mem hT hT.2 hlx))
      exact absurd (hl_eq ▸ hlP) hxP
    | succ d' ih =>
      intro x hdx hx hxP hlx
      have hxr : x ≠ r := by
        intro hEq; unfold depth at hdx
        rw [hEq, forestPath_self hT.isForest r, List.length_nil] at hdx; omega
      by_cases hpP : parent T r x ∈ P
      · exact ⟨x, hx, hxr, hlx, isAncestor_refl T r x, hxP, hpP⟩
      · have hne_lx : l ≠ x := fun hEq => hxP (hEq ▸ hlP)
        have hl_p : IsAncestor T r l (parent T r x) := by
          rcases (isAncestor_iff_eq_or_parent hT hx).mp hlx with hEq | ⟨_, hp⟩
          · exact absurd hEq hne_lx
          · exact hp
        have hdp := depth_parent hT hx hxr
        obtain ⟨a, haV, har, hla, hax, haP, hpaP⟩ :=
          ih (parent T r x) (by omega) (parent_mem hT hx) hpP hl_p
        exact ⟨a, haV, har, hla, isAncestor_trans hT hx hax (isAncestor_parent hT hx hxr), haP, hpaP⟩
  exact h_ind (depth T r w) w rfl hwV hwP hlw

lemma upClosure_isBranchFree {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : R ⊆ T.V) :
    IsBranchFree T r (upClosure (hldAuxTree T r) r R) := by
  have hTH := hldAuxTree_isRootedTree hT
  have hR_TH : R ⊆ (hldAuxTree T r).V := hR
  refine ⟨upClosure_subset hTH hR_TH, fun u hu v hv => ?_⟩
  have huV := upClosure_subset hTH hR_TH hu
  have hvV := upClosure_subset hTH hR_TH hv
  let w := lca T r u v
  have hwV : w ∈ T.V := lca_mem hT huV hvV
  have hwu : IsAncestor T r w u := lca_isAncestor_left hT huV hvV
  have hwv : IsAncestor T r w v := lca_isAncestor_right hT huV hvV
  let Cw := chainOf T r w
  have hCw : Cw ∈ heavyChains T r := chainOf_mem_heavyChains hwV
  have hwCw : w ∈ Cw := mem_chainOf_self hwV
  have h_not_both : ¬ ((∃ c₁ ∈ Cw, IsAncestor T r c₁ u ∧ depth T r w < depth T r c₁) ∧
      (∃ c₂ ∈ Cw, IsAncestor T r c₂ v ∧ depth T r w < depth T r c₂)) := by
    rintro ⟨⟨c₁, hc₁C, hc₁u, hd₁⟩, ⟨c₂, hc₂C, hc₂v, hd₂⟩⟩
    have hc₁V := (heavyChain_subset hCw).2 hc₁C
    have hc₂V := (heavyChain_subset hCw).2 hc₂C
    have hwc₁ : IsAncestor T r w c₁ := by
      rcases isAncestor_total_on_ancestors hT huV hwu hc₁u with h1 | h2
      · exact h1
      · have := isAncestor_depth_le hT hwV h2; omega
    have hwc₂ : IsAncestor T r w c₂ := by
      rcases isAncestor_total_on_ancestors hT hvV hwv hc₂v with h1 | h2
      · exact h1
      · have := isAncestor_depth_le hT hwV h2; omega
    obtain ⟨x₁, hx₁V, hx₁r, hx₁c, hpx₁⟩ :=
      exists_child_of_proper_ancestor hT hc₁V hwc₁ (fun hEq => by rw [← hEq] at hd₁; omega)
    obtain ⟨x₂, hx₂V, hx₂r, hx₂c, hpx₂⟩ :=
      exists_child_of_proper_ancestor hT hc₂V hwc₂ (fun hEq => by rw [← hEq] at hd₂; omega)
    have hconv := (lemma_B_8 hT).2.1 Cw hCw
    have hx₁_Cw : x₁ ∈ Cw := hconv.2.2 c₁ hc₁C w hwCw x₁
      ((mem_walkVertices_ancestorPath_iff hT hc₁V hwc₁).mpr
        ⟨by rw [← hpx₁]; exact isAncestor_parent hT hx₁V hx₁r, hx₁c⟩)
    have hx₂_Cw : x₂ ∈ Cw := hconv.2.2 c₂ hc₂C w hwCw x₂
      ((mem_walkVertices_ancestorPath_iff hT hc₂V hwc₂).mpr
        ⟨by rw [← hpx₂]; exact isAncestor_parent hT hx₂V hx₂r, hx₂c⟩)
    have hx_eq : x₁ = x₂ :=
      (lemma_B_8 hT).2.2.1 Cw hCw w hwCw x₁ hx₁_Cw x₂ hx₂_Cw hx₁r hx₂r hpx₁ hpx₂
    subst hx_eq
    have hx₁_lca : IsAncestor T r x₁ w :=
      (isAncestor_lca_iff hT huV hvV).mpr
        ⟨isAncestor_trans hT huV hx₁c hc₁u, isAncestor_trans hT hvV hx₂c hc₂v⟩
    have hdx₁ := depth_parent hT hx₁V hx₁r
    rw [hpx₁] at hdx₁
    have hle := isAncestor_depth_le hT hwV hx₁_lca
    dsimp only [w] at hdx₁ hle
    omega
  by_cases h1 : ∀ y ∈ Cw, IsAncestor T r y u → depth T r y ≤ depth T r w
  · exact upClosure_isUpwardClosed hTH hR_TH hu
      (light_transition_isAncestor_TH hT _ u Cw w rfl huV hCw hwCw hwu h1)
  · push Not at h1
    have h2 : ∀ y ∈ Cw, IsAncestor T r y v → depth T r y ≤ depth T r w := by
      by_contra h2'
      push Not at h2'
      exact h_not_both ⟨h1, h2'⟩
    exact upClosure_isUpwardClosed hTH hR_TH hv
      (light_transition_isAncestor_TH hT _ v Cw w rfl hvV hCw hwCw hwv h2)

lemma forest_connected_along_path {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (π : ℕ → ℕ) {x y z : ℕ} (hx : x ∈ T.V) (hy : y ∈ T.V)
    (hconn : (forestGivenRoots T r R π).Connected x y)
    (hz : z ∈ T.walkVertices x (T.forestPath x y)) :
    (forestGivenRoots T r R π).Connected x z ∧ (forestGivenRoots T r R π).Connected z y := by
  unfold forestGivenRoots at hconn ⊢
  rw [connected_sdiff_iff_disjoint hT.isForest (hT.connected hx hy)] at hconn
  have hzV : z ∈ T.V := (IsWalk_vertices_mem hT.isForest.1 hx
    (forestPath_isPath hT.isForest (hT.connected hx hy)).1).2 z hz
  obtain ⟨hsplit, _⟩ := forestPath_mem_walkVertices_split hT.isForest (hT.connected hx hy) hz
  have h1 : walkEdges (T.forestPath x z) ⊆ walkEdges (T.forestPath x y) := by
    intro e he; rw [hsplit, walkEdges_append, Finset.mem_union]; exact Or.inl he
  have h2 : walkEdges (T.forestPath z y) ⊆ walkEdges (T.forestPath x y) := by
    intro e he; rw [hsplit, walkEdges_append, Finset.mem_union]; exact Or.inr he
  refine ⟨?_, ?_⟩
  · rw [connected_sdiff_iff_disjoint hT.isForest (hT.connected hx hzV)]
    exact Finset.disjoint_of_subset_left h1 hconn
  · rw [connected_sdiff_iff_disjoint hT.isForest (hT.connected hzV hy)]
    exact Finset.disjoint_of_subset_left h2 hconn

lemma upClosure_root_mem_ancestors {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {R : Finset ℕ} (hR : R ⊆ T.V) (hRne : R.Nonempty) (π : ℕ → ℕ)
    {u : ℕ} (hu : u ∈ T.V) :
    (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R) π).root u ∈
      ancestors (hldAuxTree T r) r u := by
  have hTH := hldAuxTree_isRootedTree hT
  let R' := upClosure (hldAuxTree T r) r R
  have hR_TH : R ⊆ (hldAuxTree T r).V := hR
  have hR'_sub : R' ⊆ T.V := upClosure_subset hTH hR_TH
  have hR'_bf : IsBranchFree T r R' := upClosure_isBranchFree hT hR
  have hr_R' : r ∈ R' := by
    obtain ⟨x, hxR⟩ := hRne
    exact mem_upClosure_iff.mpr ⟨x, hxR, isAncestor_root hTH (hR hxR)⟩
  have hR'_ne : R'.Nonempty := ⟨r, hr_R'⟩
  let RF := rootedForestGivenRoots T r R' π
  let F := forestGivenRoots T r R' π
  have h_ind : ∀ d w, depth (hldAuxTree T r) r w = d → w ∈ T.V →
      IsAncestor (hldAuxTree T r) r (RF.root w) w := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro w hdw hwV
      by_cases hwR : w ∈ R'
      · have hroot : RF.root w = w :=
          forestGivenRoots_root_eq_of_connected hT hR'_bf hR'_ne π hwV hwR (connected_refl F w)
        rw [hroot]
        exact isAncestor_refl (hldAuxTree T r) r w
      · let S := R' ∩ ancestors (hldAuxTree T r) r w
        have hSne : S.Nonempty := ⟨r, Finset.mem_inter.mpr
          ⟨hr_R', mem_ancestors_iff.mpr (isAncestor_root hTH hwV)⟩⟩
        obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S (depth (hldAuxTree T r) r) hSne
        rw [Finset.mem_inter, mem_ancestors_iff] at hvS
        rcases hvS with ⟨hvR, hvw_TH⟩
        have hvV := hR'_sub hvR
        let P := chainOf T r v
        have hP : P ∈ heavyChains T r := chainOf_mem_heavyChains hvV
        have hvP : v ∈ P := mem_chainOf_self hvV
        let S_P := P ∩ ancestors (hldAuxTree T r) r w
        have hSP_ne : S_P.Nonempty := ⟨v, Finset.mem_inter.mpr ⟨hvP, mem_ancestors_iff.mpr hvw_TH⟩⟩
        obtain ⟨b, hbSP, hbmax⟩ := Finset.exists_max_image S_P (depth (hldAuxTree T r) r) hSP_ne
        rw [Finset.mem_inter, mem_ancestors_iff] at hbSP
        rcases hbSP with ⟨hbP, hbw_TH⟩
        have hbV := (heavyChain_subset hP).2 hbP
        have hvb_TH : IsAncestor (hldAuxTree T r) r v b := by
          rcases isAncestor_total_on_ancestors hTH hwV hvw_TH hbw_TH with h1 | h2
          · exact h1
          · have hdv := hbmax v (Finset.mem_inter.mpr ⟨hvP, mem_ancestors_iff.mpr hvw_TH⟩)
            have hEq := (isAncestor_eq_iff_depth hTH hvV h2).mp
              (Nat.le_antisymm (isAncestor_depth_le hTH hvV h2) hdv)
            rw [hEq]; exact isAncestor_refl _ _ _
        by_cases hwP : w ∈ P
        · have hRS := forestGivenRoots_isRootedSpanningForest hT hR'_bf hR'_ne π
          obtain ⟨hw_rt_R, hconn_F⟩ := rootedForest_root_spec hRS hwV
          have hwstarV := hR'_sub hw_rt_R
          have htP : chainTop T r P ∈ P := (chainTop_spec hT hP).1
          have htV := (heavyChain_subset hP).2 htP
          have ht_R : chainTop T r P ∈ R' :=
            upClosure_isUpwardClosed hTH hR_TH hvR (chainTop_isAncestor_TH hT hP hvP)
          have hwstarP : RF.root w ∈ P := by
            by_contra hwstar_not_P
            by_cases ht_path : chainTop T r P ∈ T.walkVertices w (T.forestPath w (RF.root w))
            · have hconn_tw := (forest_connected_along_path hT π hwV hwstarV hconn_F ht_path).2
              exact hwstar_not_P (by
                by_contra hne_all
                have hne_tr : chainTop T r P ≠ RF.root w := fun hEq => hwstar_not_P (hEq ▸ htP)
                exact forestGivenRoots_not_connected_roots hT hR'_bf hR'_ne π ht_R hw_rt_R hne_tr hconn_tw)
            · let l := lca T r w (RF.root w)
              have hlV := lca_mem hT hwV hwstarV
              have hlw := lca_isAncestor_left hT hwV hwstarV
              have hlwstar := lca_isAncestor_right hT hwV hwstarV
              have hlt : IsAncestor T r (chainTop T r P) l := by
                rcases isAncestor_total_on_ancestors hT hwV ((chainTop_spec hT hP).2 w hwP) hlw with h1 | h2
                · exact h1
                · exfalso
                  exact ht_path ((mem_walkVertices_forestPath_iff hT hwV hwstarV).mpr
                    ⟨h2, Or.inl ((chainTop_spec hT hP).2 w hwP)⟩)
              have hlP : l ∈ P := by
                have hconv := (lemma_B_8 hT).2.1 P hP
                exact hconv.2.2 w hwP (chainTop T r P) htP l
                  ((mem_walkVertices_ancestorPath_iff hT hwV ((chainTop_spec hT hP).2 w hwP)).mpr ⟨hlt, hlw⟩)
              obtain ⟨a', ha'V, ha'r, hla', ha'wstar, ha'notP, hpa'P⟩ :=
                exists_boundary_below_lca hT P hlP hwstar_not_P hwstarV hlwstar
              let z := parent T r a'
              have ha'top : a' = chainTop T r (chainOf T r a') := by
                by_contra hne_top
                have hC' := chainOf_mem_heavyChains (r := r) ha'V
                have hzC' := parent_mem_chain_of_ne_chainTop hT hC' (mem_chainOf_self ha'V) hne_top
                exact ha'notP ((heavyChain_unique hP hC' hpa'P hzC') ▸ mem_chainOf_self ha'V)
              have h_a'_wstar_TH : IsAncestor (hldAuxTree T r) r a' (RF.root w) := by
                have := chainTop_isAncestor_TH_of_T hT ha'V hwstarV ha'wstar
                rwa [← ha'top] at this
              have h_z_a'_TH : IsAncestor (hldAuxTree T r) r z a' := by
                have hpar : parent (hldAuxTree T r) r a' = z := by
                  rw [(hldAuxTree_parent hT ha'V ha'r).1]
                  unfold thParent
                  rw [ite_eq_left_iff.mpr (fun h => absurd ha'top h), ← ha'top]
                rw [← hpar]; exact isAncestor_parent hTH ha'V ha'r
              have hz_R : z ∈ R' :=
                upClosure_isUpwardClosed hTH hR_TH hw_rt_R (isAncestor_trans hTH hwstarV h_z_a'_TH h_a'_wstar_TH)
              have hne_la' : l ≠ a' := fun hEq => ha'notP (hEq ▸ hlP)
              have hl_z : IsAncestor T r l z := by
                rcases (isAncestor_iff_eq_or_parent hT ha'V).mp hla' with hEq | ⟨_, hp⟩
                · exact absurd hEq hne_la'
                · exact hp
              have hz_wstar : IsAncestor T r z (RF.root w) :=
                isAncestor_trans hT hwstarV (isAncestor_parent hT ha'V ha'r) ha'wstar
              have hz_path : z ∈ T.walkVertices w (T.forestPath w (RF.root w)) :=
                (mem_walkVertices_forestPath_iff hT hwV hwstarV).mpr ⟨hl_z, Or.inr hz_wstar⟩
              have hconn_zw := (forest_connected_along_path hT π hwV hwstarV hconn_F hz_path).2
              by_cases hzw : z = RF.root w
              · exact hwstar_not_P (hzw ▸ hpa'P)
              · exact forestGivenRoots_not_connected_roots hT hR'_bf hR'_ne π hz_R hw_rt_R hzw hconn_zw
          obtain ⟨haP, hda_lo, hda_hi⟩ := lca_TH_in_chain_depth_between hT hP hwP hwstarP
          have ha_path := heavyChain_mem_forestPath_of_depth_between hT hP hwP hwstarP haP hda_lo hda_hi
          have hconn_aw : F.Connected (lca (hldAuxTree T r) r w (RF.root w)) (RF.root w) :=
            (forest_connected_along_path hT π hwV hwstarV hconn_F ha_path).2
          have ha_R : lca (hldAuxTree T r) r w (RF.root w) ∈ R' :=
            upClosure_isUpwardClosed hTH hR_TH hw_rt_R (lca_isAncestor_right hTH hwV hwstarV)
          have ha_eq : lca (hldAuxTree T r) r w (RF.root w) = RF.root w := by
            by_contra hne
            exact forestGivenRoots_not_connected_roots hT hR'_bf hR'_ne π ha_R hw_rt_R hne hconn_aw
          rw [← ha_eq]
          exact lca_isAncestor_left hTH hwV hwstarV
        · have hbw : b ≠ w := fun hEq => hwP (hEq ▸ hbP)
          obtain ⟨a, haV, har, haw_TH, hpa_TH⟩ :=
            exists_child_of_proper_ancestor hTH hwV hbw_TH hbw
          have ha_not_P : a ∉ P := by
            intro haP
            have ha_le := hbmax a (Finset.mem_inter.mpr ⟨haP, mem_ancestors_iff.mpr haw_TH⟩)
            have hda := depth_parent hTH haV har
            rw [hpa_TH] at hda
            omega
          have ha_top : a = chainTop T r (chainOf T r a) := by
            by_contra hne_top
            have haV_T : a ∈ T.V := haV
            have hCa := chainOf_mem_heavyChains (T := T) (r := r) haV_T
            have haCa := mem_chainOf_self (T := T) (r := r) haV_T
            have hpar_eq : parent (hldAuxTree T r) r a = thParent T r a := (hldAuxTree_parent hT haV_T har).1
            rw [hpar_eq] at hpa_TH
            have hb_in_Ca : b ∈ chainOf T r a := by
              have hnd := (chainList_nodup hT hCa).tail
              have haL := (chainList_tail_mem_iff hT hCa).mpr ⟨haCa, hne_top⟩
              have hm : (chainList T r (chainOf T r a)).tail.length / 2 <
                  (chainList T r (chainOf T r a)).tail.length :=
                Nat.div_lt_self (List.length_pos_of_mem haL) (by decide)
              unfold thParent at hpa_TH
              rw [ite_eq_right_iff.mpr (fun h => absurd h hne_top)] at hpa_TH
              by_cases hart : a = (chainList T r (chainOf T r a)).tail[(chainList T r (chainOf T r a)).tail.length / 2]'hm
              · have hp_top := (bstParentWith_spec _ (chainTop T r (chainOf T r a)) _ a haL rfl hnd).1 hart |>.1
                rw [hp_top] at hpa_TH
                rw [← hpa_TH]; exact (chainTop_spec hT hCa).1
              · have hp_mem := (bstParentWith_spec _ (chainTop T r (chainOf T r a)) _ a haL rfl hnd).2 hart |>.1
                rw [← hpa_TH]; exact ((chainList_tail_mem_iff hT hCa).mp hp_mem).1
            exact ha_not_P ((heavyChain_unique hP hCa hbP hb_in_Ca) ▸ haCa)
          have hpa_T : parent T r a = b := by
            rw [← hpa_TH, (hldAuxTree_parent hT haV har).1]
            unfold thParent
            rw [ite_eq_left_iff.mpr (fun h => absurd ha_top h), ← ha_top]
          have hsub_disj : ∀ z ∈ subtree T r a, z ∉ R' := by
            intro z hz hzR
            rw [mem_subtree_iff] at hz
            have hz_a_TH : IsAncestor (hldAuxTree T r) r a z := by
              have := chainTop_isAncestor_TH_of_T hT haV hz.1 hz.2
              rwa [← ha_top] at this
            have haR : a ∈ R' := upClosure_isUpwardClosed hTH hR_TH hzR hz_a_TH
            have ha_max := hvmax a (Finset.mem_inter.mpr ⟨haR, mem_ancestors_iff.mpr haw_TH⟩)
            have hda := depth_parent hTH haV har
            rw [hpa_TH] at hda
            have hvb_le := isAncestor_depth_le hTH hbV hvb_TH
            omega
          have ha_anc_w_T : IsAncestor T r a w :=
            isAncestor_TH_chainTop_implies_T hT haV ha_top _ w rfl hwV haw_TH
          have hbw_T : IsAncestor T r b w :=
            isAncestor_trans hT hwV (hpa_T ▸ isAncestor_parent hT haV har) ha_anc_w_T
          have hconn_wb : F.Connected w b := by
            unfold F forestGivenRoots
            rw [connected_sdiff_iff_disjoint hT.isForest (hT.connected hwV hbV), Finset.disjoint_left]
            intro e he_path he_del
            classical
            unfold deletedEdges at he_del
            rw [ite_eq_left_iff.mpr (fun h => absurd hR'_ne h), Finset.mem_image] at he_del
            obtain ⟨r₂, hr₂_erase, hr₂_eq⟩ := he_del
            have hr₂R := (Finset.mem_erase.mp hr₂_erase).2
            have heT : e ∈ T.E := by
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he_path)
              exact IsWalk_edges_mem (forestPath_isPath hT.isForest (hT.connected hwV hbV)).1 hx
            have hc_ex : ∃ c ∈ T.V, c ≠ r ∧ parentEdge T r c = e := by
              rcases edge_parent_orientation hT heT with ⟨_, hpe, hcr⟩ | ⟨_, hpe, hcr⟩
              · exact ⟨T.tail e, (hT.isForest.1 e heT).1, hcr, hpe⟩
              · exact ⟨T.head e, (hT.isForest.1 e heT).2, hcr, hpe⟩
            obtain ⟨c, hcV, hcr, rfl⟩ := hc_ex
            rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr hwV hbw_T] at he_path
            have hac_T : IsAncestor T r a c := by
              rcases isAncestor_total_on_ancestors hT hwV ha_anc_w_T he_path.1 with h1 | h2
              · exact h1
              · rcases (isAncestor_iff_eq_or_parent hT haV).mp h2 with hca_eq | ⟨_, hcp⟩
                · exact hca_eq ▸ isAncestor_refl T r a
                · rw [hpa_T] at hcp; exact absurd hcp he_path.2
            have hm_del := hr₂_eq ▸ deletedEdge_mem_walkEdges (π := π) hT hR'_bf hR'_ne hr₂_erase
            rw [parentEdge_mem_walkEdges_ancestor_iff hT hcV hcr (hR'_sub hr₂R)
              (rootParent_spec hT hR'_bf hR'_ne hr₂_erase).2.2.1] at hm_del
            have har₂ := isAncestor_trans hT (hR'_sub hr₂R) hac_T hm_del.1
            exact hsub_disj r₂ (mem_subtree_iff.mpr ⟨hR'_sub hr₂R, har₂⟩) hr₂R
          have hRS := forestGivenRoots_isRootedSpanningForest hT hR'_bf hR'_ne π
          have hrt_eq : RF.root w = RF.root b := by
            have hb_spec := rootedForest_root_spec hRS hbV
            exact rootedForest_root_eq_of_mem hRS hwV hb_spec.1 (connected_trans hconn_wb hb_spec.2)
          have hlt : depth (hldAuxTree T r) r b < d := by
            have hdb := depth_parent hTH haV har
            have hd_aw := isAncestor_depth_le hTH hwV haw_TH
            rw [hpa_TH] at hdb
            omega
          have hih := ih _ hlt b rfl hbV
          rw [hrt_eq]
          exact isAncestor_trans hTH hwV hih hbw_TH
  exact mem_ancestors_iff.mpr (h_ind (depth (hldAuxTree T r) r u) u rfl hu)

lemma upClosure_root_eq_of_inter_eq {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    {R₁ R₂ : Finset ℕ} (hR₁ : R₁ ⊆ T.V) (hR₂ : R₂ ⊆ T.V)
    (hR₁ne : R₁.Nonempty) (hR₂ne : R₂.Nonempty) {u : ℕ} (hu : u ∈ T.V)
    (hinter : upClosure (hldAuxTree T r) r R₁ ∩ ancestors (hldAuxTree T r) r u =
      upClosure (hldAuxTree T r) r R₂ ∩ ancestors (hldAuxTree T r) r u) :
    (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R₁) π).root u =
      (rootedForestGivenRoots T r (upClosure (hldAuxTree T r) r R₂) π).root u := by
  have hTH := hldAuxTree_isRootedTree hT
  let A₁ := upClosure (hldAuxTree T r) r R₁
  let A₂ := upClosure (hldAuxTree T r) r R₂
  let A₀ := A₁ ∩ A₂
  have hR₁_TH : R₁ ⊆ (hldAuxTree T r).V := hR₁
  have hR₂_TH : R₂ ⊆ (hldAuxTree T r).V := hR₂
  have hA₁_sub : A₁ ⊆ T.V := upClosure_subset hTH hR₁_TH
  have hA₂_sub : A₂ ⊆ T.V := upClosure_subset hTH hR₂_TH
  have hA₀_sub : A₀ ⊆ T.V := fun x hx => hA₁_sub (Finset.mem_inter.mp hx).1
  have hr₁ : r ∈ A₁ := by
    obtain ⟨x, hx⟩ := hR₁ne
    exact mem_upClosure_iff.mpr ⟨x, hx, isAncestor_root hTH (hR₁ hx)⟩
  have hr₂ : r ∈ A₂ := by
    obtain ⟨x, hx⟩ := hR₂ne
    exact mem_upClosure_iff.mpr ⟨x, hx, isAncestor_root hTH (hR₂ hx)⟩
  have hA₀_ne : A₀.Nonempty := ⟨r, Finset.mem_inter.mpr ⟨hr₁, hr₂⟩⟩
  have hA₀_eq : upClosure (hldAuxTree T r) r A₀ = A₀ := by
    apply Finset.Subset.antisymm
    · intro w hw
      rw [mem_upClosure_iff] at hw
      obtain ⟨x, hx, hwx⟩ := hw
      rw [Finset.mem_inter] at hx
      exact Finset.mem_inter.mpr
        ⟨upClosure_isUpwardClosed hTH hR₁_TH hx.1 hwx, upClosure_isUpwardClosed hTH hR₂_TH hx.2 hwx⟩
    · exact subset_upClosure
  have hB₀ : IsBranchFree T r A₀ := hA₀_eq ▸ upClosure_isBranchFree hT hA₀_sub
  have hB₁ : IsBranchFree T r A₁ := upClosure_isBranchFree hT hR₁
  have hB₂ : IsBranchFree T r A₂ := upClosure_isBranchFree hT hR₂
  have hA₁_ne : A₁.Nonempty := ⟨r, hr₁⟩
  have hA₂_ne : A₂.Nonempty := ⟨r, hr₂⟩
  have h_helper : ∀ (B : Finset ℕ) (hB : IsBranchFree T r B) (hsub : A₀ ⊆ B)
      (_ : (rootedForestGivenRoots T r B π).root u ∈ A₀),
      (rootedForestGivenRoots T r B π).root u = (rootedForestGivenRoots T r A₀ π).root u := by
    intro B hB hsub h_root_mem
    have hBne : B.Nonempty := Finset.Nonempty.mono hsub hA₀_ne
    have hRS_B := forestGivenRoots_isRootedSpanningForest hT hB hBne π
    have hconn_B := (rootedForest_root_spec hRS_B hu).2
    have hdel_sub := deletedEdges_mono hT hB₀ hB hA₀_ne hsub π hord
    have hFsub : (forestGivenRoots T r A₀ π).IsSubgraph (forestGivenRoots T r B π) :=
      ⟨Finset.Subset.refl _, Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hdel_sub,
        fun _ _ => ⟨rfl, rfl⟩⟩
    have hconn_0 := connected_of_subgraph hFsub hconn_B
    exact (forestGivenRoots_root_eq_of_connected hT hB₀ hA₀_ne π hu h_root_mem hconn_0).symm
  have hr₁_anc := upClosure_root_mem_ancestors hT hR₁ hR₁ne π hu
  have hRS₁ := forestGivenRoots_isRootedSpanningForest hT hB₁ hA₁_ne π
  have hr₁_mem : (rootedForestGivenRoots T r A₁ π).root u ∈ A₁ ∩ ancestors (hldAuxTree T r) r u :=
    Finset.mem_inter.mpr ⟨(rootedForest_root_spec hRS₁ hu).1, hr₁_anc⟩
  have hr₁_mem₂ : (rootedForestGivenRoots T r A₁ π).root u ∈ A₂ := by
    have := hr₁_mem
    rw [hinter, Finset.mem_inter] at this
    exact this.1
  have hr₁_A₀ : (rootedForestGivenRoots T r A₁ π).root u ∈ A₀ :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hr₁_mem).1, hr₁_mem₂⟩
  have hr₂_anc := upClosure_root_mem_ancestors hT hR₂ hR₂ne π hu
  have hRS₂ := forestGivenRoots_isRootedSpanningForest hT hB₂ hA₂_ne π
  have hr₂_mem : (rootedForestGivenRoots T r A₂ π).root u ∈ A₂ ∩ ancestors (hldAuxTree T r) r u :=
    Finset.mem_inter.mpr ⟨(rootedForest_root_spec hRS₂ hu).1, hr₂_anc⟩
  have hr₂_mem₁ : (rootedForestGivenRoots T r A₂ π).root u ∈ A₁ := by
    have := hr₂_mem
    rw [← hinter, Finset.mem_inter] at this
    exact this.1
  have hr₂_A₀ : (rootedForestGivenRoots T r A₂ π).root u ∈ A₀ :=
    Finset.mem_inter.mpr ⟨hr₂_mem₁, (Finset.mem_inter.mp hr₂_mem).1⟩
  have h1 := h_helper A₁ hB₁ Finset.inter_subset_left hr₁_A₀
  have h2 := h_helper A₂ hB₂ Finset.inter_subset_right hr₂_A₀
  exact h1.trans h2.symm

/-- **Lemma B.9** (`[chen2022maximum, Lemma B.9]`):
Given a tree `T` rooted at `r`, `T_H = hldAuxTree T r` is a rooted tree on `T.V` such that:
1. For all `u ∈ T.V`, `depth T_H r u ≤ (Nat.log 2 |V(T)| + 1) * (Nat.log 2 |V(T)| + 2)` (`O(log^2 n)`).
2. For any `R ⊆ T.V`, `upClosure T_H r R` is branch-free in `(T, r)`.
3. For any nonempty `R ⊆ T.V` and edge ordering `π`, `root^F_u ∈ ancestors T_H r u` for all `u ∈ T.V`,
   where `F = forestGivenRoots T r (upClosure T_H r R) π`.
4. For any edge ordering `π` and nonempty `R₁, R₂ ⊆ T.V`, if
   `upClosure T_H r R₁ ∩ ancestors T_H r u = upClosure T_H r R₂ ∩ ancestors T_H r u`, then
   `root^{F₁}_u = root^{F₂}_u`. -/
lemma lemma_B_9 {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    let TH := hldAuxTree T r
    IsRootedTree TH r ∧ TH.V = T.V ∧
    (∀ u ∈ T.V, depth TH r u ≤ (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2)) ∧
    (∀ R ⊆ T.V, IsBranchFree T r (upClosure TH r R)) ∧
    (∀ (π : ℕ → ℕ) (R : Finset ℕ), R ⊆ T.V → R.Nonempty → ∀ u ∈ T.V,
      (rootedForestGivenRoots T r (upClosure TH r R) π).root u ∈ ancestors TH r u) ∧
    (∀ (π : ℕ → ℕ), IsEdgeOrder T π → ∀ R₁ R₂ : Finset ℕ, R₁ ⊆ T.V → R₂ ⊆ T.V →
      R₁.Nonempty → R₂.Nonempty → ∀ u ∈ T.V,
      upClosure TH r R₁ ∩ ancestors TH r u = upClosure TH r R₂ ∩ ancestors TH r u →
      (rootedForestGivenRoots T r (upClosure TH r R₁) π).root u =
        (rootedForestGivenRoots T r (upClosure TH r R₂) π).root u) :=
  ⟨hldAuxTree_isRootedTree hT, rfl,
   fun _ hu => hldAuxTree_height hT hu,
   fun _ hR => upClosure_isBranchFree hT hR,
   fun π _ hR hRne _ hu => upClosure_root_mem_ancestors hT hR hRne π hu,
   fun _ hord _ _ hR₁ hR₂ hR₁ne hR₂ne _ hu hinter =>
     upClosure_root_eq_of_inter_eq hT hord hR₁ hR₂ hR₁ne hR₂ne hu hinter⟩

end MinCostFlow.LSF
