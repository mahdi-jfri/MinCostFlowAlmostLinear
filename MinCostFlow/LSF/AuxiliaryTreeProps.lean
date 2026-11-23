module

public import MinCostFlow.LSF.AuxiliaryTree
import Mathlib.Data.Finset.Max

/-!
# Properties of `T_H` and Lemma B.9 ([chen2022maximum] Appendix B.3)

This file proves the BST interval properties of `T_H = hldAuxTree T r`, Conditions 2, 3, and 4 of
`[chen2022maximum, Lemma B.9]`, and the bundled theorem `lemma_B_9`:
* `upClosure_isBranchFree` (Condition 2): `R^{↑ T_H}` is branch-free in `(T, r)`.
* `upClosure_root_mem_ancestors` (Condition 3): `root^F_u ∈ u^{↑ T_H}`.
* `upClosure_root_eq_of_inter_eq` (Condition 4): `root^{F₁}_u = root^{F₂}_u` when `R₁^{↑ T_H} ∩ u^{↑ T_H} = R₂^{↑ T_H} ∩ u^{↑ T_H}`.
* `lemma_B_9`: full statement of `[chen2022maximum, Lemma B.9]`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Heavy chain and BST interval helpers -/

lemma heavyChain_unique {T : MGraph} {r x : ℕ} {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ heavyChains T r) (hC₂ : C₂ ∈ heavyChains T r)
    (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ :=
  (chainOf_eq_of_mem hC₁ hx₁).symm.trans (chainOf_eq_of_mem hC₂ hx₂)

lemma parent_mem_chain_of_ne_chainTop {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    {C : Finset ℕ} (hC : C ∈ heavyChains T r) (hu : u ∈ C) (hut : u ≠ chainTop T r C) :
    parent T r u ∈ C := by
  have hsub := (heavyChain_subset hC).2
  have huV := hsub hu
  have htC := (chainTop_spec hT hC).1
  have htu := (chainTop_spec hT hC).2 u hu
  have hur : u ≠ r := by
    intro hEq
    rw [hEq] at htu
    have htr := isAncestor_antisymm hT hT.2 (hsub htC) (isAncestor_root hT (hsub htC)) htu
    exact hut (hEq.trans htr)
  rcases (isAncestor_iff_eq_or_parent hT huV).mp htu with hEq | ⟨_, htp⟩
  · exact absurd hEq.symm hut
  · have hconv := (lemma_B_8 hT).2.1 C hC
    exact hconv.2.2 u hu (chainTop T r C) htC (parent T r u)
      ((mem_walkVertices_ancestorPath_iff hT huV htu).mpr ⟨htp, isAncestor_parent hT huV hur⟩)

private lemma pairwise_take_drop_depth {T : MGraph} {r : ℕ} {L : List ℕ}
    (hpw : L.Pairwise (fun a b => depth T r a < depth T r b)) {m : ℕ} (hm : m < L.length) :
    (∀ x ∈ L.take m, depth T r x < depth T r L[m]) ∧
      (∀ y ∈ L.drop (m + 1), depth T r L[m] < depth T r y) := by
  have hsplit := List.take_append_drop m L
  have hdrop : L.drop m = L[m] :: L.drop (m + 1) := List.drop_eq_getElem_cons hm
  have hpw' : (L.take m ++ L[m] :: L.drop (m + 1)).Pairwise (fun a b => depth T r a < depth T r b) := by
    rwa [← hdrop, hsplit]
  rw [List.pairwise_append, List.pairwise_cons] at hpw'
  refine ⟨fun x hx => hpw'.2.2 x hx L[m] List.mem_cons_self, fun y hy => hpw'.2.1.1 y hy⟩

private lemma bst_ancestors_in_list {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ n (above : ℕ) (L : List ℕ), L.length = n → L.Nodup → (hL : L ≠ []) →
      (∀ w ∈ L, w ∈ T.V ∧ w ≠ r) →
      (∀ w ∈ L, parent (hldAuxTree T r) r w = bstParentWith above L w) →
      ∀ w ∈ L,
        IsAncestor (hldAuxTree T r) r
          (L[L.length / 2]'(Nat.div_lt_self (List.length_pos_iff.mpr hL) (by decide))) w ∧
        (∀ z, IsAncestor (hldAuxTree T r) r
            (L[L.length / 2]'(Nat.div_lt_self (List.length_pos_iff.mpr hL) (by decide))) z →
          IsAncestor (hldAuxTree T r) r z w → z ∈ L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro above L hn hnd hne hsub hstep w hw
    have hTH := hldAuxTree_isRootedTree hT
    have hpos : 0 < L.length := List.length_pos_of_mem hw
    have hm : L.length / 2 < L.length := Nat.div_lt_self hpos (by decide)
    have hanc_ind : ∀ k x, bstDepth L x = k → x ∈ L →
        IsAncestor (hldAuxTree T r) r (L[L.length / 2]'hm) x ∧
        (∀ z, IsAncestor (hldAuxTree T r) r (L[L.length / 2]'hm) z →
          IsAncestor (hldAuxTree T r) r z x → z ∈ L) := by
      intro k
      induction k with
      | zero =>
        intro x hdx hx
        have hxr : x = L[L.length / 2]'hm := by
          by_contra hxne
          obtain ⟨_, hne_spec⟩ := bstParentWith_spec L.length above L x hx rfl hnd
          obtain ⟨_, hbd⟩ := hne_spec hxne
          omega
        refine ⟨hxr ▸ isAncestor_refl (hldAuxTree T r) r _, fun z hz1 hz2 => ?_⟩
        rw [hxr] at hz2
        have hrtV : L[L.length / 2]'hm ∈ (hldAuxTree T r).V := (hsub _ (List.getElem_mem hm)).1
        have hzV : z ∈ (hldAuxTree T r).V := isAncestor_mem hTH hrtV hz2
        have hz_eq := isAncestor_antisymm hTH hzV hrtV hz2 hz1
        rw [hz_eq]
        exact List.getElem_mem hm
      | succ k' ihk =>
        intro x hdx hx
        have hxne : x ≠ L[L.length / 2]'hm := by
          intro hEq
          obtain ⟨heq_spec, _⟩ := bstParentWith_spec L.length above L x hx rfl hnd
          have := (heq_spec hEq).2
          omega
        obtain ⟨_, hne_spec⟩ := bstParentWith_spec L.length above L x hx rfl hnd
        obtain ⟨hpL, hdp_bst⟩ := hne_spec hxne
        have hp_eq : parent (hldAuxTree T r) r x = bstParentWith above L x := hstep x hx
        rw [← hp_eq] at hpL hdp_bst
        obtain ⟨ih_anc, ih_close⟩ := ihk (parent (hldAuxTree T r) r x) (by omega) hpL
        obtain ⟨hxV, hxr⟩ := hsub x hx
        refine ⟨isAncestor_trans hTH hxV ih_anc (isAncestor_parent hTH hxV hxr), fun z hz1 hz2 => ?_⟩
        rcases (isAncestor_iff_eq_or_parent hTH hxV).mp hz2 with hEq | ⟨_, hz_p⟩
        · exact hEq ▸ hx
        · exact ih_close z hz1 hz_p
    exact hanc_ind (bstDepth L w) w rfl hw

private lemma bst_lca_disjoint_sides {T : MGraph} {r above : ℕ} {L : List ℕ}
    (hT : IsRootedTree T r) (hnd : L.Nodup)
    (hsub : ∀ w ∈ L, w ∈ T.V ∧ w ≠ r)
    (hstep : ∀ w ∈ L, parent (hldAuxTree T r) r w = bstParentWith above L w)
    (hm : L.length / 2 < L.length)
    (hstep_t : ∀ w ∈ L.take (L.length / 2),
      parent (hldAuxTree T r) r w = bstParentWith (L[L.length / 2]'hm) (L.take (L.length / 2)) w)
    (hstep_d : ∀ w ∈ L.drop (L.length / 2 + 1),
      parent (hldAuxTree T r) r w = bstParentWith (L[L.length / 2]'hm) (L.drop (L.length / 2 + 1)) w)
    {x y : ℕ} (hx_t : x ∈ L.take (L.length / 2)) (hy_d : y ∈ L.drop (L.length / 2 + 1)) :
    lca (hldAuxTree T r) r x y = L[L.length / 2]'hm := by
  have hTH := hldAuxTree_isRootedTree hT
  have hx := List.take_subset _ _ hx_t
  have hy := List.drop_subset _ _ hy_d
  have hxV : x ∈ (hldAuxTree T r).V := (hsub x hx).1
  have hyV : y ∈ (hldAuxTree T r).V := (hsub y hy).1
  have hrt_mem := List.getElem_mem hm
  have hrtV : L[L.length / 2]'hm ∈ (hldAuxTree T r).V := (hsub _ hrt_mem).1
  have hLne : L ≠ [] := List.ne_nil_of_length_pos (lt_of_le_of_lt (Nat.zero_le _) hm)
  have hx_anc := bst_ancestors_in_list hT L.length above L rfl hnd hLne hsub hstep x hx
  have hy_anc := bst_ancestors_in_list hT L.length above L rfl hnd hLne hsub hstep y hy
  have hz_anc_x := lca_isAncestor_left hTH hxV hyV
  have hz_anc_y := lca_isAncestor_right hTH hxV hyV
  have hrt_anc_z : IsAncestor (hldAuxTree T r) r (L[L.length / 2]'hm)
      (lca (hldAuxTree T r) r x y) :=
    (isAncestor_lca_iff hTH hxV hyV).mpr ⟨hx_anc.1, hy_anc.1⟩
  obtain ⟨_, _, h_td⟩ := disjoint_take_drop_nodup hnd (L.length / 2)
  by_contra hne_z
  have hzV : lca (hldAuxTree T r) r x y ∈ (hldAuxTree T r).V := lca_mem hTH hxV hyV
  have hL_t_ne : L.take (L.length / 2) ≠ [] :=
    List.ne_nil_of_length_pos (List.length_pos_of_mem hx_t)
  have hL_d_ne : L.drop (L.length / 2 + 1) ≠ [] :=
    List.ne_nil_of_length_pos (List.length_pos_of_mem hy_d)
  have hx_sub := bst_ancestors_in_list hT _ (L[L.length / 2]'hm) (L.take (L.length / 2))
    rfl hnd.take hL_t_ne (fun w hw => hsub w (List.take_subset _ _ hw)) hstep_t x hx_t
  have hy_sub := bst_ancestors_in_list hT _ (L[L.length / 2]'hm) (L.drop (L.length / 2 + 1))
    rfl hnd.drop hL_d_ne (fun w hw => hsub w (List.drop_subset _ _ hw)) hstep_d y hy_d
  have hm_t : (L.take (L.length / 2)).length / 2 < (L.take (L.length / 2)).length :=
    Nat.div_lt_self (List.length_pos_of_mem hx_t) (by decide)
  have hm_d : (L.drop (L.length / 2 + 1)).length / 2 < (L.drop (L.length / 2 + 1)).length :=
    Nat.div_lt_self (List.length_pos_of_mem hy_d) (by decide)
  have hrt_t_par : parent (hldAuxTree T r) r ((L.take (L.length / 2))[(L.take (L.length / 2)).length / 2]'hm_t) =
      L[L.length / 2]'hm := by
    rw [hstep_t _ (List.getElem_mem hm_t)]
    exact (bstParentWith_spec _ _ _ _ (List.getElem_mem hm_t) rfl hnd.take).1 rfl |>.1
  have hrt_d_par : parent (hldAuxTree T r) r ((L.drop (L.length / 2 + 1))[(L.drop (L.length / 2 + 1)).length / 2]'hm_d) =
      L[L.length / 2]'hm := by
    rw [hstep_d _ (List.getElem_mem hm_d)]
    exact (bstParentWith_spec _ _ _ _ (List.getElem_mem hm_d) rfl hnd.drop).1 rfl |>.1
  have hz_t : lca (hldAuxTree T r) r x y ∈ L.take (L.length / 2) := by
    apply hx_sub.2
    · rcases isAncestor_total_on_ancestors hTH hxV hx_sub.1 hz_anc_x with h1 | h2
      · exact h1
      · have hrt_tV := (hsub _ (List.take_subset _ _ (List.getElem_mem hm_t))).1
        rcases (isAncestor_iff_eq_or_parent hTH hrt_tV).mp h2 with hEq | ⟨_, hp⟩
        · exact hEq ▸ isAncestor_refl _ _ _
        · rw [hrt_t_par] at hp
          exact absurd (isAncestor_antisymm hTH hzV hrtV hp hrt_anc_z) hne_z
    · exact hz_anc_x
  have hz_d : lca (hldAuxTree T r) r x y ∈ L.drop (L.length / 2 + 1) := by
    apply hy_sub.2
    · rcases isAncestor_total_on_ancestors hTH hyV hy_sub.1 hz_anc_y with h1 | h2
      · exact h1
      · have hrt_dV := (hsub _ (List.drop_subset _ _ (List.getElem_mem hm_d))).1
        rcases (isAncestor_iff_eq_or_parent hTH hrt_dV).mp h2 with hEq | ⟨_, hp⟩
        · exact hEq ▸ isAncestor_refl _ _ _
        · rw [hrt_d_par] at hp
          exact absurd (isAncestor_antisymm hTH hzV hrtV hp hrt_anc_z) hne_z
    · exact hz_anc_y
  exact h_td _ hz_t hz_d

private lemma bst_lca_in_list_depth_between {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ n (above : ℕ) (L : List ℕ), L.length = n → L.Nodup →
      L.Pairwise (fun a b => depth T r a < depth T r b) →
      (∀ w ∈ L, w ∈ T.V ∧ w ≠ r) →
      (∀ w ∈ L, parent (hldAuxTree T r) r w = bstParentWith above L w) →
      ∀ x ∈ L, ∀ y ∈ L,
        let z := lca (hldAuxTree T r) r x y
        z ∈ L ∧ min (depth T r x) (depth T r y) ≤ depth T r z ∧
          depth T r z ≤ max (depth T r x) (depth T r y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro above L hn hnd hpw hsub hstep x hx y hy
    have hTH := hldAuxTree_isRootedTree hT
    have hpos : 0 < L.length := List.length_pos_of_mem hx
    have hLne : L ≠ [] := List.ne_nil_of_length_pos hpos
    have hm : L.length / 2 < L.length := Nat.div_lt_self hpos (by decide)
    have hrt_mem : L[L.length / 2]'hm ∈ L := List.getElem_mem hm
    obtain ⟨h_t_ne, h_d_ne, h_td⟩ := disjoint_take_drop_nodup hnd (L.length / 2)
    obtain ⟨h_t_lt, h_d_gt⟩ := pairwise_take_drop_depth hpw hm
    have hx_anc := bst_ancestors_in_list hT L.length above L rfl hnd hLne hsub hstep x hx
    have hy_anc := bst_ancestors_in_list hT L.length above L rfl hnd hLne hsub hstep y hy
    have hxV : x ∈ (hldAuxTree T r).V := (hsub x hx).1
    have hyV : y ∈ (hldAuxTree T r).V := (hsub y hy).1
    have hrtV : L[L.length / 2]'hm ∈ (hldAuxTree T r).V := (hsub _ hrt_mem).1
    have hz_anc_x := lca_isAncestor_left hTH hxV hyV
    have hz_anc_y := lca_isAncestor_right hTH hxV hyV
    have hrt_anc_z : IsAncestor (hldAuxTree T r) r (L[L.length / 2]'hm)
        (lca (hldAuxTree T r) r x y) :=
      (isAncestor_lca_iff hTH hxV hyV).mpr ⟨hx_anc.1, hy_anc.1⟩
    have hzL : lca (hldAuxTree T r) r x y ∈ L := hx_anc.2 _ hrt_anc_z hz_anc_x
    have hstep_t : ∀ w ∈ L.take (L.length / 2),
        parent (hldAuxTree T r) r w = bstParentWith (L[L.length / 2]'hm) (L.take (L.length / 2)) w := by
      intro w hw
      rw [hstep w (List.take_subset _ _ hw)]
      have hw_ne : w ≠ L[L.length / 2]'hm := h_t_ne w hw hm
      conv_lhs => unfold bstParentWith; dsimp only
      rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
          ite_eq_right_iff.mpr (fun h => absurd h hw_ne),
          ite_eq_left_iff.mpr (fun h => absurd hw h)]
    have hstep_d : ∀ w ∈ L.drop (L.length / 2 + 1),
        parent (hldAuxTree T r) r w = bstParentWith (L[L.length / 2]'hm) (L.drop (L.length / 2 + 1)) w := by
      intro w hw
      rw [hstep w (List.drop_subset _ _ hw)]
      have hw_ne : w ≠ L[L.length / 2]'hm := h_d_ne w hw hm
      have hw_not_t : w ∉ L.take (L.length / 2) := fun hm' => h_td w hm' hw
      conv_lhs => unfold bstParentWith; dsimp only
      rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
          ite_eq_right_iff.mpr (fun h => absurd h hw_ne),
          ite_eq_right_iff.mpr (fun h => absurd h hw_not_t)]
    by_cases hx_rt : x = L[L.length / 2]'hm
    · have hz_eq : lca (hldAuxTree T r) r x y = L[L.length / 2]'hm := by
        apply isAncestor_antisymm hTH (lca_mem hTH hxV hyV) hrtV
        · rw [← hx_rt]; exact hz_anc_x
        · exact hrt_anc_z
      refine ⟨hzL, ?_, ?_⟩ <;> rw [hz_eq, hx_rt]
      · exact min_le_left _ _
      · exact le_max_left _ _
    · by_cases hy_rt : y = L[L.length / 2]'hm
      · have hz_eq : lca (hldAuxTree T r) r x y = L[L.length / 2]'hm := by
          apply isAncestor_antisymm hTH (lca_mem hTH hxV hyV) hrtV
          · rw [← hy_rt]; exact hz_anc_y
          · exact hrt_anc_z
        refine ⟨hzL, ?_, ?_⟩ <;> rw [hz_eq, hy_rt]
        · exact min_le_right _ _
        · exact le_max_right _ _
      · rcases mem_take_or_drop_of_mem_ne hm hx hx_rt with hx_t | hx_d <;>
          rcases mem_take_or_drop_of_mem_ne hm hy hy_rt with hy_t | hy_d
        · have hlt : (L.take (L.length / 2)).length < n := by rw [List.length_take]; omega
          obtain ⟨hz', h1, h2⟩ := ih _ hlt (L[L.length / 2]'hm) (L.take (L.length / 2)) rfl hnd.take hpw.take
            (fun w hw => hsub w (List.take_subset _ _ hw)) hstep_t x hx_t y hy_t
          exact ⟨List.take_subset _ _ hz', h1, h2⟩
        · have hz_eq := bst_lca_disjoint_sides hT hnd hsub hstep hm hstep_t hstep_d hx_t hy_d
          have h1 := le_of_lt (h_t_lt x hx_t)
          have h2 := le_of_lt (h_d_gt y hy_d)
          rw [hz_eq]
          exact ⟨hrt_mem, le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
        · have hz_eq : lca (hldAuxTree T r) r x y = L[L.length / 2]'hm := by
            rw [lca_comm hTH hxV hyV]
            exact bst_lca_disjoint_sides hT hnd hsub hstep hm hstep_t hstep_d hy_t hx_d
          have h1 := le_of_lt (h_t_lt y hy_t)
          have h2 := le_of_lt (h_d_gt x hx_d)
          rw [hz_eq]
          exact ⟨hrt_mem, le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩
        · have hlt : (L.drop (L.length / 2 + 1)).length < n := by rw [List.length_drop]; omega
          obtain ⟨hz', h1, h2⟩ := ih _ hlt (L[L.length / 2]'hm) (L.drop (L.length / 2 + 1)) rfl hnd.drop hpw.drop
            (fun w hw => hsub w (List.drop_subset _ _ hw)) hstep_d x hx_d y hy_d
          exact ⟨List.drop_subset _ _ hz', h1, h2⟩

private lemma chainList_tail_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {C : Finset ℕ} (hC : C ∈ heavyChains T r) :
    (chainList T r C).tail.Nodup ∧
      (chainList T r C).tail.Pairwise (fun a b => depth T r a < depth T r b) ∧
      (∀ w ∈ (chainList T r C).tail, w ∈ T.V ∧ w ≠ r) ∧
      (∀ w ∈ (chainList T r C).tail,
        parent (hldAuxTree T r) r w = bstParentWith (chainTop T r C) (chainList T r C).tail w) := by
  have hnd := (chainList_nodup hT hC).tail
  obtain ⟨hstrict, tail, hEq⟩ := chainList_strictSorted_depth hT hC
  have hpw : (chainList T r C).tail.Pairwise (fun a b => depth T r a < depth T r b) := by
    have hpw_all : (chainList T r C).Pairwise (fun a b => depth T r a < depth T r b) :=
      List.pairwise_iff_getElem.mpr (fun i j hi hj hij => hstrict i j hij hi hj)
    rw [hEq] at hpw_all ⊢
    exact hpw_all.tail
  have hsub : ∀ w ∈ (chainList T r C).tail, w ∈ T.V ∧ w ≠ r := by
    intro w hw
    have hwC := ((chainList_tail_mem_iff hT hC).mp hw).1
    have hwt := ((chainList_tail_mem_iff hT hC).mp hw).2
    have hwV := (heavyChain_subset hC).2 hwC
    refine ⟨hwV, fun hEqr => ?_⟩
    rw [hEqr] at hwC
    have := (chainTop_spec hT hC).2 r hwC
    have htr := isAncestor_antisymm hT hT.2 ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)
      (isAncestor_root hT ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)) this
    exact hwt (hEqr.trans htr)
  have hstep : ∀ w ∈ (chainList T r C).tail,
      parent (hldAuxTree T r) r w = bstParentWith (chainTop T r C) (chainList T r C).tail w := by
    intro w hw
    obtain ⟨hwV, hwr⟩ := hsub w hw
    have hwC := ((chainList_tail_mem_iff hT hC).mp hw).1
    have hwt := ((chainList_tail_mem_iff hT hC).mp hw).2
    have hCeq : chainOf T r w = C := chainOf_eq_of_mem hC hwC
    rw [(hldAuxTree_parent hT hwV hwr).1]
    unfold thParent
    rw [hCeq]
    exact ite_eq_right_iff.mpr (fun h => absurd h hwt)
  exact ⟨hnd, hpw, hsub, hstep⟩

lemma chainTop_isAncestor_TH {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {C : Finset ℕ} (hC : C ∈ heavyChains T r) {u : ℕ} (hu : u ∈ C) :
    IsAncestor (hldAuxTree T r) r (chainTop T r C) u := by
  by_cases hut : u = chainTop T r C
  · rw [hut]; exact isAncestor_refl (hldAuxTree T r) r _
  · obtain ⟨hnd, _, hsub, hstep⟩ := chainList_tail_spec hT hC
    have huL : u ∈ (chainList T r C).tail := (chainList_tail_mem_iff hT hC).mpr ⟨hu, hut⟩
    have hLne : (chainList T r C).tail ≠ [] := List.ne_nil_of_length_pos (List.length_pos_of_mem huL)
    have hm : (chainList T r C).tail.length / 2 < (chainList T r C).tail.length :=
      Nat.div_lt_self (List.length_pos_of_mem huL) (by decide)
    have hrt_anc_u := (bst_ancestors_in_list hT _ (chainTop T r C) _ rfl hnd hLne hsub hstep u huL).1
    have hrt_par : parent (hldAuxTree T r) r ((chainList T r C).tail[(chainList T r C).tail.length / 2]'hm) =
        chainTop T r C := by
      rw [hstep _ (List.getElem_mem hm)]
      exact (bstParentWith_spec _ (chainTop T r C) _ _ (List.getElem_mem hm) rfl hnd).1 rfl |>.1
    have hTH := hldAuxTree_isRootedTree hT
    obtain ⟨hrtV, hrtr⟩ := hsub _ (List.getElem_mem hm)
    have h_t_rt : IsAncestor (hldAuxTree T r) r (chainTop T r C)
        ((chainList T r C).tail[(chainList T r C).tail.length / 2]'hm) := by
      rw [← hrt_par]; exact isAncestor_parent hTH hrtV hrtr
    exact isAncestor_trans hTH (hsub u huL).1 h_t_rt hrt_anc_u

lemma lca_TH_in_chain_depth_between {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {C : Finset ℕ} (hC : C ∈ heavyChains T r) {x y : ℕ} (hx : x ∈ C) (hy : y ∈ C) :
    let z := lca (hldAuxTree T r) r x y
    z ∈ C ∧ min (depth T r x) (depth T r y) ≤ depth T r z ∧
      depth T r z ≤ max (depth T r x) (depth T r y) := by
  have hTH := hldAuxTree_isRootedTree hT
  have hxV := (heavyChain_subset hC).2 hx
  have hyV := (heavyChain_subset hC).2 hy
  have htx := chainTop_isAncestor_TH hT hC hx
  have hty := chainTop_isAncestor_TH hT hC hy
  by_cases hxt : x = chainTop T r C
  · have hz : lca (hldAuxTree T r) r x y = chainTop T r C := by
      apply isAncestor_antisymm hTH (lca_mem hTH hxV hyV) ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)
      · rw [← hxt]; exact lca_isAncestor_left hTH hxV hyV
      · exact (isAncestor_lca_iff hTH hxV hyV).mpr ⟨hxt ▸ isAncestor_refl _ _ _, hty⟩
    have hdt := isAncestor_depth_le hT hyV ((chainTop_spec hT hC).2 y hy)
    rw [hz]
    refine ⟨(chainTop_spec hT hC).1, ?_, ?_⟩
    · rw [← hxt]; exact min_le_left _ _
    · exact le_trans hdt (le_max_right _ _)
  · by_cases hyt : y = chainTop T r C
    · have hz : lca (hldAuxTree T r) r x y = chainTop T r C := by
        apply isAncestor_antisymm hTH (lca_mem hTH hxV hyV) ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)
        · rw [← hyt]; exact lca_isAncestor_right hTH hxV hyV
        · exact (isAncestor_lca_iff hTH hxV hyV).mpr ⟨htx, hyt ▸ isAncestor_refl _ _ _⟩
      have hdt := isAncestor_depth_le hT hxV ((chainTop_spec hT hC).2 x hx)
      rw [hz]
      refine ⟨(chainTop_spec hT hC).1, ?_, ?_⟩
      · rw [← hyt]; exact min_le_right _ _
      · exact le_trans hdt (le_max_left _ _)
    · obtain ⟨hnd, hpw, hsub, hstep⟩ := chainList_tail_spec hT hC
      have hxL : x ∈ (chainList T r C).tail := (chainList_tail_mem_iff hT hC).mpr ⟨hx, hxt⟩
      have hyL : y ∈ (chainList T r C).tail := (chainList_tail_mem_iff hT hC).mpr ⟨hy, hyt⟩
      obtain ⟨hzL, h1, h2⟩ := bst_lca_in_list_depth_between hT _ (chainTop T r C) _ rfl hnd hpw hsub hstep x hxL y hyL
      exact ⟨((chainList_tail_mem_iff hT hC).mp hzL).1, h1, h2⟩

lemma light_transition_isAncestor_TH {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ k u C x, depth T r u = k → u ∈ T.V → C ∈ heavyChains T r → x ∈ C → IsAncestor T r x u →
      (∀ y ∈ C, IsAncestor T r y u → depth T r y ≤ depth T r x) →
      IsAncestor (hldAuxTree T r) r x u := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro u C x hk huV hC hxC hxu hxmax
    have hTH := hldAuxTree_isRootedTree hT
    by_cases huC : u ∈ C
    · have hux : depth T r u ≤ depth T r x := hxmax u huC (isAncestor_refl T r u)
      have hxu_eq : x = u :=
        (isAncestor_eq_iff_depth hT huV hxu).mp (Nat.le_antisymm (isAncestor_depth_le hT huV hxu) hux)
      rw [hxu_eq]
      exact isAncestor_refl (hldAuxTree T r) r u
    · let Cu := chainOf T r u
      have hCu : Cu ∈ heavyChains T r := chainOf_mem_heavyChains huV
      have huCu : u ∈ Cu := mem_chainOf_self huV
      let t := chainTop T r Cu
      have htCu : t ∈ Cu := (chainTop_spec hT hCu).1
      have htV : t ∈ T.V := (heavyChain_subset hCu).2 htCu
      have htu : IsAncestor T r t u := (chainTop_spec hT hCu).2 u huCu
      have hconv := (lemma_B_8 hT).2.1 Cu hCu
      have htr : t ≠ r := by
        intro hEq
        have htx : IsAncestor T r t x := by rw [hEq]; exact isAncestor_root hT ((heavyChain_subset hC).2 hxC)
        have hxCu : x ∈ Cu := by
          have hbot := chainBot_spec hT hCu
          have hb_x := isAncestor_trans hT ((heavyChain_subset hCu).2 hbot.1) hxu (hbot.2 u huCu)
          exact hconv.2.2 (chainBot T r Cu) hbot.1 t htCu x
            ((mem_walkVertices_ancestorPath_iff hT ((heavyChain_subset hCu).2 hbot.1)
              ((chainTop_spec hT hCu).2 _ hbot.1)).mpr ⟨htx, hb_x⟩)
        exact huC ((heavyChain_unique hC hCu hxC hxCu) ▸ huCu)
      have hx_ne_t : x ≠ t := fun hEq => huC ((heavyChain_unique hC hCu hxC (hEq ▸ htCu)) ▸ huCu)
      have hx_anc_p : IsAncestor T r x (parent T r t) := by
        rcases isAncestor_total_on_ancestors hT huV htu hxu with h1 | h2
        · exfalso
          have hxCu : x ∈ Cu := hconv.2.2 u huCu t htCu x
            ((mem_walkVertices_ancestorPath_iff hT huV htu).mpr ⟨h1, hxu⟩)
          exact huC ((heavyChain_unique hC hCu hxC hxCu) ▸ huCu)
        · rcases (isAncestor_iff_eq_or_parent hT htV).mp h2 with hEq | ⟨_, hp⟩
          · exact absurd hEq hx_ne_t
          · exact hp
      have hp_mem := parent_mem hT htV
      have hdp := depth_parent hT htV htr
      have hdt := isAncestor_depth_le hT huV htu
      have hlt : depth T r (parent T r t) < k := by dsimp only [t] at hdp hdt ⊢; omega
      have hpt_u : IsAncestor T r (parent T r t) u :=
        isAncestor_trans hT huV (isAncestor_parent hT htV htr) htu
      have hih := ih _ hlt (parent T r t) C x rfl hp_mem hC hxC hx_anc_p
        (fun y hy hy_anc => hxmax y hy (isAncestor_trans hT huV hy_anc hpt_u))
      have ht_top : t = chainTop T r (chainOf T r t) :=
        congrArg (chainTop T r) (chainOf_eq_of_mem hCu htCu).symm
      have h_p_t_TH : IsAncestor (hldAuxTree T r) r (parent T r t) t := by
        have hpar : parent (hldAuxTree T r) r t = parent T r t := by
          rw [(hldAuxTree_parent hT htV htr).1]
          unfold thParent
          rw [ite_eq_left_iff.mpr (fun h => absurd ht_top h), ← ht_top]
        rw [← hpar]
        exact isAncestor_parent hTH htV htr
      have h_t_u_TH : IsAncestor (hldAuxTree T r) r t u := chainTop_isAncestor_TH hT hCu huCu
      exact isAncestor_trans hTH huV (isAncestor_trans hTH htV hih h_p_t_TH) h_t_u_TH

lemma chainTop_isAncestor_TH_of_T {T : MGraph} {r a u : ℕ} (hT : IsRootedTree T r)
    (haV : a ∈ T.V) (huV : u ∈ T.V) (hanc : IsAncestor T r a u) :
    IsAncestor (hldAuxTree T r) r (chainTop T r (chainOf T r a)) u := by
  classical
  let C := chainOf T r a
  have hC : C ∈ heavyChains T r := chainOf_mem_heavyChains haV
  let S := C.filter (fun y => IsAncestor T r y u)
  have hSne : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨mem_chainOf_self haV, hanc⟩⟩
  obtain ⟨x, hxS, hxmax⟩ := Finset.exists_max_image S (depth T r) hSne
  rw [Finset.mem_filter] at hxS
  have hx_TH := light_transition_isAncestor_TH hT _ u C x rfl huV hC hxS.1 hxS.2
    (fun y hyC hyu => hxmax y (Finset.mem_filter.mpr ⟨hyC, hyu⟩))
  have htop_x := chainTop_isAncestor_TH hT hC hxS.1
  exact isAncestor_trans (hldAuxTree_isRootedTree hT) huV htop_x hx_TH

lemma isAncestor_TH_chainTop_implies_T {T : MGraph} {r a : ℕ} (hT : IsRootedTree T r)
    (haV : a ∈ T.V) (hatop : a = chainTop T r (chainOf T r a)) :
    ∀ k u, depth (hldAuxTree T r) r u = k → u ∈ T.V →
      IsAncestor (hldAuxTree T r) r a u → IsAncestor T r a u := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro u hk huV hanc
    have hTH := hldAuxTree_isRootedTree hT
    by_cases hua : u = a
    · rw [hua]; exact isAncestor_refl T r a
    · have hur : u ≠ r := by
        intro hEq
        rw [hEq] at hanc
        exact hua (hEq.trans (isAncestor_antisymm hTH hT.2 haV (isAncestor_root hTH haV) hanc))
      have h_anc_p : IsAncestor (hldAuxTree T r) r a (parent (hldAuxTree T r) r u) := by
        rcases (isAncestor_iff_eq_or_parent hTH huV).mp hanc with hEq | ⟨_, hp⟩
        · exact absurd hEq.symm hua
        · exact hp
      have hp_mem := parent_mem hTH huV
      have hdp := depth_parent hTH huV hur
      have hih := ih _ (by omega) _ rfl hp_mem h_anc_p
      let Cu := chainOf T r u
      have hCu : Cu ∈ heavyChains T r := chainOf_mem_heavyChains huV
      have huCu : u ∈ Cu := mem_chainOf_self huV
      by_cases hut : u = chainTop T r Cu
      · have hpar_eq : parent (hldAuxTree T r) r u = parent T r u := by
          rw [(hldAuxTree_parent hT huV hur).1]
          unfold thParent
          rw [ite_eq_left_iff.mpr (fun h => absurd hut h), ← hut]
        rw [hpar_eq] at hih
        exact isAncestor_trans hT huV hih (isAncestor_parent hT huV hur)
      · have hpar_eq : parent (hldAuxTree T r) r u =
            bstParentWith (chainTop T r Cu) (chainList T r Cu).tail u := by
          rw [(hldAuxTree_parent hT huV hur).1]
          unfold thParent
          exact ite_eq_right_iff.mpr (fun h => absurd h hut)
        have hpar_in_Cu : parent (hldAuxTree T r) r u ∈ Cu := by
          have huL := (chainList_tail_mem_iff hT hCu).mpr ⟨huCu, hut⟩
          have hnd := (chainList_nodup hT hCu).tail
          have hpos := List.length_pos_of_mem huL
          have hm : (chainList T r Cu).tail.length / 2 < (chainList T r Cu).tail.length :=
            Nat.div_lt_self hpos (by decide)
          obtain ⟨heq_spec, hne_spec⟩ := bstParentWith_spec _ (chainTop T r Cu) _ u huL rfl hnd
          rw [hpar_eq]
          by_cases hurt : u = (chainList T r Cu).tail[(chainList T r Cu).tail.length / 2]'hm
          · rw [(heq_spec hurt).1]; exact (chainTop_spec hT hCu).1
          · exact ((chainList_tail_mem_iff hT hCu).mp (hne_spec hurt).1).1
        by_cases hC_eq : chainOf T r a = Cu
        · rw [hatop, hC_eq]
          exact (chainTop_spec hT hCu).2 u huCu
        · have ht_anc_p := (chainTop_spec hT hCu).2 _ hpar_in_Cu
          have ha_anc_t : IsAncestor T r a (chainTop T r Cu) := by
            rcases isAncestor_total_on_ancestors hT hp_mem hih ht_anc_p with h1 | h2
            · exact h1
            · exfalso
              have ha_in_Cu : a ∈ Cu := by
                have hconv := (lemma_B_8 hT).2.1 Cu hCu
                exact hconv.2.2 (parent (hldAuxTree T r) r u) hpar_in_Cu (chainTop T r Cu)
                  (chainTop_spec hT hCu).1 a
                  ((mem_walkVertices_ancestorPath_iff hT hp_mem ht_anc_p).mpr ⟨h2, hih⟩)
              exact hC_eq (chainOf_eq_of_mem hCu ha_in_Cu)
          exact isAncestor_trans hT huV ha_anc_t ((chainTop_spec hT hCu).2 u huCu)

lemma heavyChain_mem_forestPath_of_depth_between {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {C : Finset ℕ} (hC : C ∈ heavyChains T r) {x y z : ℕ} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hlo : min (depth T r x) (depth T r y) ≤ depth T r z)
    (hhi : depth T r z ≤ max (depth T r x) (depth T r y)) :
    z ∈ T.walkVertices x (T.forestPath x y) := by
  have hsub := (heavyChain_subset hC).2
  have hxV := hsub hx
  have hyV := hsub hy
  have hzV := hsub hz
  have hconn : ∀ a ∈ C, ∀ b ∈ C, (heavyGraph T r).Connected a b := by
    rw [heavyChains, components, Finset.mem_image] at hC
    obtain ⟨q, _, rfl⟩ := hC
    intro a ha b hb
    exact connected_trans (connected_symm (mem_compOf_iff.mp ha).2) (mem_compOf_iff.mp hb).2
  have h_between : ∀ {a b : ℕ}, a ∈ T.V → b ∈ T.V → a ∈ C → b ∈ C →
      IsAncestor T r a b → depth T r a ≤ depth T r z → depth T r z ≤ depth T r b →
      IsAncestor T r a z ∧ IsAncestor T r z b := by
    intro a b haV hbV haC hbC hab hla hhb
    have haz : IsAncestor T r a z := by
      rcases heavyGraph_connected_comparable hT haV hzV (hconn a haC z hz) with h1 | h2
      · exact h1
      · have hd := isAncestor_depth_le hT haV h2
        rw [← (isAncestor_eq_iff_depth hT haV h2).mp (Nat.le_antisymm hd hla)]
        exact isAncestor_refl T r z
    have hzb : IsAncestor T r z b := by
      rcases heavyGraph_connected_comparable hT hzV hbV (hconn z hz b hbC) with h1 | h2
      · exact h1
      · have hd := isAncestor_depth_le hT hzV h2
        rw [(isAncestor_eq_iff_depth hT hzV h2).mp (Nat.le_antisymm hd hhb)]
        exact isAncestor_refl T r z
    exact ⟨haz, hzb⟩
  rcases heavyGraph_connected_comparable hT hxV hyV (hconn x hx y hy) with hxy | hyx
  · have hdx := isAncestor_depth_le hT hyV hxy
    have hl : lca T r x y = x := isAncestor_antisymm hT (lca_mem hT hxV hyV) hxV
      (lca_isAncestor_left hT hxV hyV) ((isAncestor_lca_iff hT hxV hyV).mpr ⟨isAncestor_refl T r x, hxy⟩)
    have ⟨haz, hzb⟩ := h_between hxV hyV hx hy hxy (by rw [min_eq_left hdx] at hlo; exact hlo)
      (by rw [max_eq_right hdx] at hhi; exact hhi)
    exact (mem_walkVertices_forestPath_iff hT hxV hyV).mpr ⟨by rw [hl]; exact haz, Or.inr hzb⟩
  · have hdy := isAncestor_depth_le hT hxV hyx
    have hl : lca T r x y = y := isAncestor_antisymm hT (lca_mem hT hxV hyV) hyV
      (lca_isAncestor_right hT hxV hyV) ((isAncestor_lca_iff hT hxV hyV).mpr ⟨hyx, isAncestor_refl T r y⟩)
    have ⟨haz, hzb⟩ := h_between hyV hxV hy hx hyx (by rw [min_eq_right hdy] at hlo; exact hlo)
      (by rw [max_eq_left hdy] at hhi; exact hhi)
    exact (mem_walkVertices_forestPath_iff hT hxV hyV).mpr ⟨by rw [hl]; exact haz, Or.inl hzb⟩


end MinCostFlow.LSF
