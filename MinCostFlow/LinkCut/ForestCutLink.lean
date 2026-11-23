module

public import MinCostFlow.LinkCut.ForestReversals
import Mathlib.Tactic

/-!
# Invariant and Potential Lemma for `cut` Splices

This file proves `cut_splice_spec`: splitting `.node ne (.node a .leaf .leaf) (.node b .leaf .leaf)`
into singletons (`a`, `b`) and pushing the freed edge slot `ne` onto the free list preserves
`LctInvWith`, non-increases `sumTreePhi` (`≤`), and increases `heavyCount` by at most `1`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Singleton tree and parent-change reachability helpers -/

theorem treeIds_singleton {P : LctPayload α σ τ} {s : SplayState α σ τ} {z : ℕ} :
    treeIds P s (.node z .leaf .leaf) = [z] := by
  simp only [treeIds, SplayState.evalPairs]
  split_ifs <;> simp

private theorem singleton_rank_le_treePhi (v : ℕ → ℕ) (ne a b : ℕ) :
    (AuxTree.node a .leaf .leaf).rank v + (AuxTree.node b .leaf .leaf).rank v ≤
      (AuxTree.node ne (.node a .leaf .leaf) (.node b .leaf .leaf)).treePhi v := by
  simp [AuxTree.treePhi]

private theorem reaches_cut_b_eq {par₁ par₂ : ℕ → ℕ} {a ne b : ℕ}
    (hag : ∀ w, w ≠ a → w ≠ ne → w ≠ b → par₁ w = par₂ w)
    (hp₁_a : par₁ a = 0) (hp₁_ne : par₁ ne = 0) (hp₁_b : par₁ b = 0)
    (hp₂_a : par₂ a = 0) (hp₂_ne : par₂ ne = a) (hp₂_b : par₂ b = ne)
    {u : ℕ} (hua : u ≠ a) (hune : u ≠ ne) :
    ∀ k w, reaches par₁ k u w = reaches par₂ k u w := by
  have hS₁ : ∀ k w, w = a ∨ w = ne → reaches par₁ k u w = false := by
    intro k w hw
    rcases hw with hwa | hwne
    · cases k <;> simp [reaches, hwa, hua.symm, hp₁_a]
    · cases k <;> simp [reaches, hwne, hune.symm, hp₁_ne]
  have hS₂ : ∀ k w, w = a ∨ w = ne → reaches par₂ k u w = false := by
    intro k
    induction k with
    | zero =>
        intro w hw
        rcases hw with hwa | hwne
        · simp [reaches, hwa, hua.symm]
        · simp [reaches, hwne, hune.symm]
    | succ k ih =>
        intro w hw
        rcases hw with hwa | hwne
        · simp [reaches, hwa, hua.symm, hp₂_a]
        · simp only [reaches, beq_iff_eq, hwne, hune.symm, ↓reduceIte, hp₂_ne]
          by_cases hna : a = 0
          · simp [hna]
          · simp [hna, ih a (Or.inl rfl)]
  intro k
  induction k with
  | zero => intro w; simp [reaches]
  | succ k ih =>
      intro w
      by_cases hwu : w = u
      · subst hwu; simp [reaches]
      · by_cases hwa : w = a
        · rw [hS₁ (k + 1) w (Or.inl hwa), hS₂ (k + 1) w (Or.inl hwa)]
        · by_cases hwne : w = ne
          · rw [hS₁ (k + 1) w (Or.inr hwne), hS₂ (k + 1) w (Or.inr hwne)]
          · by_cases hwb : w = b
            · subst hwb
              simp only [reaches, beq_iff_eq, hwu, ↓reduceIte, hp₁_b, hp₂_b]
              by_cases hne0 : ne = 0
              · simp [hne0]
              · simp only [hne0, ↓reduceIte]
                exact (hS₂ k ne (Or.inr rfl)).symm
            · simp only [reaches, beq_iff_eq, hwu, ↓reduceIte]
              rw [hag w hwa hwne hwb]
              by_cases hz : par₂ w = 0
              · simp [hz]
              · simp [hz, ih (par₂ w)]

theorem reaches_mono_of_non_zero_agree {par par' : ℕ → ℕ} {active : List ℕ}
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hag : ∀ x ∈ active, par x ≠ 0 → par' x = par x) :
    ∀ k p w, w ∈ active → reaches par k p w = true → reaches par' k p w = true := by
  intro k
  induction k with
  | zero =>
      intro p w _ h
      simpa [reaches] using h
  | succ k ih =>
      intro p w hw h
      simp only [reaches, beq_iff_eq] at h ⊢
      by_cases hwp : w = p
      · simp [hwp]
      · simp only [hwp, ↓reduceIte] at h ⊢
        by_cases hpz : par w = 0
        · simp [hpz] at h
        · have hp_act := hmem w hw hpz
          have hpw_eq := hag w hw hpz
          simp only [hpz, ↓reduceIte] at h
          simp only [hpw_eq, hpz, ↓reduceIte]
          exact ih p (par w) hp_act h

theorem tree_all_reaches_head {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {t : AuxTree} (ht : t ∈ trees)
    (hpp0 : (st.splay.nodes t.rootId).ppar = 0) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∀ z ∈ t.toList, reaches par active.length (listHead0 (treeIds P st.splay t)) z = true := by
  intro active par z hz
  let ids := treeIds P st.splay t
  have ht_inv := W.treesInv _ ht
  have hids_nd : ids.Nodup := treeIds_nodup ht_inv
  have hsub : ∀ w ∈ ids, w ∈ active := fun w hw =>
    List.mem_flatMap.mpr ⟨t, ht, (mem_treeIds_iff P st.splay t w).mp hw⟩
  have h0_nin : (0 : ℕ) ∉ ids := fun h0 => by
    have hv := W.activeValid 0 (hsub 0 h0)
    simp [isNode] at hv
  have hagree : ∀ w ∈ ids, chainPred 0 ids w = par w := fun w hw => by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup ht ((mem_treeIds_iff P st.splay t w).mp hw), hpp0]
  exact reaches_chain_head_of_acyclic W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp)
    W.acyclic ids 0 (listHead0 ids) hids_nd (fun w hw h0 => h0_nin (h0 ▸ hw)) h0_nin hsub hagree
    (Or.inl rfl) z ((mem_treeIds_iff P st.splay t z).mpr hz)

/-! ### `cut_splice_spec`: detaching 3-node root tree and freeing edge slot `ne` -/

theorem cut_splice_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {ne a b : ℕ}
    (ht : AuxTree.node ne (.node a .leaf .leaf) (.node b .leaf .leaf) ∈ trees)
    (hrev : (st.splay.nodes ne).rev = false)
    (htag : (st.splay.nodes ne).tag = P.idTag)
    (hpp0 : (st.splay.nodes ne).ppar = 0)
    (he_slot : isEdgeSlot st.n ne) :
    let s1 := SplayState.detachRootChildren P st.splay ne
    let s2 := s1.setPar ne st.freeHead
    let st' : LctState α σ τ := { n := st.n, splay := s2, freeHead := ne }
    let trees' := AuxTree.node a .leaf .leaf :: AuxTree.node b .leaf .leaf ::
      trees.erase (.node ne (.node a .leaf .leaf) (.node b .leaf .leaf))
    LctInvWith P st' trees' (ne :: freeList) depth ∧
    sumTreePhi P st' ≤ sumTreePhi P st ∧
    heavyCount P st' ≤ heavyCount P st + 1 ∧
    (inducedSubPar P s2 trees' a = 0) ∧
    (inducedSubPar P s2 trees' b = 0) ∧
    (∀ z ∉ [a, ne, b], inducedSubPar P s2 trees' z = inducedSubPar P st.splay trees z) := by
  intro s1 s2 st' trees'
  let t := AuxTree.node ne (.node a .leaf .leaf) (.node b .leaf .leaf)
  let er := trees.erase t
  let active := trees.flatMap AuxTree.toList
  let active' := trees'.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  let par' := inducedSubPar P s2 trees'
  have ht_inv := W.treesInv _ ht
  have hnd := ht_inv.nodup
  simp only [AuxTree.toList, List.nil_append, List.cons_append,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have hane : a ≠ ne := hnd.1.1
  have hab : a ≠ b := hnd.1.2
  have hneb : ne ≠ b := hnd.2.1
  have hdet := SplayState.detachRootChildren_preserves hL ht_inv hrev htag
  rcases hdet with ⟨_, ha_inv1, hb_inv1, _, hpp_a1, hpp_b1, hout1⟩
  have ha_inv : SplayState.TreeInv P s2 (.node a .leaf .leaf) :=
    SplayState.TreeInv_agree ha_inv1 (fun u hu => by
      have hua : u = a := by simpa [AuxTree.toList] using hu
      dsimp only [s2, s1]
      simp [SplayState.setPar, hua ▸ hane])
  have hb_inv : SplayState.TreeInv P s2 (.node b .leaf .leaf) :=
    SplayState.TreeInv_agree hb_inv1 (fun u hu => by
      have hub : u = b := by simpa [AuxTree.toList] using hu
      dsimp only [s2, s1]
      simp [SplayState.setPar, hub ▸ hneb.symm])
  have hpp_a2 : (s2.nodes a).ppar = 0 := by
    simpa [s2, s1, SplayState.setPar, hane] using hpp_a1
  have hpp_b2 : (s2.nodes b).ppar = 0 := by
    simpa [s2, s1, SplayState.setPar, hneb.symm] using hpp_b1
  have hout2 : ∀ u ∉ [a, ne, b], s2.nodes u = st.splay.nodes u := fun u hu => by
    have hune : u ≠ ne := fun h => hu (by simp [h])
    dsimp only [s2, s1]
    simp [SplayState.setPar, hune]
    exact hout1 u hu
  have hperm_t : trees.Perm (t :: er) := List.perm_cons_erase ht
  have hact_t_perm : active.Perm ([a, ne, b] ++ er.flatMap AuxTree.toList) := by
    have h1 : active.Perm ((t :: er).flatMap AuxTree.toList) :=
      hperm_t.flatMap (fun _ _ => List.Perm.refl _)
    simpa [t, active, AuxTree.toList] using h1
  have hdisj_er : ∀ u ∈ er.flatMap AuxTree.toList, u ∉ [a, ne, b] := by
    have h1 := erase_flatMap_disjoint_of_nodup ht W.activeNodup
    simpa [t, AuxTree.toList] using h1
  have hact'_perm_eq : active'.Perm ([a, b] ++ er.flatMap AuxTree.toList) := by
    simp only [active', trees', List.flatMap_cons, AuxTree.toList, List.nil_append,
      List.append_nil, List.cons_append]
    exact List.Perm.refl _
  have hact_er_nd : ([a, b] ++ er.flatMap AuxTree.toList).Nodup := by
    have hnd_all := hact_t_perm.nodup_iff.mp W.activeNodup
    have ha_n := (List.nodup_cons.mp hnd_all).1
    have hber_nd : (b :: er.flatMap AuxTree.toList).Nodup :=
      (List.nodup_cons.mp (List.nodup_cons.mp hnd_all).2).2
    refine List.nodup_cons.mpr ⟨?_, hber_nd⟩
    intro hm
    rcases List.mem_cons.mp hm with rfl | h_er
    · exact hab rfl
    · exact ha_n (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h_er))
  have hact'_nd : active'.Nodup := hact'_perm_eq.symm.nodup_iff.mp hact_er_nd
  have ha_mem_act : a ∈ active := hact_t_perm.symm.mem_iff.mp (by simp)
  have hne_mem_act : ne ∈ active := hact_t_perm.symm.mem_iff.mp (by simp)
  have hb_mem_act : b ∈ active := hact_t_perm.symm.mem_iff.mp (by simp)
  have hmem_act'_iff : ∀ z, z ∈ active' ↔ (z ∈ active ∧ z ≠ ne) := by
    intro z
    rw [hact'_perm_eq.mem_iff, hact_t_perm.mem_iff]
    constructor
    · intro hz
      rcases List.mem_append.mp hz with h_ab | hz_er
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h_ab
        rcases h_ab with rfl | rfl
        · exact ⟨by simp, hane⟩
        · exact ⟨by simp, hneb.symm⟩
      · exact ⟨List.mem_append_right _ hz_er, fun h => hdisj_er z hz_er (by simp [h])⟩
    · rintro ⟨hz, hzne⟩
      rcases List.mem_append.mp hz with h_t | hz_er
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h_t
        rcases h_t with rfl | rfl | rfl <;> simp_all
      · exact List.mem_append_right _ hz_er
  have hids_old : treeIds P st.splay t = [a, ne, b] := by
    simp only [treeIds, t, SplayState.evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id,
      Bool.false_xor, Bool.false_eq_true, ↓reduceIte, List.map_append]
    cases (st.splay.nodes a).rev <;> cases (st.splay.nodes b).rev <;> simp
  have hpar_a : par a = 0 := by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup ht (by simp [AuxTree.toList]),
      hids_old, AuxTree.rootId, hpp0, chainPred_head]
  have hpar_ne : par ne = a := by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup ht (by simp [AuxTree.toList]),
      hids_old, AuxTree.rootId, hpp0]
    simp [chainPred, hane.symm]
  have hpar_b : par b = ne := by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup ht (by simp [AuxTree.toList]),
      hids_old, AuxTree.rootId, hpp0]
    simp [chainPred, hneb.symm, hab.symm]
  have ha_v : isVertex st.n a := by
    have h_ep := W.edgeParVertex ne hne_mem_act he_slot
    change par ne ≠ 0 ∧ isVertex st.n (par ne) at h_ep
    have h2 := h_ep.2
    rwa [hpar_ne] at h2
  have hb_v : isVertex st.n b := by
    have hbnd := W.activeValid b hb_mem_act
    by_contra hnv
    have hbe := isEdgeSlot_of_isNode_not_vertex hbnd hnv
    have hbv := (W.edgeParVertex b hb_mem_act hbe).2
    change isVertex st.n (par b) at hbv
    rw [hpar_b] at hbv
    simp only [isVertex] at hbv
    simp only [isEdgeSlot] at he_slot
    omega
  have hpar'_a : par' a = 0 := by
    dsimp only [par']
    rw [inducedSubPar_eq_of_mem hact'_nd (t := AuxTree.node a .leaf .leaf)
      (by simp [trees']) (by simp [AuxTree.toList]), treeIds_singleton]
    simp [AuxTree.rootId, hpp_a2, chainPred]
  have hpar'_b : par' b = 0 := by
    dsimp only [par']
    rw [inducedSubPar_eq_of_mem hact'_nd (t := AuxTree.node b .leaf .leaf)
      (by simp [trees']) (by simp [AuxTree.toList]), treeIds_singleton]
    simp [AuxTree.rootId, hpp_b2, chainPred]
  have hpar'_ne : par' ne = 0 :=
    inducedSubPar_eq_zero_of_not_mem (fun hm => ((hmem_act'_iff ne).mp hm).2 rfl)
  have hpar'_out : ∀ z ∉ [a, ne, b], par' z = par z := by
    intro z hz
    dsimp only [par', par]
    by_cases hz_act : z ∈ active
    · have hz_act' : z ∈ active' := (hmem_act'_iff z).mpr ⟨hz_act, fun h => hz (by simp [h])⟩
      have hz_er : z ∈ er.flatMap AuxTree.toList := by
        rcases List.mem_append.mp (hact'_perm_eq.mem_iff.mp hz_act') with h_ab | hzr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h_ab
          rcases h_ab with rfl | rfl <;> exact absurd (by simp) hz
        · exact hzr
      obtain ⟨c, hc_er, hzc⟩ := List.mem_flatMap.mp hz_er
      have hc_ts := List.mem_of_mem_erase hc_er
      have hc_in_trees' : c ∈ trees' := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc_er)
      rw [inducedSubPar_eq_of_mem hact'_nd (t := c) hc_in_trees' hzc,
        inducedSubPar_eq_of_mem W.activeNodup (t := c) hc_ts hzc]
      have hag_c : ∀ u ∈ c.toList, s2.nodes u = st.splay.nodes u := fun u hu =>
        hout2 u (hdisj_er u (List.mem_flatMap.mpr ⟨c, hc_er, hu⟩))
      rw [treeIds_agree hag_c, hag_c c.rootId (AuxTree.rootId_mem (W.treesNonEmpty c hc_ts))]
    · have hz_nact' : z ∉ active' := fun hm => hz_act ((hmem_act'_iff z).mp hm).1
      rw [inducedSubPar_eq_zero_of_not_mem hz_nact', inducedSubPar_eq_zero_of_not_mem hz_act]
  have hno_child_ne : ∀ c ∈ er, (st.splay.nodes c.rootId).ppar ≠ ne := by
    intro c hc_er hpp_c
    have hc_ts := List.mem_of_mem_erase hc_er
    let hd_c := listHead0 (treeIds P st.splay c)
    have hhd_mem : hd_c ∈ c.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty c hc_ts)
    have hhd_act : hd_c ∈ active := List.mem_flatMap.mpr ⟨c, hc_ts, hhd_mem⟩
    have hhd_nin : hd_c ∉ [a, ne, b] := hdisj_er _ (List.mem_flatMap.mpr ⟨c, hc_er, hhd_mem⟩)
    have hhd_par : par hd_c = ne := by
      dsimp only [par]
      rw [inducedSubPar_eq_of_mem W.activeNodup hc_ts hhd_mem]
      cases hids_c : treeIds P st.splay c with
      | nil => exact absurd hids_c (treeIds_ne_nil (W.treesNonEmpty c hc_ts))
      | cons _ _ =>
          dsimp only [hd_c]
          rw [hids_c]
          simp [listHead0, chainPred_head, hpp_c]
    have hhd_v : isVertex st.n hd_c := by
      by_contra hnv
      have hhe := isEdgeSlot_of_isNode_not_vertex (W.activeValid hd_c hhd_act) hnv
      have hhv := (W.edgeParVertex hd_c hhd_act hhe).2
      change isVertex st.n (par hd_c) at hhv
      rw [hhd_par] at hhv
      simp only [isVertex] at hhv
      simp only [isEdgeSlot] at he_slot
      omega
    rcases W.edgeUniqueChild ne hne_mem_act he_slot with ⟨w₀, _, huniq⟩
    have h1 := huniq hd_c ⟨hhd_act, hhd_par, hhd_v, fun h => by
      change hd_c = par ne at h; rw [hpar_ne] at h; exact hhd_nin (by simp [h])⟩
    have h2 := huniq b ⟨hb_mem_act, hpar_b, hb_v, fun h => by
      change b = par ne at h; rw [hpar_ne] at h; exact hneb (by omega)⟩
    exact hhd_nin (by simp [h1.trans h2.symm])
  have h_er_agree : ∀ c ∈ er,
      (s2.nodes c.rootId).ppar = (st.splay.nodes c.rootId).ppar ∧
      treeIds P s2 c = treeIds P st.splay c ∧
      listHead0 (treeIds P st.splay c) ∉ [a, ne, b] := by
    intro c hc_er
    have hc_ts := List.mem_of_mem_erase hc_er
    have hag : ∀ u ∈ c.toList, s2.nodes u = st.splay.nodes u := fun u hu =>
      hout2 u (hdisj_er u (List.mem_flatMap.mpr ⟨c, hc_er, hu⟩))
    have hhd_nin : listHead0 (treeIds P st.splay c) ∉ [a, ne, b] :=
      hdisj_er _ (List.mem_flatMap.mpr ⟨c, hc_er, listHead0_mem_of_ne_nil (W.treesNonEmpty c hc_ts)⟩)
    exact ⟨by rw [hag c.rootId (AuxTree.rootId_mem (W.treesNonEmpty c hc_ts))],
      treeIds_agree hag, hhd_nin⟩
  have hne_nin_fl : ne ∉ freeList := (W.partitionSlots ne he_slot).mp hne_mem_act
  have hfl : FreeListInv s2 ne (ne :: freeList) := by
    have hfl1 : FreeListInv s1 st.freeHead freeList :=
      FreeListInv_agree W.freeListInv (fun e he => by
        have hed := W.active_of_freeList_disjoint he
        have he_nin : e ∉ [a, ne, b] := fun hm =>
          hed (hact_t_perm.symm.mem_iff.mp (List.mem_append_left _ hm))
        rw [hout1 e he_nin])
    refine ⟨fun h => by simp [isEdgeSlot] at he_slot; omega, rfl, ?_⟩
    have hs2_ne : (s2.nodes ne).par = st.freeHead := by simp [s2, SplayState.setPar]
    rw [hs2_ne]
    exact FreeListInv_agree hfl1 (fun e he => by
      have hne_e : e ≠ ne := fun h => hne_nin_fl (h ▸ he)
      simp [s2, SplayState.setPar, hne_e])
  have hsubpar'_mem : ∀ z ∈ active', par' z ≠ 0 → par' z ∈ active' := by
    intro z hz hpz
    by_cases hza : z = a
    · subst hza; exact absurd hpar'_a hpz
    · by_cases hzb : z = b
      · subst hzb; exact absurd hpar'_b hpz
      · have hzne : z ≠ ne := ((hmem_act'_iff z).mp hz).2
        have hz_nin : z ∉ [a, ne, b] := by simp [hza, hzne, hzb]
        rw [hpar'_out z hz_nin] at hpz ⊢
        have hp_act : par z ∈ active := W.subPar_mem_active ((hmem_act'_iff z).mp hz).1 hpz
        refine (hmem_act'_iff _).mpr ⟨hp_act, fun h => ?_⟩
        have hz_hd_v : isVertex st.n z := by
          by_contra hnv
          have hze := isEdgeSlot_of_isNode_not_vertex (W.activeValid z ((hmem_act'_iff z).mp hz).1) hnv
          have hzv := (W.edgeParVertex z ((hmem_act'_iff z).mp hz).1 hze).2
          change isVertex st.n (par z) at hzv
          rw [h] at hzv
          simp only [isVertex] at hzv; simp only [isEdgeSlot] at he_slot; omega
        rcases W.edgeUniqueChild ne hne_mem_act he_slot with ⟨w₀, _, huniq⟩
        have h1 := huniq z ⟨((hmem_act'_iff z).mp hz).1, h, hz_hd_v, fun hne_p => by
          change z = par ne at hne_p; rw [hpar_ne] at hne_p; exact hz_nin (by simp [hne_p])⟩
        have h2 := huniq b ⟨hb_mem_act, hpar_b, hb_v, fun hne_p => by
          change b = par ne at hne_p; rw [hpar_ne] at hne_p; exact hneb (by omega)⟩
        exact hz_nin (by simp [h1.trans h2.symm])
  have hacyc' : ∀ z ∈ active', par' z ≠ 0 → depth (par' z) < depth z := by
    intro z hz hpz
    by_cases hza : z = a
    · subst hza; exact absurd hpar'_a hpz
    · by_cases hzb : z = b
      · subst hzb; exact absurd hpar'_b hpz
      · have hzne : z ≠ ne := ((hmem_act'_iff z).mp hz).2
        have hz_nin : z ∉ [a, ne, b] := by simp [hza, hzne, hzb]
        rw [hpar'_out z hz_nin] at hpz ⊢
        exact W.acyclic z ((hmem_act'_iff z).mp hz).1 hpz
  have hW' : LctInvWith P st' trees' (ne :: freeList) depth :=
    { treesNonEmpty := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc'
        · simp
        · rcases List.mem_cons.mp hc' with rfl | hc''
          · simp
          · exact W.treesNonEmpty c (List.mem_of_mem_erase hc'')
      treesInv := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ha_inv
        · rcases List.mem_cons.mp hc' with rfl | hc''
          · exact hb_inv
          · have hc_ts := List.mem_of_mem_erase hc''
            exact SplayState.TreeInv_agree (W.treesInv c hc_ts)
              (fun u hu => (hout2 u (hdisj_er u (List.mem_flatMap.mpr ⟨c, hc'', hu⟩))).symm)
      activeNodup := hact'_nd
      activeValid := fun z hz => W.activeValid z ((hmem_act'_iff z).mp hz).1
      verticesActive := fun v hv => (hmem_act'_iff (vid v)).mpr ⟨W.verticesActive v hv, fun h => by
        have hvv : isVertex st.n (vid v) := ⟨by simp [vid], by simp [vid]; omega⟩
        simp only [isVertex] at hvv; simp only [isEdgeSlot] at he_slot; omega⟩
      freeNodup := List.nodup_cons.mpr ⟨hne_nin_fl, W.freeNodup⟩
      freeValid := fun e he => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact he_slot
        · exact W.freeValid e he'
      partitionSlots := fun e he => by
        constructor
        · intro he_act'
          have hmem_old := ((hmem_act'_iff e).mp he_act')
          intro hfl_mem
          rcases List.mem_cons.mp hfl_mem with rfl | hfl_old
          · exact hmem_old.2 rfl
          · exact (W.partitionSlots e he).mp hmem_old.1 hfl_old
        · intro hn_fl
          simp only [List.mem_cons, not_or] at hn_fl
          exact (hmem_act'_iff e).mpr
            ⟨(W.partitionSlots e he).mpr hn_fl.2, fun h => hn_fl.1 h⟩
      freeListInv := hfl
      pparActive := fun c hc hp => by
        dsimp only [st'] at hp ⊢
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact absurd hpp_a2 hp
        · rcases List.mem_cons.mp hc' with rfl | hc''
          · exact absurd hpp_b2 hp
          · have hc_ts := List.mem_of_mem_erase hc''
            have hpp_old : (st.splay.nodes c.rootId).ppar = (s2.nodes c.rootId).ppar :=
              (h_er_agree c hc'').1.symm
            have hne_pp : (s2.nodes c.rootId).ppar ≠ ne := fun h => hno_child_ne c hc'' (hpp_old.trans h)
            refine (hmem_act'_iff _).mpr ⟨?_, hne_pp⟩
            rw [← hpp_old]
            exact W.pparActive c hc_ts (by rw [hpp_old]; exact hp)
      acyclic := hacyc'
      vertexParEdge := fun u huv hpu => by
        dsimp only [st'] at huv ⊢
        change par' u ≠ 0 at hpu
        change isEdgeSlot st.n (par' u)
        by_cases hua : u = a
        · subst hua; exact absurd hpar'_a hpu
        · by_cases hub : u = b
          · subst hub; exact absurd hpar'_b hpu
          · have hune : u ≠ ne := fun h => by
              subst h; simp only [isVertex] at huv; simp only [isEdgeSlot] at he_slot; omega
            have hu_nin : u ∉ [a, ne, b] := by simp [hua, hune, hub]
            rw [hpar'_out u hu_nin] at hpu ⊢
            exact W.vertexParEdge u huv hpu
      edgeParVertex := fun e he hes => by
        dsimp only [st'] at hes ⊢
        change par' e ≠ 0 ∧ isVertex st.n (par' e)
        by_cases hea : e = a
        · subst hea; simp only [isVertex] at ha_v; simp only [isEdgeSlot] at hes; omega
        · by_cases heb : e = b
          · subst heb; simp only [isVertex] at hb_v; simp only [isEdgeSlot] at hes; omega
          · have hene : e ≠ ne := ((hmem_act'_iff e).mp he).2
            have he_nin : e ∉ [a, ne, b] := by simp [hea, hene, heb]
            rw [hpar'_out e he_nin]
            exact W.edgeParVertex e ((hmem_act'_iff e).mp he).1 hes
      edgeUniqueChild := fun e he hes => by
        dsimp only [st'] at hes ⊢
        have hea : e ≠ a := fun h => by
          subst h; simp only [isVertex] at ha_v; simp only [isEdgeSlot] at hes; omega
        have heb : e ≠ b := fun h => by
          subst h; simp only [isVertex] at hb_v; simp only [isEdgeSlot] at hes; omega
        have hene : e ≠ ne := ((hmem_act'_iff e).mp he).2
        have he_nin : e ∉ [a, ne, b] := by simp [hea, hene, heb]
        rcases W.edgeUniqueChild e ((hmem_act'_iff e).mp he).1 hes with
          ⟨w₀, ⟨hw₀_act, hw₀_p, hw₀_v, hw₀_ne⟩, huniq⟩
        have hw₀_nin : w₀ ∉ [a, ne, b] := by
          intro hm
          rcases List.mem_cons.mp hm with hwa | hm'
          · change par w₀ = e at hw₀_p; rw [hwa, hpar_a] at hw₀_p
            simp only [isEdgeSlot] at hes; omega
          · rcases List.mem_cons.mp hm' with hwne | hm''
            · change par w₀ = e at hw₀_p; rw [hwne, hpar_ne] at hw₀_p; exact hea hw₀_p.symm
            · have : w₀ = b := by simpa using hm''
              change par w₀ = e at hw₀_p
              rw [this, hpar_b] at hw₀_p; exact hene hw₀_p.symm
        have hw₀_act' : w₀ ∈ active' :=
          (hmem_act'_iff w₀).mpr ⟨hw₀_act, fun h => hw₀_nin (by simp [h])⟩
        have hpar'_w₀ : par' w₀ = e := (hpar'_out w₀ hw₀_nin).trans hw₀_p
        have hpar'_e : par' e = par e := hpar'_out e he_nin
        refine ⟨w₀, ⟨hw₀_act', hpar'_w₀, hw₀_v, ?_⟩, ?_⟩
        · change w₀ ≠ par' e; rw [hpar'_e]; exact hw₀_ne
        · intro y ⟨hy_act', hpy, hy_v, hy_ne⟩
          have hy_nin : y ∉ [a, ne, b] := by
            intro hm
            rcases List.mem_cons.mp hm with hya | hm'
            · change par' y = e at hpy; rw [hya, hpar'_a] at hpy
              simp only [isEdgeSlot] at hes; omega
            · rcases List.mem_cons.mp hm' with hyne | hm''
              · exact ((hmem_act'_iff y).mp hy_act').2 hyne
              · have : y = b := List.mem_singleton.mp hm''
                change par' y = e at hpy
                rw [this, hpar'_b] at hpy; simp only [isEdgeSlot] at hes; omega
          change par' y = e at hpy
          rw [hpar'_out y hy_nin] at hpy
          change y ≠ par' e at hy_ne
          rw [hpar'_e] at hy_ne
          exact huniq y ⟨((hmem_act'_iff y).mp hy_act').1, hpy, hy_v, hy_ne⟩ }
  rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
  rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
  have hrep_out : ∀ u, u ≠ a → u ≠ ne → repSize active' par' u = repSize active par u := by
    intro u hua hune
    have hlen_le : active'.length ≤ active.length := by
      rw [hact'_perm_eq.length_eq, hact_t_perm.length_eq]
      simp
    have hstab : ∀ w ∈ active',
        reaches par' active'.length u w = reaches par' active.length u w := fun w hw =>
      (reaches_stable hact'_nd hsubpar'_mem hacyc' hw hlen_le).symm
    have hagree_cut : ∀ w, w ≠ a → w ≠ ne → w ≠ b → par' w = par w := fun w h1 h2 h3 =>
      hpar'_out w (by simp [h1, h2, h3])
    have hcut_eq : ∀ w, reaches par' active.length u w = reaches par active.length u w :=
      reaches_cut_b_eq hagree_cut hpar'_a hpar'_ne hpar'_b hpar_a hpar_ne hpar_b hua hune
        active.length
    have hne_false : reaches par active.length u ne = false := by
      have : reaches par' active.length u ne = false := by
        cases hL_eq : active.length with
        | zero => simp [reaches, hune.symm]
        | succ m => simp [reaches, hune.symm, hpar'_ne]
      exact (hcut_eq ne).symm.trans this
    have hperm_act : active.Perm (ne :: active') := by
      have h1 : active.Perm ([a, ne, b] ++ er.flatMap AuxTree.toList) := hact_t_perm
      have h2 : ([a, ne, b] ++ er.flatMap AuxTree.toList).Perm
          (ne :: ([a, b] ++ er.flatMap AuxTree.toList)) := by
        simp only [List.cons_append, List.nil_append]
        exact List.Perm.swap ne a (b :: er.flatMap AuxTree.toList)
      exact h1.trans (h2.trans (List.Perm.cons ne hact'_perm_eq.symm))
    dsimp only [repSize]
    rw [(hperm_act.filter _).length_eq, filter_cons_length, hne_false]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact congrArg List.length (List.filter_congr (fun w hw => (hstab w hw).trans (hcut_eq w)))
  let v := vSize P st.splay active par trees
  let v' := vSize P s2 active' par' trees'
  have hv_eq : ∀ u, u ≠ 0 → v' u = v u := by
    intro u hu_nz
    dsimp only [v', v, vSize, trees']
    rw [((hperm_t.filter _).map _).sum_eq, filter_cons_map_sum, filter_cons_map_sum,
      filter_cons_map_sum]
    have hp_old_t : ((st.splay.nodes t.rootId).ppar == u) = false := by
      simp [t, AuxTree.rootId, hpp0, beq_false_of_ne (Ne.symm hu_nz)]
    have hp_new_a : ((s2.nodes (AuxTree.node a .leaf .leaf).rootId).ppar == u) = false := by
      simp [AuxTree.rootId, hpp_a2, beq_false_of_ne (Ne.symm hu_nz)]
    have hp_new_b : ((s2.nodes (AuxTree.node b .leaf .leaf).rootId).ppar == u) = false := by
      simp [AuxTree.rootId, hpp_b2, beq_false_of_ne (Ne.symm hu_nz)]
    have hfilt_er : (er.filter (fun c => (s2.nodes c.rootId).ppar == u)) =
        (er.filter (fun c => (st.splay.nodes c.rootId).ppar == u)) :=
      List.filter_congr (fun c hc => by rw [(h_er_agree c hc).1])
    have hsum_er : ((er.filter (fun c => (s2.nodes c.rootId).ppar == u)).map
          (fun c => repSize active' par' (listHead0 (treeIds P s2 c)))).sum =
        ((er.filter (fun c => (st.splay.nodes c.rootId).ppar == u)).map
          (fun c => repSize active par (listHead0 (treeIds P st.splay c)))).sum := by
      rw [hfilt_er]
      congr 1
      refine List.map_congr_left (fun c hc => ?_)
      have hc' := h_er_agree c (List.mem_filter.mp hc).1
      have hha : listHead0 (treeIds P st.splay c) ≠ a := fun h => hc'.2.2 (by simp [h])
      have hhne : listHead0 (treeIds P st.splay c) ≠ ne := fun h => hc'.2.2 (by simp [h])
      rw [hc'.2.1, hrep_out _ hha hhne]
    rw [hp_old_t, hp_new_a, hp_new_b, hsum_er]
    simp
  have hphi_le : sumTreePhi P st' ≤ sumTreePhi P st := by
    rw [hPhi_new, hPhi_old]
    have hsum_old : sumTreePhiList v trees = t.treePhi v + sumTreePhiList v er := by
      dsimp only [sumTreePhiList]
      rw [(hperm_t.map _).sum_eq, List.map_cons, List.sum_cons]
    have hsum_new : sumTreePhiList v' trees' =
        (AuxTree.node a .leaf .leaf).treePhi v' +
        ((AuxTree.node b .leaf .leaf).treePhi v' + sumTreePhiList v' er) := by
      dsimp only [sumTreePhiList, trees', er, t]
      simp only [List.map_cons, List.sum_cons]
    have ha_nz : a ≠ 0 := by have := W.activeValid a ha_mem_act; simp [isNode] at this; omega
    have hb_nz : b ≠ 0 := by have := W.activeValid b hb_mem_act; simp [isNode] at this; omega
    have hphi_a : (AuxTree.node a .leaf .leaf).treePhi v' = (AuxTree.node a .leaf .leaf).rank v := by
      rw [SplayState.treePhi_agree (v₂ := v) (fun u hu => by
        have : u = a := by simpa [AuxTree.toList] using hu
        rw [this]; exact hv_eq a ha_nz)]
      simp [AuxTree.treePhi]
    have hphi_b : (AuxTree.node b .leaf .leaf).treePhi v' = (AuxTree.node b .leaf .leaf).rank v := by
      rw [SplayState.treePhi_agree (v₂ := v) (fun u hu => by
        have : u = b := by simpa [AuxTree.toList] using hu
        rw [this]; exact hv_eq b hb_nz)]
      simp [AuxTree.treePhi]
    have hsum_er : sumTreePhiList v' er = sumTreePhiList v er := by
      dsimp only [sumTreePhiList]
      congr 1
      refine List.map_congr_left (fun c hc => SplayState.treePhi_agree (fun u hu => ?_))
      have hnd_u := W.activeValid u (List.mem_flatMap.mpr ⟨c, List.mem_of_mem_erase hc, hu⟩)
      exact hv_eq u (by simp [isNode] at hnd_u; omega)
    have hrank_le := singleton_rank_le_treePhi v ne a b
    dsimp only [v, v'] at hsum_old hsum_new hphi_a hphi_b hsum_er hrank_le
    dsimp only [t, er] at hsum_old hsum_new hsum_er hrank_le
    rw [hsum_new, hsum_old, hphi_a, hphi_b, hsum_er]
    omega
  have hheavy_le : heavyCount P st' ≤ heavyCount P st + 1 := by
    have ha_light : isHeavyEdge P s2 active' par' (.node a .leaf .leaf) = false := by
      dsimp only [isHeavyEdge]; simp [AuxTree.rootId, hpp_a2]
    have hb_light : isHeavyEdge P s2 active' par' (.node b .leaf .leaf) = false := by
      dsimp only [isHeavyEdge]; simp [AuxTree.rootId, hpp_b2]
    have hsplit : (er.filter (isHeavyEdge P s2 active' par')).length ≤
        (er.filter (fun c => ((s2.nodes c.rootId).ppar != a) &&
          isHeavyEdge P s2 active' par' c)).length +
        (er.filter (fun c => ((s2.nodes c.rootId).ppar == a) &&
          isHeavyEdge P s2 active' par' c)).length := by
      have hperm_f : er.filter (isHeavyEdge P s2 active' par') =
          er.filter (fun c => (((s2.nodes c.rootId).ppar != a) &&
            isHeavyEdge P s2 active' par' c) ||
            (((s2.nodes c.rootId).ppar == a) && isHeavyEdge P s2 active' par' c)) := by
        refine List.filter_congr (fun c _ => ?_)
        by_cases h : (s2.nodes c.rootId).ppar = a <;>
          cases isHeavyEdge P s2 active' par' c <;> simp [h]
      rw [hperm_f]
      exact filter_or_length_le _ _ er
    have hne_a_le : (er.filter (fun c => ((s2.nodes c.rootId).ppar != a) &&
        isHeavyEdge P s2 active' par' c)).length ≤ heavyCount P st := by
      have hlen1 := filter_length_le_of_imp
        (fun c => ((s2.nodes c.rootId).ppar != a) && isHeavyEdge P s2 active' par' c)
        (isHeavyEdge P st.splay active par) er (fun c hc h => by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
          have hc' := h_er_agree c hc
          have hc_pp_ne : (st.splay.nodes c.rootId).ppar ≠ ne := hno_child_ne c hc
          have hpp_na : (st.splay.nodes c.rootId).ppar ≠ a := hc'.1 ▸ h.1
          have hh_eq : isHeavyEdge P s2 active' par' c = isHeavyEdge P st.splay active par c := by
            dsimp only [isHeavyEdge]
            have hha : listHead0 (treeIds P st.splay c) ≠ a := fun hm => hc'.2.2 (by simp [hm])
            have hhne : listHead0 (treeIds P st.splay c) ≠ ne := fun hm => hc'.2.2 (by simp [hm])
            rw [hc'.1, hc'.2.1, hrep_out _ hpp_na hc_pp_ne, hrep_out _ hha hhne]
          exact hh_eq ▸ h.2)
      have hH_old_eq : heavyCount P st = (trees.filter (isHeavyEdge P st.splay active par)).length :=
        hH_old
      have hperm_t' : trees.Perm (t :: trees.erase t) := hperm_t
      dsimp only [active, par] at hH_old_eq hlen1
      dsimp only [er] at hlen1 ⊢
      rw [hH_old_eq, (hperm_t'.filter _).length_eq, filter_cons_length]
      omega
    have her_nd : er.Nodup :=
      (List.nodup_cons.mp ((hperm_t.nodup_iff.mp
        (nodup_of_flatMap_nodup trees W.activeNodup W.treesNonEmpty)))).2
    have ha_le1 : (er.filter (fun c => ((s2.nodes c.rootId).ppar == a) &&
        isHeavyEdge P s2 active' par' c)).length ≤ 1 := by
      refine filter_length_le_one_of_nodup _ er her_nd (fun c₁ hc₁ c₂ hc₂ hq₁ hq₂ => ?_)
      simp only [Bool.and_eq_true, beq_iff_eq] at hq₁ hq₂
      by_contra hne
      have hc₁_ts := List.mem_of_mem_erase hc₁
      have hc₂_ts := List.mem_of_mem_erase hc₂
      let d₁ := listHead0 (treeIds P s2 c₁)
      let d₂ := listHead0 (treeIds P s2 c₂)
      have hc₁_trees' : c₁ ∈ trees' := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc₁)
      have hc₂_trees' : c₂ ∈ trees' := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc₂)
      have hd₁_mem : d₁ ∈ active' :=
        List.mem_flatMap.mpr ⟨c₁, hc₁_trees', listHead0_mem_of_ne_nil (W.treesNonEmpty c₁ hc₁_ts)⟩
      have hd₂_mem : d₂ ∈ active' :=
        List.mem_flatMap.mpr ⟨c₂, hc₂_trees', listHead0_mem_of_ne_nil (W.treesNonEmpty c₂ hc₂_ts)⟩
      have hd₁_ne : d₁ ≠ d₂ := fun heq => by
        dsimp only [d₁, d₂] at heq
        exact hne (flatMap_mem_unique hact'_nd hc₁_trees' hc₂_trees'
          (listHead0_mem_of_ne_nil (W.treesNonEmpty c₁ hc₁_ts))
          (heq ▸ listHead0_mem_of_ne_nil (W.treesNonEmpty c₂ hc₂_ts)))
      have hp1 : par' d₁ = a := by
        dsimp only [d₁, par']
        rw [inducedSubPar_eq_of_mem hact'_nd (t := c₁) hc₁_trees'
          (listHead0_mem_of_ne_nil (W.treesNonEmpty c₁ hc₁_ts))]
        cases hids1 : treeIds P s2 c₁ with
        | nil => exact absurd hids1 (treeIds_ne_nil (W.treesNonEmpty c₁ hc₁_ts))
        | cons _ _ => simp [listHead0, chainPred_head, hq₁.1]
      have hp2 : par' d₂ = a := by
        dsimp only [d₂, par']
        rw [inducedSubPar_eq_of_mem hact'_nd (t := c₂) hc₂_trees'
          (listHead0_mem_of_ne_nil (W.treesNonEmpty c₂ hc₂_ts))]
        cases hids2 : treeIds P s2 c₂ with
        | nil => exact absurd hids2 (treeIds_ne_nil (W.treesNonEmpty c₂ hc₂_ts))
        | cons _ _ => simp [listHead0, chainPred_head, hq₂.1]
      have ha_act' : a ∈ active' := (hmem_act'_iff a).mpr ⟨ha_mem_act, hane⟩
      have ha_nz : a ≠ 0 := by have := W.activeValid a ha_mem_act; simp [isNode] at this; omega
      have htwo := repSize_ge_one_add_two_children hact'_nd hsubpar'_mem hacyc' ha_act' ha_nz
        hd₁_mem hd₂_mem hp1 hp2 hd₁_ne
      dsimp only [d₁, d₂] at htwo
      have hh1 := hq₁.2; have hh2 := hq₂.2
      dsimp only [isHeavyEdge] at hh1 hh2
      simp only [hq₁.1, Bool.and_eq_true, decide_eq_true_eq] at hh1
      simp only [hq₂.1, Bool.and_eq_true, decide_eq_true_eq] at hh2
      dsimp only [active'] at htwo hh1 hh2
      omega
    have hH_new' : heavyCount P st' = (er.filter (isHeavyEdge P s2 active' par')).length := by
      rw [hH_new]
      dsimp only [heavyCountList]
      change ((.node a .leaf .leaf :: .node b .leaf .leaf :: er).filter
        (isHeavyEdge P s2 active' par')).length = _
      rw [filter_cons_length, filter_cons_length, ha_light, hb_light]
      simp
    rw [hH_new']
    omega
  exact ⟨hW', hphi_le, hheavy_le, hpar'_a, hpar'_b, hpar'_out⟩

end MinCostFlow.LinkCut
