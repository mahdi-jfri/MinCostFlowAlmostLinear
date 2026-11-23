module

public import MinCostFlow.LinkCut.ForestSplices
import Mathlib.Tactic

/-!
# Invariant and Potential Lemmas for `attachRight` and `exposeStep`

This file proves `LctInvWith` preservation and `sumTreePhi`/`heavyCount` equations for
`attachRight` (`attachRight_spec`) and the combined `detachRight + attachRight` expose splice
(`exposeStep_heavy_light`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Transition 3: `attachRight` and combined `exposeStep` heavy-light charging -/

private theorem listHead0_mem_treeIds {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {t : AuxTree} (ht : t ≠ .leaf) :
    listHead0 (treeIds P s t) ∈ t.toList := by
  cases hids : treeIds P s t with
  | nil => exact absurd hids (treeIds_ne_nil ht)
  | cons a rest => exact (mem_treeIds_iff P s t a).mp (by simp [hids])

theorem attachRight_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {u : ℕ} {Lu tx : AuxTree}
    (htu : AuxTree.node u Lu .leaf ∈ trees)
    (htx : tx ∈ trees) (hne_t : AuxTree.node u Lu .leaf ≠ tx)
    (hrev_u : (st.splay.nodes u).rev = false)
    (htag_u : (st.splay.nodes u).tag = P.idTag)
    (hpp_x : (st.splay.nodes tx.rootId).ppar = u) :
    let x := tx.rootId
    let s' := SplayState.attachRight P st.splay u x
    let st' : LctState α σ τ := { st with splay := s' }
    let t_new := AuxTree.node u Lu tx
    let trees' := t_new :: ((trees.erase (.node u Lu .leaf)).erase tx)
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    LctInvWith P st' trees' freeList depth ∧
    sumTreePhi P st' = sumTreePhi P st ∧
    heavyCount P st' + (if isHeavyEdge P st.splay active par tx then 1 else 0) = heavyCount P st ∧
    ∀ z, inducedSubPar P s' trees' z = par z := by
  intro x s' st' t_new trees' active par
  have hx_ne : tx ≠ .leaf := W.treesNonEmpty tx htx
  have htx_er : tx ∈ trees.erase (.node u Lu .leaf) :=
    (List.mem_erase_of_ne hne_t.symm).mpr htx
  have hdisj_er := erase_flatMap_disjoint_of_nodup htu W.activeNodup
  have hdisj_u_x : ∀ a ∈ (AuxTree.node u Lu .leaf).toList, a ∉ tx.toList := fun a ha hax =>
    hdisj_er a (List.mem_flatMap.mpr ⟨tx, htx_er, hax⟩) ha
  have hatt := SplayState.attachRight_preserves hL (W.treesInv _ htu) hrev_u htag_u
    (W.treesInv _ htx) hx_ne rfl hdisj_u_x
  rcases hatt with ⟨htnew_inv, _, _, hu_pp, hev_new, hout⟩
  have hu_pp' : (s'.nodes u).ppar = (st.splay.nodes u).ppar := hu_pp
  have hev_new' : SplayState.evalPairs P s' t_new false P.idTag =
      SplayState.evalPairs P st.splay Lu false P.idTag ++ [(u, (st.splay.nodes u).val)] ++
        SplayState.evalPairs P st.splay tx false P.idTag := hev_new
  have hperm_two : trees.Perm (.node u Lu .leaf :: tx :: (trees.erase (.node u Lu .leaf)).erase tx) := by
    have h1 := List.perm_cons_erase htu
    have h2 := List.perm_cons_erase htx_er
    exact h1.trans (List.Perm.cons _ h2)
  have hdisj_er2 : ∀ a ∈ ((trees.erase (.node u Lu .leaf)).erase tx).flatMap AuxTree.toList,
      a ∉ t_new.toList := by
    have hfm := (hperm_two.flatMap (fun _ _ => List.Perm.refl _)).nodup_iff.mp W.activeNodup
    simp only [List.flatMap_cons, List.nodup_append] at hfm
    rcases hfm with ⟨_, ⟨_, _, hdisj_tx_er⟩, hdisj_u⟩
    intro a ha ha_new
    simp only [t_new, AuxTree.toList, List.mem_append, List.mem_singleton] at ha_new
    rcases ha_new with (haL | h_au) | hax
    · exact hdisj_u a (by simp [AuxTree.toList, haL]) _ (List.mem_append_right _ ha) rfl
    · rw [h_au] at ha; exact hdisj_u u (by simp [AuxTree.toList]) _ (List.mem_append_right _ ha) rfl
    · exact hdisj_tx_er a hax _ ha rfl
  have hperm_new : t_new.toList.Perm ((AuxTree.node u Lu .leaf).toList ++ tx.toList) := by
    simp only [t_new, AuxTree.toList, List.append_nil, List.append_assoc]
    exact List.Perm.refl _
  have hact_perm : (trees'.flatMap AuxTree.toList).Perm active := by
    have h1 : active.Perm (((AuxTree.node u Lu .leaf) :: tx ::
        (trees.erase (.node u Lu .leaf)).erase tx).flatMap AuxTree.toList) :=
      hperm_two.flatMap (fun _ _ => List.Perm.refl _)
    refine List.Perm.trans ?_ h1.symm
    simp only [trees', List.flatMap_cons]
    rw [← List.append_assoc (AuxTree.node u Lu .leaf).toList]
    exact hperm_new.append_right _
  have hact_nd : (trees'.flatMap AuxTree.toList).Nodup := hact_perm.nodup_iff.mpr W.activeNodup
  have hids_tu_ne : treeIds P st.splay (.node u Lu .leaf) ≠ [] :=
    treeIds_ne_nil (P := P) (s := st.splay) (by simp)
  have hev_tu_orig : SplayState.evalPairs P st.splay (.node u Lu .leaf) false P.idTag =
      SplayState.evalPairs P st.splay Lu false P.idTag ++ [(u, (st.splay.nodes u).val)] := by
    simp [SplayState.evalPairs, hrev_u, htag_u, hL.compTag_id_left, hL.actVal_id]
  have hids_new_eq : treeIds P s' t_new =
      treeIds P st.splay (.node u Lu .leaf) ++ treeIds P st.splay tx := by
    simp only [treeIds, hev_new', hev_tu_orig, List.map_append]
  have hpar_eq : ∀ z, inducedSubPar P s' trees' z = par z := by
    intro z
    dsimp only [par]
    by_cases hz_act : z ∈ active
    · have hz_act' : z ∈ trees'.flatMap AuxTree.toList := hact_perm.mem_iff.mpr hz_act
      by_cases hz_u : z ∈ (AuxTree.node u Lu .leaf).toList
      · have hz_new : z ∈ t_new.toList := hperm_new.mem_iff.mpr (List.mem_append_left _ hz_u)
        rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees']) hz_new,
          inducedSubPar_eq_of_mem W.activeNodup htu hz_u]
        change chainPred (s'.nodes u).ppar (treeIds P s' t_new) z = _
        rw [hu_pp', hids_new_eq]
        exact chainPred_mem_append_left ((mem_treeIds_iff P st.splay (.node u Lu .leaf) z).mpr hz_u)
      · by_cases hz_x : z ∈ tx.toList
        · have hz_new : z ∈ t_new.toList := hperm_new.mem_iff.mpr (List.mem_append_right _ hz_x)
          rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees']) hz_new,
            inducedSubPar_eq_of_mem W.activeNodup htx hz_x]
          have hnd_new := treeIds_nodup htnew_inv
          rw [hids_new_eq] at hnd_new
          have hlast_tu : (treeIds P st.splay (.node u Lu .leaf)).getLast? = some u := by
            simp only [treeIds, hev_tu_orig, List.map_append, List.map_cons, List.map_nil]
            rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
            rfl
          rw [hids_new_eq, chainPred_mem_append_right hnd_new
            ((mem_treeIds_iff P st.splay tx z).mpr hz_x) hlast_tu, hpp_x]
        · have hz_er : z ∈ ((trees.erase (.node u Lu .leaf)).erase tx).flatMap AuxTree.toList := by
            rcases List.mem_flatMap.mp hz_act' with ⟨a, ha, hza⟩
            rcases List.mem_cons.mp ha with rfl | ha'
            · rcases hperm_new.mem_iff.mp hza |> List.mem_append.mp with h | h <;>
                [exact absurd h hz_u; exact absurd h hz_x]
            · exact List.mem_flatMap.mpr ⟨a, ha', hza⟩
          obtain ⟨a, ha_er, hza⟩ := List.mem_flatMap.mp hz_er
          have ha_ts := List.mem_of_mem_erase (List.mem_of_mem_erase ha_er)
          rw [inducedSubPar_eq_of_mem hact_nd (by simp [trees', ha_er]) hza,
            inducedSubPar_eq_of_mem W.activeNodup ha_ts hza]
          have hag_a : ∀ w ∈ a.toList, s'.nodes w = st.splay.nodes w := fun w hw =>
            hout w (hdisj_er2 w (List.mem_flatMap.mpr ⟨a, ha_er, hw⟩))
          rw [treeIds_agree hag_a, hag_a a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))]
    · have hz_act' : z ∉ trees'.flatMap AuxTree.toList := fun hm => hz_act (hact_perm.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hz_act', inducedSubPar_eq_zero_of_not_mem hz_act]
  have hpar_fun : inducedSubPar P s' trees' = par := funext hpar_eq
  have hfl : FreeListInv s' st.freeHead freeList :=
    FreeListInv_agree W.freeListInv (fun e he => by
      have := hout e (fun hmt => W.active_of_freeList_disjoint he
        (hact_perm.mem_iff.mp (List.mem_flatMap.mpr ⟨t_new, by simp [trees'], hmt⟩)))
      rw [this])
  have hW' : LctInvWith P st' trees' freeList depth :=
    { treesNonEmpty := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha'
        · simp [t_new]
        · exact W.treesNonEmpty a (List.mem_of_mem_erase (List.mem_of_mem_erase ha'))
      treesInv := fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact htnew_inv
        · have ha_ts := List.mem_of_mem_erase (List.mem_of_mem_erase ha')
          exact SplayState.TreeInv_agree (W.treesInv a ha_ts)
            (fun w hw => (hout w (hdisj_er2 w (List.mem_flatMap.mpr ⟨a, ha', hw⟩))).symm)
      activeNodup := hact_nd
      activeValid := fun z hz => W.activeValid z (hact_perm.mem_iff.mp hz)
      verticesActive := fun v hv => hact_perm.symm.mem_iff.mp (W.verticesActive v hv)
      freeNodup := W.freeNodup
      freeValid := W.freeValid
      partitionSlots := fun e he => by
        rw [hact_perm.mem_iff]; exact W.partitionSlots e he
      freeListInv := hfl
      pparActive := fun a ha hp => by
        dsimp only [st'] at hp ⊢
        rw [hact_perm.mem_iff]
        rcases List.mem_cons.mp ha with rfl | ha'
        · change (s'.nodes u).ppar ≠ 0 at hp
          change (s'.nodes u).ppar ∈ active
          rw [hu_pp'] at hp ⊢
          exact W.pparActive _ htu hp
        · have ha_ts := List.mem_of_mem_erase (List.mem_of_mem_erase ha')
          have hrt_eq := hout a.rootId (hdisj_er2 a.rootId
            (List.mem_flatMap.mpr ⟨a, ha', AuxTree.rootId_mem (W.treesNonEmpty a ha_ts)⟩))
          rw [hrt_eq] at hp ⊢
          exact W.pparActive a ha_ts hp
      acyclic := fun z hz hp => by
        rw [hpar_fun] at hp ⊢; exact W.acyclic z (hact_perm.mem_iff.mp hz) hp
      vertexParEdge := fun z hz hp => by
        rw [hpar_fun] at hp ⊢; exact W.vertexParEdge z hz hp
      edgeParVertex := fun e he hes => by
        rw [hpar_fun]; exact W.edgeParVertex e (hact_perm.mem_iff.mp he) hes
      edgeUniqueChild := fun e he hes => by
        rcases W.edgeUniqueChild e (hact_perm.mem_iff.mp he) hes with ⟨w, hw, huniq⟩
        refine ⟨w, ?_, ?_⟩
        · dsimp only [st', active] at *; simp only [hact_perm.mem_iff, hpar_fun]; exact hw
        · intro y hy; dsimp only [st', active] at hy; simp only [hact_perm.mem_iff, hpar_fun] at hy
          exact huniq y hy }
  rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
  rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
  let active' := trees'.flatMap AuxTree.toList
  let v := vSize P st.splay active par trees
  let v' := vSize P s' active' (inducedSubPar P s' trees') trees'
  have hrep_eq : ∀ y, repSize active' (inducedSubPar P s' trees') y = repSize active par y := by
    intro y
    dsimp only [repSize, active']
    rw [hpar_fun, hact_perm.length_eq]
    exact (hact_perm.filter _).length_eq
  have h_er_agree : ∀ a ∈ (trees.erase (.node u Lu .leaf)).erase tx,
      (s'.nodes a.rootId).ppar = (st.splay.nodes a.rootId).ppar ∧
      treeIds P s' a = treeIds P st.splay a := by
    intro a ha_er
    have ha_ts := List.mem_of_mem_erase (List.mem_of_mem_erase ha_er)
    have hag : ∀ w ∈ a.toList, s'.nodes w = st.splay.nodes w := fun w hw =>
      hout w (hdisj_er2 w (List.mem_flatMap.mpr ⟨a, ha_er, hw⟩))
    exact ⟨by rw [hag a.rootId (AuxTree.rootId_mem (W.treesNonEmpty a ha_ts))], treeIds_agree hag⟩
  have hids_tnew_head : listHead0 (treeIds P s' t_new) =
      listHead0 (treeIds P st.splay (.node u Lu .leaf)) := by
    rw [hids_new_eq, listHead0_append_of_ne_nil hids_tu_ne]
  have h_v_gen : ∀ y, v y = v' y +
      (if u == y then repSize active par (listHead0 (treeIds P st.splay tx)) else 0) := by
    intro y
    dsimp only [v, v', vSize]
    rw [((hperm_two.filter _).map _).sum_eq, filter_cons_map_sum, filter_cons_map_sum]
    have hsum_new : ((trees'.filter (fun a => (s'.nodes a.rootId).ppar == y)).map
        (fun a => repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' a)))).sum =
        (if (s'.nodes t_new.rootId).ppar == y then
          repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' t_new)) else 0) +
        ((((trees.erase (.node u Lu .leaf)).erase tx).filter
            (fun a => (s'.nodes a.rootId).ppar == y)).map
          (fun a => repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' a)))).sum := by
      dsimp only [trees']; rw [filter_cons_map_sum]
    have hfilt_er : ((trees.erase (.node u Lu .leaf)).erase tx).filter
        (fun a => (s'.nodes a.rootId).ppar == y) =
        ((trees.erase (.node u Lu .leaf)).erase tx).filter
          (fun a => (st.splay.nodes a.rootId).ppar == y) :=
      List.filter_congr (fun a ha => by rw [(h_er_agree a ha).1])
    have hsum_er : ((((trees.erase (.node u Lu .leaf)).erase tx).filter
          (fun a => (st.splay.nodes a.rootId).ppar == y)).map
        (fun a => repSize active par (listHead0 (treeIds P st.splay a)))).sum =
        ((((trees.erase (.node u Lu .leaf)).erase tx).filter
            (fun a => (s'.nodes a.rootId).ppar == y)).map
          (fun a => repSize active' (inducedSubPar P s' trees') (listHead0 (treeIds P s' a)))).sum := by
      rw [hfilt_er]
      congr 1
      refine List.map_congr_left (fun a ha => ?_)
      have ha' := h_er_agree a (List.mem_filter.mp ha).1
      rw [hrep_eq, ha'.2]
    have hnew_pp : ((s'.nodes t_new.rootId).ppar == y) =
        ((st.splay.nodes (AuxTree.node u Lu .leaf).rootId).ppar == y) := by
      change ((s'.nodes u).ppar == y) = ((st.splay.nodes u).ppar == y)
      rw [hu_pp']
    have htx_pp : ((st.splay.nodes tx.rootId).ppar == y) = (u == y) := by rw [hpp_x]
    rw [hsum_new, hsum_er, hnew_pp, htx_pp, hrep_eq, hids_tnew_head]
    omega
  have hu_nin_tx : u ∉ tx.toList := hdisj_u_x u (by simp [AuxTree.toList])
  have hu_nin_Lu : u ∉ Lu.toList := (AuxTree.nodup_node_unfold (W.treesInv _ htu).nodup).2.1
  have hv_tx : ∀ a ∈ tx.toList, v' a = v a := fun a ha => by
    have hua : u ≠ a := fun h => hu_nin_tx (h ▸ ha)
    simp [h_v_gen a, beq_false_of_ne hua]
  have hv_Lu : ∀ a ∈ Lu.toList, v' a = v a := fun a ha => by
    have hua : u ≠ a := fun h => hu_nin_Lu (h ▸ ha)
    simp [h_v_gen a, beq_false_of_ne hua]
  have htx_sz_eq : tx.treeSize v' = repSize active par (listHead0 (treeIds P st.splay tx)) := by
    rw [SplayState.treeSize_agree hv_tx, treeSize_vSize_eq_repSize W htx]
  have hv_u : v u = v' u + tx.treeSize v' := by
    rw [htx_sz_eq]; simp [h_v_gen u]
  have hatt_phi := SplayState.attachRight_treePhi_eq hv_Lu hv_tx hv_u
  have hphi_eq : sumTreePhi P st' = sumTreePhi P st := by
    rw [hPhi_new, hPhi_old]
    have hsum_old : sumTreePhiList v trees =
        (AuxTree.node u Lu .leaf).treePhi v + tx.treePhi v +
          sumTreePhiList v ((trees.erase (.node u Lu .leaf)).erase tx) := by
      dsimp only [sumTreePhiList]
      rw [(hperm_two.map _).sum_eq]
      simp only [List.map_cons, List.sum_cons]; omega
    have hsum_new : sumTreePhiList v' trees' =
        t_new.treePhi v' + sumTreePhiList v' ((trees.erase (.node u Lu .leaf)).erase tx) := by
      dsimp only [sumTreePhiList, trees']
      simp only [List.map_cons, List.sum_cons]
    have hsum_er_eq : sumTreePhiList v' ((trees.erase (.node u Lu .leaf)).erase tx) =
        sumTreePhiList v ((trees.erase (.node u Lu .leaf)).erase tx) := by
      dsimp only [sumTreePhiList]
      congr 1
      refine List.map_congr_left (fun a ha => SplayState.treePhi_agree (fun w hw => ?_))
      have huw : u ≠ w := fun h => hdisj_er2 w (List.mem_flatMap.mpr ⟨a, ha, hw⟩)
        (h ▸ by simp [t_new, AuxTree.toList])
      simp [h_v_gen w, beq_false_of_ne huw]
    rw [hsum_new, hsum_old, hatt_phi.2, hsum_er_eq]
  have htnew_heavy : isHeavyEdge P s' active' (inducedSubPar P s' trees') t_new =
      isHeavyEdge P st.splay active par (.node u Lu .leaf) := by
    simp only [isHeavyEdge, t_new, AuxTree.rootId, hu_pp', hids_tnew_head, hrep_eq]; rfl
  have hheavy_eq : heavyCount P st' +
      (if isHeavyEdge P st.splay active par tx then 1 else 0) = heavyCount P st := by
    have hlen_old : heavyCount P st =
        (if isHeavyEdge P st.splay active par (.node u Lu .leaf) then 1 else 0) +
        ((if isHeavyEdge P st.splay active par tx then 1 else 0) +
        (((trees.erase (.node u Lu .leaf)).erase tx).filter
          (isHeavyEdge P st.splay active par)).length) := by
      rw [hH_old]
      dsimp only [heavyCountList]
      rw [(hperm_two.filter _).length_eq, filter_cons_length, filter_cons_length]
    have hfilt_er : ((trees.erase (.node u Lu .leaf)).erase tx).filter
        (isHeavyEdge P s' active' (inducedSubPar P s' trees')) =
        ((trees.erase (.node u Lu .leaf)).erase tx).filter
          (isHeavyEdge P st.splay active par) := by
      refine List.filter_congr (fun a ha => ?_)
      have ha' := h_er_agree a ha
      simp only [isHeavyEdge, ha'.1, ha'.2, hrep_eq]
    have hlen_new : heavyCount P st' =
        (if isHeavyEdge P s' active' (inducedSubPar P s' trees') t_new then 1 else 0) +
        (((trees.erase (.node u Lu .leaf)).erase tx).filter
          (isHeavyEdge P s' active' (inducedSubPar P s' trees'))).length := by
      rw [hH_new]
      dsimp only [heavyCountList]
      change (((t_new :: ((trees.erase (.node u Lu .leaf)).erase tx)).filter
        (isHeavyEdge P s' active' (inducedSubPar P s' trees'))).length) = _
      rw [filter_cons_length]
    rw [hlen_new, hlen_old, htnew_heavy, hfilt_er]
    omega
  exact ⟨hW', hphi_eq, hheavy_eq, hpar_eq⟩

/-! ### Combined heavy-light step (`exposeStep`: `detachRight` then optional `attachRight`) -/

/-- If `prev` (dashed child of `x`) is heavy BEFORE `detachRight x` and `attachRight x prev`,
then `R` (detached from `x`) is NOT heavy, so `heavyCount` strictly drops by `1`!
And if `prev` is light, `heavyCount` grows by at most `1` and `2 * prev.treeSize v_old ≤ repSize x`. -/
theorem exposeStep_heavy_light {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {x : ℕ} {L R prev : AuxTree}
    (ht : AuxTree.node x L R ∈ trees) (hprev : prev ∈ trees)
    (hne : AuxTree.node x L R ≠ prev)
    (hrev : (st.splay.nodes x).rev = false)
    (htag : (st.splay.nodes x).tag = P.idTag)
    (hpp : (st.splay.nodes prev.rootId).ppar = x) :
    let s1 := SplayState.detachRight P st.splay x
    let st1 : LctState α σ τ := { st with splay := s1 }
    let s2 := SplayState.attachRight P s1 x prev.rootId
    let st2 : LctState α σ τ := { st1 with splay := s2 }
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    let t_new := AuxTree.node x L prev
    let trees_base := if R = .leaf then trees else AuxTree.node x L .leaf :: R :: trees.erase (.node x L R)
    let trees2 := t_new :: ((trees_base.erase (.node x L .leaf)).erase prev)
    LctInvWith P st2 trees2 freeList depth ∧
    sumTreePhi P st2 = sumTreePhi P st ∧
    (isHeavyEdge P st.splay active par prev = true →
      heavyCount P st2 + 1 = heavyCount P st) ∧
    (isHeavyEdge P st.splay active par prev = false →
      heavyCount P st2 ≤ heavyCount P st + 1 ∧
      2 * prev.treeSize v ≤ repSize active par x) ∧
    ∀ z, inducedSubPar P s2 trees2 z = par z := by
  intro s1 st1 s2 st2 active par v t_new trees_base trees2
  rcases detachRight_spec hL W ht hrev htag with
    ⟨W1, hPhi1, hH1_leaf, hH1_ne, hH1_le, hpar1⟩
  have hx_mem : x ∈ trees.flatMap AuxTree.toList :=
    List.mem_flatMap.mpr ⟨_, ht, by simp [AuxTree.toList]⟩
  have hx_nz : x ≠ 0 := by have := W.activeValid x hx_mem; simp [isNode] at this; omega
  have hprev_disj := erase_flatMap_disjoint_of_nodup ht W.activeNodup
  have hprev_in_er : prev ∈ trees.erase (.node x L R) :=
    (List.mem_erase_of_ne hne.symm).mpr hprev
  have hprev_in_1 : prev ∈ trees_base := by
    cases hRc : R with
    | leaf => subst hRc; simp [trees_base, hprev]
    | node rid rL rR => subst hRc; simp [trees_base, hprev_in_er]
  have htu_in_1 : AuxTree.node x L .leaf ∈ trees_base := by
    cases hRc : R with
    | leaf => subst hRc; simp [trees_base, ht]
    | node rid rL rR => subst hRc; simp [trees_base]
  have hne1 : AuxTree.node x L .leaf ≠ prev := by
    intro h
    have hx_in_prev : x ∈ prev.toList := h ▸ by simp [AuxTree.toList]
    exact hprev_disj x (List.mem_flatMap.mpr ⟨prev, hprev_in_er, hx_in_prev⟩)
      (by simp [AuxTree.toList])
  have hdet := SplayState.detachRight_preserves hL (W.treesInv _ ht) hrev htag
  rcases hdet with ⟨_, hrev1, htag1, _, _, _, hR_spec1, hout1⟩
  have hpp1 : (s1.nodes prev.rootId).ppar = x := by
    have hnin : prev.rootId ∉ (AuxTree.node x L R).toList := fun hm =>
      hprev_disj prev.rootId (List.mem_flatMap.mpr ⟨prev, hprev_in_er,
        AuxTree.rootId_mem (W.treesNonEmpty prev hprev)⟩) hm
    rw [hout1 prev.rootId hnin, hpp]
  have hprev_agree : ∀ u ∈ prev.toList, s1.nodes u = st.splay.nodes u := fun u hu =>
    hout1 u (fun hm => hprev_disj u (List.mem_flatMap.mpr ⟨prev, hprev_in_er, hu⟩) hm)
  rcases attachRight_spec hL W1 htu_in_1 hprev_in_1 hne1 hrev1 htag1 hpp1 with
    ⟨W2, hPhi2, hH2, hpar2⟩
  have hpar2_fun : ∀ z, inducedSubPar P s2 trees2 z = par z := fun z =>
    (hpar2 z).trans (hpar1 z)
  have hact1_perm : (trees_base.flatMap AuxTree.toList).Perm active := by
    cases hRc : R with
    | leaf => subst hRc; simp [trees_base]; exact List.Perm.refl _
    | node rid rL rR =>
        subst hRc
        have htb : trees_base =
            AuxTree.node x L .leaf :: AuxTree.node rid rL rR ::
              trees.erase (.node x L (.node rid rL rR)) := by
          simp [trees_base]
        have h1 : active.Perm
            (((.node x L (.node rid rL rR)) :: trees.erase (.node x L (.node rid rL rR))).flatMap
              AuxTree.toList) :=
          (List.perm_cons_erase ht).flatMap (fun _ _ => List.Perm.refl _)
        refine List.Perm.trans ?_ h1.symm
        rw [htb]
        simp only [List.flatMap_cons]
        rw [← List.append_assoc (AuxTree.node x L .leaf).toList]
        refine List.Perm.append_right _ ?_
        simp [AuxTree.toList, List.append_assoc]
  have hrep1 : ∀ y, repSize (trees_base.flatMap AuxTree.toList)
      (inducedSubPar P s1 trees_base) y = repSize active par y := by
    intro y
    dsimp only [repSize]
    rw [funext hpar1, hact1_perm.length_eq]
    exact (hact1_perm.filter _).length_eq
  have hheavy_prev_eq :
      isHeavyEdge P s1 (trees_base.flatMap AuxTree.toList) (inducedSubPar P s1 trees_base) prev =
      isHeavyEdge P st.splay active par prev := by
    simp only [isHeavyEdge, hpp1, hpp, hrep1, treeIds_agree hprev_agree]
  rw [hheavy_prev_eq] at hH2
  have hH2' : heavyCount P st2 +
      (if isHeavyEdge P st.splay active par prev then 1 else 0) = heavyCount P st1 := hH2
  have hprev_head_mem : listHead0 (treeIds P st.splay prev) ∈ active :=
    List.mem_flatMap.mpr ⟨prev, hprev, listHead0_mem_treeIds (W.treesNonEmpty prev hprev)⟩
  have hprev_head_par : par (listHead0 (treeIds P st.splay prev)) = x := by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup hprev (listHead0_mem_treeIds (W.treesNonEmpty prev hprev))]
    cases hids : treeIds P st.splay prev with
    | nil => exact absurd hids (treeIds_ne_nil (W.treesNonEmpty prev hprev))
    | cons a rest => simp [listHead0, chainPred_head, hpp]
  have hx_bne : (x != 0) = true := bne_iff_ne.mpr hx_nz
  refine ⟨W2, hPhi2.trans hPhi1, ?_, ?_, hpar2_fun⟩
  · intro hp_heavy
    simp only [hp_heavy, ↓reduceIte] at hH2'
    cases hRc : R with
    | leaf =>
        have hH1_leaf' : heavyCount P st1 = heavyCount P st := hH1_leaf hRc
        omega
    | node rid rL rR =>
        subst hRc
        have hR_ne : AuxTree.node rid rL rR ≠ .leaf := by simp
        have h1 : heavyCount P st1 = heavyCount P st +
            (if isHeavyEdge P s1 (trees_base.flatMap AuxTree.toList)
              (inducedSubPar P s1 trees_base) (.node rid rL rR) then 1 else 0) :=
          hH1_ne hR_ne
        have hR_mem_1 : AuxTree.node rid rL rR ∈ trees_base := by simp [trees_base]
        have hR_hd_mem := listHead0_mem_treeIds (P := P) (s := s1) hR_ne
        have hprev_hd_mem := listHead0_mem_treeIds (P := P) (s := st.splay) (W.treesNonEmpty prev hprev)
        have hR_hd_ne : listHead0 (treeIds P s1 (.node rid rL rR)) ≠
            listHead0 (treeIds P st.splay prev) := by
          intro h
          have h1m_orig : listHead0 (treeIds P s1 (.node rid rL rR)) ∈
              (AuxTree.node x L (.node rid rL rR)).toList := by
            change _ ∈ L.toList ++ [x] ++ (AuxTree.node rid rL rR).toList
            exact List.mem_append_right _ hR_hd_mem
          exact hprev_disj _ (List.mem_flatMap.mpr ⟨prev, hprev_in_er, h ▸ hprev_hd_mem⟩) h1m_orig
        rcases hR_spec1 hR_ne with ⟨_, hR_pp1, _⟩
        have hR_hd_par1 : inducedSubPar P s1 trees_base
            (listHead0 (treeIds P s1 (.node rid rL rR))) = x := by
          rw [inducedSubPar_eq_of_mem W1.activeNodup hR_mem_1 hR_hd_mem]
          cases hids : treeIds P s1 (.node rid rL rR) with
          | nil => exact absurd hids (treeIds_ne_nil hR_ne)
          | cons a rest => simpa [listHead0, chainPred_head, AuxTree.rootId] using hR_pp1
        have hR_hd_act : listHead0 (treeIds P s1 (.node rid rL rR)) ∈ active := by
          have h_in_orig : listHead0 (treeIds P s1 (.node rid rL rR)) ∈
              (AuxTree.node x L (.node rid rL rR)).toList := by
            change _ ∈ L.toList ++ [x] ++ (AuxTree.node rid rL rR).toList
            exact List.mem_append_right _ hR_hd_mem
          exact List.mem_flatMap.mpr ⟨_, ht, h_in_orig⟩
        have htwo : 1 + repSize active par (listHead0 (treeIds P st.splay prev)) +
            repSize active par (listHead0 (treeIds P s1 (.node rid rL rR))) ≤ repSize active par x :=
          repSize_ge_one_add_two_children W.activeNodup
            (fun y hy hp => W.subPar_mem_active hy hp) W.acyclic hx_mem hx_nz
            hprev_head_mem hR_hd_act hprev_head_par
            ((hpar1 _).symm.trans hR_hd_par1) hR_hd_ne.symm
        dsimp only [isHeavyEdge] at hp_heavy
        simp only [hpp, hx_bne, Bool.true_and, decide_eq_true_eq] at hp_heavy
        have hR_pp1' : (s1.nodes (AuxTree.node rid rL rR).rootId).ppar = x := hR_pp1
        have hR_not_heavy : isHeavyEdge P s1 (trees_base.flatMap AuxTree.toList)
            (inducedSubPar P s1 trees_base) (.node rid rL rR) = false := by
          dsimp only [isHeavyEdge]
          simp only [hR_pp1', hrep1, hx_bne, Bool.true_and,
            decide_eq_false_iff_not, not_lt]
          omega
        simp only [hR_not_heavy, Bool.false_eq_true, ↓reduceIte, add_zero] at h1
        omega
  · intro hp_light
    simp only [hp_light, Bool.false_eq_true, ↓reduceIte, add_zero] at hH2'
    have hH1_le' : heavyCount P st1 ≤ heavyCount P st + 1 := hH1_le
    refine ⟨by omega, ?_⟩
    rw [treeSize_vSize_eq_repSize W hprev]
    simp only [isHeavyEdge, hpp, hx_bne, Bool.true_and,
      decide_eq_false_iff_not, not_lt] at hp_light
    exact hp_light

end MinCostFlow.LinkCut
