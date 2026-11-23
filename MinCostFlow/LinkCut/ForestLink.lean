module

public import MinCostFlow.LinkCut.ForestCutLink
import Mathlib.Tactic

/-!
# Invariant and Potential Lemma for `link` Splices

This file proves `link_splice_spec`: popping a free edge slot `ne` to join two distinct root
auxiliary trees `tu` and `tv` (with `tv.rootId` a vertex) preserves `LctInvWith` with an explicit
shifted `depth`, increases `sumTreePhi` by at most `2 * Nat.log 2 (2 * st.n + 1)`, and increases
`heavyCount` by at most `2`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### `link_splice_spec`: joining two distinct root auxiliary trees `tu` and `tv` via `ne` -/

theorem link_splice_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {ne : ℕ} {freeRest : List ℕ} (hfl : freeList = ne :: freeRest)
    {tu tv : AuxTree} (htu : tu ∈ trees) (htv : tv ∈ trees) (hne : tu ≠ tv)
    (hpu0 : (st.splay.nodes tu.rootId).ppar = 0)
    (hpv0 : (st.splay.nodes tv.rootId).ppar = 0)
    (htv_v : isVertex st.n tv.rootId)
    (eVal : α) :
    let nextFree := (st.splay.nodes ne).par
    let s1 := SplayState.makeSingleton P st.splay ne eVal tv.rootId
    let s2 := s1.setPpar tu.rootId ne
    let st' : LctState α σ τ := { n := st.n, splay := s2, freeHead := nextFree }
    let trees' := AuxTree.node ne .leaf .leaf :: trees
    let u_head := listHead0 (treeIds P st.splay tu)
    ∃ depth' : ℕ → ℕ,
      LctInvWith P st' trees' freeRest depth' ∧
      sumTreePhi P st' ≤ sumTreePhi P st + 2 * Nat.log 2 (2 * st.n + 1) ∧
      heavyCount P st' ≤ heavyCount P st + 2 ∧
      inducedSubPar P s2 trees' u_head = ne ∧
      inducedSubPar P s2 trees' ne = tv.rootId ∧
      ∀ z ≠ u_head, z ≠ ne → inducedSubPar P s2 trees' z = inducedSubPar P st.splay trees z := by
  intro nextFree s1 s2 st' trees' u_head
  let rv := tv.rootId
  let active := trees.flatMap AuxTree.toList
  let active' := trees'.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  let par' := inducedSubPar P s2 trees'
  let tne := AuxTree.node ne .leaf .leaf
  have hfl_unfold : ne ≠ 0 ∧ st.freeHead = ne ∧ FreeListInv st.splay nextFree freeRest := by
    have hfl0 : FreeListInv st.splay st.freeHead (ne :: freeRest) := hfl ▸ W.freeListInv
    rcases hfl0 with ⟨hnz, hfh, hrest⟩
    refine ⟨by rw [← hfh]; exact hnz, hfh, ?_⟩
    simpa [nextFree, hfh] using hrest
  have hne_slot : isEdgeSlot st.n ne := W.freeValid ne (by simp [hfl])
  have hne_nin_act : ne ∉ active := fun hm =>
    ((W.partitionSlots ne hne_slot).mp hm) (by simp [hfl])
  have hne_nz : ne ≠ 0 := hfl_unfold.1
  have hru_mem : tu.rootId ∈ tu.toList := AuxTree.rootId_mem (W.treesNonEmpty tu htu)
  have hru_act : tu.rootId ∈ active := List.mem_flatMap.mpr ⟨tu, htu, hru_mem⟩
  have hru_ne : tu.rootId ≠ ne := fun h => hne_nin_act (h ▸ hru_act)
  have hrv_mem : rv ∈ tv.toList := AuxTree.rootId_mem (W.treesNonEmpty tv htv)
  have hrv_act : rv ∈ active := List.mem_flatMap.mpr ⟨tv, htv, hrv_mem⟩
  have hrv_ne : rv ≠ ne := fun h => hne_nin_act (h ▸ hrv_act)
  have hru_nin_tv : tu.rootId ∉ tv.toList := fun hm =>
    hne (flatMap_mem_unique W.activeNodup htu htv hru_mem hm)
  have ht_ne_inv1 := SplayState.makeSingleton_treeInv hL st.splay hne_nz eVal rv
  rcases ht_ne_inv1 with ⟨htne_1, hpp_ne1, _, _, _, hout_s1⟩
  have htu_inv1 : SplayState.TreeInv P s1 tu :=
    SplayState.TreeInv_agree (W.treesInv tu htu) (fun w hw =>
      (hout_s1 w (fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tu, htu, hw⟩))).symm)
  have htu_s2 := SplayState.setPpar_root_preserves P htu_inv1 (W.treesNonEmpty tu htu) (pp := ne)
  rcases htu_s2 with ⟨htu_inv2, hev_tu2, hpp_tu2, hout_s2⟩
  have hev_tu2' : SplayState.evalPairs P s2 tu false P.idTag =
      SplayState.evalPairs P s1 tu false P.idTag := hev_tu2
  have hpp_tu2' : (s2.nodes tu.rootId).ppar = ne := hpp_tu2
  have htne_inv2 : SplayState.TreeInv P s2 tne :=
    SplayState.TreeInv_agree htne_1 (fun w hw => by
      have hwne : w = ne := by simpa [tne, AuxTree.toList] using hw
      exact (hout_s2 w (hwne ▸ hru_ne.symm)).symm)
  have hpp_ne2 : (s2.nodes ne).ppar = rv := by
    rw [hout_s2 ne hru_ne.symm]; exact hpp_ne1
  have hout2 : ∀ w ∈ active, w ≠ tu.rootId → s2.nodes w = st.splay.nodes w := fun w hw hwru => by
    have hwne : w ≠ ne := fun h => hne_nin_act (h ▸ hw)
    exact (hout_s2 w hwru).trans (hout_s1 w hwne)
  have hact'_eq : active' = ne :: active := by
    simp [active', trees', AuxTree.toList, active]
  have hact'_mem : trees'.flatMap AuxTree.toList = ne :: active := hact'_eq
  have hact'_nd : active'.Nodup := by
    rw [hact'_eq]
    exact List.nodup_cons.mpr ⟨hne_nin_act, W.activeNodup⟩
  have hhead_mem : u_head ∈ tu.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty tu htu)
  have hhead_act : u_head ∈ active := List.mem_flatMap.mpr ⟨tu, htu, hhead_mem⟩
  have hhead_nin_tv : u_head ∉ tv.toList := fun hm =>
    hne (flatMap_mem_unique W.activeNodup htu htv hhead_mem hm)
  have hhead_ne : u_head ≠ ne := fun h => hne_nin_act (h ▸ hhead_act)
  have hpar_head_old : par u_head = 0 := by
    dsimp only [par]
    rw [inducedSubPar_eq_of_mem W.activeNodup htu hhead_mem]
    cases hids_u : treeIds P st.splay tu with
    | nil => exact absurd hids_u (treeIds_ne_nil (W.treesNonEmpty tu htu))
    | cons _ _ =>
        dsimp only [u_head]
        rw [hids_u]
        simp [listHead0, chainPred_head, hpu0]
  have hu_head_v : isVertex st.n u_head := isVertex_of_par_zero W hhead_act hpar_head_old
  have hpar'_ne : par' ne = rv := by
    dsimp only [par']
    rw [inducedSubPar_eq_of_mem hact'_nd (t := tne) List.mem_cons_self (by simp [tne, AuxTree.toList])]
    simp [tne, treeIds_singleton, AuxTree.rootId, hpp_ne2, chainPred]
  have hids_tu2 : treeIds P s2 tu = treeIds P st.splay tu := by
    have h1 : SplayState.evalPairs P s1 tu false P.idTag =
        SplayState.evalPairs P st.splay tu false P.idTag :=
      SplayState.evalPairs_agree P (fun w hw =>
        hout_s1 w (fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tu, htu, hw⟩))) false P.idTag
    simp only [treeIds, hev_tu2', h1]
  have hpar'_head : par' u_head = ne := by
    dsimp only [par']
    rw [inducedSubPar_eq_of_mem hact'_nd (t := tu) (by simp [trees', htu]) hhead_mem, hids_tu2]
    cases hids_u : treeIds P st.splay tu with
    | nil => exact absurd hids_u (treeIds_ne_nil (W.treesNonEmpty tu htu))
    | cons _ _ =>
        dsimp only [u_head]
        rw [hids_u]
        simp [listHead0, chainPred_head, hpp_tu2']
  have hpar'_out : ∀ z, z ≠ u_head → z ≠ ne → par' z = par z := by
    intro z hz_u hz_ne
    dsimp only [par', par]
    by_cases hz_act : z ∈ active
    · by_cases hz_tu : z ∈ tu.toList
      · rw [inducedSubPar_eq_of_mem hact'_nd (t := tu) (by simp [trees', htu]) hz_tu,
          inducedSubPar_eq_of_mem W.activeNodup htu hz_tu, hids_tu2, hpp_tu2, hpu0]
        cases hids_u : treeIds P st.splay tu with
        | nil => exact absurd hids_u (treeIds_ne_nil (W.treesNonEmpty tu htu))
        | cons a rest =>
            have hza : z ≠ a := by
              dsimp only [u_head] at hz_u
              rw [hids_u] at hz_u
              simpa [listHead0] using hz_u
            simp [chainPred, hza]
      · rcases List.mem_flatMap.mp hz_act with ⟨c, hc_ts, hzc⟩
        have hc_ne_tu : c ≠ tu := fun h => hz_tu (h ▸ hzc)
        have htu_disj := erase_flatMap_disjoint_of_nodup htu W.activeNodup
        have hru_nin_c : tu.rootId ∉ c.toList := fun hm =>
          htu_disj tu.rootId (List.mem_flatMap.mpr ⟨c, (List.mem_erase_of_ne hc_ne_tu).mpr hc_ts, hm⟩)
            hru_mem
        have hag_c : ∀ w ∈ c.toList, s2.nodes w = st.splay.nodes w := fun w hw =>
          hout2 w (List.mem_flatMap.mpr ⟨c, hc_ts, hw⟩) (fun h => hru_nin_c (h ▸ hw))
        rw [inducedSubPar_eq_of_mem hact'_nd (t := c) (by simp [trees', hc_ts]) hzc,
          inducedSubPar_eq_of_mem W.activeNodup hc_ts hzc, treeIds_agree hag_c,
          hag_c c.rootId (AuxTree.rootId_mem (W.treesNonEmpty c hc_ts))]
    · have hz_nact' : z ∉ active' := by rw [hact'_eq]; simp [hz_ne, hz_act]
      rw [inducedSubPar_eq_zero_of_not_mem hz_nact', inducedSubPar_eq_zero_of_not_mem hz_act]
  have hsubpar'_mem : ∀ z ∈ active', par' z ≠ 0 → par' z ∈ active' := by
    intro z hz hpz
    by_cases hzu : z = u_head
    · subst hzu; rw [hpar'_head, hact'_eq]; exact List.mem_cons_self
    · by_cases hzne : z = ne
      · subst hzne; rw [hpar'_ne, hact'_eq]; exact List.mem_cons_of_mem _ hrv_act
      · rw [hpar'_out z hzu hzne] at hpz ⊢
        have hz_act : z ∈ active := by
          rw [hact'_eq] at hz
          rcases List.mem_cons.mp hz with h | h
          · exact absurd h hzne
          · exact h
        rw [hact'_eq]
        exact List.mem_cons_of_mem _ (W.subPar_mem_active hz_act hpz)
  let M := depth rv + 2
  let depth' : ℕ → ℕ := fun z =>
    if z = ne then depth rv + 1
    else if reaches par active.length u_head z then depth z + M
    else depth z
  have hrv_no_reach : reaches par active.length u_head rv = false := by
    have hclosed_tv : ∀ x ∈ tv.toList, par x = 0 ∨ par x ∈ tv.toList := fun x hx => by
      dsimp only [par]
      rw [inducedSubPar_eq_of_mem W.activeNodup htv hx, hpv0]
      rcases chainPred_mem_or_prev ((mem_treeIds_iff P st.splay tv x).mpr hx) with h | h
      · exact Or.inl h
      · exact Or.inr ((mem_treeIds_iff P st.splay tv _).mp h)
    have hreach_tv_only : ∀ k x, x ∈ tv.toList → reaches par k u_head x = false := by
      intro k
      induction k with
      | zero =>
          intro x hx
          simp [reaches, show x ≠ u_head from fun h => hhead_nin_tv (h ▸ hx)]
      | succ k ih =>
          intro x hx
          have hxu : x ≠ u_head := fun h => hhead_nin_tv (h ▸ hx)
          rcases hclosed_tv x hx with hp0 | hptv
          · simp [reaches, hxu, hp0]
          · simp only [reaches, beq_iff_eq, hxu, ↓reduceIte]
            by_cases hz : par x = 0
            · simp [hz]
            · simp [hz, ih (par x) hptv]
    exact hreach_tv_only active.length rv hrv_mem
  have hacyc' : ∀ z ∈ active', par' z ≠ 0 → depth' (par' z) < depth' z := by
    intro z hz hpz
    by_cases hzu : z = u_head
    · subst hzu
      rw [hpar'_head]
      have hru_self : reaches par active.length u_head u_head = true := reaches_self par _ _
      simp only [depth', hhead_ne, ↓reduceIte, hru_self]
      dsimp only [M]; omega
    · by_cases hzne : z = ne
      · subst hzne
        rw [hpar'_ne]
        simp only [depth', hrv_ne, ↓reduceIte, hrv_no_reach, Bool.false_eq_true]
        omega
      · have hz_act : z ∈ active := by
          rw [hact'_eq] at hz
          rcases List.mem_cons.mp hz with h | h
          · exact absurd h hzne
          · exact h
        rw [hpar'_out z hzu hzne] at hpz ⊢
        have hpnz : par z ≠ 0 := hpz
        have hp_act : par z ∈ active := W.subPar_mem_active hz_act hpnz
        have hp_ne : par z ≠ ne := fun h => hne_nin_act (h ▸ hp_act)
        have hd_lt : depth (par z) < depth z := W.acyclic z hz_act hpnz
        have hstep := reaches_step_iff W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp)
          W.acyclic (u := u_head) hz_act
        have hreach_eq : reaches par active.length u_head z =
            reaches par active.length u_head (par z) :=
          Bool.eq_iff_iff.mpr ⟨fun hr => (hstep.mp hr).elim (fun h => absurd h hzu) And.right,
            fun hr => hstep.mpr (Or.inr ⟨hpnz, hr⟩)⟩
        by_cases hrz : reaches par active.length u_head z = true
        · have hrp : reaches par active.length u_head (par z) = true := hreach_eq ▸ hrz
          simp only [depth', hzne, hp_ne, ↓reduceIte, hrz, hrp]
          dsimp only [M]
          omega
        · have hrp : reaches par active.length u_head (par z) = false := by
            rw [← hreach_eq]; cases hc : reaches par active.length u_head z <;> simp_all
          simp only [depth', hzne, hp_ne, ↓reduceIte, hrz, hrp, Bool.false_eq_true]
          exact hd_lt
  have hne_nin_fl_rest : ne ∉ freeRest := fun hm =>
    (List.nodup_cons.mp (hfl ▸ W.freeNodup)).1 hm
  have hfl' : FreeListInv s2 nextFree freeRest :=
    FreeListInv_agree hfl_unfold.2.2 (fun e he => by
      have he_mem_fl : e ∈ freeList := by simp [hfl, he]
      have he_nin_act := W.active_of_freeList_disjoint he_mem_fl
      have he_ne : e ≠ ne := fun h => hne_nin_fl_rest (h ▸ he)
      have he_ru : e ≠ tu.rootId := fun h => he_nin_act (h ▸ hru_act)
      rw [hout_s2 e he_ru, hout_s1 e he_ne])
  have hW' : LctInvWith P st' trees' freeRest depth' :=
    { treesNonEmpty := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc'
        · simp
        · exact W.treesNonEmpty c hc'
      treesInv := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact htne_inv2
        · by_cases hct : c = tu
          · subst hct; exact htu_inv2
          · have hru_nin_c : tu.rootId ∉ c.toList := fun hm =>
              hct (flatMap_mem_unique W.activeNodup htu hc' hru_mem hm).symm
            exact SplayState.TreeInv_agree (W.treesInv c hc') (fun w hw =>
              (hout2 w (List.mem_flatMap.mpr ⟨c, hc', hw⟩) (fun h => hru_nin_c (h ▸ hw))).symm)
      activeNodup := hact'_nd
      activeValid := fun z hz => by
        rw [hact'_mem] at hz
        rcases List.mem_cons.mp hz with rfl | hz_act
        · exact ⟨by simp [isEdgeSlot] at hne_slot; omega, hne_slot.2⟩
        · exact W.activeValid z hz_act
      verticesActive := fun v hv => by
        rw [hact'_mem]
        exact List.mem_cons_of_mem _ (W.verticesActive v hv)
      freeNodup := (List.nodup_cons.mp (hfl ▸ W.freeNodup)).2
      freeValid := fun e he => W.freeValid e (by simp [hfl, he])
      partitionSlots := fun e he => by
        constructor
        · intro he_act'
          rw [hact'_mem] at he_act'
          rcases List.mem_cons.mp he_act' with rfl | he_act
          · exact hne_nin_fl_rest
          · intro hfr
            exact (W.partitionSlots e he).mp he_act (by simp [hfl, hfr])
        · intro hn_fr
          by_cases hene : e = ne
          · subst hene; rw [hact'_mem]; exact List.mem_cons_self
          · rw [hact'_mem]
            exact List.mem_cons_of_mem _ ((W.partitionSlots e he).mpr (by simp [hfl, hn_fr, hene]))
      freeListInv := hfl'
      pparActive := fun c hc hp => by
        dsimp only [st'] at hp ⊢
        rw [hact'_mem]
        rcases List.mem_cons.mp hc with rfl | hc'
        · simp only [AuxTree.rootId] at hp ⊢
          rw [hpp_ne2]; exact List.mem_cons_of_mem _ hrv_act
        · by_cases hct : c = tu
          · subst hct
            rw [hpp_tu2]
            exact List.mem_cons_self
          · have hc_rt_mem : c.rootId ∈ c.toList := AuxTree.rootId_mem (W.treesNonEmpty c hc')
            have hru_nc : tu.rootId ≠ c.rootId := fun h =>
              hct (flatMap_mem_unique W.activeNodup htu hc' hru_mem (h ▸ hc_rt_mem)).symm
            have hrt_eq := hout2 c.rootId (List.mem_flatMap.mpr ⟨c, hc', hc_rt_mem⟩) hru_nc.symm
            rw [hrt_eq] at hp ⊢
            exact List.mem_cons_of_mem _ (W.pparActive c hc' hp)
      acyclic := hacyc'
      vertexParEdge := fun u huv hpu => by
        dsimp only [st'] at huv ⊢
        change par' u ≠ 0 at hpu
        change isEdgeSlot st.n (par' u)
        by_cases hzu : u = u_head
        · subst hzu; rw [hpar'_head]; exact hne_slot
        · by_cases hzne : u = ne
          · subst hzne; simp only [isVertex] at huv; simp only [isEdgeSlot] at hne_slot; omega
          · rw [hpar'_out u hzu hzne] at hpu ⊢; exact W.vertexParEdge u huv hpu
      edgeParVertex := fun e he hes => by
        dsimp only [st'] at hes ⊢
        change par' e ≠ 0 ∧ isVertex st.n (par' e)
        by_cases hzu : e = u_head
        · subst hzu; simp only [isVertex] at hu_head_v; simp only [isEdgeSlot] at hes; omega
        · by_cases hzne : e = ne
          · rw [hzne, hpar'_ne]
            exact ⟨by simp [isVertex] at htv_v; omega, htv_v⟩
          · have he_act : e ∈ active := by
              rw [hact'_mem] at he
              rcases List.mem_cons.mp he with h | h
              · exact absurd h hzne
              · exact h
            rw [hpar'_out e hzu hzne]
            exact W.edgeParVertex e he_act hes
      edgeUniqueChild := fun e he hes => by
        dsimp only [st'] at hes ⊢
        have hzu : e ≠ u_head := fun h => by
          subst h; simp only [isVertex] at hu_head_v; simp only [isEdgeSlot] at hes; omega
        by_cases hzne : e = ne
        · rw [hzne]
          refine ⟨u_head, ⟨by rw [hact'_mem]; exact List.mem_cons_of_mem _ hhead_act,
            hpar'_head, hu_head_v, ?_⟩, ?_⟩
          · change u_head ≠ par' ne
            rw [hpar'_ne]
            exact fun h => hhead_nin_tv (h ▸ hrv_mem)
          · intro y ⟨hy_act', hpy, hy_v, hy_ne⟩
            by_cases hyu : y = u_head
            · exact hyu
            · have hy_nne : y ≠ ne := fun h => by
                subst h; simp only [isVertex] at hy_v; simp only [isEdgeSlot] at hne_slot; omega
              change par' y = ne at hpy
              rw [hpar'_out y hyu hy_nne] at hpy
              have hy_act : y ∈ active := by
                rw [hact'_mem] at hy_act'
                rcases List.mem_cons.mp hy_act' with h | h
                · exact absurd h hy_nne
                · exact h
              have hpy_act : par y ∈ active := W.subPar_mem_active hy_act (by change par y ≠ 0; rw [hpy]; exact hne_nz)
              rw [hpy] at hpy_act
              exact absurd hpy_act hne_nin_act
        · have he_act : e ∈ active := by
            rw [hact'_mem] at he
            rcases List.mem_cons.mp he with h | h
            · exact absurd h hzne
            · exact h
          rcases W.edgeUniqueChild e he_act hes with ⟨w₀, ⟨hw₀_act, hw₀_p, hw₀_v, hw₀_ne⟩, huniq⟩
          have hw₀_nu : w₀ ≠ u_head := fun h => by
            change par w₀ = e at hw₀_p
            rw [h, hpar_head_old] at hw₀_p
            simp only [isEdgeSlot] at hes; omega
          have hw₀_nne : w₀ ≠ ne := fun h => hne_nin_act (h ▸ hw₀_act)
          refine ⟨w₀, ⟨by rw [hact'_mem]; exact List.mem_cons_of_mem _ hw₀_act,
            (hpar'_out w₀ hw₀_nu hw₀_nne).trans hw₀_p, hw₀_v, ?_⟩, ?_⟩
          · change w₀ ≠ par' e; rw [hpar'_out e hzu hzne]; exact hw₀_ne
          · intro y ⟨hy_act', hpy, hy_v, hy_ne⟩
            have hy_nu : y ≠ u_head := fun h => by
              change par' y = e at hpy
              rw [h, hpar'_head] at hpy; exact hzne hpy.symm
            have hy_nne : y ≠ ne := fun h => by
              change par' y = e at hpy
              rw [h, hpar'_ne] at hpy
              simp only [isEdgeSlot] at hes; simp only [isVertex] at htv_v; omega
            have hy_act : y ∈ active := by
              rw [hact'_mem] at hy_act'
              rcases List.mem_cons.mp hy_act' with h | h
              · exact absurd h hy_nne
              · exact h
            change par' y = e at hpy
            rw [hpar'_out y hy_nu hy_nne] at hpy
            change y ≠ par' e at hy_ne
            rw [hpar'_out e hzu hzne] at hy_ne
            exact huniq y ⟨hy_act, hpy, hy_v, hy_ne⟩ }
  rcases LctInvWith_canon_potentials W with ⟨hH_old, hPhi_old⟩
  rcases LctInvWith_canon_potentials hW' with ⟨hH_new, hPhi_new⟩
  let S : List ℕ := u_head :: ne :: tv.toList
  have hS_par_cl : ∀ w ∈ S, par w = 0 ∨ par w ∈ S := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact Or.inl hpar_head_old
    · rcases List.mem_cons.mp hw' with rfl | hwtv
      · exact Or.inl (inducedSubPar_eq_zero_of_not_mem hne_nin_act)
      · dsimp only [par]
        rw [inducedSubPar_eq_of_mem W.activeNodup htv hwtv, hpv0]
        rcases chainPred_mem_or_prev ((mem_treeIds_iff P st.splay tv w).mpr hwtv) with h0 | htv_w
        · exact Or.inl h0
        · exact Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            ((mem_treeIds_iff P st.splay tv _).mp htv_w)))
  have hS_par'_cl : ∀ w ∈ S, par' w = 0 ∨ par' w ∈ S := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact Or.inr (by simp [S, hpar'_head])
    · rcases List.mem_cons.mp hw' with rfl | hwtv
      · exact Or.inr (by simp [S, hpar'_ne, hrv_mem])
      · have hwu : w ≠ u_head := fun h => hhead_nin_tv (h ▸ hwtv)
        have hwne : w ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tv, htv, hwtv⟩)
        rw [hpar'_out w hwu hwne]
        exact hS_par_cl w hw
  have hpar_eq_S : ∀ w ∉ S, par' w = par w := fun w hw =>
    hpar'_out w (fun h => hw (by simp [S, h])) (fun h => hw (by simp [S, h]))
  have hrep_out_S : ∀ u, u ∉ S → repSize active' par' u = repSize active par u := by
    intro u hu
    have hlen_le : active.length ≤ active'.length := by
      rw [hact'_eq]; simp
    have hne_false' : reaches par' active'.length u ne = false := by
      have hr := reaches_eq_of_not_mem_closed hpar_eq_S hS_par'_cl hS_par_cl hu active'.length ne
      rw [hr]
      cases hk : active'.length with
      | zero => simp [reaches, show ne ≠ u from fun h => hu (by simp [S, h])]
      | succ m =>
          have hpnz : par ne = 0 := inducedSubPar_eq_zero_of_not_mem hne_nin_act
          simp [reaches, show ne ≠ u from fun h => hu (by simp [S, h]), hpnz]
    have hfilt_eq : active.filter (fun w => reaches par' active'.length u w) =
        active.filter (fun w => reaches par active.length u w) := by
      refine List.filter_congr (fun w hw => ?_)
      have heq1 := reaches_eq_of_not_mem_closed hpar_eq_S hS_par'_cl hS_par_cl hu active'.length w
      have hstab := reaches_stable W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp)
        W.acyclic (u := u) hw hlen_le
      exact heq1.trans hstab
    dsimp only [repSize]
    rw [show active'.filter (fun x => reaches par' active'.length u x) =
        (ne :: active).filter (fun x => reaches par' active'.length u x) by rw [hact'_eq]]
    rw [List.filter_cons, hne_false']
    simp [hfilt_eq]
  have h_er_tu : ∀ c ∈ trees.erase tu,
      (s2.nodes c.rootId).ppar = (st.splay.nodes c.rootId).ppar ∧
      treeIds P s2 c = treeIds P st.splay c := by
    intro c hc_er
    have hc_ts := List.mem_of_mem_erase hc_er
    have htu_disj := erase_flatMap_disjoint_of_nodup htu W.activeNodup
    have hag : ∀ w ∈ c.toList, s2.nodes w = st.splay.nodes w := fun w hw =>
      hout2 w (List.mem_flatMap.mpr ⟨c, hc_ts, hw⟩)
        (fun h => htu_disj tu.rootId (List.mem_flatMap.mpr ⟨c, hc_er, h ▸ hw⟩) hru_mem)
    exact ⟨by rw [hag c.rootId (AuxTree.rootId_mem (W.treesNonEmpty c hc_ts))], treeIds_agree hag⟩
  have hrep_child : ∀ c ∈ trees, c ≠ tu → (st.splay.nodes c.rootId).ppar ≠ 0 →
      repSize active' par' (listHead0 (treeIds P st.splay c)) =
      repSize active par (listHead0 (treeIds P st.splay c)) := by
    intro c hc hc_tu hc_pp
    have hc_ne_tv : c ≠ tv := fun h => hc_pp (h ▸ hpv0)
    let hdc := listHead0 (treeIds P st.splay c)
    have hh_mem : hdc ∈ c.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty c hc)
    have hh_nin_tv : hdc ∉ tv.toList := fun hm =>
      hc_ne_tv (flatMap_mem_unique W.activeNodup hc htv hh_mem hm)
    have hh_ne : hdc ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨c, hc, hh_mem⟩)
    have hh_nu : hdc ≠ u_head := fun h =>
      hc_tu (flatMap_mem_unique W.activeNodup hc htu hh_mem (h ▸ hhead_mem))
    exact hrep_out_S hdc (by simp [S, hh_nu, hh_ne, hh_nin_tv])
  let v := vSize P st.splay active par trees
  let v' := vSize P s2 active' par' trees'
  have hperm_tu := List.perm_cons_erase htu
  have hv_eq_out : ∀ w, w ≠ 0 → w ≠ ne → w ≠ rv → v' w = v w := by
    intro w hw_nz hw_ne hw_rv
    dsimp only [v', v, vSize, trees']
    rw [filter_cons_map_sum, ((hperm_tu.filter _).map _).sum_eq, filter_cons_map_sum,
      ((hperm_tu.filter _).map _).sum_eq, filter_cons_map_sum]
    have hpp_tne_w : ((s2.nodes (AuxTree.node ne AuxTree.leaf AuxTree.leaf).rootId).ppar == w) = false := by
      simp [AuxTree.rootId, hpp_ne2, beq_false_of_ne (Ne.symm hw_rv)]
    have hpp_tu_new : ((s2.nodes tu.rootId).ppar == w) = false :=
      by rw [hpp_tu2']; exact beq_false_of_ne (Ne.symm hw_ne)
    have hpp_tu_old : ((st.splay.nodes tu.rootId).ppar == w) = false :=
      by rw [hpu0]; exact beq_false_of_ne (Ne.symm hw_nz)
    have hfilt_er : ((trees.erase tu).filter (fun c => (s2.nodes c.rootId).ppar == w)) =
        ((trees.erase tu).filter (fun c => (st.splay.nodes c.rootId).ppar == w)) :=
      List.filter_congr (fun c hc => by rw [(h_er_tu c hc).1])
    have hsum_er : (((trees.erase tu).filter (fun c => (s2.nodes c.rootId).ppar == w)).map
          (fun c => repSize active' par' (listHead0 (treeIds P s2 c)))).sum =
        (((trees.erase tu).filter (fun c => (st.splay.nodes c.rootId).ppar == w)).map
          (fun c => repSize active par (listHead0 (treeIds P st.splay c)))).sum := by
      rw [hfilt_er]
      congr 1
      refine List.map_congr_left (fun c hc => ?_)
      have hmem_f := List.mem_filter.mp hc
      have hc_er := hmem_f.1
      have hc_ts := List.mem_of_mem_erase hc_er
      have hc_tu : c ≠ tu := fun h => (List.nodup_cons.mp (hperm_tu.nodup_iff.mp
        (nodup_of_flatMap_nodup trees W.activeNodup W.treesNonEmpty))).1 (h ▸ hc_er)
      have hc_pp_nz : (st.splay.nodes c.rootId).ppar ≠ 0 := by
        have hp_w : (st.splay.nodes c.rootId).ppar = w := by simpa using hmem_f.2
        exact hp_w ▸ hw_nz
      rw [(h_er_tu c hc_er).2, hrep_child c hc_ts hc_tu hc_pp_nz]
    rw [hpp_tne_w, hpp_tu_new, hpp_tu_old, hsum_er]
    simp
  have hact'_len_le : active'.length ≤ 2 * st.n :=
    active_length_le_two_mul hact'_nd hW'.activeValid
  have hphi_le : sumTreePhi P st' ≤ sumTreePhi P st + 2 * Nat.log 2 (2 * st.n + 1) := by
    rw [hPhi_new, hPhi_old]
    have hperm_tv := List.perm_cons_erase htv
    have htu_in_er_tv : tu ∈ trees.erase tv :=
      (List.mem_erase_of_ne hne).mpr htu
    have hperm_both : trees.Perm (tv :: tu :: ((trees.erase tv).erase tu)) :=
      hperm_tv.trans (List.Perm.cons tv (List.perm_cons_erase htu_in_er_tv))
    let rest := (trees.erase tv).erase tu
    have hnd_both := hperm_both.nodup_iff.mp (nodup_of_flatMap_nodup trees W.activeNodup W.treesNonEmpty)
    have hrest_er_tu : ∀ c ∈ rest, c ∈ trees.erase tu := fun c hc => by
      have hc1 := List.mem_of_mem_erase hc
      have hcu : c ≠ tu := fun h =>
        (List.nodup_cons.mp (List.nodup_cons.mp hnd_both).2).1 ((congrArg (· ∈ rest) h).mp hc)
      exact (List.mem_erase_of_ne hcu).mpr (List.mem_of_mem_erase hc1)
    have hsum_old : sumTreePhiList v trees =
        tv.treePhi v + (tu.treePhi v + sumTreePhiList v rest) := by
      dsimp only [sumTreePhiList]
      rw [(hperm_both.map _).sum_eq, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have hsum_new : sumTreePhiList v' trees' =
        tne.treePhi v' + (tv.treePhi v' + (tu.treePhi v' + sumTreePhiList v' rest)) := by
      dsimp only [sumTreePhiList, trees', tne, rest]
      rw [List.map_cons, List.sum_cons, ((hperm_both.map _).sum_eq)]
      simp only [List.map_cons, List.sum_cons]
    have htne_phi_le : tne.treePhi v' ≤ Nat.log 2 (2 * st.n + 1) := by
      have h1 : tne.treeSize v' = repSize active' par' (listHead0 (treeIds P s2 tne)) := by
        simpa [v', active', par'] using
          treeSize_vSize_eq_repSize hW' (by simp [trees', tne] : tne ∈ trees')
      have h2 := repSize_le_active (active := active') (par := par') (listHead0 (treeIds P s2 tne))
      have h3 : Nat.log 2 (repSize active' par' (listHead0 (treeIds P s2 tne))) ≤ Nat.log 2 (2 * st.n + 1) :=
        Nat.log_mono_right (by omega)
      have hphi_tne : tne.treePhi v' = Nat.log 2 (tne.treeSize v') := by
        simp [tne, AuxTree.treePhi, AuxTree.rank]
      rw [hphi_tne, h1]
      exact h3
    have htu_phi_eq : tu.treePhi v' = tu.treePhi v := by
      refine SplayState.treePhi_agree (fun w hw => ?_)
      have hwu_nz : w ≠ 0 := by
        have := W.activeValid w (List.mem_flatMap.mpr ⟨tu, htu, hw⟩)
        simp [isNode] at this; omega
      have hwu_ne : w ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tu, htu, hw⟩)
      have hwu_rv : w ≠ rv := fun h => hne (flatMap_mem_unique W.activeNodup htu htv hw (h ▸ hrv_mem))
      exact hv_eq_out w hwu_nz hwu_ne hwu_rv
    have hsum_rest_eq : sumTreePhiList v' rest = sumTreePhiList v rest := by
      dsimp only [sumTreePhiList]
      congr 1
      refine List.map_congr_left (fun c hc => SplayState.treePhi_agree (fun w hw => ?_))
      have hc_ts := List.mem_of_mem_erase (hrest_er_tu c hc)
      have hc_ne_tv : c ≠ tv := fun h =>
        (List.nodup_cons.mp hnd_both).1 (List.mem_cons_of_mem _ ((congrArg (· ∈ rest) h).mp hc))
      have hw_nz : w ≠ 0 := by
        have := W.activeValid w (List.mem_flatMap.mpr ⟨c, hc_ts, hw⟩)
        simp [isNode] at this; omega
      have hw_ne : w ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨c, hc_ts, hw⟩)
      have hw_rv : w ≠ rv := fun h =>
        hc_ne_tv (flatMap_mem_unique W.activeNodup hc_ts htv hw (h ▸ hrv_mem))
      exact hv_eq_out w hw_nz hw_ne hw_rv
    have htv_phi_le : tv.treePhi v' ≤ tv.treePhi v + Nat.log 2 (2 * st.n + 1) := by
      cases htv_c : tv with
      | leaf => exact absurd htv_c (W.treesNonEmpty tv htv)
      | node rid Lv Rv =>
          have hrid_eq : rid = rv := by simp [rv, htv_c, AuxTree.rootId]
          have hnd_tv := (W.treesInv tv htv).nodup
          rw [htv_c] at hnd_tv
          rcases AuxTree.nodup_node_unfold hnd_tv with ⟨_, hrid_nL, _, hrid_nR, _⟩
          have hLv_eq : Lv.treePhi v' = Lv.treePhi v := by
            refine SplayState.treePhi_agree (fun w hw => ?_)
            have hw_tv : w ∈ tv.toList := by rw [htv_c]; simp [AuxTree.toList, hw]
            have hw_nz : w ≠ 0 := by
              have := W.activeValid w (List.mem_flatMap.mpr ⟨tv, htv, hw_tv⟩)
              simp [isNode] at this; omega
            have hw_ne : w ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tv, htv, hw_tv⟩)
            have hw_rv : w ≠ rv := fun h => hrid_nL (hrid_eq ▸ h ▸ hw)
            exact hv_eq_out w hw_nz hw_ne hw_rv
          have hRv_eq : Rv.treePhi v' = Rv.treePhi v := by
            refine SplayState.treePhi_agree (fun w hw => ?_)
            have hw_tv : w ∈ tv.toList := by rw [htv_c]; simp [AuxTree.toList, hw]
            have hw_nz : w ≠ 0 := by
              have := W.activeValid w (List.mem_flatMap.mpr ⟨tv, htv, hw_tv⟩)
              simp [isNode] at this; omega
            have hw_ne : w ≠ ne := fun h => hne_nin_act (h ▸ List.mem_flatMap.mpr ⟨tv, htv, hw_tv⟩)
            have hw_rv : w ≠ rv := fun h => hrid_nR (hrid_eq ▸ h ▸ hw)
            exact hv_eq_out w hw_nz hw_ne hw_rv
          have htv_sz : (AuxTree.node rid Lv Rv).treeSize v' =
              repSize active' par' (listHead0 (treeIds P s2 tv)) := by
            rw [← htv_c]
            simpa [v', active', par'] using treeSize_vSize_eq_repSize hW' (by simp [trees', htv])
          have htv_rk : (AuxTree.node rid Lv Rv).rank v' ≤ Nat.log 2 (2 * st.n + 1) := by
            simp only [AuxTree.rank, htv_sz]
            have h2 := repSize_le_active (active := active') (par := par') (listHead0 (treeIds P s2 tv))
            exact Nat.log_mono_right (by omega)
          simp only [AuxTree.treePhi]
          omega
    dsimp only [v, v'] at hsum_old hsum_new htne_phi_le htu_phi_eq hsum_rest_eq htv_phi_le
    rw [hsum_new, hsum_old, htu_phi_eq, hsum_rest_eq]
    omega
  have hheavy_le : heavyCount P st' ≤ heavyCount P st + 2 := by
    have hrep_mono : ∀ p, repSize active par p ≤ repSize active' par' p := by
      intro p
      have h1 : ∀ w ∈ active, par w ≠ 0 → par' w = par w := fun w hw hp => by
        have hwne : w ≠ ne := fun h => hne_nin_act (h ▸ hw)
        have hwu : w ≠ u_head := fun h => hp (h ▸ hpar_head_old)
        exact hpar'_out w hwu hwne
      have hlen_le : active.length ≤ active'.length := by
        rw [hact'_eq]; simp
      have himp : ∀ w ∈ active, reaches par active.length p w = true →
          reaches par' active'.length p w = true := fun w hw hr =>
        reaches_mono hlen_le
          (reaches_mono_of_non_zero_agree (fun y hy hp => W.subPar_mem_active hy hp) h1
            active.length p w hw hr)
      have hflen := filter_length_le_of_imp
        (fun w => reaches par active.length p w)
        (fun w => reaches par' active'.length p w) active himp
      have hact'_len : active'.length = active.length + 1 := by
        rw [hact'_eq, List.length_cons]
      rw [hact'_len] at hflen
      dsimp only [repSize]
      rw [hact'_eq, List.filter_cons]
      split_ifs <;> simp at hflen ⊢ <;> omega
    have her_le : ((trees.erase tu).filter (isHeavyEdge P s2 active' par')).length ≤
        ((trees.erase tu).filter (isHeavyEdge P st.splay active par)).length := by
      refine filter_length_le_of_imp _ _ (trees.erase tu) (fun c hc_er h => ?_)
      have hc_ts := List.mem_of_mem_erase hc_er
      have hc_tu : c ≠ tu := fun h => (List.nodup_cons.mp (hperm_tu.nodup_iff.mp
        (nodup_of_flatMap_nodup trees W.activeNodup W.treesNonEmpty))).1 (h ▸ hc_er)
      have hc_er_ag := h_er_tu c hc_er
      dsimp only [isHeavyEdge] at h ⊢
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h ⊢
      have hpp_nz : (st.splay.nodes c.rootId).ppar ≠ 0 := hc_er_ag.1 ▸ h.1
      have hhc := hrep_child c hc_ts hc_tu hpp_nz
      have hpm := hrep_mono (st.splay.nodes c.rootId).ppar
      refine ⟨hpp_nz, ?_⟩
      rw [hc_er_ag.1, hc_er_ag.2] at h
      omega
    have hH_new' : heavyCount P st' =
        (if isHeavyEdge P s2 active' par' tne then 1 else 0) +
        ((if isHeavyEdge P s2 active' par' tu then 1 else 0) +
          ((trees.erase tu).filter (isHeavyEdge P s2 active' par')).length) := by
      rw [hH_new]
      dsimp only [heavyCountList, trees']
      rw [filter_cons_length, (hperm_tu.filter _).length_eq, filter_cons_length]
    have hH_old' : heavyCount P st =
        (if isHeavyEdge P st.splay active par tu then 1 else 0) +
          ((trees.erase tu).filter (isHeavyEdge P st.splay active par)).length := by
      rw [hH_old]
      dsimp only [heavyCountList]
      rw [(hperm_tu.filter _).length_eq, filter_cons_length]
    rw [hH_new', hH_old']
    dsimp only [active, par, active', par'] at her_le ⊢
    split_ifs <;> omega
  exact ⟨depth', hW', hphi_le, hheavy_le, hpar'_head, hpar'_ne, hpar'_out⟩

end MinCostFlow.LinkCut
