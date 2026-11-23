module

public import MinCostFlow.LinkCut.ForestModelRoot

/-!
# High-level generic Link-Cut Tree operations (`findRoot`, `connected`, `reroot`, path ops)

This module builds the represented-tree query and update operations on top of `lctExpose_spec`
for any `P : LctPayload α σ τ` satisfying `P.Laws`:
- `lctFindRootCost` / `lctFindRoot`: expose `v` and splay the leftmost node (`subRoot`), keeping
  `inducedSubPar` and `heavyCount` unchanged and paying `9 log(2n + 1)` amortized potential.
- `lctConnectedCost` / `lctConnected`: compare the component roots of two active nodes.
- `lctRerootCost` / `lctReroot`: expose `v` and lazily reverse the path (`revNode`), making `v`
  the new component root, reversing `evalPairs` with `P.revVal`, and preserving `subRoot`
  equivalence.
- `lctPathSummaryCost` / `lctPathSummary`: reroot `u`, expose `v`, and read `(nodes v).sum`.
- `lctPathApplyCost` / `lctPathApply`: reroot `u`, expose `v`, and apply lazy tag `t₀` at `v`.
-/

namespace MinCostFlow.LinkCut

@[expose] public section

variable {α σ τ : Type*}

private theorem lctReroot_subRoot_aux {P : LctPayload α σ τ} (hL : P.Laws)
    {st1 st' : LctState α σ τ} {trees1 trees' : List AuxTree}
    {fl : List ℕ} {d1 d' : ℕ → ℕ}
    (W1 : LctInvWith P st1 trees1 fl d1) (W' : LctInvWith P st' trees' fl d')
    {v : ℕ} {Lv : AuxTree} (ht1 : AuxTree.node v Lv AuxTree.leaf ∈ trees1)
    (ht' : AuxTree.node v AuxTree.leaf Lv ∈ trees')
    (hpp1 : (st1.splay.nodes v).ppar = 0)
    (hpp' : (st'.splay.nodes v).ppar = 0)
    (hids' : treeIds P st'.splay (AuxTree.node v AuxTree.leaf Lv) =
      (treeIds P st1.splay (AuxTree.node v Lv AuxTree.leaf)).reverse)
    (hrev1 : (st1.splay.nodes v).rev = false) (htag1 : (st1.splay.nodes v).tag = P.idTag)
    (_hright1 : (st1.splay.nodes v).right = 0)
    (hpar_out : ∀ z ∉ (AuxTree.node v Lv AuxTree.leaf).toList,
      inducedSubPar P st'.splay trees' z = inducedSubPar P st1.splay trees1 z)
    (hperm : (trees'.flatMap AuxTree.toList).Perm (trees1.flatMap AuxTree.toList)) :
    let h := listHead0 (treeIds P st1.splay (AuxTree.node v Lv AuxTree.leaf))
    let par1 := inducedSubPar P st1.splay trees1
    let par' := inducedSubPar P st'.splay trees'
    let a1 := trees1.flatMap AuxTree.toList
    let a' := trees'.flatMap AuxTree.toList
    (par1 h = 0 ∧ par' v = 0 ∧ h ∈ (AuxTree.node v Lv AuxTree.leaf).toList ∧
      v ∈ (AuxTree.node v Lv AuxTree.leaf).toList) ∧
      ∀ x ∈ a1,
        (subRoot par1 a1.length x = h → subRoot par' a'.length x = v) ∧
        (subRoot par1 a1.length x ≠ h →
          subRoot par' a'.length x = subRoot par1 a1.length x ∧
          subRoot par1 a1.length x ∉ (AuxTree.node v Lv AuxTree.leaf).toList) := by
  intro h par1 par' a1 a'
  let t1 := AuxTree.node v Lv AuxTree.leaf
  let t' := AuxTree.node v AuxTree.leaf Lv
  have hh_par0 : par1 h = 0 := listHead0_par_eq_zero_of_ppar W1 ht1 hpp1
  have hids1_last : listLast0 (treeIds P st1.splay t1) = v :=
    listLast0_eq_root_of_right_leaf hL hrev1 htag1
  have hhead'_v : listHead0 (treeIds P st'.splay t') = v := by
    rw [hids', listHead0_reverse_eq_listLast0, hids1_last]
  have hv_par'0 : par' v = 0 := by
    have h1 := listHead0_par_eq_zero_of_ppar W' ht' (by simpa [t', AuxTree.rootId] using hpp')
    rw [hhead'_v] at h1
    exact h1
  have hh_mem : h ∈ t1.toList := listHead0_mem_of_ne_nil (W1.treesNonEmpty t1 ht1)
  have hv_mem : v ∈ t1.toList := by simp [t1, AuxTree.toList]
  refine ⟨⟨hh_par0, hv_par'0, hh_mem, hv_mem⟩, ?_⟩
  suffices hmain : ∀ k x, x ∈ a1 → d1 x ≤ k →
      (subRoot par1 a1.length x = h → subRoot par' a'.length x = v) ∧
      (subRoot par1 a1.length x ≠ h →
        subRoot par' a'.length x = subRoot par1 a1.length x ∧
        subRoot par1 a1.length x ∉ t1.toList) from
    fun x hx => hmain (d1 x) x hx le_rfl
  intro k
  induction k with
  | zero =>
      intro x hx hle
      by_cases hxt : x ∈ t1.toList
      · have hx' : x ∈ t'.toList := by
          simp only [t', AuxTree.toList, List.mem_append, List.mem_singleton]
          simp only [t1, AuxTree.toList, List.mem_append, List.mem_singleton] at hxt
          tauto
        have hr1 : subRoot par1 a1.length x = h :=
          subRoot_eq_of_reaches_zero le_rfl (tree_reaches_head W1 ht1 hxt) hh_par0
        have hr' : subRoot par' a'.length x = v := by
          have hrc := tree_reaches_head W' ht' hx'
          rw [hhead'_v] at hrc
          exact subRoot_eq_of_reaches_zero le_rfl hrc hv_par'0
        exact ⟨fun _ => hr', fun hne => absurd hr1 hne⟩
      · have hpx0 : par1 x = 0 := by
          by_contra hnz
          have hlt := W1.acyclic x hx hnz
          omega
        have hxt_exp : x ∉ (AuxTree.node v Lv AuxTree.leaf).toList := hxt
        have hpx'0 : par' x = 0 := by change inducedSubPar P st'.splay trees' x = 0; rw [hpar_out x hxt_exp]; exact hpx0
        have hs1 : subRoot par1 a1.length x = x := subRoot_eq_self_of_zero W1 hx hpx0
        have hs' : subRoot par' a'.length x = x :=
          subRoot_eq_self_of_zero W' (hperm.symm.mem_iff.mp hx) hpx'0
        have hxh : x ≠ h := fun heq => hxt (heq ▸ hh_mem)
        exact ⟨fun hEq => absurd (hs1 ▸ hEq) hxh, fun _ => ⟨hs'.trans hs1.symm, by rwa [hs1]⟩⟩
  | succ k ih =>
      intro x hx hle
      by_cases hxt : x ∈ t1.toList
      · have hx' : x ∈ t'.toList := by
          simp only [t', AuxTree.toList, List.mem_append, List.mem_singleton]
          simp only [t1, AuxTree.toList, List.mem_append, List.mem_singleton] at hxt
          tauto
        have hr1 : subRoot par1 a1.length x = h :=
          subRoot_eq_of_reaches_zero le_rfl (tree_reaches_head W1 ht1 hxt) hh_par0
        have hr' : subRoot par' a'.length x = v := by
          have hrc := tree_reaches_head W' ht' hx'
          rw [hhead'_v] at hrc
          exact subRoot_eq_of_reaches_zero le_rfl hrc hv_par'0
        exact ⟨fun _ => hr', fun hne => absurd hr1 hne⟩
      · by_cases hpx0 : par1 x = 0
        · have hxt_exp : x ∉ (AuxTree.node v Lv AuxTree.leaf).toList := hxt
          have hpx'0 : par' x = 0 := by change inducedSubPar P st'.splay trees' x = 0; rw [hpar_out x hxt_exp]; exact hpx0
          have hs1 : subRoot par1 a1.length x = x := subRoot_eq_self_of_zero W1 hx hpx0
          have hs' : subRoot par' a'.length x = x :=
            subRoot_eq_self_of_zero W' (hperm.symm.mem_iff.mp hx) hpx'0
          have hxh : x ≠ h := fun heq => hxt (heq ▸ hh_mem)
          exact ⟨fun hEq => absurd (hs1 ▸ hEq) hxh, fun _ => ⟨hs'.trans hs1.symm, by rwa [hs1]⟩⟩
        · have hxt_exp : x ∉ (AuxTree.node v Lv AuxTree.leaf).toList := hxt
          have hpx' : par' x = par1 x := hpar_out x hxt_exp
          have hpx'_nz : par' x ≠ 0 := hpx' ▸ hpx0
          have hpx_mem : par1 x ∈ a1 := W1.subPar_mem_active hx hpx0
          have hd_px : d1 (par1 x) ≤ k := by
            have hlt : d1 (par1 x) < d1 x := W1.acyclic x hx hpx0
            omega
          have hstep1 : subRoot par1 a1.length x = subRoot par1 a1.length (par1 x) :=
            subRoot_step_eq W1 hx hpx0
          have hstep' : subRoot par' a'.length x = subRoot par' a'.length (par1 x) := by
            rw [← hpx']
            exact subRoot_step_eq W' (hperm.symm.mem_iff.mp hx) hpx'_nz
          rcases ih (par1 x) hpx_mem hd_px with ⟨ih1, ih2⟩
          exact ⟨fun hEq => hstep'.trans (ih1 (hstep1.symm.trans hEq)),
            fun hNe => by
              rcases ih2 (fun hEq => hNe (hstep1.trans hEq)) with ⟨ha, hb⟩
              exact ⟨hstep'.trans (ha.trans hstep1.symm), hstep1 ▸ hb⟩⟩

private theorem perm_flatMap_of_perm {β γ : Type*} {f : β → List γ} :
    ∀ {l₁ l₂ : List β}, l₁.Perm l₂ → (l₁.flatMap f).Perm (l₂.flatMap f)
  | _, _, .nil => .nil
  | _, _, .cons x h => List.Perm.append_left (f x) (perm_flatMap_of_perm h)
  | _, _, .swap x y l => by
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact List.Perm.append_right (l.flatMap f) List.perm_append_comm
  | _, _, .trans h₁ h₂ => (perm_flatMap_of_perm h₁).trans (perm_flatMap_of_perm h₂)

private theorem forestPairs_congr_trees {P : LctPayload α σ τ}
    {s₁ s₂ : SplayState α σ τ} : ∀ {ts : List AuxTree},
    (∀ t ∈ ts, SplayState.evalPairs P s₁ t false P.idTag = SplayState.evalPairs P s₂ t false P.idTag) →
    forestPairs P s₁ ts = forestPairs P s₂ ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [forestPairs, List.flatMap_cons]
      rw [h t List.mem_cons_self]
      have hrest : forestPairs P s₁ ts = forestPairs P s₂ ts :=
        forestPairs_congr_trees fun c hc => h c (List.mem_cons_of_mem _ hc)
      simpa [forestPairs] using congrArg (SplayState.evalPairs P s₂ t false P.idTag ++ ·) hrest

theorem lctReroot_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) (hv_v : isVertex st.n v) :
    let res := lctRerootCost P st v
    let st' := res.1
    let halves := res.2.1
    let iters := res.2.2
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    ∃ trees' L depth',
      let t_rev := AuxTree.node v AuxTree.leaf L
      let t_exp := AuxTree.node v L AuxTree.leaf
      let st_exp := (lctExposeCost P st v).1
      let onPath := SplayState.evalPairs P st_exp.splay t_exp false P.idTag
      let offPath := forestPairs P st_exp.splay (trees'.erase t_rev)
      t_rev ∈ trees' ∧
        LctInvWith P st' trees' freeList depth' ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        (st'.splay.nodes v).ppar = 0 ∧
        inducedSubPar P st'.splay trees' v = 0 ∧
        (∀ z, z ∈ t_rev.toList ↔ reaches par active.length z v = true) ∧
        (∀ z ∉ t_rev.toList, inducedSubPar P st'.splay trees' z = par z) ∧
        (∀ x ∈ t_rev.toList, ∀ y ∈ t_rev.toList,
          inducedSubPar P st'.splay trees' x = y ↔ par y = x) ∧
        SplayState.evalPairs P st'.splay t_rev false P.idTag =
          (onPath.map (fun p => (p.1, P.revVal p.2))).reverse ∧
        (onPath ++ offPath).Perm (forestPairs P st.splay trees) ∧
        (forestPairs P st'.splay trees').Perm
          ((onPath.map (fun p => (p.1, P.revVal p.2))).reverse ++ offPath) ∧
        (∀ p ∈ offPath, p.1 ∉ t_rev.toList) ∧
        (∀ p ∈ onPath, p.1 ∈ t_rev.toList) ∧
        (∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
          c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w) ∧
        (∀ x ∈ active, ∀ y ∈ active,
          subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length x =
            subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length y ↔
          subRoot par active.length x = subRoot par active.length y) ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3 := by
  intro res st' halves iters active par
  rcases lctExpose_spec hL W htv hv with
    ⟨trees1, Lv, ht1_mem, hW1, hact1_perm, hpar1, hpairs1, hpp_v1, hright1, hrev1, htag1,
      hreach1, hunt1, hpot1, hH1⟩
  let st1 := (lctExposeCost P st v).1
  have hst1_n : st1.n = st.n := rfl
  have hlast1_v : isVertex st1.n (listLast0 (treeIds P st1.splay (AuxTree.node v Lv AuxTree.leaf))) := by
    have hl : listLast0 (treeIds P st1.splay (AuxTree.node v Lv AuxTree.leaf)) = v :=
      listLast0_eq_root_of_right_leaf hL hrev1 htag1
    rw [hl, hst1_n]
    exact hv_v
  rcases revNode_spec hL hW1 ht1_mem hpp_v1 hlast1_v with
    ⟨depth', hW', hPhi', hH', hids', hout_rev⟩
  let t_rev := AuxTree.node v AuxTree.leaf Lv
  let t_exp := AuxTree.node v Lv AuxTree.leaf
  let trees' := t_rev :: trees1.erase t_exp
  have ht'_mem : t_rev ∈ trees' := List.mem_cons_self
  have hperm_t : t_rev.toList.Perm t_exp.toList := by
    simp only [t_rev, t_exp, AuxTree.toList, List.append_nil, List.nil_append]
    exact List.perm_append_comm
  have hact'_perm1 : (trees'.flatMap AuxTree.toList).Perm (trees1.flatMap AuxTree.toList) :=
    flatMap_perm_of_replace ht1_mem hperm_t
  have hact'_perm : (trees'.flatMap AuxTree.toList).Perm active :=
    hact'_perm1.trans hact1_perm
  have htrev_toList : ∀ z, z ∈ t_rev.toList ↔ z ∈ t_exp.toList := fun z => hperm_t.mem_iff
  have hrev_root := SplayState.revNode_root_preserves hL (hW1.treesInv t_exp ht1_mem).nodup
    (hW1.treesInv t_exp ht1_mem).sub
  rcases hrev_root with ⟨_, hev_rev, hpp_rev, _⟩
  have hpp'_v : (st'.splay.nodes v).ppar = 0 := by
    change ((SplayState.revNode P st1.splay v).nodes v).ppar = 0
    rw [hpp_rev, hpp_v1]
  have hev_t_rev : SplayState.evalPairs P st'.splay t_rev false P.idTag =
      ((SplayState.evalPairs P st1.splay t_exp false P.idTag).map (fun p => (p.1, P.revVal p.2))).reverse := by
    change SplayState.evalPairs P (SplayState.revNode P st1.splay v) t_rev false P.idTag = _
    rw [hev_rev false P.idTag]
    simp only [Bool.not_false]
    rw [SplayState.evalPairs_true_idTag hL, List.map_reverse]
  have hW'_eq : LctInvWith P st' trees' freeList depth' := hW'
  have hpar_out1 : ∀ z ∉ t_exp.toList,
      inducedSubPar P st'.splay trees' z = inducedSubPar P st1.splay trees1 z := by
    intro z hzn
    by_cases hz_a : z ∈ trees1.flatMap AuxTree.toList
    · rcases List.mem_flatMap.mp hz_a with ⟨c, hc, hzc⟩
      have hne : c ≠ t_exp := fun h => hzn (h ▸ hzc)
      have hc' : c ∈ trees' := List.mem_cons_of_mem _ ((List.mem_erase_of_ne hne).mpr hc)
      rw [inducedSubPar_eq_of_mem hW'_eq.activeNodup hc' hzc,
        inducedSubPar_eq_of_mem hW1.activeNodup hc hzc]
      have hag : ∀ w ∈ c.toList, st'.splay.nodes w = st1.splay.nodes w := fun w hw => by
        have hw_nt : w ∉ t_exp.toList := fun hm =>
          hne (flatMap_mem_unique hW1.activeNodup hc ht1_mem hw hm)
        exact hout_rev w hw_nt
      have hev_c : SplayState.evalPairs P st'.splay c false P.idTag =
          SplayState.evalPairs P st1.splay c false P.idTag :=
        SplayState.evalPairs_agree P hag false P.idTag
      have hids_c : treeIds P st'.splay c = treeIds P st1.splay c := treeIds_eq_of_evalPairs hev_c
      have hpp_c : (st'.splay.nodes c.rootId).ppar = (st1.splay.nodes c.rootId).ppar :=
        congrArg SplayNode.ppar (hag c.rootId (AuxTree.rootId_mem (hW1.treesNonEmpty c hc)))
      rw [hids_c, hpp_c]
    · have hz_a' : z ∉ trees'.flatMap AuxTree.toList := fun hm =>
        hz_a (hact'_perm1.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hz_a', inducedSubPar_eq_zero_of_not_mem hz_a]
  have hpar_out : ∀ z ∉ t_rev.toList, inducedSubPar P st'.splay trees' z = par z := fun z hzn => by
    have hzn' : z ∉ t_exp.toList := fun hm => hzn ((htrev_toList z).mpr hm)
    rw [hpar_out1 z hzn', hpar1 z]
  have hsub_aux := lctReroot_subRoot_aux hL hW1 hW'_eq ht1_mem ht'_mem hpp_v1 hpp'_v hids' hrev1 htag1
    hright1 hpar_out1 hact'_perm1
  rcases hsub_aux with ⟨⟨_, hv_par'0, _, _⟩, hsub_map⟩
  have hpar_rev_iff : ∀ x ∈ t_rev.toList, ∀ y ∈ t_rev.toList,
      inducedSubPar P st'.splay trees' x = y ↔ par y = x := by
    intro x hx y hy
    have hx_e := (htrev_toList x).mp hx
    have hy_e := (htrev_toList y).mp hy
    have hi1 := inducedSubPar_eq_of_mem (P := P) (s := st'.splay) hW'_eq.activeNodup ht'_mem hx
    have hi2 := inducedSubPar_eq_of_mem (P := P) (s := st1.splay) hW1.activeNodup ht1_mem hy_e
    have hpy : par y = inducedSubPar P st1.splay trees1 y := (hpar1 y).symm
    have ht_rev_rt : t_rev.rootId = v := rfl
    have ht_exp_rt : (AuxTree.node v Lv AuxTree.leaf).rootId = v := rfl
    have hids_rev : treeIds P st'.splay t_rev = (treeIds P st1.splay t_exp).reverse := hids'
    change inducedSubPar P st'.splay trees' x = y ↔ par y = x
    rw [hi1, hpy, hi2, ht_rev_rt, ht_exp_rt, hpp'_v, hpp_v1, hids_rev]
    have hnd_ids : (treeIds P st1.splay t_exp).Nodup := treeIds_nodup (hW1.treesInv t_exp ht1_mem)
    have h0_nmem : 0 ∉ treeIds P st1.splay t_exp := fun hm => by
      have hm' := (mem_treeIds_iff P st1.splay t_exp 0).mp hm
      have hm_act := hW1.activeValid 0 (List.mem_flatMap.mpr ⟨t_exp, ht1_mem, hm'⟩)
      simp [isNode] at hm_act
    have hx_ids : x ∈ treeIds P st1.splay t_exp := (mem_treeIds_iff P st1.splay t_exp x).mpr hx_e
    have hy_ids : y ∈ treeIds P st1.splay t_exp := (mem_treeIds_iff P st1.splay t_exp y).mpr hy_e
    exact chainPred_reverse_iff hnd_ids h0_nmem hx_ids hy_ids
  have hreach_rev : ∀ z, z ∈ t_rev.toList ↔ reaches par active.length z v = true := fun z =>
    (htrev_toList z).trans (hreach1 z)
  have hunt_rev : ∀ c ∈ trees, (∀ w ∈ c.toList, reaches par active.length w v = false) →
      c ∈ trees' ∧ ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := by
    intro c hc hno
    rcases hunt1 c hc hno with ⟨hc1, hag1⟩
    have hv_nc : v ∉ c.toList := fun hm => by
      have := hno v hm; simp [reaches_self] at this
    have hc_ne : c ≠ t_exp := fun h => hv_nc (h ▸ (by simp [t_exp, AuxTree.toList]))
    have hc' : c ∈ trees' := List.mem_cons_of_mem _ ((List.mem_erase_of_ne hc_ne).mpr hc1)
    have hag' : ∀ w ∈ c.toList, st'.splay.nodes w = st.splay.nodes w := fun w hw => by
      have hw_nt : w ∉ t_exp.toList := fun hm =>
        hc_ne (flatMap_mem_unique hW1.activeNodup hc1 ht1_mem hw hm)
      change (SplayState.revNode P st1.splay v).nodes w = st.splay.nodes w
      rw [hout_rev w hw_nt, hag1 w hw]
    exact ⟨hc', hag'⟩
  have hconn_iff : ∀ x ∈ active, ∀ y ∈ active,
      subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length y ↔
      subRoot par active.length x = subRoot par active.length y := by
    intro x hx y hy
    have hx_a : x ∈ trees.flatMap AuxTree.toList := hx
    have hy_a : y ∈ trees.flatMap AuxTree.toList := hy
    have hx1 : x ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hx_a
    have hy1 : y ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hy_a
    have hsx : subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length x =
        subRoot par active.length x :=
      subRoot_eq_of_LctInvWith_agree W hW1 hact1_perm.symm (fun z => (hpar1 z).symm) hx_a
    have hsy : subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length y =
        subRoot par active.length y :=
      subRoot_eq_of_LctInvWith_agree W hW1 hact1_perm.symm (fun z => (hpar1 z).symm) hy_a
    rcases hsub_map x hx1 with ⟨hx_eq, hx_ne⟩
    rcases hsub_map y hy1 with ⟨hy_eq, hy_ne⟩
    rw [hsx] at hx_eq hx_ne
    rw [hsy] at hy_eq hy_ne
    let h := listHead0 (treeIds P st1.splay t_exp)
    by_cases hxh : subRoot par active.length x = h <;> by_cases hyh : subRoot par active.length y = h
    · rw [hx_eq hxh, hy_eq hyh, hxh, hyh]
      simp
    · have hy' := hy_ne hyh
      have hv_in : v ∈ t_exp.toList := by simp [t_exp, AuxTree.toList]
      have hne_v : v ≠ subRoot par active.length y := fun heq => hy'.2 (heq ▸ hv_in)
      rw [hx_eq hxh, hy'.1, hxh]
      exact ⟨fun heq => absurd heq hne_v, fun heq => absurd heq.symm hyh⟩
    · have hx' := hx_ne hxh
      have hv_in : v ∈ t_exp.toList := by simp [t_exp, AuxTree.toList]
      have hne_v : subRoot par active.length x ≠ v := fun heq => hx'.2 (heq.symm ▸ hv_in)
      rw [hy_eq hyh, hx'.1, hyh]
      exact ⟨fun heq => absurd heq hne_v, fun heq => absurd heq hxh⟩
    · have hx' := hx_ne hxh
      have hy' := hy_ne hyh
      rw [hx'.1, hy'.1]
  refine ⟨trees', Lv, depth', ht'_mem, hW', hact'_perm, hpp'_v, hv_par'0, hreach_rev, hpar_out,
    hpar_rev_iff, hev_t_rev, ?_, ?_, ?_, ?_, hunt_rev, hconn_iff, ?_, ?_⟩
  · have h_er : (trees'.erase t_rev) = trees1.erase t_exp := by simp [trees', t_rev, t_exp]
    rw [h_er]
    have hperm_trees : trees1.Perm (t_exp :: trees1.erase t_exp) :=
      List.perm_cons_erase ht1_mem
    have hfp : (forestPairs P st1.splay trees1).Perm
        (SplayState.evalPairs P st1.splay t_exp false P.idTag ++
          forestPairs P st1.splay (trees1.erase t_exp)) := by
      simpa [forestPairs, List.flatMap_cons] using perm_flatMap_of_perm hperm_trees
    exact hfp.symm.trans hpairs1
  · have h_er : (trees'.erase t_rev) = trees1.erase t_exp := by simp [trees', t_rev, t_exp]
    rw [h_er]
    have hfp : (forestPairs P st'.splay trees').Perm
        (SplayState.evalPairs P st'.splay t_rev false P.idTag ++
          forestPairs P st'.splay (trees1.erase t_exp)) := by
      dsimp only [trees', forestPairs]
      rw [List.flatMap_cons]
    have hfp_off : forestPairs P st'.splay (trees1.erase t_exp) =
        forestPairs P st1.splay (trees1.erase t_exp) := by
      refine forestPairs_congr_trees fun c hc => ?_
      have hc_ne : c ≠ t_exp := ne_of_mem_erase_trees hW1.activeNodup hW1.treesNonEmpty hc
      have hc1 : c ∈ trees1 := List.mem_of_mem_erase hc
      exact SplayState.evalPairs_agree P (fun w hw => hout_rev w fun hm =>
        hc_ne (flatMap_mem_unique hW1.activeNodup hc1 ht1_mem hw hm)) false P.idTag
    rw [hev_t_rev, hfp_off] at hfp
    exact hfp
  · intro p hp
    have h_er : (trees'.erase t_rev) = trees1.erase t_exp := by simp [trees', t_rev, t_exp]
    rw [h_er] at hp
    rcases List.mem_flatMap.mp hp with ⟨c, hc, hpc⟩
    have hc_ne : c ≠ t_exp := ne_of_mem_erase_trees hW1.activeNodup hW1.treesNonEmpty hc
    have hc1 : c ∈ trees1 := List.mem_of_mem_erase hc
    have hp_c : p.1 ∈ c.toList :=
      (mem_treeIds_iff P st1.splay c p.1).mp (List.mem_map_of_mem hpc)
    exact fun hm => hc_ne (flatMap_mem_unique hW1.activeNodup hc1 ht1_mem hp_c ((htrev_toList p.1).mp hm))
  · intro p hp
    have hp_e : p.1 ∈ t_exp.toList :=
      (mem_treeIds_iff P st1.splay t_exp p.1).mp (List.mem_map_of_mem hp)
    exact (htrev_toList p.1).mpr hp_e
  · have hpot1' : (lctExposeCost P st v).2.1 + sumTreePhi P st1 ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := hpot1
    have hPhi'' : sumTreePhi P st' = sumTreePhi P st1 := hPhi'
    change (lctExposeCost P st v).2.1 + sumTreePhi P st' ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1)
    omega
  · have hH1' : (lctExposeCost P st v).2.2 + heavyCount P st1 ≤
        heavyCount P st + 2 * Nat.log 2 (2 * st.n + 1) + 2 := hH1
    have hst1_n' : (lctExposeCost P st v).1.n = st.n := rfl
    rw [hst1_n'] at hH'
    have hH'' : heavyCount P st' ≤ heavyCount P st1 + Nat.log 2 (2 * st.n + 1) + 1 := hH'
    change (lctExposeCost P st v).2.2 + heavyCount P st' ≤ heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3
    omega

/-! ### `lctPathSummary` and `lctPathApply` -/

/-- Reroot `u`, expose `v`, and return `(st', (st'.splay.nodes v).sum, halves, iters)`. -/
def lctPathSummaryCost (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    LctState α σ τ × σ × ℕ × ℕ :=
  let r1 := lctRerootCost P st u
  let r2 := lctExposeCost P r1.1 v
  (r2.1, (r2.1.splay.nodes v).sum, r1.2.1 + r2.2.1, r1.2.2 + r2.2.2)

/-- Functional wrapper for `lctPathSummaryCost`. -/
def lctPathSummary (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    LctState α σ τ × σ :=
  let r := lctPathSummaryCost P st u v
  (r.1, r.2.1)

/-- Reroot `u`, expose `v`, and apply lazy path tag `t₀` at `v`. -/
def lctPathApplyCost (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (t₀ : τ) :
    LctState α σ τ × ℕ × ℕ :=
  let r1 := lctRerootCost P st u
  let r2 := lctExposeCost P r1.1 v
  let s3 := SplayState.applyTagNode P r2.1.splay v t₀
  ({ n := st.n, splay := s3, freeHead := r2.1.freeHead }, r1.2.1 + r2.2.1, r1.2.2 + r2.2.2)

/-- Functional wrapper for `lctPathApplyCost`. -/
def lctPathApply (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (t₀ : τ) :
    LctState α σ τ :=
  (lctPathApplyCost P st u v t₀).1

private theorem list_filter_congr_mem {β : Type*} {p q : β → Bool} : ∀ {l : List β},
    (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.filter_cons, h x List.mem_cons_self]
      cases q x <;> simp [list_filter_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem list_map_congr_mem {β γ : Type*} {f g : β → γ} : ∀ {l : List β},
    (∀ x ∈ l, f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.map_cons, h x List.mem_cons_self,
        list_map_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem repSize_congr_par_same {active : List ℕ} {par₁ par₂ : ℕ → ℕ}
    (hpar : ∀ z, par₁ z = par₂ z) (u : ℕ) :
    repSize active par₁ u = repSize active par₂ u := by
  dsimp only [repSize]
  rw [list_filter_congr_mem fun w _ => reaches_congr hpar active.length u w]

private theorem vSize_congr_apply {P : LctPayload α σ τ}
    {s₁ s₂ : SplayState α σ τ} {active : List ℕ} {par₁ par₂ : ℕ → ℕ} {ts : List AuxTree}
    (htreeIds : ∀ t ∈ ts, treeIds P s₁ t = treeIds P s₂ t)
    (hppar : ∀ t ∈ ts, (s₁.nodes t.rootId).ppar = (s₂.nodes t.rootId).ppar)
    (hpar : ∀ z, par₁ z = par₂ z) :
    vSize P s₁ active par₁ ts = vSize P s₂ active par₂ ts := by
  funext u
  dsimp only [vSize]
  have hflt : ts.filter (fun t => (s₁.nodes t.rootId).ppar == u) =
      ts.filter (fun t => (s₂.nodes t.rootId).ppar == u) :=
    list_filter_congr_mem fun t ht => by simp [hppar t ht]
  rw [hflt]
  congr 1
  refine list_map_congr_mem fun t ht => ?_
  have ht' : t ∈ ts := (List.mem_filter.mp ht).1
  rw [htreeIds t ht']
  exact repSize_congr_par_same hpar _

private theorem heavyCountList_congr_applyTag {P : LctPayload α σ τ}
    {s₁ s₂ : SplayState α σ τ} {active : List ℕ} {par₁ par₂ : ℕ → ℕ} {trees : List AuxTree}
    (htreeIds : ∀ t ∈ trees, treeIds P s₁ t = treeIds P s₂ t)
    (hppar : ∀ t ∈ trees, (s₁.nodes t.rootId).ppar = (s₂.nodes t.rootId).ppar)
    (hpar : ∀ z, par₁ z = par₂ z) :
    heavyCountList P s₁ active par₁ trees = heavyCountList P s₂ active par₂ trees := by
  dsimp only [heavyCountList]
  congr 1
  exact list_filter_congr_mem fun t ht => by
    have h1 : listHead0 (treeIds P s₁ t) = listHead0 (treeIds P s₂ t) := by rw [htreeIds t ht]
    have h2 : (s₁.nodes t.rootId).ppar = (s₂.nodes t.rootId).ppar := hppar t ht
    have hrep := repSize_congr_par_same (active := active) hpar
    simp only [isHeavyEdge, h1, h2, hrep]

theorem lctPathSummary_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList) (hu_v : isVertex st.n u)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList)
    (hconn : subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length v) :
    let res := lctPathSummaryCost P st u v
    let st' := res.1
    let sumRes := res.2.1
    let halves := res.2.2.1
    let iters := res.2.2.2
    let active := trees.flatMap AuxTree.toList
    let st1 := (lctRerootCost P st u).1
    ∃ trees1 trees' L depth',
      let t_exp := AuxTree.node v L AuxTree.leaf
      let onPath := SplayState.evalPairs P st'.splay t_exp false P.idTag
      let offPath := forestPairs P st'.splay (trees'.erase t_exp)
      t_exp ∈ trees' ∧
        LctInvWith P st' trees' freeList depth' ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        (st'.splay.nodes v).ppar = 0 ∧
        (st'.splay.nodes v).right = 0 ∧
        (st'.splay.nodes v).rev = false ∧
        (st'.splay.nodes v).tag = P.idTag ∧
        inducedSubPar P st'.splay trees' u = 0 ∧
        listHead0 (treeIds P st'.splay t_exp) = u ∧
        listLast0 (treeIds P st'.splay t_exp) = v ∧
        sumRes = P.listSummary onPath ∧
        (onPath ++ offPath).Perm (forestPairs P st1.splay trees1) ∧
        (forestPairs P st'.splay trees').Perm (onPath ++ offPath) ∧
        (∀ z, z ∈ t_exp.toList ↔ reaches (inducedSubPar P st'.splay trees')
          (trees'.flatMap AuxTree.toList).length z v = true) ∧
        (∀ p ∈ offPath, p.1 ∉ t_exp.toList) ∧
        (∀ p ∈ onPath, p.1 ∈ t_exp.toList) ∧
        (∀ x ∈ active, ∀ y ∈ active,
          subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length x =
            subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length y ↔
          subRoot (inducedSubPar P st.splay trees) active.length x =
            subRoot (inducedSubPar P st.splay trees) active.length y) ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 12 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 5 := by
  intro res st' sumRes halves iters active st1
  rcases lctReroot_spec hL W htu hu hu_v with
    ⟨trees1, Lu, depth1, ht1_mem, hW1, hact1_perm, hpp1_u, hpar1_u, _, _, _, _, _, _, _, _, _,
      hconn1_iff, hpot1, hH1⟩
  have hv1 : v ∈ trees1.flatMap AuxTree.toList :=
    hact1_perm.symm.mem_iff.mp (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)
  rcases List.mem_flatMap.mp hv1 with ⟨tv1, htv1, hv1'⟩
  rcases lctExpose_spec hL hW1 htv1 hv1' with
    ⟨trees2, Lv, ht2_mem, hW2, hact2_perm, hpar2, hpairs2, hpp_v2, hright2, hrev2, htag2,
      hreach2, _, hpot2, hH2⟩
  let t_exp := AuxTree.node v Lv AuxTree.leaf
  have hst'_eq : st' = (lctExposeCost P st1 v).1 := rfl
  have hu_act : u ∈ active := List.mem_flatMap.mpr ⟨tu, htu, hu⟩
  have hv_act : v ∈ active := List.mem_flatMap.mpr ⟨tv, htv, hv⟩
  have hconn1 : subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length v :=
    (hconn1_iff u hu_act v hv_act).mpr hconn
  have hu1_mem : u ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hu_act
  have hsub1_u : subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length u = u :=
    subRoot_eq_self_of_zero hW1 hu1_mem hpar1_u
  have hreach1_uv : reaches (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length u v = true := by
    rw [← hsub1_u, hconn1]
    exact reaches_subRoot hW1 hv1
  have hu_exp : u ∈ t_exp.toList := (hreach2 u).mpr hreach1_uv
  have hpar'_u : inducedSubPar P st'.splay trees2 u = 0 := by
    rw [hst'_eq, hpar2 u]; exact hpar1_u
  have hhead_u : listHead0 (treeIds P st'.splay t_exp) = u :=
    (eq_listHead0_of_par_zero hW2 ht2_mem hu_exp hpar'_u).symm
  have hlast_v : listLast0 (treeIds P st'.splay t_exp) = v :=
    listLast0_eq_root_of_right_leaf hL hrev2 htag2
  have hsum_eq : sumRes = P.listSummary (SplayState.evalPairs P st'.splay t_exp false P.idTag) := by
    have hsub := (hW2.treesInv t_exp ht2_mem).sub
    rw [SplayState.SubtreeInv.eq_2] at hsub
    exact hsub.2.2.2.2.2.2.1
  have hperm_trees2 : trees2.Perm (t_exp :: trees2.erase t_exp) := List.perm_cons_erase ht2_mem
  have hfp2 : (forestPairs P st'.splay trees2).Perm
      (SplayState.evalPairs P st'.splay t_exp false P.idTag ++
        forestPairs P st'.splay (trees2.erase t_exp)) := by
    simpa [forestPairs, List.flatMap_cons] using perm_flatMap_of_perm hperm_trees2
  have hreach' : ∀ z, z ∈ t_exp.toList ↔
      reaches (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length z v = true := by
    intro z
    rw [hst'_eq, hact2_perm.length_eq, reaches_congr hpar2]
    exact hreach2 z
  have hconn2_iff : ∀ x ∈ active, ∀ y ∈ active,
      subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length y ↔
      subRoot (inducedSubPar P st.splay trees) active.length x =
        subRoot (inducedSubPar P st.splay trees) active.length y := by
    intro x hx y hy
    have hsx : subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length x :=
      subRoot_eq_of_LctInvWith_agree hW1 hW2 hact2_perm.symm (fun z => (hpar2 z).symm)
        (hact1_perm.symm.mem_iff.mp hx)
    have hsy : subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length y =
        subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length y :=
      subRoot_eq_of_LctInvWith_agree hW1 hW2 hact2_perm.symm (fun z => (hpar2 z).symm)
        (hact1_perm.symm.mem_iff.mp hy)
    rw [hsx, hsy]
    exact hconn1_iff x hx y hy
  refine ⟨trees1, trees2, Lv, depth1, ht2_mem, hW2, hact2_perm.trans hact1_perm, hpp_v2, hright2,
    hrev2, htag2, hpar'_u, hhead_u, hlast_v, hsum_eq, hfp2.symm.trans hpairs2, hfp2, hreach',
    ?_, ?_, hconn2_iff, ?_, ?_⟩
  · intro p hp
    rcases List.mem_flatMap.mp hp with ⟨c, hc, hpc⟩
    have hc_ne : c ≠ t_exp := ne_of_mem_erase_trees hW2.activeNodup hW2.treesNonEmpty hc
    have hc2 : c ∈ trees2 := List.mem_of_mem_erase hc
    have hp_c : p.1 ∈ c.toList :=
      (mem_treeIds_iff P st'.splay c p.1).mp (List.mem_map_of_mem hpc)
    exact fun hm => hc_ne (flatMap_mem_unique hW2.activeNodup hc2 ht2_mem hp_c hm)
  · intro p hp
    exact (mem_treeIds_iff P st'.splay t_exp p.1).mp (List.mem_map_of_mem hp)
  · have hst1_n : (lctRerootCost P st u).1.n = st.n := rfl
    rw [hst1_n] at hpot2
    have hsum1 := Nat.add_le_add_left hpot2 (lctRerootCost P st u).2.1
    have hsum2 := Nat.add_le_add_right hpot1 (6 * Nat.log 2 (2 * st.n + 1))
    calc halves + sumTreePhi P st'
        = (lctRerootCost P st u).2.1 + ((lctExposeCost P (lctRerootCost P st u).1 v).2.1 +
            sumTreePhi P (lctExposeCost P (lctRerootCost P st u).1 v).1) := by
            dsimp only [halves, res, lctPathSummaryCost, st']
            omega
      _ ≤ (lctRerootCost P st u).2.1 + (sumTreePhi P (lctRerootCost P st u).1 +
            6 * Nat.log 2 (2 * st.n + 1)) := hsum1
      _ ≤ (sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1)) + 6 * Nat.log 2 (2 * st.n + 1) := by omega
      _ = sumTreePhi P st + 12 * Nat.log 2 (2 * st.n + 1) := by omega
  · have hst1_n : (lctRerootCost P st u).1.n = st.n := rfl
    rw [hst1_n] at hH2
    have hsum1 := Nat.add_le_add_left hH2 (lctRerootCost P st u).2.2
    calc iters + heavyCount P st'
        = (lctRerootCost P st u).2.2 + ((lctExposeCost P (lctRerootCost P st u).1 v).2.2 +
            heavyCount P (lctExposeCost P (lctRerootCost P st u).1 v).1) := by
            dsimp only [iters, res, lctPathSummaryCost, st']
            omega
      _ ≤ (lctRerootCost P st u).2.2 + (heavyCount P (lctRerootCost P st u).1 +
            2 * Nat.log 2 (2 * st.n + 1) + 2) := hsum1
      _ ≤ (heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3) +
            (2 * Nat.log 2 (2 * st.n + 1) + 2) := by omega
      _ = heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 5 := by omega

theorem lctPathApply_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList) (hu_v : isVertex st.n u)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList)
    (hconn : subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length v)
    (t₀ : τ) :
    let res := lctPathApplyCost P st u v t₀
    let st' := res.1
    let halves := res.2.1
    let iters := res.2.2
    let active := trees.flatMap AuxTree.toList
    let st_exp := (lctExposeCost P (lctRerootCost P st u).1 v).1
    ∃ trees' L depth',
      let t_exp := AuxTree.node v L AuxTree.leaf
      let onPath := SplayState.evalPairs P st_exp.splay t_exp false P.idTag
      let offPath := forestPairs P st_exp.splay (trees'.erase t_exp)
      t_exp ∈ trees' ∧
        LctInvWith P st' trees' freeList depth' ∧
        (trees'.flatMap AuxTree.toList).Perm active ∧
        inducedSubPar P st'.splay trees' u = 0 ∧
        listHead0 (treeIds P st'.splay t_exp) = u ∧
        listLast0 (treeIds P st'.splay t_exp) = v ∧
        SplayState.evalPairs P st'.splay t_exp false P.idTag =
          onPath.map (fun p => (p.1, P.actVal t₀ p.2)) ∧
        (∀ z, inducedSubPar P st'.splay trees' z = inducedSubPar P st_exp.splay trees' z) ∧
        (forestPairs P st'.splay trees').Perm
          (onPath.map (fun p => (p.1, P.actVal t₀ p.2)) ++ offPath) ∧
        (forestPairs P st_exp.splay trees').Perm (onPath ++ offPath) ∧
        (∀ p ∈ offPath, p.1 ∉ t_exp.toList) ∧
        (∀ p ∈ onPath, p.1 ∈ t_exp.toList) ∧
        (∀ x ∈ active, ∀ y ∈ active,
          subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length x =
            subRoot (inducedSubPar P st'.splay trees') (trees'.flatMap AuxTree.toList).length y ↔
          subRoot (inducedSubPar P st.splay trees) active.length x =
            subRoot (inducedSubPar P st.splay trees) active.length y) ∧
        halves + sumTreePhi P st' ≤ sumTreePhi P st + 12 * Nat.log 2 (2 * st.n + 1) ∧
        iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 5 := by
  intro res st' halves iters active st_exp
  rcases lctPathSummary_spec hL W htu hu hu_v htv hv hconn with
    ⟨_, trees2, Lv, depth2, ht2_mem, hW2, hact2_perm, hpp_v2, _, _, _,
      hpar2_u, hhead2_u, hlast2_v, _, _, hfp2, _, hoff2, hon2, hconn2_iff, hpot2, hH2⟩
  let t_exp := AuxTree.node v Lv AuxTree.leaf
  have hst_exp_n : st_exp.n = st.n := rfl
  have hinv_t := hW2.treesInv t_exp ht2_mem
  have happ := SplayState.applyTagNode_root_preserves hL hinv_t.nodup hinv_t.sub (t₀ := t₀)
  rcases happ with ⟨hsub3, hev3, hpp3, hout3⟩
  have hst'_eq : st' = LctState.mk st.n (SplayState.applyTagNode P st_exp.splay v t₀) st_exp.freeHead := rfl
  have hst_exp_eq : (lctPathSummaryCost P st u v).1 = st_exp := rfl
  have hev_on : SplayState.evalPairs P st'.splay t_exp false P.idTag =
      (SplayState.evalPairs P st_exp.splay t_exp false P.idTag).map (fun p => (p.1, P.actVal t₀ p.2)) := by
    have h1 : SplayState.evalPairs P st'.splay t_exp false P.idTag =
        SplayState.evalPairs P st_exp.splay t_exp false (P.compTag P.idTag t₀) := by
      simpa [hst'_eq, hst_exp_eq, Bool.false_eq_true] using hev3 false P.idTag
    rw [hL.compTag_id_left] at h1
    rw [h1, ← hL.compTag_id_right t₀, SplayState.evalPairs_compTag hL, hL.compTag_id_right]
  have hids_exp : treeIds P st'.splay t_exp = treeIds P st_exp.splay t_exp := by
    dsimp only [treeIds]
    rw [hev_on]
    simp [List.map_map]
  have hids_all : ∀ t ∈ trees2, treeIds P st'.splay t = treeIds P st_exp.splay t := fun t ht => by
    by_cases hteq : t = t_exp
    · subst hteq; exact hids_exp
    · exact treeIds_eq_of_evalPairs (SplayState.evalPairs_agree P (fun w hw => hout3 w fun hm =>
        hteq (flatMap_mem_unique hW2.activeNodup ht ht2_mem hw hm)) false P.idTag)
  have hpp_all : ∀ t ∈ trees2, (st'.splay.nodes t.rootId).ppar = (st_exp.splay.nodes t.rootId).ppar := by
    intro t ht
    by_cases hteq : t = t_exp
    · subst hteq; exact hpp3
    · exact congrArg SplayNode.ppar (hout3 t.rootId fun hm =>
        hteq (flatMap_mem_unique hW2.activeNodup ht ht2_mem (AuxTree.rootId_mem (hW2.treesNonEmpty t ht)) hm))
  have hpar3 : ∀ z, inducedSubPar P st'.splay trees2 z = inducedSubPar P st_exp.splay trees2 z := by
    intro z
    by_cases hz : z ∈ trees2.flatMap AuxTree.toList
    · rcases List.mem_flatMap.mp hz with ⟨t, ht, hzt⟩
      rw [inducedSubPar_eq_of_mem hW2.activeNodup ht hzt,
        inducedSubPar_eq_of_mem hW2.activeNodup ht hzt, hids_all t ht, hpp_all t ht]
    · rw [inducedSubPar_eq_zero_of_not_mem hz, inducedSubPar_eq_zero_of_not_mem hz]
  have hW3 : LctInvWith P st' trees2 freeList depth2 := by
    have hfl3 : FreeListInv st'.splay st'.freeHead freeList := by
      refine FreeListInv_agree hW2.freeListInv fun x hx => ?_
      have hdisj : x ∉ t_exp.toList := fun hm => by
        have hx_slot := hW2.freeValid x hx
        exact (hW2.partitionSlots x hx_slot).mp (List.mem_flatMap.mpr ⟨t_exp, ht2_mem, hm⟩) hx
      exact congrArg SplayNode.par (hout3 x hdisj)
    refine ⟨hW2.treesNonEmpty, ?_, hW2.activeNodup, fun x hx => hW2.activeValid x hx,
      fun w hw => hW2.verticesActive w hw, hW2.freeNodup,
      fun e he => hW2.freeValid e he,
      fun e he => hW2.partitionSlots e he, hfl3, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      by_cases hteq : t = t_exp
      · subst hteq; exact ⟨hinv_t.nodup, hsub3⟩
      · refine ⟨(hW2.treesInv t ht).nodup, SplayState.SubtreeInv_agree (hW2.treesInv t ht).sub fun w hw => ?_⟩
        exact (hout3 w fun hm => hteq (flatMap_mem_unique hW2.activeNodup ht ht2_mem hw hm)).symm
    · intro t ht hnz
      rw [hpp_all t ht] at hnz ⊢
      exact hW2.pparActive t ht hnz
    · intro x hx hpx
      rw [hpar3] at hpx ⊢
      exact hW2.acyclic x hx hpx
    · intro x hx hpx
      rw [hpar3] at hpx ⊢
      exact hW2.vertexParEdge x hx hpx
    · intro e he he_s
      rw [hpar3]
      exact hW2.edgeParVertex e he he_s
    · intro e he he_s
      have h1 := hW2.edgeUniqueChild e he he_s
      have hst_n' : st'.n = st_exp.n := rfl
      rw [hst_exp_eq] at h1
      rw [hst_n']
      simpa [hpar3] using h1
  have hpot_H3 := LctInvWith_canon_potentials hW3
  have hpot_H2 := LctInvWith_canon_potentials hW2
  have hv_eq : vSize P st'.splay (trees2.flatMap AuxTree.toList) (inducedSubPar P st'.splay trees2) trees2 =
      vSize P st_exp.splay (trees2.flatMap AuxTree.toList) (inducedSubPar P st_exp.splay trees2) trees2 :=
    vSize_congr_apply hids_all hpp_all hpar3
  have hPhi3 : sumTreePhi P st' = sumTreePhi P st_exp := by
    rw [hpot_H3.2, hv_eq, ← hst_exp_eq]
    exact hpot_H2.2.symm
  have hH3 : heavyCount P st' = heavyCount P st_exp := by
    rw [hpot_H3.1]
    have h2' : heavyCount P st_exp =
        heavyCountList P st_exp.splay (trees2.flatMap AuxTree.toList)
          (inducedSubPar P st_exp.splay trees2) trees2 := by
      rw [← hst_exp_eq]; exact hpot_H2.1
    rw [h2']
    exact heavyCountList_congr_applyTag hids_all hpp_all hpar3
  have hperm_trees2 : trees2.Perm (t_exp :: trees2.erase t_exp) := List.perm_cons_erase ht2_mem
  have hfp3 : (forestPairs P st'.splay trees2).Perm
      ((SplayState.evalPairs P st_exp.splay t_exp false P.idTag).map (fun p => (p.1, P.actVal t₀ p.2)) ++
        forestPairs P st_exp.splay (trees2.erase t_exp)) := by
    have h1 : (forestPairs P st'.splay trees2).Perm
        (SplayState.evalPairs P st'.splay t_exp false P.idTag ++
          forestPairs P st'.splay (trees2.erase t_exp)) := by
      simpa [forestPairs, List.flatMap_cons] using perm_flatMap_of_perm hperm_trees2
    have hoff_eq : forestPairs P st'.splay (trees2.erase t_exp) =
        forestPairs P st_exp.splay (trees2.erase t_exp) := by
      refine forestPairs_congr_trees fun c hc => ?_
      have hc_ne : c ≠ t_exp := ne_of_mem_erase_trees hW2.activeNodup hW2.treesNonEmpty hc
      have hc2 : c ∈ trees2 := List.mem_of_mem_erase hc
      exact SplayState.evalPairs_agree P (fun w hw => hout3 w fun hm =>
        hc_ne (flatMap_mem_unique hW2.activeNodup hc2 ht2_mem hw hm)) false P.idTag
    rw [hev_on, hoff_eq] at h1
    exact h1
  have hconn3_iff : ∀ x ∈ active, ∀ y ∈ active,
      subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar P st'.splay trees2) (trees2.flatMap AuxTree.toList).length y ↔
      subRoot (inducedSubPar P st.splay trees) active.length x =
        subRoot (inducedSubPar P st.splay trees) active.length y := by
    intro x hx y hy
    have hx_a : x ∈ trees.flatMap AuxTree.toList := hx
    have hy_a : y ∈ trees.flatMap AuxTree.toList := hy
    have hsx := subRoot_eq_of_LctInvWith_agree hW2 hW3 List.Perm.rfl (fun z => (hpar3 z).symm)
      (hact2_perm.symm.mem_iff.mp hx_a)
    have hsy := subRoot_eq_of_LctInvWith_agree hW2 hW3 List.Perm.rfl (fun z => (hpar3 z).symm)
      (hact2_perm.symm.mem_iff.mp hy_a)
    rw [hsx, hsy]
    exact hconn2_iff x hx y hy
  refine ⟨trees2, Lv, depth2, ht2_mem, hW3, hact2_perm, by rw [hpar3]; exact hpar2_u,
    by rw [hids_exp]; exact hhead2_u, by rw [hids_exp]; exact hlast2_v, hev_on, hpar3, hfp3, hfp2,
    hoff2, hon2, hconn3_iff, ?_, ?_⟩
  · have hpot2' : (lctPathSummaryCost P st u v).2.2.1 + sumTreePhi P st_exp ≤
        sumTreePhi P st + 12 * Nat.log 2 (2 * st.n + 1) := hpot2
    change halves + sumTreePhi P st' ≤ sumTreePhi P st + 12 * Nat.log 2 (2 * st.n + 1)
    rw [hPhi3]
    exact hpot2'
  · have hH2' : (lctPathSummaryCost P st u v).2.2.2 + heavyCount P st_exp ≤
        heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 5 := hH2
    change iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 5
    rw [hH3]
    exact hH2'

end
end MinCostFlow.LinkCut
