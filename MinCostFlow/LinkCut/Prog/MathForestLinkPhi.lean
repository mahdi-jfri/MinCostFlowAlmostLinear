module

public import MinCostFlow.LinkCut.Prog.MathForestLinkInvs

/-!
# Potential Bound for `link`

Proves the pure reachability and potential increase bound for the `link` splice:
- `link_reachesIn_mono`: every node reachable before `link` remains reachable afterwards.
- `link_evalInorder_no_tv_reach`: starting from `v + 1` under `mem₃` stays within `t_v.toList`.
- `link_reachesIn_off_tv`: nodes off `t_v` (and `≠ ed`) do not gain new reaching nodes.
- `link_phi_le`: `lctPhi` increases by at most `2 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_HEAVY L`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LinkPhi

private lemma list_filter_length_mono {α : Type*} (xs : List α) (p q : α → Bool)
    (hpq : ∀ a ∈ xs, p a = true → q a = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      have ih' := ih (fun x hx => hpq x (by simp [hx]))
      by_cases hpa : p a = true
      · have hqa : q a = true := hpq a (by simp) hpa
        simp [hpa, hqa, ih']
      · have hpf : p a = false := Bool.eq_false_iff.2 hpa
        cases hqa : q a <;> simp [hpf, hqa] <;> omega

private lemma link_phi_arith {sp_p sp_3 k2r ch hc_p hc_3 : ℕ}
    (hsp : sp_p ≤ sp_3 + k2r) (hhc : hc_p ≤ hc_3 + 1) :
    sp_p + ch * hc_p ≤ sp_3 + ch * hc_3 + k2r + ch := by
  have h2 : ch * hc_p ≤ ch * (hc_3 + 1) := Nat.mul_le_mul_left ch hhc
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

/-- Monotonicity of `reachesIn` under `link`: since `par₃ ed = 0` and `par₃ u1 = 0`, any
non-zero `iterParent` chain under `par₃` uses neither `ed` nor `u1` before its last step. -/
theorem link_reachesIn_mono {par₃ par_p : ℕ → ℕ} {cap ed u1 v1 q y : ℕ}
    (hpar_eq : ∀ z, par_p z = if z = ed then v1 else if z = u1 then ed else par₃ z)
    (hp0 : par₃ 0 = 0) (hp_ed : par₃ ed = 0) (hp_u : par₃ u1 = 0)
    (hy1 : 1 ≤ y) (hr : reachesIn par₃ cap q y = true) :
    reachesIn par_p cap q y = true := by
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at hr ⊢
  rcases hr with ⟨hq, ⟨k, hk_lt, hk_eq⟩⟩
  refine ⟨hq, ⟨k, hk_lt, ?_⟩⟩
  have hchain : ∀ m q', iterParent par₃ m q' ≠ 0 → iterParent par_p m q' = iterParent par₃ m q' := by
    intro m
    induction m with
    | zero => intro _ _; rfl
    | succ m ih =>
        intro q' hnz
        rw [iterParent_succ_right] at hnz
        rw [iterParent_succ_right, iterParent_succ_right]
        have hm_nz : iterParent par₃ m q' ≠ 0 := fun h0 => by
          rw [h0, hp0] at hnz; exact hnz rfl
        have hm_ne_ed : iterParent par₃ m q' ≠ ed := fun hed => by
          rw [hed, hp_ed] at hnz; exact hnz rfl
        have hm_ne_u : iterParent par₃ m q' ≠ u1 := fun hu => by
          rw [hu, hp_u] at hnz; exact hnz rfl
        rw [ih q' hm_nz, hpar_eq, ite_eq_right hm_ne_ed, ite_eq_right hm_ne_u]
  rw [hchain k q (by rw [hk_eq]; omega), hk_eq]

/-- Starting at `v + 1` in `mem₃`, iterated auxiliary parents remain in `0` or `t_v.toList`
when `nodeField mem₃ nb (v + 1) OFF_PPAR = 0`. -/
theorem link_evalInorder_no_tv_reach {w h L P b n v : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_v : AuxTree} {t_tv : AuxTree} {trees₃ : List AuxTree} {mem₃ : ℕ → ℕ}
    (htv_eq : t_tv = AuxTree.node (v + 1) l_v .leaf)
    (htv_mem : t_tv ∈ trees₃)
    (hi₃ : LctExposeInvs w h L P b n freeEdges edgeMap trees₃ mem₃)
    (hpp_v3 : nodeField mem₃ (lctNodesBase b) (v + 1) OFF_PPAR = 0) :
    ∀ m, iterParent (lctAuxParent mem₃ (lctNodesBase b) (lctCap n)) m (v + 1) = 0 ∨
      iterParent (lctAuxParent mem₃ (lctNodesBase b) (lctCap n)) m (v + 1) ∈ t_tv.toList := by
  let nb := lctNodesBase b
  let cap := lctCap n
  let par := lctAuxParent mem₃ nb cap
  have hseq_eq : lctTreeSeq mem₃ nb cap t_tv.rootId = t_tv.evalInorder (revFlag mem₃ nb) false :=
    hi₃.sf.lctTreeSeq_eq htv_mem
  intro m
  induction m with
  | zero =>
      right
      rw [iterParent, htv_eq]
      simp [AuxTree.toList]
  | succ m ih =>
      rw [iterParent_succ_right]
      rcases ih with h0 | hmem
      · left; exact h0 ▸ lctAuxParent_zero mem₃ nb cap
      · have hmem_seq : iterParent par m (v + 1) ∈ lctTreeSeq mem₃ nb cap t_tv.rootId := by
          rw [hseq_eq]
          exact (t_tv.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.2 hmem
        rcases List.getElem_of_mem hmem_seq with ⟨i, hi_lt, hi_eq⟩
        have hp := lctAuxParent_of_tree hi₃.sf hi₃.ppar_le_cap htv_mem i hi_lt
        rw [hi_eq] at hp
        by_cases hi0 : i = 0
        · simp only [hi0, ↓reduceIte, htv_eq, AuxTree.rootId] at hp
          left; exact hp.trans hpp_v3
        · have him1_lt : i - 1 < (lctTreeSeq mem₃ nb cap t_tv.rootId).length := by omega
          simp only [hi0, ↓reduceIte] at hp
          have hget : (lctTreeSeq mem₃ nb cap t_tv.rootId)[i - 1]! =
              (lctTreeSeq mem₃ nb cap t_tv.rootId)[i - 1] := by
            simp [getElem!_def, List.getElem?_eq_getElem him1_lt]
          rw [hget] at hp
          right
          rw [hp]
          have hmem_prev : (lctTreeSeq mem₃ nb cap t_tv.rootId)[i - 1] ∈
              t_tv.evalInorder (revFlag mem₃ nb) false := by
            rw [← hseq_eq]; exact List.getElem_mem him1_lt
          exact (t_tv.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.1 hmem_prev

/-- For `1 ≤ y ≤ cap`, `y ≠ ed`, and `y` unreachable from `v1` in `par₃`, `y` gains no new
reaching nodes under `par_p`. -/
theorem link_reachesIn_off_tv {par₃ par_p : ℕ → ℕ} {cap ed u1 v1 q y : ℕ}
    (hpar_eq : ∀ z, par_p z = if z = ed then v1 else if z = u1 then ed else par₃ z)
    (hp0_p : par_p 0 = 0)
    (hle_p : ∀ z, 1 ≤ z → z ≤ cap → par_p z ≤ cap)
    (hy1 : 1 ≤ y) (hy2 : y ≤ cap) (hy_ne_ed : y ≠ ed)
    (hy_off : ∀ m, iterParent par₃ m v1 ≠ y)
    (hr_p : reachesIn par_p cap q y = true) :
    reachesIn par₃ cap q y = true := by
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at hr_p ⊢
  rcases hr_p with ⟨hq_bd, ⟨k, hk_lt, hk_eq⟩⟩
  refine ⟨hq_bd, ⟨k, hk_lt, ?_⟩⟩
  have hgo : ∀ m y', 1 ≤ y' → y' ≤ cap → y' ≠ ed → (∀ j, iterParent par₃ j v1 ≠ y') →
      iterParent par_p m q = y' → iterParent par₃ m q = y' := by
    intro m
    induction m with
    | zero =>
        intro y' _ _ _ _ hm
        simpa [iterParent] using hm
    | succ m ih =>
        intro y' hy1' hy2' hne_ed' hoff' hm
        rw [iterParent_succ_right] at hm ⊢
        set z := iterParent par_p m q
        have hz_le : z ≤ cap := iterParent_le_cap hp0_p hle_p hq_bd.2 m
        have hz_nz : z ≠ 0 := fun h0 => by
          rw [h0, hp0_p] at hm; omega
        have hz_ne_ed : z ≠ ed := fun hed => by
          rw [hed, hpar_eq ed, ite_eq_left rfl] at hm
          exact hoff' 0 hm
        have hz_ne_u : z ≠ u1 := fun hu => by
          rw [hu, hpar_eq u1, ite_eq_right (hu ▸ hz_ne_ed), ite_eq_left rfl] at hm
          exact hne_ed' hm.symm
        have hpar_z : par₃ z = y' := by
          rw [hpar_eq z, ite_eq_right hz_ne_ed, ite_eq_right hz_ne_u] at hm
          exact hm
        have hz_off : ∀ j, iterParent par₃ j v1 ≠ z := fun j hj => by
          have hj1 : iterParent par₃ (j + 1) v1 = y' := by
            rw [iterParent_succ_right, hj, hpar_z]
          exact hoff' (j + 1) hj1
        rw [ih z (by omega) hz_le hz_ne_ed hz_off rfl, hpar_z]
  exact hgo k y hy1 hy2 hy_ne_ed hy_off hk_eq

/-- Potential bound for the `link` splice: `lctPhi` increases by at most
`2 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_HEAVY L`. -/
theorem link_phi_le {w h L P b n u v ed : ℕ}
    {free' : List ℕ} {edgeMap edgeMap' : List (ℕ × ForestEdge)}
    {r_u l_v : AuxTree} {rest_fin : List AuxTree} {mem₃ mem_p : ℕ → ℕ}
    (hi₃ : LctExposeInvs w h L P b n (ed :: free') edgeMap
      (AuxTree.node (u + 1) .leaf r_u :: AuxTree.node (v + 1) l_v .leaf ::
        AuxTree.node ed .leaf .leaf :: rest_fin) mem₃)
    (hi_p : LctExposeInvs w h L P b n free' edgeMap'
      (AuxTree.node ed .leaf (AuxTree.node (u + 1) .leaf r_u) ::
        AuxTree.node (v + 1) l_v .leaf :: rest_fin) mem_p)
    (hpar_eq : ∀ z, lctAuxParent mem_p (lctNodesBase b) (lctCap n) z =
      if z = ed then v + 1 else if z = u + 1 then ed else
        lctAuxParent mem₃ (lctNodesBase b) (lctCap n) z)
    (hrest_agree : ∀ s ∈ rest_fin,
      nodeField mem_p (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₃ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_p (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₃ (lctNodesBase b)) false)
    (hpp_u3 : nodeField mem₃ (lctNodesBase b) (u + 1) OFF_PPAR = 0)
    (hpar_u3 : lctAuxParent mem₃ (lctNodesBase b) (lctCap n) (u + 1) = 0)
    (hpp_v3 : nodeField mem₃ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hpp_vp : nodeField mem_p (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hpp_ed_p : nodeField mem_p (lctNodesBase b) ed OFF_PPAR = v + 1) :
    lctPhi L mem_p b n ≤
      lctPhi L mem₃ b n + 2 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_HEAVY L := by
  let nb := lctNodesBase b
  let cap := lctCap n
  let t_u := AuxTree.node (u + 1) .leaf r_u
  let t_v := AuxTree.node (v + 1) l_v .leaf
  let t_ed := AuxTree.node ed .leaf t_u
  let trees₃ := t_u :: t_v :: AuxTree.node ed .leaf .leaf :: rest_fin
  let trees_fin := t_ed :: t_v :: rest_fin
  have hed_bd := hi₃.freeNodeOk ed List.mem_cons_self
  have hnd3 : (trees₃.flatMap AuxTree.toList).Nodup :=
    hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hdisj_tu_tv : ∀ x ∈ t_u.toList, x ∉ t_v.toList := fun x hx hxv => by
    have h1 := hnd3
    dsimp only [trees₃] at h1
    rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons] at h1
    exact h1.2.2 x hx x (List.mem_append.2 (Or.inl hxv)) rfl
  have hv_nin_tu : v + 1 ∉ t_u.toList := fun hm =>
    hdisj_tu_tv (v + 1) hm (by simp [t_v, AuxTree.toList])
  have hed_nin_tv : ed ∉ t_v.toList := fun hm => by
    have h1 := hnd3
    dsimp only [trees₃] at h1
    rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append,
      List.flatMap_cons] at h1
    exact h1.2.1.2.2 ed hm ed (List.mem_append.2 (Or.inl (by simp [AuxTree.toList]))) rfl
  have hdisj_rest : ∀ s ∈ rest_fin, ∀ z ∈ s.toList, z ≠ ed ∧ z ∉ t_v.toList := by
    intro s hs z hz
    have hrest_flat : z ∈ (rest_fin.flatMap AuxTree.toList) := List.mem_flatMap.2 ⟨s, hs, hz⟩
    have h1 := hnd3
    dsimp only [trees₃] at h1
    rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append,
      List.flatMap_cons, List.nodup_append] at h1
    refine ⟨fun hze => ?_, fun hzv => ?_⟩
    · exact h1.2.1.2.1.2.2 ed (by simp [AuxTree.toList]) z (hze ▸ hrest_flat) hze.symm
    · exact h1.2.1.2.2 z hzv z (List.mem_append.2 (Or.inr hrest_flat)) rfl
  have hreach_mono : ∀ q y, 1 ≤ y →
      reachesIn (lctAuxParent mem₃ nb cap) cap q y = true →
      reachesIn (lctAuxParent mem_p nb cap) cap q y = true := fun q y hy1 hr =>
    link_reachesIn_mono hpar_eq (lctAuxParent_zero mem₃ nb cap)
      (hi₃.subdivOk.2.1 ed List.mem_cons_self) hpar_u3 hy1 hr
  have hrep_mono : ∀ y, 1 ≤ y → lctRepSize mem₃ nb cap y ≤ lctRepSize mem_p nb cap y :=
    fun y hy1 => list_filter_length_mono _ _ _ fun q _ hq => hreach_mono q y hy1 hq
  have hv_reach : ∀ m, iterParent (lctAuxParent mem₃ nb cap) m (v + 1) = 0 ∨
      iterParent (lctAuxParent mem₃ nb cap) m (v + 1) ∈ t_v.toList :=
    link_evalInorder_no_tv_reach (t_tv := t_v) rfl (by simp [t_v]) hi₃ hpp_v3
  have hrep_eq_off : ∀ y, 1 ≤ y → y ≤ cap → y ≠ ed → y ∉ t_v.toList →
      lctRepSize mem_p nb cap y = lctRepSize mem₃ nb cap y := by
    intro y hy1 hy2 hne_ed hnin_tv
    apply Nat.le_antisymm _ (hrep_mono y hy1)
    apply list_filter_length_mono
    intro q _ hq
    refine link_reachesIn_off_tv hpar_eq (lctAuxParent_zero mem_p nb cap)
      (fun z _ _ => lctAuxParent_le_cap mem_p nb cap z)
      hy1 hy2 hne_ed (fun m hm => ?_) hq
    rcases hv_reach m with h0 | hmem
    · omega
    · exact hnin_tv (hm ▸ hmem)
  have hseq_rest : ∀ s ∈ rest_fin,
      lctTreeSeq mem_p nb cap s.rootId = lctTreeSeq mem₃ nb cap s.rootId := by
    intro s hs
    have hs_p : s ∈ trees_fin := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)
    have hs_3 : s ∈ trees₃ :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
    rw [hi_p.sf.lctTreeSeq_eq hs_p, hi₃.sf.lctTreeSeq_eq hs_3, (hrest_agree s hs).2]
  have hdash_rest : ∀ s ∈ rest_fin,
      dashedChildSize mem_p nb cap s.rootId = dashedChildSize mem₃ nb cap s.rootId := by
    intro s hs
    have hs_3 : s ∈ trees₃ :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
    have hs_ok3 := hi₃.sf.trees_ok s hs_3
    have hne : lctTreeSeq mem₃ nb cap s.rootId ≠ [] := by
      rw [hi₃.sf.lctTreeSeq_eq hs_3]
      exact auxTree_eval_ne_nil_of_ne_leaf hs_ok3.1
    simp only [dashedChildSize, hseq_rest s hs]
    cases hseq : lctTreeSeq mem₃ nb cap s.rootId with
    | nil => exact absurd hseq hne
    | cons hd tl =>
        have hhd_mem : hd ∈ s.toList := by
          have : hd ∈ s.evalInorder (revFlag mem₃ nb) false := by
            rw [← hi₃.sf.lctTreeSeq_eq hs_3, hseq]; simp
          exact (s.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.1 this
        have hhd_bd := hs_ok3.2.2.nodup_perm_mem hhd_mem
        have hhd_disj := hdisj_rest s hs hd hhd_mem
        exact hrep_eq_off hd hhd_bd.1 hhd_bd.2 hhd_disj.1 hhd_disj.2
  have hvsize_eq : ∀ y, 1 ≤ y → y ≤ cap → y ≠ v + 1 →
      lctVSize mem_p nb cap y = lctVSize mem₃ nb cap y := by
    intro y hy1 hy2 hney
    simp only [lctVSize]
    rw [list_filter_map_sum_ite, list_filter_map_sum_ite]
    have hp_p := hi_p.sf.auxRootIds_perm.map fun r =>
      if decide (nodeField mem_p nb r OFF_PPAR = y) = true then dashedChildSize mem_p nb cap r else 0
    have hp_3 := hi₃.sf.auxRootIds_perm.map fun r =>
      if decide (nodeField mem₃ nb r OFF_PPAR = y) = true then dashedChildSize mem₃ nb cap r else 0
    rw [hp_p.sum_eq, hp_3.sum_eq]
    have hr1 : (AuxTree.node ed .leaf (AuxTree.node (u + 1) .leaf r_u)).rootId = ed := rfl
    have hr2 : (AuxTree.node (v + 1) l_v .leaf).rootId = v + 1 := rfl
    have hr3 : (AuxTree.node (u + 1) .leaf r_u).rootId = u + 1 := rfl
    have hr4 : (AuxTree.node ed .leaf .leaf).rootId = ed := rfl
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, decide_eq_true_eq]
    rw [hr1, hr2, hr3, hr4]
    dsimp only [nb] at hpp_ed_p hpp_vp hpp_u3 hpp_v3 ⊢
    rw [hpp_ed_p, hpp_vp, hpp_u3, hpp_v3, hed_bd.2.2.2.1]
    have hne_vy : (v + 1 = y) = False := eq_false hney.symm
    have hne_0y : (0 = y) = False := eq_false (by omega)
    simp only [hne_vy, hne_0y, ↓reduceIte, Nat.zero_add]
    congr 1; apply List.map_congr_left
    intro s hs
    have hd_s := hdash_rest s hs
    dsimp only [nb] at hd_s
    simp only [(hrest_agree s hs).1, hd_s]
  have hsplay_le : splayMemPhi (K_SPLAY_STEP L) mem_p nb cap (lctVSize mem_p nb cap) ≤
      splayMemPhi (K_SPLAY_STEP L) mem₃ nb cap (lctVSize mem₃ nb cap) +
        2 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) := by
    rw [splayMemPhi_eq_sum hi_p.sf, splayMemPhi_eq_sum hi₃.sf]
    have hrest_phi :
        (rest_fin.map (AuxTree.treePhi (lctVSize mem_p nb cap))).sum =
        (rest_fin.map (AuxTree.treePhi (lctVSize mem₃ nb cap))).sum := by
      congr 1; apply List.map_congr_left
      intro s hs
      have hs_3 : s ∈ trees₃ :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
      have hs_tok := (hi₃.sf.trees_ok s hs_3).2.2
      exact auxTree_treePhi_congr fun z hz =>
        hvsize_eq z (hs_tok.nodup_perm_mem hz).1 (hs_tok.nodup_perm_mem hz).2
          (fun heq => (hdisj_rest s hs z hz).2 (by rw [heq]; simp [t_v, AuxTree.toList]))
    have htu_phi : t_u.treePhi (lctVSize mem_p nb cap) = t_u.treePhi (lctVSize mem₃ nb cap) := by
      have htu_tok := (hi₃.sf.trees_ok t_u (by simp [t_u])).2.2
      exact auxTree_treePhi_congr fun z hz =>
        hvsize_eq z (htu_tok.nodup_perm_mem hz).1 (htu_tok.nodup_perm_mem hz).2
          (fun heq => hv_nin_tu (heq ▸ hz))
    have hted_rank : t_ed.rank (lctVSize mem_p nb cap) ≤ Nat.log 2 (n + 2) + 1 :=
      treeRank_le_log_of_invs hi_p.sf hi_p.subdivOk.1 hi_p.auxPathOk (t := t_ed)
        (by dsimp only [t_ed, t_u]; simp)
    have htv_rank : t_v.rank (lctVSize mem_p nb cap) ≤ Nat.log 2 (n + 2) + 1 :=
      treeRank_le_log_of_invs hi_p.sf hi_p.subdivOk.1 hi_p.auxPathOk (t := t_v)
        (by dsimp only [t_v]; simp)
    have hlv_phi : l_v.treePhi (lctVSize mem_p nb cap) = l_v.treePhi (lctVSize mem₃ nb cap) := by
      have htv_tok := (hi₃.sf.trees_ok t_v (by simp [t_v])).2.2
      have htv_nd := mem_nodup_of_flatMap_nodup hnd3 (s := t_v) (by simp [trees₃, t_v])
      have hv_nin_lv : v + 1 ∉ l_v.toList := auxTree_nodup_id_nin_left htv_nd
      exact auxTree_treePhi_congr fun z hz => by
        have hz_tv : z ∈ t_v.toList := by simp [t_v, AuxTree.toList, hz]
        exact hvsize_eq z (htv_tok.nodup_perm_mem hz_tv).1 (htv_tok.nodup_perm_mem hz_tv).2
          (fun heq => hv_nin_lv (heq ▸ hz))
    have hsum_le :
        (trees_fin.map (AuxTree.treePhi (lctVSize mem_p nb cap))).sum ≤
        (trees₃.map (AuxTree.treePhi (lctVSize mem₃ nb cap))).sum + 2 * (Nat.log 2 (n + 2) + 1) := by
      simp only [trees_fin, trees₃, List.map_cons, List.sum_cons, hrest_phi]
      have h1 : t_ed.treePhi (lctVSize mem_p nb cap) =
          t_ed.rank (lctVSize mem_p nb cap) + t_u.treePhi (lctVSize mem₃ nb cap) := by
        simp [t_ed, AuxTree.treePhi, htu_phi]
      have h2 : t_v.treePhi (lctVSize mem_p nb cap) =
          t_v.rank (lctVSize mem_p nb cap) + l_v.treePhi (lctVSize mem₃ nb cap) := by
        simp [t_v, AuxTree.treePhi, hlv_phi]
      have h3 : l_v.treePhi (lctVSize mem₃ nb cap) ≤ t_v.treePhi (lctVSize mem₃ nb cap) := by
        simp [t_v, AuxTree.treePhi]
      rw [h1, h2]
      set r1 := t_ed.rank (lctVSize mem_p nb cap)
      set r2 := t_v.rank (lctVSize mem_p nb cap)
      set p_u := t_u.treePhi (lctVSize mem₃ nb cap)
      set p_v := t_v.treePhi (lctVSize mem₃ nb cap)
      set p_l := l_v.treePhi (lctVSize mem₃ nb cap)
      set p_e := (AuxTree.node ed .leaf .leaf).treePhi (lctVSize mem₃ nb cap)
      set p_r := (rest_fin.map (AuxTree.treePhi (lctVSize mem₃ nb cap))).sum
      omega
    have hmul := Nat.mul_le_mul_left (K_SPLAY_STEP L) hsum_le
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (K_SPLAY_STEP L) 2] at hmul
    exact hmul
  have hheavy_le : lctHeavyCount mem_p nb cap ≤ lctHeavyCount mem₃ nb cap + 1 := by
    simp only [lctHeavyCount, list_filter_length_ite]
    have hp_p := hi_p.sf.auxRootIds_perm.map fun r =>
      if isHeavyRoot mem_p nb cap r = true then 1 else 0
    have hp_3 := hi₃.sf.auxRootIds_perm.map fun r =>
      if isHeavyRoot mem₃ nb cap r = true then 1 else 0
    rw [hp_p.sum_eq, hp_3.sum_eq]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def]
    have hv_not_heavy : isHeavyRoot mem_p nb cap (AuxTree.node (v + 1) l_v .leaf).rootId = false := by
      dsimp only [nb]
      simp [isHeavyRoot, AuxTree.rootId, hpp_vp]
    have hrest_heavy :
        (rest_fin.map (fun s => if isHeavyRoot mem_p nb cap s.rootId = true then 1 else 0)).sum ≤
        (rest_fin.map (fun s => if isHeavyRoot mem₃ nb cap s.rootId = true then 1 else 0)).sum := by
      apply List.sum_le_sum
      intro s hs
      by_cases hp : isHeavyRoot mem_p nb cap s.rootId = true
      · have hs_3 : s ∈ trees₃ :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
        have hs_ok3 := hi₃.sf.trees_ok s hs_3
        have hp' := hp
        simp only [isHeavyRoot, Bool.and_eq_true, decide_eq_true_eq, hseq_rest s hs] at hp'
        have hpp_s := (hrest_agree s hs).1
        dsimp only [nb, cap] at hp'
        rw [hpp_s] at hp'
        rcases hp' with ⟨hpp_bd, hlt⟩
        have hheavy3 : isHeavyRoot mem₃ nb cap s.rootId = true := by
          dsimp only [nb, cap]
          simp only [isHeavyRoot, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hpp_bd, ?_⟩
          cases hseq : lctTreeSeq mem₃ (lctNodesBase b) (lctCap n) s.rootId with
          | nil =>
              have : lctTreeSeq mem₃ (lctNodesBase b) (lctCap n) s.rootId = [] := hseq
              rw [this] at hlt
              simp at hlt
          | cons hd tl =>
              rw [hseq] at hlt
              simp only [decide_eq_true_eq] at hlt ⊢
              have hhd_mem : hd ∈ s.toList := by
                have : hd ∈ s.evalInorder (revFlag mem₃ nb) false := by
                  rw [← hi₃.sf.lctTreeSeq_eq hs_3]
                  rw [hseq]
                  simp
                exact (s.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.1 this
              have hhd_bd := hs_ok3.2.2.nodup_perm_mem hhd_mem
              have hhd_disj := hdisj_rest s hs hd hhd_mem
              have hrep_hd := hrep_eq_off hd hhd_bd.1 hhd_bd.2 hhd_disj.1 hhd_disj.2
              have hrep_pp := hrep_mono (nodeField mem₃ (lctNodesBase b) s.rootId OFF_PPAR) hpp_bd.1
              dsimp only [nb, cap] at hrep_hd hrep_pp hlt ⊢
              omega
        have hp_b : isHeavyRoot mem_p (lctNodesBase b) cap s.rootId = true := hp
        have h3_b : isHeavyRoot mem₃ (lctNodesBase b) cap s.rootId = true := hheavy3
        rw [ite_eq_left hp_b, ite_eq_left h3_b]
      · have hp_f : isHeavyRoot mem_p (lctNodesBase b) cap s.rootId ≠ true := hp
        rw [ite_eq_right hp_f]
        omega
    have hroot_le : (if isHeavyRoot mem_p nb cap t_ed.rootId = true then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    dsimp only [t_ed, t_u, t_v] at hv_not_heavy hroot_le ⊢
    simp only [hv_not_heavy, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    set s1 := (rest_fin.map (fun s => if isHeavyRoot mem_p nb cap s.rootId = true then 1 else 0)).sum
    set s2 := (rest_fin.map (fun s => if isHeavyRoot mem₃ nb cap s.rootId = true then 1 else 0)).sum
    set b_ed := if isHeavyRoot mem_p nb cap (AuxTree.node ed .leaf (AuxTree.node (u + 1) .leaf r_u)).rootId = true then 1 else 0
    omega
  unfold lctPhi
  exact link_phi_arith hsplay_le hheavy_le

end LinkPhi

end MinCostFlow.LinkCut.Prog
