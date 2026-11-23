module

public import MinCostFlow.LinkCut.PathTree.NumOps
import MinCostFlow.LinkCut.ForestReversals

/-!
# The numbers of a cut fit

A cut reroots at `u` and exposes `v` (`rerootExpose_num`). When the path from `u` to `v` is one
edge, the exposed tree has three nodes. The cut pushes at the left child of `v`, splays the edge
node, and detaches its two children.

* The push keeps every route at most its old value (`pathTagRouteMagnitude_pushDown_le`), so the
  forest keeps its bounds (`replace_num`).
* The splay is `splay_num`.
* The detached edge node has no children, so its new summary is the summary of its own value.

`expose_num'` is `expose_num` with the shape of the exposed tree from `lctExpose_spec`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState
  MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

/-- Bounds move to another list of trees with the same values and no new nodes. -/
theorem ForestB.transfer {st : PathTreeState} {trees trees' : List AuxTree} {V R : ℤ}
    (hB : ForestB st trees V R)
    (hval : ∀ p ∈ forestPairs pathPayload st.splay trees', ValB V p.2)
    (hact : ∀ z ∈ trees'.flatMap AuxTree.toList, z ∈ trees.flatMap AuxTree.toList) :
    ForestB st trees' V R :=
  ⟨hval, fun c hc y hy => hB.chg' (hact y (List.mem_flatMap.mpr ⟨c, hc, hy⟩))⟩

/-- An expose, with the shape of the exposed tree. -/
theorem expose_num' {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {v : ℕ}
    (hv : v ∈ trees.flatMap AuxTree.toList) :
    ExposeOk (pathOk h K) pathPayload st v ∧
    ∃ trees' Lv, AuxTree.node v Lv .leaf ∈ trees' ∧
      LctInvWith pathPayload (lctExpose pathPayload st v) trees' fl d ∧
      ForestB (lctExpose pathPayload st v) trees' V R := by
  obtain ⟨hE, trees_e, -, hB_e, hact_e⟩ := expose_num W hB C hv
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨trees', Lv, ht', W', hperm, -, hfp, -⟩ := lctExpose_spec pathPayload_laws W htv hvt
  refine ⟨hE, trees', Lv, ht', W', hB_e.transfer (fun p hp => hB.val p (hfp.mem_iff.mp hp))
    (fun z hz => hact_e z (hperm.mem_iff.mp hz))⟩

/-- A change of one tree that keeps its values and does not raise its charges. -/
theorem replace_num {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) {t t' : AuxTree} {s' : SplayState (Option PathEdgeValue)
      PathSummary PathTag} (ht : t ∈ trees) (ht'_ne : t' ≠ .leaf)
    (ht'_inv : TreeInv pathPayload s' t') (hperm : t'.toList.Perm t.toList)
    (hev : evalPairs pathPayload s' t' false pathPayload.idTag =
      evalPairs pathPayload st.splay t false pathPayload.idTag)
    (hpp : (s'.nodes t'.rootId).ppar = (st.splay.nodes t.rootId).ppar)
    (hout : ∀ u ∉ t.toList, s'.nodes u = st.splay.nodes u)
    (hchg : ∀ y ∈ t'.toList, charge s' (2 * st.n + 1) y ≤ R) :
    LctInvWith pathPayload { st with splay := s' } (t' :: trees.erase t) fl d ∧
      ForestB { st with splay := s' } (t' :: trees.erase t) V R := by
  have W' := (replaceSameIds_spec W ht ht'_ne ht'_inv hperm hev hpp hout).1
  have hfp := forestPairs_perm_cons_erase (P := pathPayload) ht rfl hev hout W.activeNodup
  refine ⟨W', fun p hp => hB.val p (hfp.mem_iff.mp hp), fun c hc y hy => ?_⟩
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hchg y hy
  · have hct := List.mem_of_mem_erase hc
    have hdisj : ∀ u ∈ c.toList, u ∉ t.toList := fun u hu =>
      erase_flatMap_disjoint_of_nodup ht W.activeNodup u (List.mem_flatMap.mpr ⟨c, hc, hu⟩)
    change charge s' (2 * st.n + 1) y ≤ R
    rw [charge_keep (W.treesInv c hct) (W'.treesInv c (List.mem_cons_of_mem _ hc))
      (tree_size W hct) (fun u hu => hout u (hdisj u hu)) hy]
    exact hB.chg c hct y hy

/-- After the pointer writes of a detach, the node has no children and keeps its value. -/
theorem detachChildrenMid_self {α σ τ : Type*} (s : SplayState α σ τ) (x : ℕ) :
    ((detachChildrenMid s x).nodes x).left = 0 ∧ ((detachChildrenMid s x).nodes x).right = 0 ∧
      ((detachChildrenMid s x).nodes x).val = (s.nodes x).val := by
  have hval : ∀ (st : SplayState α σ τ) a z, ((clearUp st a).nodes z).val = (st.nodes z).val := by
    intro st a z
    unfold clearUp
    split_ifs
    · rfl
    · by_cases hz : z = a
      · subst hz
        simp only [SplayState.setPar, SplayState.setPpar, SplayState.nodes_updateNode_self]
      · simp only [SplayState.setPar, SplayState.setPpar, SplayState.nodes_updateNode_ne _ hz]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [detachChildrenMid, SplayState.setRight, SplayState.setLeft,
      SplayState.nodes_updateNode_self]
  rw [hval, hval]

/-- The numbers of a cut between two vertices fit. -/
theorem cut_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {u v : ℕ}
    (hu : isVertex st.n u) (hv : isVertex st.n v) :
    CutOk (pathOk h K) pathPayload st u v := by
  obtain ⟨hRok, trees1, d1, W1, hB1⟩ := reroot_num W hB C hu
  have hv1 := isVertex_mem_active W1 hv
  obtain ⟨hEok, trees2, Lv, ht2, W2, hB2⟩ := expose_num' W1 hB1 C hv1
  change LctInvWith pathPayload (cutMid pathPayload st u v) trees2 fl d1 at W2
  change ForestB (cutMid pathPayload st u v) trees2 V R at hB2
  have C2 : NumCtx h K (2 * (cutMid pathPayload st u v).n + 1) V R := C
  set t_exp := AuxTree.node v Lv .leaf with ht_exp
  have hT2 := forestB_treeB W2 hB2 ht2
  have ht2_inv := hT2.inv
  have hl0_mem : ((cutMid pathPayload st u v).splay.nodes v).sz = 3 →
      cutL0 pathPayload st u v ∈ t_exp.toList := by
    intro hsz
    have hcnt : (AuxTree.node v Lv AuxTree.leaf).countNodes = 3 := by
      rw [← hsz]; exact ht2_inv.sub.2.2.2.2.2.1.symm
    have hLv : Lv ≠ .leaf := by
      rintro rfl; simp [AuxTree.countNodes] at hcnt
    have hl : cutL0 pathPayload st u v = Lv.rootId := ht2_inv.sub.2.1
    rw [hl]
    simp [t_exp, AuxTree.toList, AuxTree.rootId_mem hLv]
  refine ⟨⟨hRok, hEok⟩, fun hsz => pushDownOk_tree C2 hT2 (hl0_mem hsz), fun hsz _ => ?_⟩
  have hl0 := hl0_mem hsz
  obtain ⟨hpd_inv, hpd_perm, -, -, hpd_path, -, -, -, -, hpd_ppar, hpd_out, hpd_ev⟩ :=
    pushDown_preserves_TreeInv pathPayload_laws ht2_inv hl0
  set t_pd := pushDownTree (cutMid pathPayload st u v).splay (cutL0 pathPayload st u v) t_exp
  change TreeInv pathPayload (cutPd pathPayload st u v) t_pd at hpd_inv
  have hpd_ne : t_pd ≠ .leaf := by
    intro h
    have h1 := hpd_perm.length_eq
    rw [h] at h1
    simp [t_exp, AuxTree.toList] at h1
  have hk_pd : t_pd.countNodes ≤ 2 * st.n + 1 := by
    rw [countNodes_perm hpd_perm]; exact hT2.size
  have hchg : ∀ y ∈ t_pd.toList, charge (cutPd pathPayload st u v) (2 * st.n + 1) y ≤ R := by
    intro y hy
    have hy' := hpd_perm.mem_iff.mp hy
    rw [charge_eq_route hpd_inv hy hk_pd]
    unfold route
    rw [hpd_path y]
    refine (pathTagRouteMagnitude_pushDown_le ht2_inv.nodup ht2_inv.sub hl0 hy').trans ?_
    have := hT2.chg y hy'
    rwa [charge_eq_route ht2_inv hy' hT2.size] at this
  obtain ⟨W3, hB3⟩ := replace_num W2 hB2 ht2 hpd_ne hpd_inv hpd_perm hpd_ev hpd_ppar hpd_out hchg
  have hne_mem : cutNe pathPayload st u v ∈ t_pd.toList := by
    unfold cutNe
    split_ifs with hr
    · exact hpd_perm.mem_iff.mpr hl0
    · exact (SubtreeInv.child_mem hpd_inv.sub (hpd_perm.mem_iff.mpr hl0)).2 hr
  obtain ⟨hsOk, t', -, -, hperm', -, -, -, W4, hB4, -⟩ :=
    splay_num W3 hB3 C List.mem_cons_self hne_mem
  refine ⟨hsOk, fun hne0 => ?_⟩
  set s_cut := splay pathPayload (cutPd pathPayload st u v) (2 * st.n + 1)
    (cutNe pathPayload st u v)
  have hb : PathNodeBound ((2 * st.n + 1 : ℕ) * (V + 2 * R))
      (s_cut.nodes (cutNe pathPayload st u v)) :=
    node_bound W4 hB4 C (List.mem_flatMap.mpr ⟨t', List.mem_cons_self,
      hperm'.mem_iff.mpr hne_mem⟩)
  obtain ⟨hl, hr, hval⟩ := detachChildrenMid_self s_cut (cutNe pathPayload st u v)
  change PathSummaryFits h K (pullSum pathPayload
    (detachChildrenMid s_cut (cutNe pathPayload st u v)) (cutNe pathPayload st u v))
  unfold pullSum
  rw [hl, hr, hval]
  simp only [↓reduceIte]
  rw [pathPayload_laws.combine_empty_right, pathPayload_laws.combine_empty_left]
  have hB0 := bound_nonneg hb
  have f {z : ℤ} (hz : |z| ≤ (2 * st.n + 1 : ℕ) * (V + 2 * R)) : Num.Fits h K z :=
    fits_of_abs (by linarith) C.room
  change PathSummaryFits h K (PathSummary.single (s_cut.nodes (cutNe pathPayload st u v)).val)
  cases hvv : (s_cut.nodes (cutNe pathPayload st u v)).val with
  | none =>
    refine ⟨f ?_, f ?_, trivial⟩ <;>
      simp only [PathSummary.single, PathSummary.empty, abs_zero] <;> linarith
  | some e =>
    obtain ⟨h1, h2, -, h4⟩ := hb.1 e hvv
    exact ⟨f h1, f h2, f h4⟩

end MinCostFlow.LinkCut.PathTree
