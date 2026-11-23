module

public import MinCostFlow.LinkCut.Prog.MathForestCutAfter

/-!
# Potential Bound for `cut`

After `reroot x` and `expose y`, the edge node `ed` sits between `x + 1` and `y + 1` in one
auxiliary tree. The cut write splits this tree into three single nodes. This file shows that
the potential `lctPhi` grows by at most `2 * C_HEAVY L` in this step.

The idea is simple. The write sets the represented parent of `x + 1`, `ed` and `y + 1` to `0`
and leaves every other parent alone. A chain of parents that enters these three nodes never
leaves them except to `0`. So every node outside them keeps the same set of descendants, and
all virtual sizes stay the same. The splay part then only loses rank. A dashed edge can turn
heavy only if its parent is `x + 1` or `y + 1`, and each node has at most one heavy child.

- `cut_repSize_eq`: represented sizes agree outside a set closed under the old parent map.
- `heavy_child_unique`: two disjoint trees with the same path parent are not both heavy.
- `cut_phi_le`: the potential bound.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutPhi

/-- A chain under a parent map that only loses links is also a chain under the old map. -/
theorem cut_reachesIn_of_new {par₃ par_w : ℕ → ℕ} {cap q y : ℕ}
    (hpar : ∀ z, par_w z = 0 ∨ par_w z = par₃ z) (hp0 : par_w 0 = 0) (hy1 : 1 ≤ y)
    (hr : reachesIn par_w cap q y = true) : reachesIn par₃ cap q y = true := by
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at hr ⊢
  rcases hr with ⟨hq, ⟨k, hk_lt, hk_eq⟩⟩
  refine ⟨hq, ⟨k, hk_lt, ?_⟩⟩
  have hchain : ∀ m, iterParent par_w m q ≠ 0 →
      iterParent par_w m q = iterParent par₃ m q := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hnz
        rw [iterParent_succ_right] at hnz
        rw [iterParent_succ_right, iterParent_succ_right]
        have hm_nz : iterParent par_w m q ≠ 0 := fun h0 => by
          rw [h0, hp0] at hnz; exact hnz rfl
        rw [← ih hm_nz]
        rcases hpar (iterParent par_w m q) with h | h
        · exact absurd h hnz
        · exact h
  rw [← hchain k (by rw [hk_eq]; omega), hk_eq]

/-- If the two parent maps agree outside a set `P` that the old map never leaves, then a
chain under the old map that ends outside `P` is also a chain under the new map. -/
theorem cut_reachesIn_of_old {par₃ par_w : ℕ → ℕ} {cap q y : ℕ} {P : ℕ → Prop}
    (hclosed : ∀ z, P z → P (par₃ z)) (hagree : ∀ z, ¬ P z → par_w z = par₃ z)
    (hy : ¬ P y) (hr : reachesIn par₃ cap q y = true) : reachesIn par_w cap q y = true := by
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at hr ⊢
  rcases hr with ⟨hq, ⟨k, hk_lt, hk_eq⟩⟩
  refine ⟨hq, ⟨k, hk_lt, ?_⟩⟩
  have hchain : ∀ m, ¬ P (iterParent par₃ m q) →
      iterParent par_w m q = iterParent par₃ m q := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hnp
        rw [iterParent_succ_right] at hnp
        rw [iterParent_succ_right, iterParent_succ_right]
        have hm : ¬ P (iterParent par₃ m q) := fun h => hnp (hclosed _ h)
        rw [ih hm, hagree _ hm]
  rw [hchain k (by rw [hk_eq]; exact hy), hk_eq]

/-- Represented sizes agree at every node outside a set that the old parent map never
leaves, when the new map agrees with the old one outside that set and is otherwise `0`. -/
theorem cut_repSize_eq {mem₃ mem_w : ℕ → ℕ} {nb cap y : ℕ} {P : ℕ → Prop}
    (hpar : ∀ z, lctAuxParent mem_w nb cap z = 0 ∨
      lctAuxParent mem_w nb cap z = lctAuxParent mem₃ nb cap z)
    (hclosed : ∀ z, P z → P (lctAuxParent mem₃ nb cap z))
    (hagree : ∀ z, ¬ P z → lctAuxParent mem_w nb cap z = lctAuxParent mem₃ nb cap z)
    (hy1 : 1 ≤ y) (hy : ¬ P y) :
    lctRepSize mem_w nb cap y = lctRepSize mem₃ nb cap y := by
  unfold lctRepSize
  congr 1
  apply List.filter_congr
  intro q _
  apply Bool.eq_iff_iff.2
  exact ⟨cut_reachesIn_of_new hpar (lctAuxParent_zero mem_w nb cap) hy1,
    cut_reachesIn_of_old hclosed hagree hy⟩

/-- A list of numbers at most `1` with no two entries equal to `1` has sum at most `1`. -/
private lemma list_sum_le_one_of_pairs {α : Type*} (L : List α) (f : α → ℕ)
    (hf : ∀ a ∈ L, f a ≤ 1) (hpair : ∀ a b, [a, b].Sublist L → f a = 1 → f b = 1 → False) :
    (L.map f).sum ≤ 1 := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons]
      have ih' := ih (fun c hc => hf c (List.mem_cons_of_mem _ hc))
        (fun c d hcd => hpair c d (hcd.cons a))
      by_cases ha : f a = 1
      · have hz : (tl.map f).sum = 0 := by
          apply List.sum_eq_zero
          intro v hv
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
          have hc1 := hf c (List.mem_cons_of_mem _ hc)
          by_contra hne
          exact hpair a c ((List.singleton_sublist.2 hc).cons_cons a) ha (by omega)
        omega
      · have := hf a List.mem_cons_self
        omega

/-- Two disjoint auxiliary trees with the same path parent `p` cannot both be heavy: the
sizes of their top nodes add up to less than the size of `p`. -/
theorem heavy_child_unique {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ} {trees : List AuxTree}
    (hok : SplayForestOk w h L mem nb cap trees)
    (hpp_le : ∀ t ∈ trees, nodeField mem nb t.rootId OFF_PPAR ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem nb cap) cap u = 0)
    {a b : AuxTree} (ha : a ∈ trees) (hb : b ∈ trees) (hdisj : ∀ z ∈ a.toList, z ∉ b.toList)
    (hpp : nodeField mem nb a.rootId OFF_PPAR = nodeField mem nb b.rootId OFF_PPAR)
    (hha : isHeavyRoot mem nb cap a.rootId = true)
    (hhb : isHeavyRoot mem nb cap b.rootId = true) : False := by
  set p := nodeField mem nb a.rootId OFF_PPAR with hp_def
  have hd_of : ∀ t ∈ trees, nodeField mem nb t.rootId OFF_PPAR = p →
      isHeavyRoot mem nb cap t.rootId = true →
      ∃ hd, hd ∈ t.toList ∧ 1 ≤ hd ∧ hd ≤ cap ∧ lctAuxParent mem nb cap hd = p ∧
        1 ≤ p ∧ p ≤ cap ∧ lctRepSize mem nb cap p < 2 * lctRepSize mem nb cap hd := by
    intro t ht htp hth
    cases hseq : lctTreeSeq mem nb cap t.rootId with
    | nil => simp [isHeavyRoot, hseq] at hth
    | cons hd tl =>
        simp only [isHeavyRoot, hseq, htp, Bool.and_eq_true, decide_eq_true_eq] at hth
        have hmem_seq : hd ∈ t.evalInorder (revFlag mem nb) false := by
          rw [← hok.lctTreeSeq_eq ht, hseq]; simp
        have hmem : hd ∈ t.toList := (t.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hmem_seq
        have hbd := (hok.trees_ok t ht).2.2.nodup_perm_mem hmem
        have hpar := lctAuxParent_of_tree hok hpp_le ht 0 (by rw [hseq]; simp)
        simp only [hseq, ↓reduceIte, htp] at hpar
        exact ⟨hd, hmem, hbd.1, hbd.2, by simpa using hpar, hth.1.1, hth.1.2, hth.2⟩
  obtain ⟨hda, hda_mem, hda1, hda2, hpar_a, hp1, hp2, hlt_a⟩ := hd_of a ha rfl hha
  obtain ⟨hdb, hdb_mem, hdb1, hdb2, hpar_b, -, -, hlt_b⟩ := hd_of b hb hpp.symm hhb
  have hne : hda ≠ hdb := fun heq => hdisj hda hda_mem (heq ▸ hdb_mem)
  let cs := ((List.range cap).map (· + 1)).filter
    (fun c => decide (lctAuxParent mem nb cap c = p))
  have hcs_nd : cs.Nodup :=
    (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
  have hin : ∀ c, 1 ≤ c → c ≤ cap → lctAuxParent mem nb cap c = p → c ∈ cs := by
    intro c hc1 hc2 hcp
    simp only [cs, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    exact ⟨⟨c - 1, by omega, by omega⟩, hcp⟩
  have hsum := list_sum_two_mem_le hcs_nd (lctRepSize mem nb cap)
    (hin hda hda1 hda2 hpar_a) (hin hdb hdb1 hdb2 hpar_b) hne
  have hrep := lctRepSize_eq_one_add_sum mem nb cap p
    (fun z _ _ => lctAuxParent_le_cap mem nb cap z) hacyc hp1 hp2
  dsimp only [cs] at hsum
  omega

/-- Potential bound for the cut write: `lctPhi` grows by at most `2 * C_HEAVY L`. -/
theorem cut_phi_le {w h L P b n x y ed : ℕ}
    {free free' : List ℕ} {edgeMap edgeMap' : List (ℕ × ForestEdge)}
    {rest : List AuxTree} {mem₃ mem_w : ℕ → ℕ}
    (hi₃ : LctExposeInvs w h L P b n free edgeMap
      (AuxTree.node ed (AuxTree.node (x + 1) .leaf .leaf) (AuxTree.node (y + 1) .leaf .leaf) ::
        rest) mem₃)
    (hi_w : LctExposeInvs w h L P b n free' edgeMap'
      (AuxTree.node (x + 1) .leaf .leaf :: AuxTree.node (y + 1) .leaf .leaf ::
        AuxTree.node ed .leaf .leaf :: rest) mem_w)
    (hpar_eq : ∀ z, lctAuxParent mem_w (lctNodesBase b) (lctCap n) z =
      if z = ed ∨ z = x + 1 ∨ z = y + 1 then 0 else
        lctAuxParent mem₃ (lctNodesBase b) (lctCap n) z)
    (hrest_agree : ∀ s ∈ rest,
      nodeField mem_w (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₃ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_w (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₃ (lctNodesBase b)) false)
    (hpp_ed3 : nodeField mem₃ (lctNodesBase b) ed OFF_PPAR = 0)
    (hpx_w : nodeField mem_w (lctNodesBase b) (x + 1) OFF_PPAR = 0)
    (hpy_w : nodeField mem_w (lctNodesBase b) (y + 1) OFF_PPAR = 0)
    (hped_w : nodeField mem_w (lctNodesBase b) ed OFF_PPAR = 0)
    (hpar3_x : lctAuxParent mem₃ (lctNodesBase b) (lctCap n) (x + 1) = 0)
    (hpar3_ed : lctAuxParent mem₃ (lctNodesBase b) (lctCap n) ed = x + 1)
    (hpar3_y : lctAuxParent mem₃ (lctNodesBase b) (lctCap n) (y + 1) = ed)
    (hed_only : ∀ z, 1 ≤ z → z ≤ lctCap n →
      lctAuxParent mem₃ (lctNodesBase b) (lctCap n) z = ed → z = y + 1) :
    lctPhi L mem_w b n ≤ lctPhi L mem₃ b n + 2 * C_HEAVY L := by
  set nb := lctNodesBase b with hnb
  set cap := lctCap n with hcap
  set t_ed := AuxTree.node ed (AuxTree.node (x + 1) .leaf .leaf)
    (AuxTree.node (y + 1) .leaf .leaf) with ht_ed
  set trees₃ := t_ed :: rest with htrees₃
  set trees_w := AuxTree.node (x + 1) .leaf .leaf :: AuxTree.node (y + 1) .leaf .leaf ::
    AuxTree.node ed .leaf .leaf :: rest with htrees_w
  have hnd3 : (trees₃.flatMap AuxTree.toList).Nodup :=
    hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [htrees₃, List.flatMap_cons, List.nodup_append] at hnd3
  have hrest_nd : (rest.flatMap AuxTree.toList).Nodup := hnd3.2.1
  have hdisj_rest : ∀ s ∈ rest, ∀ z ∈ s.toList, ¬ (z = ed ∨ z = x + 1 ∨ z = y + 1) := by
    intro s hs z hz hzS
    have hz_flat : z ∈ rest.flatMap AuxTree.toList := List.mem_flatMap.2 ⟨s, hs, hz⟩
    have hz_ed : z ∈ t_ed.toList := by
      rcases hzS with rfl | rfl | rfl <;> simp [t_ed, AuxTree.toList]
    exact hnd3.2.2 z hz_ed z hz_flat rfl
  have hs_bd : ∀ s ∈ rest, ∀ z ∈ s.toList, 1 ≤ z ∧ z ≤ cap := fun s hs z hz =>
    (hi₃.sf.trees_ok s (List.mem_cons_of_mem _ hs)).2.2.nodup_perm_mem hz
  -- Represented sizes outside `{ed, x + 1, y + 1}`.
  have hrs_eq : ∀ z, 1 ≤ z → ¬ (z = ed ∨ z = x + 1 ∨ z = y + 1) →
      lctRepSize mem_w nb cap z = lctRepSize mem₃ nb cap z := by
    intro z hz1 hzS
    refine cut_repSize_eq (P := fun z => z = 0 ∨ z = ed ∨ z = x + 1 ∨ z = y + 1)
      (fun z => ?_) (fun z hz => ?_) (fun z hz => ?_) hz1 (by omega)
    · rw [hpar_eq z]; split_ifs <;> simp
    · rcases hz with rfl | rfl | rfl | rfl
      · simp [lctAuxParent_zero]
      · simp [hpar3_ed]
      · simp [hpar3_x]
      · simp [hpar3_y]
    · rw [hpar_eq z, ite_eq_right_iff.2 (fun h => absurd h (by tauto))]
  -- The sequences and top sizes of the remaining trees.
  have hseq_rest : ∀ s ∈ rest,
      lctTreeSeq mem_w nb cap s.rootId = lctTreeSeq mem₃ nb cap s.rootId := by
    intro s hs
    rw [hi_w.sf.lctTreeSeq_eq (t := s) (by simp [trees_w, hs]),
      hi₃.sf.lctTreeSeq_eq (t := s) (List.mem_cons_of_mem _ hs), (hrest_agree s hs).2]
  have hhd_of : ∀ s ∈ rest, ∀ hd tl, lctTreeSeq mem₃ nb cap s.rootId = hd :: tl →
      hd ∈ s.toList := by
    intro s hs hd tl hseq
    have : hd ∈ s.evalInorder (revFlag mem₃ nb) false := by
      rw [← hi₃.sf.lctTreeSeq_eq (List.mem_cons_of_mem _ hs), hseq]; simp
    exact (s.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.1 this
  have hdash_rest : ∀ s ∈ rest,
      dashedChildSize mem_w nb cap s.rootId = dashedChildSize mem₃ nb cap s.rootId := by
    intro s hs
    simp only [dashedChildSize, hseq_rest s hs]
    cases hseq : lctTreeSeq mem₃ nb cap s.rootId with
    | nil => rfl
    | cons hd tl =>
        have hm := hhd_of s hs hd tl hseq
        exact hrs_eq hd (hs_bd s hs hd hm).1 (hdisj_rest s hs hd hm)
  -- Virtual sizes do not change at any node.
  have hvs_eq : ∀ z, 1 ≤ z → lctVSize mem_w nb cap z = lctVSize mem₃ nb cap z := by
    intro z hz1
    simp only [lctVSize]
    rw [list_filter_map_sum_ite, list_filter_map_sum_ite]
    have hp_w := hi_w.sf.auxRootIds_perm.map fun r =>
      if decide (nodeField mem_w nb r OFF_PPAR = z) = true then
        dashedChildSize mem_w nb cap r else 0
    have hp_3 := hi₃.sf.auxRootIds_perm.map fun r =>
      if decide (nodeField mem₃ nb r OFF_PPAR = z) = true then
        dashedChildSize mem₃ nb cap r else 0
    rw [hp_w.sum_eq, hp_3.sum_eq]
    simp only [trees_w, trees₃, t_ed, List.map_cons, List.map_map, List.sum_cons,
      Function.comp_def, decide_eq_true_eq, auxTree_rootId_node]
    rw [hpx_w, hpy_w, hped_w, hpp_ed3]
    have hne_0z : (0 = z) = False := eq_false (by omega)
    simp only [hne_0z, ↓reduceIte, Nat.zero_add]
    congr 1
    apply List.map_congr_left
    intro s hs
    rw [(hrest_agree s hs).1, hdash_rest s hs]
  -- The splay part does not grow.
  have hsplay_le : splayMemPhi (K_SPLAY_STEP L) mem_w nb cap (lctVSize mem_w nb cap) ≤
      splayMemPhi (K_SPLAY_STEP L) mem₃ nb cap (lctVSize mem₃ nb cap) := by
    rw [splayMemPhi_eq_sum hi_w.sf, splayMemPhi_eq_sum hi₃.sf]
    apply Nat.mul_le_mul_left
    have hphi_w : ∀ s ∈ trees_w,
        s.treePhi (lctVSize mem_w nb cap) = s.treePhi (lctVSize mem₃ nb cap) := by
      intro s hs
      have htok := (hi_w.sf.trees_ok s hs).2.2
      exact auxTree_treePhi_congr fun z hz => hvs_eq z (htok.nodup_perm_mem hz).1
    rw [List.map_congr_left hphi_w]
    set vs := lctVSize mem₃ nb cap
    have hrk : (AuxTree.node ed .leaf .leaf).rank vs ≤ t_ed.rank vs := by
      apply Nat.log_mono_right
      simp only [t_ed, AuxTree.treeSize]
      omega
    have h1 : (AuxTree.node ed .leaf .leaf).treePhi vs =
        (AuxTree.node ed .leaf .leaf).rank vs := by simp [AuxTree.treePhi]
    have h2 : t_ed.treePhi vs = t_ed.rank vs +
        (AuxTree.node (x + 1) .leaf .leaf).treePhi vs +
        (AuxTree.node (y + 1) .leaf .leaf).treePhi vs := by
      simp only [t_ed, AuxTree.treePhi]
    simp only [trees_w, trees₃, List.map_cons, List.sum_cons]
    rw [h1, h2]
    omega
  -- The number of heavy roots grows by at most two.
  have hheavy_le : lctHeavyCount mem_w nb cap ≤ lctHeavyCount mem₃ nb cap + 2 := by
    simp only [lctHeavyCount, list_filter_length_ite]
    have hp_w := hi_w.sf.auxRootIds_perm.map fun r =>
      if isHeavyRoot mem_w nb cap r = true then 1 else 0
    have hp_3 := hi₃.sf.auxRootIds_perm.map fun r =>
      if isHeavyRoot mem₃ nb cap r = true then 1 else 0
    rw [hp_w.sum_eq, hp_3.sum_eq]
    simp only [trees_w, trees₃, List.map_cons, List.map_map, List.sum_cons, Function.comp_def]
    have hnot : ∀ r, nodeField mem_w nb r OFF_PPAR = 0 → isHeavyRoot mem_w nb cap r = false := by
      intro r hr
      simp [isHeavyRoot, hr]
    simp only [auxTree_rootId_node, hnot _ hpx_w, hnot _ hpy_w, hnot _ hped_w, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add]
    let hw := fun s : AuxTree => if isHeavyRoot mem_w nb cap s.rootId = true then 1 else 0
    let h3 := fun s : AuxTree => if isHeavyRoot mem₃ nb cap s.rootId = true then 1 else 0
    let A := fun (p : ℕ) (s : AuxTree) =>
      if isHeavyRoot mem_w nb cap s.rootId = true ∧ nodeField mem_w nb s.rootId OFF_PPAR = p
      then 1 else 0
    have hstep : ∀ s ∈ rest, hw s ≤ h3 s + A (x + 1) s + A (y + 1) s := by
      intro s hs
      by_cases hhw : isHeavyRoot mem_w nb cap s.rootId = true
      · by_cases hpx : nodeField mem_w nb s.rootId OFF_PPAR = x + 1
        · simp only [hw, A, hhw, hpx, true_and, ↓reduceIte]; omega
        by_cases hpy : nodeField mem_w nb s.rootId OFF_PPAR = y + 1
        · simp only [hw, A, hhw, hpy, true_and, ↓reduceIte]; omega
        have hpp := (hrest_agree s hs).1
        have hh3 : isHeavyRoot mem₃ nb cap s.rootId = true := by
          have hhw' := hhw
          simp only [isHeavyRoot, hseq_rest s hs, Bool.and_eq_true, decide_eq_true_eq] at hhw' ⊢
          rw [hpp] at hhw' hpx hpy
          refine ⟨hhw'.1, ?_⟩
          have hlt := hhw'.2
          cases hseq : lctTreeSeq mem₃ nb cap s.rootId with
          | nil => rw [hseq] at hlt; simp at hlt
          | cons hd tl =>
              rw [hseq] at hlt
              simp only [decide_eq_true_eq] at hlt ⊢
              have hm := hhd_of s hs hd tl hseq
              have hd_bd := hs_bd s hs hd hm
              have hrs_hd := hrs_eq hd hd_bd.1 (hdisj_rest s hs hd hm)
              have hpp_ne_ed : nodeField mem₃ nb s.rootId OFF_PPAR ≠ ed := by
                intro hed
                have hlen : 0 < (lctTreeSeq mem₃ nb cap s.rootId).length := by rw [hseq]; simp
                have hpar0 : lctAuxParent mem₃ nb cap (lctTreeSeq mem₃ nb cap s.rootId)[0] =
                    nodeField mem₃ nb s.rootId OFF_PPAR := by
                  have := lctAuxParent_of_tree hi₃.sf hi₃.ppar_le_cap
                    (List.mem_cons_of_mem _ hs) 0 hlen
                  simpa using this
                have hpar : lctAuxParent mem₃ nb cap hd = ed := by
                  simp only [hseq, List.getElem_cons_zero] at hpar0
                  rw [hpar0, hed]
                have := hed_only hd hd_bd.1 hd_bd.2 hpar
                exact hdisj_rest s hs hd hm (Or.inr (Or.inr this))
              have hrs_pp := hrs_eq _ hhw'.1.1 (by tauto)
              omega
        simp only [hw, h3, A, hhw, hh3, ↓reduceIte]; omega
      · simp only [hw, hhw, Bool.false_eq_true, ↓reduceIte]; omega
    have hA : ∀ p, (rest.map (A p)).sum ≤ 1 := by
      intro p
      apply list_sum_le_one_of_pairs
      · intro s _; simp only [A]; split_ifs <;> omega
      · intro a c hac ha hc
        simp only [A] at ha hc
        split_ifs at ha hc with ha' hc'
        · have ha_mem : a ∈ rest := hac.subset (by simp)
          have hc_mem : c ∈ rest := hac.subset (by simp)
          have hsub : (a.toList ++ c.toList).Sublist (rest.flatMap AuxTree.toList) := by
            have := (hac.map AuxTree.toList).flatten
            simpa [List.flatMap] using this
          have hnd_ac := (hsub.nodup hrest_nd)
          rw [List.nodup_append] at hnd_ac
          exact heavy_child_unique hi_w.sf hi_w.ppar_le_cap hi_w.subdivOk.1
            (by simp [trees_w, ha_mem]) (by simp [trees_w, hc_mem])
            (fun z hza hzc => hnd_ac.2.2 z hza z hzc rfl)
            (ha'.2.trans hc'.2.symm) ha'.1 hc'.1
    have hsum := List.sum_le_sum hstep
    rw [List.sum_map_add, List.sum_map_add] at hsum
    have h1 := hA (x + 1)
    have h2 := hA (y + 1)
    have hsum' : (rest.map hw).sum ≤ (rest.map h3).sum + 2 := by omega
    have hed_le : 0 ≤ (if isHeavyRoot mem₃ nb cap ed = true then 1 else 0) := Nat.zero_le _
    simp only [hw, h3] at hsum'
    omega
  show splayMemPhi (K_SPLAY_STEP L) mem_w nb cap (lctVSize mem_w nb cap) +
      C_HEAVY L * lctHeavyCount mem_w nb cap ≤
    splayMemPhi (K_SPLAY_STEP L) mem₃ nb cap (lctVSize mem₃ nb cap) +
      C_HEAVY L * lctHeavyCount mem₃ nb cap + 2 * C_HEAVY L
  have hmul : C_HEAVY L * lctHeavyCount mem_w nb cap ≤
      C_HEAVY L * lctHeavyCount mem₃ nb cap + 2 * C_HEAVY L := by
    have := Nat.mul_le_mul_left (C_HEAVY L) hheavy_le
    rw [Nat.mul_add] at this
    omega
  omega

end CutPhi

end MinCostFlow.LinkCut.Prog
