module

public import MinCostFlow.LinkCut.Prog.MathForestRootMove

/-!
# Reroot Potential Bound and Full `revNode_reroot_invs`

Proves `revNode_reroot_phi` (`splayMemPhi` preserved and `lctHeavyCount` increases by at most
`Nat.log 2 (n + 2) + 2`) and assembles `revNode_reroot_invs`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem revNode_reroot_phi {w h L P b n v : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_fin : AuxTree} {rest_fin : List AuxTree} {mem₁ mem₂ : ℕ → ℕ}
    (hi₁ : LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin) mem₁)
    (hsf₂ : SplayForestOk w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin))
    (hm₂ : TreeMemMatch w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin) 0 0)
    (hpp_zero₁ : nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hpp_zero₂ : nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hout_x₂ : ∀ addr, addr < lctNodesBase b + NODE_STRIDE * (v + 1) ∨
        lctNodesBase b + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ addr →
      mem₂ addr = mem₁ addr)
    (hnin_rest : ∀ s ∈ rest_fin, v + 1 ∉ s.toList)
    (hrest_agree : ∀ s ∈ rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false)
    (hacyc₂ : ∀ u, 1 ≤ u → u ≤ lctCap n →
      iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) u = 0)
    (hout_par : ∀ u, u ∉ (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false →
      lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u =
        lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u)
    (hclosed : ∀ u, u = 0 ∨ u ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false →
      (lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u = 0 ∨
        lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u ∈
          (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
            (revFlag mem₁ (lctNodesBase b)) false) ∧
      (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u = 0 ∨
        lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u ∈
          (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
            (revFlag mem₁ (lctNodesBase b)) false))
    (hp_seq2_s : ∀ i (hi : i + 1 < ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false).length),
      lctAuxParent mem₂ (lctNodesBase b) (lctCap n)
        (((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
          (revFlag mem₁ (lctNodesBase b)) false)[i]) =
        (((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
          (revFlag mem₁ (lctNodesBase b)) false)[i + 1]))
    (hseq_ne : (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
      (revFlag mem₁ (lctNodesBase b)) false ≠ [])
    (hpp₂_le : ∀ s ∈ AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n) :
    lctPhi L mem₂ b n ≤ lctPhi L mem₁ b n + C_HEAVY L * (Nat.log 2 (n + 2) + 2) := by
  let seq := (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder (revFlag mem₁ (lctNodesBase b)) false
  change seq ≠ [] at hseq_ne
  change ∀ i (hi : i + 1 < seq.length),
    lctAuxParent mem₂ (lctNodesBase b) (lctCap n) seq[i] = seq[i + 1] at hp_seq2_s
  have hnd_all₁ : ((AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList).Nodup :=
    hi₁.sf.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hpar₂_le := lctAuxParent_le_cap_of_trees hsf₂ hpp₂_le
  have hrep_off : ∀ z, 1 ≤ z → z ≤ lctCap n → z ∉ seq →
      lctRepSize mem₂ (lctNodesBase b) (lctCap n) z =
        lctRepSize mem₁ (lctNodesBase b) (lctCap n) z := by
    intro z hz1 _ hzn
    unfold lctRepSize
    congr 1
    refine List.filter_congr ?_
    intro u _
    simp only [reachesIn]
    congr 1
    congr 1
    funext k
    by_cases h1 : iterParent (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) k u = z
    · have h2 : iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) k u = z :=
        (reroot_repSize_eq_off_seq hout_par hclosed (by omega) hzn k u).2 h1
      simp [h1, h2]
    · have h2 : iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) k u ≠ z := fun h2e =>
        h1 ((reroot_repSize_eq_off_seq hout_par hclosed (by omega) hzn k u).1 h2e)
      simp [h1, h2]
  have haux_roots_eq : auxRootIds mem₂ (lctNodesBase b) (lctCap n) =
      auxRootIds mem₁ (lctNodesBase b) (lctCap n) := by
    unfold auxRootIds
    refine List.filter_congr ?_
    intro r hr
    rcases List.mem_map.1 hr with ⟨i, hi, rfl⟩
    by_cases hrv : i + 1 = v + 1
    · rw [hrv]
      have hm1 := (hi₁.sf.2.2.2.2.2.2.2.2.2 (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)).2.2
      have hp1 : nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PARENT = 0 := hm1.2.2.2.2.1
      have hp2 : nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PARENT = 0 := hm₂.2.2.2.2.1
      simp [hp1, hp2]
    · rw [mem_off_slot_eq hout_x₂ hrv (by decide)]
  have hvsize_eq : ∀ y, 1 ≤ y → y ≤ lctCap n →
      lctVSize mem₂ (lctNodesBase b) (lctCap n) y = lctVSize mem₁ (lctNodesBase b) (lctCap n) y := by
    intro y hy1 _
    unfold lctVSize
    rw [haux_roots_eq]
    have hflt_eq :
        (auxRootIds mem₁ (lctNodesBase b) (lctCap n)).filter
          (fun r => decide (nodeField mem₂ (lctNodesBase b) r OFF_PPAR = y)) =
        (auxRootIds mem₁ (lctNodesBase b) (lctCap n)).filter
          (fun r => decide (nodeField mem₁ (lctNodesBase b) r OFF_PPAR = y)) := by
      refine List.filter_congr ?_
      intro r hr
      by_cases hrv : r = v + 1
      · subst hrv; simp [hpp_zero₁, hpp_zero₂, show (0 : ℕ) ≠ y by omega]
      · rw [mem_off_slot_eq hout_x₂ hrv (by decide)]
    rw [hflt_eq]
    congr 1
    refine List.map_congr_left ?_
    intro r hr
    rw [List.mem_filter] at hr
    rcases hr with ⟨hr_root, hr_pp⟩
    have hr_ne_v : r ≠ v + 1 := fun heq => by
      subst heq; simp [hpp_zero₁] at hr_pp; omega
    have hr_mem : r ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList := by
      rw [hi₁.sf.2.2.2.2.2.2.2.2.1.mem_iff]
      simp only [auxRootIds, List.mem_filter] at hr_root
      exact hr_root.1
    rcases List.mem_flatMap.1 hr_mem with ⟨s, hs, hrs⟩
    have hs_ne_t1 : s ∈ rest_fin := by
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs_rest
      · have hpar0 : nodeField mem₁ (lctNodesBase b) r OFF_PARENT = 0 := by
          simp only [auxRootIds, List.mem_filter, decide_eq_true_eq] at hr_root
          exact hr_root.2
        have hm1 := (hi₁.sf.2.2.2.2.2.2.2.2.2 (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)).2.2
        dsimp only [AuxTree.rootId] at hm1
        rw [hpp_zero₁] at hm1
        exact absurd (eq_rootId_of_parent_zero hm1 hrs hpar0) hr_ne_v
      · exact hs_rest
    have hm_s1 := (hi₁.sf.2.2.2.2.2.2.2.2.2 s (by simp [hs_ne_t1])).2.2
    have hm_s2 := (hsf₂.2.2.2.2.2.2.2.2.2 s (by simp [hs_ne_t1])).2.2
    have hs_nd1 : s.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all₁ (by simp [hs_ne_t1])
    have hs_cnt : s.countNodes ≤ lctCap n := by
      rw [← AuxTree.length_toList]
      have hsub : s.toList ⊆ (List.range (lctCap n)).map (· + 1) := fun z hz =>
        hi₁.sf.2.2.2.2.2.2.2.2.1.subset (List.mem_flatMap.2 ⟨s, by simp [hs_ne_t1], hz⟩)
      have hnd_r : ((List.range (lctCap n)).map (· + 1)).Nodup :=
        List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)
      simpa using (List.Nodup.subperm hs_nd1 hsub).length_le
    have hpar0 : nodeField mem₁ (lctNodesBase b) r OFF_PARENT = 0 := by
      simp only [auxRootIds, List.mem_filter, decide_eq_true_eq] at hr_root
      exact hr_root.2
    have hrs_eq : r = s.rootId := eq_rootId_of_parent_zero hm_s1 hrs hpar0
    have hseq_s1 : lctTreeSeq mem₁ (lctNodesBase b) (lctCap n) r =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false := by
      unfold lctTreeSeq
      rw [hrs_eq, hm_s1.readAuxTree_eq hs_cnt]
    have hseq_s2 : lctTreeSeq mem₂ (lctNodesBase b) (lctCap n) r =
        s.evalInorder (revFlag mem₂ (lctNodesBase b)) false := by
      unfold lctTreeSeq
      rw [hrs_eq, hm_s2.readAuxTree_eq hs_cnt]
    unfold dashedChildSize
    rw [hseq_s1, hseq_s2, (hrest_agree s hs_ne_t1).2]
    cases hs_eval : s.evalInorder (revFlag mem₁ (lctNodesBase b)) false with
    | nil => rfl
    | cons hd tl =>
        have hhd_mem : hd ∈ s.toList :=
          (s.evalInorder_perm (revFlag mem₁ (lctNodesBase b)) false).mem_iff.1 (by rw [hs_eval]; simp)
        have hhd_bd := hm_s1.nodup_perm_mem hhd_mem
        have hhd_nseq : hd ∉ seq := fun hm => by
          have hhd_t1 : hd ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
            ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hm
          have heq_tr := unique_tree_of_mem hnd_all₁ (by simp) (by simp [hs_ne_t1]) hhd_t1 hhd_mem
          have hv_in_s : v + 1 ∈ s.toList := heq_tr ▸ (by simp [AuxTree.toList])
          exact hnin_rest s hs_ne_t1 hv_in_s
        exact hrep_off hd hhd_bd.1 hhd_bd.2 hhd_nseq
  have hsplay_phi_eq :
      splayMemPhi (K_SPLAY_STEP L) mem₂ (lctNodesBase b) (lctCap n)
        (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
      splayMemPhi (K_SPLAY_STEP L) mem₁ (lctNodesBase b) (lctCap n)
        (lctVSize mem₁ (lctNodesBase b) (lctCap n)) := by
    rw [splayMemPhi_eq_sum hsf₂, splayMemPhi_eq_sum hi₁.sf]
    congr 1
    have htree_eq : ∀ t ∈ AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin,
        t.treePhi (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
          t.treePhi (lctVSize mem₁ (lctNodesBase b) (lctCap n)) := by
      intro t ht
      have hm_t := (hi₁.sf.2.2.2.2.2.2.2.2.2 t ht).2.2
      have hv_on : ∀ u ∈ t.toList,
          lctVSize mem₂ (lctNodesBase b) (lctCap n) u =
            lctVSize mem₁ (lctNodesBase b) (lctCap n) u := fun u hu =>
        have hb := hm_t.nodup_perm_mem hu; hvsize_eq u hb.1 hb.2
      have go : ∀ s : AuxTree,
          (∀ u ∈ s.toList, lctVSize mem₂ (lctNodesBase b) (lctCap n) u =
            lctVSize mem₁ (lctNodesBase b) (lctCap n) u) →
          s.treeSize (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
            s.treeSize (lctVSize mem₁ (lctNodesBase b) (lctCap n)) ∧
          s.treePhi (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
            s.treePhi (lctVSize mem₁ (lctNodesBase b) (lctCap n)) := by
        intro s
        induction s with
        | leaf => intro _; simp [AuxTree.treeSize, AuxTree.treePhi]
        | node id l r ihl ihr =>
            intro hagree
            have hid := hagree id (by simp [AuxTree.toList])
            have hl := ihl fun u hu => hagree u (by simp [AuxTree.toList, hu])
            have hr := ihr fun u hu => hagree u (by simp [AuxTree.toList, hu])
            have hsz : (AuxTree.node id l r).treeSize (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
                (AuxTree.node id l r).treeSize (lctVSize mem₁ (lctNodesBase b) (lctCap n)) := by
              simp [AuxTree.treeSize, hid, hl.1, hr.1]
            have hrk : (AuxTree.node id l r).rank (lctVSize mem₂ (lctNodesBase b) (lctCap n)) =
                (AuxTree.node id l r).rank (lctVSize mem₁ (lctNodesBase b) (lctCap n)) := by
              simp [AuxTree.rank, hsz]
            refine ⟨hsz, ?_⟩
            simp [AuxTree.treePhi, hrk, hl.2, hr.2]
      exact (go t hv_on).2
    have hrev_phi := (AuxTree.node (v + 1) l_fin AuxTree.leaf).revRoot_treePhi
      (lctVSize mem₂ (lctNodesBase b) (lctCap n))
    simp only [AuxTree.revRoot] at hrev_phi
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hrev_phi,
      htree_eq (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)]
    congr 1
    congr 1
    exact List.map_congr_left fun t ht => htree_eq t (by simp [ht])
  have hheavy_le : lctHeavyCount mem₂ (lctNodesBase b) (lctCap n) ≤
      lctHeavyCount mem₁ (lctNodesBase b) (lctCap n) + (Nat.log 2 (n + 2) + 2) := by
    unfold lctHeavyCount
    rw [haux_roots_eq]
    let roots := auxRootIds mem₁ (lctNodesBase b) (lctCap n)
    let newH := roots.filter (fun r =>
      isHeavyRoot mem₂ (lctNodesBase b) (lctCap n) r &&
      !isHeavyRoot mem₁ (lctNodesBase b) (lctCap n) r)
    have hfilt := list_filter_diff_length
      (isHeavyRoot mem₂ (lctNodesBase b) (lctCap n))
      (isHeavyRoot mem₁ (lctNodesBase b) (lctCap n)) roots
    have hnew_prop : ∀ r ∈ newH,
        ∃ s ∈ rest_fin, s.rootId = r ∧
          ∃ hd, 1 ≤ hd ∧ hd ≤ lctCap n ∧ hd ∈ s.toList ∧ hd ∉ seq ∧
            lctAuxParent mem₂ (lctNodesBase b) (lctCap n) hd =
              nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
            nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∈ seq ∧
            lctRepSize mem₂ (lctNodesBase b) (lctCap n) (nodeField mem₂ (lctNodesBase b) r OFF_PPAR) <
              2 * lctRepSize mem₂ (lctNodesBase b) (lctCap n) hd := by
      intro r hr
      simp only [newH, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hr
      rcases hr with ⟨hr_root, hh2, hh1⟩
      have hne_v : r ≠ v + 1 := fun heq => by
        subst heq; simp [isHeavyRoot, hpp_zero₂] at hh2
      have hr_mem : r ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList := by
        rw [hi₁.sf.2.2.2.2.2.2.2.2.1.mem_iff]
        simp only [roots, auxRootIds, List.mem_filter] at hr_root
        exact hr_root.1
      rcases List.mem_flatMap.1 hr_mem with ⟨s, hs, hrs⟩
      have hpar0 : nodeField mem₁ (lctNodesBase b) r OFF_PARENT = 0 := by
        simp only [roots, auxRootIds, List.mem_filter, decide_eq_true_eq] at hr_root
        exact hr_root.2
      have hs_rest : s ∈ rest_fin := by
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hsr
        · have hm1 := (hi₁.sf.2.2.2.2.2.2.2.2.2 (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)).2.2
          dsimp only [AuxTree.rootId] at hm1
          rw [hpp_zero₁] at hm1
          exact absurd (eq_rootId_of_parent_zero hm1 hrs hpar0) hne_v
        · exact hsr
      have hm_s1 := (hi₁.sf.2.2.2.2.2.2.2.2.2 s (by simp [hs_rest])).2.2
      have hm_s2 := (hsf₂.2.2.2.2.2.2.2.2.2 s (by simp [hs_rest])).2.2
      have hrs_eq : s.rootId = r := (eq_rootId_of_parent_zero hm_s1 hrs hpar0).symm
      have hs_nd1 : s.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all₁ (by simp [hs_rest])
      have hs_cnt : s.countNodes ≤ lctCap n := by
        rw [← AuxTree.length_toList]
        have hsub : s.toList ⊆ (List.range (lctCap n)).map (· + 1) := fun z hz =>
          hi₁.sf.2.2.2.2.2.2.2.2.1.subset (List.mem_flatMap.2 ⟨s, by simp [hs_rest], hz⟩)
        have hnd_r : ((List.range (lctCap n)).map (· + 1)).Nodup :=
          List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)
        simpa using (List.Nodup.subperm hs_nd1 hsub).length_le
      have hseq_s2 : lctTreeSeq mem₂ (lctNodesBase b) (lctCap n) r =
          s.evalInorder (revFlag mem₂ (lctNodesBase b)) false := by
        unfold lctTreeSeq; rw [← hrs_eq, hm_s2.readAuxTree_eq hs_cnt]
      have hseq_s1 : lctTreeSeq mem₁ (lctNodesBase b) (lctCap n) r =
          s.evalInorder (revFlag mem₁ (lctNodesBase b)) false := by
        unfold lctTreeSeq; rw [← hrs_eq, hm_s1.readAuxTree_eq hs_cnt]
      simp only [isHeavyRoot] at hh2 hh1
      have hpp_b : 1 ≤ nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
          nodeField mem₂ (lctNodesBase b) r OFF_PPAR ≤ lctCap n := by
        have h1 : decide (1 ≤ nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
            nodeField mem₂ (lctNodesBase b) r OFF_PPAR ≤ lctCap n) = true := by
          revert hh2
          cases hdec : decide (1 ≤ nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
              nodeField mem₂ (lctNodesBase b) r OFF_PPAR ≤ lctCap n) <;> simp
        simpa using h1
      rw [hseq_s2] at hh2
      cases hs_ev : s.evalInorder (revFlag mem₂ (lctNodesBase b)) false with
      | nil => simp [hs_ev] at hh2
      | cons hd tl =>
          rw [hs_ev] at hh2
          have hh2_lt : lctRepSize mem₂ (lctNodesBase b) (lctCap n)
              (nodeField mem₂ (lctNodesBase b) r OFF_PPAR) <
              2 * lctRepSize mem₂ (lctNodesBase b) (lctCap n) hd := by
            have hd1 : decide (1 ≤ nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
                nodeField mem₂ (lctNodesBase b) r OFF_PPAR ≤ lctCap n) = true := by
              simpa using hpp_b
            simp only [hd1, Bool.true_and, decide_eq_true_eq] at hh2
            exact hh2
          have hhd_mem : hd ∈ s.toList :=
            (s.evalInorder_perm (revFlag mem₂ (lctNodesBase b)) false).mem_iff.1 (by rw [hs_ev]; simp)
          have hhd_bd := hm_s2.nodup_perm_mem hhd_mem
          have hhd_nseq : hd ∉ seq := fun hm => by
            have hhd_t1 : hd ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
              ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hm
            have heq_tr := unique_tree_of_mem hnd_all₁ (by simp) (by simp [hs_rest]) hhd_t1 hhd_mem
            exact hnin_rest s hs_rest (heq_tr ▸ (by simp [AuxTree.toList]))
          have hpar_hd : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) hd =
              nodeField mem₂ (lctNodesBase b) r OFF_PPAR := by
            have hof := lctAuxParent_of_tree hsf₂ hpp₂_le (t := s) (by simp [hs_rest])
            dsimp only at hof
            rw [hrs_eq, hseq_s2, hs_ev] at hof
            have h0 := hof 0 (by simp)
            simpa [hrs_eq] using h0
          have hpp_in_seq : nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∈ seq := by
            by_contra hpp_nseq
            have heq_pp := hrep_off _ hpp_b.1 hpp_b.2 hpp_nseq
            have heq_hd := hrep_off _ hhd_bd.1 hhd_bd.2 hhd_nseq
            have hpp_eq1 : nodeField mem₁ (lctNodesBase b) r OFF_PPAR =
                nodeField mem₂ (lctNodesBase b) r OFF_PPAR :=
              (mem_off_slot_eq hout_x₂ hne_v (by decide)).symm
            have hd1 : decide (1 ≤ nodeField mem₁ (lctNodesBase b) r OFF_PPAR ∧
                nodeField mem₁ (lctNodesBase b) r OFF_PPAR ≤ lctCap n) = true := by
              rw [hpp_eq1]; simpa using hpp_b
            rw [hseq_s1, ← (hrest_agree s hs_rest).2, hs_ev] at hh1
            simp only [hd1, Bool.true_and, decide_eq_false_iff_not] at hh1
            rw [hpp_eq1, ← heq_pp, ← heq_hd] at hh1
            exact hh1 hh2_lt
          exact ⟨s, hs_rest, hrs_eq, hd, hhd_bd.1, hhd_bd.2, hhd_mem, hhd_nseq,
            hpar_hd, hpp_in_seq, hh2_lt⟩
    let idxFn := fun r => seq.idxOf (nodeField mem₂ (lctNodesBase b) r OFF_PPAR)
    let idxs := newH.map idxFn
    have hroots_nd : roots.Nodup :=
      (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
    have hnewH_nd : newH.Nodup := hroots_nd.filter _
    have hid_nd : idxs.Nodup := by
      refine hnewH_nd.map_on ?_
      intro r₁ hr1 r₂ hr2 hidx_eq
      by_contra hne_r
      rcases hnew_prop r₁ hr1 with ⟨s₁, hs1, hr1_id, hd₁, hd1_1, hd1_2, hd1_mem, _, hpar1_hd, hpp1_seq, hh1_lt⟩
      rcases hnew_prop r₂ hr2 with ⟨s₂, hs2, hr2_id, hd₂, hd2_1, hd2_2, hd2_mem, _, hpar2_hd, hpp2_seq, hh2_lt⟩
      have hpp_eq : nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR =
          nodeField mem₂ (lctNodesBase b) r₂ OFF_PPAR := by
        have hlt1 : idxFn r₁ < seq.length := List.idxOf_lt_length_of_mem hpp1_seq
        have hlt2 : idxFn r₂ < seq.length := List.idxOf_lt_length_of_mem hpp2_seq
        have hg1 := List.getElem_idxOf hlt1
        have hg2 := List.getElem_idxOf hlt2
        calc
          nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR = seq[idxFn r₁] := hg1.symm
          _ = seq[idxFn r₂] := by simp only [hidx_eq]
          _ = nodeField mem₂ (lctNodesBase b) r₂ OFF_PPAR := hg2
      have hne_hd : hd₁ ≠ hd₂ := fun heq => by
        have heq_s : s₁ = s₂ := unique_tree_of_mem hnd_all₁ (by simp [hs1]) (by simp [hs2])
          hd1_mem (heq ▸ hd2_mem)
        exact hne_r (by rw [← hr1_id, ← hr2_id, heq_s])
      have hy_bd : 1 ≤ nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR ∧
          nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR ≤ lctCap n := by
        have hmem_y : nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR ∈
            (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
          ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hpp1_seq
        exact (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hmem_y
      have hsum := lctRepSize_eq_one_add_sum mem₂ (lctNodesBase b) (lctCap n)
        (nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR)
        (fun x _ _ => hpar₂_le x) hacyc₂ hy_bd.1 hy_bd.2
      have hcs_nd : (((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c =
            nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR))).Nodup :=
        (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
      have hm1 : hd₁ ∈ ((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c =
            nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR)) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨hd₁ - 1, List.mem_range.2 (by omega), by omega⟩,
          by simpa using hpar1_hd⟩
      have hm2 : hd₂ ∈ ((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c =
            nodeField mem₂ (lctNodesBase b) r₁ OFF_PPAR)) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨hd₂ - 1, List.mem_range.2 (by omega), by omega⟩, by
          rw [← hpp_eq] at hpar2_hd; simpa using hpar2_hd⟩
      have hge := list_sum_ge_two_of_mem_ne (f := lctRepSize mem₂ (lctNodesBase b) (lctCap n))
        hcs_nd hm1 hm2 hne_hd
      rw [← hpp_eq] at hh2_lt
      omega
    let repFn := fun i =>
      if h : i < seq.length then lctRepSize mem₂ (lctNodesBase b) (lctCap n) seq[i] else 0
    have hidx_lt : ∀ j ∈ idxs, j < seq.length := by
      intro j hj
      rcases List.mem_map.1 hj with ⟨r, hr, rfl⟩
      rcases hnew_prop r hr with ⟨_, _, _, _, _, _, _, _, _, hpp_seq, _⟩
      exact List.idxOf_lt_length_of_mem hpp_seq
    have hrep_bd : ∀ i < seq.length, repFn i ≤ lctCap n := by
      intro i hi
      simp only [repFn, hi, ↓reduceDIte, lctRepSize]
      exact le_trans (List.length_filter_le _ _) (by simp)
    have hrep_pos : 1 ≤ repFn 0 := by
      have h0_lt : 0 < seq.length := List.length_pos_of_ne_nil hseq_ne
      simp only [repFn, h0_lt, ↓reduceDIte]
      have h0_mem : seq[0] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 (List.getElem_mem h0_lt)
      have h0_bd := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem h0_mem
      have hsum := lctRepSize_eq_one_add_sum mem₂ (lctNodesBase b) (lctCap n) seq[0]
        (fun x _ _ => hpar₂_le x) hacyc₂ h0_bd.1 h0_bd.2
      omega
    have hrep_mono : ∀ i, i + 1 < seq.length → repFn i ≤ repFn (i + 1) := by
      intro i hi
      simp only [repFn, hi, show i < seq.length by omega, ↓reduceDIte]
      have hi1_mem : seq[i + 1] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 (List.getElem_mem hi)
      have hi1_bd := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hi1_mem
      have hi_mem : seq[i] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1
          (List.getElem_mem (l := seq) (by omega))
      have hi_bd := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hi_mem
      have hsum := lctRepSize_eq_one_add_sum mem₂ (lctNodesBase b) (lctCap n) seq[i + 1]
        (fun x _ _ => hpar₂_le x) hacyc₂ hi1_bd.1 hi1_bd.2
      have hm_cs : seq[i] ∈ ((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c = seq[i + 1])) := by
        refine List.mem_filter.2 ⟨List.mem_map.2 ⟨seq[i] - 1, List.mem_range.2 (by omega), by omega⟩, ?_⟩
        simpa using hp_seq2_s i hi
      have hmem_sum : lctRepSize mem₂ (lctNodesBase b) (lctCap n) seq[i] ≤
          ((((List.range (lctCap n)).map (· + 1)).filter
            (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c = seq[i + 1]))).map
              (lctRepSize mem₂ (lctNodesBase b) (lctCap n))).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨seq[i], hm_cs, rfl⟩)
      omega
    have hrep_dbl : ∀ j ∈ idxs, 0 < j → 2 * repFn (j - 1) ≤ repFn j := by
      intro j hj hj0
      rcases List.mem_map.1 hj with ⟨r, hr, rfl⟩
      rcases hnew_prop r hr with ⟨s, hs_rest, _, hd, hd1, hd2, hd_mem, hd_nseq, hpar_hd, hpp_seq, hh_lt⟩
      have hlt_j : idxFn r < seq.length := List.idxOf_lt_length_of_mem hpp_seq
      have hj_eq : seq[idxFn r] = nodeField mem₂ (lctNodesBase b) r OFF_PPAR := List.getElem_idxOf hlt_j
      simp only [repFn, show idxFn r - 1 < seq.length by omega, hlt_j, ↓reduceDIte]
      rw [← hj_eq] at hh_lt
      have hj_bd : 1 ≤ nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∧
          nodeField mem₂ (lctNodesBase b) r OFF_PPAR ≤ lctCap n := by
        have hmem_y : nodeField mem₂ (lctNodesBase b) r OFF_PPAR ∈
            (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
          ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hpp_seq
        exact (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hmem_y
      have hsum := lctRepSize_eq_one_add_sum mem₂ (lctNodesBase b) (lctCap n)
        seq[idxFn r] (fun x _ _ => hpar₂_le x) hacyc₂
        (hj_eq ▸ hj_bd.1) (hj_eq ▸ hj_bd.2)
      have hcs_nd : (((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c = seq[idxFn r]))).Nodup :=
        (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
      have hm_hd : hd ∈ ((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c = seq[idxFn r])) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨hd - 1, List.mem_range.2 (by omega), by omega⟩,
          by simpa [hj_eq] using hpar_hd⟩
      have hprev_bd : 1 ≤ seq[idxFn r - 1] ∧ seq[idxFn r - 1] ≤ lctCap n := by
        have hmem_p : seq[idxFn r - 1] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
          ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1
            (List.getElem_mem (l := seq) (by omega))
        exact (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hmem_p
      have hm_prev : seq[idxFn r - 1] ∈ ((List.range (lctCap n)).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) c = seq[idxFn r])) := by
        refine List.mem_filter.2
          ⟨List.mem_map.2 ⟨seq[idxFn r - 1] - 1, List.mem_range.2 (by omega), by omega⟩, ?_⟩
        have hp_s := hp_seq2_s (idxFn r - 1) (by omega)
        have hidx_eq : seq[(idxFn r - 1) + 1]'(by omega) = seq[idxFn r]'hlt_j := by congr 1; omega
        rw [hidx_eq] at hp_s
        simpa using hp_s
      have hne_p : hd ≠ seq[idxFn r - 1] := fun heq => hd_nseq (heq ▸ List.getElem_mem (by omega))
      have hge := list_sum_ge_two_of_mem_ne (f := lctRepSize mem₂ (lctNodesBase b) (lctCap n))
        hcs_nd hm_hd hm_prev hne_p
      omega
    have hidx_len := reroot_heavy_length_bound repFn seq.length n idxs hid_nd hidx_lt
      hrep_dbl hrep_mono hrep_bd hrep_pos
    have hnew_len : newH.length ≤ Nat.log 2 (n + 2) + 2 := by
      simpa [idxs] using hidx_len
    dsimp only [roots, newH] at hfilt
    exact le_trans hfilt (Nat.add_le_add_left hnew_len _)
  unfold lctPhi
  rw [hsplay_phi_eq]
  have hmul : C_HEAVY L * lctHeavyCount mem₂ (lctNodesBase b) (lctCap n) ≤
      C_HEAVY L * (lctHeavyCount mem₁ (lctNodesBase b) (lctCap n) + (Nat.log 2 (n + 2) + 2)) :=
    Nat.mul_le_mul_left _ hheavy_le
  rw [Nat.mul_add] at hmul
  omega

/-- Pure structural and potential preservation theorem for reversing an exposed root tree `t₁`
into `t₁.revRoot` (assuming `hedge_lt` and `hslot_cover` from `LctMemRep`). -/
theorem revNode_reroot_invs {w h L P b n v : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_fin : AuxTree} {rest_fin : List AuxTree} {mem₁ mem₂ : ℕ → ℕ}
    (hi₁ : LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin) mem₁)
    (hv : v < n)
    (hpp_zero₁ : nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hev₁ : (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder (revFlag mem₁ (lctNodesBase b)) false =
      l_fin.evalInorder (revFlag mem₁ (lctNodesBase b)) false ++ [v + 1])
    (hm₂ : TreeMemMatch w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin) 0 0)
    (hsteps₂ : evalMemSteps mem₂ (lctNodesBase b) h L (AuxTree.node (v + 1) AuxTree.leaf l_fin) false 0 =
      (evalMemSteps mem₁ (lctNodesBase b) h L
        (AuxTree.node (v + 1) l_fin AuxTree.leaf) false 0).reverse.map RawStep.flip)
    (hev₂ : (AuxTree.node (v + 1) AuxTree.leaf l_fin).evalInorder (revFlag mem₂ (lctNodesBase b)) false =
      ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false).reverse)
    (hhp₂ : mem₂ (lctNodesBase b - 1) = mem₁ (lctNodesBase b - 1))
    (hstat₂ : ∀ u off, IsStaticPayloadOff off →
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off)
    (hout_x₂ : ∀ addr, addr < lctNodesBase b + NODE_STRIDE * (v + 1) ∨
        lctNodesBase b + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ addr →
      mem₂ addr = mem₁ addr)
    (hedge_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    (hslot_cover : ∀ u, n + 1 ≤ u → u ≤ lctCap n → u ∈ freeEdges ∨ ∃ p ∈ edgeMap, p.1 = u) :
    LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) mem₂ ∧
    nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PPAR = 0 ∧
    lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (v + 1) = 0 ∧
    (∀ x y, 1 ≤ x → x ≤ lctCap n → 1 ≤ y → y ≤ lctCap n →
      (rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) y ↔
       rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) y)) ∧
    RootMove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n))
      (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) (v + 1) ∧
    lctPhi L mem₂ b n ≤ lctPhi L mem₁ b n + C_HEAVY L * (Nat.log 2 (n + 2) + 2) := by
  rcases revNode_reroot_sf hi₁ hv hm₂ hhp₂ hstat₂ hout_x₂ with
    ⟨hhN, hhC, hhL, hhP, hsf₂, hfreeChain₂, hfreeNode₂, hvert₂, hnin_rest, hslot_rest, hheap₂,
      hrest_agree⟩
  have hpp_zero₂ : nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PPAR = 0 := hm₂.2.2.2.2.2.1
  rcases revNode_reroot_edge_subdiv hi₁ hsf₂ hv hpp_zero₁ hpp_zero₂ hev₁ hsteps₂ hev₂ hstat₂
      hnin_rest hslot_rest hheap₂ hrest_agree hedge_lt hslot_cover with
    ⟨hedge₂, haux₂, hsubdiv₂, hpar₂_v, hcomp, _, hseq_ne, hout_par, hclosed, hp_seq2_s, hpp₂_le⟩
  have hphi := revNode_reroot_phi hi₁ hsf₂ hm₂ hpp_zero₁ hpp_zero₂ hout_x₂ hnin_rest hrest_agree
    hsubdiv₂.1 hout_par hclosed hp_seq2_s hseq_ne hpp₂_le
  have hmove : RootMove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n))
      (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) (v + 1) := by
    have hsub : ∀ s ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false, 1 ≤ s ∧ s ≤ lctCap n := by
      intro s hs
      have ht : s ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        (AuxTree.evalInorder_perm _ _ _).mem_iff.1 hs
      have hfl : s ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap
          AuxTree.toList := List.mem_flatMap.2 ⟨_, by simp, ht⟩
      have hr := hi₁.sf.2.2.2.2.2.2.2.2.1.mem_iff.1 hfl
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      have := List.mem_range.1 hk
      exact ⟨by omega, by omega⟩
    have hlast : ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false).getLast? = some (v + 1) := by
      rw [hev₁]; simp
    exact rootMove_of_seq (lctAuxParent_zero _ _ _) (fun x _ _ => lctAuxParent_le_cap _ _ _ x)
      hi₁.subdivOk.1 (lctAuxParent_zero _ _ _) (fun x _ _ => lctAuxParent_le_cap _ _ _ x)
      hsubdiv₂.1 hcomp hsub hout_par hp_seq2_s hlast (by omega) (by unfold lctCap; omega) hpar₂_v
  exact ⟨⟨hhN, hhC, hhL, hhP, hsf₂, hfreeChain₂, hfreeNode₂, hvert₂, hedge₂, haux₂, hsubdiv₂⟩,
    hpp_zero₂, hpar₂_v, hcomp, hmove, hphi⟩

end MinCostFlow.LinkCut.Prog
